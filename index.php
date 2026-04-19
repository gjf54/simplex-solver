<?php
class SimplexSolver
{
    private $matrix;
    private $numVariables;
    private $numConstraints;
    private $basis;
    private $isMaximization;
    private $steps = [];
    private $iteration = 0;
    private $variableNames = [];
    private $slackNames = [];
    private $artificialNames = []; 
    private $nonBasisColumns = []; 
    private $dualEstimates = []; 
    private $bigM = 1000; 
    private $hasArtificial = false; 
    
    public function solve($c, $A, $b, $constraintTypes, $isMaximization = true)
    {
        $this->isMaximization = $isMaximization;
        $this->numVariables = count($c);
        $this->numConstraints = count($b);
        $this->steps = [];
        $this->iteration = 0;
        $this->hasArtificial = false;
        
        for ($i = 1; $i <= $this->numVariables; $i++) {
            $this->variableNames[] = "x{$i}";
        }
        
        $this->createInitialTable($c, $A, $b, $constraintTypes);
        $this->calculateDualEstimates();
        $this->addStep('Начальная симплекс-таблица');
        
        
        if ($this->hasArtificial) {
            $this->removeArtificialVariables();
        }
        
        while (true) {
            $pivotCol = $this->findPivotColumn();
            
            if ($pivotCol === -1) {
                break;
            }
            
            $pivotRow = $this->findPivotRow($pivotCol);
            
            if ($pivotRow === -1) {
                return [
                    'success' => false,
                    'error' => 'Целевая функция не ограничена',
                    'steps' => $this->steps
                ];
            }
            
            $this->pivot($pivotRow, $pivotCol);
            $this->calculateDualEstimates();
            $this->iteration++;
            $this->addStep("Итерация {$this->iteration}");
        }
        
        
        for ($i = 0; $i < $this->numConstraints; $i++) {
            $basisIndex = $this->basis[$i];
            if ($basisIndex >= $this->numVariables + count($this->slackNames)) {
                $value = $this->matrix[$i + 1][count($this->matrix[$i + 1]) - 1];
                if (abs($value) > 1e-6) {
                    return [
                        'success' => false,
                        'error' => 'Задача не имеет допустимых решений',
                        'steps' => $this->steps
                    ];
                }
            }
        }
        
        $solution = $this->extractSolution();
        $dualSolution = $this->extractDualSolution();
        
        return [
            'success' => true,
            'solution' => $solution,
            'dual_solution' => $dualSolution,
            'optimal_value' => $this->getOptimalValue(),
            'steps' => $this->steps
        ];
    }
    
    private function createInitialTable($c, $A, $b, $constraintTypes)
    {
        $slackCount = 0;
        $artificialCount = 0;
        
        
        foreach ($constraintTypes as $type) {
            if ($type == '<=') {
                $slackCount++;
            } elseif ($type == '>=') {
                $slackCount++;
                $artificialCount++;
                $this->hasArtificial = true;
            } elseif ($type == '=') {
                $artificialCount++;
                $this->hasArtificial = true;
            }
        }
        
        $totalVars = $this->numVariables + $slackCount + $artificialCount;
        
        
        for ($i = 1; $i <= $slackCount; $i++) {
            $this->slackNames[] = "t{$i}";
        }
        
        
        for ($i = 1; $i <= $artificialCount; $i++) {
            $this->artificialNames[] = "r{$i}";
        }
        
        $this->matrix = array_fill(0, $this->numConstraints + 1, array_fill(0, $totalVars + 1, 0));
        $this->basis = array_fill(0, $this->numConstraints, 0);
        
        
        for ($j = 0; $j < $this->numVariables; $j++) {
            $this->matrix[0][$j] = $this->isMaximization ? -$c[$j] : $c[$j];
        }
        
        $slackIndex = $this->numVariables;
        $artificialIndex = $this->numVariables + $slackCount;
        
        for ($i = 0; $i < $this->numConstraints; $i++) {
            
            for ($j = 0; $j < $this->numVariables; $j++) {
                $this->matrix[$i + 1][$j] = $A[$i][$j];
            }
            
            if ($constraintTypes[$i] == '<=') {
                
                $this->matrix[$i + 1][$slackIndex] = 1;
                $this->basis[$i] = $slackIndex;
                $slackIndex++;
            } elseif ($constraintTypes[$i] == '>=') {
                
                $this->matrix[$i + 1][$slackIndex] = -1;
                $slackIndex++;
                
                
                $this->matrix[$i + 1][$artificialIndex] = 1;
                $this->basis[$i] = $artificialIndex;
                
                
                if ($this->isMaximization) {
                    $this->matrix[0][$artificialIndex] = -$this->bigM;
                } else {
                    $this->matrix[0][$artificialIndex] = $this->bigM;
                }
                
                $artificialIndex++;
            } elseif ($constraintTypes[$i] == '=') {
                
                $this->matrix[$i + 1][$artificialIndex] = 1;
                $this->basis[$i] = $artificialIndex;
                
                
                if ($this->isMaximization) {
                    $this->matrix[0][$artificialIndex] = -$this->bigM;
                } else {
                    $this->matrix[0][$artificialIndex] = $this->bigM;
                }
                
                $artificialIndex++;
            }
            
            
            $this->matrix[$i + 1][$totalVars] = $b[$i];
        }
        
        
        for ($i = 0; $i < $this->numConstraints; $i++) {
            $basisIndex = $this->basis[$i];
            if ($basisIndex >= $this->numVariables + $slackCount) {
                
                $factor = $this->matrix[0][$basisIndex];
                if (abs($factor) > 1e-10) {
                    for ($j = 0; $j <= $totalVars; $j++) {
                        $this->matrix[0][$j] -= $factor * $this->matrix[$i + 1][$j];
                    }
                }
            }
        }
        
        $this->updateNonBasisColumns();
    }
    
    private function removeArtificialVariables()
    {
        
        $maxIterations = 50;
        $iter = 0;
        
        while ($iter < $maxIterations) {
            $artificialInBasis = -1;
            
            
            for ($i = 0; $i < $this->numConstraints; $i++) {
                $basisIndex = $this->basis[$i];
                if ($basisIndex >= $this->numVariables + count($this->slackNames)) {
                    $artificialInBasis = $i + 1; 
                    break;
                }
            }
            
            if ($artificialInBasis == -1) {
                break; 
            }
            
            
            $pivotCol = -1;
            for ($j = 0; $j < count($this->matrix[0]) - 1; $j++) {
                if ($j < $this->numVariables + count($this->slackNames)) {
                    
                    if (abs($this->matrix[$artificialInBasis][$j]) > 1e-10) {
                        $pivotCol = $j;
                        break;
                    }
                }
            }
            
            if ($pivotCol == -1) {
                
                $value = $this->matrix[$artificialInBasis][count($this->matrix[$artificialInBasis]) - 1];
                if (abs($value) > 1e-6) {
                    
                    return false;
                }
                
                
                for ($j = 0; $j < count($this->matrix[0]); $j++) {
                    $this->matrix[$artificialInBasis][$j] = 0;
                }
            } else {
                
                $this->pivot($artificialInBasis, $pivotCol);
            }
            
            $iter++;
        }
        
        return true;
    }
    
    private function calculateDualEstimates()
    {
        $this->dualEstimates = [];
        $numCols = count($this->matrix[0]) - 1;
        
        
        for ($j = 0; $j < $numCols; $j++) {
            $this->dualEstimates[$j] = $this->matrix[0][$j];
        }
    }
    
    private function updateNonBasisColumns()
    {
        $totalCols = count($this->matrix[0]) - 1; 
        $this->nonBasisColumns = [];
        
        for ($j = 0; $j < $totalCols; $j++) {
            $isBasisColumn = false;
            for ($i = 0; $i < $this->numConstraints; $i++) {
                if ($this->basis[$i] == $j) {
                    $isBasisColumn = true;
                    break;
                }
            }
            
            if (!$isBasisColumn) {
                $this->nonBasisColumns[] = $j;
            }
        }
    }
    
    private function findPivotColumn()
    {
        $minValue = 0;
        $pivotCol = -1;
        
        for ($j = 0; $j < count($this->matrix[0]) - 1; $j++) {
            
            if ($j >= $this->numVariables + count($this->slackNames)) {
                continue;
            }
            if ($this->matrix[0][$j] < $minValue - 1e-10) {
                $minValue = $this->matrix[0][$j];
                $pivotCol = $j;
            }
        }
        
        return $pivotCol;
    }
    
    private function findPivotRow($pivotCol)
    {
        $minRatio = INF;
        $pivotRow = -1;
        
        for ($i = 1; $i < count($this->matrix); $i++) {
            if ($this->matrix[$i][$pivotCol] > 1e-10) {
                $ratio = $this->matrix[$i][count($this->matrix[$i]) - 1] / $this->matrix[$i][$pivotCol];
                
                if ($ratio < $minRatio - 1e-10) {
                    $minRatio = $ratio;
                    $pivotRow = $i;
                }
            }
        }
        
        return $pivotRow;
    }
    
    private function pivot($pivotRow, $pivotCol)
    {
        $rows = count($this->matrix);
        $cols = count($this->matrix[0]);
        $oldMatrix = $this->matrix;
        
        $pivotElement = $oldMatrix[$pivotRow][$pivotCol];
        for ($j = 0; $j < $cols; $j++) {
            $this->matrix[$pivotRow][$j] = $oldMatrix[$pivotRow][$j] / $pivotElement;
        }
        
        for ($i = 0; $i < $rows; $i++) {
            if ($i != $pivotRow) {
                $factor = $oldMatrix[$i][$pivotCol];
                for ($j = 0; $j < $cols; $j++) {
                    $this->matrix[$i][$j] = $oldMatrix[$i][$j] - $factor * $this->matrix[$pivotRow][$j];
                }
            }
        }
        
        $this->basis[$pivotRow - 1] = $pivotCol;
        $this->updateNonBasisColumns();
    }
    
    private function extractSolution()
    {
        $solution = array_fill(0, $this->numVariables, 0);
        
        for ($i = 0; $i < $this->numConstraints; $i++) {
            $basisIndex = $this->basis[$i];
            if ($basisIndex < $this->numVariables) {
                $solution[$basisIndex] = $this->matrix[$i + 1][count($this->matrix[$i + 1]) - 1];
            }
        }
        
        return $solution;
    }
    
    private function extractDualSolution()
    {
        $dualSolution = array_fill(0, $this->numConstraints, 0);
        
        
        for ($i = 0; $i < $this->numConstraints; $i++) {
            $slackIndex = $this->numVariables + $i;
            if ($slackIndex < count($this->matrix[0]) - 1) {
                $dualSolution[$i] = -$this->matrix[0][$slackIndex];
            }
        }
        
        return $dualSolution;
    }
    
    private function getOptimalValue()
    {
        $value = $this->matrix[0][count($this->matrix[0]) - 1];
        
        
        for ($j = $this->numVariables + count($this->slackNames); $j < count($this->matrix[0]) - 1; $j++) {
            if (abs($this->matrix[0][$j]) > 1e-6) {
                
                
                return INF;
            }
        }
        
        return $this->isMaximization ? $value : -$value;
    }
    
    private function addStep($description)
    {
        $step = [
            'iteration' => $this->iteration,
            'description' => $description,
            'table' => $this->formatTable(),
            'basis' => $this->formatBasis(),
            'numVars' => $this->numVariables,
            'numConstraints' => $this->numConstraints,
            'slackNames' => $this->slackNames,
            'artificialNames' => $this->artificialNames,
            'nonBasisColumns' => $this->nonBasisColumns,
            'basisIndices' => $this->basis,
            'dualEstimates' => $this->dualEstimates
        ];
        
        $this->steps[] = $step;
    }
    
    private function formatTable()
    {
        $formatted = [];
        foreach ($this->matrix as $row) {
            $formattedRow = [];
            foreach ($row as $value) {
                $formattedRow[] = round($value, 4);
            }
            $formatted[] = $formattedRow;
        }
        return $formatted;
    }
    
    private function formatBasis()
    {
        $basisDisplay = [];
        for ($i = 0; $i < count($this->basis); $i++) {
            $varIndex = $this->basis[$i];
            if ($varIndex < $this->numVariables) {
                $basisDisplay[] = "x" . ($varIndex + 1);
            } elseif ($varIndex < $this->numVariables + count($this->slackNames)) {
                $slackNum = $varIndex - $this->numVariables + 1;
                $basisDisplay[] = "t" . $slackNum;
            } else {
                $artNum = $varIndex - $this->numVariables - count($this->slackNames) + 1;
                $basisDisplay[] = "r" . $artNum;
            }
        }
        return $basisDisplay;
    }
}

$result = null;
$error = null;

if ($_SERVER['REQUEST_METHOD'] === 'POST') {
    try {
        $numVars = intval($_POST['num_vars']);
        $numConstraints = intval($_POST['num_constraints']);
        $optimization = $_POST['optimization'];
        
        $c = [];
        for ($i = 1; $i <= $numVars; $i++) {
            $c[] = floatval($_POST["c_$i"]);
        }
        
        $A = [];
        $b = [];
        $constraintTypes = [];
        
        for ($i = 1; $i <= $numConstraints; $i++) {
            $row = [];
            for ($j = 1; $j <= $numVars; $j++) {
                $row[] = floatval($_POST["a_{$i}_{$j}"]);
            }
            $A[] = $row;
            $b[] = floatval($_POST["b_$i"]);
            $constraintTypes[] = $_POST["type_$i"];
        }
        
        $solver = new SimplexSolver();
        $result = $solver->solve($c, $A, $b, $constraintTypes, $optimization === 'max');
        
    } catch (Exception $e) {
        $error = $e->getMessage();
    }
}
?>

<!DOCTYPE html>
<html lang="ru">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Симплекс-метод:</title>
    <style>
        body {
            font-family: Arial, sans-serif;
            margin: 20px;
        }
        
        .container {
            max-width: 95vw;
            margin: 0 auto;
            background-color: white;
            padding: 20px;
            border-radius: 8px;
        }
        
        h1, h2, h3, h4 {
            color: #333;
        }
        
        .form-group {
            margin-bottom: 15px;
        }
        
        label {
            display: inline-block;
            width: 200px;
            font-weight: bold;
        }
        
        input[type="number"] {
            padding: 8px;
            border: 1px solid #ddd;
            border-radius: 4px;
            width: 100px;
        }
        
        select {
            padding: 8px;
            border: 1px solid #ddd;
            border-radius: 4px;
        }
        
        table {
            border-collapse: collapse;
            margin: 15px 0;
            width: 100%;
            font-size: 14px;
        }
        
        th, td {
            border: 1px solid #ddd;
            padding: 8px;
            text-align: center;
        }
        
        th {
            background-color: #4CAF50;
            color: white;
        }
        
        .constraint-table th {
            background-color: #2196F3;
        }
        
        .step-table {
            margin: 30px 0;
            overflow-x: auto;
            border: 2px solid #000;
            padding: 15px;
            border-radius: 8px;
        }
        
        .step-table h4 {
            margin-top: 0;
            color: #000;
        }
        
        .step-table th {
            background-color: rgba(255, 140, 255, 0.2);
        }
        
        .basis-cell {
            background-color: #e8f5e8;
            font-weight: bold;
        }
        
        .optimal-value {
            font-size: 1.2em;
            color: #4CAF50;
            font-weight: bold;
        }
        
        .btn {
            background-color: #4CAF50;
            color: white;
            padding: 12px 24px;
            border: none;
            border-radius: 4px;
            cursor: pointer;
            font-size: 16px;
            margin: 10px 0;
        }
        
        .btn:hover {
            background-color: #45a049;
        }
        
        .error {
            color: red;
            padding: 10px;
            background-color: #ffebee;
            border-radius: 4px;
            margin: 10px 0;
        }
        
        .success {
            color: green;
            padding: 10px;
            background-color: #e8f5e8;
            border-radius: 4px;
            margin: 10px 0;
        }
        
        .problem-description {
            background-color: #f0f0f0;
            padding: 15px;
            border-radius: 4px;
            margin: 15px 0;
        }
        
        .note {
            font-style: italic;
            color: #666;
            margin-top: 5px;
        }
        
        .dual-table {
            margin-top: 20px;
        }
        
        .dual-table th {
            background-color: rgba(120, 240, 180, 0.2);
        }
        
        .primary {
            background-color: #e3f2fd;
        }
        
        .dual {
            background-color: #f3e5f5;
        }
        
        .artificial {
            background-color: #ffebee;
        }
        
        .estimates-grid {
            display: grid;
            grid-template-columns: 1fr 1fr;
            gap: 20px;
            margin: 20px 0;
        }
        
        .estimates-card {
            border: 1px solid #ddd;
            border-radius: 8px;
            padding: 15px;
        }
        
        .primary-card {
            background-color: #e3f2fd;
        }
        
        .dual-card {
            background-color: #f3e5f5;
        }
        
        .variable-type {
            font-size: 12px;
            color: #666;
        }
    </style>
    <script>
        function updateForm() {
            let numVars = parseInt(document.getElementById('num_vars').value);
            let numConstraints = parseInt(document.getElementById('num_constraints').value);
            
            let objectiveHtml = '<h3>Целевая функция</h3>';
            objectiveHtml += '<table>';
            objectiveHtml += '<tr><th>Переменная</th><th>Коэффициент</th></tr>';
            
            for (let i = 1; i <= numVars; i++) {
                objectiveHtml += '<tr>';
                objectiveHtml += '<td>x<sub>' + i + '</sub></td>';
                objectiveHtml += '<td><input type="number" name="c_' + i + '" step="any" required value="0" style="width: 100px;"></td>';
                objectiveHtml += '</tr>';
            }
            objectiveHtml += '</table>';
            document.getElementById('objective_function').innerHTML = objectiveHtml;
            
            let constraintsHtml = '<h3>Система ограничений</h3>';
            constraintsHtml += '<table class="constraint-table">';
            
            constraintsHtml += '<tr><th>№</th>';
            for (let j = 1; j <= numVars; j++) {
                constraintsHtml += '<th>x<sub>' + j + '</sub></th>';
            }
            constraintsHtml += '<th>Тип</th><th>Своб. член</th></tr>';
            
            for (let i = 1; i <= numConstraints; i++) {
                constraintsHtml += '<tr>';
                constraintsHtml += '<td><strong>' + i + '</strong></td>';
                
                for (let j = 1; j <= numVars; j++) {
                    constraintsHtml += '<td><input type="number" name="a_' + i + '_' + j + '" step="any" required value="0" style="width: 80px;"></td>';
                }
                
                constraintsHtml += '<td>';
                constraintsHtml += '<select name="type_' + i + '">';
                constraintsHtml += '<option value="<=">≤</option>';
                constraintsHtml += '<option value="=">=</option>';
                constraintsHtml += '<option value=">=">≥</option>';
                constraintsHtml += '</select>';
                constraintsHtml += '</td>';
                
                constraintsHtml += '<td><input type="number" name="b_' + i + '" step="any" required value="0" style="width: 80px;"></td>';
                constraintsHtml += '</tr>';
            }
            constraintsHtml += '</table>';
            document.getElementById('constraints').innerHTML = constraintsHtml;
        }
    </script>
</head>
<body>
    <div class="container">
        <h1>Симплекс-метод. Создано при поддержке MW Inc. и Короля Гороха</h1>
        
        <form method="POST">
            <div class="form-group">
                <label for="num_vars">Количество переменных:</label>
                <input type="number" id="num_vars" name="num_vars" min="1" max="10" value="3" required onchange="updateForm()">
            </div>
            
            <div class="form-group">
                <label for="num_constraints">Количество ограничений:</label>
                <input type="number" id="num_constraints" name="num_constraints" min="1" max="10" value="3" required onchange="updateForm()">
            </div>
            
            <div class="form-group">
                <label for="optimization">Тип оптимизации:</label>
                <select name="optimization" id="optimization">
                    <option value="max">Максимизация</option>
                    <option value="min">Минимизация</option>
                </select>
            </div>
            
            <div id="objective_function"></div>
            <div id="constraints"></div>
            
            <button type="submit" class="btn">Решить задачу</button>
        </form>
        
        <?php if ($error): ?>
            <div class="error">Ошибка: <?php echo htmlspecialchars($error); ?></div>
        <?php endif; ?>
        
        <?php if ($result): ?>
            <h2>Результат решения</h2>
            
            <?php if ($result['success']): ?>
                <div class="success">
                    <h3>Оптимальное решение найдено. Не благодарите.</h3>
                    <p class="optimal-value">
                        Оптимальное значение F = <?php echo number_format($result['optimal_value'], 4); ?>
                    </p>
                    
                    <div class="estimates-grid">
                        <div class="estimates-card primary-card">
                            <h4>Прямые оценки (переменные xᵢ):</h4>
                            <ul style="list-style-type:none; padding:0;">
                                <?php foreach ($result['solution'] as $i => $value): ?>
                                    <li><strong>x<sub><?php echo ($i + 1); ?></sub></strong> = <?php echo number_format($value, 4); ?></li>
                                <?php endforeach; ?>
                            </ul>
                        </div>
                    </div>
                </div>
                
                <?php foreach ($result['steps'] as $index => $step): ?>
                    <div class="step-table">
                        <h4>Симплекс-таблица №<?php echo ($index + 1); ?></h4>
                        
                        <?php
                        $numVars = $step['numVars'];
                        $numConstraints = $step['numConstraints'];
                        $slackNames = $step['slackNames'];
                        $artificialNames = $step['artificialNames'];
                        $nonBasisColumns = $step['nonBasisColumns'];
                        $table = $step['table'];
                        $dualEstimates = $step['dualEstimates'];
                        ?>
                        
                        <table>
                            <tr>
                                <th><span style="color:#000;">Базис</span></th>
                                <th><span style="color:#000;">ПО</span></th>
                                <?php foreach ($nonBasisColumns as $colIndex): ?>
                                    <?php if ($colIndex < $numVars): ?>
                                        <th><span style="color:#000;">x<sub><?php echo $colIndex + 1; ?></sub></span></th>
                                    <?php elseif ($colIndex < $numVars + count($slackNames)): ?>
                                        <th><span style="color:#000;"><?php echo $slackNames[$colIndex - $numVars]; ?></span></th>
                                    <?php else: ?>
                                        <th class="artificial"><?php echo $artificialNames[$colIndex - $numVars - count($slackNames)]; ?></th>
                                    <?php endif; ?>
                                <?php endforeach; ?>
                            </tr>
                            
                            <?php foreach ($table as $i => $row): ?>
                                <tr>
                                    <?php if ($i == 0): ?>
                                        <td class="basis-cell"><span style="color:#000;">F</span></td>
                                    <?php else: ?>
                                        <td class="basis-cell"><span style="color:#000;"><?php echo $step['basis'][$i - 1]; ?></span></td>
                                    <?php endif; ?>

                                    <td><?php echo number_format($row[count($row) - 1], 4); ?></td>

                                    <?php foreach ($nonBasisColumns as $colIndex): ?>
                                        <td><?php echo number_format($row[$colIndex], 4); ?></td>
                                    <?php endforeach; ?>
                                </tr>
                            <?php endforeach; ?>
                        </table>
                        
                        <p class="note">Базисные переменные: <?php echo implode(', ', $step['basis']); ?></p>
                    </div>
                <?php endforeach; ?>
                
            <?php else: ?>
                <div class="error">
                    <h3>Решение не найдено. Можете благодарить.</h3>
                    <p><?php echo htmlspecialchars($result['error']); ?></p>
                </div>
            <?php endif; ?>
        <?php endif; ?>
    </div>
    
    <script>
        window.onload = updateForm;
    </script>
</body>
</html>