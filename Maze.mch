/* Maze
 * Author: 
 * Creation date: 12/18/19
 */
MACHINE
    Maze
    
CONSTANTS
    x_axis,
    y_axis,
    blocked_cell,
    grid,
    start_cell,
    exit_cell
    
INVARIANT
    //declare x and y axis
    x_axis <: NATURAL1 &
    y_axis <: NATURAL1
    
PROPERTIES
    //starting to end
    x_axis = 1..7 &
    y_axis = 1..5 &
    
    //how to make the maze grid
    grid = x_axis*y_axis &
    //blocked cells
    blocked_cell = {(1 |-> 3), (2 |-> 1), (2 |-> 3), (2 |-> 5), (3 |-> 3), (4 |-> 2),  (4 |-> 3), (4 |-> 4),  (6 |-> 1),(6 |-> 2), (6|-> 4), (7 |-> 4) } &
    
    //define start position
    start_cell = (1 |->1) &
    
    //define more about start
    start_cell : grid &
    start_cell /: blocked_cell &
    
    //define exit position
    exit_cell = (1 |-> 5) &
    
    exit_cell : grid &
    exit_cell /: blocked_cell 
    

END
