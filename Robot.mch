/* Robot
* Author: 
* Creation date: 12/18/19
*/
MACHINE
    Robot
    //inherit from can see maze
SEES Maze
    
SETS
    messages = {can_visit_to_the_cell, outside_the_grid, inside_the_wall, yes, no}
    
VARIABLES
    x_cord,
    y_cord,
    path
    
INVARIANT
    //because can see
    //to stay cuz this is the same in the maze as defined
    x_cord : x_axis &
    y_cord : y_axis &
    
    //not to go inside the blocked
    (x_cord |-> y_cord) /: blocked_cell &
    //define for the path inside the path but the sequence is larger
    path : seq(grid) //because blocked are previously filtered
    
    
INITIALISATION
    //starting square
    x_cord := 1 ||
    y_cord := 1 ||
    //path in the start - empty
    path := []
    
DEFINITIONS
    //check boolean to make in a common format. 
    //to be in a good position definition in the grid
    isInMaze(x_x,y_y) == ((x_x |-> y_y) : grid);
    //to be in a bad position definition
    isInWall(x_x,y_y) == ((x_x |-> y_y) : blocked_cell);
    //to be in the end position definition
    isCompleted(x_x,y_y) == ((x_x |-> y_y) = (1 |-> 5))


OPERATIONS
    reports <-- moveNorth =
    // for the message output if went to north
    PRE reports : messages
        //check if we are not in a wall if we move in to the next cell
        //because we are going in to the north we have to add +1 to y cord
    THEN
        IF(isInMaze(x_cord,y_cord +1) & not(isInWall(x_cord,y_cord +1)))
            //can you go to the next position and show the message
        THEN reports := can_visit_to_the_cell ||
            //move to the next point y value
            y_cord := y_cord +1 ||
            //adding the new path to the old
            path := path ^ [(x_cord |-> y_cord)]
        ELSIF
            //if it's failed have to show the output
            (isInWall(x_cord,y_cord +1))
        THEN reports := inside_the_wall
            //for the +1 not condition
        ELSIF not(isInMaze(x_cord,y_cord +1))
            THEN reports := outside_the_grid
        END
    END;
    
    
    reports <-- moveSouth =
    // for the message output if went to south
    PRE reports : messages
        //check if we are not in a wall if we move in to the next cell
        //because we are going in to the south we have to add +1 to y cord
    THEN
        IF(isInMaze(x_cord,y_cord -1) & not(isInWall(x_cord,y_cord -1)))
            //can you go to the next position and show the message
        THEN reports := can_visit_to_the_cell ||
            //move to the next point y value
            y_cord := y_cord -1 ||
            //adding the new path to the old
            path := path ^ [(x_cord |-> y_cord)]
        ELSIF
            //if it's failed have to show the output
            (isInWall(x_cord,y_cord -1))
        THEN reports := inside_the_wall
            //for the +1 not condition
        ELSIF not(isInMaze(x_cord,y_cord -1))
            THEN reports := outside_the_grid
        END
    END;
    
    
    reports <-- moveEast =
    // for the message output if went to east
    PRE reports : messages
        //check if we are not in a wall if we move in to the next cell
        //because we are going in to the east we have to add +1 to y cord
    THEN
        IF(isInMaze(x_cord +1,y_cord) & not(isInWall(x_cord +1,y_cord)))
            //can you go to the next position and show the message
        THEN reports := can_visit_to_the_cell ||
            //move to the next point y value
            x_cord := x_cord +1 ||
            //adding the new path to the old
            path := path ^ [(x_cord |-> y_cord)]
        ELSIF
            //if it's failed have to show the output
            (isInWall(x_cord +1,y_cord))
        THEN reports := inside_the_wall
            //for the +1 not condition
        ELSIF not(isInMaze(x_cord +1,y_cord))
            THEN reports := outside_the_grid
        END
    END;
    
    reports <-- moveWest =
    // for the message output if went to west
    PRE reports : messages
        //check if we are not in a wall if we move in to the next cell
        //because we are going in to the west we have to add +1 to y cord
    THEN
        IF(isInMaze(x_cord -1,y_cord) & not(isInWall(x_cord -1,y_cord )))
            //can you go to the next position and show the message
        THEN reports := can_visit_to_the_cell ||
            //move to the next point y value
            x_cord := x_cord -1 ||
            //adding the new path to the old
            path := path ^ [(x_cord |-> y_cord)]moveWest-->outside_the_grid
        ELSIF
            //if it's failed have to show the output
            (isInWall(x_cord -1,y_cord ))
        THEN reports := inside_the_wall
            //for the +1 not condition
        ELSIF not(isInMaze(x_cord -1,y_cord))
            THEN reports := outside_the_grid
        END
    END;
    
    reports <-- teleport(teleport_x, teleport_y) =
    // for the message output if went to north
    PRE reports : messages  &
         (teleport_x : x_axis  &
         teleport_y : y_axis)
        //check if we are not in a wall if we move in to the next cell
        //because we are going in to the north we have to add +1 to y cord
    THEN
        IF(isInMaze(teleport_x, teleport_y) & not(isInWall(teleport_x, teleport_y)))
            //can you go to the next position and show the message
        THEN reports := can_visit_to_the_cell ||
            //move to the next point y value
            x_cord := teleport_x ||
            y_cord := teleport_y ||
            //adding the new path to the old
            path := path ^ [(teleport_x |-> teleport_y)]
        ELSIF
            //if it's failed have to show the output
            (isInWall(teleport_x, teleport_y ))
        THEN reports := inside_the_wall
            //for the +1 not condition
        ELSIF not(isInMaze(teleport_x, teleport_y))
            THEN reports := outside_the_grid
        END
    END;
    
    //show the current position 
    showPosition <-- getPosition =
    BEGIN
    showPosition := (x_cord, y_cord)
    
    END;

    //found Exit
    reports <-- foundExit = 
    BEGIN
        //if the current position meets the exit cell show yes or no
        IF(isCompleted(x_cord, y_cord))
        THEN reports := yes
        ELSE reports := no
            
    END 
END;

    //check whether the cells have been visited
    reports <-- visitedSquare(xCordinate, yCordinate) =
    PRE
        reports : messages &
        //get the coordinates
        xCordinate : x_axis &
        yCordinate : y_axis
    THEN
        //ran uses to get the path
        IF(yCordinate |-> yCordinate) : ran(path)
        THEN reports := yes
        ELSE reports := no
        END
    END;
          

//route is the grid 
    reports <-- robotsRoute = 
    BEGIN
        reports := path
    END
      
    END
    