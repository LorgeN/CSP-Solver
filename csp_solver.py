import copy
import itertools
import time


def current_time_millis():
    """
    Simple function to get the current time in milliseconds. Used for timings the
    performance of the algorithm
    :return: The current time in milliseconds since unix epoch
    """
    return int(round(time.time() * 1000))


class CSP:
    def __init__(self):
        # self.variables is a list of the variable names in the CSP
        self.variables = []

        # self.domains[i] is a list of legal values for variable i
        self.domains = {}

        # self.constraints[i][j] is a list of legal value pairs for
        # the variable pair (i, j)
        self.constraints = {}

        self.backtrack_count = 0
        self.backtrack_failure_count = 0

    def add_variable(self, name, domain):
        """Add a new variable to the CSP. 'name' is the variable name
        and 'domain' is a list of the legal values for the variable.
        """
        self.variables.append(name)
        self.domains[name] = list(domain)
        self.constraints[name] = {}

    def get_all_possible_pairs(self, a, b):
        """Get a list of all possible pairs (as tuples) of the values in
        the lists 'a' and 'b', where the first component comes from list
        'a' and the second component comes from list 'b'.
        """
        return itertools.product(a, b)

    def get_all_arcs(self):
        """Get a list of all arcs/constraints that have been defined in
        the CSP. The arcs/constraints are represented as tuples (i, j),
        indicating a constraint between variable 'i' and 'j'.
        """
        return [(i, j) for i in self.constraints for j in self.constraints[i]]

    def get_all_neighboring_arcs(self, var):
        """Get a list of all arcs/constraints going to/from variable
        'var'. The arcs/constraints are represented as in get_all_arcs().
        """
        return [(i, var) for i in self.constraints[var]]

    def add_constraint_one_way(self, i, j, filter_function):
        """Add a new constraint between variables 'i' and 'j'. The legal
        values are specified by supplying a function 'filter_function',
        that returns True for legal value pairs and False for illegal
        value pairs. This function only adds the constraint one way,
        from i -> j. You must ensure that the function also gets called
        to add the constraint the other way, j -> i, as all constraints
        are supposed to be two-way connections!
        """
        if j not in self.constraints[i]:
            # First, get a list of all possible pairs of values between variables i and j
            self.constraints[i][j] = self.get_all_possible_pairs(self.domains[i], self.domains[j])

        # Next, filter this list of value pairs through the function
        # 'filter_function', so that only the legal value pairs remain
        self.constraints[i][j] = list(filter(lambda value_pair: filter_function(*value_pair), self.constraints[i][j]))

    def add_all_different_constraint(self, variables):
        """Add an Alldiff constraint between all of the variables in the
        list 'variables'.
        """
        for (i, j) in self.get_all_possible_pairs(variables, variables):
            if i != j:
                self.add_constraint_one_way(i, j, lambda x, y: x != y)

    def backtracking_search(self):
        """This functions starts the CSP solver and returns the found
        board.
        """
        # Make a so-called "deep copy" of the dictionary containing the
        # domains of the CSP variables. The deep copy is required to
        # ensure that any changes made to 'assignment' does not have any
        # side effects elsewhere.
        assignment = copy.deepcopy(self.domains)

        # Run AC-3 on all constraints in the CSP, to weed out all of the
        # values that are not arc-consistent to begin with
        self.inference(assignment, self.get_all_arcs())

        # Call backtrack with the partial assignment 'assignment'
        return self.backtrack(assignment)

    def backtrack(self, assignment):
        """The function 'Backtrack' from the pseudocode in the
        textbook.

        The function is called recursively, with a partial assignment of
        values 'assignment'. 'assignment' is a dictionary that contains
        a list of all legal values for the variables that have *not* yet
        been decided, and a list of only a single value for the
        variables that *have* been decided.

        When all of the variables in 'assignment' have lists of length
        one, i.e. when all variables have been assigned a value, the
        function should return 'assignment'. Otherwise, the search
        should continue. When the function 'inference' is called to run
        the AC-3 algorithm, the lists of legal values in 'assignment'
        should get reduced as AC-3 discovers illegal values.

        IMPORTANT: For every iteration of the for-loop in the
        pseudocode, you need to make a deep copy of 'assignment' into a
        new variable before changing it. Every iteration of the for-loop
        should have a clean slate and not see any traces of the old
        assignments and inferences that took place in previous
        iterations of the loop.
        """

        # Increment call counter
        self.backtrack_count += 1

        # Find the next unassigned variable to work on
        variable = self.select_unassigned_variable(assignment)

        # If none is found, we may have a solution or we may have
        # an unsolvable problem
        if not variable:
            # Check if the problem is unsolvable by checking if any of
            # the lists containing values is empty
            if any(not values for values in assignment.values()):
                # Increment failure counter
                self.backtrack_failure_count += 1
                return None

            # Problem has been solved!
            return assignment

        # Check every legal value for the given unassigned variable. We could
        # implement a function here that prioritizes which value to look at first
        # (e. g. by using LCV heuristic)
        for value in assignment[variable]:
            # Make a deep copy of the assignment dict to make backtracking easier
            copy = {var: vals[:] for var, vals in assignment.items()}

            # Set the variable to the current value
            copy[variable] = [value]

            # Check all neighbouring arcs
            neighbours = self.get_all_neighboring_arcs(variable)
            if self.inference(copy, neighbours):
                # If we were able to infer something, we continue
                # looking at another unassigned variable by calling the
                # backtrack method recursively
                result = self.backtrack(copy)

                # If a result is returned, we have found a solution
                if result:
                    return result
        # Increment failure counter
        self.backtrack_failure_count += 1
        # No solution found
        return None

    def select_unassigned_variable(self, assignment):
        """The function 'Select-Unassigned-Variable' from the pseudocode
        in the textbook. Should return the name of one of the variables
        in 'assignment' that have not yet been decided, i.e. whose list
        of legal values has a length greater than one.
        """
        # Creates a list of all unassigned variables
        unassigned = [item[0] for item in assignment.items() if len(item[1]) > 1]
        # Checks if the list is empty, if it is returns None, otherwise finds the one
        # which has the minimum amount of values (MRV heuristic)
        return None if not unassigned else min(unassigned, key=lambda key: len(assignment[key]))

    def inference(self, assignment, queue):
        """The function 'AC-3' from the pseudocode in the textbook.
        'assignment' is the current partial assignment, that contains
        the lists of legal values for each undecided variable. 'queue'
        is the initial queue of arcs that should be visited.
        """
        # Keep going until queue is empty
        while queue:
            # Pop and unwrap the values since queue contains tuples
            x_i, x_j = queue.pop(0)

            if self.revise(assignment, x_i, x_j):
                d_i = self.domains[x_i]

                # Check if the revision has made it impossible for us
                # to satisfy constraints for x_i. If so, this is no
                # longer a valid solution and we have to backtrack
                if not d_i:
                    return False

                # Queue all neighbouring arcs for updates since we have
                # now revised the legal values for x_i, which could possibly
                # affect the legal values for the neighbours aswell
                for x_k, _ in self.get_all_neighboring_arcs(x_i):
                    if x_k == x_j:
                        continue

                    if (x_k, x_i) in queue:
                        continue

                    queue.append((x_k, x_i))

        # The inference was a success and we can continue evaluating this line
        # of values
        return True

    def revise(self, assignment, i, j):
        """The function 'Revise' from the pseudocode in the textbook.
        'assignment' is the current partial assignment, that contains
        the lists of legal values for each undecided variable. 'i' and
        'j' specifies the arc that should be visited. If a value is
        found in variable i's domain that doesn't satisfy the constraint
        between i and j, the value should be deleted from i's list of
        legal values in 'assignment'.
        """
        revised = False

        # Tuples of all allowed combination of values on the form (i, j)
        constraints = self.constraints[i][j]
        # And all values that the current assignment allows for i and j
        legal_values_i = assignment[i]
        legal_values_j = assignment[j]

        # Check every value to see if any possible pairing with the legal
        # values for j. If not, remove them since they can not meet our
        # constraints
        for x in legal_values_i:
            # All possible pairs of values i = x and j can form
            pairs = self.get_all_possible_pairs([x], legal_values_j)

            # Check if any of these pairs exist in the constraints. If they
            # do, we can still keep x as a legal value for i
            if any(pair in constraints for pair in pairs):
                continue

            legal_values_i.remove(x)
            if not legal_values_i:
                # We have revised something but this solution is useless,
                # so we have to backtrack any changes we make here anyway.

                # This will cause the #inference loop to immediately
                # exit since D_i will be empty
                return True

            revised = True
        return revised


def create_map_coloring_csp():
    """Instantiate a CSP representing the map coloring problem from the
    textbook. This can be useful for testing your CSP solver as you
    develop your code.
    """
    csp = CSP()
    states = ['WA', 'NT', 'Q', 'NSW', 'V', 'SA', 'T']
    edges = {'SA': ['WA', 'NT', 'Q', 'NSW', 'V'], 'NT': ['WA', 'Q'], 'NSW': ['Q', 'V']}
    colors = ['red', 'green', 'blue']
    for state in states:
        csp.add_variable(state, colors)
    for state, other_states in edges.items():
        for other_state in other_states:
            csp.add_constraint_one_way(state, other_state, lambda i, j: i != j)
            csp.add_constraint_one_way(other_state, state, lambda i, j: i != j)
    return csp


def create_sudoku_csp(filename):
    """Instantiate a CSP representing the Sudoku board found in the text
    file named 'filename' in the current directory.
    """
    csp = CSP()
    board = list(map(lambda x: x.strip(), open(filename, 'r')))

    for row in range(9):
        for col in range(9):
            if board[row][col] == '0':
                csp.add_variable('%d-%d' % (row, col), list(map(str, range(1, 10))))
            else:
                csp.add_variable('%d-%d' % (row, col), [board[row][col]])

    for row in range(9):
        csp.add_all_different_constraint(['%d-%d' % (row, col) for col in range(9)])
    for col in range(9):
        csp.add_all_different_constraint(['%d-%d' % (row, col) for row in range(9)])
    for box_row in range(3):
        for box_col in range(3):
            cells = []
            for row in range(box_row * 3, (box_row + 1) * 3):
                for col in range(box_col * 3, (box_col + 1) * 3):
                    cells.append('%d-%d' % (row, col))
            csp.add_all_different_constraint(cells)

    return csp


def print_sudoku_solution(file, solution):
    """
    Prints the board before and after solving side by side
    """

    # Read the board from file and map to a dict
    board = list(map(lambda x: x.strip(), open(file, 'r')))
    base = {}

    for row in range(9):
        for col in range(9):
            if board[row][col] == '0':
                base['%d-%d' % (row, col)] = " "
            else:
                base['%d-%d' % (row, col)] = [board[row][col]]

    for base, complete in zip(format_board(base), format_board(solution)):
        print(base.ljust(25) + complete.rjust(25))


def format_board(board):
    """
    Creates a human readable sudoku board based on the given dict
    :param board: The board stored as a dict
    :return: The lines in the human readable format
    """
    lines = []
    for row in range(9):
        line = ""
        for col in range(9):
            line += board['%d-%d' % (row, col)][0] + " "
            if col == 2 or col == 5:
                line += '| '
        lines.append(line)
        if row == 2 or row == 5:
            lines.append('------+-------+------')
    return lines


if __name__ == '__main__':
    """
    Runs the CSP solver for all the provided sudoku boards and prints the
    results in human readable form.
    """

    files = ["boards/easy.txt", "boards/medium.txt", "boards/hard.txt", "boards/veryhard.txt"]

    for file in files:
        print(f"Solving {file}...")
        csp = create_sudoku_csp(file)

        # Time how long the algorithm spends solving the problem
        start = current_time_millis()
        solution = csp.backtracking_search()
        end = current_time_millis()

        print_sudoku_solution(file, solution)
        print(f"Took {end - start}ms to solve.")
        print(f"Backtrack called {csp.backtrack_count} time(s) and failed {csp.backtrack_failure_count} time(s)")
