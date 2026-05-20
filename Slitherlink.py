#!/usr/bin/env python3
# slitherlink.py: Template para implementação do projeto de Inteligência Artificial 2025/2026.
# Devem alterar as classes e funções neste ficheiro de acordo com as instruções do enunciado.
# Além das funções e classes sugeridas, podem acrescentar outras que considerem pertinentes.

# Grupo 75:
# 111085 Feliciana Clarice Sacalema Carlos
# 1119226 Lara Isabel da Conceição Santos

import random, copy
from sys import stdin
from collections import defaultdict

import utils
from utils import *

from search import (
    Problem,
    Node,
    astar_search,
    breadth_first_tree_search,
    depth_first_tree_search,
    greedy_search,
    recursive_best_first_search,
)


class SlitherlinkState:
    state_id = 0


    def __init__(self, board):
        self.board = board
        self.id = SlitherlinkState.state_id
        SlitherlinkState.state_id += 1
    
    def __lt__(self, other):
        return self.id < other.id
    
    # implementação de eq e hash para permitir usar estados em sets e dicionários

    #a função eq compara os tabuleiros dos estados
    def __eq__(self, other):
        if not isinstance(other, SlitherlinkState):
            return False
        return (self.board.horizontal_walls == other.board.horizontal_walls and
                self.board.vertical_walls == other.board.vertical_walls)

    
    # a função hash gera um hash baseado nas arestas ativas do tabuleiro
    def __hash__(self):
        # vai se representar o estado pelas arestas ativas, é suficiente para distinguir estados
        h = tuple(tuple(row) for row in self.board.horizontal_walls)
        v = tuple(tuple(row) for row in self.board.vertical_walls)
        return hash((h, v))
        

class Board:
    """Representação interna de um tabuleiro de Slitherlink."""

    def adjacent_cell(self, cell:tuple) -> list:
        """Devolve uma lista das células que fazem
        fronteira com a célula enviada no argumento"""

        r, c = cell
        adjacent = []
        if r > 0:
            adjacent.append((r - 1, c))
        if r < self.rows - 1:
            adjacent.append((r + 1, c))
        if c > 0:
            adjacent.append((r, c - 1))
        if c < self.cols - 1:
            adjacent.append((r, c + 1))
        return adjacent
        #TODO
        pass

    def get_cell_edges(self, row:int, column:int) -> list:
        """Devolve os arestas da célula enviada no argumento"""
        #ordem: cima, direita, baixo, esquerda

        return [
            ("h", row, column),  # cima
            ("v", row, column + 1),  # direita
            ("h", row + 1, column),  # baixo
            ("v", row, column),  # esquerda
        ]

        #TODO
        pass

    def get_active_edges(self, row:int, column:int) -> list:
        """Devolve o número de arestas ativas"""
        cnt = 0
        for edge in self.get_cell_edges(row, column):
            if self.get_edge(edge):
                cnt += 1
        return cnt
    
        #TODO
        pass


    @staticmethod
    def parse_instance():
        """Lê o test do standard input (stdin) que é passado como argumento
        e retorna uma instância da classe Board.

        Por exemplo:
            $ python3 pipe.py < test-01.txt

            > from sys import stdin
            > line = stdin.readline().split()
        """
        grid = [
            [int(value) if value != b"." else -1 for value in line.split()]
            for line in stdin.buffer
            if line.strip()
        ]

        board = Board()
        board.grid = grid
        board.hints = grid
        board.rows = len(grid)
        board.cols = len(grid[0]) if grid else 0
        board.horizontal_walls = [[False] * board.cols for _ in range(board.rows + 1)]
        board.vertical_walls = [[False] * (board.cols + 1) for _ in range(board.rows)]
        return board

    def copy(self):
        """Retorna uma cópia do tabuleiro com dicas imutáveis ​​compartilhadas e arestas copiadas.."""
        board = Board()
        board.grid = self.grid
        board.hints = self.hints
        board.rows = self.rows
        board.cols = self.cols
        board.horizontal_walls = [row[:] for row in self.horizontal_walls]
        board.vertical_walls = [row[:] for row in self.vertical_walls]
        return board

    def iter_edges(self):
        """Gere cada aresta como ('h'|'v', linha, coluna)."""
        for row in range(self.rows + 1):
            for col in range(self.cols):
                yield ('h', row, col)
        for row in range(self.rows):
            for col in range(self.cols + 1):
                yield ('v', row, col)

    def get_edge(self, edge):
        kind, row, col = edge
        if kind == 'h':
            return self.horizontal_walls[row][col]
        return self.vertical_walls[row][col]

    def set_edge(self, edge, value=True):
        kind, row, col = edge
        if kind == 'h':
            self.horizontal_walls[row][col] = value
        else:
            self.vertical_walls[row][col] = value

    def active_edge_count(self):
        return sum(map(sum, self.horizontal_walls)) + sum(map(sum, self.vertical_walls))

    def vertex_degree(self, row, col):
        degree = 0
        if row > 0 and self.vertical_walls[row - 1][col]:
            degree += 1
        if row < self.rows and self.vertical_walls[row][col]:
            degree += 1
        if col > 0 and self.horizontal_walls[row][col - 1]:
            degree += 1
        if col < self.cols and self.horizontal_walls[row][col]:
            degree += 1
        return degree

    def satisfies_hints(self):
        for row in range(self.rows):
            h_top = self.horizontal_walls[row]
            h_bottom = self.horizontal_walls[row + 1]
            v_row = self.vertical_walls[row]
            hints_row = self.hints[row]
            for col in range(self.cols):
                hint = hints_row[col]
                if hint >= 0 and h_top[col] + h_bottom[col] + v_row[col] + v_row[col + 1] != hint:
                    return False
        return True

    def forms_single_loop(self):
        start = None
        for row in range(self.rows + 1):
            for col in range(self.cols + 1):
                degree = self.vertex_degree(row, col)
                if degree not in (0, 2):
                    return False
                if degree == 2 and start is None:
                    start = (row, col)

        if start is None:
            return False

        seen = {start}
        stack = [start]
        while stack:
            row, col = stack.pop()
            if row > 0 and self.vertical_walls[row - 1][col]:
                nxt = (row - 1, col)
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)
            if row < self.rows and self.vertical_walls[row][col]:
                nxt = (row + 1, col)
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)
            if col > 0 and self.horizontal_walls[row][col - 1]:
                nxt = (row, col - 1)
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)
            if col < self.cols and self.horizontal_walls[row][col]:
                nxt = (row, col + 1)
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)

        return len(seen) * 2 == self.active_edge_count()

    def to_solution_grid(self):
        solution = []
        for row in range(self.rows):
            solution_row = []
            h_top = self.horizontal_walls[row]
            h_bottom = self.horizontal_walls[row + 1]
            v_row = self.vertical_walls[row]
            for col in range(self.cols):
                solution_row.append(
                    f"{int(h_top[col])}{int(v_row[col + 1])}{int(h_bottom[col])}{int(v_row[col])}"
                )
            solution.append(solution_row)
        return solution

class Slitherlink(Problem):
    def __init__(self, board: Board, gui=None):
        """O construtor especifica o estado inicial."""
        initial_state = SlitherlinkState(board)
        super().__init__(initial_state) 
        self.gui = gui
        # TODO
        pass


    def actions(self, state: SlitherlinkState):
        """Retorna uma lista de ações que podem ser executadas a
        partir do estado passado como argumento."""

        board = state.board
        actions = []
        for edge in board.iter_edges():
            if not board.get_edge(edge):
                actions.append(edge)
        return actions
        # TODO
        pass


    def result(self, state: SlitherlinkState, action):
        """Retorna o estado resultante de executar a 'action' sobre
        'state' passado como argumento. A ação a executar deve ser uma
        das presentes na lista obtida pela execução de
        self.actions(state)."""

        new_board = state.board.copy()
        new_board.set_edge(action, True)
        new_state = SlitherlinkState(new_board)
        return new_state
        # TODO
        pass

    def goal_test(self, state: SlitherlinkState):
        """Retorna True se e só se o estado passado como argumento é
        um estado objetivo. Deve verificar se todas as posições do tabuleiro
        estão preenchidas de acordo com as regras do problema."""

        g = state.board
        return g.satisfies_hints() and g.forms_single_loop()
        # TODO
        pass

    def h(self, node: Node):
        """Função heuristica utilizada para a procura A*."""
        Board = node.state.board
        h_val = 0

        #penaliza cada célula com um valor absoluto da diferença entre o número de arestas ativas e a dica da célula
        for r in range(Board.rows):
            for c in range(Board.cols):
                hint = Board.hints[r][c]
                if hint >= 0:
                    active_edges = Board.get_active_edges(r, c)
                    h_val += abs(active_edges - hint)

        #penaliza cada vértice que tem um grau diferente de 0 ou 2, já que isso viola a condição de formar um loop
        for r in range(Board.rows + 1):
            for c in range(Board.cols + 1):
                degree = Board.vertex_degree(r, c)
                if degree not in (0, 2):
                    h_val += 1

        return h_val
        # TODO
        pass

    


if __name__ == "__main__":
    board = Board.parse_instance()
    print("Board lido com sucesso")
    print("Rows:", board.rows, "Cols:", board.cols)
    
    problem = Slitherlink(board)
    print("Problema criado")
    
    goal_node = astar_search(problem)
    print("Procura terminada")
    print("Goal node:", goal_node)

'''  TODO:
    # Ler o ficheiro do standard input,
    # Usar uma técnica de procura para resolver a instância,
    # Retirar a solução a partir do nó resultante,
    # Imprimir para o standard output no formato indicado.

    #leitura do tabuleiro a partir do standard input
    board = Board.parse_instance()

    #criação do problema a partir do tabuleiro
    problem = Slitherlink(board)

    #resolução do problema usando a procura A*
    goal_node = astar_search(problem)

    #impressão da solução no formato indicado
    sol_grid = goal_node.state.board.to_solution_grid()
    
    # imprime a solução no formato indicado, cada célula é representada por uma string de 4 caracteres indicando a presença de arestas (cima, direita, baixo, esquerda)
    for row in sol_grid:
        print(" ".join(row))
    pass
'''