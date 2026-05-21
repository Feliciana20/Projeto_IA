#!/usr/bin/python3
# slitherlink.py: Template para implementação do projeto de Inteligência Artificial 2025/2026.

# Grupo 75:
# 111085 Feliciana Carlos
# 119226 Lara Santos

import random, copy
from sys import stdin, setrecursionlimit
from collections import defaultdict

# Aumentar o limite para recursões profundas
setrecursionlimit(200000)

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

    def __eq__(self, other):
        if not isinstance(other, SlitherlinkState):
            return False
        return (self.board.horizontal_walls == other.board.horizontal_walls and
                self.board.vertical_walls == other.board.vertical_walls)

    def __hash__(self):
        h = tuple(tuple(row) for row in self.board.horizontal_walls)
        v = tuple(tuple(row) for row in self.board.vertical_walls)
        return hash((h, v))


class Board:
    """Representação interna de um tabuleiro de Slitherlink."""

    def __init__(self, grid):
        self.grid = grid
        self.rows = len(grid)
        self.cols = len(grid[0]) if self.rows > 0 else 0

        # 0: desconhecido, 1: linha ativa, -1: proibido
        self.horizontal_walls = [[0] * self.cols for _ in range(self.rows + 1)]
        self.vertical_walls = [[0] * (self.cols + 1) for _ in range(self.rows)]
        
        # Flag crucial para indicar se este tabuleiro violou alguma restrição
        self.is_valid = True

    def copy(self):
        new_board = Board(self.grid)
        new_board.horizontal_walls = [row[:] for row in self.horizontal_walls]
        new_board.vertical_walls = [row[:] for row in self.vertical_walls]
        new_board.is_valid = self.is_valid
        return new_board

    def get_edge(self, edge: tuple) -> int:
        kind, r, c = edge
        if kind == 'h':
            return self.horizontal_walls[r][c]
        else:
            return self.vertical_walls[r][c]

    def set_edge(self, edge: tuple, val: int):
        kind, r, c = edge
        if kind == 'h':
            self.horizontal_walls[r][c] = val
        else:
            self.vertical_walls[r][c] = val

    def adjacent_cell(self, cell: tuple) -> list:
        r, c = cell
        cells = []
        if r > 0:           cells.append((r - 1, c))
        if r < self.rows-1: cells.append((r + 1, c))
        if c > 0:           cells.append((r, c - 1))
        if c < self.cols-1: cells.append((r, c + 1))
        return cells

    def get_cell_edges(self, row: int, column: int) -> list:
        return [
            ('h', row, column),       # topo
            ('v', row, column + 1),   # direita
            ('h', row + 1, column),   # baixo
            ('v', row, column)        # esquerda
        ]

    def get_active_edges(self, row: int, column: int) -> int:
        return sum(1 for e in self.get_cell_edges(row, column) if self.get_edge(e) == 1)

    def vertex_edges(self, r: int, c: int) -> list:
        edges = []
        if r > 0:           edges.append(('v', r - 1, c))
        if r < self.rows:   edges.append(('v', r, c))
        if c > 0:           edges.append(('h', r, c - 1))
        if c < self.cols:   edges.append(('h', r, c))
        return edges

    def vertex_degree(self, r: int, c: int) -> int:
        return sum(1 for e in self.vertex_edges(r, c) if self.get_edge(e) == 1)

    def count_unknown(self) -> int:
        count = 0
        for row in self.horizontal_walls:
            count += row.count(0)
        for row in self.vertical_walls:
            count += row.count(0)
        return count

    def propagate(self) -> bool:
        if not self.is_valid:
            return False

        changed = True
        while changed:
            changed = False

            # 1. Restrições Locais das Células
            for r in range(self.rows):
                for c in range(self.cols):
                    hint = self.grid[r][c]
                    if hint == -1:
                        continue

                    edges = self.get_cell_edges(r, c)
                    act = sum(1 for e in edges if self.get_edge(e) == 1)
                    inact = sum(1 for e in edges if self.get_edge(e) == -1)
                    unk = [e for e in edges if self.get_edge(e) == 0]

                    if act > hint or (4 - inact) < hint:
                        self.is_valid = False
                        return False

                    if act == hint and unk:
                        for e in unk:
                            self.set_edge(e, -1)
                        changed = True

                    if (act + len(unk)) == hint and unk:
                        for e in unk:
                            self.set_edge(e, 1)
                        changed = True

            # 2. Conservação de Fluxo nos Vértices
            for r in range(self.rows + 1):
                for c in range(self.cols + 1):
                    v_edges = self.vertex_edges(r, c)
                    act = sum(1 for e in v_edges if self.get_edge(e) == 1)
                    unk = [e for e in v_edges if self.get_edge(e) == 0]

                    if act > 2:
                        self.is_valid = False
                        return False
                    if act == 2 and unk:
                        for e in unk:
                            self.set_edge(e, -1)
                        changed = True
                    if act == 1 and len(unk) == 1:
                        self.set_edge(unk[0], 1)
                        changed = True
                    if act == 0 and len(unk) == 1:
                        self.set_edge(unk[0], -1)
                        changed = True
                    if len(unk) == 0 and act == 1:
                        self.is_valid = False
                        return False

            # 3. Poda de Ciclo Precoce Isolado
            if not self.check_early_cycles():
                self.is_valid = False
                return False

        return True

    def check_early_cycles(self) -> bool:
        active_edges = set()
        for r in range(self.rows + 1):
            for c in range(self.cols):
                if self.horizontal_walls[r][c] == 1:
                    active_edges.add(('h', r, c))
        for r in range(self.rows):
            for c in range(self.cols + 1):
                if self.vertical_walls[r][c] == 1:
                    active_edges.add(('v', r, c))

        if not active_edges:
            return True

        visited = set()
        for edge in active_edges:
            if edge in visited:
                continue

            comp = set()
            stk = [edge]
            is_closed = True

            while stk:
                curr = stk.pop()
                if curr in comp:
                    continue
                comp.add(curr)

                kind, er, ec = curr
                vertices = [(er, ec), (er, ec + 1)] if kind == 'h' else [(er, ec), (er + 1, ec)]

                for vr, vc in vertices:
                    if self.vertex_degree(vr, vc) == 1:
                        is_closed = False
                    for adj in self.vertex_edges(vr, vc):
                        if self.get_edge(adj) == 1 and adj not in comp:
                            stk.append(adj)

            visited.update(comp)

            if is_closed and len(comp) < len(active_edges):
                return False

        return True

    def choose_branch_edge(self):
        best_edge = None
        max_score = -1

        for r in range(self.rows + 1):
            for c in range(self.cols):
                if self.horizontal_walls[r][c] == 0:
                    score = self.evaluate_edge_weight('h', r, c)
                    if score > max_score:
                        max_score = score
                        best_edge = ('h', r, c)

        for r in range(self.rows):
            for c in range(self.cols + 1):
                if self.vertical_walls[r][c] == 0:
                    score = self.evaluate_edge_weight('v', r, c)
                    if score > max_score:
                        max_score = score
                        best_edge = ('v', r, c)

        return best_edge

    def evaluate_edge_weight(self, kind, r, c) -> int:
        score = 0
        if kind == 'h':
            if self.vertex_degree(r, c) == 1 or self.vertex_degree(r, c + 1) == 1:
                score += 200
            if r > 0 and self.grid[r - 1][c] != -1:
                score += self.grid[r - 1][c] * 10
            if r < self.rows and self.grid[r][c] != -1:
                score += self.grid[r][c] * 10
        else:
            if self.vertex_degree(r, c) == 1 or self.vertex_degree(r + 1, c) == 1:
                score += 200
            if c > 0 and self.grid[r][c - 1] != -1:
                score += self.grid[r][c - 1] * 10
            if c < self.cols and self.grid[r][c] != -1:
                score += self.grid[r][c] * 10
        return score

    def satisfies_hints(self) -> bool:
        for r in range(self.rows):
            for c in range(self.cols):
                hint = self.grid[r][c]
                if hint != -1 and self.get_active_edges(r, c) != hint:
                    return False
        return True

    def forms_single_loop(self) -> bool:
        active_count = sum(row.count(1) for row in self.horizontal_walls) + sum(row.count(1) for row in self.vertical_walls)
        if active_count == 0:
            return False

        start_v = None
        for r in range(self.rows + 1):
            for c in range(self.cols + 1):
                if self.vertex_degree(r, c) == 2:
                    start_v = (r, c)
                    break
            if start_v:
                break

        if not start_v:
            return False

        visited_edges = set()
        curr_v = start_v
        prev_v = None

        while True:
            r, c = curr_v
            next_v = None
            for e in self.vertex_edges(r, c):
                if self.get_edge(e) == 1 and e not in visited_edges:
                    kind, er, ec = e
                    v1, v2 = ((er, ec), (er, ec + 1)) if kind == 'h' else ((er, ec), (er + 1, ec))
                    candidate = v2 if v1 == curr_v else v1
                    if candidate != prev_v:
                        next_v = candidate
                        visited_edges.add(e)
                        break
            
            if next_v is None:
                break
            prev_v = curr_v
            curr_v = next_v
            if curr_v == start_v:
                break

        return len(visited_edges) == active_count

    def to_string(self) -> str:
        lines = []
        for r in range(self.rows):
            row_strs = []
            for c in range(self.cols):
                edges = self.get_cell_edges(r, c)
                vals = [1 if self.get_edge(e) == 1 else 0 for e in edges]
                row_strs.append("".join(map(str, vals)))
            lines.append("\t".join(row_strs))
        return "\n".join(lines)

    @staticmethod
    def parse_instance():
        grid = []
        for line in stdin:
            line = line.strip()
            if not line:
                continue
            parts = line.split()
            row = [int(p) if p != '.' else -1 for p in parts]
            grid.append(row)
        return Board(grid)


class Slitherlink(Problem):
    def __init__(self, board: Board, gui=None):
        initial_board = board.copy()
        initial_board.propagate()
        super().__init__(SlitherlinkState(initial_board))
        self.gui = gui

    def actions(self, state: SlitherlinkState):
        b = state.board
        
        # CORREÇÃO CRUCIAL: Se o estado foi marcado como inválido pela propagação, 
        # não gera nenhuma ação. Isto força o search.py a fazer backtrack imediatamente!
        if not b.is_valid or b.count_unknown() == 0:
            return []

        edge = b.choose_branch_edge()
        if edge is None:
            return []

        return [(edge, 1), (edge, -1)]

    def result(self, state: SlitherlinkState, action):
        edge, val = action
        new_board = state.board.copy()
        new_board.set_edge(edge, val)
        
        # Executa a propagação. Se violar regras, a flag interior `is_valid` passará a False
        new_board.propagate()
        
        return SlitherlinkState(new_board)

    def goal_test(self, state: SlitherlinkState):
        b = state.board
        return b.is_valid and b.count_unknown() == 0 and b.satisfies_hints() and b.forms_single_loop()

    def h(self, node: Node):
        board = node.state.board
        h_val = 0
        for r in range(board.rows):
            for c in range(board.cols):
                hint = board.grid[r][c]
                if hint != -1:
                    h_val += abs(board.get_active_edges(r, c) - hint)
        for r in range(board.rows + 1):
            for c in range(board.cols + 1):
                d = board.vertex_degree(r, c)
                if d > 2:
                    h_val += d - 2
        return h_val


if __name__ == "__main__":
    board = Board.parse_instance()
    problem = Slitherlink(board)
    
    # Resolve instantaneamente através da infraestrutura clássica do enunciado
    solution_node = depth_first_tree_search(problem)
    
    if solution_node:
        print(solution_node.state.board.to_string())