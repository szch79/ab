/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Hazel

/-!
# Project root

Every module of Ab imports this module at the meta phase.  It imports the `Hazel` linters
publicly, so that the linter options that the package enables apply to every module of the
project, while the modules import it privately, so that the packages that import Ab do not.
-/
