/-
Copyright (c) 2026 Jake Weinstein. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Weinstein
-/
import CombinatorialGames.Surreal.Division
import CombinatorialGames.Surreal.Ordinal
import Mathlib.Tactic.NormNum

/-!
# Smoke test for the surreal calculus project

Verifies the environment: mathlib + the CombinatorialGames library build, the
surreal numbers import, their field structure is available, and basic
arithmetic computes.
-/

noncomputable example : Field Surreal := inferInstance

example : (2 : Surreal) + 2 = 4 := by norm_num

example : ((1 : Surreal) / 2) * 2 = 1 := by norm_num

example : (0 : NatOrdinal).toSurreal = 0 := NatOrdinal.toSurreal_zero
