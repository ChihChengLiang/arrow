/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual
open Verso.Genre.Manual

namespace Docs


-- Here, `inlines!` is a macro that parses a string constant into Verso inline elements

def somePaper : InProceedings where
  title := inlines!"A one-shot proof of Arrow's impossibility theorem"
  authors := #[inlines!"Ning Neil Yu"]
  year := 2012
  booktitle := inlines!"Economic Theory"
  url := "https://sites.math.rutgers.edu/~zeilberg/EM22/yu2012.pdf"
