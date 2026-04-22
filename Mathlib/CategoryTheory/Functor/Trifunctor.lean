/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Whiskering
/-!
# Trifunctors obtained by composition of bifunctors

Given two bifunctors `F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂` and `G : C₁₂ ⥤ C₃ ⥤ C₄`, we define
the trifunctor `bifunctorComp₁₂ F₁₂ G : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` which sends three
objects `X₁ : C₁`, `X₂ : C₂` and `X₃ : C₃` to `G.obj ((F₁₂.obj X₁).obj X₂).obj X₃`.

Similarly, given two bifunctors `F : C₁ ⥤ C₂₃ ⥤ C₄` and `G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃`, we define
the trifunctor `bifunctorComp₂₃ F G₂₃ : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` which sends three
objects `X₁ : C₁`, `X₂ : C₂` and `X₃ : C₃` to `(F.obj X₁).obj ((G₂₃.obj X₂).obj X₃)`.

-/

@[expose] public section

namespace CategoryTheory

variable {C₁ C₂ C₃ C₄ C₁₂ C₂₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₄] [Category* C₁₂] [Category* C₂₃]

section bifunctorComp₁₂Functor

/-- Auxiliary definition for `bifunctorComp₁₂`. -/
@[simps!]
def bifunctorComp₁₂Obj (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ C₄) (X₁ : C₁) :
    C₂ ⥤ C₃ ⥤ C₄ :=
  F₁₂.obj X₁ ⋙ G

/-- Given two bifunctors `F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂` and `G : C₁₂ ⥤ C₃ ⥤ C₄`, this is
the trifunctor `C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` obtained by composition. -/
@[simps!]
def bifunctorComp₁₂ (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ C₄) :
    C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ :=
  (Functor.postcompose₂.obj G).obj F₁₂

/-- Auxiliary definition for `bifunctorComp₁₂Functor`. -/
@[simps!]
def bifunctorComp₁₂FunctorObj (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) :
    (C₁₂ ⥤ C₃ ⥤ C₄) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ :=
  Functor.postcompose₂.flip.obj F₁₂

/-- Auxiliary definition for `bifunctorComp₁₂Functor`. -/
@[simps!]
def bifunctorComp₁₂FunctorMap {F₁₂ F₁₂' : C₁ ⥤ C₂ ⥤ C₁₂} (φ : F₁₂ ⟶ F₁₂') :
    bifunctorComp₁₂FunctorObj (C₃ := C₃) (C₄ := C₄) F₁₂ ⟶
      bifunctorComp₁₂FunctorObj F₁₂' :=
  Functor.postcompose₂.flip.map φ

/-- The functor `(C₁ ⥤ C₂ ⥤ C₁₂) ⥤ (C₁₂ ⥤ C₃ ⥤ C₄) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` which
sends `F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂` and `G : C₁₂ ⥤ C₃ ⥤ C₄` to the functor
`bifunctorComp₁₂ F₁₂ G : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄`. -/
@[simps]
def bifunctorComp₁₂Functor : (C₁ ⥤ C₂ ⥤ C₁₂) ⥤ (C₁₂ ⥤ C₃ ⥤ C₄) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ where
  obj := bifunctorComp₁₂FunctorObj
  map := bifunctorComp₁₂FunctorMap

end bifunctorComp₁₂Functor

section bifunctorComp₂₃Functor

/-- Auxiliary definition for `bifunctorComp₂₃`. -/
@[simps!]
def bifunctorComp₂₃Obj (F : C₁ ⥤ C₂₃ ⥤ C₄) (G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃) (X₁ : C₁) :
    C₂ ⥤ C₃ ⥤ C₄ :=
  (Functor.postcompose₂.obj (F.obj X₁)).obj G₂₃

/-- Given two bifunctors `F : C₁ ⥤ C₂₃ ⥤ C₄` and `G₂₃ : C₂ ⥤ C₃ ⥤ C₄`, this is
the trifunctor `C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` obtained by composition. -/
@[simps!]
def bifunctorComp₂₃ (F : C₁ ⥤ C₂₃ ⥤ C₄) (G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃) :
    C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ := (F ⋙ Functor.postcompose₂).flip.obj G₂₃

/-- Auxiliary definition for `bifunctorComp₂₃Functor`. -/
@[simps!]
def bifunctorComp₂₃FunctorObj (F : C₁ ⥤ C₂₃ ⥤ C₄) :
    (C₂ ⥤ C₃ ⥤ C₂₃) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ :=
  (F ⋙ Functor.postcompose₂).flip

/-- Auxiliary definition for `bifunctorComp₂₃Functor`. -/
@[simps!]
def bifunctorComp₂₃FunctorMap {F F' : C₁ ⥤ C₂₃ ⥤ C₄} (φ : F ⟶ F') :
    bifunctorComp₂₃FunctorObj F (C₂ := C₂) (C₃ := C₃) ⟶ bifunctorComp₂₃FunctorObj F' :=
  (flipFunctor C₁ (C₂ ⥤ C₃ ⥤ C₂₃) (C₂ ⥤ C₃ ⥤ C₄)).map
    (Functor.whiskerRight φ Functor.postcompose₂)

/-- The functor `(C₁ ⥤ C₂₃ ⥤ C₄) ⥤ (C₂ ⥤ C₃ ⥤ C₂₃) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` which
sends `F : C₁ ⥤ C₂₃ ⥤ C₄` and `G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃` to the
functor `bifunctorComp₂₃ F G₂₃ : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄`. -/
@[simps]
def bifunctorComp₂₃Functor :
    (C₁ ⥤ C₂₃ ⥤ C₄) ⥤ (C₂ ⥤ C₃ ⥤ C₂₃) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ where
  obj := bifunctorComp₂₃FunctorObj
  map := bifunctorComp₂₃FunctorMap

end bifunctorComp₂₃Functor

end CategoryTheory
