/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Cartesian closure of Type

Show that `Type u₁` is Cartesian closed, and `C ⥤ Type u₁` is Cartesian closed for `C` a small
category in `Type u₁`.
Note this implies that the category of presheaves on a small category `C` is Cartesian closed.
-/

@[expose] public section


namespace CategoryTheory

noncomputable section

open Category Limits MonoidalCategory

universe v₁ v₂ u₁ u₂

variable {C : Type v₂} [Category.{v₁} C]

section MonoidalClosed

/-- The adjunction `tensorLeft.obj X ⊣ coyoneda.obj (Opposite.op X)`
for any `X : Type v₁`. -/
def Types.tensorProductAdjunction (X : Type v₁) :
    tensorLeft X ⊣ coyoneda.obj (Opposite.op X) where
  unit := { app := fun Z (z : Z) x => ⟨x, z⟩ }
  counit := { app := fun _ xf => xf.2 xf.1 }

instance (X : Type v₁) : (tensorLeft X).IsLeftAdjoint :=
  ⟨_, ⟨Types.tensorProductAdjunction X⟩⟩

instance : MonoidalClosed (Type v₁) := MonoidalClosed.mk
  fun X => Closed.mk _ (Types.tensorProductAdjunction X)

instance {C : Type v₁} [SmallCategory C] : MonoidalClosed (C ⥤ Type v₁) :=
  FunctorToTypes.monoidalClosed.{0, v₁, v₁}

-- TODO: once we have `MonoidalClosed` instances for functor categories into general monoidal
-- closed categories, replace this with that, as it will be a more explicit construction.
/-- This is not a good instance because of the universe levels. Below is the instance where the
target category is `Type (max u₁ v₁)`. -/
@[implicit_reducible]
def cartesianClosedFunctorToTypes {C : Type u₁} [Category.{v₁} C] :
    MonoidalClosed (C ⥤ Type (max u₁ v₁ u₂)) :=
  FunctorToTypes.monoidalClosed.{u₂, v₁, u₁}

-- TODO: once we have `MonoidalClosed` instances for functor categories into general monoidal
-- closed categories, replace this with that, as it will be a more explicit construction.
instance {C : Type u₁} [Category.{v₁} C] : MonoidalClosed (C ⥤ Type (max u₁ v₁)) :=
  cartesianClosedFunctorToTypes

-- TODO: once we have `MonoidalClosed` instances for functor categories into general monoidal
-- closed categories, replace this with that, as it will be a more explicit construction.
instance {C : Type u₁} [Category.{v₁} C] [EssentiallySmall.{v₁} C] :
    MonoidalClosed (C ⥤ Type v₁) :=
  let e : (SmallModel C) ⥤ Type v₁ ≌ C ⥤ Type v₁ :=
    Functor.asEquivalence ((Functor.whiskeringLeft _ _ _).obj (equivSmallModel _).functor)
  cartesianClosedOfEquiv e

end MonoidalClosed

end

end CategoryTheory
