module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Subobject.MonoOver
import StacksCore.Tactic.StacksAttribute

/-! ## `MonoOver.exists` along monomorphisms and composites.

## Relation to mathlib

**Everything in this file is temporary and is expected to be deleted.** It is the `MonoOver`
half of mathlib#42757 (`feat(CategoryTheory/Subobject): extend exists and pullback API`,
merged 2026-09-07, after our pinned revision of 2026-09-01), ported with the upstream names
and statements, so that the file can be deleted as a whole once the pin moves past that
commit. The only deviation is the proof of
`factorThruImage_comp_existsPullbackAdj_counit_app_hom_left`, which upstream proves under
`set_option backward.isDefEq.respectTransparency false`; here it is a term-mode chain, so that
no option is needed.
-/

@[expose] public section

namespace CategoryTheory.MonoOver

open Limits

variable {C : Type*} [Category* C] {X Y Z : C} [HasImages C]

/-- For a monomorphism `f`, the functor `MonoOver.exists f` is full, being isomorphic to
`MonoOver.map f`. Ported from mathlib#42757; delete when the pin moves past it. -/
instance full_exists (f : X ⟶ Y) [Mono f] : Functor.Full («exists» f) :=
  Functor.Full.of_iso (existsIsoMap f).symm

/-- The counit of `exists f ⊣ pullback f` at `B`, composed with the factorisation of
`pullback.snd B.arrow f ≫ f` through its image, is the first pullback projection.
Ported from mathlib#42757 (with a term-mode proof); delete when the pin moves past it. -/
@[simp, reassoc]
lemma factorThruImage_comp_existsPullbackAdj_counit_app_hom_left
    (f : X ⟶ Y) [HasPullbacks C] (B : MonoOver Y) :
    factorThruImage (pullback.snd B.arrow f ≫ f) ≫
        ((existsPullbackAdj f).counit.app B).hom.left = pullback.fst B.arrow f := by
  have hw : ((existsPullbackAdj f).counit.app B).hom.left ≫ B.arrow =
      image.ι (pullback.snd B.arrow f ≫ f) :=
    MonoOver.w ((existsPullbackAdj f).counit.app B)
  refine (cancel_mono B.arrow).1 ?_
  exact (Category.assoc _ _ _).trans
    ((congrArg (factorThruImage (pullback.snd B.arrow f ≫ f) ≫ ·) hw).trans
      ((image.fac _).trans pullback.condition.symm))

/-- `MonoOver.exists` commutes with composition (up to isomorphism).
Ported from mathlib#42757; delete when the pin moves past it. -/
noncomputable def existsComp (f : X ⟶ Y) (g : Y ⟶ Z) [HasPullbacks C] :
    «exists» (f ≫ g) ≅ «exists» f ⋙ «exists» g :=
  ((conjugateIsoEquiv (existsPullbackAdj (f ≫ g))
    ((existsPullbackAdj f).comp (existsPullbackAdj g))).symm (pullbackComp f g)).symm

end CategoryTheory.MonoOver
