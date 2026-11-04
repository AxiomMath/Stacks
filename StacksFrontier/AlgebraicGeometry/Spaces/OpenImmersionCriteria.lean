module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions

/-!
# Subspaces of subspaces of an algebraic space

A subspace of an algebraic space over `S` which is contained in a second subfunctor is a
subspace of that second subfunctor, for each of the three immersion properties.

## Main results

* `AlgebraicGeometry.Space.isOpenSubspace_of_le`,
  `AlgebraicGeometry.Space.isClosedSubspace_of_le` and
  `AlgebraicGeometry.Space.isLocallyClosedSubspace_of_le`: an open, closed or locally closed
  subspace contained in a second subfunctor is one of that subfunctor.
* `CategoryTheory.MorphismProperty.presheaf_of_comp_mono`: a morphism of presheaves whose
  composite with a monomorphism is representable with `P` is itself representable with `P`.

## Implementation notes

For a subfunctor `F₁ ≤ F₂` of `F`, the subspace of `F₂` which `F₁` induces is the range of the
canonical inclusion `F₁.toFunctor ⟶ F₂.toFunctor`. Neither `F₂` nor `F` needs to be an
algebraic space.

## References

* [Stacks Project, Tag 02YX](https://stacks.math.columbia.edu/tag/02YX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C) [P.RespectsIso]
    {A B D : Cᵒᵖ ⥤ Type v}

/-- A morphism of presheaves which becomes representable with `P` after composition with a
monomorphism is already representable with `P`. -/
theorem presheaf_of_comp_mono {f : A ⟶ B} {m : B ⟶ D} [Mono m]
    (hfm : P.presheaf (f ≫ m)) : P.presheaf f := by
  apply relative.of_exists (F := yoneda) (P := P)
  intro U t
  obtain ⟨V, s, a, hOuter⟩ := hfm.rep (t ≫ m)
  have hcomm : a ≫ f = yoneda.map s ≫ t := by
    apply (cancel_mono m).1
    simpa [Category.assoc] using hOuter.w
  have hpb : IsPullback a (yoneda.map s) f t := by
    refine IsPullback.of_isLimit' (CommSq.mk hcomm) ?_
    refine PullbackCone.IsLimit.mk hcomm
      (fun c => hOuter.lift c.fst c.snd
        (by simpa [Category.assoc] using congrArg (fun k => k ≫ m) c.condition))
      (fun c => by simp) (fun c => by simp)
      (fun c k hk₁ hk₂ => hOuter.hom_ext (by simpa using hk₁) (by simpa using hk₂))
  exact ⟨V, a, s, hpb, hfm.property (t ≫ m) a s hOuter⟩

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace Space

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The range of the inclusion induced by a containment of subfunctors is an algebraic space
over `S` as soon as the smaller subfunctor is. -/
theorem isAlgebraicSpace_range_homOfLe {F₁ F₂ : Subfunctor F} (h : F₁ ≤ F₂)
    (hF₁ : IsAlgebraicSpace B S hS F₁.toFunctor) :
    IsAlgebraicSpace B S hS (Subfunctor.range (Subfunctor.homOfLe h)).toFunctor :=
  have : Mono (Subfunctor.homOfLe h) := mono_of_mono_fac (Subfunctor.homOfLe_ι h)
  hF₁.of_iso (asIso (Subfunctor.toRange (Subfunctor.homOfLe h)))

/-- If the inclusion of the smaller of two nested subfunctors is representable with a
property `P` of scheme morphisms stable under base change, then so is the inclusion of the
induced subfunctor of the larger one. -/
theorem presheaf_ι_range_homOfLe (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {F₁ F₂ : Subfunctor F} (h : F₁ ≤ F₂)
    (hF₁ : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf F₁.ι) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
      (Subfunctor.range (Subfunctor.homOfLe h)).ι := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have : Mono (Subfunctor.homOfLe h) := mono_of_mono_fac (Subfunctor.homOfLe_ι h)
  set Q := MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)
  set e := asIso (Subfunctor.toRange (Subfunctor.homOfLe h))
  have hhe : e.hom ≫ ((Subfunctor.range (Subfunctor.homOfLe h)).ι ≫ F₂.ι) = F₁.ι := by
    rw [← Category.assoc, show e.hom ≫ (Subfunctor.range (Subfunctor.homOfLe h)).ι
      = Subfunctor.homOfLe h from Subfunctor.toRange_ι _, Subfunctor.homOfLe_ι]
  have hcomp : Q.presheaf ((Subfunctor.range (Subfunctor.homOfLe h)).ι ≫ F₂.ι) := by
    rw [show (Subfunctor.range (Subfunctor.homOfLe h)).ι ≫ F₂.ι = e.inv ≫ F₁.ι from by
      rw [← hhe, Iso.inv_hom_id_assoc]]
    exact MorphismProperty.RespectsIso.precomp Q.presheaf e.inv F₁.ι hF₁
  exact MorphismProperty.presheaf_of_comp_mono Q hcomp

/-- An open subspace of an algebraic space over `S` which
is contained in a second subfunctor is an open subspace of that subfunctor. -/
@[stacks 02YX "open subspaces"]
theorem isOpenSubspace_of_le (F₁ F₂ : Subfunctor F) (hF₁ : IsOpenSubspace B S hS F₁)
    (h : F₁ ≤ F₂) :
    IsOpenSubspace B S hS (Subfunctor.range (Subfunctor.homOfLe h)) :=
  ⟨isAlgebraicSpace_range_homOfLe B S hS h hF₁.1,
    presheaf_ι_range_homOfLe B S hS
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) h hF₁.2⟩

/-- A closed subspace of an algebraic space over `S` which is contained in a second subfunctor
is a closed subspace of that subfunctor. -/
@[stacks 02YX "closed subspaces"]
theorem isClosedSubspace_of_le (F₁ F₂ : Subfunctor F) (hF₁ : IsClosedSubspace B S hS F₁)
    (h : F₁ ≤ F₂) :
    IsClosedSubspace B S hS (Subfunctor.range (Subfunctor.homOfLe h)) :=
  ⟨isAlgebraicSpace_range_homOfLe B S hS h hF₁.1,
    presheaf_ι_range_homOfLe B S hS
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) h hF₁.2⟩

/-- A locally closed subspace of an algebraic space over `S` which is contained in a second
subfunctor is a locally closed subspace of that subfunctor. -/
@[stacks 02YX "locally closed subspaces"]
theorem isLocallyClosedSubspace_of_le (F₁ F₂ : Subfunctor F)
    (hF₁ : IsLocallyClosedSubspace B S hS F₁) (h : F₁ ≤ F₂) :
    IsLocallyClosedSubspace B S hS (Subfunctor.range (Subfunctor.homOfLe h)) :=
  ⟨isAlgebraicSpace_range_homOfLe B S hS h hF₁.1,
    presheaf_ι_range_homOfLe B S hS
      (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) h hF₁.2⟩

end Space

end AlgebraicGeometry

end
