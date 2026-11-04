module

public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedSections
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentTfae

/-!
# Relative pseudo-coherence and the pseudo-coherence of derived sections

Let `f : X ⟶ S` be a morphism of schemes locally of finite type and let `E` be an object of
`D_{QCoh}(𝒪_X)`. Then `E` is `m`-pseudo-coherent relative to `S` exactly when, for every
compatible pair of affine opens `U ⊆ f ⁻¹ᵁ V`, the complex of `Γ(X, U)`-modules `RΓ(U, E)` is
`m`-pseudo-coherent relative to `Γ(S, V)`, and it is enough to test this on one affine open
covering. This file states that comparison for bounded below `E`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.DerivedSectionsPseudoCoherentOn f E m hU hV e`: `RΓ(U, E)` is
  `m`-pseudo-coherent relative to `Γ(S, V)`, at one compatible pair of affine opens.
* `AlgebraicGeometry.DerivedSectionsPseudoCoherentComparison f E m`: relative
  `m`-pseudo-coherence of `E`, the condition on one affine open covering and the condition at
  every compatible pair of affine opens are equivalent, for `E` bounded below.

## Main results

* `AlgebraicGeometry.exists_affineCover_derivedSectionsPseudoCoherentOn`: if `RΓ(U, E)` is
  `m`-pseudo-coherent relative to `Γ(S, V)` at every compatible pair of affine opens, then it is
  so on some affine open covering.

## References

* [The Stacks Project, Lemma 36.61.8 (09VF)](https://stacks.math.columbia.edu/tag/09VF)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Definition 15.82.4 (065I)](https://stacks.math.columbia.edu/tag/065I)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- For a compatible pair of affine opens `U ⊆ f ⁻¹ᵁ V`, the complex of `Γ(X, U)`-modules
`RΓ(U, E)` is `m`-pseudo-coherent relative to `Γ(S, V)`, where `Γ(X, U)` is a finite type
`Γ(S, V)`-algebra through `f`. -/
public abbrev Scheme.Hom.DerivedSectionsPseudoCoherentOn [LocallyOfFiniteType f]
    (E : DerivedCategory.Plus X.Modules) (m : ℤ) {U : X.Opens} (hU : IsAffineOpen U)
    {V : S.Opens} (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) : Prop :=
  letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  letI : Algebra.FiniteType Γ(S, V) Γ(X, U) := algebraFiniteType_appLE f U hU V hV e
  PseudoCoherence.IsRelativelyPseudoCoherentFrom (R := Γ(S, V)) (A := Γ(X, U))
    (DerivedCategory.Plus.ι.obj ((Stacks.Cohomology.derivedSections X U).obj E)) m

/-- For `f : X ⟶ S` locally of finite type, `E` a bounded below object of the derived category of
`𝒪_X`-modules all of whose cohomology sheaves are quasi-coherent, and `m` an integer, the
following three conditions are equivalent:

1. `E` is `m`-pseudo-coherent relative to `S`, that is
   `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom`;
2. there are an affine open covering of `S` and, over each of its members `V i`, an affine open
   covering of `f ⁻¹ᵁ V i` such that `RΓ(U, E)` is `m`-pseudo-coherent relative to `Γ(S, V i)`
   for each member `U` of the latter;
3. `RΓ(U, E)` is `m`-pseudo-coherent relative to `Γ(S, V)` for *every* compatible pair of affine
   opens `U ⊆ f ⁻¹ᵁ V`. -/
public abbrev DerivedSectionsPseudoCoherentComparison [LocallyOfFiniteType f]
    (E : DerivedCategory.Plus X.Modules)
    (_hE : ∀ i : ℤ,
      ((DerivedCategory.Plus.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (m : ℤ) : Prop :=
  List.TFAE [
    Scheme.Hom.IsPseudoCoherentFrom f (DerivedCategory.Plus.ι.obj E) m,
    ∃ (ι : Type u) (V : ι → S.affineOpens),
      (⨆ i, (V i : S.Opens)) = ⊤ ∧
        ∀ i, ∃ (κ : Type u) (U : κ → X.affineOpens),
          (⨆ j, (U j : X.Opens)) = f ⁻¹ᵁ (V i).1 ∧
            ∀ j, ∃ h : (U j).1 ≤ f ⁻¹ᵁ (V i).1,
              f.DerivedSectionsPseudoCoherentOn E m (U j).2 (V i).2 h,
    ∀ (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
      (e : U ≤ f ⁻¹ᵁ V), f.DerivedSectionsPseudoCoherentOn E m hU hV e]

/-- If the derived sections `RΓ(U, E)` are `m`-pseudo-coherent relative to `Γ(S, V)` for every
compatible pair of affine opens, then this holds on an affine open covering: all the affine opens
of `S`, and over each of them all the affine opens of `X` contained in its inverse image. -/
public theorem exists_affineCover_derivedSectionsPseudoCoherentOn [LocallyOfFiniteType f]
    (E : DerivedCategory.Plus X.Modules) (m : ℤ)
    (h : ∀ (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
      (e : U ≤ f ⁻¹ᵁ V), f.DerivedSectionsPseudoCoherentOn E m hU hV e) :
    ∃ (ι : Type u) (V : ι → S.affineOpens),
      (⨆ i, (V i : S.Opens)) = ⊤ ∧
        ∀ i, ∃ (κ : Type u) (U : κ → X.affineOpens),
          (⨆ j, (U j : X.Opens)) = f ⁻¹ᵁ (V i).1 ∧
            ∀ j, ∃ h : (U j).1 ≤ f ⁻¹ᵁ (V i).1,
              f.DerivedSectionsPseudoCoherentOn E m (U j).2 (V i).2 h :=
  ⟨S.affineOpens, id, iSup_affineOpens_eq_top S, fun V ↦
    ⟨{U : X.affineOpens // U.1 ≤ f ⁻¹ᵁ (V : S.Opens)}, fun U ↦ U.1,
      iSup_affineOpens_subtype_eq _, fun U ↦ ⟨U.2, h _ U.1.2 _ V.2 _⟩⟩⟩

end AlgebraicGeometry

end
