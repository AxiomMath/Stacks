module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeNormalizationExactSequence
public import StacksFrontier.AlgebraicGeometry.Curves.SheafDerivationStalk

/-!
# Descending a vector field from the normalization: the right-to-left direction of Tag 0E68

Let `X` be a reduced scheme over a field `k` and let `ν : X^ν ⟶ X` be its normalization. A vector
field `D'` on `X^ν` — a `k`-derivation of `𝒪_{X^ν}` in the sense of Tag 0E66 — is `ν^♯` applied
to a unique vector field on `X` as soon as, at every point `x` of `X`, either `ν` is an
isomorphism on the stalk at `x`, or `𝒪_{X, x}` is a nodal `k`-algebra and the derivation `D'`
induces on `(ν_* 𝒪_{X^ν})_x` fixes the two points of the normalization above `x`.

This closes the right-to-left direction of
[Stacks, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68) once the node data at a point is
given, by composing the five statements that were already available: the descent criterion
`Stacks.Curves.existsUnique_descend_iff_preserves`, its localization
`Stacks.Curves.preserves_of_germ_mem_range`, the injectivity
`Stacks.Curves.app_normalization_injective`, the coatom computation behind
`Ring.deltaInvariant A = 1`, and the local criterion
`Stacks.Curves.mem_range_of_fixes_of_isCoatom`, with the derivation on the stalk supplied by
`Stacks.Curves.stalkDerivation`.

## Main definitions

* `Stacks.Curves.SheafDerivationOf.Fixes` — a vector field fixes a closed point, for a structure
  morphism given explicitly; the same condition as `Stacks.Curves.SheafDerivation.Fixes`.

## Main results

* `Stacks.Curves.mem_vanishingIdeal_ideal_iff` — on an affine open the vanishing ideal sheaf of a
  closed point consists of the sections vanishing at that point.
* `Stacks.Curves.SheafDerivationOf.fixes_iff_basicOpen` — fixing a point, stated through the
  non-vanishing loci rather than the ideal sheaf.
* `Stacks.Curves.fixes_stalkDerivation_of_fixes` — the bridge: a vector field fixing a point `y`
  of `Y` in the sheaf-theoretic sense induces a derivation of `(ν_* 𝒪_Y)_{ν y}` fixing the
  `k`-point that `y` cuts out, in the sense of `Stacks.Curves.NodalVectorFields.Fixes`.
* `Stacks.Curves.isCoatom_range_algebraMap_normalizationPushforwardStalk` — at a node the image
  of the local ring is a coatom in the stalk of the direct image.
* `Stacks.Curves.preserves_of_isCoatom_of_fixes` and
  `Stacks.Curves.existsUnique_descend_normalization_of_fixes` — the descent itself.

## Implementation notes

The identification of the vanishing ideal sheaf on an affine open needs no closedness and no
case distinction on whether the point lies in the open: on `U` the ideal is the vanishing ideal
of `U.2.fromSpec ⁻¹' {y}`, so membership asks that `s` lie in every prime of `Γ(X, U)` over `y`,
which through `AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_basicOpen` is exactly that `y`
lies outside `X.basicOpen s`. When `y ∉ U` there is no such prime and `y ∉ X.basicOpen s` because
`X.basicOpen s ≤ U`, so both sides hold.

`Stacks.Curves.SheafDerivationOf.Fixes` repeats `Stacks.Curves.SheafDerivation.Fixes` for an
explicit structure morphism rather than a `Scheme.Over` instance, because the globalisation
compares two structure morphisms at once; the two conditions are the same by definition, which is
`Stacks.Curves.SheafDerivation.fixes_iff`. Neither refers to the structure morphism at all.

The bridge passes from the stalk to an affine open twice: a germ with `ε`-value zero has a
representative over some open `U ∋ x`, which must then be restricted to an affine open `V ∋ y`
inside `ν ⁻¹ᵁ U` for the sheaf-level `Fixes` to apply (`AlgebraicGeometry.Scheme.
isBasis_affineOpens`), and the conclusion is transported back out of `V` because
`AlgebraicGeometry.Scheme.basicOpen_res` intersects the non-vanishing locus with `V`, which
contains `y`. The hypothesis on `ε` is that its vanishing on a germ says that a representative
vanishes at `y`; for a node of a curve over an algebraically closed field `ε` is the residue at
one of the two points above the node, and that hypothesis holds because the residue field there
is `k`.

The coatom property is the one computation the node case rests on. It is stated for
`integralClosure 𝒪_{X, x} (Frac 𝒪_{X, x})` and transported to `(ν_* 𝒪_{X^ν})_x` along Tag
0C3B(2) through the order isomorphism of submodule lattices that an `𝒪_{X, x}`-linear equivalence
induces (`Submodule.orderIsoMapComap`, `OrderIso.isCoatom_iff`); the image of `𝒪_{X, x}` is
carried to the image of `𝒪_{X, x}` because the equivalence is one of algebras.

Nothing here derives the node data from the geometry: that `𝒪_{X, x}` is nodal at a singular
point of an at-worst-nodal curve, that exactly two points of `X^ν` lie above a node, and that
their residue fields are `k`, are hypotheses of
`Stacks.Curves.existsUnique_descend_normalization_of_fixes` rather than consequences of a
properness or algebraic-closedness assumption. The left-to-right direction of the tag — extending
a vector field on `X` to `X^ν`, which the source gets from `𝒪_{X^ν, x'} = k + (u)` — is not
addressed.

## References

* [Stacks Project, Tag 0C1X](https://stacks.math.columbia.edu/tag/0C1X)
* [Stacks Project, Tag 0E66](https://stacks.math.columbia.edu/tag/0E66)
* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k]

/-- **The vanishing ideal sheaf of a point, on an affine open, is the sections vanishing at the
point.** On an affine open `U` the quasi-coherent ideal sheaf of a closed point `y` is the
vanishing ideal of the primes of `Γ(X, U)` lying over `y`, and a section belongs to it exactly
when `y` is outside its non-vanishing locus. If `y ∉ U` both sides hold vacuously. -/
theorem mem_vanishingIdeal_ideal_iff {X : Scheme.{u}} {y : X} (hy : IsClosed ({y} : Set X))
    (U : X.affineOpens) (s : Γ(X, U)) :
    s ∈ (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).ideal U ↔ y ∉ X.basicOpen s := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  have hpre : ∀ p : PrimeSpectrum Γ(X, U),
      p ∈ PrimeSpectrum.basicOpen s ↔ U.2.fromSpec.base p ∈ X.basicOpen s := by
    intro p
    have h := congrArg (fun W : (Spec Γ(X, U.1)).Opens => p ∈ W)
      (U.2.fromSpec_preimage_basicOpen s)
    exact (eq_iff_iff.mp h).symm
  refine ⟨fun hs hmem => ?_, fun hs p hp => ?_⟩
  · obtain ⟨p, hp⟩ : y ∈ Set.range U.2.fromSpec.base := by
      rw [U.2.range_fromSpec]; exact X.basicOpen_le s hmem
    exact (PrimeSpectrum.mem_basicOpen s p).mp ((hpre p).mpr (hp ▸ hmem))
      (hs p (by exact hp))
  · refine not_not.mp fun hcon => hs ?_
    have := (hpre p).mp ((PrimeSpectrum.mem_basicOpen s p).mpr hcon)
    rwa [show U.2.fromSpec.base p = y from hp] at this

namespace SheafDerivationOf

variable {Y : Scheme.{u}} {g : Y ⟶ Spec (.of k)}

/-- A vector field fixes a closed point of `Y` when it preserves the point's vanishing ideal
sheaf, imposed on affine opens as in Section 53.26. The structure morphism plays no role, so this
is `Stacks.Curves.SheafDerivation.Fixes` for `g = Y ↘ Spec k`. -/
def Fixes (D : SheafDerivationOf g) (y : Y) (hy : IsClosed ({y} : Set Y)) : Prop :=
  ∀ (V : Y.affineOpens) (s : Γ(Y, V)),
    s ∈ (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).ideal V →
      D.onSections s ∈ (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).ideal V

/-- Fixing a point is a condition on the vanishing of sections at it. -/
theorem fixes_iff_basicOpen (D : SheafDerivationOf g) (y : Y) (hy : IsClosed ({y} : Set Y)) :
    D.Fixes y hy ↔ ∀ (V : Y.affineOpens) (s : Γ(Y, V)),
      y ∉ Y.basicOpen s → y ∉ Y.basicOpen (D.onSections s) := by
  refine ⟨fun h V s hs => ?_, fun h V s hs => ?_⟩
  · exact (mem_vanishingIdeal_ideal_iff hy V _).mp
      (h V s ((mem_vanishingIdeal_ideal_iff hy V s).mpr hs))
  · exact (mem_vanishingIdeal_ideal_iff hy V _).mpr
      (h V s ((mem_vanishingIdeal_ideal_iff hy V s).mp hs))

end SheafDerivationOf

/-- The `Fixes` condition of `Stacks.Curves.SheafDerivation` is the one of
`Stacks.Curves.SheafDerivationOf`: fixing a point does not refer to the structure morphism. -/
theorem SheafDerivation.fixes_iff {X : Scheme.{u}} [X.Over (Spec (.of k))]
    (D : SheafDerivation k X) (x : X) (hx : IsClosed ({x} : Set X)) :
    D.Fixes x hx ↔ SheafDerivationOf.Fixes D x hx := Iff.rfl

section Bridge

variable {X Y : Scheme.{u}} {hX : X ⟶ Spec (.of k)}

/-- **A vector field fixing a point of `Y` fixes it on the stalk of the direct image.** Let
`y` be a closed point of `Y` lying over `x`, and let `ε` be a `k`-algebra map from the stalk
`(ν_* 𝒪_Y)_x` to `k` whose vanishing on a germ says that a representative vanishes at `y` — the
residue at `y`. If `D'` fixes `y` in the sense of Section 53.26, then the derivation `D'` induces
on `(ν_* 𝒪_Y)_x` fixes the point cut out by `ε` in the sense of
`Stacks.Curves.NodalVectorFields.Fixes`.

This is the bridge between the sheaf-level `Fixes` of
`Stacks.Curves.SheafDerivationOf.Fixes` and the pointwise one that
`Stacks.Curves.mem_range_algebraMap_of_fixes` consumes. -/
theorem fixes_stalkDerivation_of_fixes (ν : Y ⟶ X) (D' : SheafDerivationOf (ν ≫ hX))
    (y : Y) (hy : IsClosed ({y} : Set Y)) (hfix : D'.Fixes y hy) (x : X)
    (hxy : ν.base y = x) :
    letI := directImageStalkFieldAlgebra ν hX x
    ∀ ε : ((ν.base _* Y.presheaf).stalk x) →ₐ[k] k,
      (∀ (U : X.Opens) (hxU : x ∈ U) (s : Γ(Y, ν ⁻¹ᵁ U)),
          ε ((ν.base _* Y.presheaf).germ U x hxU s) = 0 ↔ y ∉ Y.basicOpen s) →
        NodalVectorFields.Fixes ε (stalkDerivation ν D' x) := by
  let := directImageStalkFieldAlgebra ν hX x
  intro ε hε z hz
  obtain ⟨U, hxU, s, hsz⟩ := TopCat.Presheaf.exists_germ_eq (ν.base _* Y.presheaf) z
  subst hsz
  have hvan : y ∉ Y.basicOpen s := (hε U hxU s).mp hz
  have hyU : y ∈ ν ⁻¹ᵁ U := by
    show ν.base y ∈ U
    rw [hxy]; exact hxU
  obtain ⟨-, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyU (ν ⁻¹ᵁ U).2
  have hVle : V ≤ ν ⁻¹ᵁ U := hVU
  have hrest : y ∉ Y.basicOpen ((Y.presheaf.map (homOfLE hVle).op).hom s) := by
    rw [Scheme.basicOpen_res]
    exact fun hc => hvan hc.2
  have hres := (D'.fixes_iff_basicOpen y hy).mp hfix ⟨V, hV⟩ _ hrest
  rw [SheafDerivationOf.onSections_restrict, Scheme.basicOpen_res] at hres
  have hvan' : y ∉ Y.basicOpen (D'.onSections s) := fun hc => hres ⟨hyV, hc⟩
  rw [stalkDerivation_germ]
  exact (hε U hxU (D'.onSections s)).mpr hvan'

end Bridge

section Node

open Stacks.AlgebraicGeometry.NormalizationQuotient Stacks.NormalizationStalkAmbient

/-- **At a node the image of the local ring is a coatom in the stalk of the direct image of the
normalization.** This is
`Stacks.Curves.isCoatom_range_algebraMap_integralClosure_of_isNodalAlgebra` transported along Tag
0C3B(2), which identifies `(ν_* 𝒪_{X^ν})_x` with the integral closure of `𝒪_{X, x}` in its total
ring of fractions as an `𝒪_{X, x}`-algebra. -/
theorem isCoatom_range_algebraMap_normalizationPushforwardStalk (k : Type u) [Field k]
    (X : Scheme.{u}) [IsReduced X]
    (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) [IsNoetherianRing (X.presheaf.stalk x)] [Algebra k (X.presheaf.stalk x)]
    (hA : IsNodalAlgebra k (X.presheaf.stalk x)) :
    letI := normalizationPushforwardStalkAlgebra X hfin x
    IsCoatom (LinearMap.range (Algebra.linearMap (X.presheaf.stalk x)
      (normalizationPushforwardStalk X hfin x))) := by
  let := normalizationPushforwardStalkAlgebra X hfin x
  have hcomp :
      ((normalizationStalkAlgEquivIntegralClosureSelf X hfin x).toLinearEquiv :
          normalizationPushforwardStalk X hfin x →ₗ[X.presheaf.stalk x]
            integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))) ∘ₗ
        Algebra.linearMap (X.presheaf.stalk x)
          (normalizationPushforwardStalk X hfin x) =
        Algebra.linearMap (X.presheaf.stalk x)
          (integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))) :=
    LinearMap.ext fun a => (normalizationStalkAlgEquivIntegralClosureSelf X hfin x).commutes a
  have hmap : Submodule.map
      ((normalizationStalkAlgEquivIntegralClosureSelf X hfin x).toLinearEquiv :
        normalizationPushforwardStalk X hfin x →ₗ[X.presheaf.stalk x]
          integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x)))
      (LinearMap.range (Algebra.linearMap (X.presheaf.stalk x)
        (normalizationPushforwardStalk X hfin x))) =
      LinearMap.range (Algebra.linearMap (X.presheaf.stalk x)
        (integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x)))) := by
    rw [← LinearMap.range_comp, hcomp]
  have hiso := (Submodule.orderIsoMapComap
      ((normalizationStalkAlgEquivIntegralClosureSelf X hfin x).toLinearEquiv :
        normalizationPushforwardStalk X hfin x ≃ₗ[X.presheaf.stalk x]
          integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x)))).isCoatom_iff
      (LinearMap.range (Algebra.linearMap (X.presheaf.stalk x)
        (normalizationPushforwardStalk X hfin x)))
  rw [Submodule.orderIsoMapComap_apply, hmap] at hiso
  exact hiso.mp
    (isCoatom_range_algebraMap_integralClosure_of_isNodalAlgebra k (X.presheaf.stalk x) hA)

variable {X Y : Scheme.{u}} {hX : X ⟶ Spec (.of k)}

/-- **A vector field fixing the two branch points at every singular point descends.** Let
`ν : Y ⟶ X` be injective on sections of the structure sheaves and let `D'` be a vector field on
`Y`. Suppose that at every point `x` of `X` either `𝒪_{X, x} → (ν_* 𝒪_Y)_x` is surjective — `ν` is
an isomorphism over a neighbourhood of `x`, the smooth case — or the image of `𝒪_{X, x}` is a
coatom and carries two distinct `k`-points of `(ν_* 𝒪_Y)_x` agreeing on it which the induced
derivation fixes. Then `D'` preserves `ν^♯ 𝒪_X`, hence descends.

The second alternative is `Stacks.Curves.mem_range_of_fixes_of_isCoatom`, the local
ring-theoretic content of the right-to-left direction of Tag 0E68, and the first discharges the
points where `ν` is an isomorphism. -/
theorem preserves_of_isCoatom_of_fixes (ν : Y ⟶ X) (D' : SheafDerivationOf (ν ≫ hX))
    (hinj : ∀ U : X.Opens, Function.Injective (ν.app U).hom)
    (h : ∀ x : X,
      letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk hX x).hom.toAlgebra
      letI := directImageStalkAlgebra ν x
      letI := directImageStalkFieldAlgebra ν hX x
      Function.Surjective
          (algebraMap (X.presheaf.stalk x) ((ν.base _* Y.presheaf).stalk x)) ∨
        IsCoatom (LinearMap.range (Algebra.linearMap (X.presheaf.stalk x)
            ((ν.base _* Y.presheaf).stalk x))) ∧
          ∃ ε₁ ε₂ : ((ν.base _* Y.presheaf).stalk x) →ₐ[k] k,
            (∀ a : X.presheaf.stalk x,
                ε₁ (algebraMap (X.presheaf.stalk x) ((ν.base _* Y.presheaf).stalk x) a) =
                  ε₂ (algebraMap (X.presheaf.stalk x)
                    ((ν.base _* Y.presheaf).stalk x) a)) ∧
              ε₁ ≠ ε₂ ∧ NodalVectorFields.Fixes ε₁ (stalkDerivation ν D' x) ∧
                NodalVectorFields.Fixes ε₂ (stalkDerivation ν D' x)) :
    Preserves ν D' := by
  refine preserves_of_stalkDerivation_mem_range ν D' hinj fun x a => ?_
  let : Algebra k (X.presheaf.stalk x) := (fieldToStalk hX x).hom.toAlgebra
  let := directImageStalkAlgebra ν x
  let := directImageStalkFieldAlgebra ν hX x
  rcases h x with hsurj | ⟨hco, ε₁, ε₂, hres, hne, h₁, h₂⟩
  · exact hsurj _
  · exact mem_range_of_fixes_of_isCoatom ε₁ ε₂ hres hne hco (stalkDerivation ν D' x) h₁ h₂
      ⟨a, rfl⟩

/-- **The right-to-left direction of Tag 0E68.** Let `X` be a reduced scheme over `k` with
normalization `ν : X^ν ⟶ X`, and let `D'` be a vector field on `X^ν`. Suppose that at every point
`x` of `X` either `𝒪_{X, x} → (ν_* 𝒪_{X^ν})_x` is surjective — the points where `ν` is an
isomorphism, in particular the smooth points — or `𝒪_{X, x}` is a nodal `k`-algebra carrying two
distinct `k`-points of `(ν_* 𝒪_{X^ν})_x` with the same restriction to `𝒪_{X, x}` which the
derivation induced by `D'` fixes. Then `D'` is `ν^♯` applied to a unique vector field on `X`.

The two `k`-points are the residues at the two points of `X^ν` above the node, and
`Stacks.Curves.fixes_stalkDerivation_of_fixes` is what turns "`D'` fixes those two points" in the
sense of Section 53.26 into the hypothesis here. The nodality of the local ring enters only
through `Stacks.Curves.isCoatom_range_algebraMap_normalizationPushforwardStalk`, the delta
invariant computation of Tag 0C4A, and the identification of the image of `𝒪_{X, x}` with the
elements of equal branch residues is
`Stacks.Curves.range_algebraMap_integralClosure_eq_equalizer`, the sequence of Tag 0C1X. -/
theorem existsUnique_descend_normalization_of_fixes (k : Type u) [Field k] (X : Scheme.{u})
    [IsReduced X] (hX : X ⟶ Spec (.of k))
    (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hnoeth : ∀ x : X, IsNoetherianRing (X.presheaf.stalk x))
    (D' : SheafDerivationOf (Scheme.normalization X hfin ≫ hX))
    (h : ∀ x : X,
      letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk hX x).hom.toAlgebra
      letI := directImageStalkAlgebra (Scheme.normalization X hfin) x
      letI := directImageStalkFieldAlgebra (Scheme.normalization X hfin) hX x
      Function.Surjective
          (algebraMap (X.presheaf.stalk x)
            (((Scheme.normalization X hfin).base _*
              (Scheme.normalizationScheme X hfin).presheaf).stalk x)) ∨
        IsNodalAlgebra k (X.presheaf.stalk x) ∧
          ∃ ε₁ ε₂ : (((Scheme.normalization X hfin).base _*
              (Scheme.normalizationScheme X hfin).presheaf).stalk x) →ₐ[k] k,
            (∀ a : X.presheaf.stalk x,
                ε₁ (algebraMap (X.presheaf.stalk x) _ a) =
                  ε₂ (algebraMap (X.presheaf.stalk x) _ a)) ∧
              ε₁ ≠ ε₂ ∧
                NodalVectorFields.Fixes ε₁
                    (stalkDerivation (Scheme.normalization X hfin) D' x) ∧
                  NodalVectorFields.Fixes ε₂
                    (stalkDerivation (Scheme.normalization X hfin) D' x)) :
    ∃! D : SheafDerivationOf hX, ∀ (U : X.Opens) (s : Γ(X, U)),
      ((Scheme.normalization X hfin).app U).hom (D.onSections s) =
        D'.onSections (((Scheme.normalization X hfin).app U).hom s) := by
  refine (existsUnique_descend_iff_preserves D' (app_normalization_injective X hfin)).mpr
    (preserves_of_isCoatom_of_fixes _ D' (app_normalization_injective X hfin) fun x => ?_)
  let : Algebra k (X.presheaf.stalk x) := (fieldToStalk hX x).hom.toAlgebra
  let := hnoeth x
  let := directImageStalkAlgebra (Scheme.normalization X hfin) x
  let := directImageStalkFieldAlgebra (Scheme.normalization X hfin) hX x
  rcases h x with hsurj | ⟨hA, ε₁, ε₂, hres, hne, h₁, h₂⟩
  · exact Or.inl hsurj
  · refine Or.inr ⟨?_, ε₁, ε₂, hres, hne, h₁, h₂⟩
    exact isCoatom_range_algebraMap_normalizationPushforwardStalk k X hfin x hA

end Node

end Stacks.Curves

end
