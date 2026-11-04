module

public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatKunneth.KunnethFlatSheaves
public import StacksFrontier.AlgebraicGeometry.Varieties.KunnethUnconditional
public import StacksFrontier.Homology.KunnethTopDegree

/-!
# The Künneth formula in the top degree, for two quasi-coherent modules

Let `a : X ⟶ S` and `b : Y ⟶ S` be quasi-compact quasi-separated morphisms of schemes with `S`
affine, `A = Γ(S, 𝒪_S)`, let `ℱ` on `X` and `𝒢` on `Y` be quasi-coherent with `𝒢` flat over `S`,
and write `p`, `q` for the projections of `W = X ×_S Y`. If `Hᵐ(X, ℱ) = 0` for `m > i` and
`Hᵐ(Y, 𝒢) = 0` for `m > j`, then

`Hⁱ(X, ℱ) ⊗_A Hʲ(Y, 𝒢) ≅ Hⁱ⁺ʲ(X ×_S Y, p^*ℱ ⊗_{𝒪_W} q^*𝒢)`.

This is the step of the proof of [Stacks, Tag 0G8J] that reads: "by the Künneth formula (either
Lemma 0FLQ or Lemma 0FU4) we see that `H^{2n}(X ×_S X, Ω^{n-1} ⊠ Ωⁿ) = Hⁿ(X, Ω^{n-1}) ⊗_A
Hⁿ(X, Ωⁿ)` … namely, since we are looking in top degree there are no higher tor groups that
intervene". The isomorphism is the composite of the cohomology product of [Stacks, Tag 068H],
invertible in the top degree (`CochainComplex.Kunneth.cohomologyTensorProductIsoTop`), with the
Künneth isomorphism of [Stacks, Tag 0FU4]
(`AlgebraicGeometry.FlatKunneth.isIso_kunnethMapOfSheavesSchemeCanonical_of_isFlatOver`).

The vanishing hypotheses enter through the amplitude of `RΓ(X, ℱ)`: an object `RΓ(X, ℱ[0])` of
`D(A)` lies in degrees `≤ i` exactly when `Hᵐ(X, ℱ) = 0` for `m > i`
(`AlgebraicGeometry.FlatKunneth.isLE_sectionsOverBase_singleD`), the cohomology modules of
`RΓ(X, ℱ[0])` being the right derived functors of global sections
(`AlgebraicGeometry.homologyIso_sectionsOverBase`).

## Main results

* `AlgebraicGeometry.FlatKunneth.isLE_sectionsOverBase_singleD`: `RΓ(X, ℱ[0]) ∈ D^{≤ i}(A)` as
  soon as `Hᵐ(X, ℱ) = 0` for `m > i`.
* `AlgebraicGeometry.FlatKunneth.kunnethTopDegreeIso`: the top-degree Künneth isomorphism.

## References

* [Stacks Project, Tag 0FU4](https://stacks.math.columbia.edu/tag/0FU4)
* [Stacks Project, Tag 068H](https://stacks.math.columbia.edu/tag/068H)
* [Stacks Project, Tag 0G8J](https://stacks.math.columbia.edu/tag/0G8J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace
open Stacks.Cohomology.DerivedSectionsLeray (sectionsOverOpen)
open Stacks.Cohomology.GlobalKunneth (baseRing tensorBase sectionsOverBase singleD
  kunnethMapOfSheavesSchemeCanonical)

open scoped Stacks.StandardDerivedModel

universe u

namespace AlgebraicGeometry.FlatKunneth

section Amplitude

variable {S X : Scheme.{u}} (c : X ⟶ S)

/-- **The cohomology of `RΓ(X, ℱ[0])` over `Γ(S, 𝒪_S)` vanishes above `i` as soon as that of `ℱ`
does.** The cohomology modules of `RΓ(X, ℱ[0])` in nonnegative degrees are the right derived
functors of global sections at `ℱ` with scalars restricted
(`AlgebraicGeometry.homologyIso_sectionsOverBase`), and those in negative degrees vanish. -/
theorem isLE_sectionsOverBase_singleD (F : X.Modules) (i : ℤ)
    (hF : ∀ m : ℕ, i < m →
      IsZero (((sectionsOverOpen X.toRingedSpace ⊤).rightDerived m).obj F)) :
    ((sectionsOverBase c.toLRSHom.toShHom).obj (singleD F)).IsLE i := by
  rw [DerivedCategory.isLE_iff]
  intro m hm
  have e := (sectionsOverBase c.toLRSHom.toShHom).mapIso
    ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app F)
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ m).mapIso e.symm)
  rcases lt_or_ge m 0 with hneg | hpos
  · exact isZero_homology_sectionsOverBase c m hneg F
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = (k : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg hpos).symm⟩
    refine IsZero.of_iso ?_ ((homologyIso_sectionsOverBase c k).app F)
    have h : Subsingleton (((sectionsOverOpen X.toRingedSpace ⊤).rightDerived k).obj F) :=
      ModuleCat.isZero_iff_subsingleton.mp (hF k hm)
    exact ModuleCat.isZero_iff_subsingleton.mpr h

end Amplitude

section TopDegree

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **The Künneth isomorphism in the top degree** (the step "since we are looking in top degree
there are no higher tor groups that intervene" of the proof of [Stacks, Tag 0G8J]). Let
`a : X ⟶ S` and `b : Y ⟶ S` be quasi-compact quasi-separated with `S` affine, `A = Γ(S, 𝒪_S)`,
and let `ℱ` on `X` and `𝒢` on `Y` be quasi-coherent with `𝒢` flat over `S`. If `RΓ(X, ℱ)` lies in
degrees `≤ i` and `RΓ(Y, 𝒢)` in degrees `≤ j`, then

`Hⁱ(RΓ(X, ℱ)) ⊗_A Hʲ(RΓ(Y, 𝒢)) ≅ Hⁱ⁺ʲ(RΓ(X ×_S Y, p^*ℱ ⊗ q^*𝒢))`,

the cohomology product of [Stacks, Tag 068H] followed by the Künneth isomorphism of
[Stacks, Tag 0FU4]. -/
def kunnethTopDegreeIso [IsAffine S] [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b]
    [QuasiSeparated b] (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hG : IsFlatOver b.toLRSHom.toShHom G) (i j : ℤ)
    [((sectionsOverBase a.toLRSHom.toShHom).obj (singleD F)).IsLE i]
    [((sectionsOverBase b.toLRSHom.toShHom).obj (singleD G)).IsLE j] :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace)) i).obj
        ((sectionsOverBase a.toLRSHom.toShHom).obj (singleD F)) ⊗
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace)) j).obj
        ((sectionsOverBase b.toLRSHom.toShHom).obj (singleD G)) ≅
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace)) (i + j)).obj
      ((sectionsOverBase (pullback.fst a b ≫ a).toLRSHom.toShHom).obj
        (singleD (externalTensorProduct a b F G))) :=
  CochainComplex.Kunneth.cohomologyTensorProductIsoTop _ _ i j ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace)) (i + j)).mapIso
      (@asIso _ _ _ _ (kunnethMapOfSheavesSchemeCanonical a b F G)
        (isIso_kunnethMapOfSheavesSchemeCanonical_of_isFlatOver a b F G hG))

/-- The top-degree Künneth isomorphism is the cohomology product of [Stacks, Tag 068H] followed by
the Künneth map of [Stacks, Tag 0FU4] in degree `i + j`. -/
theorem kunnethTopDegreeIso_hom [IsAffine S] [QuasiCompact a] [QuasiSeparated a]
    [QuasiCompact b] [QuasiSeparated b] (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] (hG : IsFlatOver b.toLRSHom.toShHom G) (i j : ℤ)
    [((sectionsOverBase a.toLRSHom.toShHom).obj (singleD F)).IsLE i]
    [((sectionsOverBase b.toLRSHom.toShHom).obj (singleD G)).IsLE j] :
    (kunnethTopDegreeIso a b F G hG i j).hom =
      (RingTheory.TorProducts.cohomologyTensorProduct _ _ i j).map ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace)) (i + j)).map
          (kunnethMapOfSheavesSchemeCanonical a b F G) :=
  rfl

end TopDegree

end AlgebraicGeometry.FlatKunneth

end
