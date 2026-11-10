module

public import StacksFrontier.AlgebraicGeometry.Conormal.ConormalSectionsRing
public import StacksFrontier.Examples.Scheme.RegularImmersionNotPermanentInMiddle

/-!
# `Γ(Spec(R ⧸ I), 𝒞_*) ≅ Gr_I(R)`, in the form part (2) of [Stacks, Tag 0897] consumes

Let `R` be a commutative ring and `I ⊆ R` an ideal, and let `i : Spec(R ⧸ I) ⟶ Spec R` be the
closed immersion it cuts out (`Stacks.ClosedImmersion.AffineConormal.quotImmersion`). This file
instantiates `Stacks.Conormal.conormalSectionsRingEquiv` at `i` and the affine open `⊤`, giving a
**ring isomorphism**

`Gr_I(R) ≃+* Γ(Spec(R ⧸ I), 𝒞_*)`

onto the global sections of the ungraded realization of the conormal algebra of `i`, carrying
`algebraMap (R ⧸ I) (Gr_I(R))` to the structure map of the algebra sheaf.

That pair is exactly the `ρ` and `hρ` of
`Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_of_gradedAlgebraSections`,
with `k = R ⧸ I` and the graded algebra taken as
`(Stacks.Conormal.conormalAlgebra i).algebra`: the ungraded realization
`Stacks.Conormal.conormalAlgebraSheaf i` *is*
`Stacks.RelativeSpec.gradedAlgebraSheaf _ (conormalAlgebra i).algebra
(conormalAlgebra i).mul_comm_int` by definition. At the fibre of [Stacks, Tag 0D2N] it is used
with `R = 𝒪_{Y,y}`, `I = 𝔪`, `R ⧸ I = κ(y)` and `Gr_I(R) = Gr_𝔪(𝒪_{Y,y})`, Noetherian by
`AssociatedGraded.isNoetherianRing_gradedRing`.

## The two steps

1. **The chart ideal of `i` over `⊤` is `I`, transported along `Γ(Spec R, ⊤) ≅ R`**
   (`Stacks.Conormal.map_chartIdeal_quotImmersion`). The chart ideal is by definition the kernel
   of the map on global sections, which `Stacks.Examples.ker_appTop_spec_map` computes as the
   preimage of `ker(R ⟶ R ⧸ I) = I` along `Γ(Spec R, ⊤) ≅ R`; the preimage of an ideal along a
   surjection maps onto it again (`Ideal.map_comap_of_surjective`). The transport of the
   associated graded ring itself is `AssociatedGraded.congrRingEquiv`.
2. **The chart-level identification at `U = ⊤`.** `Spec R` is affine, `i` is a closed immersion,
   so it restricts to one over every open and in particular over `⊤`; `i ⁻¹ᵁ ⊤` is `⊤` by
   `rfl`.

## Main results

* `Stacks.Conormal.map_chartIdeal_quotImmersion`: the chart ideal of `i` over `⊤` is `I`, read
  through `Γ(Spec R, ⊤) ≅ R`.
* `Stacks.Conormal.specConormalSectionsRingEquiv`: **`Gr_I(R) ≃+* Γ(Spec(R ⧸ I), 𝒞_*)`.**
* `Stacks.Conormal.specConormalSectionsRingEquiv_algebraMap`: **it carries
  `algebraMap (R ⧸ I) (Gr_I(R))` to the structure map of the algebra sheaf.**

## The distance from here to [Stacks, Tag 0D2M]'s one remaining input

Both halves of [Stacks, Tag 0D2M] now stand on one common hypothesis, in the spelling

`∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ p : ℕ, 0 < p → ∀ n : ℕ, IsZero (((moduleGlobalSections X
).rightDerived p).obj (kernel (idealPowerQuotientDrop (baseIdealSheaf A 𝔪 f) (Nat.le_succ n)
(twistModule X L F d))))`

for `Stacks.Cohomology.AffineBase.moduleGlobalSections`, while the engine fed by `ρ` and `hρ`
concludes

`∃ d₀ : ℕ, ∀ d p : ℕ, d₀ ≤ d → 0 < p → ∀ n : ℕ, IsZero (Hgroup Z.ringCatSheaf ⊤ p
(tensorModules Z (M.piece (n : ℤ)) (tensorPowModule Z L (d : ℤ))))`.

The four differences are these, and none of them is about `ρ` or `hρ`.

* **The scheme.** The engine concludes on `Z`, which at the fibre is `X_y`; the hypothesis is on
  `X`. No restatement closes this: it needs the cohomology comparison along the closed immersion
  `X_y ⟶ X`, which is where [Stacks, Tag 089W] and [Stacks, Tag 087T] enter, and for which
  `Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward` asks no quasi-coherence.
* **The module.** `tensorModules Z (M.piece (n : ℤ)) (tensorPowModule Z L (d : ℤ))` *is*
  `twistModule Z L (M.piece (n : ℤ)) (d : ℤ)`, that being an `abbrev`, so this half of the
  spelling already agrees once the scheme does. What is still owed is that `M.piece n` is the
  fibre realization of `𝔪 ⁿℱ/𝔪 ⁿ⁺¹ℱ` — the graded module — and that the twist may be moved
  across the adic quotient, `𝔪 ⁿ(ℱ(d))/𝔪 ⁿ⁺¹(ℱ(d)) ≅ (𝔪 ⁿℱ/𝔪 ⁿ⁺¹ℱ)(d)`, which holds because
  `L` is invertible. In the hypothesis the twist is taken *inside* the quotient and in the
  engine's conclusion *outside* the graded piece.
* **The cohomology functor.** `Stacks.Cohomology.Hgroup R ⊤ p` is the `p`-th right derived
  functor of `Stacks.Cohomology.secF R ⊤ = SheafOfModules.toSheaf R ⋙ (sections at ⊤ in
  AddCommGrpCat)`, valued in `AddCommGrpCat`; `moduleGlobalSections X` is
  `SheafOfModules.evaluation X.ringCatSheaf (op ⊤)`, valued in `ModuleCat Γ(X, ⊤)`. These are
  different functors into different categories, so `IsZero` of one is not `IsZero` of the other
  by `rfl`; the two are related by the forgetful functor `ModuleCat Γ(X, ⊤) ⥤ AddCommGrpCat`,
  and the cheap route between the two `IsZero`s is `Subsingleton` on both sides, Mathlib's
  `ModuleCat.isZero_iff_subsingleton` on one.
* **The degree.** `d₀ : ℕ` with `∀ d : ℕ` against `d₀ : ℤ` with `∀ d : ℤ`: taking the integer
  `d₀` to be the engine's recast by `Int.ofNat` loses nothing, since `d₀ ≤ d` with `0 ≤ d₀`
  forces `d = (d' : ℕ)` (`Int.eq_ofNat_of_zero_le`). Reordering `∀ d p : ℕ` into
  `∀ d, _ → ∀ p` is free. This difference is a one-line restatement.

So the first two are mathematics, owed by the fibre-module comparison and by [Stacks, Tag 0D2M];
the last two are restatements, and they belong on the far side of the first, where the scheme is
already `X`. Nothing here is a comparison layer and no bridging lemma is introduced.

## Implementation notes

The kernel of `Spec φ` on global sections is not recomputed here: it is
`Stacks.Examples.ker_appTop_spec_map`, which is stated for an arbitrary `φ : R ⟶ S` of
`CommRingCat`, and importing the module it lives in is what this file does instead of re-deriving
the naturality square `AlgebraicGeometry.Scheme.ΓSpecIso_naturality`. The import is why the
chart-level statement is in its own module: that one stays inside the `AlgebraicGeometry` tree,
and only this instantiation — a leaf of the [Stacks, Tag 0D2N] chain — pays for the heavier
closure.

The immersion is `Stacks.ClosedImmersion.AffineConormal.quotImmersion`, which already exists; no
new name is introduced for `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`.

`R ⧸ I` is spelled `Stacks.ClosedImmersion.IdealSheafAffine.quotRing I`, an `abbrev` for
`CommRingCat.of (↥R ⧸ I)`, so it is reducibly the `CommRingCat.of k` the consumer asks for.

No `@[stacks]` attribute is attached: this is one input of part (2) of [Stacks, Tag 0897] at the
fibre and not the assertion of a numbered result.

## References

* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.RelativeSpec
open Stacks.ClosedImmersion.AffineConormal Stacks.ClosedImmersion.IdealSheafAffine
open scoped DirectSum

universe u

namespace Stacks.Conormal

variable (R : CommRingCat.{u}) (I : Ideal R)

/-- `Spec(R ⧸ I) ⟶ Spec R` is a closed immersion, the quotient map being surjective. -/
instance isClosedImmersion_quotImmersion : IsClosedImmersion (quotImmersion R I) :=
  IsClosedImmersion.spec_of_surjective (quotHom I) Ideal.Quotient.mk_surjective

/-- A closed immersion restricts to a closed immersion over `⊤`, which is the hypothesis the
chart-level identification of [Stacks, Tag 0633] takes. -/
theorem isClosedImmersion_resLE_top_quotImmersion :
    IsClosedImmersion
      ((quotImmersion R I).resLE ⊤ (quotImmersion R I ⁻¹ᵁ ⊤) le_rfl) := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- **The chart ideal of `Spec(R ⧸ I) ⟶ Spec R` over `⊤` is `I`**, read through
`Γ(Spec R, ⊤) ≅ R`. The chart ideal is the kernel of the map on global sections, which
`Stacks.Examples.ker_appTop_spec_map` identifies with the preimage of `ker(R ⟶ R ⧸ I) = I`
(`Ideal.mk_ker`) along that isomorphism. -/
theorem map_chartIdeal_quotImmersion :
    Ideal.map ((Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv : ↥Γ(Spec R, ⊤) →+* ↥R)
        (chartIdeal (quotImmersion R I) ⟨⊤, isAffineOpen_top (Spec R)⟩) = I := by
  have hker : chartIdeal (quotImmersion R I) ⟨⊤, isAffineOpen_top (Spec R)⟩ =
      Ideal.comap ((Scheme.ΓSpecIso R).hom).hom I :=
    (show chartIdeal (quotImmersion R I) ⟨⊤, isAffineOpen_top (Spec R)⟩ =
        RingHom.ker ((quotImmersion R I).appTop).hom from rfl).trans
      ((Stacks.Examples.ker_appTop_spec_map (quotHom I)).trans
        (congrArg (Ideal.comap ((Scheme.ΓSpecIso R).hom).hom) Ideal.mk_ker))
  rw [hker]
  exact Ideal.map_comap_of_surjective _
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.surjective I

/-- **`Gr_I(R) ≃+* Γ(Spec(R ⧸ I), 𝒞_*)`**: the associated graded ring of an ideal `I ⊆ R` is the
ring of global sections of the ungraded realization of the conormal algebra of the closed
immersion `Spec(R ⧸ I) ⟶ Spec R`.

This is `Stacks.Conormal.conormalSectionsRingEquiv` at the affine open `⊤`, with the associated
graded ring of the chart ideal moved to that of `I` along `Γ(Spec R, ⊤) ≅ R` by
`AssociatedGraded.congrRingEquiv`. -/
def specConormalSectionsRingEquiv :
    AssociatedGraded.gradedRing I ≃+*
      ↥(AlgebraSheaf.sections (conormalAlgebraSheaf (quotImmersion R I)) ⊤) :=
  (AssociatedGraded.congrRingEquiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
      (map_chartIdeal_quotImmersion R I)).symm.trans
    (conormalSectionsRingEquiv (quotImmersion R I) ⟨⊤, isAffineOpen_top (Spec R)⟩
      (isClosedImmersion_resLE_top_quotImmersion R I))

/-- The map on global sections of `Spec(R ⧸ I) ⟶ Spec R` is the quotient map, read through the
identifications `Γ(Spec R, ⊤) ≅ R` and `Γ(Spec(R ⧸ I), ⊤) ≅ R ⧸ I`. This is
`AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality`. -/
theorem appTop_quotImmersion_specTopEquiv (a : ↥R) :
    ((quotImmersion R I).appTop).hom
        ((Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv a) =
      (Scheme.ΓSpecIso (quotRing I)).symm.commRingCatIsoToRingEquiv
        (Ideal.Quotient.mk I a) :=
  (congrArg (fun κ : R ⟶ Γ(Spec (quotRing I), ⊤) => κ.hom a)
    (Scheme.ΓSpecIso_inv_naturality (quotHom I))).symm

/-- **The identification carries `algebraMap (R ⧸ I) (Gr_I(R))` to the structure map of the
algebra sheaf.** Together with `Stacks.Conormal.specConormalSectionsRingEquiv` this is the pair
`ρ`, `hρ` of
`Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_of_gradedAlgebraSections`.

The `R ⧸ I`-algebra structure of `Gr_I(R)` is `AssociatedGraded.algebraQuotient`: on the class of
`a : R` the structure map is the degree-zero class of `a`
(`AssociatedGraded.algebraMap_quotient_mk`), which
`Stacks.Conormal.conormalSectionsRingEquiv_gradeZeroRingHom` carries to the structural ring map of
the conormal algebra sheaf applied to the image of `a` in `Γ(Spec(R ⧸ I), ⊤)`. -/
theorem specConormalSectionsRingEquiv_algebraMap (c : ↥(quotRing I)) :
    specConormalSectionsRingEquiv R I
        (algebraMap (↥R ⧸ I) (AssociatedGraded.gradedRing I) c) =
      (conormalAlgebraSheaf (quotImmersion R I)).unitTop.hom
        ((Scheme.ΓSpecIso (quotRing I)).symm.commRingCatIsoToRingEquiv c) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) c
  have hsymm : (AssociatedGraded.congrRingEquiv
        (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
        (map_chartIdeal_quotImmersion R I)).symm
      (AssociatedGraded.gradeZeroRingHom I a) =
      AssociatedGraded.gradeZeroRingHom
        (chartIdeal (quotImmersion R I) ⟨⊤, isAffineOpen_top (Spec R)⟩)
        ((Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv a) := by
    have hs : (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv =
        (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm := rfl
    refine (RingEquiv.symm_apply_eq _).2 ?_
    rw [AssociatedGraded.congrRingEquiv_gradeZeroRingHom, hs, RingEquiv.apply_symm_apply]
  change conormalSectionsRingEquiv (quotImmersion R I) ⟨⊤, isAffineOpen_top (Spec R)⟩
      (isClosedImmersion_resLE_top_quotImmersion R I)
      ((AssociatedGraded.congrRingEquiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
        (map_chartIdeal_quotImmersion R I)).symm
          (algebraMap (↥R ⧸ I) (AssociatedGraded.gradedRing I) (Ideal.Quotient.mk I a))) = _
  rw [AssociatedGraded.algebraMap_quotient_mk, hsymm,
    conormalSectionsRingEquiv_gradeZeroRingHom]
  exact congrArg
    (fun z => ((conormalAlgebraSheaf (quotImmersion R I)).hom.hom.app (op ⊤)).hom z)
    (appTop_quotImmersion_specTopEquiv R I a)

end Stacks.Conormal

end
