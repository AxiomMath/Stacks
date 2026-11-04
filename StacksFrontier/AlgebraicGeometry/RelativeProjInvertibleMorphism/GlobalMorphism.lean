module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ClauseThreeConsistency
public import StacksFrontier.AlgebraicGeometry.Scheme.AffinePreimageGluing

/-!
# The global morphism `r_{ℒ,ψ} : U(ψ) ⟶ Proj_S(𝒜)` of Stacks Tag 01O9

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra, `rp` a relative homogeneous
spectrum for `𝒜`, `f : X ⟶ S` a morphism of schemes and `P = (ℒ, ψ)` the datum of
[Stacks, Tag 01O8].  **This file glues the clause (3) prescriptions of [Stacks, Tag 01O9] into the
global morphism**

`r_{ℒ,ψ} : U(ψ) ⟶ Proj_S(𝒜)`

out of the open `U(ψ) ⊆ X` of [Stacks, Tag 01O8], together with its characterizing restriction
property and its uniqueness.

The gluing uses:

* the per-affine-open [Stacks, Tag 01NK] datum `…GradedPowerMap.affineDatum`;
* that the part of `U(ψ)` lying over an affine open `V` of the base is exactly the source of the
  prescription over `V` (`…GradedPowerMap.image_preimage_toBase_eq` and
  `…GradedPowerMap.image_coveringOpen_affineDatum`);
* the consistency of the prescriptions along a nested pair of affine opens,
  `…GradedPowerMap.relativeChart_affineDatum_resLE`, which rests on the coherence
  `…ProjChartRatioPullbackLocalMul.natTensorPowCongr_restrictPowSection_res`;
* and `AlgebraicGeometry.Scheme.glueOverAffinePreimages`, which asks for **no** overlap condition
  at all — only compatibility along the inclusions between the preimages of nested affine opens,
  which is exactly what the consistency supplies.

## Main definitions

* `…GradedPowerMap.chartOver`: the clause (3) prescription over an affine open `V` of the base,
  read on the open `U(ψ_V)` of `X`.
* `…GradedPowerMap.globalMorphism`: **`r_{ℒ,ψ}`**, the glued morphism `U(ψ) ⟶ Proj_S(𝒜)`.

## Main results

* `…GradedPowerMap.homOfLE_chartOver`: the prescriptions are compatible along the inclusion
  `U(ψ_Z) ⊆ U(ψ_V)` for affine `Z ≤ V`.
* `…GradedPowerMap.ι_globalMorphism`: **the characterizing restriction property.**  Over the
  preimage of an affine open `V` of the base, `r_{ℒ,ψ}` is the clause (3) prescription there.
* `…GradedPowerMap.eq_globalMorphism`: **uniqueness.**  `r_{ℒ,ψ}` is the only morphism out of
  `U(ψ)` with that property.
* `…GradedPowerMap.existsUnique_globalMorphism`: the two together.

## Implementation notes

Every identification of opens is made against an isomorphism built out of
`AlgebraicGeometry.Scheme.Hom.isoImage` and a proved equality of opens of `X` — `datumIso` on
`…GradedPowerMap.image_coveringOpen_affineDatum` and `toBaseIso` on
`…GradedPowerMap.image_preimage_toBase_eq` — rather than by transporting along an equality of
opens of a subscheme.  That keeps every compatibility a statement about morphisms into `X`, where
it is settled by `CategoryTheory.cancel_mono` against the inclusion of an open followed by
`AlgebraicGeometry.Scheme.Hom.resLE_comp_ι` and `AlgebraicGeometry.Scheme.homOfLE_ι`.  Doing it
the other way needs a transport of `resLE` along two equalities of opens, which has no lemma here.

## The tag

`θ` is `…GradedPowerMap.theta`, and the whole statement of [Stacks, Tag 01O9] is
`Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.tag01O9`.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjFromSections

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

namespace GradedPowerMap

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f) (rp : RelativeProjData A)

/-! ### The prescription over an affine open of the base, on an open of `X` -/

/-- The covering open of the induced datum over `V`, read as the open `U(ψ_V)` of `X`. -/
public def datumIso (V : S.Opens) :
    ((P.affineDatum V).coveringOpen).toScheme ≅ (P.coveringOpenOver V).toScheme :=
  (f ⁻¹ᵁ V).ι.isoImage (P.affineDatum V).coveringOpen
    ≪≫ T.isoOfEq (P.image_coveringOpen_affineDatum V)

/-- `datumIso` followed by the inclusion of `U(ψ_V)` into `X` is the inclusion of the covering
open of the induced datum into `f⁻¹(V)`, followed by the inclusion of `f⁻¹(V)` into `X`. -/
public theorem datumIso_hom_ι (V : S.Opens) :
    (P.datumIso V).hom ≫ (P.coveringOpenOver V).ι
      = ((P.affineDatum V).coveringOpen).ι ≫ (f ⁻¹ᵁ V).ι := by
  rw [datumIso]
  simp [Scheme.Hom.isoImage_hom_ι]

/-- **The clause (3) prescription over an affine open `V` of the base**, read on the open
`U(ψ_V)` of `X`: the morphism of [Stacks, Tag 01NK] for the induced datum, composed with the
chart of [Stacks, Tag 01NQ] over `V`, transported to `U(ψ_V)`. -/
public def chartOver (V : S.Opens) (hV : IsAffineOpen V) :
    (P.coveringOpenOver V).toScheme ⟶ rp.scheme :=
  (P.datumIso V).inv ≫ relativeChart rp V hV (P.affineDatum V)

/-- **The prescriptions are compatible along the inclusion `U(ψ_Z) ⊆ U(ψ_V)`** for affine opens
`Z ≤ V` of the base.  This is `…GradedPowerMap.relativeChart_affineDatum_resLE` read on opens of
`X`. -/
public theorem homOfLE_chartOver {Z V : S.Opens} (h : Z ≤ V) (hZ : IsAffineOpen Z)
    (hV : IsAffineOpen V) (hle : P.coveringOpenOver Z ≤ P.coveringOpenOver V) :
    T.homOfLE hle ≫ P.chartOver rp V hV = P.chartOver rp Z hZ := by
  have le' : (P.affineDatum Z).coveringOpen
      ≤ (T.homOfLE (f.preimage_mono h)) ⁻¹ᵁ (P.affineDatum V).coveringOpen :=
    (P.coveringOpen_comap_affineDatum h hZ hV).ge.trans
      (Stacks.AlgebraicGeometry.ProjChartGradedIsoTransport.coveringOpen_comap_le_preimage_of_iso
        (A.res h) (T.homOfLE (f.preimage_mono h)) (P.affineDatum V)
        (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictCompIso P.L
          (f.preimage_mono h)) (P.affineDatum Z) (P.affineDatum_hchi h))
  have hiso : T.homOfLE hle ≫ (P.datumIso V).inv
      = (P.datumIso Z).inv
        ≫ (T.homOfLE (f.preimage_mono h)).resLE (P.affineDatum V).coveringOpen
            ((P.affineDatum Z).coveringOpen) le' := by
    rw [← cancel_mono (P.datumIso V).hom, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, ← cancel_mono (P.coveringOpenOver V).ι,
      Category.assoc, Category.assoc, P.datumIso_hom_ι V, Scheme.homOfLE_ι]
    rw [← Category.assoc ((T.homOfLE (f.preimage_mono h)).resLE _ _ le'),
      Scheme.Hom.resLE_comp_ι, Category.assoc, Scheme.homOfLE_ι,
      ← P.datumIso_hom_ι Z, Iso.inv_hom_id_assoc]
  rw [chartOver, chartOver, ← Category.assoc, hiso, Category.assoc,
    ← P.relativeChart_affineDatum_resLE h hZ hV rp le']

/-! ### The glued morphism -/

/-- The part of `U(ψ)` lying over an affine open `V` of the base, read as the open `U(ψ_V)` of
`X`. -/
public def toBaseIso (V : S.Opens) (hV : IsAffineOpen V) :
    (P.toBase ⁻¹ᵁ V).toScheme ≅ (P.coveringOpenOver V).toScheme :=
  P.coveringOpen.ι.isoImage (P.toBase ⁻¹ᵁ V)
    ≪≫ T.isoOfEq (P.image_preimage_toBase_eq V hV)

/-- `toBaseIso` followed by the inclusion of `U(ψ_V)` into `X` is the inclusion of the preimage
of `V` into `U(ψ)`, followed by the inclusion of `U(ψ)` into `X`. -/
public theorem toBaseIso_hom_ι (V : S.Opens) (hV : IsAffineOpen V) :
    (P.toBaseIso V hV).hom ≫ (P.coveringOpenOver V).ι
      = (P.toBase ⁻¹ᵁ V).ι ≫ P.coveringOpen.ι := by
  rw [toBaseIso]
  simp [Scheme.Hom.isoImage_hom_ι]

/-- `U(ψ_Z) ⊆ U(ψ_V)` for affine opens `Z ≤ V` of the base. -/
public theorem coveringOpenOver_le {Z V : S.Opens} (h : Z ≤ V) (hZ : IsAffineOpen Z)
    (hV : IsAffineOpen V) : P.coveringOpenOver Z ≤ P.coveringOpenOver V :=
  (P.coveringOpenOver_inf_preimage_eq hZ hV h).ge.trans inf_le_left

/-- The clause (3) prescription over an affine open of the base, on the piece of `U(ψ)` lying
over it — the shape `AlgebraicGeometry.Scheme.glueOverAffinePreimages` presents its pieces in. -/
public def piece (V : S.affineOpens) : (P.toBase ⁻¹ᵁ V.1).toScheme ⟶ rp.scheme :=
  (P.toBaseIso V.1 V.2).hom ≫ P.chartOver rp V.1 V.2

/-- **The pieces are compatible along the inclusions between the preimages of nested affine opens
of the base**, which is the single hypothesis of
`AlgebraicGeometry.Scheme.glueOverAffinePreimages`. -/
public theorem homOfLE_piece (Z V : S.affineOpens) (h : Z.1 ≤ V.1) :
    P.coveringOpen.toScheme.homOfLE (P.toBase.preimage_mono h) ≫ P.piece rp V
      = P.piece rp Z := by
  have hle := P.coveringOpenOver_le h Z.2 V.2
  have hiso : P.coveringOpen.toScheme.homOfLE (P.toBase.preimage_mono h)
        ≫ (P.toBaseIso V.1 V.2).hom
      = (P.toBaseIso Z.1 Z.2).hom ≫ T.homOfLE hle := by
    rw [← cancel_mono (P.coveringOpenOver V).ι, Category.assoc, Category.assoc,
      P.toBaseIso_hom_ι V.1 V.2, Scheme.homOfLE_ι, ← Category.assoc, Scheme.homOfLE_ι,
      P.toBaseIso_hom_ι Z.1 Z.2]
  rw [piece, piece, ← Category.assoc, hiso, Category.assoc,
    P.homOfLE_chartOver rp h Z.2 V.2 hle]

/-- **`r_{ℒ,ψ}` of [Stacks, Tag 01O9]**: the morphism `U(ψ) ⟶ Proj_S(𝒜)` glued from the clause (3)
prescriptions over the affine opens of the base.

`U(ψ)` is the open of [Stacks, Tag 01O8] attached to the global datum `(ℒ, ψ)`, and the
prescription over an affine open `V` is the morphism of [Stacks, Tag 01NK] for the induced datum
read through the chart of [Stacks, Tag 01NQ].  No overlap condition is imposed and none is
carried: `AlgebraicGeometry.Scheme.glueOverAffinePreimages` asks only for compatibility along the
inclusions between the preimages of nested affine opens, and that is `homOfLE_piece`. -/
public def globalMorphism : P.coveringOpen.toScheme ⟶ rp.scheme :=
  Scheme.glueOverAffinePreimages P.toBase (P.piece rp) (P.homOfLE_piece rp)

/-- **The characterizing restriction property of `r_{ℒ,ψ}`**: over the preimage of an affine open
`V` of the base it is the clause (3) prescription there. -/
public theorem ι_globalMorphism (V : S.affineOpens) :
    (P.toBase ⁻¹ᵁ V.1).ι ≫ P.globalMorphism rp = P.piece rp V :=
  Scheme.ι_glueOverAffinePreimages P.toBase (P.piece rp) (P.homOfLE_piece rp) V

/-- **`r_{ℒ,ψ}` is the only morphism with that restriction property.** -/
public theorem eq_globalMorphism {R : P.coveringOpen.toScheme ⟶ rp.scheme}
    (hR : ∀ V : S.affineOpens, (P.toBase ⁻¹ᵁ V.1).ι ≫ R = P.piece rp V) :
    R = P.globalMorphism rp :=
  Scheme.hom_ext_of_affinePreimages P.toBase fun V =>
    (hR V).trans (P.ι_globalMorphism rp V).symm

/-- **Existence and uniqueness of `r_{ℒ,ψ}`, in one statement.**  There is exactly one morphism
`U(ψ) ⟶ Proj_S(𝒜)` whose restriction over the preimage of each affine open of the base is the
clause (3) prescription there. -/
public theorem existsUnique_globalMorphism :
    ∃! R : P.coveringOpen.toScheme ⟶ rp.scheme,
      ∀ V : S.affineOpens, (P.toBase ⁻¹ᵁ V.1).ι ≫ R = P.piece rp V :=
  ⟨P.globalMorphism rp, P.ι_globalMorphism rp, fun _ hR => P.eq_globalMorphism rp hR⟩

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
