module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesTransport

/-!
# The affine blowup is the blowup of the ideal sheaf it defines

For an ideal `K` of a commutative ring `R` there are two blowups of `Spec R` in `K` available:
the affine one, `Stacks.Blowup.toSpec K`, which is `Proj` of the Rees algebra `R[Kt]`, and the
general one, `AlgebraicGeometry.blowUpToBase`, applied to the quasi-coherent ideal sheaf `K`
defines on `Spec R`. This file identifies them as schemes over `Spec R`.

## Main results

* `Stacks.Blowup.nonempty_over_iso_blowUpToBase`: **the two blowups of `Spec R` in `K` agree**,
  over `Spec R`.

## Implementation notes

`Stacks.Blowup.isPullback_blowUpChart` exhibits `Proj` of the Rees algebra of `ℐ(U)` as the part
of the blowup of `ℐ` over an affine open `U` of the base. Taking `U = ⊤` makes the bottom edge of
that square the isomorphism `(⊤ : X.Opens).ι`, so the chart itself is an isomorphism, and
`Stacks.Blowup.chartToOpen_eq` identifies the resulting structure morphism with
`Stacks.Blowup.toSpec (ℐ(⊤))` followed by `Spec Γ(X, ⊤) ≅ X`.

What is left is that `ℐ(⊤)` is not `K` but its transport along the counit `Γ(Spec R, ⊤) ≅ R`;
`Stacks.Blowup.isIso_map_reesGradedHom` and `Stacks.Blowup.map_reesGradedHom_comp_toSpec` supply
the matching isomorphism of blowups over `Spec` of that counit. The last step passes from
`Stacks.Blowup.blowUp` to `AlgebraicGeometry.blowUp` by `Stacks.Blowup.blowUpOverIso`.

The morphisms coming out of the transport and out of the chart square are introduced as opaque
local variables by `obtain`, because `Stacks.Blowup.blowUpSpec` is a plain definition and not an
abbreviation: a composite written with both spellings of `Proj (reesGrading K)` is accepted but
is then out of reach of `rw`.

## References

* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Blowup

variable (R : Type u) [CommRing R] (K : Ideal R)

/-- The ideal of global sections of the ideal sheaf attached to an ideal of global sections. -/
theorem ideal_ofIdealTop_top {X : Scheme.{u}} [IsAffine X] (L : Ideal Γ(X, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop L).ideal ⟨⊤, isAffineOpen_top X⟩ = L := by
  rw [Scheme.IdealSheafData.ofIdealTop_ideal,
    show (homOfLE (le_top (a := (⊤ : X.Opens)))) = 𝟙 _ from rfl]
  simp

/-- **The blowup of `Spec R` in an ideal `K` is the blowup of `Spec R` in the ideal sheaf
attached to `K`, over `Spec R`.** The affine blowup `Proj` of the Rees algebra of `K` is the
chart of the ideal-sheaf blowup over the affine open `⊤`, after transporting the coefficient
ring along `Γ(Spec R, ⊤) ≅ R`. -/
theorem nonempty_over_iso_blowUpToBase :
    Nonempty (Over.mk (toSpec K) ≅
      Over.mk (AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom K)))) := by
  set e := Scheme.ΓSpecIso (CommRingCat.of R)
  set ℐ := Scheme.IdealSheafData.ofIdealTop (Ideal.map e.inv.hom K)
  set U : (Spec (CommRingCat.of R)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hU : ℐ.ideal U = Ideal.map e.inv.hom K := ideal_ofIdealTop_top _
  have hψφ : e.inv.hom.comp e.hom.hom = RingHom.id Γ(Spec (CommRingCat.of R), ⊤) :=
    congrArg CommRingCat.Hom.hom e.hom_inv_id
  have hφψ : e.hom.hom.comp e.inv.hom = RingHom.id R :=
    congrArg CommRingCat.Hom.hom e.inv_hom_id
  have hJ : Ideal.map e.hom.hom (ℐ.ideal U) = K := by
    rw [hU, Ideal.map_map, hφψ, Ideal.map_id]
  have hI : Ideal.map e.inv.hom K = ℐ.ideal U := hU.symm
  have hκ : (Stacks.RelativeProj.isAffineOpen U).isoSpec.inv ≫ U.1.ι = Spec.map e.inv := by
    show (isAffineOpen_top (Spec (CommRingCat.of R))).fromSpec = Spec.map e.inv
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  have hιiso : IsIso U.1.ι := by
    show IsIso (Scheme.topIso _).hom
    infer_instance
  have hchart := Stacks.Blowup.isPullback_blowUpChart ℐ U
  have hchartIso : IsIso (Stacks.Blowup.blowUpChart ℐ U) :=
    MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme) hchart hιiso
  have hw0 : Stacks.Blowup.blowUpChart ℐ U ≫ Stacks.Blowup.blowUpToBase ℐ =
      toSpec (ℐ.ideal U) ≫ Spec.map e.inv := by
    rw [← hchart.w, chartToOpen_eq, ← hκ]
    exact Category.assoc _ _ _
  obtain ⟨θ, hθiso, hθ⟩ : ∃ θ : blowUpSpec K ⟶ blowUpSpec (ℐ.ideal U), IsIso θ ∧
      θ ≫ toSpec (ℐ.ideal U) = toSpec K ≫ Spec.map (CommRingCat.ofHom e.hom.hom) :=
    ⟨Proj.map (reesGradedHom e.hom.hom (ℐ.ideal U) K hJ)
        (Proj.irrelevant_le_map_of_surjective _
          (surjective_reesGradedHom e.hom.hom (ℐ.ideal U) K hJ e.inv.hom hI hφψ)),
      isIso_map_reesGradedHom e.hom.hom (ℐ.ideal U) K hJ e.inv.hom hI hψφ hφψ,
      map_reesGradedHom_comp_toSpec e.hom.hom (ℐ.ideal U) K hJ _⟩
  obtain ⟨c, hciso, hw⟩ : ∃ c : blowUpSpec (ℐ.ideal U) ⟶ Stacks.Blowup.blowUp ℐ, IsIso c ∧
      c ≫ Stacks.Blowup.blowUpToBase ℐ = toSpec (ℐ.ideal U) ≫ Spec.map e.inv :=
    ⟨Stacks.Blowup.blowUpChart ℐ U, hchartIso, hw0⟩
  have := hθiso
  have := hciso
  have hε : (θ ≫ c) ≫ Stacks.Blowup.blowUpToBase ℐ = toSpec K := by
    rw [Category.assoc, hw, ← Category.assoc, hθ, Category.assoc, ← Spec.map_comp,
      CommRingCat.ofHom_hom, e.inv_hom_id, Spec.map_id, Category.comp_id]
  have e1 : Over.mk (toSpec K) ≅ Over.mk (Stacks.Blowup.blowUpToBase ℐ) :=
    Over.isoMk (asIso θ ≪≫ asIso c) hε
  exact ⟨e1 ≪≫ blowUpOverIso ℐ⟩

end Stacks.Blowup

end
