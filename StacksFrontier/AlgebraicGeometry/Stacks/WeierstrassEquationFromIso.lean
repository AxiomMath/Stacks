module

public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassEquationApproximation
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassEquationLocalComparison

/-!
# A Weierstrass equation from an isomorphism onto a plane cubic over an open

Let `E` be a pointed family over `Spec B` and `C` a Weierstrass equation over `B`, and let
`φ : E ⟶ E_C` be a morphism over `Spec B` onto the plane cubic of `C` carrying the section of `E`
to the section `(0 : 1 : 0)` of `E_C`. If `φ` is an isomorphism over an open `U` of `Spec B`, then
at every point `x ∈ U` at which the discriminant of `C` does not vanish, `E` is near `x` a
restriction of the Weierstrass family `(E_W, f_W, 0_W)`, as in the proof of Tag 072T.

Over an affine open `V ∋ x` inside `U` on which the discriminant is invertible, `E|_V` is the
plane cubic of the restriction of `C` to `Γ(Spec B, V)`, a Weierstrass equation with invertible
discriminant.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.hasLocalComparison_of_isIso_overPullback`:
  the statement above.

## References

* [Stacks Project, Tag 072T](https://stacks.math.columbia.edu/tag/072T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

/-- If a morphism `φ : E ⟶ E_C` over `Spec B` from a pointed family onto the plane cubic of a
Weierstrass equation `C` over `B`, compatible with the sections, is an isomorphism over an open
`U` of `Spec B`, then near every point of `U` at which the discriminant of `C` does not vanish,
`E` is a restriction of the Weierstrass family. -/
theorem hasLocalComparison_of_isIso_overPullback {B : Type u} [CommRing B]
    (E : PointedFamily (Spec (.of B))) (C : WeierstrassCurve B) (φ : E.total ⟶ projOf C)
    (hφ : φ ≫ projectionOf C = E.map) (hzero : E.zero ≫ φ = zeroOf C)
    (U : (Spec (.of B)).Opens)
    (hU : IsIso ((Over.pullback U.ι).map
      (Over.homMk (U := Over.mk E.map) (V := Over.mk (projectionOf C)) φ hφ)).left)
    (x : Spec (.of B)) (hx : x ∈ U) (hΔ : C.Δ ∉ x.asIdeal) :
    HasLocalComparison family.{u} E x := by
  let X := Spec (CommRingCat.of B)
  let g : Γ(X, ⊤) := (Scheme.ΓSpecIso (.of B)).inv C.Δ
  obtain ⟨V, hV, hxV, hVle⟩ := exists_isAffineOpen_mem_and_subset
    (U := U ⊓ X.basicOpen g) ⟨hx, by rwa [basicOpen_eq_of_affine]⟩
  have hVU : V ≤ U := hVle.trans inf_le_left
  have hVD : V ≤ X.basicOpen g := hVle.trans inf_le_right
  let ψ : CommRingCat.of B ⟶ Γ(X, V) :=
    (Scheme.ΓSpecIso (.of B)).inv ≫ X.presheaf.map (homOfLE le_top).op
  have hψ : V.ι = hV.isoSpec.hom ≫ Spec.map ψ := by
    rw [IsAffineOpen.isoSpec_hom, Spec.map_comp,
      Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  have : (C.map ψ.hom).IsElliptic := by
    refine ⟨?_⟩
    rw [WeierstrassCurve.map_Δ]
    have h₁ : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le g)).op g) :=
      X.toRingedSpace.isUnit_res_basicOpen g
    have h₂ := h₁.map (X.presheaf.map (homOfLE hVD).op).hom
    convert h₂ using 1
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  let eU : FamilyIso (E.pullback U.ι) ((familyOf C).pullback U.ι) :=
    { iso := @asIso _ _ _ _ _ hU
      iso_map := Limits.pullback.lift_snd _ _ _
      zero_iso := by
        refine Limits.pullback.hom_ext ?_ ?_
        · refine (Category.assoc _ _ _).trans ?_
          refine (congrArg _ (Limits.pullback.lift_fst _ _ _)).trans ?_
          refine (Limits.pullback.lift_fst_assoc _ _ _ _).trans ?_
          refine ((Category.assoc _ _ _).trans (congrArg _ hzero)).trans ?_
          exact (Limits.pullback.lift_fst _ _ _).symm
        · refine (Category.assoc _ _ _).trans ?_
          refine (congrArg _ (Limits.pullback.lift_snd _ _ _)).trans ?_
          refine (Limits.pullback.lift_snd _ _ _).trans ?_
          exact (Limits.pullback.lift_snd _ _ _).symm }
  let i := X.homOfLE hVU
  let eV : FamilyIso (E.pullback V.ι) ((familyOf C).pullback V.ι) :=
    ((E.pullbackPullbackIso U.ι i (X.homOfLE_ι hVU).symm).symm.trans (eU.pullback i)).trans
      ((familyOf C).pullbackPullbackIso U.ι i (X.homOfLE_ι hVU).symm)
  let e₁ : FamilyIso ((familyOf (C.map ψ.hom)).pullback hV.isoSpec.hom)
      ((familyOf C).pullback V.ι) :=
    ((familyOfMapIso C ψ.hom).symm.pullback hV.isoSpec.hom).trans
      ((familyOf C).pullbackPullbackIso (Spec.map (CommRingCat.ofHom ψ.hom)) hV.isoSpec.hom hψ)
  exact exists_comparison_of_familyIso E hV hxV (C.map ψ.hom) (e₁.trans eV.symm)

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass
