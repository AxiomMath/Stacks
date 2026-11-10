module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.FaceAlgebra
public import StacksFrontier.Algebra.Module.ConeBaseChangeTransfer

/-!
# The theorem of the cube: the fibre of a chart over a rational point

Let `A` be a group scheme over a field `k`, `V ⊆ A` an affine open with ring `R` and `z ∈ V` a
rational point, with evaluation `ev_z : R → k`. The fibre of `P_V = (A × A) × V ⟶ Spec R` over
`z` is `A × A`, embedded by `j_z : (x, y) ↦ (x, y, z)` (`Stacks.Cube.isPullback_fibre`), so the
alternating Čech complex of `N` over the chart becomes, after base change along `ev_z`, the
alternating Čech complex of `j_z^* N` on `A × A` (`Stacks.Cube.isBaseChange_θC`). Likewise
functions on the face `U_j × V` become functions on `U_j` after restriction along
`τ_z : y ↦ (y, z)` (`Stacks.Cube.isBaseChange_θD`).

## References

* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct

universe u

namespace Stacks.Cube

open Stacks.KunnethCech Stacks.TrivialGenerator

variable {k : Type u} [Field k] {A : Over (Spec (.of k))}

/-! ### The fibre over a rational point -/

section Fibre

variable (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _)

include hzk in
/-- The maps `𝟙` and `(A × A) ⟶ Spec k ⟶ A` (constant at `z`) agree over `Spec k`. -/
theorem jz_w : 𝟙 (B A) ≫ (A ⊗ A).hom = ((A ⊗ A).hom ≫ z) ≫ A.hom := by
  rw [Category.assoc, hzk, Category.comp_id, Category.id_comp]

/-- The embedding `(x, y) ↦ (x, y, z)` of the fibre. -/
noncomputable def jz : B A ⟶ P A := pullback.lift (𝟙 _) ((A ⊗ A).hom ≫ z) (jz_w z hzk)

/-- The composite of `jz` with the projection `q` to `A × A` is the identity. -/
@[reassoc (attr := simp)]
theorem jz_q : jz z hzk ≫ q A = 𝟙 _ := pullback.lift_fst _ _ _

/-- The composite of `jz` with the third projection `r` is the constant map at `z`. -/
@[reassoc (attr := simp)]
theorem jz_r : jz z hzk ≫ r A = (A ⊗ A).hom ≫ z := pullback.lift_snd _ _ _

include hzk in
/-- The maps `𝟙` and `A ⟶ Spec k ⟶ A` (constant at `z`) agree over `Spec k`. -/
theorem τz_w : 𝟙 A.left ≫ A.hom = (A.hom ≫ z) ≫ A.hom := by
  rw [Category.assoc, hzk, Category.comp_id, Category.id_comp]

/-- The embedding `y ↦ (y, z)` into `A × A`. -/
noncomputable def τz : A.left ⟶ B A := pullback.lift (𝟙 _) (A.hom ≫ z) (τz_w z hzk)

/-- The first coordinate of `τz` is the identity of `A`. -/
@[reassoc (attr := simp)]
theorem τz_bx : τz z hzk ≫ bx A = 𝟙 _ := pullback.lift_fst _ _ _

/-- The second coordinate of `τz` is the constant map at `z`. -/
@[reassoc (attr := simp)]
theorem τz_bz : τz z hzk ≫ bz A = A.hom ≫ z := pullback.lift_snd _ _ _

include hzk in
/-- **The fibre of `r` over `z` is `A × A`.** -/
theorem isPullback_jz : IsPullback (jz z hzk) (A ⊗ A).hom (r A) z := by
  have hout : IsPullback (jz z hzk ≫ q A) (A ⊗ A).hom (A ⊗ A).hom (z ≫ A.hom) := by
    rw [jz_q, hzk]
    exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
  exact IsPullback.of_right hout (jz_r z hzk) (IsPullback.of_hasPullback _ _)

variable {V : A.left.Opens} (hV : IsAffineOpen V) (hzV : z ⁻¹ᵁ V = ⊤)

include hzV in
/-- If `z⁻¹ V` is everything, the point `z` lies in `V`. -/
theorem range_z_le : Set.range z ⊆ Set.range V.ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  have : x ∈ z ⁻¹ᵁ V := by rw [hzV]; trivial
  exact this

/-- The point `z` as a point of `V`. -/
noncomputable def zV : Spec (.of k) ⟶ V.toScheme := IsOpenImmersion.lift V.ι z (range_z_le z hzV)

/-- The point `zV` of `V`, composed with the inclusion of `V`, is `z`. -/
@[reassoc (attr := simp)]
theorem zV_ι : zV z hzV ≫ V.ι = z := IsOpenImmersion.lift_fac _ _ _

include hzk hzV in
/-- The image of `jz` lies in the open `P_V = r⁻¹ V`. -/
theorem range_jz_le : Set.range (jz z hzk) ⊆ Set.range (PV V).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  change (jz z hzk ≫ r A) x ∈ V
  rw [jz_r, Scheme.Hom.comp_apply]
  have : (A ⊗ A).hom x ∈ z ⁻¹ᵁ V := by rw [hzV]; trivial
  exact this

/-- The embedding of the fibre into the chart. -/
noncomputable def jzV : B A ⟶ (PV V).toScheme :=
  IsOpenImmersion.lift (PV V).ι (jz z hzk) (range_jz_le z hzk hzV)

/-- The embedding `jzV`, composed with the inclusion of `P_V`, is `jz`. -/
@[reassoc (attr := simp)]
theorem jzV_ι : jzV z hzk hzV ≫ (PV V).ι = jz z hzk := IsOpenImmersion.lift_fac _ _ _

/-- The restriction of `r` to `P_V` sends the fibre `jzV` to the point `zV`. -/
theorem jzV_r : jzV z hzk hzV ≫ (r A ∣_ V) = (A ⊗ A).hom ≫ zV z hzV := by
  rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, jzV_ι_assoc, jz_r, Category.assoc,
    zV_ι]

include hzV in
/-- The whole of `Spec k` is contained in `z⁻¹ V`. -/
theorem le_top_preimage_z : (⊤ : (Spec (.of k)).Opens) ≤ z ⁻¹ᵁ V := by rw [hzV]

/-- **Evaluation at the rational point `z`.** -/
noncomputable def evz : chartRing V →+* k :=
  (Scheme.ΓSpecIso (.of k)).hom.hom.comp (z.appLE V ⊤ (le_top_preimage_z z hzV)).hom

/-- `Scheme.Hom.appLE` of equal morphisms agree. -/
theorem appLE_congr' {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) {O : Y.Opens} {O' : X.Opens}
    (e : O' ≤ g ⁻¹ᵁ O) : g.appLE O O' e = f.appLE O O' (h ▸ e) := by
  subst h; rfl

/-- The map `Γ(A, V) ⟶ Γ(Spec k, ⊤)` induced by `z` factors through `zV`. -/
theorem z_appLE_eq : z.appLE V ⊤ (le_top_preimage_z z hzV) = V.topIso.inv ≫ (zV z hzV).appTop := by
  rw [appLE_congr' (zV_ι z hzV), ← Scheme.Hom.appLE_comp_appLE (zV z hzV) V.ι V ⊤ ⊤ (by simp)
    (by simp), Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv, Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE]
  rfl

/-- `Spec` of the evaluation `evz` is the point `zV` followed by `V ≅ Spec Γ(A, V)`. -/
theorem SpecMap_evz : Spec.map (CommRingCat.ofHom (evz z hzV)) = zV z hzV ≫ hV.isoSpec.hom := by
  refine ext_of_isAffine ?_
  rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop]
  rw [← cancel_mono (Scheme.ΓSpecIso (.of k)).hom, Scheme.ΓSpecIso_naturality]
  simp only [evz, Category.assoc, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom]
  rw [z_appLE_eq z hzV]
  rfl

include hzk in
/-- **The fibre of the chart over `z`.** -/
theorem isPullback_fibre :
    IsPullback (jzV z hzk hzV) (A ⊗ A).hom (chartMap hV)
      (Spec.map (CommRingCat.ofHom (evz z hzV))) := by
  have h3 : IsPullback (jzV z hzk hzV) (A ⊗ A).hom (r A ∣_ V) (zV z hzV) := by
    refine IsPullback.of_right ?_ (jzV_r z hzk hzV) (isPullback_morphismRestrict (r A) V).flip
    rw [jzV_ι, zV_ι]
    exact isPullback_jz z hzk
  rw [SpecMap_evz z hV hzV]
  exact h3.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) hV.isoSpec
    (by simp) (by simp) (by simp [chartMap]) (by simp)

include hzk in
/-- Evaluation at the rational point `z` restricts to the identity on `k`. -/
theorem evz_algebraMap (c : k) :
    evz z hzV ((Stacks.Cech.baseRingHom A.hom V).hom c) = c := by
  simp only [evz, RingHom.comp_apply]
  rw [Stacks.Cech.baseRingHom_eq_appLE A.hom V (Stacks.AffineProduct.le_preimage_top _ _)]
  change (Scheme.ΓSpecIso (.of k)).hom ((z.appLE V ⊤ _) (A.hom.appLE ⊤ V _
    ((Scheme.ΓSpecIso (.of k)).inv c))) = c
  rw [appLE_comp, appLE_congr hzk, id_appLE_self, Iso.inv_hom_id_apply]

end Fibre

end Stacks.Cube

end
