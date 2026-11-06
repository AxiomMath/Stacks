module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.SmoothLift.Interface
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.FiniteEtaleLiftFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth

/-!
# A smooth morphism of algebraic spaces is formally smooth

This file assembles the étale-local lifts of
`StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.FiniteEtaleLiftFamily`, the Čech argument of
`StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.SmoothLift.Cech` and the étale descent of
points into the implication (1) ⟹ (2) of [Stacks Project, Tag 04AM] for an arbitrary morphism of
algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.SmoothLift.Problem.exists_lift`: a lifting problem for a smooth
  morphism along `Spec (A' ⧸ C) ⊂ Spec A'` has a solution.
* `AlgebraicGeometry.Space.formallySmooth_of_isSmooth_of_isAlgebraicSpace`: **a smooth morphism
  of algebraic spaces is formally smooth.**

The equivalence of [Stacks Project, Tag 04AM] itself is
`AlgebraicGeometry.Space.isSmooth_iff_isLocallyOfFinitePresentation_and_formallySmooth` of
`StacksFrontier/AlgebraicGeometry/Spaces/FormallySmooth/OfIsSmooth.lean`.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space.SmoothLift

open Stacks.SmoothLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : Base B S hS}

/-- For `v : yoneda.obj V ⟶ Fu`, the value of `v` at `g ≫ h` is the restriction along `g` of its
value at `h`. -/
theorem yoneda_app_comp {Fu : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS}
    (v : yoneda.obj V ⟶ Fu) {U U' : BigFppfOver B S hS} (g : U' ⟶ U) (h : U ⟶ V) :
    v.app (op U') (g ≫ h) = Fu.map g.op (v.app (op U) h) :=
  NatTrans.naturality_apply v g.op h

/-! ### The covering family attached to the chart-adapted local lifts -/

section Family

variable (𝔓 : Problem D) {U : BigFppfOver B S hS}
  [hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  (j : U ⟶ O (baseAlg D)) {W V : BigFppfOver B S hS}
  [hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
  [hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  (w : yoneda.obj W ⟶ 𝔓.X) (v : yoneda.obj V ⟶ 𝔓.Y) (κ : W ⟶ V) (ℓ : U ⟶ W)
  (hw : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf w)
  (hv : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf v)
  (hκ : yoneda.map κ ≫ v = w ≫ 𝔓.f) (hsm : Smooth ((BigFppfOver.toScheme B S hS).map κ))
  (hy : v.app (op U) (ℓ ≫ κ) = 𝔓.Y.map j.op 𝔓.y)
  (hl : ∀ (Z : BigFppfOver B S hS) (p : Z ⟶ O₀ (baseAlg D)) (q : Z ⟶ U),
    p ≫ incl (baseAlg D) = q ≫ j → 𝔓.X.map p.op 𝔓.x = w.app (op Z) (q ≫ ℓ))

/-- The chart of the family member. -/
def frameOf : Frame 𝔓 := ⟨W, V, w, v, κ, hκ, hw, hv, hsm⟩

include hy in
omit hW hV in
/-- The section `v` at the composite `(eU D j).hom ≫ ℓ ≫ κ` is the base point
`𝔓.yR (algOf D j)`. -/
theorem v_app_base :
    v.app (op (O (algOf D j))) ((eU D j).hom ≫ ℓ ≫ κ) = 𝔓.yR (algOf D j) := by
  calc v.app (op (O (algOf D j))) ((eU D j).hom ≫ ℓ ≫ κ)
      = 𝔓.Y.map (eU D j).hom.op (v.app (op U) (ℓ ≫ κ)) := yoneda_app_comp v _ _
    _ = 𝔓.Y.map (eU D j).hom.op (𝔓.Y.map j.op 𝔓.y) := by rw [hy]
    _ = 𝔓.yR (algOf D j) := by rw [map_map, eU_hom_j]

include hl in
omit hW in
/-- The section `w` at the composite `incl (algOf D j) ≫ (eU D j).hom ≫ ℓ` is the reduced point
`𝔓.xR (algOf D j)`. -/
theorem w_app_red :
    w.app (op (O₀ (algOf D j))) (incl (algOf D j) ≫ (eU D j).hom ≫ ℓ) = 𝔓.xR (algOf D j) := by
  refine (hl _ (mO₀ (toBase (algOf D j))) (incl (algOf D j) ≫ (eU D j).hom) ?_).symm
  rw [Category.assoc, eU_hom_j, incl_mO]

/-- The framing of the family member. -/
noncomputable def framingOf : Framing (frameOf 𝔓 w v κ hw hv hκ hsm) (algOf D j) where
  red := incl (algOf D j) ≫ (eU D j).hom ≫ ℓ
  base := (eU D j).hom ≫ ℓ ≫ κ
  hred := w_app_red 𝔓 j w ℓ hl
  hbase := v_app_base 𝔓 j v κ ℓ hy
  comm := by
    simp only [Category.assoc]
    rfl

/-- The lift of the family member. -/
noncomputable def liftOf : 𝔓.Lifts (algOf D j) :=
  ⟨w.app (op (O (algOf D j))) ((eU D j).hom ≫ ℓ),
    (yoneda_app_comp w (incl (algOf D j)) ((eU D j).hom ≫ ℓ)).symm.trans
      (w_app_red 𝔓 j w ℓ hl), by
    rw [← v_app_base 𝔓 j v κ ℓ hy]
    exact (congrFun (congrArg (fun α => α.app (op (O (algOf D j)))) hκ)
      ((eU D j).hom ≫ ℓ)).symm⟩

end Family

/-! ### Separatedness along the closed fibres of a covering family -/

/-- If `mO (toBase R)` is étale, then so is its base change `mO₀ (toBase R)`. -/
theorem etale_mO₀ (R : Alg D) (h : Etale ((BigFppfOver.toScheme B S hS).map (mO (toBase R)))) :
    Etale ((BigFppfOver.toScheme B S hS).map (mO₀ (toBase R))) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (isPullback_incl_scheme R) h

/-- If the morphisms `mO (toBase (Rk k))` are jointly surjective onto `O (baseAlg D)`, then the
morphisms `mO₀ (toBase (Rk k))` are jointly surjective onto `O₀ (baseAlg D)`. -/
theorem exists_mO₀ {ι : Type u} (Rk : ι → Alg D)
    (h : ∀ t : (BigFppfOver.toScheme B S hS).obj (O (baseAlg D)),
      ∃ k, ∃ u : (BigFppfOver.toScheme B S hS).obj (O (Rk k)),
        ((BigFppfOver.toScheme B S hS).map (mO (toBase (Rk k)))).base u = t)
    (t : (BigFppfOver.toScheme B S hS).obj (O₀ (baseAlg D))) :
    ∃ k, ∃ u : (BigFppfOver.toScheme B S hS).obj (O₀ (Rk k)),
      ((BigFppfOver.toScheme B S hS).map (mO₀ (toBase (Rk k)))).base u = t := by
  obtain ⟨k, u, hu⟩ := h (((BigFppfOver.toScheme B S hS).map (incl (baseAlg D))).base t)
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback u t hu
  refine ⟨k, ((isPullback_incl_scheme (Rk k)).isoPullback.inv).base z, ?_⟩
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hz2]

/-! ### The lifting problem has a solution -/

/-- Sections of an algebraic space agreeing on a jointly surjective étale family agree. -/
theorem eq_of_forall_map_eq {Fu : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hFu : IsAlgebraicSpace B S hS Fu) {T' : BigFppfOver B S hS} {ι : Type u}
    (U : ι → BigFppfOver B S hS) (j : ∀ k, U k ⟶ T')
    (hjet : ∀ k, Etale ((BigFppfOver.toScheme B S hS).map (j k)))
    (hjsurj : ∀ t' : (BigFppfOver.toScheme B S hS).obj T',
      ∃ (k : ι) (u : (BigFppfOver.toScheme B S hS).obj (U k)),
        ((BigFppfOver.toScheme B S hS).map (j k)).base u = t')
    (a b : Fu.obj (op T')) (h : ∀ k, Fu.map (j k).op a = Fu.map (j k).op b) : a = b :=
  (existsUnique_map_eq_of_etale_of_jointlySurjective B S hS hFu U j hjet hjsurj
    (fun k => Fu.map (j k).op a) (fun k l => by rw [map_map, map_map, pullback.condition])).unique
    (fun _ => rfl) (fun k => (h k).symm)

/-- The square formed by `j`, `j'` and the two structure morphisms from `O` of the tensor product
of `algOf D j` and `algOf D j'`, transported along `eU D j` and `eU D j'`, is a pullback. -/
theorem isPullback_eU {U U' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (j : U ⟶ O (baseAlg D))
    (j' : U' ⟶ O (baseAlg D)) :
    IsPullback (mO (incl₁ (R := algOf D j) (algOf D j')) ≫ (eU D j).hom)
      (mO (incl₂ (R := algOf D j) (algOf D j')) ≫ (eU D j').hom) j j' := by
  refine (isPullback_tensor (algOf D j) (algOf D j')).of_iso (Iso.refl _) (eU D j) (eU D j')
    (Iso.refl _) (by simp) (by simp) ?_ ?_ <;> rw [Iso.refl_hom, Category.comp_id, eU_hom_j]

/-- **A lifting problem for a smooth morphism has a solution.** -/
theorem Problem.exists_lift (𝔓 : Problem D) (hf : IsSmooth B S hS 𝔓.f) :
    ∃ z : 𝔓.X.obj (op (O (baseAlg D))),
      𝔓.X.map (incl (baseAlg D)).op z = 𝔓.x ∧ 𝔓.f.app _ z = 𝔓.y := by
  classical
  obtain ⟨ι, hfin, U, j, W, V, w, v, κ, ℓ, hU, hj, hsurj, hW, hV, hw, hv, hκ, hy, hl⟩ :=
    exists_finite_chartLift_of_isSmooth B S hS 𝔓.hX 𝔓.hY hf
      (inferInstance : IsAffine ((BigFppfOver.toScheme B S hS).obj (O (baseAlg D))))
      (incl (baseAlg D)) (isSquareZero_incl _) 𝔓.x 𝔓.y 𝔓.hxy
  have : Fintype ι := Fintype.ofFinite ι
  have := hU
  let Bk : ι → Alg D := fun k => algOf D (j k)
  have hflat : ∀ k, Module.Flat D.A (Bk k).R := fun k => flat_algOf D (j k) (hj k)
  have : Module.FaithfullyFlat D.A (∀ k, (Bk k).R) := by
    refine faithfullyFlat_pi (fun k => (Bk k).R) fun p => ?_
    obtain ⟨k, u, hu⟩ := hsurj p
    refine ⟨k, ((BigFppfOver.toScheme B S hS).obj (U k)).isoSpec.hom.base u, ?_⟩
    have h : (Spec.map (structOf D (j k))).base
        (((BigFppfOver.toScheme B S hS).obj (U k)).isoSpec.hom.base u) = (jS D (j k)).base u := by
      rw [← isoSpec_inv_j D (j k), ← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
    exact h.trans hu
  let Fk : ι → Frame 𝔓 := fun k =>
    frameOf 𝔓 (w k) (v k) (κ k) (hw k) (hv k) (hκ k)
      (hf (W k) (V k) (w k) (v k) (κ k) (hw k) (hv k) (hκ k))
  let Frk : ∀ k, Framing (Fk k) (Bk k) := fun k =>
    framingOf 𝔓 (j k) (w k) (v k) (κ k) (ℓ k) (hw k) (hv k) (hκ k) _ (hy k) (hl k)
  obtain ⟨z', hz'⟩ := exists_compatible_lifts Bk Frk fun k =>
    liftOf 𝔓 (j k) (w k) (v k) (κ k) (ℓ k) (hκ k) (hy k) (hl k)
  let mk : ∀ k, O (Bk k) ⟶ O (baseAlg D) := fun k => mO (toBase (Bk k))
  have hmet : ∀ k, Etale ((BigFppfOver.toScheme B S hS).map (mk k)) := fun k =>
    etale_mO_toBase D (j k) (hj k)
  have hmsurj : ∀ t : (BigFppfOver.toScheme B S hS).obj (O (baseAlg D)),
      ∃ k, ∃ u : (BigFppfOver.toScheme B S hS).obj (O (Bk k)),
        ((BigFppfOver.toScheme B S hS).map (mk k)).base u = t := by
    intro t
    obtain ⟨k, u, hu⟩ := hsurj t
    refine ⟨k, ((BigFppfOver.toScheme B S hS).map (eU D (j k)).inv).base u, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, eU_inv_mO, hu]
  obtain ⟨z, hz, -⟩ := existsUnique_map_eq_of_etale_of_jointlySurjective B S hS 𝔓.hX
    (fun k => O (Bk k)) mk hmet hmsurj (fun k => (z' k).1) (fun k l => by
      have P := isPullback_tensor (Bk k) (Bk l)
      rw [← P.isoPullback_inv_fst, ← P.isoPullback_inv_snd, op_comp, op_comp,
        Functor.map_comp_apply, Functor.map_comp_apply]
      exact congrArg _ (congrArg Subtype.val (hz' k l)))
  refine ⟨z, ?_, ?_⟩
  · refine eq_of_forall_map_eq 𝔓.hX (fun k => O₀ (Bk k)) (fun k => mO₀ (toBase (Bk k)))
      (fun k => etale_mO₀ _ (hmet k)) (exists_mO₀ Bk hmsurj) _ _ fun k => ?_
    rw [map_map, ← incl_mO, ← map_map]
    exact (congrArg _ (hz k)).trans (z' k).2.1
  · refine eq_of_forall_map_eq 𝔓.hY (fun k => O (Bk k)) mk hmet hmsurj _ _ fun k => ?_
    rw [← NatTrans.naturality_apply]
    exact (congrArg _ (hz k)).trans (z' k).2.2

end AlgebraicGeometry.Space.SmoothLift

namespace AlgebraicGeometry.Space

open SmoothLift

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04AM, (1) implies (2), formal smoothness.** A smooth morphism of algebraic spaces
over `S` is formally smooth. -/
theorem formallySmooth_of_isSmooth_of_isAlgebraicSpace {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsSmooth B S hS f) : FormallySmooth f := by
  intro T T' hT hT' i hi x y hxy
  have := hT
  have := hT'
  have hsq : i ≫ (eT' i hi).inv = (eT i hi).inv ≫ incl (baseAlg (baseOf i hi)) := by
    rw [Iso.comp_inv_eq, Category.assoc, ← eT_hom_i, Iso.inv_hom_id_assoc]
  have hxy' : f.app _ (X.map (eT i hi).hom.op x) =
      Y.map (incl (baseAlg (baseOf i hi))).op (Y.map (eT' i hi).hom.op y) := by
    rw [NatTrans.naturality_apply, hxy, map_map, map_map, eT_hom_i]
  let 𝔓 : Problem (baseOf i hi) :=
    ⟨X, Y, hX, hY, f, X.map (eT i hi).hom.op x, Y.map (eT' i hi).hom.op y, hxy'⟩
  obtain ⟨z, hz1, hz2⟩ := 𝔓.exists_lift hf
  refine ⟨X.map (eT' i hi).inv.op z, ?_, ?_⟩
  · change X.map (incl (baseAlg (baseOf i hi))).op z = X.map (eT i hi).hom.op x at hz1
    rw [map_map, hsq, ← map_map, hz1, map_map, Iso.inv_hom_id, op_id,
      Functor.map_id_apply]
  · change f.app _ z = Y.map (eT' i hi).hom.op y at hz2
    rw [NatTrans.naturality_apply, hz2, map_map, Iso.inv_hom_id, op_id,
      Functor.map_id_apply]

end AlgebraicGeometry.Space
