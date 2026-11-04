module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.TangentDecalage

/-!
# Lifting the descent datum to first order

With the notation of `AlgebraicGeometry.Stack.GroupoidLift.NerveDatum`: given a lift `u` of the
point `ū` over `C'`, and a lift `r` of the descent arrow `r̄` with source `v₀ ∘ u`, the
*obstruction* is the class in `Mod` at the vertex `1` of the difference between `vₗ ∘ u` and the
target of `r`. When the descent arrow satisfies the cocycle condition (`NerveDatum.IsCocycle`) the
obstruction is a `1`-cocycle of the tangent décalage (`obs_cocycle`), and changing `u` by a
derivation `E` changes it by the coboundary of `E` (`obs_addLift`). By the décalage the obstruction
is therefore killed by a change of `u`, and then `r` may be chosen with target `vₗ ∘ u`.

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.NerveDatum.obs_addLift`: the change-of-lift formula.
* `AlgebraicGeometry.Stack.GroupoidLift.NerveDatum.obs_cocycle`: the obstruction is a cocycle.
* `AlgebraicGeometry.Stack.GroupoidLift.NerveDatum.exists_lift_arrow`: for a cocycle descent
  arrow and a faithfully flat `C'` there is a lift `u` of `ū` and a lift `r` of `r̄` from
  `v₀ ∘ u` to `vₗ ∘ u`.
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {A' : Type u} [CommRing A'] {κ : Cardinal.{u}}
  {P : Type u} [CommRing P] [Algebra A' P] {G : Groupoid A' κ P}
  {hκ : Cardinal.aleph0 < κ} {C' : Type u} [CommRing C'] [Algebra A' C']
  {hC : Cardinal.mk C' < κ} {I : Ideal A'} {hI : I ^ 2 = ⊥}

/-- The class in `Mod` of a sum of derivations is the sum of their classes. -/
theorem mkMod_add' {C₁ C₂ : SmallAlg A' κ} {e : SqZero C₁ C₂} {w : P →ₐ[A'] C₂.obj}
    {a b : P →ₗ[A'] C₁.obj} (ha : a ∈ Der e w) (hb : b ∈ Der e w) :
    (mkMod (G := G) a ha : Mod G e w) + mkMod b hb = mkMod (a + b) (Submodule.add_mem _ ha hb) :=
  rfl

/-- The class in `Mod` of a difference of derivations is the difference of their classes. -/
theorem mkMod_sub' {C₁ C₂ : SmallAlg A' κ} {e : SqZero C₁ C₂} {w : P →ₐ[A'] C₂.obj}
    {a b : P →ₗ[A'] C₁.obj} (ha : a ∈ Der e w) (hb : b ∈ Der e w) :
    (mkMod (G := G) a ha : Mod G e w) - mkMod b hb = mkMod (a - b) (Submodule.sub_mem _ ha hb) :=
  rfl

/-- A transport may be restated along equal endpoints. -/
theorem Tr.congr {C₁ C₂ : SmallAlg A' κ} {e : SqZero C₁ C₂} {R : G.arr.obj C₂}
    {a a' b b' : P →ₐ[A'] C₁.obj} (t : Tr G e R a b) (ha : a = a') (hb : b = b') :
    Tr G e R a' b' := by
  subst ha hb
  exact t

/-- A lift of an arrow, pulled back along a map of the nerve, is a transport of the pullback. -/
theorem tr_pull {n m : ℕ} (f : cech A' C' n →ₐ[A'] cech A' C' m)
    {R : G.arr.obj (red I (nerve (A' := A') hκ C' hC n))}
    {r : G.arr.obj (nerve (A' := A') hκ C' hC n)}
    (hr : G.arr.map (thk I hI (nerve (A' := A') hκ C' hC n)).q r = R) :
    Tr G (thk I hI (nerve (A' := A') hκ C' hC m))
      (G.arr.map (thkHom I hI (N := nerve (A' := A') hκ C' hC n)
        (N' := nerve (A' := A') hκ C' hC m) f).bot R)
      (f.comp (G.src r)) (f.comp (G.tgt r)) :=
  Tr.map (thkHom I hI (N := nerve (A' := A') hκ C' hC n) (N' := nerve (A' := A') hκ C' hC m) f)
    ⟨r, hr, rfl, rfl⟩

/-- Postcomposition with a map of the nerve sends a difference of two lifts to the difference of
their images. -/
private theorem postcomp_Th_sub {n m : ℕ} (f : cech A' C' n →ₐ[A'] cech A' C' m)
    (a b : P →ₐ[A'] (nerve (A' := A') hκ C' hC n).obj) :
    postcomp (NerveDatum.Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) f)
        (a.toLinearMap - b.toLinearMap) =
      (f.comp a).toLinearMap - (f.comp b).toLinearMap := by
  ext x
  exact map_sub f (a x) (b x)

/-- A lift of an arrow `r` of the nerve with source `s` is a transport from `s`. -/
private theorem tr_pull_of_src {n m : ℕ} (f : cech A' C' n →ₐ[A'] cech A' C' m)
    {R : G.arr.obj (red I (nerve (A' := A') hκ C' hC n))}
    {r : G.arr.obj (nerve (A' := A') hκ C' hC n)}
    (hr : G.arr.map (thk I hI (nerve (A' := A') hκ C' hC n)).q r = R)
    {s : P →ₐ[A'] (nerve (A' := A') hκ C' hC m).obj} (hs : f.comp (G.src r) = s) :
    Tr G (thk I hI (nerve (A' := A') hκ C' hC m))
      (G.arr.map (thkHom I hI (N := nerve (A' := A') hκ C' hC n)
        (N' := nerve (A' := A') hκ C' hC m) f).bot R) s (f.comp (G.tgt r)) :=
  Tr.congr (tr_pull f hr) hs rfl

/-- The map of `Mod` along a map of the nerve, on the class of a difference of two lifts. -/
theorem modMap_thkHom_mk_sub {n m : ℕ} (f : cech A' C' n →ₐ[A'] cech A' C' m)
    {w : P →ₐ[A'] (red I (nerve (A' := A') hκ C' hC n)).obj}
    {w₂ : P →ₐ[A'] (red I (nerve (A' := A') hκ C' hC m)).obj}
    (hw : (thkHom I hI (N := nerve (A' := A') hκ C' hC n)
      (N' := nerve (A' := A') hκ C' hC m) f).bot.hom.hom.comp w = w₂)
    {ℓ₁ ℓ₂ : P →ₐ[A'] (nerve (A' := A') hκ C' hC n).obj}
    (h₁ : (thk I hI (nerve (A' := A') hκ C' hC n)).q.hom.hom.comp ℓ₁ = w)
    (h₂ : (thk I hI (nerve (A' := A') hκ C' hC n)).q.hom.hom.comp ℓ₂ = w)
    (h₁' : (thk I hI (nerve (A' := A') hκ C' hC m)).q.hom.hom.comp (f.comp ℓ₁) = w₂)
    (h₂' : (thk I hI (nerve (A' := A') hκ C' hC m)).q.hom.hom.comp (f.comp ℓ₂) = w₂) :
    modMap (G := G) (thkHom I hI (N := nerve (A' := A') hκ C' hC n)
        (N' := nerve (A' := A') hκ C' hC m) f) hw
      (mkMod (ℓ₂.toLinearMap - ℓ₁.toLinearMap) (sub_mem_Der h₁ h₂)) =
      mkMod ((f.comp ℓ₂).toLinearMap - (f.comp ℓ₁).toLinearMap) (sub_mem_Der h₁' h₂') := by
  rw [modMap_mk]
  exact mkMod_congr (postcomp_Th_sub f ℓ₂ ℓ₁) _ _

namespace NerveDatum

variable (D : NerveDatum hκ C' hC I hI G)

/-- The target of a lift `r` of the descent arrow reduces to the point `w 1` of the nerve. -/
theorem tgt_lift_reduce {r : G.arr.obj (nerve (A' := A') hκ C' hC 1)}
    (hr : G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 1)).q r = D.rbar) :
    (thk I hI (nerve (A' := A') hκ C' hC 1)).q.hom.hom.comp (G.tgt r) = D.w 1 := by
  rw [← G.tgt_map, hr, D.tgt_rbar]

/-- If `u` lifts `ū`, then `vₗ ∘ u` reduces to the point `w n` of the nerve at every level. -/
theorem vₗ_lift_reduce {u : P →ₐ[A'] C'}
    (hu : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp u = D.ubar) (n : ℕ) :
    (thk I hI (nerve (A' := A') hκ C' hC n)).q.hom.hom.comp ((vₗ A' C' n).comp u) = D.w n := by
  rw [q_comp_lift (n := 0) (vₗ A' C' n) u, hu]

/-- **The obstruction** of a lift `u` and a lift `r` of the descent arrow with source `v₀ ∘ u`. -/
noncomputable def obs {u : P →ₐ[A'] C'}
    (hu : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp u = D.ubar)
    (r : G.arr.obj (nerve (A' := A') hκ C' hC 1))
    (hr : G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 1)).q r = D.rbar) : D.M 1 :=
  mkMod (((vₗ A' C' 1).comp u).toLinearMap - (G.tgt r).toLinearMap)
    (sub_mem_Der (D.tgt_lift_reduce hr) (D.vₗ_lift_reduce hu 1))

variable (hG : G.SrcFormallySmooth)
/-- The plain face `0` of level `0` on the class of a difference of two lifts. -/
theorem faceT_zero_zero_mk {u u' : P →ₐ[A'] C'}
    (hu : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp u = D.w 0)
    (hu' : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp u' = D.w 0)
    (h₁ : (thk I hI (nerve (A' := A') hκ C' hC 1)).q.hom.hom.comp ((vₗ A' C' 1).comp u) = D.w 1)
    (h₂ : (thk I hI (nerve (A' := A') hκ C' hC 1)).q.hom.hom.comp ((vₗ A' C' 1).comp u') =
      D.w 1) :
    D.faceT hG 0 0 (mkMod (u'.toLinearMap - u.toLinearMap) (sub_mem_Der hu hu')) =
      mkMod (((vₗ A' C' 1).comp u').toLinearMap - ((vₗ A' C' 1).comp u).toLinearMap)
        (sub_mem_Der h₁ h₂) := by
  rw [show D.faceT hG 0 0 = modMapA' _ (D.hw_plain 0 0) from D.faceT_castSucc hG 0 0,
    modMapA'_apply]
  exact modMap_thkHom_mk_sub (face A' C' 0 0) (D.hw_plain 0 0) hu hu' h₁ h₂

/-- The twisted face `1` of level `0` on the class of a difference of two lifts: the transport
along the descent arrow. -/
theorem faceT_zero_one_mk {u u' : P →ₐ[A'] C'}
    (hu : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp u = D.w 0)
    (hu' : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp u' = D.w 0)
    {m m' : P →ₐ[A'] (nerve (A' := A') hκ C' hC 1).obj}
    (t : Tr G (thk I hI (nerve (A' := A') hκ C' hC 1)) (D.ρ 0) ((v₀ A' C' 1).comp u) m)
    (t' : Tr G (thk I hI (nerve (A' := A') hκ C' hC 1)) (D.ρ 0) ((v₀ A' C' 1).comp u') m') :
    D.faceT hG 0 1 (mkMod (u'.toLinearMap - u.toLinearMap) (sub_mem_Der hu hu')) =
      mkMod (m'.toLinearMap - m.toLinearMap)
        (sub_mem_Der (t.reduce_tgt.trans (D.tgt_ρ 0)) (t'.reduce_tgt.trans (D.tgt_ρ 0))) := by
  have h : ∀ v : P →ₐ[A'] C', (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp v = D.w 0 →
      (thk I hI (nerve (A' := A') hκ C' hC 1)).q.hom.hom.comp ((face A' C' 0 1).comp v) =
        D.wAt ((GroupoidLift.κ A' C' 0).comp (v₀ A' C' 1)) := fun v hv => by
    rw [q_comp_lift, hv]
    exact D.hw_tw 0
  have h₁ := h u hu
  have h₂ := h u' hu'
  rw [show D.faceT hG 0 1 = D.faceTw hG 0 from D.faceT_last hG 0]
  simp only [faceTw, LinearMap.comp_apply, LinearMap.restrictScalars_apply, modMapA'_apply]
  rw [modMap_thkHom_mk_sub (face A' C' 0 (Fin.last (0 + 1))) (D.hw_tw 0) hu hu' h₁ h₂]
  exact transModAt_mk (le_of_lt hκ) hG (D.ρ 0) (D.src_ρ 0) (D.tgt_ρ 0) _ _ h₁ h₂ t t'

/-- **Change of lift.** Moving the lift `u` by a derivation `E` moves the obstruction by the
coboundary of the class of `E`. -/
theorem obs_addLift {u : P →ₐ[A'] C'}
    (hu : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp u = D.ubar)
    (Ev : P →ₗ[A'] C') (hE : Ev ∈ Der (thk I hI (nerve (A' := A') hκ C' hC 0)) (D.w 0))
    (hu' : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp
      (addLift (e := thk I hI (nerve (A' := A') hκ C' hC 0)) Ev hE u
        (hu.trans D.w_zero.symm)) = D.ubar)
    {r r' : G.arr.obj (nerve (A' := A') hκ C' hC 1)}
    (hr : G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 1)).q r = D.rbar)
    (hr' : G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 1)).q r' = D.rbar)
    (hrs : G.src r = (v₀ A' C' 1).comp u)
    (hrs' : G.src r' = (v₀ A' C' 1).comp
      (addLift (e := thk I hI (nerve (A' := A') hκ C' hC 0)) Ev hE u (hu.trans D.w_zero.symm))) :
    D.obs hu' r' hr' =
      D.obs hu r hr + (D.faceT hG 0 0 (mkMod Ev hE) - D.faceT hG 0 1 (mkMod Ev hE)) := by
  have h0 := hu.trans D.w_zero.symm
  have h0' := hu'.trans D.w_zero.symm
  have t := tr_pull_of_src (GroupoidLift.κ A' C' 0) hr (by rw [hrs])
  have t' := tr_pull_of_src (GroupoidLift.κ A' C' 0) hr' (by rw [hrs'])
  rw [mkMod_addLift (G := G) (e := thk I hI (nerve (A' := A') hκ C' hC 0)) Ev hE u h0,
    D.faceT_zero_zero_mk hG h0 h0' (D.vₗ_lift_reduce hu 1) (D.vₗ_lift_reduce hu' 1),
    D.faceT_zero_one_mk hG h0 h0' t t']
  unfold obs
  rw [mkMod_sub', mkMod_add']
  apply mkMod_congr
  show _ = _ + (_ - ((G.tgt r').toLinearMap - (G.tgt r).toLinearMap))
  abel

/-- The face `0` of level `1` is the map `κ` of level `1`. -/
theorem face_one_zero_eq_κ : face A' C' 1 0 = GroupoidLift.κ A' C' 1 := rfl

/-- **The cocycle condition** on the descent arrow: over the triple nerve, the arrow from the
vertex `1` to `2` after the arrow from `0` to `1` is the arrow from `0` to `2`. -/
def IsCocycle : Prop :=
  ∃ h : G.src (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' 1 0)).bot
      D.rbar) = G.tgt (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI)
        (face A' C' 1 2)).bot D.rbar),
    G.comp (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' 1 0)).bot D.rbar)
      (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' 1 2)).bot D.rbar) h =
      G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' 1 1)).bot D.rbar

/-- The target of a lift `r` of the descent arrow, pushed along a map `f` of the nerve, reduces
to the point of `f ∘ vₗ`. -/
theorem q_comp_tgt {r : G.arr.obj (nerve (A' := A') hκ C' hC 1)}
    (hr : G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 1)).q r = D.rbar) {m : ℕ}
    (f : cech A' C' 1 →ₐ[A'] cech A' C' m) :
    (thk I hI (nerve (A' := A') hκ C' hC m)).q.hom.hom.comp (f.comp (G.tgt r)) =
      D.wAt (f.comp (vₗ A' C' 1)) := by
  rw [q_comp_lift, D.tgt_lift_reduce hr]
  exact D.Th_bot_wAt f (vₗ A' C' 1)

/-- If `u` lifts `ū`, then `f ∘ u` reduces to the point of `f`, for every map `f` from `C'`
into the nerve. -/
theorem q_comp_at {u : P →ₐ[A'] C'}
    (hu : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp u = D.ubar) {m : ℕ}
    (f : C' →ₐ[A'] cech A' C' m) :
    (thk I hI (nerve (A' := A') hκ C' hC m)).q.hom.hom.comp (f.comp u) = D.wAt f := by
  rw [q_comp_lift (n := 0) f u, hu]

/-- A plain face of level `1` on the obstruction. -/
theorem faceT_one_plain_obs {u : P →ₐ[A'] C'}
    (hu : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp u = D.ubar)
    {r : G.arr.obj (nerve (A' := A') hκ C' hC 1)}
    (hr : G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 1)).q r = D.rbar) (j : Fin 2)
    (h₂ : (thk I hI (nerve (A' := A') hκ C' hC 2)).q.hom.hom.comp
      ((face A' C' 1 j.castSucc).comp (G.tgt r)) = D.w 2) :
    D.faceT hG 1 j.castSucc (D.obs hu r hr) =
      mkMod (((vₗ A' C' 2).comp u).toLinearMap -
          ((face A' C' 1 j.castSucc).comp (G.tgt r)).toLinearMap)
        (sub_mem_Der h₂ (D.vₗ_lift_reduce hu 2)) := by
  rw [D.faceT_castSucc hG 1 j, modMapA'_apply]
  unfold obs
  rw [modMap_mk]
  apply mkMod_congr
  rw [postcomp_Th_sub, ← AlgHom.comp_assoc,
    face_comp_vₗ 1 j.castSucc (by have := j.isLt; simp; omega)]

/-- The twisted face of level `1` on the obstruction. -/
theorem faceT_one_last_obs {u : P →ₐ[A'] C'}
    (hu : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp u = D.ubar)
    {r : G.arr.obj (nerve (A' := A') hκ C' hC 1)}
    (hr : G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 1)).q r = D.rbar)
    (hrs : G.src r = (v₀ A' C' 1).comp u) {m : P →ₐ[A'] (nerve (A' := A') hκ C' hC 2).obj}
    (t : Tr G (thk I hI (nerve (A' := A') hκ C' hC 2)) (D.ρ 1)
      ((face A' C' 1 (Fin.last 2)).comp (G.tgt r)) m) :
    D.faceT hG 1 (Fin.last 2) (D.obs hu r hr) =
      mkMod (((GroupoidLift.κ A' C' 1).comp (G.tgt r)).toLinearMap - m.toLinearMap)
        (sub_mem_Der (t.reduce_tgt.trans (D.tgt_ρ 1))
          ((D.q_comp_tgt hr _).trans (by rw [κ_comp_vₗ]))) := by
  have t' := tr_pull_of_src (GroupoidLift.κ A' C' 1) hr (s := ((GroupoidLift.κ A' C' 1).comp
    (v₀ A' C' 1)).comp u) (by rw [hrs]; rfl)
  have h₁ := (D.q_comp_tgt hr (face A' C' 1 (Fin.last 2))).trans
    (by rw [face_last_comp_vₗ])
  have h₂ := D.q_comp_at hu ((GroupoidLift.κ A' C' 1).comp (v₀ A' C' 1))
  rw [D.faceT_last hG 1]
  simp only [faceTw, LinearMap.comp_apply, LinearMap.restrictScalars_apply, modMapA'_apply]
  unfold obs
  rw [modMap_mk]
  rw [mkMod_congr (show postcomp (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI)
      (face A' C' 1 (Fin.last (1 + 1))))
      (((vₗ A' C' 1).comp u).toLinearMap - (G.tgt r).toLinearMap) =
      (((GroupoidLift.κ A' C' 1).comp (v₀ A' C' 1)).comp u).toLinearMap -
        ((face A' C' 1 (Fin.last 2)).comp (G.tgt r)).toLinearMap by
      rw [postcomp_Th_sub, ← AlgHom.comp_assoc, face_last_comp_vₗ]) _ (sub_mem_Der h₁ h₂)]
  exact transModAt_mk (le_of_lt hκ) hG (D.ρ 1) (D.src_ρ 1) (D.tgt_ρ 1) _ _ h₁ h₂ t t'

/-- **The obstruction is a cocycle** of the tangent décalage. -/
theorem obs_cocycle (hcoc : D.IsCocycle) {u : P →ₐ[A'] C'}
    (hu : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp u = D.ubar)
    {r : G.arr.obj (nerve (A' := A') hκ C' hC 1)}
    (hr : G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 1)).q r = D.rbar)
    (hrs : G.src r = (v₀ A' C' 1).comp u) :
    D.faceT hG 1 0 (D.obs hu r hr) - D.faceT hG 1 1 (D.obs hu r hr) +
      D.faceT hG 1 2 (D.obs hu r hr) = 0 := by
  obtain ⟨hc, hcoc⟩ := hcoc
  have hq : (thk I hI (nerve (A' := A') hκ C' hC 2)).q.hom.hom.comp
      ((face A' C' 1 (Fin.last 2)).comp (G.tgt r)) = G.src (D.ρ 1) :=
    ((D.q_comp_tgt hr _).trans (by rw [face_last_comp_vₗ])).trans (D.src_ρ 1).symm
  obtain ⟨X, tX⟩ := exists_tr hG (D.ρ 1) _ hq
  have e0 : D.faceT hG 1 0 = D.faceT hG 1 (0 : Fin 2).castSucc := rfl
  have e1 : D.faceT hG 1 1 = D.faceT hG 1 (1 : Fin 2).castSucc := rfl
  have e2 : D.faceT hG 1 2 = D.faceT hG 1 (Fin.last 2) := rfl
  have h20 := (D.q_comp_tgt hr (face A' C' 1 (0 : Fin 2).castSucc)).trans
    (by rw [face_comp_vₗ 1 _ (by decide)])
  have h21 := (D.q_comp_tgt hr (face A' C' 1 (1 : Fin 2).castSucc)).trans
    (by rw [face_comp_vₗ 1 _ (by decide)])
  rw [e0, e1, e2, D.faceT_one_plain_obs hG hu hr 0 h20, D.faceT_one_plain_obs hG hu hr 1 h21,
    D.faceT_one_last_obs hG hu hr hrs tX, mkMod_sub', mkMod_add', mkMod_eq_zero_iff]
  have key : ((face A' C' 1 (1 : Fin 2).castSucc).comp (G.tgt r)).toLinearMap - X.toLinearMap ∈
      S G (thk I hI (nerve (A' := A') hκ C' hC 2)) (D.w 2) := by
    have tX' : Tr G (thk I hI (nerve (A' := A') hκ C' hC 2))
        (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' 1 0)).bot D.rbar)
        ((face A' C' 1 (Fin.last 2)).comp (G.tgt r)) X := tX
    have t02 := Tr.comp hc (tr_pull (face A' C' 1 2) hr) tX'
    rw [hcoc] at t02
    have a1 : (face A' C' 1 2).comp (v₀ A' C' 1) = v₀ A' C' 2 := face_succ_comp_v₀ 1 1
    have a2 : (face A' C' 1 1).comp (v₀ A' C' 1) = v₀ A' C' 2 := face_succ_comp_v₀ 1 0
    have hsrc : (face A' C' 1 2).comp (G.src r) = (face A' C' 1 1).comp (G.src r) := by
      rw [hrs, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc, a1, a2]
    have rel := Tr.rel (Tr.congr t02 hsrc rfl) (tr_pull (face A' C' 1 1) hr)
    have htgt : G.tgt (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI)
        (face A' C' 1 1)).bot D.rbar) = D.w 2 := by
      rw [G.tgt_map, D.tgt_rbar]
      exact (D.Th_bot_wAt _ _).trans (by rw [face_comp_vₗ 1 1 (by decide)])
    rw [htgt] at rel
    exact sub_mem_S (tX.reduce_tgt.trans (D.tgt_ρ 1)) rel
  convert key using 1
  rw [show ((GroupoidLift.κ A' C' 1).comp (G.tgt r)).toLinearMap =
    ((face A' C' 1 (0 : Fin 2).castSucc).comp (G.tgt r)).toLinearMap from rfl]
  abel

section Existence

variable [Module.FinitePresentation P Ω[P⁄A']] [Module.FaithfullyFlat A' C']
  {Q : Type u} [CommRing Q] [Algebra A' Q] [Module.FinitePresentation Q Ω[Q⁄A']]
  {b : Chart G.arr Q} (hb : b.IsFormallyEtale) {sV tV : P →ₐ[A'] Q}
  (hsV : ∀ (C : SmallAlg A' κ) (v : Q →ₐ[A'] C.obj), G.src (b.app C v) = v.comp sV)
  (htV : ∀ (C : SmallAlg A' κ) (v : Q →ₐ[A'] C.obj), G.tgt (b.app C v) = v.comp tV)
  (εbar : Q →ₐ[A'] (red I (nerve (A' := A') hκ C' hC 0)).obj) (ε₀ : Q →ₐ[A'] C')
  (hε₀ : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp ε₀ = εbar)
  (hε : b.app _ εbar = G.idt D.ubar)

include hG hb hsV htV hε₀ hε in
/-- **The first-order step.** A cocycle descent arrow lifts, after a change of the lift of the
point, to an arrow from `v₀ ∘ u` to `vₗ ∘ u`. -/
theorem exists_lift_arrow (hcoc : D.IsCocycle) :
    ∃ (u : P →ₐ[A'] C') (_ : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp u = D.ubar)
      (r : G.arr.obj (nerve (A' := A') hκ C' hC 1)),
      G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 1)).q r = D.rbar ∧
        G.src r = (v₀ A' C' 1).comp u ∧ G.tgt r = (vₗ A' C' 1).comp u := by
  let T := D.tangentDecalage hG hb hsV htV εbar ε₀ hε₀ hε
  obtain ⟨r₀, hr₀, hs₀⟩ := hG (thk I hI (nerve (A' := A') hκ C' hC 1)) D.rbar
    ((v₀ A' C' 1).comp D.u₀) ((D.q_comp_at D.u₀_lift (v₀ A' C' 1)).trans D.src_rbar.symm)
  have hdiff : T.diff 1 (D.obs D.u₀_lift r₀ hr₀) = 0 := by
    rw [T.diff_one_apply]
    exact D.obs_cocycle hG hcoc D.u₀_lift hr₀ hs₀
  obtain ⟨y, hy⟩ := T.exists_diff_eq 0 _ hdiff
  obtain ⟨Ev, hE, rfl⟩ := Mod.mk_surjective y
  rw [T.diff_zero_apply] at hy
  have h0 := D.u₀_lift.trans D.w_zero.symm
  have hu₁ : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp
      (addLift (e := thk I hI (nerve (A' := A') hκ C' hC 0)) (-Ev) (neg_mem hE) D.u₀ h0) =
      D.ubar := (addLift_reduce _ _ _ _).trans D.w_zero
  obtain ⟨r₁, hr₁, hs₁⟩ := hG (thk I hI (nerve (A' := A') hκ C' hC 1)) D.rbar
    ((v₀ A' C' 1).comp (addLift (e := thk I hI (nerve (A' := A') hκ C' hC 0)) (-Ev)
      (neg_mem hE) D.u₀ h0)) ((D.q_comp_at hu₁ (v₀ A' C' 1)).trans D.src_rbar.symm)
  have hobs := D.obs_addLift hG D.u₀_lift (-Ev) (neg_mem hE) hu₁ hr₀ hr₁ hs₀ hs₁
  have hneg : (mkMod (G := G) (-Ev) (neg_mem hE) : D.M 0) = -mkMod Ev hE := rfl
  have hy' : D.faceT hG 0 0 (mkMod Ev hE) - D.faceT hG 0 1 (mkMod Ev hE) =
      D.obs D.u₀_lift r₀ hr₀ := hy
  have hzero : D.obs hu₁ r₁ hr₁ = 0 := by
    rw [hobs, hneg, map_neg, map_neg, neg_sub_neg, ← neg_sub, hy', add_neg_cancel]
  unfold obs at hzero
  rw [mkMod_eq_zero_iff] at hzero
  have hrel := (rel_iff_mem_S b hb sV tV hsV htV (D.chart_at εbar hε 1) (D.tgt_lift_reduce hr₁)
    (D.vₗ_lift_reduce hu₁ 1)).mpr hzero
  have t : Tr G (thk I hI (nerve (A' := A') hκ C' hC 1)) D.rbar
      ((v₀ A' C' 1).comp (addLift (e := thk I hI (nerve (A' := A') hκ C' hC 0)) (-Ev)
        (neg_mem hE) D.u₀ h0)) (G.tgt r₁) := ⟨r₁, hr₁, hs₁, rfl⟩
  obtain ⟨r, hr, hs, ht⟩ := Tr.of_rel_tgt t (by rw [D.tgt_rbar]; exact hrel)
  exact ⟨_, hu₁, r, hr, hs, ht⟩

end Existence

end NerveDatum

end AlgebraicGeometry.Stack.GroupoidLift

end
