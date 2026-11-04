module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.Nerve
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.Decalage

/-!
# The décalage of the tangent modules along a descent datum

Fix the Čech nerve of a flat `κ`-small `A'`-algebra `C'`, thickened along a square-zero ideal
`I ⊆ A'`, a point `ū` of the reduction of `C'` and an arrow `r̄` of the groupoid over the reduction
of `C' ⊗ C'` from the vertex `0` to the vertex `1` of `ū`. The modules `Mod` at the last vertex
`ū n` of the levels of the nerve form a décalage
(`AlgebraicGeometry.Stack.GroupoidLift.tangentDecalage`): the faces of index at most `n` are
induced by the faces of the nerve, the last face is the face of the nerve followed by the transport
along the pullback of `r̄`, and the décalage itself is the flat base change along the face `0`.
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {A' : Type u} [CommRing A'] {κ : Cardinal.{u}}
  {P : Type u} [CommRing P] [Algebra A' P] {G : Groupoid A' κ P}

/-- A map of thickenings induces an `A'`-linear map of `Mod`. -/
noncomputable def modMapA' {C' C D' D : SmallAlg A' κ} {e : SqZero C' C} {e₂ : SqZero D' D}
    (φ : SqZero.Hom e e₂) {w : P →ₐ[A'] C.obj} {w₂ : P →ₐ[A'] D.obj}
    (hw : φ.bot.hom.hom.comp w = w₂) : Mod G e w →ₗ[A'] Mod G e₂ w₂ where
  toFun := modMap φ hw
  map_add' := map_add _
  map_smul' a m := by
    have h0 : a • m = (algebraMap A' C'.obj a) • m :=
      (IsScalarTower.algebraMap_smul (A := (C'.obj : Type u)) a m).symm
    rw [h0, map_smulₛₗ, RingHom.id_apply]
    have h1 : (φ.top.hom.hom : C'.obj →+* D'.obj) (algebraMap A' C'.obj a) =
        algebraMap A' D'.obj a := φ.top.hom.hom.commutes a
    rw [h1]
    exact IsScalarTower.algebraMap_smul (A := (D'.obj : Type u)) a _

/-- The `A'`-linear map `modMapA' φ hw` is `modMap φ hw`. -/
theorem modMapA'_apply {C' C D' D : SmallAlg A' κ} {e : SqZero C' C} {e₂ : SqZero D' D}
    (φ : SqZero.Hom e e₂) {w : P →ₐ[A'] C.obj} {w₂ : P →ₐ[A'] D.obj}
    (hw : φ.bot.hom.hom.comp w = w₂) (m : Mod G e w) :
    modMapA' φ hw m = modMap φ hw m := rfl

variable (hκ : Cardinal.aleph0 < κ) (C' : Type u) [CommRing C'] [Algebra A' C']
  (hC : Cardinal.mk C' < κ) (I : Ideal A') (hI : I ^ 2 = ⊥)

/-- The data of a descent problem along the nerve. -/
structure NerveDatum (G : Groupoid A' κ P) where
  /-- The point over the reduction of `C'`. -/
  ubar : P →ₐ[A'] (red I (nerve (A' := A') hκ C' hC 0)).obj
  /-- A lift of the point. -/
  u₀ : P →ₐ[A'] C'
  /-- The lift `u₀` reduces to `ubar`. -/
  u₀_lift : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp u₀ = ubar
  /-- The descent arrow, from the vertex `0` to the vertex `1`. -/
  rbar : G.arr.obj (red I (nerve (A' := A') hκ C' hC 1))
  src_rbar : G.src rbar = (redMap I (N := nerve (A' := A') hκ C' hC 0)
    (N' := nerve (A' := A') hκ C' hC 1) (v₀ A' C' 1)).comp ubar
  tgt_rbar : G.tgt rbar = (redMap I (N := nerve (A' := A') hκ C' hC 0)
    (N' := nerve (A' := A') hκ C' hC 1) (vₗ A' C' 1)).comp ubar
  /-- The descent arrow restricts to the identity along the diagonal. -/
  norm_rbar : G.arr.map (thkHom I hI (N := nerve (A' := A') hκ C' hC 1)
    (N' := nerve (A' := A') hκ C' hC 0) (codeg A' C' 0)).bot rbar = G.idt ubar

namespace NerveDatum

variable {hκ C' hC I hI} (D : NerveDatum hκ C' hC I hI G)

/-- The thickening at level `n`. -/
abbrev E (n : ℕ) := thk I hI (nerve (A' := A') hκ C' hC n)

/-- The map of thickenings induced by an algebra map of the nerve. -/
abbrev Th {n m : ℕ} (f : cech A' C' n →ₐ[A'] cech A' C' m) :
    SqZero.Hom (thk I hI (nerve (A' := A') hκ C' hC n)) (thk I hI (nerve (A' := A') hκ C' hC m)) :=
  thkHom I hI (N := nerve (A' := A') hκ C' hC n) (N' := nerve (A' := A') hκ C' hC m) f

/-- The point at the last vertex of level `n`. -/
abbrev w (n : ℕ) : P →ₐ[A'] (red I (nerve (A' := A') hκ C' hC n)).obj :=
  (redMap I (N := nerve (A' := A') hκ C' hC 0) (N' := nerve (A' := A') hκ C' hC n)
    (vₗ A' C' n)).comp D.ubar

/-- The point at an arbitrary vertex `f : C' → cech n`. -/
abbrev wAt {n : ℕ} (f : C' →ₐ[A'] cech A' C' n) :
    P →ₐ[A'] (red I (nerve (A' := A') hκ C' hC n)).obj :=
  (redMap I (N := nerve (A' := A') hκ C' hC 0) (N' := nerve (A' := A') hκ C' hC n) f).comp D.ubar

/-- The map induced by `g` carries the point at the vertex `f` to the point at the vertex
`g.comp f`. -/
theorem Th_bot_wAt {n m : ℕ} (g : cech A' C' n →ₐ[A'] cech A' C' m) (f : C' →ₐ[A'] cech A' C' n) :
    (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g).bot.hom.hom.comp (D.wAt f) =
      D.wAt (g.comp f) := by
  rw [thkHom_bot, ← AlgHom.comp_assoc]
  exact congrArg (fun h ↦ h.comp D.ubar)
    (redMap_comp I (N := nerve (A' := A') hκ C' hC 0) (N' := nerve (A' := A') hκ C' hC n)
      (N'' := nerve (A' := A') hκ C' hC m) f g)

/-- The module at level `n`. -/
abbrev M (n : ℕ) : Type u :=
  Mod G (thk I hI (nerve (A' := A') hκ C' hC n)) (D.w n)

/-- The reduction of `f.comp ℓ` is the reduction of `ℓ` followed by the map induced by `f`. -/
theorem q_comp_lift {n m : ℕ} (f : cech A' C' n →ₐ[A'] cech A' C' m)
    (ℓ : P →ₐ[A'] cech A' C' n) :
    (thk I hI (nerve (A' := A') hκ C' hC m)).q.hom.hom.comp (f.comp ℓ) =
      (redMap I (N := nerve (A' := A') hκ C' hC n) (N' := nerve (A' := A') hκ C' hC m) f).comp
        ((thk I hI (nerve (A' := A') hκ C' hC n)).q.hom.hom.comp ℓ) := by
  ext x
  rfl

/-- The lift `f.comp D.u₀` reduces to the point `D.wAt f` at the vertex `f`. -/
theorem q_comp_liftAt {n : ℕ} (f : C' →ₐ[A'] cech A' C' n) :
    (thk I hI (nerve (A' := A') hκ C' hC n)).q.hom.hom.comp (f.comp D.u₀) = D.wAt f := by
  rw [q_comp_lift (n := 0) f D.u₀]
  exact congrArg _ D.u₀_lift

/-- The face of index `j.castSucc` carries the point at the last vertex of level `n` to the point
at the last vertex of level `n + 1`. -/
theorem hw_plain (n : ℕ) (j : Fin (n + 1)) :
    (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' n j.castSucc)).bot.hom.hom.comp
      (D.w n) = D.w (n + 1) := by
  rw [D.Th_bot_wAt, face_comp_vₗ n j.castSucc (by simp; omega)]

/-- The face `0` carries the point at the last vertex of level `n` to the point at the last vertex
of level `n + 1`. -/
theorem hw_zero (n : ℕ) :
    (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' n 0)).bot.hom.hom.comp
      (D.w n) = D.w (n + 1) := by
  rw [D.Th_bot_wAt, face_comp_vₗ n 0 (Nat.zero_le _)]

/-- The last face carries the point at the last vertex of level `n` to the point at the vertex
`(κ A' C' n).comp (v₀ A' C' 1)` of level `n + 1`. -/
theorem hw_tw (n : ℕ) :
    (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI)
        (face A' C' n (Fin.last (n + 1)))).bot.hom.hom.comp (D.w n) =
      D.wAt ((GroupoidLift.κ A' C' n).comp (v₀ A' C' 1)) := by
  rw [D.Th_bot_wAt, face_last_comp_vₗ]

/-- The pullback of the descent arrow to the last two vertices of level `n + 1`. -/
abbrev ρ (n : ℕ) : G.arr.obj (red I (nerve (A' := A') hκ C' hC (n + 1))) :=
  G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (GroupoidLift.κ A' C' n)).bot D.rbar

/-- The source of `D.ρ n` is the point at the vertex `(κ A' C' n).comp (v₀ A' C' 1)`. -/
theorem src_ρ (n : ℕ) : G.src (D.ρ n) = D.wAt ((GroupoidLift.κ A' C' n).comp (v₀ A' C' 1)) := by
  rw [G.src_map, D.src_rbar]
  exact D.Th_bot_wAt _ _

/-- The target of `D.ρ n` is the point at the last vertex of level `n + 1`. -/
theorem tgt_ρ (n : ℕ) : G.tgt (D.ρ n) = D.w (n + 1) := by
  rw [G.tgt_map, D.tgt_rbar, D.Th_bot_wAt, κ_comp_vₗ]

/-- The reduction of the map induced by `g` followed by that induced by `f` is the reduction of the
map induced by `f.comp g`. -/
theorem Th_comp_bot {n m k : ℕ} (f : cech A' C' m →ₐ[A'] cech A' C' k)
    (g : cech A' C' n →ₐ[A'] cech A' C' m) :
    (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g).bot ≫
      (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) f).bot =
      (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (f.comp g)).bot :=
  ObjectProperty.hom_ext _ <| CommAlgCat.hom_ext <|
    redMap_comp I (N := nerve (A' := A') hκ C' hC n) (N' := nerve (A' := A') hκ C' hC m)
      (N'' := nerve (A' := A') hκ C' hC k) g f

/-- Transporting an arrow along the map induced by `g` and then along the map induced by `f` is
transporting it along the map induced by `f.comp g`. -/
theorem map_Th_map_Th {n m k : ℕ} (f : cech A' C' m →ₐ[A'] cech A' C' k)
    (g : cech A' C' n →ₐ[A'] cech A' C' m) (r : G.arr.obj (red I (nerve (A' := A') hκ C' hC n))) :
    G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) f).bot
      (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g).bot r) =
      G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (f.comp g)).bot r := by
  rw [G.map_map, Th_comp_bot]

/-- The face `0` carries `D.ρ n` to `D.ρ (n + 1)`. -/
theorem map_face_zero_ρ (n : ℕ) :
    G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' (n + 1) 0)).bot (D.ρ n) =
      D.ρ (n + 1) := by
  rw [map_Th_map_Th, face_comp_κ n 0 (Nat.zero_le _)]

/-- The codegeneracy carries `D.ρ (n + 1)` to `D.ρ n`. -/
theorem map_codeg_ρ (n : ℕ) :
    G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (codeg A' C' (n + 1))).bot
      (D.ρ (n + 1)) = D.ρ n := by
  rw [map_Th_map_Th, codeg_comp_κ]

variable (hG : G.SrcFormallySmooth)

/-- The twisted (last) face: the face of the nerve followed by the transport. -/
noncomputable def faceTw (n : ℕ) : D.M n →ₗ[A'] D.M (n + 1) :=
  (transModAt (le_of_lt hκ) hG (D.ρ n) (D.src_ρ n) (D.tgt_ρ n)
      (((GroupoidLift.κ A' C' n).comp (v₀ A' C' 1)).comp D.u₀)
      (D.q_comp_liftAt _)).restrictScalars A' ∘ₗ
    modMapA' _ (D.hw_tw n)

/-- The faces of the décalage. -/
noncomputable def faceT (n : ℕ) (i : Fin (n + 2)) : D.M n →ₗ[A'] D.M (n + 1) :=
  Fin.lastCases (motive := fun _ ↦ D.M n →ₗ[A'] D.M (n + 1)) (D.faceTw hG n)
    (fun j ↦ modMapA' _ (D.hw_plain n j)) i

/-- The last face of the décalage is the twisted face `D.faceTw hG n`. -/
theorem faceT_last (n : ℕ) : D.faceT hG n (Fin.last (n + 1)) = D.faceTw hG n := by
  simp [faceT]

/-- The face of index `j.castSucc` of the décalage is the map of `Mod` induced by the face of index
`j.castSucc` of the nerve. -/
theorem faceT_castSucc (n : ℕ) (j : Fin (n + 1)) :
    D.faceT hG n j.castSucc = modMapA' _ (D.hw_plain n j) := by
  simp [faceT]

/-- The codegeneracy carries the point at the last vertex of level `n + 1` to the point at the last
vertex of level `n`. -/
theorem hw_codeg (n : ℕ) :
    (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (codeg A' C' n)).bot.hom.hom.comp
      (D.w (n + 1)) = D.w n := by
  rw [D.Th_bot_wAt, codeg_comp_vₗ]

/-- The codegeneracy of the décalage. -/
noncomputable def codegT (n : ℕ) : D.M (n + 1) →ₗ[A'] D.M n := modMapA' _ (D.hw_codeg n)

variable [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' C']

/-- The décalage map: the flat base change along the face `0`. -/
noncomputable def decalT (n : ℕ) : C' ⊗[A'] D.M n →ₗ[A'] D.M (n + 1) :=
  modBC (G := G) (hY := card_cech_lt A' C' hκ hC (n + 1)) (D.hw_zero n)

variable {Q : Type u} [CommRing Q] [Algebra A' Q] [Module.FinitePresentation Q Ω[Q⁄A']]
  {b : Chart G.arr Q} (hb : b.IsFormallyEtale) {sV tV : P →ₐ[A'] Q}
  (hsV : ∀ (C : SmallAlg A' κ) (v : Q →ₐ[A'] C.obj), G.src (b.app C v) = v.comp sV)
  (htV : ∀ (C : SmallAlg A' κ) (v : Q →ₐ[A'] C.obj), G.tgt (b.app C v) = v.comp tV)
  (εbar : Q →ₐ[A'] (red I (nerve (A' := A') hκ C' hC 0)).obj) (ε₀ : Q →ₐ[A'] C')
  (hε₀ : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp ε₀ = εbar)
  (hε : b.app _ εbar = G.idt D.ubar)

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' C']
  [Module.FinitePresentation Q Ω[Q⁄A']] in
include hε in
/-- The chart `b` sends the pullback of `εbar` to the last vertex of level `n` to the identity
arrow at `D.w n`. -/
theorem chart_at (n : ℕ) :
    b.app _ ((redMap I (N := nerve (A' := A') hκ C' hC 0) (N' := nerve (A' := A') hκ C' hC n)
      (vₗ A' C' n)).comp εbar) = G.idt (D.w n) := by
  have := b.natural (SmallAlg.homMk (redMap I (N := nerve (A' := A') hκ C' hC 0)
    (N' := nerve (A' := A') hκ C' hC n) (vₗ A' C' n))) εbar
  rw [← SmallAlg.homMk_hom (redMap I (N := nerve (A' := A') hκ C' hC 0)
    (N' := nerve (A' := A') hκ C' hC n) (vₗ A' C' n)), ← this, hε, G.idt_map]
  rfl

include hb hsV htV hε₀ hε in
/-- The décalage map `D.decalT n` is bijective. -/
theorem decalT_bijective (n : ℕ) : Function.Bijective (D.decalT n) :=
  modBC_bijective (isBaseChange_nerve_face_zero hκ C' hC I hI n) hb hsV htV
    ((vₗ A' C' n).comp D.u₀) (D.q_comp_liftAt _) (D.hw_zero n) (D.chart_at εbar hε n)
    ((vₗ A' C' n).comp ε₀) (by
      rw [q_comp_lift (n := 0) (vₗ A' C' n) ε₀, hε₀])

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' C'] in
/-- On a pure tensor `c ⊗ₜ m`, the décalage map is the image of `m` under the map induced by the
face `0`, multiplied by `1 ⊗ₜ c`. -/
theorem decalT_tmul (n : ℕ) (c : C') (m : D.M n) :
    D.decalT n (c ⊗ₜ m) = ((1 : cech A' C' n) ⊗ₜ[A'] c : cech A' C' n ⊗[A'] C') •
      modMap (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' n 0)) (D.hw_zero n) m :=
  rfl

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' C'] in
/-- A face of positive index sends `1 ⊗ₜ c` to `1 ⊗ₜ c`. -/
theorem face_succ_one_tmul (n : ℕ) (k : Fin (n + 2)) (c : C') :
    face A' C' (n + 1) k.succ ((1 : cech A' C' n) ⊗ₜ[A'] c) =
      ((1 : cech A' C' (n + 1)) ⊗ₜ[A'] c : cech A' C' (n + 1) ⊗[A'] C') := by
  rw [face_succ_tmul, map_one]

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' C'] in
/-- Composition of the maps induced by two algebra maps of the nerve. -/
theorem modMap_Th_Th {n m k : ℕ} (f : cech A' C' m →ₐ[A'] cech A' C' k)
    (g : cech A' C' n →ₐ[A'] cech A' C' m) (h : cech A' C' n →ₐ[A'] cech A' C' k)
    (hfg : f.comp g = h) {w : P →ₐ[A'] (red I (nerve (A' := A') hκ C' hC n)).obj}
    {w₂ : P →ₐ[A'] (red I (nerve (A' := A') hκ C' hC m)).obj}
    {w₃ : P →ₐ[A'] (red I (nerve (A' := A') hκ C' hC k)).obj}
    (hw : (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g).bot.hom.hom.comp w = w₂)
    (hw₂ : (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) f).bot.hom.hom.comp w₂ = w₃)
    (hw₃ : (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) h).bot.hom.hom.comp w = w₃)
    (x : Mod G (thk I hI (nerve (A' := A') hκ C' hC n)) w) :
    modMap (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) f) hw₂
      (modMap (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g) hw x) =
      modMap (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) h) hw₃ x :=
  modMap_modMap _ _ _ (fun y ↦ by rw [← hfg]; rfl) hw hw₂ hw₃ x

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' C'] in
/-- The décalage map intertwines the face of index `j.castSucc` at level `n` with the face of index
`j.castSucc.succ` at level `n + 1`. -/
theorem faceT_succ_decalT_plain (n : ℕ) (j : Fin (n + 1)) (c : C') (m : D.M n) :
    D.faceT hG (n + 1) j.castSucc.succ (D.decalT n (c ⊗ₜ m)) =
      D.decalT (n + 1) (c ⊗ₜ D.faceT hG n j.castSucc m) := by
  rw [Fin.succ_castSucc, faceT_castSucc, faceT_castSucc, modMapA'_apply, modMapA'_apply,
    decalT_tmul, decalT_tmul, map_smulₛₗ]
  have h1 : ((Th (hκ := hκ) (hC := hC) (I := I) (hI := hI)
      (face A' C' (n + 1) j.succ.castSucc)).top.hom.hom :
        (nerve (A' := A') hκ C' hC (n + 1)).obj →+* (nerve (A' := A') hκ C' hC (n + 2)).obj)
      ((1 : cech A' C' n) ⊗ₜ[A'] c) = ((1 : cech A' C' (n + 1)) ⊗ₜ[A'] c) := by
    show face A' C' (n + 1) j.succ.castSucc ((1 : cech A' C' n) ⊗ₜ[A'] c) = _
    rw [← Fin.succ_castSucc]
    exact face_succ_one_tmul n j.castSucc c
  rw [h1]
  congr 1
  rw [modMap_Th_Th _ _ ((face A' C' (n + 1) 0).comp (face A' C' n j.castSucc))
      (by rw [← Fin.succ_castSucc]; exact face_succ_comp_face_zero n j.castSucc) _ _
      (by rw [D.Th_bot_wAt, AlgHom.comp_assoc, face_comp_vₗ n j.castSucc (by simp; omega),
        face_comp_vₗ (n + 1) 0 (Nat.zero_le _)]),
    modMap_Th_Th _ _ ((face A' C' (n + 1) 0).comp (face A' C' n j.castSucc)) rfl _ _
      (by rw [D.Th_bot_wAt, AlgHom.comp_assoc, face_comp_vₗ n j.castSucc (by simp; omega),
        face_comp_vₗ (n + 1) 0 (Nat.zero_le _)])]

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' C'] in
/-- The face `0` carries the source of `D.ρ n` to the source of `D.ρ (n + 1)`. -/
theorem hw_srcρ (n : ℕ) :
    (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' (n + 1) 0)).bot.hom.hom.comp
      (D.wAt ((GroupoidLift.κ A' C' n).comp (v₀ A' C' 1))) =
      D.wAt ((GroupoidLift.κ A' C' (n + 1)).comp (v₀ A' C' 1)) := by
  rw [D.Th_bot_wAt, ← AlgHom.comp_assoc, face_comp_κ n 0 (Nat.zero_le _)]

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' C'] in
/-- The décalage map intertwines the last face at level `n` with the last face at level `n + 1`. -/
theorem faceT_succ_decalT_last (n : ℕ) (c : C') (m : D.M n) :
    D.faceT hG (n + 1) (Fin.last (n + 1)).succ (D.decalT n (c ⊗ₜ m)) =
      D.decalT (n + 1) (c ⊗ₜ D.faceT hG n (Fin.last (n + 1)) m) := by
  rw [Fin.succ_last, faceT_last, faceT_last]
  simp only [faceTw, LinearMap.comp_apply, LinearMap.restrictScalars_apply, modMapA'_apply]
  rw [decalT_tmul, decalT_tmul, map_smulₛₗ]
  have h1 : ((Th (hκ := hκ) (hC := hC) (I := I) (hI := hI)
      (face A' C' (n + 1) (Fin.last (n + 2)))).top.hom.hom :
        (nerve (A' := A') hκ C' hC (n + 1)).obj →+* (nerve (A' := A') hκ C' hC (n + 2)).obj)
      ((1 : cech A' C' n) ⊗ₜ[A'] c) = ((1 : cech A' C' (n + 1)) ⊗ₜ[A'] c) := by
    show face A' C' (n + 1) (Fin.last (n + 2)) ((1 : cech A' C' n) ⊗ₜ[A'] c) = _
    rw [← Fin.succ_last]
    exact face_succ_one_tmul n (Fin.last (n + 1)) c
  rw [h1, LinearMap.map_smul]
  congr 1
  rw [modMap_transModAt' (le_of_lt hκ) hG _ (D.ρ n) (D.src_ρ n) (D.tgt_ρ n) _ _ (D.hw_srcρ n)
      (D.hw_zero (n + 1)) (D.ρ (n + 1)) (D.map_face_zero_ρ n) (D.src_ρ (n + 1)) (D.tgt_ρ (n + 1))
      (((GroupoidLift.κ A' C' (n + 1)).comp (v₀ A' C' 1)).comp D.u₀) (D.q_comp_liftAt _)]
  congr 1
  have hcomp : (face A' C' (n + 1) (Fin.last (n + 2))).comp (face A' C' n 0) =
      (face A' C' (n + 1) 0).comp (face A' C' n (Fin.last (n + 1))) := by
    rw [← Fin.succ_last]
    exact face_succ_comp_face_zero n (Fin.last (n + 1))
  rw [modMap_Th_Th _ _ _ hcomp _ _ (by
      rw [D.Th_bot_wAt, AlgHom.comp_assoc, face_last_comp_vₗ, ← AlgHom.comp_assoc,
        face_comp_κ n 0 (Nat.zero_le _)]),
    modMap_Th_Th _ _ ((face A' C' (n + 1) 0).comp (face A' C' n (Fin.last (n + 1)))) rfl _ _
      (by rw [D.Th_bot_wAt, AlgHom.comp_assoc, face_last_comp_vₗ, ← AlgHom.comp_assoc,
        face_comp_κ n 0 (Nat.zero_le _)])]

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' C'] in
/-- The map of `Mod` induced by the identity of the nerve is the transport along the equality
`w = w'`. -/
theorem modMap_Th_id {n : ℕ} {w w' : P →ₐ[A'] (red I (nerve (A' := A') hκ C' hC n)).obj}
    (hw : (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI)
      (AlgHom.id A' (cech A' C' n))).bot.hom.hom.comp w = w') (hww : w = w')
    (x : Mod G (thk I hI (nerve (A' := A') hκ C' hC n)) w) :
    modMap (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (AlgHom.id A' (cech A' C' n))) hw x =
      hww ▸ x := by
  subst hww
  obtain ⟨Dv, hDv, rfl⟩ := Mod.mk_surjective x
  rw [modMap_mk]
  rfl

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' C'] in
/-- The codegeneracy after the face of index `j.castSucc.succ.succ` is the face of index
`j.castSucc.succ` after the codegeneracy. -/
theorem codegT_faceT_succ_succ_plain (n : ℕ) (j : Fin n) (m : D.M (n + 1)) :
    D.codegT (n + 1) (D.faceT hG (n + 1) j.castSucc.succ.succ m) =
      D.faceT hG n j.castSucc.succ (D.codegT n m) := by
  have e1 : j.castSucc.succ.succ = (j.succ.succ : Fin (n + 2)).castSucc := by
    ext; simp
  have e2 : (j.castSucc.succ : Fin (n + 2)) = (j.succ : Fin (n + 1)).castSucc := by
    ext; simp
  rw [e1, e2, faceT_castSucc, faceT_castSucc]
  simp only [codegT, modMapA'_apply]
  have hring :
      (codeg A' C' (n + 1)).comp (face A' C' (n + 1) (j.succ.succ : Fin (n + 2)).castSucc) =
        (face A' C' n (j.succ : Fin (n + 1)).castSucc).comp (codeg A' C' n) := by
    rw [← e1, ← e2]
    exact codeg_comp_face_succ_succ n j.castSucc
  rw [modMap_Th_Th _ _ _ hring _ _ (by
      rw [D.Th_bot_wAt, AlgHom.comp_assoc, codeg_comp_vₗ, face_comp_vₗ n _ (by simp)]),
    modMap_Th_Th _ _ ((face A' C' n (j.succ : Fin (n + 1)).castSucc).comp (codeg A' C' n)) rfl _ _
      (by rw [D.Th_bot_wAt, AlgHom.comp_assoc, codeg_comp_vₗ, face_comp_vₗ n _ (by simp)])]

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' C'] in
/-- The codegeneracy carries the source of `D.ρ (n + 1)` to the source of `D.ρ n`. -/
theorem hw_codeg_srcρ (n : ℕ) :
    (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (codeg A' C' (n + 1))).bot.hom.hom.comp
      (D.wAt ((GroupoidLift.κ A' C' (n + 1)).comp (v₀ A' C' 1))) =
      D.wAt ((GroupoidLift.κ A' C' n).comp (v₀ A' C' 1)) := by
  rw [D.Th_bot_wAt, ← AlgHom.comp_assoc, codeg_comp_κ]

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' C'] in
/-- The codegeneracy after the last face at level `n + 1` is the last face at level `n` after the
codegeneracy. -/
theorem codegT_faceT_succ_succ_last (n : ℕ) (m : D.M (n + 1)) :
    D.codegT (n + 1) (D.faceT hG (n + 1) (Fin.last n).succ.succ m) =
      D.faceT hG n (Fin.last n).succ (D.codegT n m) := by
  rw [Fin.succ_last, Fin.succ_last, faceT_last, faceT_last]
  simp only [faceTw, codegT, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    modMapA'_apply]
  rw [modMap_transModAt' (le_of_lt hκ) hG _ (D.ρ (n + 1)) (D.src_ρ (n + 1)) (D.tgt_ρ (n + 1)) _ _
      (D.hw_codeg_srcρ n) (D.hw_codeg (n + 1)) (D.ρ n) (D.map_codeg_ρ n) (D.src_ρ n) (D.tgt_ρ n)
      (((GroupoidLift.κ A' C' n).comp (v₀ A' C' 1)).comp D.u₀) (D.q_comp_liftAt _)]
  congr 1
  have hring : (codeg A' C' (n + 1)).comp (face A' C' (n + 1) (Fin.last (n + 2))) =
      (face A' C' n (Fin.last (n + 1))).comp (codeg A' C' n) := by
    have := codeg_comp_face_succ_succ (A' := A') (C' := C') n (Fin.last n)
    rwa [Fin.succ_last, Fin.succ_last] at this
  rw [modMap_Th_Th _ _ _ hring _ _ (by
      rw [D.Th_bot_wAt, AlgHom.comp_assoc, codeg_comp_vₗ, face_last_comp_vₗ]),
    modMap_Th_Th _ _ ((face A' C' n (Fin.last (n + 1))).comp (codeg A' C' n)) rfl _ _
      (by rw [D.Th_bot_wAt, AlgHom.comp_assoc, codeg_comp_vₗ, face_last_comp_vₗ])]

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' C'] in
/-- The point at the last vertex of level `0` is `D.ubar`. -/
theorem w_zero : D.w 0 = D.ubar := by
  show (redMap I (N := nerve (A' := A') hκ C' hC 0) (N' := nerve (A' := A') hκ C' hC 0)
    (AlgHom.id A' _)).comp D.ubar = D.ubar
  rw [redMap_id]
  rfl

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' C'] in
/-- The codegeneracy carries `D.ρ 0` to the identity arrow at `D.w 0`. -/
theorem map_codeg_ρ_zero :
    G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (codeg A' C' 0)).bot (D.ρ 0) =
      G.idt (D.w 0) := by
  rw [map_Th_map_Th, w_zero]
  exact D.norm_rbar

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' C'] in
/-- At level `0`, the codegeneracy after the face `1` is the identity. -/
theorem codegT_faceT_one_zero (m : D.M 0) : D.codegT 0 (D.faceT hG 0 1 m) = m := by
  show D.codegT 0 (D.faceT hG 0 (Fin.last 1) m) = m
  rw [faceT_last]
  simp only [faceTw, codegT, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    modMapA'_apply]
  have hsrc : (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (codeg A' C' 0)).bot.hom.hom.comp
      (D.wAt ((GroupoidLift.κ A' C' 0).comp (v₀ A' C' 1))) = D.w 0 := by
    rw [D.Th_bot_wAt, ← AlgHom.comp_assoc]
    exact congrArg D.wAt (codeg_comp_face_one 0)
  rw [modMap_transModAt' (le_of_lt hκ) hG _ (D.ρ 0) (D.src_ρ 0) (D.tgt_ρ 0) _ _
      hsrc (D.hw_codeg 0) (G.idt (D.w 0)) D.map_codeg_ρ_zero (G.src_idt _) (G.tgt_idt _)
      ((vₗ A' C' 0).comp D.u₀) (D.q_comp_liftAt _), transModAt_idt]
  rw [modMap_Th_Th _ _ (AlgHom.id A' _)
      (show (codeg A' C' 0).comp (face A' C' 0 (Fin.last (0 + 1))) = AlgHom.id A' _ from
        codeg_comp_face_one 0) _ _
      (by rw [D.Th_bot_wAt]; rfl), modMap_Th_id _ rfl]

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' C'] in
/-- At level `n + 1`, the codegeneracy after the face `1` is the identity. -/
theorem codegT_faceT_one_succ (n : ℕ) (m : D.M (n + 1)) :
    D.codegT (n + 1) (D.faceT hG (n + 1) 1 m) = m := by
  have e1 : (1 : Fin (n + 3)) = (1 : Fin (n + 2)).castSucc := rfl
  rw [e1, faceT_castSucc]
  simp only [codegT, modMapA'_apply]
  rw [modMap_Th_Th _ _ (AlgHom.id A' _) (by rw [← e1]; exact codeg_comp_face_one (n + 1)) _ _
      (by rw [D.Th_bot_wAt]; rfl), modMap_Th_id _ rfl]

include hb hsV htV hε₀ hε in
/-- **The tangent modules along the nerve form a décalage.** -/
noncomputable def tangentDecalage : Stacks.Decalage.Decalage A' C' D.M where
  face := D.faceT hG
  codeg := D.codegT
  decal := D.decalT
  decal_bijective := D.decalT_bijective hb hsV htV εbar ε₀ hε₀ hε
  face_succ_decal n i x := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c m =>
      rw [LinearMap.lTensor_tmul]
      cases i using Fin.lastCases with
      | last => exact D.faceT_succ_decalT_last hG n c m
      | cast j => exact D.faceT_succ_decalT_plain hG n j c m
  codeg_face_one n m := by
    cases n with
    | zero => exact D.codegT_faceT_one_zero hG m
    | succ n => exact D.codegT_faceT_one_succ hG n m
  codeg_face_succ_succ n i m := by
    cases i using Fin.lastCases with
    | last => exact D.codegT_faceT_succ_succ_last hG n m
    | cast j => exact D.codegT_faceT_succ_succ_plain hG n j m

end NerveDatum

end AlgebraicGeometry.Stack.GroupoidLift

end
