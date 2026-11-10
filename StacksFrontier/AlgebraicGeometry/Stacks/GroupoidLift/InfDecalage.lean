module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.InfBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.FirstOrder

/-!
# The modules of infinitesimal automorphisms along the nerve

For a descent problem along the Čech nerve of `A' → C'` (`NerveDatum`) and a chart `b` of the
arrows near the identities, the infinitesimal automorphisms of the last vertex at level `n` form
the module `N n` of derivations of `Q` killed by `sV` and `tV` (see
`AlgebraicGeometry.Stack.GroupoidLift.exists_infOf_eq`). Given a lift of the descent arrow
between lifted points, these modules form a décalage
(`AlgebraicGeometry.Stack.GroupoidLift.NerveDatum.infDecalage`): the plain faces and the
codegeneracy are the maps of the nerve, the last face is twisted by conjugation with the lifted
descent arrow, and the décalage maps are the flat base change along the face `0`.

## Main definitions

* `AlgebraicGeometry.Stack.GroupoidLift.NerveDatum.vAt`: the chart point at a vertex.
* `AlgebraicGeometry.Stack.GroupoidLift.NerveDatum.N`: the module at level `n`.
* `infFacePlain`, `infCodeg`, `infDecal` (with `infDecal_bijective`), `infFaceLast`.
* `AlgebraicGeometry.Stack.GroupoidLift.NerveDatum.infDecalage`: the décalage.
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

namespace NerveDatum

variable (D : NerveDatum hκ C' hC I hI G)
  {Q : Type u} [CommRing Q] [Algebra A' Q] {b : Chart G.arr Q} (sV tV : P →ₐ[A'] Q)
  (εbar : Q →ₐ[A'] (red I (nerve (A' := A') hκ C' hC 0)).obj)

/-- The chart point at the vertex `f`. -/
abbrev vAt {n : ℕ} (f : C' →ₐ[A'] cech A' C' n) :
    Q →ₐ[A'] (red I (nerve (A' := A') hκ C' hC n)).obj :=
  (redMap I (N := nerve (A' := A') hκ C' hC 0) (N' := nerve (A' := A') hκ C' hC n) f).comp εbar

omit D in
/-- The bottom of the thickening map induced by `g` carries the chart point at `f` to the chart
point at `g.comp f`. -/
theorem Th_bot_vAt {n m : ℕ} (g : cech A' C' n →ₐ[A'] cech A' C' m) (f : C' →ₐ[A'] cech A' C' n) :
    (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g).bot.hom.hom.comp (vAt εbar f) =
      vAt εbar (g.comp f) := by
  rw [thkHom_bot, ← AlgHom.comp_assoc]
  exact congrArg (fun h ↦ h.comp εbar)
    (redMap_comp I (N := nerve (A' := A') hκ C' hC 0) (N' := nerve (A' := A') hκ C' hC n)
      (N'' := nerve (A' := A') hκ C' hC m) f g)

/-- If the chart sends `εbar` to the identity at `D.ubar`, it sends the chart point at the vertex
`f` to the identity at `D.wAt f`. -/
theorem chart_vAt (hε : b.app _ εbar = G.idt D.ubar) {n : ℕ} (f : C' →ₐ[A'] cech A' C' n) :
    b.app _ (vAt εbar f) = G.idt (D.wAt f) := by
  unfold vAt
  have := b.natural (SmallAlg.homMk (redMap I (N := nerve (A' := A') hκ C' hC 0)
    (N' := nerve (A' := A') hκ C' hC n) f)) εbar
  rw [← SmallAlg.homMk_hom (redMap I (N := nerve (A' := A') hκ C' hC 0)
    (N' := nerve (A' := A') hκ C' hC n) f), ← this, hε, G.idt_map]
  rfl

/-- **The module of infinitesimal automorphisms at level `n`**, at the last vertex. -/
abbrev N (n : ℕ) : Type u :=
  K2 (thk I hI (nerve (A' := A') hκ C' hC n)) (vAt εbar (vₗ A' C' n)) sV tV

omit D in
/-- The plain face `j.castSucc` carries the chart point at the last vertex of level `n` to the
chart point at the last vertex of level `n + 1`. -/
theorem hv_plain (n : ℕ) (j : Fin (n + 1)) :
    (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' n j.castSucc)).bot.hom.hom.comp
      (vAt εbar (vₗ A' C' n)) = vAt εbar (vₗ A' C' (n + 1)) := by
  rw [Th_bot_vAt, face_comp_vₗ n j.castSucc (by simp; omega)]

omit D in
/-- The face `0` carries the chart point at the last vertex of level `n` to the chart point at the
last vertex of level `n + 1`. -/
theorem hv_zero (n : ℕ) :
    (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' n 0)).bot.hom.hom.comp
      (vAt εbar (vₗ A' C' n)) = vAt εbar (vₗ A' C' (n + 1)) := by
  rw [Th_bot_vAt, face_comp_vₗ n 0 (Nat.zero_le _)]

omit D in
/-- The codegeneracy carries the chart point at the last vertex of level `n + 1` to the chart
point at the last vertex of level `n`. -/
theorem hv_codeg (n : ℕ) :
    (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (codeg A' C' n)).bot.hom.hom.comp
      (vAt εbar (vₗ A' C' (n + 1))) = vAt εbar (vₗ A' C' n) := by
  rw [Th_bot_vAt, codeg_comp_vₗ]

/-- The plain faces. -/
noncomputable def infFacePlain (n : ℕ) (j : Fin (n + 1)) :
    N (hI := hI) sV tV εbar n →ₗ[A'] N (hI := hI) sV tV εbar (n + 1) :=
  K2Map sV tV _ (hv_plain (hI := hI) εbar n j)

/-- The codegeneracy. -/
noncomputable def infCodeg (n : ℕ) :
    N (hI := hI) sV tV εbar (n + 1) →ₗ[A'] N (hI := hI) sV tV εbar n :=
  K2Map sV tV _ (hv_codeg (hI := hI) εbar n)

/-- The face `i.succ` carries `(1 ⊗ₜ c) * d₀ y` to `(1 ⊗ₜ c) * d₀ (d_i y)`. -/
private theorem face_succ_tmul_mul_face_zero (n : ℕ) (i : Fin (n + 2)) (c : C')
    (y : cech A' C' n) :
    face A' C' (n + 1) i.succ (((1 : cech A' C' n) ⊗ₜ[A'] c : cech A' C' n ⊗[A'] C') *
        face A' C' n 0 y) =
      ((1 : cech A' C' (n + 1)) ⊗ₜ[A'] c : cech A' C' (n + 1) ⊗[A'] C') *
        face A' C' (n + 1) 0 (face A' C' n i y) := by
  rw [map_mul, face_succ_one_tmul]
  congr 1
  exact AlgHom.congr_fun (face_succ_comp_face_zero n i) y

variable [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C']
  (hsV : ∀ (C : SmallAlg A' κ) (v : Q →ₐ[A'] C.obj), G.src (b.app C v) = v.comp sV)
  (htV : ∀ (C : SmallAlg A' κ) (v : Q →ₐ[A'] C.obj), G.tgt (b.app C v) = v.comp tV)
  (ε₀ : Q →ₐ[A'] C') (hε₀ : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp ε₀ = εbar)
  (hε : b.app _ εbar = G.idt D.ubar)

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
include hsV hε in
/-- The chart point at the vertex `f`, composed with `sV`, is `D.wAt f`. -/
theorem vAt_comp_sV {n : ℕ} (f : C' →ₐ[A'] cech A' C' n) :
    (vAt εbar f).comp sV = D.wAt f := by
  rw [← hsV, D.chart_vAt εbar hε, G.src_idt]

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
include htV hε in
/-- The chart point at the vertex `f`, composed with `tV`, is `D.wAt f`. -/
theorem vAt_comp_tV {n : ℕ} (f : C' →ₐ[A'] cech A' C' n) :
    (vAt εbar f).comp tV = D.wAt f := by
  rw [← htV, D.chart_vAt εbar hε, G.tgt_idt]

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
include hε₀ in
/-- The reduction of `f.comp ε₀` is the chart point at the vertex `f`. -/
theorem q_comp_ε₀ {n : ℕ} (f : C' →ₐ[A'] cech A' C' n) :
    (thk I hI (nerve (A' := A') hκ C' hC n)).q.hom.hom.comp (f.comp ε₀) = vAt εbar f := by
  rw [q_comp_lift (n := 0) f ε₀, hε₀]

/-- **The décalage map**: flat base change along the face `0`. -/
noncomputable def infDecal (n : ℕ) :
    C' ⊗[A'] N (hI := hI) sV tV εbar n →ₗ[A']
      N (hI := hI) sV tV εbar (n + 1) :=
  K2BC (isBaseChange_nerve_face_zero hκ C' hC I hI n) sV tV ((vₗ A' C' n).comp ε₀)
    (q_comp_ε₀ εbar ε₀ hε₀ (vₗ A' C' n)) (hv_zero (hI := hI) εbar n)

include D hsV htV hε in
/-- The décalage map is bijective. -/
theorem infDecal_bijective (n : ℕ) :
    Function.Bijective (infDecal sV tV εbar ε₀ hε₀ n) :=
  K2BC_bijective _ sV tV (D.vAt_comp_sV sV εbar hsV hε (vₗ A' C' n))
    (D.vAt_comp_tV tV εbar htV hε (vₗ A' C' n)) _ _ _
    (D.Th_bot_wAt (face A' C' n 0) (vₗ A' C' n) |>.trans (by rw [face_comp_vₗ n 0 (Nat.zero_le _)]))
    (D.vAt_comp_sV sV εbar hsV hε (vₗ A' C' (n + 1)))
    (D.vAt_comp_tV tV εbar htV hε (vₗ A' C' (n + 1)))

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The décalage map sends `c ⊗ₜ E` to `1 ⊗ₜ c` times the postcomposition of `E` with the
face `0`. -/
theorem infDecal_tmul (n : ℕ) (c : C') (E : N (hI := hI) sV tV εbar n) :
    ((infDecal sV tV εbar ε₀ hε₀ n (c ⊗ₜ E) : N (hI := hI) sV tV εbar (n + 1)) :
      Q →ₗ[A'] cech A' C' (n + 1)) =
      ((1 : cech A' C' n) ⊗ₜ[A'] c : cech A' C' n ⊗[A'] C') •
        postcomp (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' n 0)) E.1 :=
  K2BC_tmul _ sV tV _ _ _ c E

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The plain face `j` applies the face `j.castSucc` of the nerve pointwise. -/
theorem infFacePlain_apply (n : ℕ) (j : Fin (n + 1)) (E : N (hI := hI) sV tV εbar n) (x : Q) :
    (infFacePlain sV tV εbar n j E : Q →ₗ[A'] cech A' C' (n + 1)) x =
      face A' C' n j.castSucc (E.1 x) := rfl

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The décalage map sends `c ⊗ₜ E` to `x ↦ (1 ⊗ₜ c) * face 0 (E x)`. -/
theorem infDecal_tmul_apply (n : ℕ) (c : C') (E : N (hI := hI) sV tV εbar n) (x : Q) :
    ((infDecal sV tV εbar ε₀ hε₀ n (c ⊗ₜ E) : N (hI := hI) sV tV εbar (n + 1)) :
      Q →ₗ[A'] cech A' C' (n + 1)) x =
      ((1 : cech A' C' n) ⊗ₜ[A'] c : cech A' C' n ⊗[A'] C') * face A' C' n 0 (E.1 x) := by
  rw [infDecal_tmul]
  rfl

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The décalage map carries the plain face `j` to the plain face `j.succ`. -/
theorem infFacePlain_decal (n : ℕ) (j : Fin (n + 1)) (c : C') (E : N (hI := hI) sV tV εbar n) :
    infFacePlain sV tV εbar (n + 1) j.succ (infDecal sV tV εbar ε₀ hε₀ n (c ⊗ₜ E)) =
      infDecal sV tV εbar ε₀ hε₀ (n + 1) (c ⊗ₜ infFacePlain sV tV εbar n j E) := by
  apply Subtype.ext
  ext x
  rw [infFacePlain_apply, infDecal_tmul_apply, infDecal_tmul_apply, infFacePlain_apply,
    ← Fin.succ_castSucc]
  exact face_succ_tmul_mul_face_zero n j.castSucc c _

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The codegeneracy applies the codegeneracy of the nerve pointwise. -/
theorem infCodeg_apply (n : ℕ) (E : N (hI := hI) sV tV εbar (n + 1)) (x : Q) :
    (infCodeg sV tV εbar n E : Q →ₗ[A'] cech A' C' n) x = codeg A' C' n (E.1 x) := rfl

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The codegeneracy is a left inverse of the plain face `1`. -/
theorem infCodeg_facePlain_one (n : ℕ) (E : N (hI := hI) sV tV εbar (n + 1)) :
    infCodeg sV tV εbar (n + 1) (infFacePlain sV tV εbar (n + 1) 1 E) = E :=
  Subtype.ext <| LinearMap.ext fun _ ↦ AlgHom.congr_fun (codeg_comp_face_one (n + 1)) _

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The codegeneracy commutes with the plain faces `j.succ.succ` and `j.succ`. -/
theorem infCodeg_facePlain_succ_succ (n : ℕ) (j : Fin n) (E : N (hI := hI) sV tV εbar (n + 1)) :
    infCodeg sV tV εbar (n + 1) (infFacePlain sV tV εbar (n + 1) j.succ.succ E) =
      infFacePlain sV tV εbar n j.succ (infCodeg sV tV εbar n E) := by
  apply Subtype.ext
  ext x
  rw [infCodeg_apply, infFacePlain_apply, infFacePlain_apply, infCodeg_apply]
  have e1 : (j.succ.succ : Fin (n + 2)).castSucc = (j.castSucc).succ.succ := by ext; simp
  have e2 : (j.succ : Fin (n + 1)).castSucc = (j.castSucc).succ := by ext; simp
  rw [e1, e2]
  exact AlgHom.congr_fun (codeg_comp_face_succ_succ n j.castSucc) _

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The last face carries the chart point at the last vertex of level `n` to the chart point at
the second-to-last vertex of level `n + 1`. -/
theorem hv_last (n : ℕ) :
    (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI)
        (face A' C' n (Fin.last (n + 1)))).bot.hom.hom.comp
      (vAt εbar (vₗ A' C' n)) = vAt εbar ((GroupoidLift.κ A' C' n).comp (v₀ A' C' 1)) := by
  rw [Th_bot_vAt, face_last_comp_vₗ]

/-! ### The twisted face: conjugation by the lifted descent arrow -/

section Twisted

variable (hb : b.IsFormallyEtale) {u : P →ₐ[A'] C'}
  (hu : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp u = D.ubar)
  {r : G.arr.obj (nerve (A' := A') hκ C' hC 1)} (hrs : G.src r = (v₀ A' C' 1).comp u)
  (hrt : G.tgt r = (vₗ A' C' 1).comp u)
  (hrq : G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 1)).q r = D.rbar)

/-- The lifted descent arrow on the last two vertices of level `n + 1`. -/
abbrev rAt (r : G.arr.obj (nerve (A' := A') hκ C' hC 1)) (n : ℕ) :
    G.arr.obj (nerve (A' := A') hκ C' hC (n + 1)) :=
  G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (GroupoidLift.κ A' C' n)).top r

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
include hrs in
/-- The source of `rAt r n` is the lift `u` at the second-to-last vertex of level `n + 1`. -/
theorem src_rAt (n : ℕ) :
    G.src (rAt (hI := hI) r n) = ((GroupoidLift.κ A' C' n).comp (v₀ A' C' 1)).comp u := by
  rw [G.src_map, hrs]
  rfl

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
include hrt in
/-- The target of `rAt r n` is the lift `u` at the last vertex of level `n + 1`. -/
theorem tgt_rAt (n : ℕ) : G.tgt (rAt (hI := hI) r n) = (vₗ A' C' (n + 1)).comp u := by
  rw [G.tgt_map, hrt, ← κ_comp_vₗ n]
  rfl

/-- **The twisted last face**: the face of the nerve followed by conjugation by the lifted
descent arrow. -/
noncomputable def infFaceLast (n : ℕ) :
    N (hI := hI) sV tV εbar n →ₗ[A'] N (hI := hI) sV tV εbar (n + 1) :=
  (conjLin b hb sV tV hsV htV (D.chart_vAt εbar hε _) (D.chart_vAt εbar hε (vₗ A' C' (n + 1)))
    (D.q_comp_at hu _) (D.q_comp_at hu (vₗ A' C' (n + 1))) (src_rAt (I := I) (hI := hI) hrs n)
    (tgt_rAt (I := I) (hI := hI) hrt n)
    hκ).comp (K2Map sV tV _ (hv_last (hI := hI) εbar n))

/-- The faces. -/
noncomputable def infFace (n : ℕ) (i : Fin (n + 2)) :
    N (hI := hI) sV tV εbar n →ₗ[A'] N (hI := hI) sV tV εbar (n + 1) :=
  Fin.lastCases (motive := fun _ ↦ N (hI := hI) sV tV εbar n →ₗ[A'] N (hI := hI) sV tV εbar (n + 1))
    (D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt n) (infFacePlain sV tV εbar n) i

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- Conjugation at a pair of vertices of level `m`, by an arrow between the lifted points. -/
noncomputable abbrev conjAt {m : ℕ} {f f' : C' →ₐ[A'] cech A' C' m}
    {r' : G.arr.obj (nerve (A' := A') hκ C' hC m)} (hs : G.src r' = f.comp u)
    (ht : G.tgt r' = f'.comp u) {E : Q →ₗ[A'] cech A' C' m}
    (hE : E ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV) :
    Q →ₗ[A'] cech A' C' m :=
  conjK b hb sV tV hsV htV (D.chart_vAt εbar hε f) (D.chart_vAt εbar hε f')
    (D.q_comp_at hu f) (D.q_comp_at hu f') hs ht hE

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- Conjugation at vertices depends only on the vertices, the arrow and the derivation. -/
theorem conjAt_congr {m : ℕ} {f f' f₁ f₁' : C' →ₐ[A'] cech A' C' m}
    {r' r₁ : G.arr.obj (nerve (A' := A') hκ C' hC m)} (hs : G.src r' = f.comp u)
    (ht : G.tgt r' = f'.comp u) (hs₁ : G.src r₁ = f₁.comp u) (ht₁ : G.tgt r₁ = f₁'.comp u)
    {E E₁ : Q →ₗ[A'] cech A' C' m}
    (hE : E ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV)
    (hE₁ : E₁ ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f₁) sV tV)
    (hf : f = f₁) (hf' : f' = f₁') (hr : r' = r₁) (h : E = E₁) :
    D.conjAt sV tV εbar hsV htV hε hb hu hs ht hE =
      D.conjAt sV tV εbar hsV htV hε hb hu hs₁ ht₁ hE₁ := by
  subst hf hf' hr h
  rfl

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- Conjugation at vertices is natural along the maps of the nerve. -/
theorem postcomp_conjAt {m k : ℕ} (g : cech A' C' m →ₐ[A'] cech A' C' k)
    {f f' : C' →ₐ[A'] cech A' C' m} {r' : G.arr.obj (nerve (A' := A') hκ C' hC m)}
    (hs : G.src r' = f.comp u) (ht : G.tgt r' = f'.comp u) {E : Q →ₗ[A'] cech A' C' m}
    (hE : E ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV)
    {g₁ g₁' : C' →ₐ[A'] cech A' C' k} (hg₁ : g.comp f = g₁) (hg₁' : g.comp f' = g₁')
    {r₁ : G.arr.obj (nerve (A' := A') hκ C' hC k)}
    (hr₁ : G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g).top r' = r₁)
    (hs₁ : G.src r₁ = g₁.comp u) (ht₁ : G.tgt r₁ = g₁'.comp u) {E₁ : Q →ₗ[A'] cech A' C' k}
    (hE₁ : E₁ ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC k)) (vAt εbar g₁) sV tV)
    (hEE : postcomp (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g) E = E₁) :
    postcomp (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g)
        (D.conjAt sV tV εbar hsV htV hε hb hu hs ht hE) =
      D.conjAt sV tV εbar hsV htV hε hb hu hs₁ ht₁ hE₁ :=
  postcomp_conjK_eq b hb sV tV hsV htV _ _ _ _ _ _ _ _ _
    ((Th_bot_vAt εbar g f).trans (congrArg (vAt εbar) hg₁))
    ((Th_bot_vAt εbar g f').trans (congrArg (vAt εbar) hg₁')) hr₁ _ _ _ _ _ _ hEE

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- Conjugation at vertices is linear over `cech A' C' m`. -/
theorem conjAt_smul {m : ℕ} {f f' : C' →ₐ[A'] cech A' C' m}
    {r' : G.arr.obj (nerve (A' := A') hκ C' hC m)} (hs : G.src r' = f.comp u)
    (ht : G.tgt r' = f'.comp u) (c : cech A' C' m) {E : Q →ₗ[A'] cech A' C' m}
    (hE : E ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV) :
    D.conjAt sV tV εbar hsV htV hε hb hu hs ht (Submodule.smul_mem _ c hE) =
      c • D.conjAt sV tV εbar hsV htV hε hb hu hs ht hE :=
  conjK_smul b hb sV tV hsV htV _ _ _ _ hs ht hκ c hE

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- Conjugation by an arrow reducing to an identity is trivial. -/
theorem conjAt_of_red {m : ℕ} {f : C' →ₐ[A'] cech A' C' m}
    {r' : G.arr.obj (nerve (A' := A') hκ C' hC m)} (hs : G.src r' = f.comp u)
    (ht : G.tgt r' = f.comp u)
    (hq : G.arr.map (thk I hI (nerve (A' := A') hκ C' hC m)).q r' = G.idt (D.wAt f))
    {E : Q →ₗ[A'] cech A' C' m}
    (hE : E ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV) :
    D.conjAt sV tV εbar hsV htV hε hb hu hs ht hE = E := by
  obtain ⟨F, hF, rfl⟩ := exists_infOf_eq b hb sV tV hsV htV (D.chart_vAt εbar hε f)
    (D.q_comp_at hu f) hs ht hq
  exact conjK_infOf b hb sV tV hsV htV hκ (D.chart_vAt εbar hε f) (D.q_comp_at hu f) hF hE

omit D [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- Transporting an arrow along the tops of the thickening maps of `f` and then `g` is transport
along the top of the thickening map of `g.comp f`. -/
theorem map_top_Th_Th {n m k : ℕ} (g : cech A' C' m →ₐ[A'] cech A' C' k)
    (f : cech A' C' n →ₐ[A'] cech A' C' m) (r' : G.arr.obj (nerve (A' := A') hκ C' hC n)) :
    G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g).top
      (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) f).top r') =
      G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (g.comp f)).top r' := by
  rw [G.map_map]
  rfl

omit D [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- Reducing an arrow transported along the top of the thickening map of `g` is transporting its
reduction along the bottom. -/
theorem map_q_map_top {n m : ℕ} (g : cech A' C' n →ₐ[A'] cech A' C' m)
    (r' : G.arr.obj (nerve (A' := A') hκ C' hC n)) :
    G.arr.map (thk I hI (nerve (A' := A') hκ C' hC m)).q
      (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g).top r') =
      G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g).bot
        (G.arr.map (thk I hI (nerve (A' := A') hκ C' hC n)).q r') := by
  rw [G.map_map, G.map_map, (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g).w]

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The twisted last face is conjugation by `rAt r n` of the postcomposition with the last
face. -/
theorem infFaceLast_val (n : ℕ) (E : N (hI := hI) sV tV εbar n) :
    (D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt n E : Q →ₗ[A'] cech A' C' (n + 1)) =
      D.conjAt sV tV εbar hsV htV hε hb hu (src_rAt (I := I) (hI := hI) hrs n)
        (tgt_rAt (I := I) (hI := hI) hrt n) (postcomp_mem_K2 sV tV _ (hv_last εbar n) E.2) :=
  rfl

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
omit D in
/-- The codegeneracy is postcomposition with the codegeneracy of the nerve. -/
theorem infCodeg_val (n : ℕ) (E : N (hI := hI) sV tV εbar (n + 1)) :
    (infCodeg sV tV εbar n E : Q →ₗ[A'] cech A' C' n) =
      postcomp (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (codeg A' C' n)) E.1 :=
  rfl

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The décalage carries the twisted last face to the twisted last face. -/
theorem infFaceLast_decal (n : ℕ) (c : C') (E : N (hI := hI) sV tV εbar n) :
    D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt (n + 1)
        (infDecal sV tV εbar ε₀ hε₀ n (c ⊗ₜ E)) =
      infDecal sV tV εbar ε₀ hε₀ (n + 1)
        (c ⊗ₜ D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt n E) := by
  apply Subtype.ext
  conv_lhs => rw [infFaceLast_val]
  conv_rhs => rw [infDecal_tmul, infFaceLast_val]
  have hf : (face A' C' (n + 1) 0).comp ((GroupoidLift.κ A' C' n).comp (v₀ A' C' 1)) =
      (GroupoidLift.κ A' C' (n + 1)).comp (v₀ A' C' 1) := by
    rw [← AlgHom.comp_assoc, face_comp_κ n 0 (Nat.zero_le _)]
  rw [D.postcomp_conjAt sV tV εbar hsV htV hε hb hu (face A' C' (n + 1) 0) _ _ _ hf
      (face_comp_vₗ (n + 1) 0 (Nat.zero_le _))
      (by rw [rAt, rAt, map_top_Th_Th, face_comp_κ n 0 (Nat.zero_le _)])
      (src_rAt (I := I) (hI := hI) hrs (n + 1)) (tgt_rAt (I := I) (hI := hI) hrt (n + 1))
      (postcomp_mem_K2 sV tV _ ((Th_bot_vAt εbar _ _).trans (congrArg (vAt εbar) hf))
        (postcomp_mem_K2 sV tV _ (hv_last εbar n) E.2)) rfl]
  refine Eq.trans ?_ (D.conjAt_smul sV tV εbar hsV htV hε hb hu (m := n + 2) _ _
    ((1 : cech A' C' (n + 1)) ⊗ₜ[A'] c : cech A' C' (n + 1) ⊗[A'] C') _)
  refine D.conjAt_congr sV tV εbar hsV htV hε hb hu _ _ _ _ _ _ rfl rfl rfl ?_
  rw [infDecal_tmul]
  refine LinearMap.ext fun x ↦ ?_
  change face A' C' (n + 1) (Fin.last (n + 2)) (((1 : cech A' C' n) ⊗ₜ[A'] c :
      cech A' C' n ⊗[A'] C') * face A' C' n 0 (E.1 x)) =
    ((1 : cech A' C' (n + 1)) ⊗ₜ[A'] c : cech A' C' (n + 1) ⊗[A'] C') *
      face A' C' (n + 1) 0 (face A' C' n (Fin.last (n + 1)) (E.1 x))
  exact face_succ_tmul_mul_face_zero n (Fin.last (n + 1)) c _

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The codegeneracy commutes with the twisted last face. -/
theorem infCodeg_faceLast_succ (n : ℕ) (E : N (hI := hI) sV tV εbar (n + 1)) :
    infCodeg sV tV εbar (n + 1) (D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt (n + 1) E) =
      D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt n (infCodeg sV tV εbar n E) := by
  apply Subtype.ext
  conv_lhs => rw [infCodeg_val, infFaceLast_val]
  conv_rhs => rw [infFaceLast_val]
  have hf : (codeg A' C' (n + 1)).comp ((GroupoidLift.κ A' C' (n + 1)).comp (v₀ A' C' 1)) =
      (GroupoidLift.κ A' C' n).comp (v₀ A' C' 1) := by
    rw [← AlgHom.comp_assoc, codeg_comp_κ]
  have hring : (codeg A' C' (n + 1)).comp (face A' C' (n + 1) (Fin.last (n + 2))) =
      (face A' C' n (Fin.last (n + 1))).comp (codeg A' C' n) := by
    have := codeg_comp_face_succ_succ (A' := A') (C' := C') n (Fin.last n)
    rwa [Fin.succ_last, Fin.succ_last] at this
  exact D.postcomp_conjAt sV tV εbar hsV htV hε hb hu (codeg A' C' (n + 1)) _ _ _ hf
    (codeg_comp_vₗ (n + 1)) (by rw [rAt, rAt, map_top_Th_Th, codeg_comp_κ]) _ _ _
    (LinearMap.ext fun x ↦ AlgHom.congr_fun hring _)

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
include hrq in
/-- The identity `σ₀ d₁ = id` at level `0`, where `d₁` is the twisted face: the conjugating
arrow restricts to an infinitesimal automorphism along the diagonal. -/
theorem infCodeg_faceLast_zero (E : N (hI := hI) sV tV εbar 0) :
    infCodeg sV tV εbar 0 (D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt 0 E) = E := by
  apply Subtype.ext
  conv_lhs => rw [infCodeg_val, infFaceLast_val]
  have h1 : (codeg A' C' 0).comp (face A' C' 0 (Fin.last (0 + 1))) = AlgHom.id A' _ :=
    codeg_comp_face_one 0
  have hf : (codeg A' C' 0).comp ((GroupoidLift.κ A' C' 0).comp (v₀ A' C' 1)) = vₗ A' C' 0 := by
    rw [← face_last_comp_vₗ 0, ← AlgHom.comp_assoc, h1, AlgHom.id_comp]
  have hs : G.src (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (codeg A' C' 0)).top
      (rAt (hI := hI) r 0)) = (vₗ A' C' 0).comp u := by
    rw [G.src_map, src_rAt (I := I) (hI := hI) hrs 0, ← hf]
    rfl
  have ht : G.tgt (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (codeg A' C' 0)).top
      (rAt (hI := hI) r 0)) = (vₗ A' C' 0).comp u := by
    rw [G.tgt_map, tgt_rAt (I := I) (hI := hI) hrt 0, ← codeg_comp_vₗ 0]
    rfl
  have hq : G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 0)).q
      (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (codeg A' C' 0)).top
        (rAt (hI := hI) r 0)) = G.idt (D.wAt (vₗ A' C' 0)) := by
    rw [map_q_map_top, rAt, map_q_map_top, hrq, map_Th_map_Th]
    exact D.norm_rbar.trans (congrArg G.idt D.w_zero.symm)
  rw [D.postcomp_conjAt sV tV εbar hsV htV hε hb hu (codeg A' C' 0) _ _ _ hf (codeg_comp_vₗ 0)
    rfl hs ht E.2
    (LinearMap.ext fun x ↦ AlgHom.congr_fun h1 _)]
  exact D.conjAt_of_red sV tV εbar hsV htV hε hb hu hs ht hq E.2

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The last face is the twisted last face. -/
theorem infFace_last (n : ℕ) :
    D.infFace sV tV εbar hsV htV hε hb hu hrs hrt n (Fin.last (n + 1)) =
      D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt n := by
  rw [infFace, Fin.lastCases_last]

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The face `j.castSucc` is the plain face `j`. -/
theorem infFace_castSucc (n : ℕ) (j : Fin (n + 1)) :
    D.infFace sV tV εbar hsV htV hε hb hu hrs hrt n j.castSucc = infFacePlain sV tV εbar n j := by
  rw [infFace, Fin.lastCases_castSucc]

include hrq in
/-- **The modules of infinitesimal automorphisms along the nerve form a décalage**: plain faces
by the maps of the nerve, the last face twisted by conjugation with the lifted descent arrow,
and the décalage maps by flat base change along the face `0`. -/
noncomputable def infDecalage : Stacks.Decalage A' C' (N (hI := hI) sV tV εbar) where
  face := D.infFace sV tV εbar hsV htV hε hb hu hrs hrt
  codeg := infCodeg sV tV εbar
  decal := infDecal sV tV εbar ε₀ hε₀
  decal_bijective := D.infDecal_bijective sV tV εbar hsV htV ε₀ hε₀ hε
  face_succ_decal n i x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c m =>
      rw [LinearMap.lTensor_tmul]
      cases i using Fin.lastCases with
      | last =>
        rw [Fin.succ_last, infFace_last, infFace_last]
        exact D.infFaceLast_decal sV tV εbar hsV htV ε₀ hε₀ hε hb hu hrs hrt n c m
      | cast j =>
        rw [Fin.succ_castSucc, infFace_castSucc, infFace_castSucc]
        exact infFacePlain_decal sV tV εbar ε₀ hε₀ n j c m
  codeg_face_one n m := by
    cases n with
    | zero =>
      rw [show (1 : Fin 2) = Fin.last 1 from rfl, infFace_last]
      exact D.infCodeg_faceLast_zero sV tV εbar hsV htV hε hb hu hrs hrt hrq m
    | succ n =>
      rw [show (1 : Fin (n + 3)) = (1 : Fin (n + 2)).castSucc from rfl, infFace_castSucc]
      exact infCodeg_facePlain_one sV tV εbar n m
  codeg_face_succ_succ n i m := by
    cases i using Fin.lastCases with
    | last =>
      rw [Fin.succ_last, Fin.succ_last, infFace_last, infFace_last]
      exact D.infCodeg_faceLast_succ sV tV εbar hsV htV hε hb hu hrs hrt n m
    | cast j =>
      have e1 : j.castSucc.succ.succ = (j.succ.succ : Fin (n + 2)).castSucc := by ext; simp
      have e2 : (j.castSucc.succ : Fin (n + 2)) = (j.succ : Fin (n + 1)).castSucc := by
        ext; simp
      rw [e1, e2, infFace_castSucc, infFace_castSucc]
      exact infCodeg_facePlain_succ_succ sV tV εbar n j m

end Twisted

end NerveDatum

end AlgebraicGeometry.Stack.GroupoidLift

end
