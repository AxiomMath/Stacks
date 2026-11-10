module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.InfAlg
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.Calculus

/-!
# Infinitesimal automorphisms near the identities

Let `G` be a groupoid in presheaves on the `κ`-small `A'`-algebras with object presheaf
`Hom(P, -)`, and let `b : Hom(Q, -) → G.arr` be a formally étale chart of its arrows, with source
and target `sV, tV : P → Q`. Fix a square-zero thickening `e : C' → C`, a point `w` of `P` over
`C` whose identity arrow is `b(v)`, and a lift `ℓ` of `w` over `C'`.

The *infinitesimal automorphisms* of `ℓ` are the arrows from `ℓ` to `ℓ` over `C'` that reduce to
the identity of `w`. They are exactly the arrows `b(vt + E)` where `vt` is the lift of `v` with
`b(vt) = id ℓ` and `E` is a derivation of `Q` along `v` killed by `sV` and by `tV`
(`infOf`, `infOf_surj`, `infOf_injective`), and composition of such arrows is addition of the
derivations (`comp_infOf`).

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.comp_infOf`: composition is addition.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {A' : Type u} [CommRing A'] {κ : Cardinal.{u}} {P : Type u} [CommRing P] [Algebra A' P]
  {G : Groupoid A' κ P} {Q : Type u} [CommRing Q] [Algebra A' Q]
  {C' C : SmallAlg A' κ} (e : SqZero C' C)

/-- Composition of arrows is congruent in both arguments, whatever the composability proofs. -/
theorem Groupoid.comp_eq' (G : Groupoid A' κ P) {C : SmallAlg A' κ} {g g' f f' : G.arr.obj C}
    (hg : g = g') (hf : f = f') (h : G.src g = G.tgt f) (h' : G.src g' = G.tgt f') :
    G.comp g f h = G.comp g' f' h' := by
  subst hg hf
  rfl

/-- The derivations of `Q` along `v` killed by `sV` and `tV`. -/
def K2 (v : Q →ₐ[A'] C.obj) (sV tV : P →ₐ[A'] Q) : Submodule C'.obj (Q →ₗ[A'] C'.obj) :=
  K e v sV ⊓ LinearMap.ker (precomp C' tV)

variable {e} (b : Chart G.arr Q) (hb : b.IsFormallyEtale) (sV tV : P →ₐ[A'] Q)
  (hsV : ∀ (C : SmallAlg A' κ) (v : Q →ₐ[A'] C.obj), G.src (b.app C v) = v.comp sV)
  (htV : ∀ (C : SmallAlg A' κ) (v : Q →ₐ[A'] C.obj), G.tgt (b.app C v) = v.comp tV)

include hb in
/-- If `b(v)` is the identity of `w` and `ℓ` lifts `w` over `C'`, then `v` has a lift `vt` over
`C'` with `b(vt)` the identity of `ℓ`. -/
theorem exists_infBase {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w) :
    ∃ vt : Q →ₐ[A'] C'.obj, e.q.hom.hom.comp vt = v ∧ b.app C' vt = G.idt ℓ :=
  (hb C' C e.q e.surj e.sq v (G.idt ℓ) (by rw [G.idt_map, hℓ, hv])).exists

/-- The lift of `v` whose image under the chart is the identity of `ℓ`. -/
noncomputable def infBase {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w) : Q →ₐ[A'] C'.obj :=
  (exists_infBase b hb hv hℓ).choose

/-- The reduction of `infBase` along `e` is `v`. -/
theorem infBase_red {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w) :
    e.q.hom.hom.comp (infBase b hb hv hℓ) = v :=
  (exists_infBase b hb hv hℓ).choose_spec.1

/-- The chart sends `infBase` to the identity of `ℓ`. -/
theorem app_infBase {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w) :
    b.app C' (infBase b hb hv hℓ) = G.idt ℓ :=
  (exists_infBase b hb hv hℓ).choose_spec.2

include hsV in
/-- The composite of `infBase` with `sV` is `ℓ`. -/
theorem infBase_comp_sV {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w) :
    (infBase b hb hv hℓ).comp sV = ℓ := by
  rw [← hsV, app_infBase, G.src_idt]

include htV in
/-- The composite of `infBase` with `tV` is `ℓ`. -/
theorem infBase_comp_tV {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w) :
    (infBase b hb hv hℓ).comp tV = ℓ := by
  rw [← htV, app_infBase, G.tgt_idt]

/-- The lift `vt + E` of `v`. -/
noncomputable def infLift {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w) {E : Q →ₗ[A'] C'.obj}
    (hE : E ∈ K2 e v sV tV) : Q →ₐ[A'] C'.obj :=
  addLift E hE.1.1 (infBase b hb hv hℓ) (infBase_red b hb hv hℓ)

/-- **The infinitesimal automorphism of a derivation**, `b(vt + E)`. -/
noncomputable def infOf {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w) {E : Q →ₗ[A'] C'.obj}
    (hE : E ∈ K2 e v sV tV) : G.arr.obj C' :=
  b.app C' (infLift b hb sV tV hv hℓ hE)

/-- A derivation in `K2 e v sV tV` vanishes on the image of `sV`. -/
theorem K2_sV {v : Q →ₐ[A'] C.obj} {E : Q →ₗ[A'] C'.obj} (hE : E ∈ K2 e v sV tV) (x : P) :
    E (sV x) = 0 :=
  congrArg (fun f : P →ₗ[A'] C'.obj ↦ f x) (LinearMap.mem_ker.mp hE.1.2)

/-- A derivation in `K2 e v sV tV` vanishes on the image of `tV`. -/
theorem K2_tV {v : Q →ₐ[A'] C.obj} {E : Q →ₗ[A'] C'.obj} (hE : E ∈ K2 e v sV tV) (x : P) :
    E (tV x) = 0 :=
  congrArg (fun f : P →ₗ[A'] C'.obj ↦ f x) (LinearMap.mem_ker.mp hE.2)

include hsV in
/-- The composite of the lift `vt + E` with `sV` is `ℓ`. -/
theorem infLift_comp_sV {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w) {E : Q →ₗ[A'] C'.obj}
    (hE : E ∈ K2 e v sV tV) : (infLift b hb sV tV hv hℓ hE).comp sV = ℓ := by
  ext x
  change infBase b hb hv hℓ (sV x) + E (sV x) = ℓ x
  rw [K2_sV sV tV hE, add_zero, ← AlgHom.comp_apply, infBase_comp_sV b hb sV hsV]

include htV in
/-- The composite of the lift `vt + E` with `tV` is `ℓ`. -/
theorem infLift_comp_tV {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w) {E : Q →ₗ[A'] C'.obj}
    (hE : E ∈ K2 e v sV tV) : (infLift b hb sV tV hv hℓ hE).comp tV = ℓ := by
  ext x
  change infBase b hb hv hℓ (tV x) + E (tV x) = ℓ x
  rw [K2_tV sV tV hE, add_zero, ← AlgHom.comp_apply, infBase_comp_tV b hb tV htV]

include hsV in
/-- The source of `infOf E` is `ℓ`. -/
theorem src_infOf {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w) {E : Q →ₗ[A'] C'.obj}
    (hE : E ∈ K2 e v sV tV) : G.src (infOf b hb sV tV hv hℓ hE) = ℓ := by
  rw [infOf, hsV, infLift_comp_sV b hb sV tV hsV]

include htV in
/-- The target of `infOf E` is `ℓ`. -/
theorem tgt_infOf {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w) {E : Q →ₗ[A'] C'.obj}
    (hE : E ∈ K2 e v sV tV) : G.tgt (infOf b hb sV tV hv hℓ hE) = ℓ := by
  rw [infOf, htV, infLift_comp_tV b hb sV tV htV]

/-- The reduction of `infOf E` along `e` is the identity of `w`. -/
theorem map_infOf {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w) {E : Q →ₗ[A'] C'.obj}
    (hE : E ∈ K2 e v sV tV) : G.arr.map e.q (infOf b hb sV tV hv hℓ hE) = G.idt w := by
  rw [infOf, b.natural]
  change b.app C (e.q.hom.hom.comp (addLift E hE.1.1 _ _)) = _
  rw [addLift_reduce, hv]

/-- The infinitesimal automorphism of the zero derivation is the identity of `ℓ`. -/
theorem infOf_zero {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w) :
    infOf b hb sV tV hv hℓ (zero_mem (K2 e v sV tV)) = G.idt ℓ := by
  rw [← app_infBase b hb hv hℓ]
  exact congrArg (b.app C') (AlgHom.ext fun x ↦ by simp [infLift])

include hb in
/-- **Uniqueness of chart preimages**, the formal étaleness of the chart along `e`. -/
theorem chart_unique {v : Q →ₐ[A'] C.obj} {z : G.arr.obj C'} (hz : G.arr.map e.q z = b.app C v)
    {vt₁ vt₂ : Q →ₐ[A'] C'.obj} (h₁ : e.q.hom.hom.comp vt₁ = v) (h₁' : b.app C' vt₁ = z)
    (h₂ : e.q.hom.hom.comp vt₂ = v) (h₂' : b.app C' vt₂ = z) : vt₁ = vt₂ :=
  (hb C' C e.q e.surj e.sq v z hz).unique ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩

/-- The lift `vt + E` and `vt` have the same reduction along `e`. -/
theorem infLift_red {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w) {E : Q →ₗ[A'] C'.obj}
    (hE : E ∈ K2 e v sV tV) :
    e.q.hom.hom.comp (infLift b hb sV tV hv hℓ hE) = e.q.hom.hom.comp (infBase b hb hv hℓ) := by
  rw [infLift, addLift_reduce, infBase_red]

include hsV htV in
/-- **Every infinitesimal automorphism comes from a derivation.** -/
theorem exists_infOf_eq {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w) {g : G.arr.obj C'}
    (hs : G.src g = ℓ) (ht : G.tgt g = ℓ) (hg : G.arr.map e.q g = G.idt w) :
    ∃ (E : Q →ₗ[A'] C'.obj) (hE : E ∈ K2 e v sV tV), infOf b hb sV tV hv hℓ hE = g := by
  obtain ⟨vg, hvg, hbvg⟩ := (hb C' C e.q e.surj e.sq v g (hg.trans hv.symm)).exists
  have hvt := infBase_red b hb hv hℓ
  have hD := sub_mem_Der hvt hvg
  have hker : ∀ u : P →ₐ[A'] Q, vg.comp u = (infBase b hb hv hℓ).comp u →
      precomp C' u (vg.toLinearMap - (infBase b hb hv hℓ).toLinearMap) = 0 := fun u hu ↦ by
    ext x
    exact sub_eq_zero.mpr (AlgHom.congr_fun hu x)
  refine ⟨_, ⟨⟨hD, LinearMap.mem_ker.mpr (hker sV ?_)⟩, LinearMap.mem_ker.mpr (hker tV ?_)⟩, ?_⟩
  · rw [infBase_comp_sV b hb sV hsV, ← hsV, hbvg, hs]
  · rw [infBase_comp_tV b hb tV htV, ← htV, hbvg, ht]
  refine Eq.trans ?_ hbvg
  exact congrArg (b.app C') (AlgHom.ext fun x ↦ by simp [infLift])

/-- **A derivation is determined by its infinitesimal automorphism.** -/
theorem infOf_injective {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w) {E₁ E₂ : Q →ₗ[A'] C'.obj}
    (hE₁ : E₁ ∈ K2 e v sV tV) (hE₂ : E₂ ∈ K2 e v sV tV)
    (h : infOf b hb sV tV hv hℓ hE₁ = infOf b hb sV tV hv hℓ hE₂) : E₁ = E₂ := by
  have hvt := infBase_red b hb hv hℓ
  have hz : G.arr.map e.q (infOf b hb sV tV hv hℓ hE₁) = b.app C v := by rw [map_infOf, hv]
  have := chart_unique b hb hz ((infLift_red b hb sV tV hv hℓ hE₁).trans hvt) rfl
    ((infLift_red b hb sV tV hv hℓ hE₂).trans hvt) h.symm
  ext x
  simpa [infLift] using AlgHom.congr_fun this x

/-- Each projection of the algebra of triples, followed by the reduction `e.q`, is the reduction
of the algebra of triples. -/
theorem fib3Proj_red (hκ : Cardinal.aleph0 < κ) (k : Fin 3) :
    fib3Proj e hκ k ≫ e.q = (fib3Sq e hκ).q := by
  ext x
  fin_cases k
  · rfl
  · exact x.2.1.symm
  · exact x.2.2.symm

/-- Each projection of the algebra of triples sends a lift of `v` through the reduction of the
algebra of triples to a lift of `v` through `e`. -/
private theorem comp_fib3Proj_red (hκ : Cardinal.aleph0 < κ) {v : Q →ₐ[A'] C.obj}
    {H : Q →ₐ[A'] (fib3 e hκ).obj} (hH : (fib3Sq e hκ).q.hom.hom.comp H = v) (k : Fin 3) :
    e.q.hom.hom.comp ((fib3Proj e hκ k).hom.hom.comp H) = v := by
  rw [← AlgHom.comp_assoc]
  change ((fib3Proj e hκ k) ≫ e.q).hom.hom.comp H = v
  rw [fib3Proj_red, hH]

/-- A lift of `v` whose chart image is `infOf E` is the lift `vt + E`. -/
private theorem eq_infLift_of_app_eq_infOf {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj}
    (hv : b.app C v = G.idt w) {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w)
    {E : Q →ₗ[A'] C'.obj} (hE : E ∈ K2 e v sV tV) {vt' : Q →ₐ[A'] C'.obj}
    (hred : e.q.hom.hom.comp vt' = v) (h : b.app C' vt' = infOf b hb sV tV hv hℓ hE) :
    vt' = infLift b hb sV tV hv hℓ hE :=
  chart_unique b hb ((map_infOf b hb sV tV hv hℓ hE).trans hv.symm) hred h
    ((infLift_red b hb sV tV hv hℓ hE).trans (infBase_red b hb hv hℓ)) rfl

include hsV htV in
/-- **Composition of infinitesimal automorphisms is addition of derivations.** -/
theorem comp_infOf (hκ : Cardinal.aleph0 < κ) {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj}
    (hv : b.app C v = G.idt w) {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w)
    {E₁ E₂ : Q →ₗ[A'] C'.obj} (hE₁ : E₁ ∈ K2 e v sV tV) (hE₂ : E₂ ∈ K2 e v sV tV) :
    G.comp (infOf b hb sV tV hv hℓ hE₁) (infOf b hb sV tV hv hℓ hE₂)
      (by rw [src_infOf b hb sV tV hsV, tgt_infOf b hb sV tV htV]) =
      infOf b hb sV tV hv hℓ (add_mem hE₁ hE₂) := by
  set vt := infBase b hb hv hℓ with hvtdef
  have hvt : e.q.hom.hom.comp vt = v := infBase_red b hb hv hℓ
  set f₁ := infLift b hb sV tV hv hℓ hE₁
  set f₂ := infLift b hb sV tV hv hℓ hE₂
  have h₁ : e.q.hom.hom.comp f₁ = e.q.hom.hom.comp vt := infLift_red b hb sV tV hv hℓ hE₁
  have h₂ : e.q.hom.hom.comp f₂ = e.q.hom.hom.comp vt := infLift_red b hb sV tV hv hℓ hE₂
  let L₁ := fib3Lift e hκ vt f₁ vt h₁ rfl
  let L₂ := fib3Lift e hκ vt vt f₂ rfl h₂
  have hs₀ : ∀ x, vt (sV x) = ℓ x := fun x ↦
    AlgHom.congr_fun (infBase_comp_sV b hb sV hsV hv hℓ) x
  have ht₀ : ∀ x, vt (tV x) = ℓ x := fun x ↦
    AlgHom.congr_fun (infBase_comp_tV b hb tV htV hv hℓ) x
  have hs₁ : ∀ x, f₁ (sV x) = ℓ x := fun x ↦
    AlgHom.congr_fun (infLift_comp_sV b hb sV tV hsV hv hℓ hE₁) x
  have ht₂ : ∀ x, f₂ (tV x) = ℓ x := fun x ↦
    AlgHom.congr_fun (infLift_comp_tV b hb sV tV htV hv hℓ hE₂) x
  have hL : L₁.comp sV = L₂.comp tV := AlgHom.ext fun x ↦ Subtype.ext (Prod.ext
    ((hs₀ x).trans (ht₀ x).symm) (Prod.ext ((hs₁ x).trans (ht₀ x).symm)
      ((hs₀ x).trans (ht₂ x).symm)))
  have hsrc : G.src (b.app _ L₁) = G.tgt (b.app _ L₂) := by rw [hsV, htV, hL]
  set Gc := G.comp (b.app _ L₁) (b.app _ L₂) hsrc
  have hred : ∀ (L : Q →ₐ[A'] (fib3 e hκ).obj),
      (fib3Sq e hκ).q.hom.hom.comp L = e.q.hom.hom.comp vt →
        G.arr.map (fib3Sq e hκ).q (b.app _ L) = G.idt w := by
    intro L hL'
    rw [b.natural, hL', hvt, hv]
  have hz : G.arr.map (fib3Sq e hκ).q Gc = b.app C v := by
    rw [G.comp_map, G.comp_eq' (hred L₁ (fib3Lift_red e hκ _ _ _ _ _))
      (hred L₂ (fib3Lift_red e hκ _ _ _ _ _)) _ (by rw [G.src_idt, G.tgt_idt]), hv]
    exact (G.comp_eq' rfl (congrArg G.idt (G.src_idt w).symm) _ _).trans (G.comp_idt _)
  obtain ⟨H, ⟨hHq, hHb⟩, -⟩ := hb (fib3 e hκ) C (fib3Sq e hκ).q (fib3Sq e hκ).surj
    (fib3Sq e hκ).sq v Gc hz
  have hcomp : ∀ k : Fin 3, b.app C' ((fib3Proj e hκ k).hom.hom.comp H) =
      G.comp (G.arr.map (fib3Proj e hκ k) (b.app _ L₁)) (G.arr.map (fib3Proj e hκ k) (b.app _ L₂))
        (by rw [G.src_map, G.tgt_map, hsrc]) := fun k ↦ by
    rw [← b.natural, hHb, G.comp_map]
  have hproj₁ : ∀ k : Fin 3, G.arr.map (fib3Proj e hκ k) (b.app _ L₁) =
      b.app C' (![vt, f₁, vt] k) := fun k ↦ by rw [b.natural, fib3Lift_proj]
  have hproj₂ : ∀ k : Fin 3, G.arr.map (fib3Proj e hκ k) (b.app _ L₂) =
      b.app C' (![vt, vt, f₂] k) := fun k ↦ by rw [b.natural, fib3Lift_proj]
  have hHred := comp_fib3Proj_red hκ hHq
  have hzℓ : G.arr.map e.q (G.idt ℓ) = b.app C v := by rw [G.idt_map, hℓ, hv]
  have hbvt : b.app C' vt = G.idt ℓ := app_infBase b hb hv hℓ
  have hH₀ : (fib3Proj e hκ 0).hom.hom.comp H = vt := by
    refine chart_unique b hb hzℓ (hHred 0) ?_ hvt hbvt
    rw [hcomp, G.comp_eq' ((hproj₁ 0).trans hbvt) ((hproj₂ 0).trans hbvt) _
      (by rw [G.src_idt, G.tgt_idt])]
    exact (G.comp_eq' rfl (congrArg G.idt (G.src_idt ℓ).symm) _ _).trans (G.comp_idt _)
  have hH₁ : (fib3Proj e hκ 1).hom.hom.comp H = f₁ := by
    refine eq_infLift_of_app_eq_infOf b hb sV tV hv hℓ hE₁ (hHred 1) ?_
    rw [hcomp, G.comp_eq' (hproj₁ 1) ((hproj₂ 1).trans hbvt) _
      (by rw [G.tgt_idt]; exact src_infOf b hb sV tV hsV hv hℓ hE₁)]
    exact (G.comp_eq' rfl (congrArg G.idt (src_infOf b hb sV tV hsV hv hℓ hE₁).symm) _ _).trans
      (G.comp_idt _)
  have hH₂ : (fib3Proj e hκ 2).hom.hom.comp H = f₂ := by
    refine eq_infLift_of_app_eq_infOf b hb sV tV hv hℓ hE₂ (hHred 2) ?_
    rw [hcomp, G.comp_eq' ((hproj₁ 2).trans hbvt) (hproj₂ 2) _
      (by rw [G.src_idt]; exact (tgt_infOf b hb sV tV htV hv hℓ hE₂).symm)]
    exact (G.comp_eq' (congrArg G.idt (tgt_infOf b hb sV tV htV hv hℓ hE₂).symm) rfl _ _).trans
      (G.idt_comp _)
  set σ := fib3Sigma e hκ 1 1
  have hσH : σ.hom.hom.comp H = infLift b hb sV tV hv hℓ (add_mem hE₁ hE₂) := by
    ext x
    have e₀ : (H x).1.1 = vt x := AlgHom.congr_fun hH₀ x
    have e₁ : (H x).1.2.1 = f₁ x := AlgHom.congr_fun hH₁ x
    have e₂ : (H x).1.2.2 = f₂ x := AlgHom.congr_fun hH₂ x
    change (H x).1.1 + 1 * ((H x).1.2.1 - (H x).1.1) + 1 * ((H x).1.2.2 - (H x).1.1) =
      vt x + (E₁ + E₂) x
    rw [e₀, e₁, e₂]
    change vt x + 1 * (vt x + E₁ x - vt x) + 1 * (vt x + E₂ x - vt x) = vt x + (E₁ x + E₂ x)
    ring
  have hσ₁ : σ.hom.hom.comp L₁ = f₁ := by
    ext x
    change vt x + 1 * (f₁ x - vt x) + 1 * (vt x - vt x) = f₁ x
    ring
  have hσ₂ : σ.hom.hom.comp L₂ = f₂ := by
    ext x
    change vt x + 1 * (vt x - vt x) + 1 * (f₂ x - vt x) = f₂ x
    ring
  have key : G.arr.map σ Gc = G.comp (infOf b hb sV tV hv hℓ hE₁) (infOf b hb sV tV hv hℓ hE₂)
      (by rw [src_infOf b hb sV tV hsV, tgt_infOf b hb sV tV htV]) := by
    rw [G.comp_map]
    exact G.comp_eq' ((b.natural _ _).trans (congrArg (b.app C') hσ₁))
      ((b.natural _ _).trans (congrArg (b.app C') hσ₂)) _ _
  rw [← key, ← hHb, b.natural, hσH]
  rfl


/-- **An automorphism over the triples is read off from its three components.** If an arrow over
the algebra of triples has components the identity of `ℓ`, `infOf E₁` and `infOf E₂`, then its
affine combination `σ_{c₁, c₂}` is `infOf (c₁ E₁ + c₂ E₂)`. -/
theorem map_sigma_eq_infOf (hκ : Cardinal.aleph0 < κ) {w : P →ₐ[A'] C.obj}
    {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w) {ℓ : P →ₐ[A'] C'.obj}
    (hℓ : e.q.hom.hom.comp ℓ = w) {E₁ E₂ : Q →ₗ[A'] C'.obj} (hE₁ : E₁ ∈ K2 e v sV tV)
    (hE₂ : E₂ ∈ K2 e v sV tV) (g : G.arr.obj (fib3 e hκ))
    (h₀ : G.arr.map (fib3Proj e hκ 0) g = G.idt ℓ)
    (h₁ : G.arr.map (fib3Proj e hκ 1) g = infOf b hb sV tV hv hℓ hE₁)
    (h₂ : G.arr.map (fib3Proj e hκ 2) g = infOf b hb sV tV hv hℓ hE₂) (c₁ c₂ : C'.obj) :
    G.arr.map (fib3Sigma e hκ c₁ c₂) g = infOf b hb sV tV hv hℓ
      (add_mem (Submodule.smul_mem _ c₁ hE₁) (Submodule.smul_mem _ c₂ hE₂)) := by
  have hvt := infBase_red b hb hv hℓ
  have hz : G.arr.map (fib3Sq e hκ).q g = b.app C v := by
    rw [← fib3Proj_red (e := e) hκ 0, ← G.map_map, h₀, G.idt_map, hℓ, hv]
  obtain ⟨H, ⟨hHq, hHb⟩, -⟩ := hb (fib3 e hκ) C (fib3Sq e hκ).q (fib3Sq e hκ).surj
    (fib3Sq e hκ).sq v g hz
  have hHred := comp_fib3Proj_red hκ hHq
  have hbH : ∀ k : Fin 3, b.app C' ((fib3Proj e hκ k).hom.hom.comp H) =
      G.arr.map (fib3Proj e hκ k) g := fun k ↦ by rw [← b.natural, hHb]
  have hH₀ : (fib3Proj e hκ 0).hom.hom.comp H = infBase b hb hv hℓ :=
    chart_unique b hb (by rw [G.idt_map, hℓ, hv]) (hHred 0) ((hbH 0).trans h₀) hvt
      (app_infBase b hb hv hℓ)
  have hH₁ := eq_infLift_of_app_eq_infOf b hb sV tV hv hℓ hE₁ (hHred 1) ((hbH 1).trans h₁)
  have hH₂ := eq_infLift_of_app_eq_infOf b hb sV tV hv hℓ hE₂ (hHred 2) ((hbH 2).trans h₂)
  rw [← hHb, b.natural]
  refine congrArg (b.app C') (AlgHom.ext fun x ↦ ?_)
  have e₀ : (H x).1.1 = infBase b hb hv hℓ x := AlgHom.congr_fun hH₀ x
  have e₁ : (H x).1.2.1 = infBase b hb hv hℓ x + E₁ x :=
    AlgHom.congr_fun hH₁ x
  have e₂ : (H x).1.2.2 = infBase b hb hv hℓ x + E₂ x :=
    AlgHom.congr_fun hH₂ x
  change (H x).1.1 + c₁ * ((H x).1.2.1 - (H x).1.1) + c₂ * ((H x).1.2.2 - (H x).1.1) =
    infBase b hb hv hℓ x + (c₁ • E₁ + c₂ • E₂) x
  rw [e₀, e₁, e₂, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
    smul_eq_mul]
  ring

/-! ### Conjugation -/

/-- Conjugation of an arrow by an arrow. -/
def Groupoid.conj (G : Groupoid A' κ P) {C : SmallAlg A' κ} (r g : G.arr.obj C)
    (hs : G.src g = G.src r) (ht : G.tgt g = G.src r) : G.arr.obj C :=
  G.comp r (G.comp g (G.inv r) (by rw [G.tgt_inv, hs])) (by rw [G.tgt_comp, ht])

/-- The source of the conjugate of `g` by `r` is the target of `r`. -/
theorem Groupoid.src_conj (G : Groupoid A' κ P) {C : SmallAlg A' κ} (r g : G.arr.obj C)
    (hs : G.src g = G.src r) (ht : G.tgt g = G.src r) : G.src (G.conj r g hs ht) = G.tgt r := by
  rw [Groupoid.conj, G.src_comp, G.src_comp, G.src_inv]

/-- The target of the conjugate of `g` by `r` is the target of `r`. -/
theorem Groupoid.tgt_conj (G : Groupoid A' κ P) {C : SmallAlg A' κ} (r g : G.arr.obj C)
    (hs : G.src g = G.src r) (ht : G.tgt g = G.src r) : G.tgt (G.conj r g hs ht) = G.tgt r := by
  rw [Groupoid.conj, G.tgt_comp]

/-- Conjugation commutes with the maps of the presheaf of arrows. -/
theorem Groupoid.map_conj (G : Groupoid A' κ P) {C D : SmallAlg A' κ} (f : C ⟶ D)
    (r g : G.arr.obj C) (hs : G.src g = G.src r) (ht : G.tgt g = G.src r) :
    G.arr.map f (G.conj r g hs ht) = G.conj (G.arr.map f r) (G.arr.map f g)
      (by rw [G.src_map, G.src_map, hs]) (by rw [G.tgt_map, G.src_map, ht]) := by
  rw [Groupoid.conj, G.comp_map, Groupoid.conj]
  refine G.comp_eq' rfl ?_ _ _
  rw [G.comp_map]
  exact G.comp_eq' rfl (G.inv_map f r) _ _

/-- The conjugate by `r` of the identity of the source of `r` is the identity of the target of
`r`. -/
theorem Groupoid.conj_idt (G : Groupoid A' κ P) {C : SmallAlg A' κ} (r : G.arr.obj C) :
    G.conj r (G.idt (G.src r)) (G.src_idt _) (G.tgt_idt _) = G.idt (G.tgt r) := by
  rw [Groupoid.conj]
  exact (G.comp_eq' rfl ((G.comp_eq' (congrArg G.idt (G.tgt_inv r).symm) rfl _
    (by rw [G.src_idt])).trans (G.idt_comp _)) _ (G.tgt_inv r).symm).trans (G.comp_inv r)

/-- Conjugation is congruent in both arrows, whatever the endpoint proofs. -/
theorem Groupoid.conj_congr (G : Groupoid A' κ P) {C : SmallAlg A' κ} {r r' g g' : G.arr.obj C}
    (hr : r = r') (hg : g = g') (hs : G.src g = G.src r) (ht : G.tgt g = G.src r)
    (hs' : G.src g' = G.src r') (ht' : G.tgt g' = G.src r') :
    G.conj r g hs ht = G.conj r' g' hs' ht' := by
  subst hr hg
  rfl

/-- The conjugate by `r` of an arrow equal to the identity of the source of `r` is the identity of
the target of `r`. -/
theorem Groupoid.conj_eq_idt (G : Groupoid A' κ P) {C : SmallAlg A' κ} {r g : G.arr.obj C}
    (hg : g = G.idt (G.src r)) (hs : G.src g = G.src r) (ht : G.tgt g = G.src r) :
    G.conj r g hs ht = G.idt (G.tgt r) :=
  (G.conj_congr rfl hg _ _ (G.src_idt _) (G.tgt_idt _)).trans (G.conj_idt r)

section Conj

variable {w w' : P →ₐ[A'] C.obj} {v v' : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
  (hv' : b.app C v' = G.idt w') {ℓ ℓ' : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w)
  (hℓ' : e.q.hom.hom.comp ℓ' = w') {r : G.arr.obj C'} (hrs : G.src r = ℓ) (hrt : G.tgt r = ℓ')

include hsV htV hrs hrt in
/-- The conjugate by `r` of `infOf E` is `infOf E'` for a derivation `E'` of `Q` along `v'` killed
by `sV` and `tV`. -/
theorem exists_conjK {E : Q →ₗ[A'] C'.obj} (hE : E ∈ K2 e v sV tV) :
    ∃ (E' : Q →ₗ[A'] C'.obj) (hE' : E' ∈ K2 e v' sV tV), infOf b hb sV tV hv' hℓ' hE' =
      G.conj r (infOf b hb sV tV hv hℓ hE) ((src_infOf b hb sV tV hsV hv hℓ hE).trans hrs.symm)
        ((tgt_infOf b hb sV tV htV hv hℓ hE).trans hrs.symm) := by
  refine exists_infOf_eq b hb sV tV hsV htV hv' hℓ' ?_ ?_ ?_
  · rw [G.src_conj, hrt]
  · rw [G.tgt_conj, hrt]
  · rw [G.map_conj, G.conj_eq_idt (by rw [map_infOf, G.src_map, hrs, hℓ]), G.tgt_map, hrt, hℓ']

/-- **Conjugation of infinitesimal automorphisms**, on derivations. -/
noncomputable def conjK {E : Q →ₗ[A'] C'.obj} (hE : E ∈ K2 e v sV tV) : Q →ₗ[A'] C'.obj :=
  (exists_conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE).choose

/-- The conjugate derivation `conjK E` lies in `K2 e v' sV tV`. -/
theorem conjK_mem {E : Q →ₗ[A'] C'.obj} (hE : E ∈ K2 e v sV tV) :
    conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE ∈ K2 e v' sV tV :=
  (exists_conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE).choose_spec.choose

/-- The infinitesimal automorphism of `conjK E` is the conjugate by `r` of `infOf E`. -/
theorem infOf_conjK {E : Q →ₗ[A'] C'.obj} (hE : E ∈ K2 e v sV tV) :
    infOf b hb sV tV hv' hℓ' (conjK_mem b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE) =
      G.conj r (infOf b hb sV tV hv hℓ hE) ((src_infOf b hb sV tV hsV hv hℓ hE).trans hrs.symm)
        ((tgt_infOf b hb sV tV htV hv hℓ hE).trans hrs.symm) :=
  (exists_conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE).choose_spec.choose_spec

/-- **Conjugation is linear.** -/
theorem conjK_add_smul (hκ : Cardinal.aleph0 < κ) {E₁ E₂ : Q →ₗ[A'] C'.obj}
    (hE₁ : E₁ ∈ K2 e v sV tV) (hE₂ : E₂ ∈ K2 e v sV tV) (c₁ c₂ : C'.obj) :
    conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt
        (add_mem (Submodule.smul_mem _ c₁ hE₁) (Submodule.smul_mem _ c₂ hE₂)) =
      c₁ • conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE₁ +
        c₂ • conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE₂ := by
  set vt := infBase b hb hv hℓ
  set f₁ := infLift b hb sV tV hv hℓ hE₁
  set f₂ := infLift b hb sV tV hv hℓ hE₂
  have h₁ : e.q.hom.hom.comp f₁ = e.q.hom.hom.comp vt := infLift_red b hb sV tV hv hℓ hE₁
  have h₂ : e.q.hom.hom.comp f₂ = e.q.hom.hom.comp vt := infLift_red b hb sV tV hv hℓ hE₂
  set L := fib3Lift e hκ vt f₁ f₂ h₁ h₂
  set r₃ := G.arr.map (fib3Diag e hκ) r
  have hsrc₃ : G.src r₃ = (fib3Diag e hκ).hom.hom.comp ℓ := by rw [G.src_map, hrs]
  have hLu : ∀ u : P →ₐ[A'] Q, vt.comp u = ℓ → f₁.comp u = ℓ → f₂.comp u = ℓ →
      L.comp u = (fib3Diag e hκ).hom.hom.comp ℓ := fun u h₀ h₁ h₂ ↦ by
    rw [fib3Diag_comp]
    exact AlgHom.ext fun x ↦ Subtype.ext (Prod.ext (AlgHom.congr_fun h₀ x)
      (Prod.ext (AlgHom.congr_fun h₁ x) (AlgHom.congr_fun h₂ x)))
  have hLs := hLu sV (infBase_comp_sV b hb sV hsV hv hℓ) (infLift_comp_sV b hb sV tV hsV hv hℓ hE₁)
    (infLift_comp_sV b hb sV tV hsV hv hℓ hE₂)
  have hLt := hLu tV (infBase_comp_tV b hb tV htV hv hℓ) (infLift_comp_tV b hb sV tV htV hv hℓ hE₁)
    (infLift_comp_tV b hb sV tV htV hv hℓ hE₂)
  have hs₃ : G.src (b.app _ L) = G.src r₃ := by rw [hsV, hLs, hsrc₃]
  have ht₃ : G.tgt (b.app _ L) = G.src r₃ := by rw [htV, hLt, hsrc₃]
  set h := G.conj r₃ (b.app _ L) hs₃ ht₃
  have hr₃ : ∀ k : Fin 3, G.arr.map (fib3Proj e hκ k) r₃ = r := fun k ↦ by
    rw [G.map_map, fib3Diag_proj, CategoryTheory.Functor.map_id]
    rfl
  have hproj : ∀ k : Fin 3, G.arr.map (fib3Proj e hκ k) h =
      G.conj r (b.app C' (![vt, f₁, f₂] k))
        (by rw [← fib3Lift_proj e hκ vt f₁ f₂ h₁ h₂ k, hsV, AlgHom.comp_assoc, hLs, ← hr₃ k,
          G.src_map, hsrc₃])
        (by rw [← fib3Lift_proj e hκ vt f₁ f₂ h₁ h₂ k, htV, AlgHom.comp_assoc, hLt, ← hr₃ k,
          G.src_map, hsrc₃]) := fun k ↦ by
    rw [G.map_conj]
    exact G.conj_congr (hr₃ k) ((b.natural _ _).trans (by rw [fib3Lift_proj])) _ _ _ _
  have hh₀ : G.arr.map (fib3Proj e hκ 0) h = G.idt ℓ' := by
    rw [hproj, ← hrt]
    exact G.conj_eq_idt ((app_infBase b hb hv hℓ).trans (congrArg G.idt hrs.symm)) _ _
  have hh₁ : G.arr.map (fib3Proj e hκ 1) h = infOf b hb sV tV hv' hℓ'
      (conjK_mem b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE₁) := by
    rw [hproj, infOf_conjK]
    rfl
  have hh₂ : G.arr.map (fib3Proj e hκ 2) h = infOf b hb sV tV hv' hℓ'
      (conjK_mem b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE₂) := by
    rw [hproj, infOf_conjK]
    rfl
  have hσ := map_sigma_eq_infOf b hb sV tV hκ hv' hℓ' _ _ h hh₀ hh₁ hh₂ c₁ c₂
  have hσL : (fib3Sigma e hκ c₁ c₂).hom.hom.comp L = infLift b hb sV tV hv hℓ
      (add_mem (Submodule.smul_mem _ c₁ hE₁) (Submodule.smul_mem _ c₂ hE₂)) := by
    ext x
    change vt x + c₁ * ((vt x + E₁ x) - vt x) + c₂ * ((vt x + E₂ x) - vt x) =
      vt x + (c₁ • E₁ + c₂ • E₂) x
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  have hσ' : G.arr.map (fib3Sigma e hκ c₁ c₂) h = infOf b hb sV tV hv' hℓ'
      (conjK_mem b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt
        (add_mem (Submodule.smul_mem _ c₁ hE₁) (Submodule.smul_mem _ c₂ hE₂))) := by
    rw [G.map_conj, infOf_conjK]
    refine G.conj_congr ?_ ((b.natural _ _).trans (congrArg (b.app C') hσL)) _ _ _ _
    rw [G.map_map, fib3Diag_sigma, CategoryTheory.Functor.map_id]
    rfl
  exact infOf_injective b hb sV tV hv' hℓ' _ _ (hσ'.symm.trans hσ)

/-- **Characterization of conjugation**: a derivation whose automorphism is the conjugate is the
conjugate derivation. -/
theorem eq_conjK_of_infOf {E : Q →ₗ[A'] C'.obj} (hE : E ∈ K2 e v sV tV) {E' : Q →ₗ[A'] C'.obj}
    (hE' : E' ∈ K2 e v' sV tV)
    (h : infOf b hb sV tV hv' hℓ' hE' = G.conj r (infOf b hb sV tV hv hℓ hE)
      ((src_infOf b hb sV tV hsV hv hℓ hE).trans hrs.symm)
      ((tgt_infOf b hb sV tV htV hv hℓ hE).trans hrs.symm)) :
    E' = conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE :=
  infOf_injective b hb sV tV hv' hℓ' hE' (conjK_mem b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE)
    (h.trans (infOf_conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE).symm)

/-- Equal derivations have equal conjugates. -/
theorem conjK_congr {E E' : Q →ₗ[A'] C'.obj} (h : E = E') (hE : E ∈ K2 e v sV tV)
    (hE' : E' ∈ K2 e v sV tV) :
    conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE =
      conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE' := by
  subst h
  rfl

/-- Conjugation of derivations is additive. -/
theorem conjK_add (hκ : Cardinal.aleph0 < κ) {E₁ E₂ : Q →ₗ[A'] C'.obj}
    (hE₁ : E₁ ∈ K2 e v sV tV) (hE₂ : E₂ ∈ K2 e v sV tV) :
    conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt (add_mem hE₁ hE₂) =
      conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE₁ +
        conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE₂ := by
  rw [conjK_congr b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt (by rw [one_smul, one_smul])
    (add_mem hE₁ hE₂) (add_mem (Submodule.smul_mem _ 1 hE₁) (Submodule.smul_mem _ 1 hE₂)),
    conjK_add_smul b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hκ hE₁ hE₂ 1 1, one_smul, one_smul]

/-- Conjugation of derivations commutes with multiplication by elements of `C'`. -/
theorem conjK_smul (hκ : Cardinal.aleph0 < κ) (c : C'.obj) {E : Q →ₗ[A'] C'.obj}
    (hE : E ∈ K2 e v sV tV) :
    conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt (Submodule.smul_mem _ c hE) =
      c • conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE := by
  rw [conjK_congr b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt (by rw [zero_smul, add_zero])
    (Submodule.smul_mem _ c hE) (add_mem (Submodule.smul_mem _ c hE) (Submodule.smul_mem _ 0 hE)),
    conjK_add_smul b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hκ hE hE c 0, zero_smul, add_zero]

/-- Conjugation of derivations commutes with the action of `A'` on `K2 e v sV tV`. -/
theorem conjK_smul' (hκ : Cardinal.aleph0 < κ) (a : A') (E : K2 e v sV tV) :
    conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt (a • E).2 =
      a • conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt E.2 := by
  have h : ((a • E : K2 e v sV tV) : Q →ₗ[A'] C'.obj) = algebraMap A' C'.obj a • E.1 :=
    (algebraMap_smul C'.obj a E.1).symm
  rw [conjK_congr b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt h _
    (Submodule.smul_mem _ (algebraMap A' C'.obj a) E.2), conjK_smul b hb sV tV hsV htV hv hv'
      hℓ hℓ' hrs hrt hκ, algebraMap_smul]

/-- **Conjugation as an `A'`-linear map.** -/
noncomputable def conjLin (hκ : Cardinal.aleph0 < κ) : K2 e v sV tV →ₗ[A'] K2 e v' sV tV where
  toFun E := ⟨conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt E.2,
    conjK_mem b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt E.2⟩
  map_add' E₁ E₂ := Subtype.ext (conjK_add b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hκ E₁.2 E₂.2)
  map_smul' a E := Subtype.ext (conjK_smul' b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hκ a E)

/-- The linear map `conjLin` sends `E` to `conjK E`. -/
theorem conjLin_apply (hκ : Cardinal.aleph0 < κ) (E : K2 e v sV tV) :
    (conjLin b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hκ E : Q →ₗ[A'] C'.obj) =
      conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt E.2 := rfl

end Conj

/-- Conjugation by the identity of `x` fixes every arrow from `x` to `x`. -/
theorem Groupoid.conj_idt_left (G : Groupoid A' κ P) {C : SmallAlg A' κ} (g : G.arr.obj C)
    {x : P →ₐ[A'] C.obj} (hx : G.src g = x) (hs : G.src g = G.src (G.idt x))
    (ht : G.tgt g = G.src (G.idt x)) : G.conj (G.idt x) g hs ht = g := by
  have hxt : G.tgt g = x := ht.trans (G.src_idt x)
  rw [Groupoid.conj]
  have hinv : G.inv (G.idt x) = G.idt x := G.inv_idt x
  have h₁ : G.comp g (G.inv (G.idt x)) (by rw [G.tgt_inv, hs]) = g :=
    (G.comp_eq' rfl (hinv.trans (congrArg G.idt hx.symm)) _ (G.tgt_idt _).symm).trans
      (G.comp_idt g)
  exact (G.comp_eq' (congrArg G.idt hxt.symm) h₁ _ (G.src_idt _)).trans (G.idt_comp g)

include hsV htV in
/-- Conjugation by an identity is the identity. -/
theorem conjK_idt {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w) {E : Q →ₗ[A'] C'.obj}
    (hE : E ∈ K2 e v sV tV) :
    conjK b hb sV tV hsV htV hv hv hℓ hℓ (G.src_idt ℓ) (G.tgt_idt ℓ) hE = E :=
  (eq_conjK_of_infOf b hb sV tV hsV htV hv hv hℓ hℓ (G.src_idt ℓ) (G.tgt_idt ℓ) hE hE
    (G.conj_idt_left _ (src_infOf b hb sV tV hsV hv hℓ hE) _ _).symm).symm

/-- In a groupoid, a right inverse is the inverse. -/
theorem Groupoid.eq_inv_of_comp_eq_idt (G : Groupoid A' κ P) {C : SmallAlg A' κ}
    {g h : G.arr.obj C} (hgh : G.src g = G.tgt h) (h₁ : G.comp g h hgh = G.idt (G.tgt g)) :
    h = G.inv g := by
  have ha := G.assoc (G.inv g) g h (G.src_inv g) hgh
  rw [G.comp_eq' (G.inv_comp g) rfl _ (by rw [G.src_idt]; exact hgh), G.comp_eq' rfl h₁ _
    (by rw [G.tgt_idt, G.src_inv])] at ha
  rw [G.comp_eq' (congrArg G.idt hgh) rfl _ (G.src_idt _), G.idt_comp] at ha
  rw [ha, G.comp_eq' rfl (congrArg G.idt (G.src_inv g).symm) _ (G.tgt_idt _).symm, G.comp_idt]

include hsV htV in
/-- **Conjugation by an infinitesimal automorphism is trivial**, infinitesimal automorphisms
commuting with each other. -/
theorem conjK_infOf (hκ : Cardinal.aleph0 < κ) {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj}
    (hv : b.app C v = G.idt w) {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w)
    {F E : Q →ₗ[A'] C'.obj} (hF : F ∈ K2 e v sV tV) (hE : E ∈ K2 e v sV tV) :
    conjK b hb sV tV hsV htV hv hv hℓ hℓ (src_infOf b hb sV tV hsV hv hℓ hF)
      (tgt_infOf b hb sV tV htV hv hℓ hF) hE = E := by
  symm
  refine eq_conjK_of_infOf b hb sV tV hsV htV hv hv hℓ hℓ _ _ hE hE ?_
  have hneg : G.inv (infOf b hb sV tV hv hℓ hF) = infOf b hb sV tV hv hℓ (neg_mem hF) := by
    symm
    refine G.eq_inv_of_comp_eq_idt
      (by rw [src_infOf b hb sV tV hsV, tgt_infOf b hb sV tV htV]) ?_
    rw [comp_infOf b hb sV tV hsV htV hκ hv hℓ hF (neg_mem hF), tgt_infOf b hb sV tV htV]
    rw [← infOf_zero b hb sV tV hv hℓ]
    exact congrArg (fun E' : {E' // E' ∈ K2 e v sV tV} ↦ infOf b hb sV tV hv hℓ E'.2)
      (Subtype.ext (add_neg_cancel F) : (⟨F + -F, add_mem hF (neg_mem hF)⟩ :
        {E' // E' ∈ K2 e v sV tV}) = ⟨0, zero_mem _⟩)
  rw [Groupoid.conj]
  rw [G.comp_eq' rfl (G.comp_eq' rfl hneg _ (by rw [src_infOf b hb sV tV hsV,
    tgt_infOf b hb sV tV htV])) _ (by rw [G.tgt_comp, tgt_infOf b hb sV tV htV,
      src_infOf b hb sV tV hsV])]
  rw [G.comp_eq' rfl (comp_infOf b hb sV tV hsV htV hκ hv hℓ hE (neg_mem hF)) _
    (by rw [src_infOf b hb sV tV hsV, tgt_infOf b hb sV tV htV]),
    comp_infOf b hb sV tV hsV htV hκ hv hℓ hF (add_mem hE (neg_mem hF))]
  exact congrArg (fun E' : {E' // E' ∈ K2 e v sV tV} ↦ infOf b hb sV tV hv hℓ E'.2)
    (Subtype.ext (show E = F + (E + -F) by abel) : (⟨E, hE⟩ : {E' // E' ∈ K2 e v sV tV}) =
      ⟨F + (E + -F), add_mem hF (add_mem hE (neg_mem hF))⟩)

/-- **Congruence for conjugation**, in the conjugating arrow, the chart points and the
derivation (the reductions and lifts of the endpoints follow). -/
theorem conjK_congr_all {w w' w₁ w₁' : P →ₐ[A'] C.obj} {v v' v₁ v₁' : Q →ₐ[A'] C.obj}
    (hv : b.app C v = G.idt w) (hv' : b.app C v' = G.idt w') (hv₁ : b.app C v₁ = G.idt w₁)
    (hv₁' : b.app C v₁' = G.idt w₁') {ℓ ℓ' ℓ₁ ℓ₁' : P →ₐ[A'] C'.obj}
    (hℓ : e.q.hom.hom.comp ℓ = w) (hℓ' : e.q.hom.hom.comp ℓ' = w')
    (hℓ₁ : e.q.hom.hom.comp ℓ₁ = w₁) (hℓ₁' : e.q.hom.hom.comp ℓ₁' = w₁')
    {r r₁ : G.arr.obj C'} (hrs : G.src r = ℓ) (hrt : G.tgt r = ℓ') (hrs₁ : G.src r₁ = ℓ₁)
    (hrt₁ : G.tgt r₁ = ℓ₁') {E E₁ : Q →ₗ[A'] C'.obj} (hE : E ∈ K2 e v sV tV)
    (hE₁ : E₁ ∈ K2 e v₁ sV tV) (h₁ : v = v₁) (h₂ : v' = v₁') (h₃ : r = r₁) (h₄ : E = E₁) :
    conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE =
      conjK b hb sV tV hsV htV hv₁ hv₁' hℓ₁ hℓ₁' hrs₁ hrt₁ hE₁ := by
  have hw : w = w₁ := by rw [← G.src_idt w, ← hv, h₁, hv₁, G.src_idt]
  have hw' : w' = w₁' := by rw [← G.src_idt w', ← hv', h₂, hv₁', G.src_idt]
  have hl : ℓ = ℓ₁ := by rw [← hrs, h₃, hrs₁]
  have hl' : ℓ' = ℓ₁' := by rw [← hrt, h₃, hrt₁]
  subst h₁ h₂ h₃ h₄ hw hw' hl hl'
  rfl

/-! ### Naturality in the thickening -/

section Natural

variable {D' D : SmallAlg A' κ} {e₂ : SqZero D' D} (φ : SqZero.Hom e e₂)

/-- Postcomposition with the map `φ` of thickenings sends `K2 e v sV tV` into
`K2 e₂ v₂ sV tV`, where `v₂` is the image of `v`. -/
theorem postcomp_mem_K2 {v : Q →ₐ[A'] C.obj} {v₂ : Q →ₐ[A'] D.obj}
    (hv₂ : φ.bot.hom.hom.comp v = v₂) {E : Q →ₗ[A'] C'.obj} (hE : E ∈ K2 e v sV tV) :
    postcomp φ E ∈ K2 e₂ v₂ sV tV := by
  refine ⟨⟨mem_Der_postcomp φ hv₂ hE.1.1, LinearMap.mem_ker.mpr ?_⟩, LinearMap.mem_ker.mpr ?_⟩
  · ext x
    change φ.top.hom.hom (E (sV x)) = 0
    rw [K2_sV sV tV hE, map_zero]
  · ext x
    change φ.top.hom.hom (E (tV x)) = 0
    rw [K2_tV sV tV hE, map_zero]

/-- **The map of `K₂` induced by a map of thickenings**, `A'`-linear. -/
def K2Map {v : Q →ₐ[A'] C.obj} {v₂ : Q →ₐ[A'] D.obj} (hv₂ : φ.bot.hom.hom.comp v = v₂) :
    K2 e v sV tV →ₗ[A'] K2 e₂ v₂ sV tV :=
  LinearMap.codRestrict ((K2 e₂ v₂ sV tV).restrictScalars A')
    (LinearMap.llcomp A' Q C'.obj D'.obj φ.top.hom.hom.toLinearMap ∘ₗ
      (K2 e v sV tV).subtype.restrictScalars A')
    (fun E ↦ postcomp_mem_K2 sV tV φ hv₂ E.2)

/-- The map `K2Map` sends `E` to its postcomposition with `φ`. -/
theorem K2Map_apply {v : Q →ₐ[A'] C.obj} {v₂ : Q →ₐ[A'] D.obj}
    (hv₂ : φ.bot.hom.hom.comp v = v₂) (E : K2 e v sV tV) :
    (K2Map sV tV φ hv₂ E : Q →ₗ[A'] D'.obj) = postcomp φ E.1 := rfl

/-- The map `φ` of thickenings carries `infBase` for `ℓ` to `infBase` for the image of `ℓ`. -/
theorem infBase_map {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w) {w₂ : P →ₐ[A'] D.obj}
    {v₂ : Q →ₐ[A'] D.obj} (hv₂ : b.app D v₂ = G.idt w₂) (hvv : φ.bot.hom.hom.comp v = v₂)
    (hℓ₂ : e₂.q.hom.hom.comp (φ.top.hom.hom.comp ℓ) = w₂) :
    φ.top.hom.hom.comp (infBase b hb hv hℓ) = infBase b hb hv₂ hℓ₂ := by
  refine chart_unique b hb (z := G.idt (φ.top.hom.hom.comp ℓ)) (by rw [G.idt_map, hℓ₂, hv₂])
    ?_ ?_ (infBase_red b hb hv₂ hℓ₂) (app_infBase b hb hv₂ hℓ₂)
  · rw [SqZero.Hom.w_comp, infBase_red, hvv]
  · rw [← b.natural, app_infBase, G.idt_map]

/-- **Infinitesimal automorphisms are natural in the thickening.** -/
theorem map_top_infOf {w : P →ₐ[A'] C.obj} {v : Q →ₐ[A'] C.obj} (hv : b.app C v = G.idt w)
    {ℓ : P →ₐ[A'] C'.obj} (hℓ : e.q.hom.hom.comp ℓ = w) {w₂ : P →ₐ[A'] D.obj}
    {v₂ : Q →ₐ[A'] D.obj} (hv₂ : b.app D v₂ = G.idt w₂) (hvv : φ.bot.hom.hom.comp v = v₂)
    (hℓ₂ : e₂.q.hom.hom.comp (φ.top.hom.hom.comp ℓ) = w₂) {E : Q →ₗ[A'] C'.obj}
    (hE : E ∈ K2 e v sV tV) :
    G.arr.map φ.top (infOf b hb sV tV hv hℓ hE) =
      infOf b hb sV tV hv₂ hℓ₂ (postcomp_mem_K2 sV tV φ hvv hE) := by
  rw [infOf, b.natural]
  refine congrArg (b.app D') (AlgHom.ext fun x ↦ ?_)
  have h := congrArg (fun f : Q →ₐ[A'] D'.obj ↦ f x) (infBase_map b hb φ hv hℓ hv₂ hvv hℓ₂)
  change φ.top.hom.hom (infBase b hb hv hℓ x + E x) = infBase b hb hv₂ hℓ₂ x + φ.top.hom.hom (E x)
  rw [map_add]
  exact congrArg (· + φ.top.hom.hom (E x)) h


/-- **Conjugation is natural in the thickening.** -/
theorem postcomp_conjK {w w' : P →ₐ[A'] C.obj} {v v' : Q →ₐ[A'] C.obj}
    (hv : b.app C v = G.idt w) (hv' : b.app C v' = G.idt w') {ℓ ℓ' : P →ₐ[A'] C'.obj}
    (hℓ : e.q.hom.hom.comp ℓ = w) (hℓ' : e.q.hom.hom.comp ℓ' = w') {r : G.arr.obj C'}
    (hrs : G.src r = ℓ) (hrt : G.tgt r = ℓ') {w₂ w₂' : P →ₐ[A'] D.obj} {v₂ v₂' : Q →ₐ[A'] D.obj}
    (hv₂ : b.app D v₂ = G.idt w₂) (hv₂' : b.app D v₂' = G.idt w₂')
    (hvv : φ.bot.hom.hom.comp v = v₂) (hvv' : φ.bot.hom.hom.comp v' = v₂')
    (hℓ₂ : e₂.q.hom.hom.comp (φ.top.hom.hom.comp ℓ) = w₂)
    (hℓ₂' : e₂.q.hom.hom.comp (φ.top.hom.hom.comp ℓ') = w₂')
    (hrs₂ : G.src (G.arr.map φ.top r) = φ.top.hom.hom.comp ℓ)
    (hrt₂ : G.tgt (G.arr.map φ.top r) = φ.top.hom.hom.comp ℓ') {E : Q →ₗ[A'] C'.obj}
    (hE : E ∈ K2 e v sV tV) :
    postcomp φ (conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE) =
      conjK b hb sV tV hsV htV hv₂ hv₂' hℓ₂ hℓ₂' hrs₂ hrt₂ (postcomp_mem_K2 sV tV φ hvv hE) := by
  refine eq_conjK_of_infOf b hb sV tV hsV htV hv₂ hv₂' hℓ₂ hℓ₂' hrs₂ hrt₂ _
    (postcomp_mem_K2 sV tV φ hvv' (conjK_mem b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE)) ?_
  rw [← map_top_infOf b hb sV tV φ hv' hℓ' hv₂' hvv' hℓ₂'
    (conjK_mem b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE), infOf_conjK, G.map_conj]
  exact G.conj_congr rfl (map_top_infOf b hb sV tV φ hv hℓ hv₂ hvv hℓ₂ hE) _ _ _ _

/-- **Conjugation is natural in the thickening**, for any arrow `r₂`, endpoints `ℓ₂`, `ℓ₂'` and
derivation `E₂` equal to the images of `r`, `ℓ`, `ℓ'` and `E`. -/
theorem postcomp_conjK_eq {w w' : P →ₐ[A'] C.obj} {v v' : Q →ₐ[A'] C.obj}
    (hv : b.app C v = G.idt w) (hv' : b.app C v' = G.idt w') {ℓ ℓ' : P →ₐ[A'] C'.obj}
    (hℓ : e.q.hom.hom.comp ℓ = w) (hℓ' : e.q.hom.hom.comp ℓ' = w') {r : G.arr.obj C'}
    (hrs : G.src r = ℓ) (hrt : G.tgt r = ℓ') {w₂ w₂' : P →ₐ[A'] D.obj} {v₂ v₂' : Q →ₐ[A'] D.obj}
    (hv₂ : b.app D v₂ = G.idt w₂) (hv₂' : b.app D v₂' = G.idt w₂')
    (hvv : φ.bot.hom.hom.comp v = v₂) (hvv' : φ.bot.hom.hom.comp v' = v₂')
    {r₂ : G.arr.obj D'} (hr₂ : G.arr.map φ.top r = r₂) {ℓ₂ ℓ₂' : P →ₐ[A'] D'.obj}
    (hℓ₂ : e₂.q.hom.hom.comp ℓ₂ = w₂) (hℓ₂' : e₂.q.hom.hom.comp ℓ₂' = w₂')
    (hrs₂ : G.src r₂ = ℓ₂) (hrt₂ : G.tgt r₂ = ℓ₂') {E : Q →ₗ[A'] C'.obj}
    (hE : E ∈ K2 e v sV tV) {E₂ : Q →ₗ[A'] D'.obj} (hE₂ : E₂ ∈ K2 e₂ v₂ sV tV)
    (hEE : postcomp φ E = E₂) :
    postcomp φ (conjK b hb sV tV hsV htV hv hv' hℓ hℓ' hrs hrt hE) =
      conjK b hb sV tV hsV htV hv₂ hv₂' hℓ₂ hℓ₂' hrs₂ hrt₂ hE₂ := by
  have hs : G.src (G.arr.map φ.top r) = φ.top.hom.hom.comp ℓ := by rw [G.src_map, hrs]
  have ht : G.tgt (G.arr.map φ.top r) = φ.top.hom.hom.comp ℓ' := by rw [G.tgt_map, hrt]
  have hl : φ.top.hom.hom.comp ℓ = ℓ₂ := by rw [← hs, hr₂, hrs₂]
  have hl' : φ.top.hom.hom.comp ℓ' = ℓ₂' := by rw [← ht, hr₂, hrt₂]
  rw [postcomp_conjK b hb sV tV hsV htV φ hv hv' hℓ hℓ' hrs hrt hv₂ hv₂' hvv hvv'
    (by rw [hl, hℓ₂]) (by rw [hl', hℓ₂']) hs ht hE]
  exact conjK_congr_all b hb sV tV hsV htV _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl hr₂ hEE

end Natural

end AlgebraicGeometry.Stack.GroupoidLift

end
