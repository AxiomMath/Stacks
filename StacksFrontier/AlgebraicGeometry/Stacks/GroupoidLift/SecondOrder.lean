module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.InfDecalage
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.PointCategory

/-!
# The second-order step: correcting the lifted descent arrow to a cocycle

Let `r` be an arrow over the Čech nerve `C' ⊗ C'` lifting a cocycle descent arrow `rbar`, from
the lifted point `v₀ ∘ u` to `vₗ ∘ u` (the output of
`AlgebraicGeometry.Stack.GroupoidLift.NerveDatum.exists_lift_arrow`). Over `C' ⊗ C' ⊗ C'` its
three pullbacks need not satisfy the cocycle condition: the *defect*
`r₁₂ ∘ r₀₁ ∘ r₀₂⁻¹` is an infinitesimal automorphism of the last vertex, a derivation in the
module `N 2` of `AlgebraicGeometry.Stack.GroupoidLift.NerveDatum.infDecalage`. It is a
`2`-cocycle of the twisted Čech complex, hence a coboundary (`Decalage.exists_diff_eq`), and
changing `r` by the corresponding infinitesimal automorphism makes the defect vanish.

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.NerveDatum.exists_lift_arrow_cocycle`: a lift of the
  descent arrow between lifted points satisfying the cocycle condition exactly.
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {A' : Type u} [CommRing A'] {C' : Type u} [CommRing C'] [Algebra A' C']

/-! ### Cosimplicial identities from level `1` to level `3` -/

/-- The face `0` from level `2` after the face `0` from level `1` is `κ A' C' 2`. -/
theorem face_two_zero_comp_face_one_zero :
    (face A' C' 2 0).comp (face A' C' 1 0) = GroupoidLift.κ A' C' 2 :=
  Algebra.TensorProduct.ext' fun _ _ ↦ rfl

/-- The face `1` from level `2` after the face `0` from level `1` is `κ A' C' 2`. -/
theorem face_two_one_comp_face_one_zero :
    (face A' C' 2 1).comp (face A' C' 1 0) = GroupoidLift.κ A' C' 2 :=
  Algebra.TensorProduct.ext' fun _ _ ↦ rfl

/-- The cosimplicial identity `δ₀ ∘ δ₂ = δ₃ ∘ δ₀` from level `1` to level `3`. -/
theorem face_two_zero_comp_face_one_two :
    (face A' C' 2 0).comp (face A' C' 1 2) = (face A' C' 2 3).comp (face A' C' 1 0) :=
  Algebra.TensorProduct.ext' fun _ _ ↦ rfl

/-- The cosimplicial identity `δ₀ ∘ δ₁ = δ₂ ∘ δ₀` from level `1` to level `3`. -/
theorem face_two_zero_comp_face_one_one :
    (face A' C' 2 0).comp (face A' C' 1 1) = (face A' C' 2 2).comp (face A' C' 1 0) :=
  Algebra.TensorProduct.ext' fun _ _ ↦ rfl

/-- The cosimplicial identity `δ₁ ∘ δ₂ = δ₃ ∘ δ₁` from level `1` to level `3`. -/
theorem face_two_one_comp_face_one_two :
    (face A' C' 2 1).comp (face A' C' 1 2) = (face A' C' 2 3).comp (face A' C' 1 1) :=
  Algebra.TensorProduct.ext' fun _ _ ↦ rfl

/-- The cosimplicial identity `δ₁ ∘ δ₁ = δ₂ ∘ δ₁` from level `1` to level `3`. -/
theorem face_two_one_comp_face_one_one :
    (face A' C' 2 1).comp (face A' C' 1 1) = (face A' C' 2 2).comp (face A' C' 1 1) :=
  Algebra.TensorProduct.ext' fun _ _ ↦ rfl

/-- The cosimplicial identity `δ₂ ∘ δ₂ = δ₃ ∘ δ₂` from level `1` to level `3`. -/
theorem face_two_two_comp_face_one_two :
    (face A' C' 2 2).comp (face A' C' 1 2) = (face A' C' 2 3).comp (face A' C' 1 2) :=
  Algebra.TensorProduct.ext' fun _ _ ↦ rfl

variable {κ : Cardinal.{u}} {P : Type u} [CommRing P] [Algebra A' P] {G : Groupoid A' κ P}
  {hκ : Cardinal.aleph0 < κ} {hC : Cardinal.mk C' < κ} {I : Ideal A'} {hI : I ^ 2 = ⊥}

namespace NerveDatum

variable (D : NerveDatum hκ C' hC I hI G)
  {Q : Type u} [CommRing Q] [Algebra A' Q] {b : Chart G.arr Q} (sV tV : P →ₐ[A'] Q)
  (εbar : Q →ₐ[A'] (red I (nerve (A' := A') hκ C' hC 0)).obj)
  (hsV : ∀ (C : SmallAlg A' κ) (v : Q →ₐ[A'] C.obj), G.src (b.app C v) = v.comp sV)
  (htV : ∀ (C : SmallAlg A' κ) (v : Q →ₐ[A'] C.obj), G.tgt (b.app C v) = v.comp tV)
  (hε : b.app _ εbar = G.idt D.ubar) (hb : b.IsFormallyEtale) {u : P →ₐ[A'] C'}
  (hu : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp u = D.ubar)

/-! ### Infinitesimal automorphisms at a vertex -/

omit D in
/-- `infOf` does not depend on the choice of the lift `ℓ` of the reduced point. -/
theorem infOf_congr_ℓ {C₁ C₂ : SmallAlg A' κ} {e : SqZero C₁ C₂} {w : P →ₐ[A'] C₂.obj}
    {v : Q →ₐ[A'] C₂.obj} (hv : b.app C₂ v = G.idt w) {ℓ ℓ₁ : P →ₐ[A'] C₁.obj}
    (hℓ : e.q.hom.hom.comp ℓ = w) (hℓ₁ : e.q.hom.hom.comp ℓ₁ = w) {E : Q →ₗ[A'] C₁.obj}
    (hE : E ∈ K2 e v sV tV) (h : ℓ = ℓ₁) :
    infOf b hb sV tV hv hℓ hE = infOf b hb sV tV hv hℓ₁ hE := by
  subst h
  rfl

/-- The infinitesimal automorphism of the lifted point at the vertex `f` given by a
derivation. -/
noncomputable abbrev infAt {m : ℕ} (f : C' →ₐ[A'] cech A' C' m) {E : Q →ₗ[A'] cech A' C' m}
    (hE : E ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV) :
    G.arr.obj (nerve (A' := A') hκ C' hC m) :=
  infOf b hb sV tV (D.chart_vAt εbar hε f) (D.q_comp_at hu f) hE

include hsV in
/-- The source of `infAt` is the lifted point `f ∘ u`. -/
theorem src_infAt {m : ℕ} (f : C' →ₐ[A'] cech A' C' m) {E : Q →ₗ[A'] cech A' C' m}
    (hE : E ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV) :
    G.src (D.infAt sV tV εbar hε hb hu f hE) = f.comp u :=
  src_infOf b hb sV tV hsV _ _ hE

include htV in
/-- The target of `infAt` is the lifted point `f ∘ u`. -/
theorem tgt_infAt {m : ℕ} (f : C' →ₐ[A'] cech A' C' m) {E : Q →ₗ[A'] cech A' C' m}
    (hE : E ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV) :
    G.tgt (D.infAt sV tV εbar hε hb hu f hE) = f.comp u :=
  tgt_infOf b hb sV tV htV _ _ hE

/-- `infAt` at equal vertices with equal derivations agree. -/
theorem infAt_congr {m : ℕ} {f f₁ : C' →ₐ[A'] cech A' C' m} {E E₁ : Q →ₗ[A'] cech A' C' m}
    (hE : E ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV)
    (hE₁ : E₁ ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f₁) sV tV)
    (hf : f = f₁) (h : E = E₁) :
    D.infAt sV tV εbar hε hb hu f hE = D.infAt sV tV εbar hε hb hu f₁ hE₁ := by
  subst hf h
  rfl

/-- Pulling back the infinitesimal automorphism at `f` along `g` gives the infinitesimal
automorphism at `g ∘ f` of the postcomposed derivation. -/
theorem map_top_infAt {m k : ℕ} (g : cech A' C' m →ₐ[A'] cech A' C' k)
    (f : C' →ₐ[A'] cech A' C' m) {E : Q →ₗ[A'] cech A' C' m}
    (hE : E ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV) :
    G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g).top
        (D.infAt sV tV εbar hε hb hu f hE) =
      D.infAt sV tV εbar hε hb hu (g.comp f)
        (postcomp_mem_K2 sV tV _ (Th_bot_vAt εbar g f) hE) := by
  have hℓ : (thk I hI (nerve (A' := A') hκ C' hC k)).q.hom.hom.comp
      ((Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g).top.hom.hom.comp (f.comp u)) =
      D.wAt (g.comp f) := by
    rw [thkHom_top, ← AlgHom.comp_assoc]
    exact D.q_comp_at hu (g.comp f)
  rw [map_top_infOf b hb sV tV _ (D.chart_vAt εbar hε f) (D.q_comp_at hu f)
    (D.chart_vAt εbar hε (g.comp f)) (Th_bot_vAt εbar g f) hℓ hE]
  exact infOf_congr_ℓ sV tV hb _ _ _ _ (AlgHom.comp_assoc _ _ _).symm

include hsV htV in
/-- The composite of the infinitesimal automorphisms of `E₁` and `E₂` is that of `E₁ + E₂`. -/
theorem comp_infAt {m : ℕ} (f : C' →ₐ[A'] cech A' C' m) {E₁ E₂ : Q →ₗ[A'] cech A' C' m}
    (hE₁ : E₁ ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV)
    (hE₂ : E₂ ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV)
    (h : G.src (D.infAt sV tV εbar hε hb hu f hE₁) = G.tgt (D.infAt sV tV εbar hε hb hu f hE₂)) :
    G.comp (D.infAt sV tV εbar hε hb hu f hE₁) (D.infAt sV tV εbar hε hb hu f hE₂) h =
      D.infAt sV tV εbar hε hb hu f (add_mem hE₁ hE₂) :=
  comp_infOf b hb sV tV hsV htV hκ _ _ hE₁ hE₂

/-- The infinitesimal automorphism at a vertex determines its derivation. -/
theorem infAt_injective {m : ℕ} (f : C' →ₐ[A'] cech A' C' m) {E₁ E₂ : Q →ₗ[A'] cech A' C' m}
    (hE₁ : E₁ ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV)
    (hE₂ : E₂ ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV)
    (h : D.infAt sV tV εbar hε hb hu f hE₁ = D.infAt sV tV εbar hε hb hu f hE₂) : E₁ = E₂ :=
  infOf_injective b hb sV tV _ _ hE₁ hE₂ h

/-- Conjugating the infinitesimal automorphism at `f` by an arrow `r'` from `f ∘ u` to
`f' ∘ u` gives the infinitesimal automorphism at `f'` of the conjugated derivation. -/
theorem infAt_conjAt {m : ℕ} {f f' : C' →ₐ[A'] cech A' C' m}
    {r' : G.arr.obj (nerve (A' := A') hκ C' hC m)} (hs : G.src r' = f.comp u)
    (ht : G.tgt r' = f'.comp u) {E : Q →ₗ[A'] cech A' C' m}
    (hE : E ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV) :
    D.infAt sV tV εbar hε hb hu f' (conjK_mem b hb sV tV hsV htV (D.chart_vAt εbar hε f)
      (D.chart_vAt εbar hε f') (D.q_comp_at hu f) (D.q_comp_at hu f') hs ht hE) =
      G.conj r' (D.infAt sV tV εbar hε hb hu f hE)
        ((D.src_infAt sV tV εbar hsV hε hb hu f hE).trans hs.symm)
        ((D.tgt_infAt sV tV εbar htV hε hb hu f hE).trans hs.symm) :=
  infOf_conjK b hb sV tV hsV htV _ _ _ _ hs ht hE

include hsV htV in
/-- An automorphism of the lifted point `f ∘ u` reducing to the identity is the infinitesimal
automorphism of some derivation. -/
theorem exists_infAt_eq {m : ℕ} (f : C' →ₐ[A'] cech A' C' m)
    {g : G.arr.obj (nerve (A' := A') hκ C' hC m)} (hs : G.src g = f.comp u)
    (ht : G.tgt g = f.comp u)
    (hq : G.arr.map (thk I hI (nerve (A' := A') hκ C' hC m)).q g = G.idt (D.wAt f)) :
    ∃ (E : Q →ₗ[A'] cech A' C' m)
      (hE : E ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV),
      D.infAt sV tV εbar hε hb hu f hE = g :=
  exists_infOf_eq b hb sV tV hsV htV _ _ hs ht hq

/-! ### Arrows pulled back along the nerve -/

/-- The lifted point at the vertex `e` of level `m`, as a point of the groupoid. -/
abbrev ptAt (u : P →ₐ[A'] C') {m : ℕ} (e : C' →ₐ[A'] cech A' C' m) :
    G.Pt (nerve (A' := A') hκ C' hC m) :=
  ⟨e.comp u⟩

omit D in
/-- The pullback of an arrow `r'` over level `1` along `g`, as a morphism between the lifted
points at the vertices. -/
def pullH {u : P →ₐ[A'] C'} (r' : G.arr.obj (nerve (A' := A') hκ C' hC 1))
    (hs : G.src r' = (v₀ A' C' 1).comp u) (ht : G.tgt r' = (vₗ A' C' 1).comp u) {m : ℕ}
    (g : cech A' C' 1 →ₐ[A'] cech A' C' m) {e e' : C' →ₐ[A'] cech A' C' m}
    (h₀ : g.comp (v₀ A' C' 1) = e) (h₁ : g.comp (vₗ A' C' 1) = e') :
    ptAt (G := G) (hκ := hκ) (hC := hC) u e ⟶ ptAt (G := G) (hκ := hκ) (hC := hC) u e' :=
  G.toHom (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g).top r')
    (by rw [G.src_map, hs, ← h₀]; rfl) (by rw [G.tgt_map, ht, ← h₁]; rfl)

omit D in
/-- **The defect** of an arrow over level `1` from `v₀ ∘ u` to `vₗ ∘ u`: the automorphism
`r₁₂ ∘ r₀₁ ∘ r₀₂⁻¹` of the lifted point at the last vertex of level `2`. -/
noncomputable def defectH {u : P →ₐ[A'] C'} (r' : G.arr.obj (nerve (A' := A') hκ C' hC 1))
    (hs : G.src r' = (v₀ A' C' 1).comp u) (ht : G.tgt r' = (vₗ A' C' 1).comp u) :
    ptAt (G := G) (hκ := hκ) (hC := hC) u (vₗ A' C' 2) ⟶
      ptAt (G := G) (hκ := hκ) (hC := hC) u (vₗ A' C' 2) :=
  (CategoryTheory.Groupoid.inv (pullH (I := I) (hI := hI) (m := 2) r' hs ht (face A' C' 1 1)
      (e := v₀ A' C' 2) (AlgHom.ext fun _ ↦ rfl) (AlgHom.ext fun _ ↦ rfl)) ≫
    pullH (I := I) (hI := hI) (m := 2) r' hs ht (face A' C' 1 2)
      (e' := (GroupoidLift.κ A' C' 1).comp (v₀ A' C' 1))
      (AlgHom.ext fun _ ↦ rfl) (AlgHom.ext fun _ ↦ rfl)) ≫
    pullH (I := I) (hI := hI) (m := 2) r' hs ht (face A' C' 1 0) (AlgHom.ext fun _ ↦ rfl)
      (AlgHom.ext fun _ ↦ rfl)

omit D in
/-- A vanishing defect is the cocycle condition. -/
theorem cocycle_of_defectH {u : P →ₐ[A'] C'} (r' : G.arr.obj (nerve (A' := A') hκ C' hC 1))
    (hs : G.src r' = (v₀ A' C' 1).comp u) (ht : G.tgt r' = (vₗ A' C' 1).comp u)
    (h : defectH (I := I) (hI := hI) r' hs ht = 𝟙 _) :
    ∃ h' : G.src (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI)
          (face A' C' 1 0)).top r') =
        G.tgt (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' 1 2)).top r'),
      G.comp (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' 1 0)).top r')
        (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' 1 2)).top r') h' =
        G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' 1 1)).top r' := by
  unfold defectH at h
  rw [CategoryTheory.Groupoid.inv_eq_inv, Category.assoc, IsIso.inv_comp_eq,
    Category.comp_id] at h
  exact ⟨_, congrArg Subtype.val h⟩

/-- The defect of a lift of a cocycle descent arrow reduces to the identity. -/
theorem map_q_defectH {u : P →ₐ[A'] C'} {r' : G.arr.obj (nerve (A' := A') hκ C' hC 1)}
    (hs : G.src r' = (v₀ A' C' 1).comp u) (ht : G.tgt r' = (vₗ A' C' 1).comp u)
    (hrq : G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 1)).q r' = D.rbar)
    (hcoc : D.IsCocycle) :
    G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 2)).q (defectH (I := I) (hI := hI) r' hs ht).1 =
      G.idt (D.wAt (vₗ A' C' 2)) := by
  obtain ⟨h, hc⟩ := hcoc
  have e : ∀ g : cech A' C' 1 →ₐ[A'] cech A' C' 2,
      G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 2)).q
        (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g).top r') =
      G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g).bot D.rbar := fun g ↦ by
    rw [map_q_map_top, hrq]
  simp only [defectH, pullH, Groupoid.map_comp_val, Groupoid.map_inv_val, Groupoid.toHom_val]
  refine (G.comp_comp_inv_idt _ _ (e _) (e _) (e _) h hc).trans (congrArg G.idt ?_)
  rw [G.tgt_map, D.tgt_rbar]
  exact (D.Th_bot_wAt _ _).trans (congrArg D.wAt (face_comp_vₗ 1 0 (Nat.zero_le _)))

/-! ### Morphisms of the groupoid of points along the nerve -/

omit D in
/-- The pullback of a morphism of lifted points along a map of the nerve. -/
def mapPt {u : P →ₐ[A'] C'} {m k : ℕ} (g : cech A' C' m →ₐ[A'] cech A' C' k)
    {e e' : C' →ₐ[A'] cech A' C' m} {e₂ e₂' : C' →ₐ[A'] cech A' C' k} (h : g.comp e = e₂)
    (h' : g.comp e' = e₂')
    (φ : ptAt (G := G) (hκ := hκ) (hC := hC) u e ⟶ ptAt (G := G) (hκ := hκ) (hC := hC) u e') :
    ptAt (G := G) (hκ := hκ) (hC := hC) u e₂ ⟶ ptAt (G := G) (hκ := hκ) (hC := hC) u e₂' :=
  G.toHom (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g).top φ.1)
    (by rw [G.src_map, φ.2.1, ← h]; rfl) (by rw [G.tgt_map, φ.2.2, ← h']; rfl)

omit D in
/-- `mapPt` preserves composition. -/
theorem mapPt_comp {u : P →ₐ[A'] C'} {m k : ℕ} (g : cech A' C' m →ₐ[A'] cech A' C' k)
    {e e' e'' : C' →ₐ[A'] cech A' C' m} {e₂ e₂' e₂'' : C' →ₐ[A'] cech A' C' k}
    (h : g.comp e = e₂) (h' : g.comp e' = e₂') (h'' : g.comp e'' = e₂'')
    (φ : ptAt (G := G) (hκ := hκ) (hC := hC) u e ⟶ ptAt (G := G) (hκ := hκ) (hC := hC) u e')
    (ψ : ptAt (G := G) (hκ := hκ) (hC := hC) u e' ⟶ ptAt (G := G) (hκ := hκ) (hC := hC) u e'') :
    mapPt (I := I) (hI := hI) g h h'' (φ ≫ ψ) =
      mapPt (I := I) (hI := hI) g h h' φ ≫ mapPt (I := I) (hI := hI) g h' h'' ψ :=
  Subtype.ext (G.comp_map _ _ _ _)

omit D in
/-- `mapPt` preserves inverses. -/
theorem mapPt_inv {u : P →ₐ[A'] C'} {m k : ℕ} (g : cech A' C' m →ₐ[A'] cech A' C' k)
    {e e' : C' →ₐ[A'] cech A' C' m} {e₂ e₂' : C' →ₐ[A'] cech A' C' k} (h : g.comp e = e₂)
    (h' : g.comp e' = e₂')
    (φ : ptAt (G := G) (hκ := hκ) (hC := hC) u e ⟶ ptAt (G := G) (hκ := hκ) (hC := hC) u e') :
    mapPt (I := I) (hI := hI) g h' h (CategoryTheory.Groupoid.inv φ) =
      CategoryTheory.Groupoid.inv (mapPt (I := I) (hI := hI) g h h' φ) :=
  Subtype.ext (G.inv_map _ _)

omit D in
/-- Pulling back `pullH r' g` along `g'` is `pullH r' (g' ∘ g)`. -/
theorem mapPt_pullH {u : P →ₐ[A'] C'} (r' : G.arr.obj (nerve (A' := A') hκ C' hC 1))
    (hs : G.src r' = (v₀ A' C' 1).comp u) (ht : G.tgt r' = (vₗ A' C' 1).comp u) {m k : ℕ}
    (g' : cech A' C' m →ₐ[A'] cech A' C' k) (g : cech A' C' 1 →ₐ[A'] cech A' C' m)
    {e e' : C' →ₐ[A'] cech A' C' m} {e₂ e₂' : C' →ₐ[A'] cech A' C' k}
    (h₀ : g.comp (v₀ A' C' 1) = e) (h₁ : g.comp (vₗ A' C' 1) = e')
    (h : g'.comp e = e₂) (h' : g'.comp e' = e₂') (g₂ : cech A' C' 1 →ₐ[A'] cech A' C' k)
    (hg : g'.comp g = g₂) (h₂₀ : g₂.comp (v₀ A' C' 1) = e₂) (h₂₁ : g₂.comp (vₗ A' C' 1) = e₂') :
    mapPt (I := I) (hI := hI) g' h h' (pullH (I := I) (hI := hI) r' hs ht g h₀ h₁) =
      pullH (I := I) (hI := hI) r' hs ht g₂ h₂₀ h₂₁ := by
  subst hg
  exact Subtype.ext (map_top_Th_Th _ _ _)

omit D in
/-- `pullH` along equal maps agree. -/
theorem pullH_congr {u : P →ₐ[A'] C'} (r' : G.arr.obj (nerve (A' := A') hκ C' hC 1))
    (hs : G.src r' = (v₀ A' C' 1).comp u) (ht : G.tgt r' = (vₗ A' C' 1).comp u) {m : ℕ}
    {g g' : cech A' C' 1 →ₐ[A'] cech A' C' m} {e e' : C' →ₐ[A'] cech A' C' m}
    (h₀ : g.comp (v₀ A' C' 1) = e) (h₁ : g.comp (vₗ A' C' 1) = e')
    (h₀' : g'.comp (v₀ A' C' 1) = e) (h₁' : g'.comp (vₗ A' C' 1) = e') (hg : g = g') :
    pullH (I := I) (hI := hI) r' hs ht g h₀ h₁ = pullH (I := I) (hI := hI) r' hs ht g' h₀' h₁' := by
  subst hg
  rfl

/-- An infinitesimal automorphism at a vertex, as an automorphism of the lifted point. -/
noncomputable def infH {m : ℕ} (f : C' →ₐ[A'] cech A' C' m) {E : Q →ₗ[A'] cech A' C' m}
    (hE : E ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV) :
    ptAt (G := G) (hκ := hκ) (hC := hC) u f ⟶ ptAt (G := G) (hκ := hκ) (hC := hC) u f :=
  G.toHom (D.infAt sV tV εbar hε hb hu f hE) (D.src_infAt sV tV εbar hsV hε hb hu f hE)
    (D.tgt_infAt sV tV εbar htV hε hb hu f hE)

/-- `infH` of equal derivations agree. -/
theorem infH_congr {m : ℕ} (f : C' →ₐ[A'] cech A' C' m) {E E₁ : Q →ₗ[A'] cech A' C' m}
    (hE : E ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV)
    (hE₁ : E₁ ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV) (h : E = E₁) :
    D.infH sV tV εbar hsV htV hε hb hu f hE = D.infH sV tV εbar hsV htV hε hb hu f hE₁ := by
  subst h
  rfl

/-- The composite `infH E₂ ≫ infH E₁` is `infH (E₁ + E₂)`. -/
theorem infH_comp {m : ℕ} (f : C' →ₐ[A'] cech A' C' m) {E₁ E₂ : Q →ₗ[A'] cech A' C' m}
    (hE₁ : E₁ ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV)
    (hE₂ : E₂ ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV) :
    D.infH sV tV εbar hsV htV hε hb hu f hE₂ ≫ D.infH sV tV εbar hsV htV hε hb hu f hE₁ =
      D.infH sV tV εbar hsV htV hε hb hu f (add_mem hE₁ hE₂) :=
  Subtype.ext (D.comp_infAt sV tV εbar hsV htV hε hb hu f hE₁ hE₂ _)

/-- The infinitesimal automorphism of the zero derivation is the identity. -/
theorem infH_zero {m : ℕ} (f : C' →ₐ[A'] cech A' C' m) :
    D.infH sV tV εbar hsV htV hε hb hu f
      (zero_mem (K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV)) = 𝟙 _ :=
  Subtype.ext (infOf_zero b hb sV tV _ _)

/-- The infinitesimal automorphism of `-E` is the inverse of that of `E`. -/
theorem infH_neg {m : ℕ} (f : C' →ₐ[A'] cech A' C' m) {E : Q →ₗ[A'] cech A' C' m}
    (hE : E ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV) :
    D.infH sV tV εbar hsV htV hε hb hu f (neg_mem hE) =
      CategoryTheory.Groupoid.inv (D.infH sV tV εbar hsV htV hε hb hu f hE) := by
  rw [CategoryTheory.Groupoid.inv_eq_inv]
  refine IsIso.eq_inv_of_hom_inv_id ?_
  rw [infH_comp, D.infH_congr sV tV εbar hsV htV hε hb hu f _ (zero_mem _) (neg_add_cancel E),
    infH_zero]

/-- `infH` determines its derivation. -/
theorem infH_injective {m : ℕ} (f : C' →ₐ[A'] cech A' C' m) {E₁ E₂ : Q →ₗ[A'] cech A' C' m}
    (hE₁ : E₁ ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV)
    (hE₂ : E₂ ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV)
    (h : D.infH sV tV εbar hsV htV hε hb hu f hE₁ = D.infH sV tV εbar hsV htV hε hb hu f hE₂) :
    E₁ = E₂ :=
  D.infAt_injective sV tV εbar hε hb hu f hE₁ hE₂ (congrArg Subtype.val h)

/-- Pulling back `infH E` at `f` along `g` gives `infH` at `g ∘ f` of the postcomposed
derivation. -/
theorem mapPt_infH {m k : ℕ} (g : cech A' C' m →ₐ[A'] cech A' C' k) (f : C' →ₐ[A'] cech A' C' m)
    {f₂ : C' →ₐ[A'] cech A' C' k} (hf : g.comp f = f₂) {E : Q →ₗ[A'] cech A' C' m}
    (hE : E ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV)
    (hE₂ : postcomp (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g) E ∈
      K2 (thk I hI (nerve (A' := A') hκ C' hC k)) (vAt εbar f₂) sV tV) :
    mapPt (I := I) (hI := hI) g hf hf (D.infH sV tV εbar hsV htV hε hb hu f hE) =
      D.infH sV tV εbar hsV htV hε hb hu f₂ hE₂ := by
  subst hf
  exact Subtype.ext (D.map_top_infAt sV tV εbar hε hb hu g f hE)

/-- Conjugation of an infinitesimal automorphism, in the groupoid of points. -/
theorem infH_conjK {m : ℕ} {f f' : C' →ₐ[A'] cech A' C' m}
    {r' : G.arr.obj (nerve (A' := A') hκ C' hC m)} (hs : G.src r' = f.comp u)
    (ht : G.tgt r' = f'.comp u) {E : Q →ₗ[A'] cech A' C' m}
    (hE : E ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC m)) (vAt εbar f) sV tV) :
    D.infH sV tV εbar hsV htV hε hb hu f' (conjK_mem b hb sV tV hsV htV (D.chart_vAt εbar hε f)
      (D.chart_vAt εbar hε f') (D.q_comp_at hu f) (D.q_comp_at hu f') hs ht hE) =
      (CategoryTheory.Groupoid.inv (G.toHom r' hs ht) ≫
        D.infH sV tV εbar hsV htV hε hb hu f hE) ≫ G.toHom r' hs ht :=
  Subtype.ext (D.infAt_conjAt sV tV εbar hsV htV hε hb hu hs ht hE)

omit D in
/-- The top maps of `Th` compose: `Th f` then `Th g` is `Th (g ∘ f)`. -/
theorem Th_top_comp {n m k : ℕ} (g : cech A' C' m →ₐ[A'] cech A' C' k)
    (f : cech A' C' n →ₐ[A'] cech A' C' m) :
    (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) f).top ≫
      (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g).top =
      (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (g.comp f)).top :=
  rfl

omit D in
/-- Pullbacks of an arrow along the top maps of `Th g` and `Th g'` agree when `g = g'`. -/
theorem map_Th_congr {n m : ℕ} {g g' : cech A' C' n →ₐ[A'] cech A' C' m} (h : g = g')
    (r' : G.arr.obj (nerve (A' := A') hκ C' hC n)) :
    G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g).top r' =
      G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) g').top r' := by
  subst h
  rfl

/-! ### The defect is a `2`-cocycle -/

section Cocycle

variable [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] (ε₀ : Q →ₐ[A'] C')
  (hε₀ : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp ε₀ = εbar)
  {r : G.arr.obj (nerve (A' := A') hκ C' hC 1)} (hrs : G.src r = (v₀ A' C' 1).comp u)
  (hrt : G.tgt r = (vₗ A' C' 1).comp u)
  (hrq : G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 1)).q r = D.rbar)

omit D in
/-- The vertex `1` of level `3`. -/
abbrev e₁₃ : C' →ₐ[A'] cech A' C' 3 :=
  ((face A' C' 2 3).comp (face A' C' 1 2)).comp (vₗ A' C' 1)

omit D [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The pulled back arrow from the vertex `0` to the vertex `1` of level `3`. -/
noncomputable abbrev p01 : ptAt (G := G) (hκ := hκ) (hC := hC) u (v₀ A' C' 3) ⟶
    ptAt (G := G) (hκ := hκ) (hC := hC) u (e₁₃) :=
  pullH (I := I) (hI := hI) (m := 3) r hrs hrt ((face A' C' 2 3).comp (face A' C' 1 2))
    (AlgHom.ext fun _ ↦ rfl) (AlgHom.ext fun _ ↦ rfl)

omit D [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The pulled back arrow from the vertex `1` to the vertex `2` of level `3`. -/
noncomputable abbrev p12 : ptAt (G := G) (hκ := hκ) (hC := hC) u (e₁₃) ⟶
    ptAt (G := G) (hκ := hκ) (hC := hC) u ((GroupoidLift.κ A' C' 2).comp (v₀ A' C' 1)) :=
  pullH (I := I) (hI := hI) (m := 3) r hrs hrt ((face A' C' 2 3).comp (face A' C' 1 0))
    (AlgHom.ext fun _ ↦ rfl) (AlgHom.ext fun _ ↦ rfl)

omit D [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The pulled back arrow from the vertex `0` to the vertex `2` of level `3`. -/
noncomputable abbrev p02 : ptAt (G := G) (hκ := hκ) (hC := hC) u (v₀ A' C' 3) ⟶
    ptAt (G := G) (hκ := hκ) (hC := hC) u ((GroupoidLift.κ A' C' 2).comp (v₀ A' C' 1)) :=
  pullH (I := I) (hI := hI) (m := 3) r hrs hrt ((face A' C' 2 3).comp (face A' C' 1 1))
    (AlgHom.ext fun _ ↦ rfl) (AlgHom.ext fun _ ↦ rfl)

omit D [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The pulled back arrow from the vertex `1` to the vertex `3` of level `3`. -/
noncomputable abbrev p13 : ptAt (G := G) (hκ := hκ) (hC := hC) u (e₁₃) ⟶
    ptAt (G := G) (hκ := hκ) (hC := hC) u (vₗ A' C' 3) :=
  pullH (I := I) (hI := hI) (m := 3) r hrs hrt ((face A' C' 2 2).comp (face A' C' 1 0))
    (AlgHom.ext fun _ ↦ rfl) (AlgHom.ext fun _ ↦ rfl)

omit D [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The pulled back arrow from the vertex `0` to the vertex `3` of level `3`. -/
noncomputable abbrev p03 : ptAt (G := G) (hκ := hκ) (hC := hC) u (v₀ A' C' 3) ⟶
    ptAt (G := G) (hκ := hκ) (hC := hC) u (vₗ A' C' 3) :=
  pullH (I := I) (hI := hI) (m := 3) r hrs hrt ((face A' C' 2 2).comp (face A' C' 1 1))
    (AlgHom.ext fun _ ↦ rfl) (AlgHom.ext fun _ ↦ rfl)

omit D [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The pulled back arrow from the vertex `2` to the vertex `3` of level `3`. -/
noncomputable abbrev p23 : ptAt (G := G) (hκ := hκ) (hC := hC) u
    ((GroupoidLift.κ A' C' 2).comp (v₀ A' C' 1)) ⟶
      ptAt (G := G) (hκ := hκ) (hC := hC) u (vₗ A' C' 3) :=
  pullH (I := I) (hI := hI) (m := 3) r hrs hrt (GroupoidLift.κ A' C' 2) rfl (κ_comp_vₗ 2)

omit D [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The pullback of the defect along the face `0` is `p13⁻¹ ≫ p12 ≫ p23`. -/
theorem defect_face_zero :
    mapPt (I := I) (hI := hI) (k := 3) (face A' C' 2 0) (face_comp_vₗ 2 0 (Nat.zero_le _))
        (face_comp_vₗ 2 0 (Nat.zero_le _)) (defectH (I := I) (hI := hI) r hrs hrt) =
      (CategoryTheory.Groupoid.inv (p13 (I := I) (hI := hI) hrs hrt) ≫
        p12 (I := I) (hI := hI) hrs hrt) ≫ p23 (I := I) (hI := hI) hrs hrt := by
  apply Subtype.ext
  simp only [mapPt, defectH, pullH, Groupoid.toHom_val, Groupoid.comp_val, Groupoid.inv_val,
    Groupoid.comp_map, Groupoid.inv_map, Groupoid.map_map, Th_top_comp]
  exact G.comp_comp_inv_congr _ _ _ _ (map_Th_congr face_two_zero_comp_face_one_zero r)
    (map_Th_congr face_two_zero_comp_face_one_two r)
    (map_Th_congr face_two_zero_comp_face_one_one r)

omit D [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The pullback of the defect along the face `1` is `p03⁻¹ ≫ p02 ≫ p23`. -/
theorem defect_face_one :
    mapPt (I := I) (hI := hI) (k := 3) (face A' C' 2 1) (face_comp_vₗ 2 1 (by decide))
        (face_comp_vₗ 2 1 (by decide)) (defectH (I := I) (hI := hI) r hrs hrt) =
      (CategoryTheory.Groupoid.inv (p03 (I := I) (hI := hI) hrs hrt) ≫
        p02 (I := I) (hI := hI) hrs hrt) ≫ p23 (I := I) (hI := hI) hrs hrt := by
  apply Subtype.ext
  simp only [mapPt, defectH, pullH, Groupoid.toHom_val, Groupoid.comp_val, Groupoid.inv_val,
    Groupoid.comp_map, Groupoid.inv_map, Groupoid.map_map, Th_top_comp]
  exact G.comp_comp_inv_congr _ _ _ _ (map_Th_congr face_two_one_comp_face_one_zero r)
    (map_Th_congr face_two_one_comp_face_one_two r) (map_Th_congr face_two_one_comp_face_one_one r)

omit D [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The pullback of the defect along the face `2` is `p03⁻¹ ≫ p01 ≫ p13`. -/
theorem defect_face_two :
    mapPt (I := I) (hI := hI) (k := 3) (face A' C' 2 2) (face_comp_vₗ 2 2 (by decide))
        (face_comp_vₗ 2 2 (by decide)) (defectH (I := I) (hI := hI) r hrs hrt) =
      (CategoryTheory.Groupoid.inv (p03 (I := I) (hI := hI) hrs hrt) ≫
        p01 (I := I) (hI := hI) hrs hrt) ≫ p13 (I := I) (hI := hI) hrs hrt := by
  apply Subtype.ext
  simp only [mapPt, defectH, pullH, Groupoid.toHom_val, Groupoid.comp_val, Groupoid.inv_val,
    Groupoid.comp_map, Groupoid.inv_map, Groupoid.map_map, Th_top_comp]
  exact G.comp_comp_inv_congr _ _ _ _ (map_Th_congr rfl r)
    (map_Th_congr face_two_two_comp_face_one_two r) (map_Th_congr rfl r)

omit D [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The pullback of the defect along the last face is `p02⁻¹ ≫ p01 ≫ p12`. -/
theorem defect_face_last :
    mapPt (I := I) (hI := hI) (k := 3) (face A' C' 2 (Fin.last 3)) (face_last_comp_vₗ 2)
        (face_last_comp_vₗ 2) (defectH (I := I) (hI := hI) r hrs hrt) =
      (CategoryTheory.Groupoid.inv (p02 (I := I) (hI := hI) hrs hrt) ≫
        p01 (I := I) (hI := hI) hrs hrt) ≫ p12 (I := I) (hI := hI) hrs hrt := by
  apply Subtype.ext
  simp only [mapPt, defectH, pullH, Groupoid.toHom_val, Groupoid.comp_val, Groupoid.inv_val,
    Groupoid.comp_map, Groupoid.inv_map, Groupoid.map_map, Th_top_comp]
  exact G.comp_comp_inv_congr _ _ _ _ (map_Th_congr rfl r) (map_Th_congr rfl r)
    (map_Th_congr rfl r)

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- If `E` represents the defect, then `infFacePlain 2 j E` represents the pullback of the
defect along the face `j.castSucc`. -/
theorem infH_facePlain_defect (j : Fin 3) (E : N (hI := hI) sV tV εbar 2)
    (hE : D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 2) E.2 =
      defectH (I := I) (hI := hI) r hrs hrt) :
    D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 3) (infFacePlain sV tV εbar 2 j E).2 =
      mapPt (I := I) (hI := hI) (k := 3) (face A' C' 2 j.castSucc)
        (face_comp_vₗ 2 j.castSucc (by simp; omega)) (face_comp_vₗ 2 j.castSucc (by simp; omega))
        (defectH (I := I) (hI := hI) r hrs hrt) := by
  rw [← hE]
  exact (D.mapPt_infH sV tV εbar hsV htV hε hb hu (face A' C' 2 j.castSucc) (vₗ A' C' 2)
    (face_comp_vₗ 2 j.castSucc (by simp; omega)) E.2 _).symm

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- If `E` represents the defect, then `infFaceLast 2 E` represents the conjugate by `p23` of
the pullback of the defect along the last face. -/
theorem infH_faceLast_defect (E : N (hI := hI) sV tV εbar 2)
    (hE : D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 2) E.2 =
      defectH (I := I) (hI := hI) r hrs hrt) :
    D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 3)
        (D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt 2 E).2 =
      (CategoryTheory.Groupoid.inv (p23 (I := I) (hI := hI) hrs hrt) ≫
        ((CategoryTheory.Groupoid.inv (p02 (I := I) (hI := hI) hrs hrt) ≫
          p01 (I := I) (hI := hI) hrs hrt) ≫ p12 (I := I) (hI := hI) hrs hrt)) ≫
        p23 (I := I) (hI := hI) hrs hrt := by
  have h := D.infH_conjK sV tV εbar hsV htV hε hb hu (src_rAt (I := I) (hI := hI) hrs 2)
    (tgt_rAt (I := I) (hI := hI) hrt 2) (postcomp_mem_K2 sV tV _ (hv_last εbar 2) E.2)
  rw [← D.mapPt_infH sV tV εbar hsV htV hε hb hu (face A' C' 2 (Fin.last (2 + 1))) (vₗ A' C' 2)
    (face_last_comp_vₗ 2) E.2, hE] at h
  rwa [← defect_face_last]

include hrq in
/-- **The defect is a `2`-cocycle** of the twisted Čech complex of infinitesimal
automorphisms. -/
theorem diff_two_defect (E : N (hI := hI) sV tV εbar 2)
    (hE : D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 2) E.2 =
      defectH (I := I) (hI := hI) r hrs hrt) :
    (D.infDecalage sV tV εbar hsV htV ε₀ hε₀ hε hb hu hrs hrt hrq).diff 2 E = 0 := by
  rw [Stacks.Decalage.diff_two_apply]
  have h0 : (D.infDecalage sV tV εbar hsV htV ε₀ hε₀ hε hb hu hrs hrt hrq).face 2 0 E =
      infFacePlain sV tV εbar 2 0 E :=
    congrArg (· E) (D.infFace_castSucc sV tV εbar hsV htV hε hb hu hrs hrt 2 0)
  have h1 : (D.infDecalage sV tV εbar hsV htV ε₀ hε₀ hε hb hu hrs hrt hrq).face 2 1 E =
      infFacePlain sV tV εbar 2 1 E :=
    congrArg (· E) (D.infFace_castSucc sV tV εbar hsV htV hε hb hu hrs hrt 2 1)
  have h2 : (D.infDecalage sV tV εbar hsV htV ε₀ hε₀ hε hb hu hrs hrt hrq).face 2 2 E =
      infFacePlain sV tV εbar 2 2 E :=
    congrArg (· E) (D.infFace_castSucc sV tV εbar hsV htV hε hb hu hrs hrt 2 2)
  have h3 : (D.infDecalage sV tV εbar hsV htV ε₀ hε₀ hε hb hu hrs hrt hrq).face 2 3 E =
      D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt 2 E :=
    congrArg (· E) (D.infFace_last sV tV εbar hsV htV hε hb hu hrs hrt 2)
  rw [h0, h1, h2, h3]
  set F0 := infFacePlain sV tV εbar 2 0 E
  set F1 := infFacePlain sV tV εbar 2 1 E
  set F2 := infFacePlain sV tV εbar 2 2 E
  set F3 := D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt 2 E
  have hW0 : D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 3) F0.2 = _ :=
    (D.infH_facePlain_defect sV tV εbar hsV htV hε hb hu hrs hrt 0 E hE).trans
      (defect_face_zero hrs hrt)
  have hW1 : D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 3) F1.2 = _ :=
    (D.infH_facePlain_defect sV tV εbar hsV htV hε hb hu hrs hrt 1 E hE).trans
      (defect_face_one hrs hrt)
  have hW2 : D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 3) F2.2 = _ :=
    (D.infH_facePlain_defect sV tV εbar hsV htV hε hb hu hrs hrt 2 E hE).trans
      (defect_face_two hrs hrt)
  have hW3 := D.infH_faceLast_defect sV tV εbar hsV htV hε hb hu hrs hrt E hE
  have key : D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 3) (F0 + F2).2 =
      D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 3) (F3 + F1).2 := by
    calc D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 3) (F0 + F2).2
        = D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 3) F2.2 ≫
            D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 3) F0.2 :=
          (D.infH_comp sV tV εbar hsV htV hε hb hu _ F0.2 F2.2).symm
      _ = _ := by rw [hW2, hW0]
      _ = _ := CategoryTheory.Groupoid.defect_word _ _ _ _ _ _
      _ = D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 3) F1.2 ≫
            D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 3) F3.2 := by rw [hW1, hW3]
      _ = D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 3) (F3 + F1).2 :=
          D.infH_comp sV tV εbar hsV htV hε hb hu _ F3.2 F1.2
  have hsum : F0 + F2 = F3 + F1 :=
    Subtype.ext (D.infH_injective sV tV εbar hsV htV hε hb hu _ _ _ key)
  rw [show F0 - F1 + F2 - F3 = (F0 + F2) - (F3 + F1) by abel, hsum, sub_self]

omit D [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The lifted descent arrow, as a morphism of lifted points. -/
abbrev liftH : ptAt (G := G) (hκ := hκ) (hC := hC) u (v₀ A' C' 1) ⟶
    ptAt (G := G) (hκ := hκ) (hC := hC) u (vₗ A' C' 1) :=
  G.toHom r hrs hrt

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
/-- The pullback of an arrow changed by an infinitesimal automorphism of its target. -/
theorem pullH_comp_infH {m : ℕ} (g : cech A' C' 1 →ₐ[A'] cech A' C' m)
    {e e' : C' →ₐ[A'] cech A' C' m} (h₀ : g.comp (v₀ A' C' 1) = e) (h₁ : g.comp (vₗ A' C' 1) = e')
    {F : Q →ₗ[A'] cech A' C' 1}
    (hF : F ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC 1)) (vAt εbar (vₗ A' C' 1)) sV tV) :
    pullH (I := I) (hI := hI) (liftH hrs hrt ≫ D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 1) hF).1
        (liftH hrs hrt ≫ D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 1) hF).2.1
        (liftH hrs hrt ≫ D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 1) hF).2.2 g h₀ h₁ =
      pullH (I := I) (hI := hI) r hrs hrt g h₀ h₁ ≫ D.infH sV tV εbar hsV htV hε hb hu e'
        (postcomp_mem_K2 sV tV _ ((Th_bot_vAt εbar g (vₗ A' C' 1)).trans
          (congrArg (vAt εbar) h₁)) hF) := by
  have h := mapPt_comp (I := I) (hI := hI) g h₀ h₁ h₁ (liftH hrs hrt)
    (D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 1) hF)
  rwa [D.mapPt_infH sV tV εbar hsV htV hε hb hu g (vₗ A' C' 1) h₁ hF] at h

omit [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.Flat A' C'] in
include hrq in
/-- Changing the lifted descent arrow by an infinitesimal automorphism of its target does not
change its reduction `D.rbar`. -/
theorem map_q_comp_infH {F : Q →ₗ[A'] cech A' C' 1}
    (hF : F ∈ K2 (thk I hI (nerve (A' := A') hκ C' hC 1)) (vAt εbar (vₗ A' C' 1)) sV tV) :
    G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 1)).q
      (liftH hrs hrt ≫ D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 1) hF).1 = D.rbar := by
  rw [Groupoid.comp_val, G.comp_map]
  refine (G.comp_eq' (map_infOf b hb sV tV _ _ hF) hrq _ ?_).trans ?_
  · rw [G.src_idt, D.tgt_rbar]
  · refine (G.comp_eq' (congrArg G.idt ?_) rfl _ (G.src_idt _)).trans (G.idt_comp _)
    exact D.tgt_rbar.symm

end Cocycle

/-! ### The second-order step -/

section SecondOrder

variable [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]
  [Module.FaithfullyFlat A' C'] (ε₀ : Q →ₐ[A'] C')
  (hε₀ : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp ε₀ = εbar)
  {r : G.arr.obj (nerve (A' := A') hκ C' hC 1)} (hrs : G.src r = (v₀ A' C' 1).comp u)
  (hrt : G.tgt r = (vₗ A' C' 1).comp u)
  (hrq : G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 1)).q r = D.rbar)

include sV tV εbar hsV htV hε hb hu hrs hrt hrq ε₀ hε₀ in
/-- **Correcting the lifted descent arrow**: a lift of a cocycle descent arrow between lifted
points can be changed, by an infinitesimal automorphism of its target, into a lift satisfying
the cocycle condition exactly. -/
theorem exists_cocycle_of_lift (hcoc : D.IsCocycle) :
    ∃ (r' : G.arr.obj (nerve (A' := A') hκ C' hC 1)) (hs : G.src r' = (v₀ A' C' 1).comp u)
      (ht : G.tgt r' = (vₗ A' C' 1).comp u),
      G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 1)).q r' = D.rbar ∧
        defectH (I := I) (hI := hI) r' hs ht = 𝟙 _ := by
  let T := D.infDecalage sV tV εbar hsV htV ε₀ hε₀ hε hb hu hrs hrt hrq
  obtain ⟨Eδ, hEδ, hEq⟩ := D.exists_infAt_eq sV tV εbar hsV htV hε hb hu (vₗ A' C' 2)
    (defectH (I := I) (hI := hI) r hrs hrt).2.1 (defectH (I := I) (hI := hI) r hrs hrt).2.2
    (D.map_q_defectH hrs hrt hrq hcoc)
  let x : N (hI := hI) sV tV εbar 2 := ⟨Eδ, hEδ⟩
  have hx : D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 2) x.2 =
      defectH (I := I) (hI := hI) r hrs hrt := Subtype.ext hEq
  obtain ⟨y, hy⟩ := T.exists_diff_eq 1 x
    (D.diff_two_defect sV tV εbar hsV htV hε hb hu ε₀ hε₀ hrs hrt hrq x hx)
  rw [Stacks.Decalage.diff_one_apply] at hy
  refine ⟨_, (liftH hrs hrt ≫ D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 1) (neg_mem y.2)).2.1,
    (liftH hrs hrt ≫ D.infH sV tV εbar hsV htV hε hb hu (vₗ A' C' 1) (neg_mem y.2)).2.2,
    D.map_q_comp_infH sV tV εbar hsV htV hε hb hu hrs hrt hrq (neg_mem y.2), ?_⟩
  have e0 : (D.infDecalage sV tV εbar hsV htV ε₀ hε₀ hε hb hu hrs hrt hrq).face 1 0 (-y) =
      infFacePlain sV tV εbar 1 0 (-y) :=
    congrArg (· (-y)) (D.infFace_castSucc sV tV εbar hsV htV hε hb hu hrs hrt 1 0)
  have e1 : (D.infDecalage sV tV εbar hsV htV ε₀ hε₀ hε hb hu hrs hrt hrq).face 1 1 (-y) =
      infFacePlain sV tV εbar 1 1 (-y) :=
    congrArg (· (-y)) (D.infFace_castSucc sV tV εbar hsV htV hε hb hu hrs hrt 1 1)
  have e2 : (D.infDecalage sV tV εbar hsV htV ε₀ hε₀ hε hb hu hrs hrt hrq).face 1 2 (-y) =
      D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt 1 (-y) :=
    congrArg (· (-y)) (D.infFace_last sV tV εbar hsV htV hε hb hu hrs hrt 1)
  have hN : infFacePlain sV tV εbar 1 0 (-y) +
      D.infFaceLast sV tV εbar hsV htV hε hb hu hrs hrt 1 (-y) + x +
      -infFacePlain sV tV εbar 1 1 (-y) = 0 := by
    rw [← e0, ← e1, ← e2, map_neg, map_neg, map_neg, ← hy]
    abel
  have hC := D.infH_conjK sV tV εbar hsV htV hε hb hu (src_rAt (I := I) (hI := hI) hrs 1)
    (tgt_rAt (I := I) (hI := hI) hrt 1) (postcomp_mem_K2 sV tV _ (hv_last εbar 1) (neg_mem y.2))
  unfold defectH
  rw [D.pullH_comp_infH sV tV εbar hsV htV hε hb hu hrs hrt (face A' C' 1 1) _ _ (neg_mem y.2),
    D.pullH_comp_infH sV tV εbar hsV htV hε hb hu hrs hrt (face A' C' 1 2) _ _ (neg_mem y.2),
    D.pullH_comp_infH sV tV εbar hsV htV hε hb hu hrs hrt (face A' C' 1 0) _ _ (neg_mem y.2),
    CategoryTheory.Groupoid.defect_change_word' hx.symm hC.symm, ← infH_neg, infH_comp,
    infH_comp, infH_comp]
  exact (D.infH_congr sV tV εbar hsV htV hε hb hu (vₗ A' C' 2) _ (zero_mem _)
    (congrArg Subtype.val hN)).trans (D.infH_zero sV tV εbar hsV htV hε hb hu _)

include sV tV εbar hsV htV hε hb ε₀ hε₀ in
/-- **The second-order step.** A cocycle descent arrow lifts, after a change of the lift of the
point, to an arrow from `v₀ ∘ u` to `vₗ ∘ u` satisfying the cocycle condition exactly. -/
theorem exists_lift_arrow_cocycle (hG : G.SrcFormallySmooth) (hcoc : D.IsCocycle) :
    ∃ (u : P →ₐ[A'] C') (_ : (thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom.comp u = D.ubar)
      (r : G.arr.obj (nerve (A' := A') hκ C' hC 1)),
      G.arr.map (thk I hI (nerve (A' := A') hκ C' hC 1)).q r = D.rbar ∧
        G.src r = (v₀ A' C' 1).comp u ∧ G.tgt r = (vₗ A' C' 1).comp u ∧
        ∃ h : G.src (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI)
            (face A' C' 1 0)).top r) = G.tgt (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I)
              (hI := hI) (face A' C' 1 2)).top r),
          G.comp (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' 1 0)).top r)
            (G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' 1 2)).top r) h =
            G.arr.map (Th (hκ := hκ) (hC := hC) (I := I) (hI := hI) (face A' C' 1 1)).top r := by
  obtain ⟨u, hu, r, hrq, hrs, hrt⟩ := D.exists_lift_arrow hG hb hsV htV εbar ε₀ hε₀ hε hcoc
  obtain ⟨r', hs', ht', hq', hd⟩ :=
    D.exists_cocycle_of_lift sV tV εbar hsV htV hε hb hu ε₀ hε₀ hrs hrt hrq hcoc
  exact ⟨u, hu, r', hq', hs', ht', cocycle_of_defectH r' hs' ht' hd⟩

end SecondOrder


end NerveDatum

end AlgebraicGeometry.Stack.GroupoidLift

end
