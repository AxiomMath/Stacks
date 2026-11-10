module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Finiteness.Projective

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Stacks Tag 0F80 (Lemma 15.98.7, "More on Algebra", section "Perfect complexes
and the eta operator").

Let `A` be a commutative ring. Let `M`, `N₁`, `N₂` be finite projective
`A`-modules, and write `N = N₁ ⊕ N₂`. Let `s : M → N₁ ⊕ N₂` be a split
injection (it admits an `A`-linear left inverse). Then there exists a finitely
generated ideal `J ⊆ A` such that for every commutative ring `B` and every ring
map `A → B`, the map `A → B` factors through the quotient `A/J` (equivalently
`J ⊆ ker(A → B)`) if and only if the base-changed map

  s ⊗ id_B : M ⊗_A B → (N₁ ⊗_A B) ⊕ (N₂ ⊗_A B)

identifies `M ⊗_A B` with a direct sum of submodules of
`(N₁ ⊗_A B) ⊕ (N₂ ⊗_A B)` (Definition 4 below).

## Modelling choices

* We model `N = N₁ ⊕ N₂` as the product type `N₁ × N₂`, which carries the
  external direct sum structure; for two summands the product and the direct
  sum coincide.
* Base change of an `A`-linear map `f : P → Q` along a ring map `A → B` (an
  `A`-algebra structure on `B`) is `LinearMap.baseChange B f`, an `B`-linear
  map `B ⊗[A] P → B ⊗[A] Q`. We write `M_B = B ⊗[A] M`, etc.  Note that
  `LinearMap.baseChange` places the scalar ring on the left of the tensor
  product, so `M_B = B ⊗[A] M` (canonically isomorphic to the `M ⊗_A B` of the
  informal statement).
* The coordinate projectors `q₁, q₂ : N₁ × N₂ → N₁ × N₂` of Definition 3 are
  the idempotent endomorphisms projecting onto each summand.  After base change
  they become `LinearMap.baseChange B qᵢ`, and the submodule `N_{i,B} ⊆ N_B`
  is `range (LinearMap.baseChange B qᵢ)`.
* "Factors through `A/J`" is modelled as `J ≤ RingHom.ker (algebraMap A B)`,
  i.e. every element of `J` maps to `0` in `B`.
-/

open TensorProduct

namespace Stacks.SplitInjectionDirectSum

/- Universe of the test rings `B` quantified over in Remark 4 and in Tag 0F80 itself:
the Stacks statement says "for every commutative ring `B`", so `B` must not be pinned to
`Type 0`.  It is named rather than written `Type*` so that the statements quantifying over
`B` share a single level. -/
universe v

variable {A : Type*} [CommRing A]
variable {M N₁ N₂ : Type*}
  [AddCommGroup M] [Module A M]
  [AddCommGroup N₁] [Module A N₁]
  [AddCommGroup N₂] [Module A N₂]

/-- Definition 3 (coordinate projector onto the first summand): the idempotent
endomorphism of `N₁ × N₂` given by projecting onto `N₁` and re-including it. -/
noncomputable def q₁ : (N₁ × N₂) →ₗ[A] (N₁ × N₂) :=
  (LinearMap.inl A N₁ N₂).comp (LinearMap.fst A N₁ N₂)

/-- Definition 3 (coordinate projector onto the second summand). -/
noncomputable def q₂ : (N₁ × N₂) →ₗ[A] (N₁ × N₂) :=
  (LinearMap.inr A N₁ N₂).comp (LinearMap.snd A N₁ N₂)

/-- The coordinate projectors sum to the identity. -/
theorem q₁_add_q₂ : (q₁ : (N₁ × N₂) →ₗ[A] _) + q₂ = LinearMap.id :=
  LinearMap.ext fun x => by simp [q₁, q₂]

/-- `q₁` is idempotent. -/
theorem q₁_comp_q₁ : (q₁ : (N₁ × N₂) →ₗ[A] _) ∘ₗ q₁ = q₁ :=
  LinearMap.ext fun x => by simp [q₁]

/-- `q₂` is idempotent. -/
theorem q₂_comp_q₂ : (q₂ : (N₁ × N₂) →ₗ[A] _) ∘ₗ q₂ = q₂ :=
  LinearMap.ext fun x => by simp [q₂]

/-- `q₂` kills the image of `q₁`. -/
theorem q₂_comp_q₁ : (q₂ : (N₁ × N₂) →ₗ[A] _) ∘ₗ q₁ = 0 :=
  LinearMap.ext fun x => by simp [q₁, q₂]

/-- `q₁` kills the image of `q₂`. -/
theorem q₁_comp_q₂ : (q₁ : (N₁ × N₂) →ₗ[A] _) ∘ₗ q₂ = 0 :=
  LinearMap.ext fun x => by simp [q₁, q₂]

/-- If `p` is idempotent and kills the range of `p'`, then `p` maps `K ⊔ K'` into `K` whenever
`K ≤ range p` and `K' ≤ range p'`. -/
theorem apply_mem_of_mem_sup_of_le_range {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    {p p' : V →ₗ[R] V} (hpp : ∀ z, p (p z) = p z) (hpp' : ∀ z, p (p' z) = 0)
    {K K' : Submodule R V} (hK : K ≤ LinearMap.range p) (hK' : K' ≤ LinearMap.range p')
    {y : V} (hy : y ∈ K ⊔ K') : p y ∈ K := by
  obtain ⟨k, hk, k', hk', rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨a, rfl⟩ := hK hk
  obtain ⟨b, rfl⟩ := hK' hk'
  simpa [hpp, hpp'] using hk

/-- Definition 1 (split injection): an `A`-linear map `s : M → N₁ × N₂` is a
split injection if it admits an `A`-linear left inverse (a splitting). -/
def IsSplitInjective (s : M →ₗ[A] (N₁ × N₂)) : Prop :=
  ∃ π : (N₁ × N₂) →ₗ[A] M, π.comp s = LinearMap.id

/-- Definition 4 ("identifies `M_B` with a direct sum of submodules"). For a
ring map `A → B` (i.e. an `A`-algebra structure on `B`), the base-changed map
`s_B : M_B → N_{1,B} ⊕ N_{2,B}` identifies `M_B` with a direct sum of
submodules if there exist `B`-submodules `K₁ ⊆ N_{1,B}` and `K₂ ⊆ N_{2,B}`
such that the image `s_B(M_B)` equals the internal direct sum `K₁ ⊕ K₂`
(i.e. `K₁ ⊔ K₂ = range s_B` and `K₁`, `K₂` are disjoint).  Here `N_{i,B}` is
the range of the base-changed coordinate projector `qᵢ`. -/
def IdentifiesDirectSum (s : M →ₗ[A] (N₁ × N₂))
    (B : Type*) [CommRing B] [Algebra A B] : Prop :=
  ∃ (K₁ K₂ : Submodule B (B ⊗[A] (N₁ × N₂))),
    K₁ ≤ LinearMap.range (LinearMap.baseChange B (q₁ (N₁ := N₁) (N₂ := N₂))) ∧
    K₂ ≤ LinearMap.range (LinearMap.baseChange B (q₂ (N₁ := N₁) (N₂ := N₂))) ∧
    Disjoint K₁ K₂ ∧
    K₁ ⊔ K₂ = LinearMap.range (s.baseChange B)

/-! ## Auxiliary data for the proof

Fix a splitting `π` of `s`.  Set `e = s ∘ π`, an idempotent endomorphism of
`N₁ × N₂` whose image is `s(M)`.  The "obstruction" maps are
`fMap s π qᵢ = (id − e) ∘ qᵢ ∘ s : M →ₗ[A] (N₁ × N₂)` for `i = 1, 2`; by Remark 2,
`range(s_B)` is stable under the coordinate projector `q_{i,B}` iff
`fMap s π qᵢ ⊗ id_B = 0`. -/

/-- The obstruction map `(id − e) ∘ q ∘ s : M →ₗ[A] (N₁ × N₂)` attached to an endomorphism `q`
of `N₁ × N₂`, where `e = s ∘ π`. -/
noncomputable def fMap (s : M →ₗ[A] (N₁ × N₂)) (π : (N₁ × N₂) →ₗ[A] M)
    (q : (N₁ × N₂) →ₗ[A] (N₁ × N₂)) : M →ₗ[A] (N₁ × N₂) :=
  (LinearMap.id - s ∘ₗ π).comp (q.comp s)

/-- **Remark 2 (Definition 4 ⟺ stability).**  `s_B` identifies `M_B` with a
direct sum of submodules of `N_{1,B} ⊕ N_{2,B}` iff its image is stable under
both base-changed coordinate projectors.  We phrase stability via the ranges:
`range (q_{i,B} ∘ s_B) ≤ range s_B` for `i = 1, 2`.

Informal proof (equivalence with Definition 4):
(⇐) If `range s_B = K₁ ⊔ K₂` with `Kᵢ ≤ range q_{i,B}` and `K₁`, `K₂` disjoint,
then because `q_{1,B} + q_{2,B} = id` and the `Kᵢ` live in complementary
summands, `q_{i,B}` restricted to `range s_B` is the projection onto `Kᵢ ≤
range s_B`; hence the image is stable.  (⇒) Conversely, set
`Kᵢ = q_{i,B}(range s_B)`.  Stability gives `Kᵢ ≤ range s_B`, and obviously
`Kᵢ ≤ range q_{i,B} = N_{i,B}`.  Every `y ∈ range s_B` satisfies
`y = q_{1,B} y + q_{2,B} y ∈ K₁ + K₂`, so `K₁ ⊔ K₂ = range s_B`; and `K₁ ∩ K₂ ≤
N_{1,B} ∩ N_{2,B} = 0`, so they are disjoint.  Thus Definition 4 holds. -/
theorem identifiesDirectSum_iff_stable
    (s : M →ₗ[A] (N₁ × N₂)) (B : Type*) [CommRing B] [Algebra A B] :
    IdentifiesDirectSum s B ↔
      (LinearMap.range
          ((LinearMap.baseChange B (q₁ (N₁ := N₁) (N₂ := N₂))).comp
            (s.baseChange B)) ≤ LinearMap.range (s.baseChange B) ∧
       LinearMap.range
          ((LinearMap.baseChange B (q₂ (N₁ := N₁) (N₂ := N₂))).comp
            (s.baseChange B)) ≤ LinearMap.range (s.baseChange B)) := by
  set q₁_B := LinearMap.baseChange B (q₁ (A := A) (N₁ := N₁) (N₂ := N₂)) with hq₁_B
  set q₂_B := LinearMap.baseChange B (q₂ (A := A) (N₁ := N₁) (N₂ := N₂)) with hq₂_B
  set s_B := s.baseChange B
  set R := LinearMap.range s_B
  have hsum : ∀ z, q₁_B z + q₂_B z = z := fun z => by
    simpa using LinearMap.congr_fun (by
      rw [hq₁_B, hq₂_B, ← LinearMap.baseChange_add, q₁_add_q₂, LinearMap.baseChange_id] :
        q₁_B + q₂_B = LinearMap.id) z
  have h11 : ∀ z, q₁_B (q₁_B z) = q₁_B z := LinearMap.congr_fun
    (by rw [hq₁_B, ← LinearMap.baseChange_comp, q₁_comp_q₁] : q₁_B ∘ₗ q₁_B = q₁_B)
  have h22 : ∀ z, q₂_B (q₂_B z) = q₂_B z := LinearMap.congr_fun
    (by rw [hq₂_B, ← LinearMap.baseChange_comp, q₂_comp_q₂] : q₂_B ∘ₗ q₂_B = q₂_B)
  have h21 : ∀ z, q₂_B (q₁_B z) = 0 := LinearMap.congr_fun (by
    rw [hq₁_B, hq₂_B, ← LinearMap.baseChange_comp, q₂_comp_q₁, LinearMap.baseChange_zero] :
      q₂_B ∘ₗ q₁_B = 0)
  have h12 : ∀ z, q₁_B (q₂_B z) = 0 := LinearMap.congr_fun (by
    rw [hq₁_B, hq₂_B, ← LinearMap.baseChange_comp, q₁_comp_q₂, LinearMap.baseChange_zero] :
      q₁_B ∘ₗ q₂_B = 0)
  constructor
  · rintro ⟨K₁, K₂, hK₁, hK₂, -, hsup⟩
    change K₁ ⊔ K₂ = R at hsup
    have hy : ∀ x, s_B x ∈ K₁ ⊔ K₂ := fun x => hsup ▸ ⟨x, rfl⟩
    refine ⟨?_, ?_⟩ <;> rintro _ ⟨x, rfl⟩ <;> rw [← hsup]
    · exact Submodule.mem_sup_left (apply_mem_of_mem_sup_of_le_range h11 h12 hK₁ hK₂ (hy x))
    · exact Submodule.mem_sup_right
        (apply_mem_of_mem_sup_of_le_range h22 h21 hK₂ hK₁ (sup_comm K₁ K₂ ▸ hy x))
  · rintro ⟨hst1, hst2⟩
    have hdisj : Disjoint (LinearMap.range q₁_B) (LinearMap.range q₂_B) := by
      rw [Submodule.disjoint_def]
      rintro x ⟨a, rfl⟩ ⟨b, hb⟩
      rw [← h11 a, ← hb, h12]
    refine ⟨R.map q₁_B, R.map q₂_B, LinearMap.map_le_range, LinearMap.map_le_range,
      hdisj.mono LinearMap.map_le_range LinearMap.map_le_range, le_antisymm (sup_le ?_ ?_) ?_⟩
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact hst1 ⟨x, rfl⟩
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact hst2 ⟨x, rfl⟩
    · rintro _ ⟨x, rfl⟩
      rw [← hsum (s_B x)]
      exact Submodule.add_mem_sup (Submodule.mem_map_of_mem ⟨x, rfl⟩)
        (Submodule.mem_map_of_mem ⟨x, rfl⟩)

/-- **Remark 2 (stability ⟺ vanishing of the obstruction maps).**  Given a
splitting `π` of `s` (so `e = s ∘ π` is idempotent with image `s(M)`), the
image `range s_B` is stable under `q_{i,B}` iff `fMap π qᵢ ⊗ id_B = 0`.

Informal proof: `e_B = s_B ∘ π_B` is idempotent with image
`range s_B`, and an element `z ∈ N_B` lies in `range s_B` iff `e_B z = z`, i.e.
iff `(id − e_B) z = 0`.  Stability of `range s_B` under `q_{i,B}` says: for every
`x ∈ M_B`, `q_{i,B}(s_B x) ∈ range s_B`, i.e. `(id − e_B)(q_{i,B}(s_B x)) = 0`.
Since `(id − e_B) ∘ q_{i,B} ∘ s_B = (fMap π qᵢ) ⊗ id_B` (base change is a ring
homomorphism on `End` and commutes with `id`, `comp`, `sub`), this holds for all
`x` iff `(fMap π qᵢ) ⊗ id_B = 0`.  The key facts: `range s_B ⊆ ker(id − e_B)`
follows from `π ∘ s = id` (so `e ∘ s = s`, hence `e_B ∘ s_B = s_B`); and
`ker(id − e_B) ⊆ range s_B` because `e_B z = z ⇒ z = s_B (π_B z)`. -/
theorem stable_iff_fMap_baseChange_zero
    (s : M →ₗ[A] (N₁ × N₂)) (π : (N₁ × N₂) →ₗ[A] M)
    (hπ : π.comp s = LinearMap.id)
    (B : Type*) [CommRing B] [Algebra A B] :
    (LinearMap.range
        ((LinearMap.baseChange B (q₁ (N₁ := N₁) (N₂ := N₂))).comp
          (s.baseChange B)) ≤ LinearMap.range (s.baseChange B) ∧
     LinearMap.range
        ((LinearMap.baseChange B (q₂ (N₁ := N₁) (N₂ := N₂))).comp
          (s.baseChange B)) ≤ LinearMap.range (s.baseChange B)) ↔
      ((fMap s π (q₁ (N₁ := N₁) (N₂ := N₂))).baseChange B = 0 ∧
       (fMap s π (q₂ (N₁ := N₁) (N₂ := N₂))).baseChange B = 0) := by
  set s_B := s.baseChange B with hs_B
  set e_B := (s ∘ₗ π).baseChange B with he_B
  have heComp : e_B.comp s_B = s_B := by
    rw [he_B, hs_B, ← LinearMap.baseChange_comp, LinearMap.comp_assoc, hπ,
      LinearMap.comp_id]
  have memRange : ∀ z, z ∈ LinearMap.range s_B ↔
      (LinearMap.id (R := B) (M := B ⊗[A] (N₁ × N₂)) - e_B) z = 0 := by
    intro z
    rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    refine ⟨?_, fun h => ⟨π.baseChange B z, ?_⟩⟩
    · rintro ⟨x, rfl⟩
      exact (LinearMap.congr_fun heComp x).symm
    · rw [he_B] at h
      rw [hs_B, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      exact h.symm
  have core : ∀ q : (N₁ × N₂) →ₗ[A] (N₁ × N₂),
      LinearMap.range ((LinearMap.baseChange B q).comp s_B) ≤ LinearMap.range s_B ↔
        (fMap s π q).baseChange B = 0 := by
    intro q
    rw [fMap, LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.baseChange_sub,
      LinearMap.baseChange_id, LinearMap.range_le_iff_comap, eq_top_iff]
    exact ⟨fun h => LinearMap.ext fun x => (memRange _).mp (h Submodule.mem_top),
      fun h x _ => (memRange _).mpr (LinearMap.congr_fun h x)⟩
  rw [core (q₁ (N₁ := N₁) (N₂ := N₂)), core (q₂ (N₁ := N₁) (N₂ := N₂))]

/-- A linear map between finite free modules `Aᵃ → Aᵇ` vanishes after base change to `B` iff
all of its matrix entries map to `0` in `B`. -/
theorem baseChange_eq_zero_iff_algebraMap_apply_eq_zero {a b : ℕ} (B : Type*) [CommRing B]
    [Algebra A B] (G : (Fin a → A) →ₗ[A] (Fin b → A)) :
    G.baseChange B = 0 ↔ ∀ q p, algebraMap A B (G (Pi.single q 1) p) = 0 := by
  have key : ∀ q,
      (TensorProduct.piScalarRight A B B (Fin b)) ((1 : B) ⊗ₜ[A] (G (Pi.single q 1)))
        = fun p => algebraMap A B ((G (Pi.single q 1)) p) := by
    intro q
    ext p
    simp [TensorProduct.piScalarRight, Algebra.smul_def]
  constructor
  · intro h q p
    have h1 := LinearMap.congr_fun h ((1 : B) ⊗ₜ[A] (Pi.single q 1))
    simp only [LinearMap.baseChange_tmul, LinearMap.zero_apply] at h1
    simpa [key q] using congrFun (congrArg (TensorProduct.piScalarRight A B B (Fin b)) h1) p
  · intro h
    have hcoord : ∀ (v : Fin a → A) (p : Fin b), algebraMap A B ((G v) p) = 0 := by
      intro v p
      have hv : v = ∑ q, v q • Pi.single q (1 : A) := by
        ext q'
        simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
      rw [hv]
      simp [Finset.sum_apply, h]
    refine LinearMap.ext fun y => ?_
    induction y using TensorProduct.inductionOn with
    | tmul c v =>
      rw [LinearMap.baseChange_tmul, LinearMap.zero_apply]
      apply (TensorProduct.piScalarRight A B B (Fin b)).injective
      rw [map_zero]
      ext p
      change (TensorProduct.piScalarRightHom A B B (Fin b)) (c ⊗ₜ[A] (G v)) p = 0
      simp [TensorProduct.piScalarRightHom, TensorProduct.piScalarRightHomBil,
        Algebra.smul_def, hcoord v p]
    | add x y hx hy => simp [hx, hy]

/-- Vanishing of `φ.baseChange B` can be tested after precomposing with a surjection `f` and
postcomposing with a split injection `g`. -/
theorem baseChange_eq_zero_iff_baseChange_comp_eq_zero {M' P P' : Type*}
    [AddCommGroup M'] [Module A M'] [AddCommGroup P] [Module A P] [AddCommGroup P'] [Module A P']
    {f : M' →ₗ[A] M} (hf : Function.Surjective f) {g : P →ₗ[A] P'} {g' : P' →ₗ[A] P}
    (hg : g' ∘ₗ g = LinearMap.id) (φ : M →ₗ[A] P) (B : Type*) [CommRing B] [Algebra A B] :
    φ.baseChange B = 0 ↔ (g ∘ₗ φ ∘ₗ f).baseChange B = 0 := by
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp]
  refine ⟨fun h => by simp [h], fun h => LinearMap.ext fun y => ?_⟩
  obtain ⟨x, rfl⟩ := LinearMap.baseChange_surjective B hf y
  have hinj : Function.Injective (g.baseChange B) :=
    Function.LeftInverse.injective (g := g'.baseChange B) fun x => by
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hg, LinearMap.baseChange_id,
        LinearMap.id_apply]
  exact hinj (by simpa using LinearMap.congr_fun h x)

/-- **Remark 4 (finitely generated ideal cutting out vanishing of a finite
family of maps).**  Let `M, P` be finite projective `A`-modules and let
`g : ι → (M →ₗ[A] P)` be a finite family of `A`-linear maps.  Then there is a
finitely generated ideal `J ⊆ A` such that, for every `A`-algebra `B`,
`J ≤ ker(algebraMap A B)` iff `(g i).baseChange B = 0` for all `i`.

Informal proof: `H = M →ₗ[A] P` is finite projective, so by
`Module.Finite.exists_comp_eq_id_of_projective` there are `n`, a surjection
`ρ : Aⁿ → H` and an injection `ι : H → Aⁿ` with `ρ ∘ ι = id`.  Let `J` be the
ideal generated by all coordinates `(ι (g i)) j` (`i ∈ ι`, `j < n`); this is a
finite generating set, so `J.FG`.  Base change is exact on the split inclusion
`ι`, giving a natural iso `B ⊗ H ≅ Hom_B(M_B, P_B)` under which the element
`1 ⊗ (g i)` corresponds to `(g i).baseChange B`; hence `(g i).baseChange B = 0`
iff `1 ⊗ (g i) = 0` in `B ⊗ H` iff `ι(g i) ⊗ 1 = 0` in `Bⁿ` (using `ρ_B ∘ ι_B =
id`), iff every coordinate `(ι (g i)) j` maps to `0` in `B`.  Quantifying over
`i`, this is exactly `J ≤ ker(algebraMap A B)`. -/
theorem exists_fg_ideal_baseChange_family_zero
    {P : Type*} [AddCommGroup P] [Module A P]
    [Module.Finite A M] [Module.Projective A M]
    [Module.Finite A P] [Module.Projective A P]
    {ι : Type*} [Finite ι] (g : ι → (M →ₗ[A] P)) :
    ∃ J : Ideal A, J.FG ∧
      ∀ (B : Type v) [CommRing B] [Algebra A B],
        (J ≤ RingHom.ker (algebraMap A B)) ↔
          (∀ i, (g i).baseChange B = 0) := by
  obtain ⟨aM, fM, gM, hfM, -, -⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  obtain ⟨aP, fP, gP, -, -, hPid⟩ := Module.Finite.exists_comp_eq_id_of_projective A P
  let f : (ι × Fin aM × Fin aP) → A := fun x => (gP ∘ₗ g x.1 ∘ₗ fM) (Pi.single x.2.1 1) x.2.2
  refine ⟨Ideal.span (Set.range f), Submodule.fg_span (Set.finite_range f), fun B _ _ => ?_⟩
  simp only [Ideal.span_le, Set.range_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
    baseChange_eq_zero_iff_baseChange_comp_eq_zero hfM hPid,
    baseChange_eq_zero_iff_algebraMap_apply_eq_zero, Prod.forall, f]

-- Main Statement(s)

/-- **Theorem (Stacks Tag 0F80, Lemma 15.98.7).**
Let `A` be a commutative ring, let `M`, `N₁`, `N₂` be finite projective
`A`-modules, and let `s : M → N₁ × N₂` be a split injection. Then there exists
a finitely generated ideal `J ⊆ A` such that, for every commutative ring `B`
and every ring map `A → B`, the map `A → B` factors through `A/J`
(`J ≤ ker(A → B)`) if and only if the base-changed map `s_B` identifies `M_B`
with a direct sum of submodules of `N_{1,B} ⊕ N_{2,B}` (Definition 4). -/
@[stacks 0F80]
theorem main_theorem_0f80
    [Module.Finite A M] [Module.Projective A M]
    [Module.Finite A N₁] [Module.Projective A N₁]
    [Module.Finite A N₂] [Module.Projective A N₂]
    (s : M →ₗ[A] (N₁ × N₂)) (hs : IsSplitInjective s) :
    ∃ J : Ideal A, J.FG ∧
      ∀ (B : Type v) [CommRing B] [Algebra A B],
        (J ≤ RingHom.ker (algebraMap A B)) ↔ IdentifiesDirectSum s B := by
  obtain ⟨π, hπ⟩ := hs
  obtain ⟨J, hJfg, hJ⟩ :=
    exists_fg_ideal_baseChange_family_zero
      (M := M) (P := N₁ × N₂)
      (![fMap s π (q₁ (N₁ := N₁) (N₂ := N₂)),
         fMap s π (q₂ (N₁ := N₁) (N₂ := N₂))])
  refine ⟨J, hJfg, fun B _ _ => ?_⟩
  rw [hJ B, Fin.forall_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← stable_iff_fMap_baseChange_zero s π hπ B, ← identifiesDirectSum_iff_stable s B]

end Stacks.SplitInjectionDirectSum
