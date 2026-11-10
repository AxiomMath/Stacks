module

public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver

/-!
# Completion over a base commutes with finite products

Let `B` be a topological ring and `g : B →+* ∏ₛ Aₛ` a ring map into a finite product. The
completion of `∏ₛ Aₛ` over `B` is the product of the completions of the factors over `B`: the
extension of a weak ideal of definition `J` of `B` to the product is the product of its
extensions to the factors, so `(∏ₛ Aₛ) ⧸ J(∏ₛ Aₛ) = ∏ₛ Aₛ ⧸ JAₛ` compatibly with the transition
maps, and the inverse limit of a product is the product of the inverse limits.

## Main results

* `TopologicalRing.CompletionOver.piRingEquiv`: the ring isomorphism.
* `TopologicalRing.CompletionOver.continuous_piRingEquiv` and
  `TopologicalRing.CompletionOver.continuous_piRingEquiv_symm`: it is a homeomorphism.
* `TopologicalRing.CompletionOver.piRingEquiv_canonicalMap`: it is compatible with the canonical
  maps from `B`.
-/

@[expose] public noncomputable section

namespace TopologicalRing.CompletionOver

universe u v w

variable {B : Type u} [CommRing B] [TopologicalSpace B] {σ : Type w} [Finite σ]
  {A : σ → Type v} [∀ s, CommRing (A s)] (g : ∀ s, B →+* A s)

omit [TopologicalSpace B] in
/-- The extension of an ideal to a finite product is the product of its extensions. -/
theorem mem_map_pi_iff (J : Ideal B) (x : ∀ s, A s) :
    x ∈ J.map (RingHom.pi g) ↔ ∀ s, x s ∈ J.map (g s) := by
  classical
  have := Fintype.ofFinite σ
  constructor
  · intro hx s
    have h := Ideal.mem_map_of_mem (Pi.evalRingHom A s) hx
    rwa [Ideal.map_map, show (Pi.evalRingHom A s).comp (RingHom.pi g) = g s from
      RingHom.ext fun _ ↦ rfl] at h
  · intro hx
    have hsingle : ∀ s (a : A s), a ∈ J.map (g s) → Pi.single s a ∈ J.map (RingHom.pi g) := by
      intro s a ha
      refine Submodule.span_induction (p := fun a _ ↦ Pi.single s a ∈ J.map (RingHom.pi g))
        ?_ ?_ ?_ ?_ ha
      · rintro _ ⟨b, hb, rfl⟩
        have : (Pi.single s (g s b) : ∀ s, A s) = Pi.single s 1 * (RingHom.pi g) b := by
          funext t
          by_cases ht : t = s
          · subst ht; simp
          · simp [Pi.single_eq_of_ne ht]
        rw [this]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem (RingHom.pi g) hb)
      · simp
      · intro a b _ _ ha hb
        rw [Pi.single_add]
        exact Ideal.add_mem _ ha hb
      · intro c a _ ha
        rw [smul_eq_mul, Pi.single_mul]
        exact Ideal.mul_mem_left _ _ ha
    rw [← Finset.univ_sum_single x]
    exact Ideal.sum_mem _ fun s _ ↦ hsingle s (x s) (hx s)

/-- The quotient map from the `J`-th stage of the completion of the product to that of a
factor. -/
abbrev stageComponent (J : WeakIdealOfDefinitionIndex B) (s : σ) :
    (∀ s, A s) ⧸ extendedIdeal (RingHom.pi g) J →+* A s ⧸ extendedIdeal (g s) J :=
  Ideal.quotientMap _ (Pi.evalRingHom A s) (by
    rw [extendedIdeal, extendedIdeal, Ideal.map_le_iff_le_comap.symm, Ideal.map_map,
      show (Pi.evalRingHom A s).comp (RingHom.pi g) = g s from RingHom.ext fun _ ↦ rfl])

/-- The map from the completion of the product to the completion of one factor. -/
def toComponent (s : σ) : CompletionOver (RingHom.pi g) →+* CompletionOver (g s) where
  toFun x := ⟨fun J ↦ stageComponent g J s (x.1 J), by
    intro J K h
    dsimp only
    rw [← x.2 J K h]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (x.1 J)
    rw [← hy]
    rfl⟩
  map_one' := Subtype.ext (funext fun J ↦ map_one _)
  map_mul' x y := Subtype.ext (funext fun J ↦ map_mul _ _ _)
  map_zero' := Subtype.ext (funext fun J ↦ map_zero _)
  map_add' x y := Subtype.ext (funext fun J ↦ map_add _ _ _)

/-- The map from the completion of the product to the product of the completions. -/
def toPi : CompletionOver (RingHom.pi g) →+* ∀ s, CompletionOver (g s) :=
  RingHom.pi (toComponent g)

omit [Finite σ] in
/-- The `J`-th stage of the `s`-th component of `toPi g x` is the image of the `J`-th stage
of `x`. -/
theorem toPi_apply_apply (x : CompletionOver (RingHom.pi g)) (s : σ)
    (J : WeakIdealOfDefinitionIndex B) :
    ((toPi g x) s).1 J = stageComponent g J s (x.1 J) := rfl

/-- The map from the completion of the product to the product of the completions is injective. -/
theorem injective_toPi : Function.Injective (toPi g) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ Subtype.ext (funext fun J ↦ ?_)
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (x.1 J)
  have h : ∀ s, y s ∈ J.1.map (g s) := fun s ↦ by
    have := congrArg (fun z ↦ (z s).1 J) hx
    simp only [toPi_apply_apply, ← hy] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  change x.1 J = 0
  rw [← hy]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ((mem_map_pi_iff g J.1 y).mpr h)

/-- The `J`-th stage of a preimage under `toPi`. -/
def ofPiStage (y : ∀ s, CompletionOver (g s)) (J : WeakIdealOfDefinitionIndex B) :
    (∀ s, A s) ⧸ extendedIdeal (RingHom.pi g) J :=
  Ideal.Quotient.mk _ fun s ↦ ((y s).1 J).out

omit [Finite σ] in
/-- The components of `ofPiStage g y J` are the `J`-th stages of the `y s`. -/
theorem stageComponent_ofPiStage (y : ∀ s, CompletionOver (g s))
    (J : WeakIdealOfDefinitionIndex B) (s : σ) :
    stageComponent g J s (ofPiStage g y J) = (y s).1 J := by
  change Ideal.Quotient.mk _ (((y s).1 J).out) = _
  exact Quotient.out_eq _

/-- An element of a stage of the completion of the product is determined by its components. -/
theorem stage_ext (J : WeakIdealOfDefinitionIndex B)
    (z w : (∀ s, A s) ⧸ extendedIdeal (RingHom.pi g) J)
    (h : ∀ s, stageComponent g J s z = stageComponent g J s w) : z = w := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
  exact Ideal.Quotient.eq.mpr ((mem_map_pi_iff g J.1 _).mpr fun s ↦ Ideal.Quotient.eq.mp (h s))

/-- The map from the completion of the product to the product of the completions is
surjective. -/
theorem surjective_toPi : Function.Surjective (toPi g) := by
  intro y
  have hstage := stage_ext g
  refine ⟨⟨ofPiStage g y, fun J K hJK ↦ hstage K _ _ fun s ↦ ?_⟩, ?_⟩
  · rw [stageComponent_ofPiStage, ← (y s).2 J K hJK, ← stageComponent_ofPiStage g y J s]
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (ofPiStage g y J)
    rw [← hz]
    rfl
  · funext s
    exact Subtype.ext (funext fun J ↦ stageComponent_ofPiStage g y J s)

/-- **The completion over `B` of a finite product is the product of the completions.** -/
def piRingEquiv : CompletionOver (RingHom.pi g) ≃+* ∀ s, CompletionOver (g s) :=
  RingEquiv.ofBijective (toPi g) ⟨injective_toPi g, surjective_toPi g⟩

/-- The isomorphism `piRingEquiv g` is the map `toPi g`. -/
theorem piRingEquiv_apply (x : CompletionOver (RingHom.pi g)) : piRingEquiv g x = toPi g x := rfl

/-- The isomorphism `piRingEquiv g` is continuous. -/
theorem continuous_piRingEquiv : Continuous (piRingEquiv g) := by
  let (J : WeakIdealOfDefinitionIndex B) :
      TopologicalSpace ((∀ s, A s) ⧸ extendedIdeal (RingHom.pi g) J) := ⊥
  let (J : WeakIdealOfDefinitionIndex B) (s : σ) :
      TopologicalSpace (A s ⧸ extendedIdeal (g s) J) := ⊥
  have : ∀ J : WeakIdealOfDefinitionIndex B,
      DiscreteTopology ((∀ s, A s) ⧸ extendedIdeal (RingHom.pi g) J) :=
    fun _ ↦ discreteTopology_bot _
  refine continuous_pi fun s ↦ continuous_induced_rng.mpr (continuous_pi fun J ↦ ?_)
  change Continuous ((stageComponent g J s) ∘ (fun x : CompletionOver (RingHom.pi g) ↦ x.1 J))
  exact continuous_of_discreteTopology.comp
    ((continuous_apply J).comp continuous_subtype_val)

/-- The inverse of the isomorphism `piRingEquiv g` is continuous. -/
theorem continuous_piRingEquiv_symm : Continuous (piRingEquiv g).symm := by
  classical
  let (J : WeakIdealOfDefinitionIndex B) :
      TopologicalSpace ((∀ s, A s) ⧸ extendedIdeal (RingHom.pi g) J) := ⊥
  let (J : WeakIdealOfDefinitionIndex B) (s : σ) :
      TopologicalSpace (A s ⧸ extendedIdeal (g s) J) := ⊥
  have : ∀ (J : WeakIdealOfDefinitionIndex B) (s : σ),
      DiscreteTopology (A s ⧸ extendedIdeal (g s) J) :=
    fun _ _ ↦ discreteTopology_bot _
  have hsymm : ∀ y, ((piRingEquiv g).symm y).1 = ofPiStage g y := by
    intro y
    have h := (piRingEquiv g).apply_symm_apply y
    funext J
    refine stage_ext g J _ _ fun s ↦ ?_
    rw [stageComponent_ofPiStage, ← toPi_apply_apply, ← piRingEquiv_apply, h]
  refine continuous_induced_rng.mpr (continuous_pi fun J ↦ ?_)
  have hcomp : (fun y ↦ ((piRingEquiv g).symm y).1 J) =
      (fun t : ∀ s, A s ⧸ extendedIdeal (g s) J ↦
        (Ideal.Quotient.mk (extendedIdeal (RingHom.pi g) J) fun s ↦ (t s).out)) ∘
        (fun y : ∀ s, CompletionOver (g s) ↦ fun s ↦ (y s).1 J) := by
    funext y
    exact congrFun (hsymm y) J
  change Continuous (fun y ↦ ((piRingEquiv g).symm y).1 J)
  rw [hcomp]
  exact continuous_of_discreteTopology.comp
    (continuous_pi fun s ↦ ((continuous_apply J).comp continuous_subtype_val).comp
      (continuous_apply s))

/-- The isomorphism is compatible with the canonical maps from `B`. -/
theorem piRingEquiv_canonicalMap (b : B) :
    piRingEquiv g (canonicalMap (RingHom.pi g) b) = fun s ↦ canonicalMap (g s) b := by
  funext s
  exact Subtype.ext (funext fun J ↦ rfl)

end TopologicalRing.CompletionOver

end
