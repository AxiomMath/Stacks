module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.KernelLevelStabilization
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionLeftExact
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicAbelian

/-!
# Existence of the algebraization of a map into a completion (Stacks 08BB)

Let `F` be a Noetherian algebraic space, `𝓘 ⊆ 𝒪_F` a quasi-coherent sheaf of ideals, `G` a
coherent `𝒪_F`-module and `α : E ⟶ G^∧` a map in `Coh(F, 𝓘)` whose levelwise kernels and
cokernels are annihilated by one power `𝓘 ^ t` (Remark 08BA (1)).  Stacks 08BB asserts that `α`
is `β ≫ a^∧` for a map `a : M ⟶ G` of coherent modules whose kernel and cokernel are annihilated
by a power of `𝓘` and an isomorphism `β : E ≅ M^∧`, uniquely up to unique isomorphism.  The
uniqueness half is on the base as
`AlgebraicGeometry.Space.existsUnique_iso_of_algebraization_of_isNoetherian`; this file proves
the existence half and assembles the whole lemma.

## Main results

* `AlgebraicGeometry.Space.exists_image_algebraization` — the image of `α` is the completion of
  a coherent submodule `Q ⊆ G`.
* `AlgebraicGeometry.Space.exists_algebraization_of_epi` — a surjection onto `Q^∧` with
  levelwise kernels annihilated by `𝓘 ^ t` is the completion of a surjection of coherent modules.
* `AlgebraicGeometry.Space.exists_algebraization` — the existence half of Stacks 08BB.
* `AlgebraicGeometry.Space.existsUnique_algebraization` — **Stacks 08BB.**

## Implementation notes

The source proves existence by étale descent from the scheme case, Stacks 0889.  The proof here
is global instead and needs neither restriction of coherent adic systems to an étale chart nor
gluing of coherent modules.  It writes `α` as a surjection `p : E ⟶ Q^∧` followed by the
completion of `Q ⊆ G`, where `Q` is the kernel of `G ⟶ C_{t - 1}` for the cokernel `C` of `α`,
and then algebraizes `p` by the finite fibre product `Q ×_{Q / 𝓘 ᵐ⁺¹ Q} E_m` for `m` large.  The
only analytic input is the Artin–Rees stabilization of the levelwise kernels of `p`
(`AlgebraicGeometry.Space.exists_isPullback_transition_of_epi`), which is the second stabilization
of Stacks 087X on the base; the rest is the abelian structure of `Coh(𝒪_F)` and `Coh(F, 𝓘)`
(Stacks 07UC, 089P), the exactness of completion (Stacks 08B5) and Stacks 08B3.

The system is indexed by `ℕᵒᵖ` and is zero-indexed: the term at `n` is the Stacks source's
`E_{n + 1}`.

## References

* [Stacks Project, Tag 08BB](https://stacks.math.columbia.edu/tag/08BB)
* [Stacks Project, Tag 08BA](https://stacks.math.columbia.edu/tag/08BA)
* [Stacks Project, Tag 08B5](https://stacks.math.columbia.edu/tag/08B5)
* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-! ### Inverse systems -/

/-- The transition map of an inverse system from a level to itself is the identity. -/
private theorem map_homOfLE_self {C : Type*} [Category C] (E : ℕᵒᵖ ⥤ C) {l : ℕ} (h : l ≤ l) :
    E.map (homOfLE h).op = 𝟙 _ :=
  (congrArg E.map (Subsingleton.elim _ (𝟙 (op l)))).trans (E.map_id _)

/-- A monomorphism into the source of `f` that is killed by `f` has source annihilated by `𝓘 ^ t`
as soon as `ker f` is. -/
private theorem idealPowerMultiple_eq_bot_of_comp_eq_zero {X Y Z : Modules.{u, u} B S hS F hF}
    (x : X ⟶ Y) [Mono x] (f : Y ⟶ Z) (hx : x ≫ f = 0) (t : ℕ)
    (h : idealPowerMultiple B S hS F hF 𝓘 t (kernel f) = ⊥) :
    idealPowerMultiple B S hS F hF 𝓘 t X = ⊥ :=
  have : Mono (kernel.lift f x hx) := mono_of_mono_fac (kernel.lift_ι _ _ hx)
  idealPowerMultiple_eq_bot_of_mono B S hS F hF 𝓘 (kernel.lift f x hx) t h

/-- The transition maps of a coherent adic system are epimorphisms between any two levels. -/
theorem epi_map_homOfLE_of_isCoherentAdicSystem {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF}
    (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E) {l k : ℕ} (h : l ≤ k) :
    Epi (E.map (homOfLE h).op) := by
  induction k, h using Nat.le_induction with
  | base =>
      rw [map_homOfLE_self]; infer_instance
  | succ k hlk ih =>
      have := epi_map_le_succ B S hS F hF 𝓘 hE k
      have hc : E.map (homOfLE (hlk.trans (Nat.le_succ k))).op =
          E.map (homOfLE (Nat.le_succ k)).op ≫ E.map (homOfLE hlk).op :=
        (congrArg E.map (Subsingleton.elim _ _)).trans (E.map_comp _ _)
      rw [hc]; infer_instance

/-- The transition maps of a coherent adic system compose. -/
theorem map_homOfLE_comp_map_homOfLE (E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF) {j k l : ℕ}
    (h₁ : j ≤ k) (h₂ : k ≤ l) :
    E.map (homOfLE h₂).op ≫ E.map (homOfLE h₁).op = E.map (homOfLE (h₁.trans h₂)).op :=
  (E.map_comp _ _).symm.trans (congrArg E.map (Subsingleton.elim _ _))

/-- The transition maps of a coherent adic system all of whose terms are annihilated by
`𝓘 ^ (N + 1)` are isomorphisms from level `N` on. -/
theorem isIso_map_homOfLE_of_annihilated {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF}
    (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E) (N : ℕ)
    (hann : ∀ l : ℕ, idealPowerMultiple B S hS F hF 𝓘 (N + 1) (E.obj (op l)) = ⊥)
    {l : ℕ} (h : N ≤ l) : IsIso (E.map (homOfLE h).op) := by
  induction l, h using Nat.le_induction with
  | base =>
      rw [map_homOfLE_self]; infer_instance
  | succ k hNk ih =>
      have hstep : IsIso (E.map (homOfLE (Nat.le_succ k)).op) := by
        obtain ⟨e, he⟩ := hE.2.2 k
        have := isIso_π_idealPowerMultiple_of_eq_bot B S hS F hF 𝓘 (k + 1) _
          (idealPowerMultiple_eq_bot_of_le B S hS F hF 𝓘 (Nat.add_le_add_right hNk 1) _
            (hann (k + 1)))
        rw [← he]; infer_instance
      rw [← map_homOfLE_comp_map_homOfLE B S hS F hF E hNk (Nat.le_succ k)]
      infer_instance

/-- A morphism of coherent adic systems vanishes as soon as its components vanish from some level
on, the transition maps of its source being epimorphisms. -/
theorem eq_zero_of_app_eq_zero_of_le {T W : CoherentAdicSystems B S hS F hF 𝓘} (x : T ⟶ W)
    (N : ℕ) (h : ∀ l : ℕ, N ≤ l → x.hom.app (op l) = 0) : x = 0 := by
  ext1
  refine NatTrans.ext (funext fun lv => ?_)
  obtain ⟨l⟩ := lv
  have := epi_map_homOfLE_of_isCoherentAdicSystem B S hS F hF 𝓘 T.property
    (Nat.le_add_right l N)
  refine (cancel_epi (T.obj.map (homOfLE (Nat.le_add_right l N)).op)).1 ?_
  rw [x.hom.naturality, h (l + N) (Nat.le_add_left N l), zero_comp]
  exact (comp_zero (f := T.obj.map (homOfLE (Nat.le_add_right l N)).op)).symm

/-- The zero morphism of coherent adic systems has zero components. -/
theorem zero_hom_app_coherentAdicSystems {T W : CoherentAdicSystems B S hS F hF 𝓘} (x : ℕᵒᵖ) :
    (0 : T ⟶ W).hom.app x = 0 :=
  rfl

/-! ### Compatible lifts along eventually cartesian squares -/

section Lifts

variable {E E' : CoherentAdicSystems B S hS F hF 𝓘} (p : E ⟶ E') (m : ℕ)
    (hsq : ∀ j : ℕ, IsPullback (p.hom.app (op (m + j + 1)))
      (E.obj.map (homOfLE (Nat.le_succ (m + j))).op) (E'.obj.map (homOfLE (Nat.le_succ (m + j))).op)
      (p.hom.app (op (m + j))))
    {W : Modules.{u, u} B S hS F hF} (y : ∀ j : ℕ, W ⟶ E'.obj.obj (op (m + j)))
    (hy : ∀ j : ℕ, y (j + 1) ≫ E'.obj.map (homOfLE (Nat.le_succ (m + j))).op = y j)
    (x₀ : W ⟶ E.obj.obj (op m)) (h₀ : x₀ ≫ p.hom.app (op m) = y 0)

/-- The lifts `W ⟶ E_{m + j}` of a compatible family `W ⟶ E'_{m + j}` through `p`, starting from
a lift `x₀` at level `m`, built one level at a time through the pullback squares `hsq`. -/
def compatibleLift : (j : ℕ) →
    {f : W ⟶ E.obj.obj (op (m + j)) // f ≫ p.hom.app (op (m + j)) = y j}
  | 0 => ⟨x₀, h₀⟩
  | j + 1 => ⟨(hsq j).lift (y (j + 1)) (compatibleLift j).1
      (by rw [hy j, (compatibleLift j).2]), (hsq j).lift_fst _ _ _⟩

/-- The lift at level `m` is `x₀`. -/
theorem compatibleLift_zero :
    (compatibleLift B S hS F hF 𝓘 p m hsq y hy x₀ h₀ 0).1 = x₀ :=
  rfl

/-- The lifts are compatible with the transition maps `E_{m + j + 1} ⟶ E_{m + j}`. -/
theorem compatibleLift_succ_comp (j : ℕ) :
    (compatibleLift B S hS F hF 𝓘 p m hsq y hy x₀ h₀ (j + 1)).1 ≫
        E.obj.map (homOfLE (Nat.le_succ (m + j))).op =
      (compatibleLift B S hS F hF 𝓘 p m hsq y hy x₀ h₀ j).1 :=
  (hsq j).lift_snd _ _ _

/-- The lifts are compatible with every transition map `E_{m + k} ⟶ E_{m + j}`, `j ≤ k`. -/
theorem compatibleLift_comp_map {j k : ℕ} (h : j ≤ k) :
    (compatibleLift B S hS F hF 𝓘 p m hsq y hy x₀ h₀ k).1 ≫
        E.obj.map (homOfLE (Nat.add_le_add_left h m)).op =
      (compatibleLift B S hS F hF 𝓘 p m hsq y hy x₀ h₀ j).1 := by
  induction k, h using Nat.le_induction with
  | base =>
      rw [map_homOfLE_self, Category.comp_id]
  | succ k hjk ih =>
      rw [← map_homOfLE_comp_map_homOfLE B S hS F hF E.obj (Nat.add_le_add_left hjk m)
        (Nat.le_succ (m + k)), ← Category.assoc, compatibleLift_succ_comp, ih]

/-- The lift at level `l`, obtained from the lift at level `m + l` by the transition map. -/
def compatibleLiftAt (l : ℕ) : W ⟶ E.obj.obj (op l) :=
  (compatibleLift B S hS F hF 𝓘 p m hsq y hy x₀ h₀ l).1 ≫
    E.obj.map (homOfLE (Nat.le_add_left l m)).op

/-- The lifts `compatibleLiftAt` are compatible with the transition maps `E_{l'} ⟶ E_l`. -/
theorem compatibleLiftAt_comp_map {l l' : ℕ} (h : l ≤ l') :
    compatibleLiftAt B S hS F hF 𝓘 p m hsq y hy x₀ h₀ l' ≫ E.obj.map (homOfLE h).op =
      compatibleLiftAt B S hS F hF 𝓘 p m hsq y hy x₀ h₀ l := by
  simp only [compatibleLiftAt, Category.assoc]
  rw [map_homOfLE_comp_map_homOfLE B S hS F hF E.obj h (Nat.le_add_left l' m),
    ← map_homOfLE_comp_map_homOfLE B S hS F hF E.obj (Nat.le_add_left l m)
      (Nat.add_le_add_left h m), ← Category.assoc, compatibleLift_comp_map]
  exact h

/-- The lift at level `l` lifts `y l` followed by the transition map `E'_{m + l} ⟶ E'_l`. -/
theorem compatibleLiftAt_comp (l : ℕ) :
    compatibleLiftAt B S hS F hF 𝓘 p m hsq y hy x₀ h₀ l ≫ p.hom.app (op l) =
      y l ≫ E'.obj.map (homOfLE (Nat.le_add_left l m)).op := by
  rw [compatibleLiftAt, Category.assoc, p.hom.naturality, ← Category.assoc,
    (compatibleLift B S hS F hF 𝓘 p m hsq y hy x₀ h₀ l).2]

/-- The lift `compatibleLiftAt` at level `m` is `x₀`. -/
theorem compatibleLiftAt_base :
    compatibleLiftAt B S hS F hF 𝓘 p m hsq y hy x₀ h₀ m = x₀ :=
  compatibleLift_comp_map B S hS F hF 𝓘 p m hsq y hy x₀ h₀ (Nat.zero_le m)

/-- From level `m` on, the lifts map to `x₀` under the transition maps to level `m`. -/
theorem compatibleLiftAt_comp_map_base {l : ℕ} (h : m ≤ l) :
    compatibleLiftAt B S hS F hF 𝓘 p m hsq y hy x₀ h₀ l ≫ E.obj.map (homOfLE h).op = x₀ := by
  rw [compatibleLiftAt_comp_map, compatibleLiftAt]
  exact compatibleLift_comp_map B S hS F hF 𝓘 p m hsq y hy x₀ h₀ (Nat.zero_le m)

end Lifts

/-! ### The image of the map is a completion -/

section Completion

variable [Fact (HasEtaleLocalProperty B S hS F
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))]
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)

/-- **The image of a map into a completion whose cokernel is annihilated by a power of `𝓘` is a
completion.**  Let `α : E ⟶ G^∧` have levelwise cokernels annihilated by `𝓘 ^ t`.  Write `C` for
the cokernel of `α` in `Coh(F, 𝓘)`, which is levelwise, and `g : G ⟶ C_{t - 1}` for the composite
of the projections.  Then `Q = ker g` is a coherent submodule of `G` whose completion is the
image of `α`: `α` factors as an epimorphism `p : E ⟶ Q^∧` followed by the completion of the
inclusion, and the cokernel of the inclusion embeds into `C_{t - 1}`, hence is annihilated by
`𝓘 ^ t`.

The completion of `g` is, from level `t - 1` on, the projection `γ : G^∧ ⟶ C` followed by an
isomorphism, because `C` is annihilated by `𝓘 ^ t`; so a morphism into `G^∧` is killed by the
completion of `g` exactly when it is killed by `γ`.  By left exactness of the completion functor
(Stacks 08B5) the completion of `Q` is the kernel of the completion of `g`, hence the kernel of
`γ`, and the factorization of `α` through the kernel of its own cokernel is an epimorphism in
the abelian category `Coh(F, 𝓘)` (Stacks 089P). -/
theorem exists_image_algebraization (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ F)
    {G : CoherentModules.{u, u} B S hS F hF} {E : CoherentAdicSystems B S hS F hF 𝓘}
    (α : E ⟶ (completionFunctor B S hS F hF 𝓘 hI).obj G) (t : ℕ) (ht : 0 < t)
    (hcoker : ∀ k : ℕ,
      idealPowerMultiple B S hS F hF 𝓘 t (cokernel (α.hom.app (op k))) = ⊥) :
    ∃ (Q : CoherentModules.{u, u} B S hS F hF) (ι : Q ⟶ G)
      (p : E ⟶ (completionFunctor B S hS F hF 𝓘 hI).obj Q),
      Mono ι ∧ Epi p ∧ p ≫ (completionFunctor B S hS F hF 𝓘 hI).map ι = α ∧
        idealPowerMultiple B S hS F hF 𝓘 t (cokernel ι).obj = ⊥ := by
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  have hIcart :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF 𝓘.toSheafOfModules hI
  have := preservesFiniteLimits_completionFunctor_of_isNoetherian B S hS F hF 𝓘 hI hZ hN
  let C := coherentAdicCokernel B S hS F hF 𝓘 α
  let γ : (completionFunctor B S hS F hF 𝓘 hI).obj G ⟶ C :=
    coherentAdicCokernelπ B S hS F hF 𝓘 α
  have hC : ∀ l : ℕ, idealPowerMultiple B S hS F hF 𝓘 (n + 1) (C.obj.obj (op l)) = ⊥ :=
    fun l => idealPowerMultiple_eq_bot_of_iso B S hS F hF 𝓘
      (cokernelObjIso B S hS F hF α.hom (op l)).symm (n + 1) (hcoker l)
  let Cc : CoherentModules.{u, u} B S hS F hF := ⟨C.obj.obj (op n), C.property.1 n⟩
  let g : G ⟶ Cc := ObjectProperty.homMk
    (completionTermProjection B S hS F hF 𝓘 hI G n ≫ γ.hom.app (op n))
  have hg : ∀ (l : ℕ) (hl : n ≤ l), ((completionFunctor B S hS F hF 𝓘 hI).map g).hom.app (op l) =
      γ.hom.app (op l) ≫ (C.obj.map (homOfLE hl).op ≫
        completionTermProjection B S hS F hF 𝓘 hI Cc l) := by
    intro l hl
    refine (cancel_epi (completionTermProjection B S hS F hF 𝓘 hI G l)).1 ?_
    rw [completionTermProjection_naturality, ← Category.assoc (γ.hom.app (op l)),
      ← γ.hom.naturality (homOfLE hl).op, ← Category.assoc, ← Category.assoc,
      completionTermProjection_transition]
    rfl
  have hiso : ∀ (l : ℕ) (hl : n ≤ l), IsIso (C.obj.map (homOfLE hl).op ≫
      completionTermProjection B S hS F hF 𝓘 hI Cc l) := by
    intro l hl
    have := isIso_map_homOfLE_of_annihilated B S hS F hF 𝓘 C.property n hC hl
    have := isIso_completionTermProjection_of_annihilated B S hS F hF 𝓘 hI Cc l
      (idealPowerMultiple_eq_bot_of_le B S hS F hF 𝓘 (Nat.add_le_add_right hl 1) _ (hC n))
    infer_instance
  have hA : ∀ {T : CoherentAdicSystems B S hS F hF 𝓘}
      (h : T ⟶ (completionFunctor B S hS F hF 𝓘 hI).obj G),
      h ≫ (completionFunctor B S hS F hF 𝓘 hI).map g = 0 ↔ h ≫ γ = 0 := by
    intro T h
    refine ⟨fun hz => eq_zero_of_app_eq_zero_of_le B S hS F hF 𝓘 _ n fun l hl => ?_,
      fun hz => eq_zero_of_app_eq_zero_of_le B S hS F hF 𝓘 _ n fun l hl => ?_⟩
    · have h1 : h.hom.app (op l) ≫ ((completionFunctor B S hS F hF 𝓘 hI).map g).hom.app (op l) =
          0 := congrArg (fun k => k.hom.app (op l)) hz
      rw [hg l hl, ← Category.assoc] at h1
      have := hiso l hl
      change h.hom.app (op l) ≫ γ.hom.app (op l) = 0
      exact (cancel_mono _).1 (h1.trans zero_comp.symm)
    · have h1 : h.hom.app (op l) ≫ γ.hom.app (op l) = 0 := congrArg (fun k => k.hom.app (op l)) hz
      change h.hom.app (op l) ≫ ((completionFunctor B S hS F hF 𝓘 hI).map g).hom.app (op l) = 0
      rw [hg l hl, ← Category.assoc, h1, zero_comp]
  let ι : kernel g ⟶ G := kernel.ι g
  have hwg : (completionFunctor B S hS F hF 𝓘 hI).map ι ≫
      (completionFunctor B S hS F hF 𝓘 hI).map g = 0 := by
    rw [← Functor.map_comp, kernel.condition, Functor.map_zero]
  have hlimg := KernelFork.mapIsLimit _ (kernelIsKernel g) (completionFunctor B S hS F hF 𝓘 hI)
  have hmono : Mono ((completionFunctor B S hS F hF 𝓘 hI).map ι) := mono_of_isLimit_fork hlimg
  have hw : (completionFunctor B S hS F hF 𝓘 hI).map ι ≫ γ = 0 := (hA _).1 hwg
  have hlim : IsLimit (KernelFork.ofι _ hw) :=
    KernelFork.IsLimit.ofι _ hw
      (fun k hk => (KernelFork.IsLimit.lift' hlimg k ((hA k).2 hk)).1)
      (fun k hk => (KernelFork.IsLimit.lift' hlimg k ((hA k).2 hk)).2)
      (fun k hk m hm => (cancel_mono ((completionFunctor B S hS F hF 𝓘 hI).map ι)).1
        (hm.trans (KernelFork.IsLimit.lift' hlimg k ((hA k).2 hk)).2.symm))
  obtain ⟨p, hp⟩ := KernelFork.IsLimit.lift' hlim α (comp_coherentAdicCokernelπ B S hS F hF 𝓘 α)
  refine ⟨kernel g, ι, p, inferInstance, ?_, hp, ?_⟩
  · let := abelian_coherentAdicSystems B S hS F hF 𝓘 hZ hN hIcart
    have := ((ShortComplex.mk α γ
      (comp_coherentAdicCokernelπ B S hS F hF 𝓘 α)).exact_of_g_is_cokernel
        (coherentAdicCokernelIsColimit B S hS F hF 𝓘 α)).epi_kernelLift
    let e := IsLimit.conePointUniqueUpToIso (kernelIsKernel γ) hlim
    have he : e.hom ≫ (completionFunctor B S hS F hF 𝓘 hI).map ι = kernel.ι γ :=
      IsLimit.conePointUniqueUpToIso_hom_comp (kernelIsKernel γ) hlim WalkingParallelPair.zero
    have hpe : p = kernel.lift γ α (comp_coherentAdicCokernelπ B S hS F hF 𝓘 α) ≫ e.hom := by
      refine (cancel_mono ((completionFunctor B S hS F hF 𝓘 hI).map ι)).1 ?_
      rw [Category.assoc, he, kernel.lift_ι]
      exact hp
    rw [hpe]
    exact epi_comp _ _
  · have hm : Mono ((ObjectProperty.ι (isCoherent.{u, u} B S hS F hF)).map
        (Abelian.factorThruCoimage g)) := Functor.map_mono _ _
    exact idealPowerMultiple_eq_bot_of_mono B S hS F hF 𝓘
      ((ObjectProperty.ι (isCoherent.{u, u} B S hS F hF)).map (Abelian.factorThruCoimage g))
      (n + 1) (hC n)

/-- **A surjection onto a completion whose levelwise kernels are annihilated by a power of `𝓘`
is, up to isomorphism, the completion of a surjection of coherent modules.**

Let `p : E ⟶ Q^∧` be a surjection with `ker p_k` annihilated by `𝓘 ^ t` for all `k`.  From some
level `m ≥ t - 1` on, the squares of `p` are pullback squares
(`AlgebraicGeometry.Space.exists_isPullback_transition_of_epi`, where Artin–Rees enters).  The
coherent module is the fibre product `P = Q ×_{Q / 𝓘 ᵐ⁺¹ Q} E_m`; its projection `a : P ⟶ Q` is
surjective with kernel `ker p_m`.  The pullback squares lift the projection `P ⟶ E_m` to
compatible maps `P ⟶ E_l` for every `l`, which descend to a morphism `c : P^∧ ⟶ E` with
`c ≫ p = a^∧`.  It is surjective at the lowest level, hence surjective (Stacks 08B3).  It is
injective: a morphism into `P^∧` killed by `c` is killed by `a^∧`, so by left exactness of the
completion (Stacks 08B5) it factors through the completion of `ker a`, and from level `m` on the
composite of that completion with `c` is a monomorphism, because `ker a ≅ ker p_m` maps
isomorphically onto its own completion there and injects into `E_m`. -/
theorem exists_algebraization_of_epi (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ F)
    {Q : CoherentModules.{u, u} B S hS F hF} {E : CoherentAdicSystems B S hS F hF 𝓘}
    (p : E ⟶ (completionFunctor B S hS F hF 𝓘 hI).obj Q) (hp : Epi p) (t : ℕ) (ht : 0 < t)
    (hker : ∀ k : ℕ, idealPowerMultiple B S hS F hF 𝓘 t (kernel (p.hom.app (op k))) = ⊥) :
    ∃ (M : CoherentModules.{u, u} B S hS F hF) (a : M ⟶ Q)
      (β : E ≅ (completionFunctor B S hS F hF 𝓘 hI).obj M),
      Epi a ∧ idealPowerMultiple B S hS F hF 𝓘 t (kernel a).obj = ⊥ ∧
        β.hom ≫ (completionFunctor B S hS F hF 𝓘 hI).map a = p := by
  have hIcart :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF 𝓘.toSheafOfModules hI
  have := preservesFiniteLimits_completionFunctor_of_isNoetherian B S hS F hF 𝓘 hI hZ hN
  obtain ⟨m₀, hm₀⟩ :=
    exists_isPullback_transition_of_epi B S hS F hF 𝓘 hZ hN hIcart p hp t ht hker
  set m := max m₀ t with hm
  have htm : t ≤ m + 1 := by omega
  let Em : CoherentModules.{u, u} B S hS F hF := ⟨E.obj.obj (op m), E.property.1 m⟩
  let Qm : CoherentModules.{u, u} B S hS F hF :=
    ⟨((completionFunctor B S hS F hF 𝓘 hI).obj Q).obj.obj (op m),
      ((completionFunctor B S hS F hF 𝓘 hI).obj Q).property.1 m⟩
  let πQ : Q ⟶ Qm := ObjectProperty.homMk (completionTermProjection B S hS F hF 𝓘 hI Q m)
  let pm : Em ⟶ Qm := ObjectProperty.homMk (p.hom.app (op m))
  have hpm : Epi pm :=
    (ObjectProperty.ι (isCoherent.{u, u} B S hS F hF)).epi_of_epi_map
      (epi_app_of_epi B S hS F hF 𝓘 p hp m)
  have hπQ : Epi πQ :=
    (ObjectProperty.ι (isCoherent.{u, u} B S hS F hF)).epi_of_epi_map
      (epi_completionTermProjection B S hS F hF 𝓘 hI Q m)
  let a : pullback πQ pm ⟶ Q := pullback.fst πQ pm
  let q : pullback πQ pm ⟶ Em := pullback.snd πQ pm
  have hcond : q.hom ≫ p.hom.app (op m) =
      a.hom ≫ completionTermProjection B S hS F hF 𝓘 hI Q m :=
    (congrArg InducedCategory.Hom.hom (pullback.condition (f := πQ) (g := pm))).symm
  -- the compatible lifts
  have hsq : ∀ j : ℕ, IsPullback (p.hom.app (op (m + j + 1)))
      (E.obj.map (homOfLE (Nat.le_succ (m + j))).op)
      (((completionFunctor B S hS F hF 𝓘 hI).obj Q).obj.map (homOfLE (Nat.le_succ (m + j))).op)
      (p.hom.app (op (m + j))) := fun j =>
    hm₀ (m + j) (by omega) (m + j + 1) (Nat.le_succ (m + j))
  let y : ∀ j : ℕ, (pullback πQ pm).obj ⟶
      ((completionFunctor B S hS F hF 𝓘 hI).obj Q).obj.obj (op (m + j)) := fun j =>
    a.hom ≫ completionTermProjection B S hS F hF 𝓘 hI Q (m + j)
  have hy : ∀ j : ℕ, y (j + 1) ≫
      ((completionFunctor B S hS F hF 𝓘 hI).obj Q).obj.map (homOfLE (Nat.le_succ (m + j))).op =
        y j := fun j => by
    simp only [y, Category.assoc]
    rw [completionTermProjection_transition]
  let φ : ∀ l : ℕ, (pullback πQ pm).obj ⟶ E.obj.obj (op l) :=
    compatibleLiftAt B S hS F hF 𝓘 p m hsq y hy q.hom hcond
  have hφp : ∀ l : ℕ, φ l ≫ p.hom.app (op l) =
      a.hom ≫ completionTermProjection B S hS F hF 𝓘 hI Q l := fun l => by
    rw [compatibleLiftAt_comp]
    simp only [y, Category.assoc]
    rw [completionTermProjection_transition]
  have hφzero : ∀ l : ℕ, (idealPowerMultiple B S hS F hF 𝓘 (l + 1) (pullback πQ pm).obj).ι ≫
      φ l = 0 := fun l => by
    have h := idealPowerMultiple_ι_comp_comp_eq_zero B S hS F hF 𝓘 (l + 1) (φ l) (𝟙 _)
      ((Category.comp_id _).trans (submodule_ι_eq_zero_of_eq_bot B S hS F hF (E.property.2.1 l)))
    rwa [Category.comp_id] at h
  -- the comparison morphism `c : P^∧ ⟶ E`
  let cl : ∀ l : ℕ,
      ((completionFunctor B S hS F hF 𝓘 hI).obj (pullback πQ pm)).obj.obj (op l) ⟶
        E.obj.obj (op l) := fun l => cokernel.desc _ (φ l) (hφzero l)
  have hcl : ∀ l : ℕ, completionTermProjection B S hS F hF 𝓘 hI (pullback πQ pm) l ≫ cl l = φ l :=
    fun l => cokernel.π_desc _ _ _
  have hclnat : ∀ (l l' : ℕ) (h : l ≤ l'),
      ((completionFunctor B S hS F hF 𝓘 hI).obj (pullback πQ pm)).obj.map (homOfLE h).op ≫ cl l =
        cl l' ≫ E.obj.map (homOfLE h).op := by
    intro l l' h
    refine (cancel_epi (completionTermProjection B S hS F hF 𝓘 hI (pullback πQ pm) l')).1 ?_
    refine ((Category.assoc _ _ _).symm.trans ?_).trans (Category.assoc _ _ _)
    refine (congrArg (· ≫ cl l)
      (completionTermProjection_transition B S hS F hF 𝓘 hI (pullback πQ pm) h)).trans ?_
    refine (hcl l).trans ?_
    refine Eq.trans ?_ (congrArg (· ≫ E.obj.map (homOfLE h).op) (hcl l')).symm
    exact (compatibleLiftAt_comp_map B S hS F hF 𝓘 p m hsq y hy q.hom hcond h).symm
  let c : (completionFunctor B S hS F hF 𝓘 hI).obj (pullback πQ pm) ⟶ E :=
    ObjectProperty.homMk
      { app := fun x => cl x.unop
        naturality := by
          rintro ⟨l'⟩ ⟨l⟩ f
          have h : l ≤ l' := leOfHom f.unop
          obtain rfl : f = (homOfLE h).op := Subsingleton.elim _ _
          exact hclnat l l' h }
  have hc : ∀ l : ℕ, completionTermProjection B S hS F hF 𝓘 hI (pullback πQ pm) l ≫
      c.hom.app (op l) = φ l := hcl
  have hcp : c ≫ p = (completionFunctor B S hS F hF 𝓘 hI).map a := by
    ext1
    refine NatTrans.ext (funext fun lv => ?_)
    obtain ⟨l⟩ := lv
    refine (cancel_epi (completionTermProjection B S hS F hF 𝓘 hI (pullback πQ pm) l)).1 ?_
    change _ ≫ c.hom.app (op l) ≫ p.hom.app (op l) = _
    rw [← Category.assoc, hc, hφp, completionTermProjection_naturality]
  -- surjectivity of `c`
  have hqepi : Epi q := Abelian.epi_pullback_of_epi_f πQ pm
  have hqepi' : Epi q.hom := Functor.map_epi (ObjectProperty.ι (isCoherent.{u, u} B S hS F hF)) q
  have hcepi : Epi c := by
    refine epi_of_epi_app_zero B S hS F hF 𝓘 c ?_
    have h0 : φ 0 = q.hom ≫ E.obj.map (homOfLE (Nat.zero_le m)).op := by
      change compatibleLiftAt B S hS F hF 𝓘 p m hsq y hy q.hom hcond 0 = _
      rw [← compatibleLiftAt_comp_map B S hS F hF 𝓘 p m hsq y hy q.hom hcond (Nat.zero_le m),
        compatibleLiftAt_base]
    have := epi_map_homOfLE_of_isCoherentAdicSystem B S hS F hF 𝓘 E.property (Nat.zero_le m)
    have hφ0 : Epi (φ 0) := by rw [h0]; infer_instance
    rw [← hc 0] at hφ0
    exact epi_of_epi (completionTermProjection B S hS F hF 𝓘 hI (pullback πQ pm) 0) _
  -- the kernel of `a`
  have hDq : Mono (kernel.ι a ≫ q) := by
    refine Preadditive.mono_of_cancel_zero _ fun {T} x hx => ?_
    have h1 : (x ≫ kernel.ι a) ≫ a = 0 := by rw [Category.assoc, kernel.condition, comp_zero]
    have h2 : x ≫ kernel.ι a = 0 :=
      pullback.hom_ext (by rw [h1, zero_comp]) (by rw [Category.assoc, hx, zero_comp])
    exact zero_of_comp_mono (kernel.ι a) h2
  have hDq' : Mono ((kernel.ι a).hom ≫ q.hom) :=
    Functor.map_mono (ObjectProperty.ι (isCoherent.{u, u} B S hS F hF)) (kernel.ι a ≫ q)
  have hDann : idealPowerMultiple B S hS F hF 𝓘 t (kernel a).obj = ⊥ := by
    have hz : ((kernel.ι a).hom ≫ q.hom) ≫ p.hom.app (op m) = 0 := by
      rw [Category.assoc, hcond, ← Category.assoc]
      change (kernel.ι a ≫ a).hom ≫ _ = 0
      rw [kernel.condition]
      exact zero_comp
    exact idealPowerMultiple_eq_bot_of_comp_eq_zero B S hS F hF 𝓘 _ _ hz t (hker m)
  -- injectivity of `c`
  have hlimD := KernelFork.mapIsLimit _ (kernelIsKernel a) (completionFunctor B S hS F hF 𝓘 hI)
  have hcmono : Mono c := by
    refine Preadditive.mono_of_cancel_zero _ fun {T} h hh => ?_
    have hha : h ≫ (completionFunctor B S hS F hF 𝓘 hI).map a = 0 := by
      rw [← hcp, ← Category.assoc, hh, zero_comp]
    obtain ⟨h', hh'₀⟩ := KernelFork.IsLimit.lift' hlimD h hha
    have hh' : h' ≫ (completionFunctor B S hS F hF 𝓘 hI).map (kernel.ι a) = h := hh'₀
    have hz : h' = 0 := by
      refine eq_zero_of_app_eq_zero_of_le B S hS F hF 𝓘 h' m fun l hl => ?_
      have hD := isIso_completionTermProjection_of_annihilated B S hS F hF 𝓘 hI (kernel a) l
        (idealPowerMultiple_eq_bot_of_le B S hS F hF 𝓘 (htm.trans (Nat.add_le_add_right hl 1))
          _ hDann)
      have hmono : Mono (((completionFunctor B S hS F hF 𝓘 hI).map (kernel.ι a)).hom.app (op l) ≫
          c.hom.app (op l)) := by
        have hfac : completionTermProjection B S hS F hF 𝓘 hI (kernel a) l ≫
            (((completionFunctor B S hS F hF 𝓘 hI).map (kernel.ι a)).hom.app (op l) ≫
              c.hom.app (op l)) = (kernel.ι a).hom ≫ φ l := by
          rw [← Category.assoc, completionTermProjection_naturality, Category.assoc, hc]
        have hm2 : Mono ((kernel.ι a).hom ≫ φ l) := by
          have : ((kernel.ι a).hom ≫ φ l) ≫ E.obj.map (homOfLE hl).op =
              (kernel.ι a).hom ≫ q.hom := by
            rw [Category.assoc, compatibleLiftAt_comp_map_base]
          exact mono_of_mono_fac this
        have : ((completionFunctor B S hS F hF 𝓘 hI).map (kernel.ι a)).hom.app (op l) ≫
            c.hom.app (op l) = inv (completionTermProjection B S hS F hF 𝓘 hI (kernel a) l) ≫
              ((kernel.ι a).hom ≫ φ l) := by
          rw [← hfac, IsIso.inv_hom_id_assoc]
        rw [this]
        infer_instance
      have h1 : h'.hom.app (op l) ≫
          (((completionFunctor B S hS F hF 𝓘 hI).map (kernel.ι a)).hom.app (op l) ≫
            c.hom.app (op l)) = 0 :=
        congrArg (fun k => k.hom.app (op l))
          (show h' ≫ (completionFunctor B S hS F hF 𝓘 hI).map (kernel.ι a) ≫ c = 0 by
            rw [← Category.assoc, hh', hh])
      exact (cancel_mono _).1 (h1.trans zero_comp.symm)
    rw [← hh', hz, zero_comp]
  let := abelian_coherentAdicSystems B S hS F hF 𝓘 hZ hN hIcart
  have : IsIso c := isIso_of_mono_of_epi c
  have haepi : Epi a := Abelian.epi_pullback_of_epi_g πQ pm
  refine ⟨pullback πQ pm, a, (asIso c).symm, haepi, hDann, ?_⟩
  rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq, hcp]

/-! ### Stacks 08BB -/

/-- **Existence of the algebraization of a map into a completion.**  On a Noetherian algebraic
space, a map `α : E ⟶ G^∧` in `Coh(F, 𝓘)` whose levelwise kernels and cokernels are annihilated
by one power of `𝓘` is `β ≫ a^∧` for a map `a : M ⟶ G` of coherent modules whose kernel and
cokernel are annihilated by a power of `𝓘` and an isomorphism `β : E ≅ M^∧`.

`AlgebraicGeometry.Space.exists_image_algebraization` realizes the image of `α` as the
completion of a coherent submodule `Q ⊆ G`, with `α = p ≫ (Q ⊆ G)^∧` for a surjection `p`;
the levelwise kernels of `p` lie in those of `α`, and
`AlgebraicGeometry.Space.exists_algebraization_of_epi` algebraizes `p`. -/
theorem exists_algebraization (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ F)
    {G : CoherentModules.{u, u} B S hS F hF} {E : CoherentAdicSystems B S hS F hF 𝓘}
    (α : E ⟶ (completionFunctor B S hS F hF 𝓘 hI).obj G)
    (hα : ∃ t : ℕ, 0 < t ∧ ∀ k : ℕ,
      idealPowerMultiple B S hS F hF 𝓘 t (kernel (α.hom.app (op k))) = ⊥ ∧
        idealPowerMultiple B S hS F hF 𝓘 t (cokernel (α.hom.app (op k))) = ⊥) :
    ∃ (M : CoherentModules.{u, u} B S hS F hF) (a : M ⟶ G)
      (β : E ≅ (completionFunctor B S hS F hF 𝓘 hI).obj M),
      IsMapKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 a ∧
        α = β.hom ≫ (completionFunctor B S hS F hF 𝓘 hI).map a := by
  obtain ⟨t, ht, h⟩ := hα
  obtain ⟨Q, ι, p, hι, hp, hpα, hcok⟩ :=
    exists_image_algebraization B S hS F hF 𝓘 hI hZ hN α t ht fun k => (h k).2
  have hkerp : ∀ k : ℕ,
      idealPowerMultiple B S hS F hF 𝓘 t (kernel (p.hom.app (op k))) = ⊥ := fun k => by
    have hfac : p.hom.app (op k) ≫ ((completionFunctor B S hS F hF 𝓘 hI).map ι).hom.app (op k) =
        α.hom.app (op k) := congrArg (fun x => x.hom.app (op k)) hpα
    have hz : kernel.ι (p.hom.app (op k)) ≫ α.hom.app (op k) = 0 := by
      rw [← hfac, ← Category.assoc, kernel.condition, zero_comp]
    exact idealPowerMultiple_eq_bot_of_comp_eq_zero B S hS F hF 𝓘 _ _ hz t (h k).1
  obtain ⟨M, a, β, ha, hkera, hβ⟩ :=
    exists_algebraization_of_epi B S hS F hF 𝓘 hI hZ hN p hp t ht hkerp
  refine ⟨M, a ≫ ι, β, ⟨t, ht, ?_, ?_⟩, ?_⟩
  · exact idealPowerMultiple_eq_bot_of_iso B S hS F hF 𝓘
      ((ObjectProperty.ι (isCoherent.{u, u} B S hS F hF)).mapIso (kernelCompMono a ι).symm) t hkera
  · exact idealPowerMultiple_eq_bot_of_iso B S hS F hF 𝓘
      ((ObjectProperty.ι (isCoherent.{u, u} B S hS F hF)).mapIso (cokernelEpiComp a ι).symm) t hcok
  · rw [Functor.map_comp, ← Category.assoc, hβ, hpα]

/-- **Stacks 08BB.**  Let `F` be a Noetherian algebraic space, `𝓘 ⊆ 𝒪_F` a quasi-coherent sheaf
of ideals, `G` a coherent `𝒪_F`-module, `E` an object of `Coh(F, 𝓘)` and `α : E ⟶ G^∧` a map
whose kernel and cokernel are annihilated by a power of `𝓘`, in the sense of Remark 08BA (1):
one power `𝓘 ^ t` annihilates the kernels and the cokernels of all the components `α_k`.  Then
there exists a triple `(M, a, β)` of a coherent `𝒪_F`-module `M`, a map `a : M ⟶ G` whose kernel
and cokernel are annihilated by a power of `𝓘`, and an isomorphism `β : E ≅ M^∧` with
`α = β ≫ a^∧`; and it is unique up to unique isomorphism: for any second such triple
`(M', a', β')` there is exactly one isomorphism `e : M ≅ M'` with `e ≫ a' = a` and
`β ≫ e^∧ = β'`.

Existence is `AlgebraicGeometry.Space.exists_algebraization`, uniqueness is
`AlgebraicGeometry.Space.existsUnique_iso_of_algebraization_of_isNoetherian`.  The `Fact`
instance on the étale charts is the instance argument of the completion functor of Stacks 08B4,
needed for `G^∧` to be formed; it is implied by the Noetherian hypothesis (it is `hN.2.2`). -/
theorem existsUnique_algebraization (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ F)
    {G : CoherentModules.{u, u} B S hS F hF} {E : CoherentAdicSystems B S hS F hF 𝓘}
    (α : E ⟶ (completionFunctor B S hS F hF 𝓘 hI).obj G)
    (hα : ∃ t : ℕ, 0 < t ∧ ∀ k : ℕ,
      idealPowerMultiple B S hS F hF 𝓘 t (kernel (α.hom.app (op k))) = ⊥ ∧
        idealPowerMultiple B S hS F hF 𝓘 t (cokernel (α.hom.app (op k))) = ⊥) :
    ∃ (M : CoherentModules.{u, u} B S hS F hF) (a : M ⟶ G)
      (β : E ≅ (completionFunctor B S hS F hF 𝓘 hI).obj M),
      IsMapKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 a ∧
        α = β.hom ≫ (completionFunctor B S hS F hF 𝓘 hI).map a ∧
        ∀ (M' : CoherentModules.{u, u} B S hS F hF) (a' : M' ⟶ G)
          (β' : E ≅ (completionFunctor B S hS F hF 𝓘 hI).obj M'),
          IsMapKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 a' →
          α = β'.hom ≫ (completionFunctor B S hS F hF 𝓘 hI).map a' →
          ∃! e : M ≅ M', e.hom ≫ a' = a ∧
            β.hom ≫ (completionFunctor B S hS F hF 𝓘 hI).map e.hom = β'.hom := by
  obtain ⟨M, a, β, ha, hαa⟩ := exists_algebraization B S hS F hF 𝓘 hI hZ hN α hα
  exact ⟨M, a, β, ha, hαa, fun M' a' β' ha' hαa' =>
    existsUnique_iso_of_algebraization_of_isNoetherian B S hS F hF 𝓘 hI hZ hN α a a' β β' ha ha'
      hαa hαa'⟩

end Completion

end AlgebraicGeometry.Space

end
