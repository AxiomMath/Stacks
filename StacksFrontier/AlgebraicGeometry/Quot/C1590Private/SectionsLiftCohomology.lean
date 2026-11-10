module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerCohomologyReesFinite
public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSheavesProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional

/-!
# First cohomology of modules killed by a power of an ideal

Let `X` be an algebraic space, `φ : A ⟶ Γ(X, 𝒪_X)` a ring map, `𝔪 ⊆ A` a finitely generated
ideal and `F` an `𝒪_X`-module.  Suppose that the first cohomology of every quasi-coherent
quotient of a finite direct sum of copies of `F` which is killed by `𝔪` vanishes.  Then the same
holds for the quotients killed by a power of `𝔪`: a module killed by `𝔪ᴺ⁺¹` is an extension of
a module killed by `𝔪` by one killed by `𝔪ᴺ`, both again quotients of finite sums of copies of
`F`, and the long exact cohomology sequence does the rest.

## Main definitions

* `AlgebraicGeometry.C1590Private.IsKilledBy`: multiplication by every element of an ideal
  vanishes on a module.
* `AlgebraicGeometry.C1590Private.IsFiniteQuotient`: a module is a quotient of a finite direct
  sum of copies of another.

## Main results

* `AlgebraicGeometry.C1590Private.isZero_cohomology_one_of_isKilledBy_pow`: the vanishing for
  modules killed by a power of the ideal, from the vanishing for modules killed by the ideal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.C1590Private

attribute [local instance] Space.hasInjectiveResolutions_modules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {A : Type u} [CommRing A]
  (φ : A →+* ↥(GlobalSectionRing ((Stacks.SheafOfModules.Tensor.ringSheaf
    (Space.smallEtaleRingedSite B S hS X.1 X.2).O))))

/-- An `𝒪_X`-module is *killed* by an ideal `J ⊆ A` when multiplication by `φ a` vanishes on
it for every `a ∈ J`. -/
def IsKilledBy (J : Ideal A) (G : Space.Modules.{u, u} B S hS X.1 X.2) : Prop :=
  ∀ a ∈ J, globalSmul _ (φ a) G = 0

/-- `G` is a quotient of a finite direct sum of copies of `F`. -/
def IsFiniteQuotient (F G : Space.Modules.{u, u} B S hS X.1 X.2) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (p : (∐ fun _ : ι => F) ⟶ G), Epi p

variable {φ}

/-- A quotient of a quotient of a finite sum of copies of `F` is one. -/
theorem IsFiniteQuotient.of_epi {F G G' : Space.Modules.{u, u} B S hS X.1 X.2}
    (h : IsFiniteQuotient F G) (g : G ⟶ G') [Epi g] : IsFiniteQuotient F G' := by
  obtain ⟨ι, hι, p, hp⟩ := h
  exact ⟨ι, hι, p ≫ g, epi_comp _ _⟩

/-- A quotient of a finite sum of copies of a quotient of a finite sum of copies of `F` is a
quotient of a finite sum of copies of `F`. -/
theorem IsFiniteQuotient.sigma {F G : Space.Modules.{u, u} B S hS X.1 X.2}
    (h : IsFiniteQuotient F G) (κ : Type) [Finite κ] :
    IsFiniteQuotient F (∐ fun _ : κ => G) := by
  obtain ⟨ι, hι, p, hp⟩ := h
  exact ⟨Σ _ : κ, ι, inferInstance,
    (sigmaSigmaIso (fun _ : κ => ι) (fun _ _ => F)).inv ≫ Limits.Sigma.map fun _ => p,
    @epi_comp _ _ _ _ _ _ (IsIso.epi_of_iso _) _ inferInstance⟩

/-- A module killed by the unit ideal is zero. -/
theorem IsKilledBy.isZero_of_top {G : Space.Modules.{u, u} B S hS X.1 X.2}
    (h : IsKilledBy φ ⊤ G) : IsZero G := by
  rw [IsZero.iff_id_eq_zero, ← globalSmul_one, ← map_one φ]
  exact h 1 Submodule.mem_top

/-- Multiplication by a linear combination of elements is the linear combination of the
multiplications. -/
theorem globalSmul_sum {ι : Type*} (s : Finset ι) (c g : ι → A)
    (G : Space.Modules.{u, u} B S hS X.1 X.2) :
    globalSmul _ (φ (∑ i ∈ s, c i * g i)) G =
      ∑ i ∈ s, globalSmul _ (φ (c i)) G ≫ globalSmul _ (φ (g i)) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [globalSmul_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, map_add, globalSmul_add, ih, map_mul,
      globalSmul_mul]

/-- The `𝒪_X`-modules at the universe of the structure rings have enough injectives. -/
local instance (priority := 5000) enoughInjectives_modules_sectionsLift :
    EnoughInjectives (Space.Modules.{u, u} B S hS X.1 X.2) :=
  Space.enoughInjectives_modules B S hS X.1 X.2

variable (φ) in
/-- Multiplication by finitely many functions `φ (g i)`, as one morphism out of a direct sum. -/
abbrev generatorsSmul {s : ℕ} (g : Fin s → A) (G : Space.Modules.{u, u} B S hS X.1 X.2) :
    (∐ fun _ : Fin s => G) ⟶ G :=
  Sigma.desc fun i => globalSmul _ (φ (g i)) G

/-- The short exact sequence `0 ⟶ 𝔪 G ⟶ G ⟶ G / 𝔪 G ⟶ 0` for the image `𝔪 G` of
multiplication by finitely many functions. -/
abbrev generatorsShortComplex (u' : Space.Modules.{u, u} B S hS X.1 X.2)
    {G : Space.Modules.{u, u} B S hS X.1 X.2} (v : u' ⟶ G) :
    ShortComplex (Space.Modules.{u, u} B S hS X.1 X.2) :=
  ShortComplex.mk (kernel.ι (cokernel.π v)) (cokernel.π v) (kernel.condition _)

/-- The sequence `0 ⟶ ker (G ⟶ coker v) ⟶ G ⟶ coker v ⟶ 0` is short exact. -/
theorem generatorsShortComplex_shortExact (u' : Space.Modules.{u, u} B S hS X.1 X.2)
    {G : Space.Modules.{u, u} B S hS X.1 X.2} (v : u' ⟶ G) :
    (generatorsShortComplex u' v).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  mono_f := inferInstanceAs (Mono (kernel.ι (cokernel.π v)))
  epi_g := inferInstanceAs (Epi (cokernel.π v))

/-- If multiplication by `φ a` on `Y` factors through `f : X' ⟶ Y`, it vanishes on `coker f`. -/
private theorem globalSmul_cokernel_eq_zero {X' Y : Space.Modules.{u, u} B S hS X.1 X.2}
    (f : X' ⟶ Y) {a : A} (h : Y ⟶ X') (hh : globalSmul _ (φ a) Y = h ≫ f) :
    globalSmul _ (φ a) (cokernel f) = 0 := by
  refine zero_of_epi_comp (cokernel.π f) ?_
  rw [comp_globalSmul, hh, Category.assoc, cokernel.condition, comp_zero]

/-- The cokernel of multiplication by generators of `𝔪` is killed by `𝔪`. -/
private theorem isKilledBy_cokernel_generatorsSmul {m : Ideal A} {s : ℕ} {g : Fin s → A}
    (hg : Submodule.span A (Set.range g) = m) (G : Space.Modules.{u, u} B S hS X.1 X.2) :
    IsKilledBy φ m (cokernel (generatorsSmul φ g G)) := by
  intro a ha
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 (hg ▸ ha)
  refine globalSmul_cokernel_eq_zero _
    (∑ i, globalSmul _ (φ (c i)) G ≫ Sigma.ι (fun _ : Fin s => G) i) ?_
  simp only [smul_eq_mul]
  rw [globalSmul_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Category.assoc, generatorsSmul, Sigma.ι_comp_desc]

/-- **Vanishing of `H¹` for modules killed by a power of an ideal.**  Let `𝔪 ⊆ A` be finitely
generated and suppose that `H¹(X, G) = 0` for every quasi-coherent quotient `G` of a finite sum
of copies of `F` which is killed by `𝔪`.  Then `H¹(X, G) = 0` for every such quotient killed by
some power `𝔪ᴺ`. -/
theorem isZero_cohomology_one_of_isKilledBy_pow (F : Space.Modules.{u, u} B S hS X.1 X.2)
    (m : Ideal A) (hm : m.FG)
    (H₀ : ∀ G : Space.Modules.{u, u} B S hS X.1 X.2, G.IsQuasicoherentOnSite →
      IsFiniteQuotient F G → IsKilledBy φ m G →
        IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 1).obj G)) :
    ∀ (N : ℕ) (G : Space.Modules.{u, u} B S hS X.1 X.2), G.IsQuasicoherentOnSite →
      IsFiniteQuotient F G → IsKilledBy φ (m ^ N) G →
        IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 1).obj G) := by
  obtain ⟨s, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hm
  have hgm : ∀ i, g i ∈ m := fun i => hg ▸ Submodule.subset_span ⟨i, rfl⟩
  intro N
  induction N with
  | zero =>
    intro G _ _ hk
    rw [pow_zero, Ideal.one_eq_top] at hk
    exact Functor.map_isZero _ hk.isZero_of_top
  | succ N ih =>
    intro G hG hq hk
    set O := Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS X.1 X.2).O
    set Γ := globalSectionsFunctor.{u + 1, u, u, u} O
    have := hG
    let v := generatorsSmul φ g G
    have : (∐ fun _ : Fin s => G).IsQuasicoherentOnSite :=
      Space.isQuasicoherentOnSite_of_isColimit_cofan B S hS X.1 X.2 _
        (coproductIsCoproduct fun _ : Fin s => G) fun _ => hG
    have hQ : (cokernel v).IsQuasicoherentOnSite :=
      Space.isQuasicoherentOnSite_cokernel_unconditional B S hS X.1 X.2 v
    have hK : (kernel (cokernel.π v)).IsQuasicoherentOnSite :=
      Space.isQuasicoherentOnSite_kernel_of_quasicoherent B S hS X.1 X.2 (cokernel.π v)
    let w : (∐ fun _ : Fin s => G) ⟶ kernel (cokernel.π v) :=
      kernel.lift _ v (cokernel.condition v)
    have : Epi w := inferInstanceAs (Epi (Abelian.factorThruImage v))
    have h₃ : IsZero ((Γ.rightDerived 1).obj (cokernel v)) :=
      H₀ _ hQ (hq.of_epi (cokernel.π v)) (isKilledBy_cokernel_generatorsSmul hg G)
    have h₁ : IsZero ((Γ.rightDerived 1).obj (kernel (cokernel.π v))) := by
      refine ih _ hK ((hq.sigma (Fin s)).of_epi w) fun a ha => ?_
      have key : v ≫ globalSmul O (φ a) G = 0 := by
        refine Sigma.hom_ext _ _ fun i => ?_
        rw [Sigma.ι_comp_desc_assoc, comp_zero, ← globalSmul_mul, ← map_mul]
        refine hk _ ?_
        rw [pow_succ']
        exact Ideal.mul_mem_mul (hgm i) ha
      refine zero_of_comp_mono (kernel.ι (cokernel.π v)) (zero_of_epi_comp w ?_)
      calc w ≫ globalSmul O (φ a) (kernel (cokernel.π v)) ≫ kernel.ι (cokernel.π v)
          = w ≫ kernel.ι (cokernel.π v) ≫ globalSmul O (φ a) G := by
            rw [comp_globalSmul O (φ a) (kernel.ι (cokernel.π v))]
        _ = v ≫ globalSmul O (φ a) G := kernel.lift_ι_assoc _ _ _ _
        _ = 0 := key
    exact Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₂
      (generatorsShortComplex_shortExact _ v) _ 1 h₁ h₃

/-- **`J F` is a quotient of finitely many copies of `F`** when `J` is finitely generated:
multiplication by the generators. -/
theorem isFiniteQuotient_idealMultiple (F : Space.Modules.{u, u} B S hS X.1 X.2) (J : Ideal A)
    (hJ : J.FG) : IsFiniteQuotient F (Space.idealMultiple φ F J) := by
  obtain ⟨s, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hJ
  have hgJ : ∀ i, g i ∈ J := fun i => hg ▸ Submodule.subset_span ⟨i, rfl⟩
  let p : (∐ fun _ : Fin s => F) ⟶ Space.idealMultiple φ F J :=
    Sigma.desc fun i => Space.idealMultipleFactor φ F J (hgJ i)
  refine ⟨Fin s, inferInstance, p, ⟨fun {Z} h h' e => ?_⟩⟩
  refine Space.idealMultiple_hom_ext φ F J fun a ha => ?_
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 (hg ▸ ha)
  have hfac : Space.idealMultipleFactor φ F J ha =
      ∑ i, globalSmul _ (φ (c i)) F ≫ Sigma.ι (fun _ : Fin s => F) i ≫ p := by
    refine (cancel_mono (Space.idealMultipleι φ F J)).1 ?_
    rw [Space.idealMultipleFactor_ι, Preadditive.sum_comp]
    simp only [smul_eq_mul, Category.assoc, Sigma.ι_comp_desc_assoc, Space.idealMultipleFactor_ι, p]
    exact globalSmul_sum _ c g F
  rw [hfac, Preadditive.sum_comp, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Category.assoc, e]

/-- The cokernel of `𝔪^{c+2} F ⟶ 𝔪 F` is killed by `𝔪^{c+1}`. -/
private theorem isKilledBy_cokernel_idealMultipleMap (F : Space.Modules.{u, u} B S hS X.1 X.2)
    (m : Ideal A) (c : ℕ) :
    IsKilledBy φ (m ^ (c + 1)) (cokernel (Space.idealMultipleMap φ F (m ^ 1) 1
      (Space.one_mem_pow_of_le m (Nat.le_add_right 1 (c + 1))))) := by
  intro a ha
  have hmul : ∀ b ∈ m ^ 1, b * a ∈ m ^ (1 + (c + 1)) := fun b hb => by
    rw [pow_add]
    exact Ideal.mul_mem_mul hb ha
  refine globalSmul_cokernel_eq_zero _
    (Space.idealMultipleMap φ F (m ^ (1 + (c + 1))) a hmul) ?_
  refine (cancel_mono (Space.idealMultipleι φ F (m ^ 1))).1 ?_
  rw [Category.assoc, Space.idealMultipleMap_one_ι φ F
    (Ideal.pow_le_pow_right (I := m) (Nat.le_add_right 1 (c + 1))), Space.idealMultipleMap_ι,
    comp_globalSmul]

/-- The connecting map `H⁰(X, F / 𝔪 F) ⟶ H¹(X, 𝔪 F)` vanishes when some `r ∈ 1 + 𝔪` kills
`H¹(X, 𝔪 F)`. -/
private theorem delta_idealShortComplex_eq_zero (F : Space.Modules.{u, u} B S hS X.1 X.2)
    (m : Ideal A) {r : A} (hr1 : r - 1 ∈ m ^ 1)
    (hr : ∀ x ∈ (⊤ : Submodule A (Space.cohomologyIdealPower φ F m 1 1)), r • x = 0) :
    (Stacks.Cohomology.RightDerivedDelta.horseshoe
      (Space.idealShortComplex_shortExact φ F (m ^ 1))).delta
        (globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.smallEtaleRingedSite B S hS X.1 X.2).O)) 0 = 0 := by
  let Γ := globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (Space.smallEtaleRingedSite B S hS X.1 X.2).O)
  let H := Stacks.Cohomology.RightDerivedDelta.horseshoe
    (Space.idealShortComplex_shortExact φ F (m ^ 1))
  have hr' : globalSmul _ (φ r) (Space.idealQuotient φ F (m ^ 1)) = 𝟙 _ := by
    have h0 := Space.globalSmul_idealQuotient_eq_zero φ F (m ^ 1) hr1
    rw [map_sub, map_one] at h0
    rw [show φ r = (φ r - 1) + 1 by ring, globalSmul_add, h0, zero_add, globalSmul_one]
  refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
  let s' : Space.cohomologyRes φ 0 (Space.idealQuotient φ F (m ^ 1)) := s
  have hs : r • s' = s' := by
    have h1 := Space.cohomologyResMap_globalSmul φ 0 r (M := Space.idealQuotient φ F (m ^ 1)) s'
    rw [hr', Space.cohomologyResMap_id_apply] at h1
    exact h1.symm
  let δ := (H.delta Γ 0).hom
  have h3 : (φ r) • s = s := hs
  change δ s = 0
  rw [← h3, map_smul]
  exact hr (δ s) Submodule.mem_top

/-- **Sections of `F` onto sections of `F / 𝔪 F`.**  Let `𝔪 ⊆ A` be finitely generated, let `F`
be quasi-coherent with `H¹(X, 𝔪 F)` finite over `A`, let `c` be an integer such that the image of
`H¹(X, 𝔪^{c+2} F) ⟶ H¹(X, 𝔪 F)` lies in `𝔪 H¹(X, 𝔪 F)` (Stacks 08AX), and suppose that
`H¹(X, G) = 0` for every quasi-coherent quotient `G` of a finite sum of copies of `F` killed by a
power of `𝔪`.  Then `H⁰(X, F) ⟶ H⁰(X, F / 𝔪 F)` is onto.

The vanishing for `G = 𝔪 F / 𝔪^{c+2} F` makes `H¹(X, 𝔪^{c+2} F) ⟶ H¹(X, 𝔪 F)` onto, so
`H¹(X, 𝔪 F) = 𝔪 H¹(X, 𝔪 F)` and Nakayama gives `r ∈ 1 + 𝔪` killing it.  The connecting map
`H⁰(X, F / 𝔪 F) ⟶ H¹(X, 𝔪 F)` is linear, `r` acts as `1` on its source and as `0` on its
target, so it vanishes. -/
theorem epi_rightDerived_zero_map_idealQuotientπ (F : Space.Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (m : Ideal A) (hm : m.FG)
    (hfin : Module.Finite A (Space.cohomologyRes φ 1 (Space.idealMultiple φ F (m ^ 1))))
    (c : ℕ) (hc : LinearMap.range (Space.cohomologyIdealPowerTr φ F m 1
      (Nat.le_add_right 1 (c + 1))) ≤ m ^ (c + 1 - c) • (⊤ : Submodule A
        (Space.cohomologyIdealPower φ F m 1 1)))
    (hvan : ∀ (N : ℕ) (G : Space.Modules.{u, u} B S hS X.1 X.2), G.IsQuasicoherentOnSite →
      IsFiniteQuotient F G → IsKilledBy φ (m ^ N) G →
        IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 1).obj G)) :
    Epi (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 0).map
        (Space.idealQuotientπ φ F (m ^ 1))) := by
  set O := Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS X.1 X.2).O
  set Γ := globalSectionsFunctor.{u + 1, u, u, u} O
  have := hF
  -- the short exact sequence `0 ⟶ 𝔪^{c+2} F ⟶ 𝔪 F ⟶ Q ⟶ 0`
  let ιc := Space.idealMultipleMap φ F (m ^ 1) 1
    (Space.one_mem_pow_of_le m (Nat.le_add_right 1 (c + 1)))
  have : Mono ιc := mono_of_mono_fac (Space.idealMultipleMap_one_ι φ F
    (Ideal.pow_le_pow_right (I := m) (Nat.le_add_right 1 (c + 1))))
  let T := ShortComplex.mk ιc (cokernel.π ιc) (cokernel.condition _)
  have hT : T.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
      mono_f := inferInstanceAs (Mono ιc)
      epi_g := inferInstanceAs (Epi (cokernel.π ιc)) }
  have := Space.isQuasicoherentOnSite_idealMultiple φ F (m ^ 1) hF
  have := Space.isQuasicoherentOnSite_idealMultiple φ F (m ^ (1 + (c + 1))) hF
  have hQ : IsZero ((Γ.rightDerived 1).obj (cokernel ιc)) :=
    hvan _ _ (Space.isQuasicoherentOnSite_cokernel_unconditional B S hS X.1 X.2 ιc)
      ((isFiniteQuotient_idealMultiple F (m ^ 1) (by rwa [pow_one])).of_epi (cokernel.π ιc))
      (isKilledBy_cokernel_idealMultipleMap F m c)
  -- `H¹(X, 𝔪^{c+2} F) ⟶ H¹(X, 𝔪 F)` is onto
  have hepi : Epi ((Γ.rightDerived 1).map ιc) :=
    (((Stacks.Cohomology.RightDerivedDelta.horseshoe hT).exact_composableArrows₅ Γ 1).exact 0).epi_f
      (hQ.eq_of_tgt _ _)
  have hsurj : Function.Surjective (Space.cohomologyIdealPowerTr φ F m 1
      (Nat.le_add_right 1 (c + 1))) :=
    (ModuleCat.epi_iff_surjective ((Γ.rightDerived 1).map ιc)).1 hepi
  have hle : (⊤ : Submodule A (Space.cohomologyIdealPower φ F m 1 1)) ≤
      m ^ 1 • (⊤ : Submodule A (Space.cohomologyIdealPower φ F m 1 1)) :=
    calc (⊤ : Submodule A (Space.cohomologyIdealPower φ F m 1 1))
        = LinearMap.range (Space.cohomologyIdealPowerTr φ F m 1
            (Nat.le_add_right 1 (c + 1))) := (LinearMap.range_eq_top.2 hsurj).symm
      _ ≤ m ^ (c + 1 - c) • ⊤ := hc
      _ = m ^ 1 • ⊤ := by rw [show c + 1 - c = 1 by omega]
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul (m ^ 1)
    (⊤ : Submodule A (Space.cohomologyIdealPower φ F m 1 1)) (Module.Finite.fg_top) hle
  -- the connecting map vanishes
  exact (((Stacks.Cohomology.RightDerivedDelta.horseshoe
    (Space.idealShortComplex_shortExact φ F (m ^ 1))).exact_composableArrows₅ Γ 0).exact 1).epi_f
      (delta_idealShortComplex_eq_zero F m hr1 hr)

end AlgebraicGeometry.C1590Private

end
