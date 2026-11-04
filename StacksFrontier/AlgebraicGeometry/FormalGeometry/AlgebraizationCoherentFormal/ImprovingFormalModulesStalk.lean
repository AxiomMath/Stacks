module

public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalities
public import StacksFrontier.AlgebraicGeometry.Divisors.DepthOneQuotient.AffineSections
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.Stalkwise
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CompletedStalkFinite
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Transition
public import StacksFrontier.RingTheory.LocalCohomology.SupportedSectionsEssentiallyConstant

/-!
# The local hypothesis of Stacks 0EJE at a point, read off the completed stalk

Let `X` be a locally Noetherian scheme, `ℐ` a quasi-coherent ideal sheaf, `(ℱ_n)` an object of
`Coh(X, ℐ)` and `U` an affine open with ring `R = Γ(X, U)`. The modules of sections
`Γ(ℱ_n, U)` form an inverse system of finite `R`-modules with surjective transitions and kernels
`ℐ(U)^{n+1} Γ(ℱ_{n+1}, U)`.

At a point `y ∈ U ∩ V(ℐ)` with prime `𝔮 ⊆ R`, the depth hypothesis of Stacks, Tag 0EJE on the
completed stalk `ℱ_y^∧` — no nonmaximal prime `𝔭` of `𝒪_{X,y}^∧` with
`V(𝔭) ∩ V(ℐ𝒪_{X,y}^∧) = {𝔪_y^∧}` has `depth((ℱ_y^∧)_𝔭) = 0` — implies the local hypothesis
`Stacks.LocalCohomology.LocalTorsionProZeroAt` of the essential constancy theorem at `𝔮`. Given
a compatible system `Λ` of submodules of the `Γ(ℱ_n, U)`, the submodules of `ℱ_y^∧` lying over the
`𝒪_{X,y}`-spans of the germs of `Λ_n` form a filtration of the formal module `ℱ_y^∧` to which
`Stacks.LocalCohomology.FormalFiltration.exists_forall_pow_smul_mem_imp_mem` applies; the germ
maps `Γ(ℱ_n, U) → ℱ_{n,y}` are localizations at `𝔮`, which translates the conclusion back.

## Main definitions

* `Stacks.Algebraization.sectionsTower` — the inverse system of modules of sections over an open.
* `Stacks.Algebraization.completedStalkProj` — the projection of the completed stalk onto a stalk
  of the system.

## Main results

* `Stacks.Algebraization.localTorsionProZeroAt_sectionsTower` — the local hypothesis at a point
  of `U ∩ V(ℐ)` satisfying the depth condition of Stacks 0EJE.

## References

* [Stacks Project, Tag 0EJE](https://stacks.math.columbia.edu/tag/0EJE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace IsLocalRing
open Stacks.ModuleSkyscraper Stacks.ModuleStalkSpecialization Stacks.LocalCohomology

universe u

namespace Stacks.Algebraization

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {I : X.IdealSheafData}
  (F : Stacks.Coherent.CoherentAdicSystems I)

/-- The inverse system of modules of sections over an open `U` of a coherent adic system. -/
def sectionsTower (U : X.Opens) : ℕᵒᵖ ⥤ ModuleCat.{u} Γ(X, U) where
  obj n := ModuleCat.of Γ(X, U) Γ(F.obj.obj n, U)
  map f := ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap (F.obj.map f) U)
  map_id n := by
    ext x
    change (F.obj.map (𝟙 n)).app U x = x
    rw [F.obj.map_id]
    rfl
  map_comp f g := by
    ext x
    change (F.obj.map (f ≫ g)).app U x = (F.obj.map g).app U ((F.obj.map f).app U x)
    rw [F.obj.map_comp]
    rfl

omit [IsLocallyNoetherian X] in
/-- The transition maps of `sectionsTower` are the restrictions of the transition maps of the
system to sections over `U`. -/
theorem towerMap_sectionsTower_apply (U : X.Opens) {m n : ℕ} (h : m ≤ n)
    (x : Γ(F.obj.obj (op n), U)) :
    towerMap (sectionsTower F U) h x = (F.obj.map (homOfLE h).op).app U x :=
  rfl

/-- The projection of the completed stalk onto the stalk of the `n`-th term. -/
def completedStalkProj (y : X) (n : ℕ) :
    completedStalk I F y →ₗ[X.presheaf.stalk y] (modulesStalkFunctor X y).obj (F.obj.obj (op n)) :=
  (limit.π (F.obj ⋙ modulesStalkFunctor X y) (op n)).hom ∘ₗ
    (formalStalkEquivModuleStalkLimit F y).toLinearMap ∘ₗ
      (formalStalkEquivCompletedStalk F y).symm.toLinearMap

/-- The projection of the completed stalk onto each stalk of the system is surjective. -/
theorem completedStalkProj_surjective (y : X) (n : ℕ) :
    Function.Surjective (completedStalkProj F y n) :=
  (Stacks.Coherent.moduleLimit_projection_surjective (F.obj ⋙ modulesStalkFunctor X y)
    (fun k => surjective_stalk_coherentAdicTransition F y k) n).comp
    ((formalStalkEquivModuleStalkLimit F y).surjective.comp
      (formalStalkEquivCompletedStalk F y).symm.surjective)

/-- The kernel of the projection of the completed stalk onto the stalk of the `n`-th term is
`ℐ_y^{n+1}` times the completed stalk. -/
theorem completedStalkProj_ker (y : X) (n : ℕ) :
    LinearMap.ker (completedStalkProj F y n) =
      IdealSheafData.stalk I y ^ (n + 1) •
        (⊤ : Submodule (X.presheaf.stalk y) (completedStalk I F y)) := by
  have h₁ := Stacks.Coherent.moduleLimit_projection_ker (I := IdealSheafData.stalk I y)
    (F.obj ⋙ modulesStalkFunctor X y) (fun k => surjective_stalk_coherentAdicTransition F y k)
    (fun k => ker_stalk_coherentAdicTransition F y k) (Ideal.fg_of_isNoetherianRing _) n
  have h₂ := Stacks.Coherent.ker_comp_linearEquiv_pow_smul_top _
    (formalStalkEquivModuleStalkLimit F y) _ h₁
  exact Stacks.Coherent.ker_comp_linearEquiv_pow_smul_top _
    (formalStalkEquivCompletedStalk F y).symm _ h₂

/-- The projections of the completed stalk are compatible with the transition maps of the stalks
of the system. -/
theorem completedStalkProj_transition (y : X) {m n : ℕ} (h : m ≤ n) (z : completedStalk I F y) :
    ((modulesStalkFunctor X y).map (F.obj.map (homOfLE h).op)).hom (completedStalkProj F y n z) =
      completedStalkProj F y m z := by
  show ((limit.π (F.obj ⋙ modulesStalkFunctor X y) (op n)) ≫
    (F.obj ⋙ modulesStalkFunctor X y).map (homOfLE h).op).hom _ = _
  rw [limit.w]
  rfl

/-- The projection of the completed stalk onto the stalk of the `n`-th term vanishes exactly on
`ℐ_y^{n+1}` times the completed stalk. -/
private theorem completedStalkProj_eq_zero_iff (y : X) (n : ℕ) (p : completedStalk I F y) :
    completedStalkProj F y n p = 0 ↔
      p ∈ IdealSheafData.stalk I y ^ (n + 1) •
        (⊤ : Submodule (X.presheaf.stalk y) (completedStalk I F y)) := by
  rw [← completedStalkProj_ker F y n, LinearMap.mem_ker]

/-- The depth condition of Stacks 0EJE on the completed stalk at `y ∈ V(ℐ)` rules out associated
primes of the completed stalk whose closed fibre is the closed point. -/
private theorem notMem_associatedPrimes_completedStalk {y : X} (hyY : y ∈ I.support)
    (h6 : ∀ p : PrimeSpectrum (completedLocalRing I y), p.asIdeal ≠ completedMaximalIdeal I y →
      adicClosedFibreThrough I y p = {completedMaximalIdeal I y} →
      0 < completedStalkDepth I F y p)
    (𝔓 : Ideal (AdicCompletion (IdealSheafData.stalk I y) (X.presheaf.stalk y))) (h𝔓 : 𝔓.IsPrime)
    (hne : 𝔓 ≠ (maximalIdeal (X.presheaf.stalk y)).map (algebraMap _ _))
    (hfib : ∀ Q : Ideal (AdicCompletion (IdealSheafData.stalk I y) (X.presheaf.stalk y)),
      Q.IsPrime → 𝔓 ≤ Q → (IdealSheafData.stalk I y).map (algebraMap _ _) ≤ Q →
        Q = (maximalIdeal (X.presheaf.stalk y)).map (algebraMap _ _)) :
    𝔓 ∉ associatedPrimes (AdicCompletion (IdealSheafData.stalk I y) (X.presheaf.stalk y))
      (completedStalk I F y) := by
  intro hass
  have hJ : IdealSheafData.stalk I y ≤ maximalIdeal (X.presheaf.stalk y) :=
    (Stacks.Divisors.stalk_le_maximalIdeal_iff_mem_support I y).mpr hyY
  have : Module.Finite (completedLocalRing I y) (completedStalk I F y) :=
    finite_completedStalk I F y
  have : IsLocalRing (completedLocalRing I y) :=
    Stacks.AdicCompletionDimension.isLocalRing_adicCompletion_of_le_maximalIdeal _ hJ
  have hmax : completedMaximalIdeal I y = maximalIdeal (completedLocalRing I y) :=
    IsLocalRing.eq_maximalIdeal
      (AdicCompletion.isMaximal_map_of_le _ _ hJ (Ideal.fg_of_isNoetherianRing _))
  have hfibre : adicClosedFibreThrough I y ⟨𝔓, h𝔓⟩ = {completedMaximalIdeal I y} := by
    ext Q
    simp only [adicClosedFibreThrough, Set.mem_setOf_eq, Set.mem_singleton_iff]
    refine ⟨fun ⟨hQ, h𝔓Q, hJQ⟩ => hfib Q hQ h𝔓Q hJQ, ?_⟩
    rintro rfl
    refine ⟨?_, ?_, Ideal.map_mono hJ⟩ <;> rw [hmax]
    · exact (maximalIdeal.isMaximal _).isPrime
    · exact le_maximalIdeal h𝔓.ne_top
  have h0 := (Module.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes).mpr
    (Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes hass)
  have h0' : completedStalkDepth I F y ⟨𝔓, h𝔓⟩ = 0 := h0
  exact (h6 ⟨𝔓, h𝔓⟩ hne hfibre).ne' h0'

section Germ

variable {U : X.Opens} (hU : IsAffineOpen U) {y : X} (hy : y ∈ U)
include hU

/-- The germ of a section of a term of the system, as an element of its stalk. -/
abbrev sectionGerm (n : ℕ) (x : (sectionsTower F U).obj (op n)) :
    (modulesStalkFunctor X y).obj (F.obj.obj (op n)) :=
  ((F.obj.obj (op n)).presheaf.germ U y hy).hom x

omit hU [IsLocallyNoetherian X] in
/-- The germ of `r • x` is the germ of `r` times the germ of `x`. -/
theorem sectionGerm_smul (n : ℕ) (r : Γ(X, U)) (x : (sectionsTower F U).obj (op n)) :
    sectionGerm F hy n (r • x) = (X.presheaf.germ U y hy).hom r • sectionGerm F hy n x :=
  germ_smul y U hy r x

omit hU [IsLocallyNoetherian X] in
/-- The germ of a sum of sections is the sum of their germs. -/
theorem sectionGerm_add (n : ℕ) (x x' : (sectionsTower F U).obj (op n)) :
    sectionGerm F hy n (x + x') = sectionGerm F hy n x + sectionGerm F hy n x' :=
  map_add _ _ _

omit hU [IsLocallyNoetherian X] in
/-- Taking germs commutes with the transition maps of the system. -/
theorem sectionGerm_transition {m n : ℕ} (h : m ≤ n) (x : (sectionsTower F U).obj (op n)) :
    ((modulesStalkFunctor X y).map (F.obj.map (homOfLE h).op)).hom (sectionGerm F hy n x) =
      sectionGerm F hy m (towerMap (sectionsTower F U) h x) :=
  modulesStalkFunctor_map_germ _ y U hy x

omit [IsLocallyNoetherian X] in
/-- A function on `U` not in the prime of `y` has invertible germ at `y`. -/
theorem isUnit_germ_of_notMem {c : Γ(X, U)} (hc : c ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal) :
    IsUnit ((X.presheaf.germ U y hy).hom c) := by
  let := (X.presheaf.germ U y hy).hom.toAlgebra
  have := hU.isLocalization_stalk ⟨y, hy⟩
  exact IsLocalization.map_units (X.presheaf.stalk y)
    (⟨c, hc⟩ : (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl)

omit [IsLocallyNoetherian X] in
/-- A function on `U` in the prime of `y` has germ in the maximal ideal of the local ring at
`y`. -/
theorem germ_mem_maximalIdeal {a : Γ(X, U)} (ha : a ∈ (hU.primeIdealOf ⟨y, hy⟩).asIdeal) :
    (X.presheaf.germ U y hy).hom a ∈ maximalIdeal (X.presheaf.stalk y) := by
  let := (X.presheaf.germ U y hy).hom.toAlgebra
  have := hU.isLocalization_stalk ⟨y, hy⟩
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk y)
    (hU.primeIdealOf ⟨y, hy⟩).asIdeal a).mpr ha

omit [IsLocallyNoetherian X] in
/-- A prime of the local ring at `y` whose contraction is the prime of `y` is maximal. -/
theorem eq_maximalIdeal_of_comap {P : Ideal (X.presheaf.stalk y)} [P.IsPrime]
    (hP : P.comap (X.presheaf.germ U y hy).hom = (hU.primeIdealOf ⟨y, hy⟩).asIdeal) :
    P = maximalIdeal (X.presheaf.stalk y) := by
  let := (X.presheaf.germ U y hy).hom.toAlgebra
  have := hU.isLocalization_stalk ⟨y, hy⟩
  rw [← IsLocalization.map_comap (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
    (X.presheaf.stalk y) P, ← IsLocalization.map_comap
    (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (X.presheaf.stalk y)
    (maximalIdeal (X.presheaf.stalk y))]
  congr 1
  show P.comap (algebraMap _ _) = (maximalIdeal (X.presheaf.stalk y)).comap (algebraMap _ _)
  rw [show P.comap (algebraMap _ _) = _ from hP]
  exact (IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk y)
    (hU.primeIdealOf ⟨y, hy⟩).asIdeal).symm

omit [IsLocallyNoetherian X] in
/-- The contraction of any prime of the local ring at `y` lies in the prime of `y`. -/
theorem comap_le_primeIdealOf (P : Ideal (X.presheaf.stalk y)) [P.IsPrime] :
    P.comap (X.presheaf.germ U y hy).hom ≤ (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
  intro a ha
  by_contra hna
  exact ‹P.IsPrime›.ne_top (Ideal.eq_top_of_isUnit_mem P (Ideal.mem_comap.mp ha)
    (isUnit_germ_of_notMem hU hy hna))

omit [IsLocallyNoetherian X] in
/-- Every element of the stalk of the `n`-th term becomes the germ of a section over `U` after
multiplication by the germ of a function not in the prime of `y`. -/
theorem exists_germ_smul_eq_sectionGerm (n : ℕ)
    (v : (modulesStalkFunctor X y).obj (F.obj.obj (op n))) :
    ∃ (x : (sectionsTower F U).obj (op n)) (c : Γ(X, U)),
      c ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧
        (X.presheaf.germ U y hy).hom c • v = sectionGerm F hy n x := by
  have : (F.obj.obj (op n)).IsQuasicoherent := F.property.isQuasicoherent n
  exact exists_germ_smul_eq_germ (F.obj.obj (op n)) hU hy v

omit [IsLocallyNoetherian X] in
/-- Two sections over `U` with the same germ at `y` agree after multiplication by a function not
in the prime of `y`. -/
theorem exists_smul_eq_of_sectionGerm_eq (n : ℕ) (x x' : (sectionsTower F U).obj (op n))
    (h : sectionGerm F hy n x = sectionGerm F hy n x') :
    ∃ c ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal, c • x = c • x' := by
  have : (F.obj.obj (op n)).IsQuasicoherent := F.property.isQuasicoherent n
  exact exists_smul_eq_of_germ_eq (F.obj.obj (op n)) hU hy x x' h

/-- The span of the germs of a submodule of sections, as a submodule of the stalk. -/
def germSpan (n : ℕ) (W : Submodule Γ(X, U) ((sectionsTower F U).obj (op n))) :
    Submodule (X.presheaf.stalk y) ((modulesStalkFunctor X y).obj (F.obj.obj (op n))) :=
  Submodule.span _ (sectionGerm F hy n '' W)

omit [IsLocallyNoetherian X] in
/-- An element of the stalk lies in a germ span once its multiple by the germ of a function not in
the prime of `y` does. -/
private theorem mem_germSpan_of_germ_smul_mem {c : Γ(X, U)}
    (hc : c ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal)
    {n : ℕ} {W : Submodule Γ(X, U) ((sectionsTower F U).obj (op n))}
    {v : (modulesStalkFunctor X y).obj (F.obj.obj (op n))}
    (hv : (X.presheaf.germ U y hy).hom c • v ∈ germSpan F hy n W) : v ∈ germSpan F hy n W :=
  (Submodule.smul_mem_iff_of_isUnit _ (isUnit_germ_of_notMem hU hy hc)).mp hv

omit [IsLocallyNoetherian X] in
/-- **The germ span of a submodule is its localization**: an element of the stalk lies in it
exactly when a function not vanishing at `y` takes it to the germ of an element. -/
theorem mem_germSpan_iff (n : ℕ) (W : Submodule Γ(X, U) ((sectionsTower F U).obj (op n)))
    (v : (modulesStalkFunctor X y).obj (F.obj.obj (op n))) :
    v ∈ germSpan F hy n W ↔ ∃ w ∈ W, ∃ c ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal,
      (X.presheaf.germ U y hy).hom c • v = sectionGerm F hy n w := by
  have h1 : (1 : Γ(X, U)) ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    (Ideal.ne_top_iff_one _).mp (hU.primeIdealOf ⟨y, hy⟩).isPrime.ne_top
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨w, hw, rfl⟩ := hv
      exact ⟨w, hw, 1, h1, by rw [map_one, one_smul]⟩
    | zero =>
      exact ⟨0, W.zero_mem, 1, h1, (smul_zero _).trans (map_zero _).symm⟩
    | add v v' _ _ h₁ h₂ =>
      obtain ⟨w, hw, c, hc, hcw⟩ := h₁
      obtain ⟨w', hw', c', hc', hcw'⟩ := h₂
      refine ⟨c' • w + c • w', W.add_mem (W.smul_mem _ hw) (W.smul_mem _ hw'), c * c',
        (hU.primeIdealOf ⟨y, hy⟩).isPrime.mul_notMem hc hc', ?_⟩
      rw [sectionGerm_add, sectionGerm_smul, sectionGerm_smul, ← hcw, ← hcw', map_mul, smul_add,
        smul_smul, smul_smul, mul_comm ((X.presheaf.germ U y hy).hom c')]
    | smul b v _ h =>
      obtain ⟨w, hw, c, hc, hcw⟩ := h
      let := (X.presheaf.germ U y hy).hom.toAlgebra
      have := hU.isLocalization_stalk ⟨y, hy⟩
      obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl b
      refine ⟨r • w, W.smul_mem _ hw, s * c,
        (hU.primeIdealOf ⟨y, hy⟩).isPrime.mul_notMem s.2 hc, ?_⟩
      rw [sectionGerm_smul, ← hcw, smul_smul, smul_smul]
      congr 1
      show algebraMap _ _ ((s : Γ(X, U)) * c) * b = algebraMap _ _ r * algebraMap _ _ c
      rw [map_mul, mul_assoc, mul_comm (algebraMap _ _ c), ← mul_assoc, mul_comm _ b, hrs]
  · rintro ⟨w, hw, c, hc, hcw⟩
    refine mem_germSpan_of_germ_smul_mem F hU hy hc ?_
    rw [hcw]
    exact Submodule.subset_span ⟨w, hw, rfl⟩

omit [IsLocallyNoetherian X] in
/-- If the germ of a section `x` lies in the germ span of `W`, then `t • x ∈ W` for some function
`t` not in the prime of `y`. -/
theorem exists_smul_mem_of_sectionGerm_mem_germSpan (n : ℕ)
    (W : Submodule Γ(X, U) ((sectionsTower F U).obj (op n))) (x : (sectionsTower F U).obj (op n))
    (hx : sectionGerm F hy n x ∈ germSpan F hy n W) :
    ∃ t ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal, t • x ∈ W := by
  obtain ⟨w, hw, c, hc, hcw⟩ := (mem_germSpan_iff F hU hy n W _).mp hx
  rw [← sectionGerm_smul] at hcw
  obtain ⟨c', hc', hcc'⟩ := exists_smul_eq_of_sectionGerm_eq F hU hy n _ _ hcw
  refine ⟨c' * c, (hU.primeIdealOf ⟨y, hy⟩).isPrime.mul_notMem hc' hc, ?_⟩
  rw [mul_smul, hcc']
  exact W.smul_mem _ hw

omit [IsLocallyNoetherian X] in
/-- If a transition map of the system takes `W` into `W'`, then the induced map of stalks takes
the germ span of `W` into the germ span of `W'`. -/
theorem stalkMap_germSpan_le {m n : ℕ} (h : m ≤ n)
    (W : Submodule Γ(X, U) ((sectionsTower F U).obj (op n)))
    (W' : Submodule Γ(X, U) ((sectionsTower F U).obj (op m)))
    (hW : W.map (towerMap (sectionsTower F U) h) ≤ W') :
    (germSpan F hy n W).map ((modulesStalkFunctor X y).map (F.obj.map (homOfLE h).op)).hom ≤
      germSpan F hy m W' := by
  rw [germSpan, Submodule.map_span_le]
  rintro _ ⟨w, hw, rfl⟩
  rw [sectionGerm_transition]
  exact Submodule.subset_span ⟨_, hW (Submodule.mem_map_of_mem hw), rfl⟩

/-- The filtration of the completed stalk lying over the germ spans of a system of submodules of
sections. -/
private def germSpanFiltration (Λ : ∀ n, Submodule Γ(X, U) ((sectionsTower F U).obj (op n)))
    (n : ℕ) :
    Submodule (X.presheaf.stalk y) (completedStalk I F y) :=
  (germSpan F hy n (Λ n)).comap (completedStalkProj F y n)

omit hU in
/-- Membership in the germ span filtration is membership of the projection in the germ span. -/
private theorem mem_germSpanFiltration
    {Λ : ∀ n, Submodule Γ(X, U) ((sectionsTower F U).obj (op n))}
    {n : ℕ} {p : completedStalk I F y} :
    p ∈ germSpanFiltration F hy Λ n ↔ completedStalkProj F y n p ∈ germSpan F hy n (Λ n) :=
  Iff.rfl

/-- The germ spans of a system of submodules with surjective transitions form a filtration of
the completed stalk. -/
private theorem formalFiltration_germSpanFiltration
    {Λ : ∀ n, Submodule Γ(X, U) ((sectionsTower F U).obj (op n))}
    (hΛmap : ∀ n, (Λ (n + 1)).map (towerMap (sectionsTower F U) (Nat.le_succ n)) = Λ n) :
    FormalFiltration (IdealSheafData.stalk I y) (germSpanFiltration F hy Λ) := by
  have h0 : ∀ k, IdealSheafData.stalk I y ^ (k + 1) •
      (⊤ : Submodule (X.presheaf.stalk y) (completedStalk I F y)) ≤ germSpanFiltration F hy Λ k :=
    fun k p hp => by
      rw [mem_germSpanFiltration, (completedStalkProj_eq_zero_iff F y k p).mpr hp]
      exact zero_mem _
  refine ⟨h0, fun k => le_antisymm ?_ ?_⟩
  · intro p hp
    rw [mem_germSpanFiltration] at hp
    obtain ⟨w, hw, c, hc, hcw⟩ := (mem_germSpan_iff F hU hy k (Λ k) _).mp hp
    rw [← hΛmap k] at hw
    obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.mp hw
    obtain ⟨u, hu⟩ := isUnit_germ_of_notMem hU hy hc
    obtain ⟨p', hp'⟩ := completedStalkProj_surjective F y (k + 1)
      ((↑u⁻¹ : X.presheaf.stalk y) • sectionGerm F hy (k + 1) w')
    have hp'Λ : p' ∈ germSpanFiltration F hy Λ (k + 1) := by
      rw [mem_germSpanFiltration, hp']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w', hw', rfl⟩)
    have hdiff : completedStalkProj F y k (p - p') = 0 := by
      rw [map_sub, ← completedStalkProj_transition F y (Nat.le_succ k) p', hp', map_smul,
        sectionGerm_transition, ← hcw, ← hu, smul_smul, Units.inv_mul, one_smul, sub_self]
    rw [show p = p' + (p - p') by abel]
    exact Submodule.add_mem_sup hp'Λ ((completedStalkProj_eq_zero_iff F y k _).mp hdiff)
  · refine sup_le (fun p hp => ?_) (h0 k)
    rw [mem_germSpanFiltration] at hp
    rw [mem_germSpanFiltration, ← completedStalkProj_transition F y (Nat.le_succ k) p]
    exact stalkMap_germSpan_le F hU hy (Nat.le_succ k) (Λ (k + 1)) (Λ k) (hΛmap k).le
      (Submodule.mem_map_of_mem hp)

/-- If a fixed power of `ℐ(U)` kills a system of submodules of sections, a fixed power of `ℐ_y`
takes its germ span filtration at level `k` into `ℐ_y^{k+1}` times the completed stalk. -/
private theorem exists_pow_smul_mem_of_germSpanFiltration
    {Λ : ∀ n, Submodule Γ(X, U) ((sectionsTower F U).obj (op n))}
    (hΛann : ∃ c, ∀ n, ∀ a ∈ I.ideal ⟨U, hU⟩ ^ c, ∀ x ∈ Λ n, a • x = 0) :
    ∃ c, ∀ k, ∀ p ∈ germSpanFiltration F hy Λ k, ∀ a ∈ IdealSheafData.stalk I y ^ c,
      a • p ∈ IdealSheafData.stalk I y ^ (k + 1) •
        (⊤ : Submodule (X.presheaf.stalk y) (completedStalk I F y)) := by
  obtain ⟨c, hcΛ⟩ := hΛann
  refine ⟨c, fun k p hp a ha => (completedStalkProj_eq_zero_iff F y k _).mp ?_⟩
  rw [mem_germSpanFiltration] at hp
  rw [map_smul]
  obtain ⟨w, hw, c₀, hc₀, hc₀w⟩ := (mem_germSpan_iff F hU hy k (Λ k) _).mp hp
  have hle : I.ideal ⟨U, hU⟩ ^ c ≤ (Ideal.torsionOf (X.presheaf.stalk y) _
      (completedStalkProj F y k p)).comap (X.presheaf.germ U y hy).hom := by
    intro b hb
    rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff]
    have h0 : (X.presheaf.germ U y hy).hom b • (X.presheaf.germ U y hy).hom c₀ •
        completedStalkProj F y k p = 0 := by
      rw [hc₀w, ← sectionGerm_smul, hcΛ k b hb w hw]
      exact map_zero _
    rw [smul_comm] at h0
    exact (isUnit_germ_of_notMem hU hy hc₀).smul_eq_zero.mp h0
  have hJc : IdealSheafData.stalk I y ^ c ≤
      Ideal.torsionOf (X.presheaf.stalk y) _ (completedStalkProj F y k p) := by
    refine (le_of_eq ?_).trans (Ideal.map_le_iff_le_comap.mpr hle)
    rw [Ideal.map_pow, ← IdealSheafData.stalk_eq_map_germ I y ⟨U, hU⟩ hy]
  exact (Ideal.mem_torsionOf_iff _ a).mp (hJc ha)

/-- The depth hypothesis of the essential constancy theorem on a system of submodules of sections
transfers to its germ span filtration of the completed stalk. -/
private theorem exists_mem_germSpanFiltration_of_maximalIdeal_smul_mem
    {Λ : ∀ n, Submodule Γ(X, U) ((sectionsTower F U).obj (op n))}
    (hD : ∃ d, ∀ k (x : (sectionsTower F U).obj (op (k + d))),
      (∀ a ∈ (hU.primeIdealOf ⟨y, hy⟩).asIdeal, ∃ t ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal,
        t • a • x ∈ Λ (k + d)) →
        ∃ t ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal,
          t • towerMap (sectionsTower F U) (Nat.le_add_right k d) x ∈ Λ k) :
    ∃ d, ∀ k (p : completedStalk I F y),
      (∀ a ∈ maximalIdeal (X.presheaf.stalk y), a • p ∈ germSpanFiltration F hy Λ (k + d)) →
        p ∈ germSpanFiltration F hy Λ k := by
  obtain ⟨d, hd⟩ := hD
  refine ⟨d, fun k p hp => ?_⟩
  obtain ⟨x, c, hc, hcx⟩ :=
    exists_germ_smul_eq_sectionGerm F hU hy (k + d) (completedStalkProj F y (k + d) p)
  have hx : ∀ a ∈ (hU.primeIdealOf ⟨y, hy⟩).asIdeal, ∃ t ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal,
      t • a • x ∈ Λ (k + d) := by
    intro a ha
    have := hp _ (germ_mem_maximalIdeal hU hy ha)
    rw [mem_germSpanFiltration, map_smul] at this
    apply exists_smul_mem_of_sectionGerm_mem_germSpan F hU hy
    rw [sectionGerm_smul, ← hcx, smul_comm]
    exact Submodule.smul_mem _ _ this
  obtain ⟨t, ht, htx⟩ := hd k x hx
  rw [mem_germSpanFiltration]
  apply mem_germSpan_of_germ_smul_mem F hU hy (c := t * c)
    ((hU.primeIdealOf ⟨y, hy⟩).isPrime.mul_notMem ht hc)
  rw [map_mul, mul_smul, ← completedStalkProj_transition F y (Nat.le_add_right k d) p,
    ← map_smul, hcx, sectionGerm_transition, ← sectionGerm_smul]
  exact Submodule.subset_span ⟨_, htx, rfl⟩

/-- **The local hypothesis of the essential constancy theorem at a point of `U ∩ V(ℐ)`**,
from the depth condition of Stacks 0EJE on the completed stalk at that point. -/
theorem localTorsionProZeroAt_sectionsTower (hyY : y ∈ I.support)
    (h6 : ∀ p : PrimeSpectrum (completedLocalRing I y), p.asIdeal ≠ completedMaximalIdeal I y →
      adicClosedFibreThrough I y p = {completedMaximalIdeal I y} →
      0 < completedStalkDepth I F y p) :
    LocalTorsionProZeroAt (I.ideal ⟨U, hU⟩) (sectionsTower F U) (hU.primeIdealOf ⟨y, hy⟩) := by
  intro Λ hΛmap hΛann hD m
  classical
  have : Module.Finite (completedLocalRing I y) (completedStalk I F y) :=
    finite_completedStalk I F y
  have : IsAdicComplete (IdealSheafData.stalk I y) (completedStalk I F y) :=
    AdicCompletion.isAdicComplete (Ideal.fg_of_isNoetherianRing _)
  obtain ⟨m₂, hm₂, hmain⟩ :=
    (formalFiltration_germSpanFiltration F hU hy hΛmap).exists_forall_pow_smul_mem_imp_mem
      ((Stacks.Divisors.stalk_le_maximalIdeal_iff_mem_support I y).mpr hyY)
      (exists_pow_smul_mem_of_germSpanFiltration F hU hy hΛann)
      (exists_mem_germSpanFiltration_of_maximalIdeal_smul_mem F hU hy hD)
      (notMem_associatedPrimes_completedStalk F hyY h6) m
  refine ⟨m₂, hm₂, fun x ⟨e, he⟩ => ?_⟩
  obtain ⟨p, hp⟩ := completedStalkProj_surjective F y m₂ (sectionGerm F hy m₂ x)
  have hpΛ : p ∈ germSpanFiltration F hy Λ m := by
    refine hmain p ⟨e, fun a ha => ?_⟩
    have hle : (hU.primeIdealOf ⟨y, hy⟩).asIdeal ^ e ≤
        ((germSpanFiltration F hy Λ m₂).colon {p}).comap (X.presheaf.germ U y hy).hom := by
      intro b hb
      rw [Ideal.mem_comap, Submodule.mem_colon_singleton, mem_germSpanFiltration, map_smul, hp,
        ← sectionGerm_smul]
      obtain ⟨t, ht, htx⟩ := he b hb
      refine mem_germSpan_of_germ_smul_mem F hU hy ht ?_
      rw [← sectionGerm_smul]
      exact Submodule.subset_span ⟨_, htx, rfl⟩
    have h𝔪 : maximalIdeal (X.presheaf.stalk y) ^ e =
        ((hU.primeIdealOf ⟨y, hy⟩).asIdeal ^ e).map (X.presheaf.germ U y hy).hom := by
      let := (X.presheaf.germ U y hy).hom.toAlgebra
      have := hU.isLocalization_stalk ⟨y, hy⟩
      rw [Ideal.map_pow]
      congr 1
      exact (IsLocalization.AtPrime.map_eq_maximalIdeal _ (X.presheaf.stalk y)).symm
    rw [h𝔪] at ha
    exact Submodule.mem_colon_singleton.mp (Ideal.map_le_iff_le_comap.mpr hle ha)
  rw [mem_germSpanFiltration, ← completedStalkProj_transition F y hm₂ p, hp,
    sectionGerm_transition] at hpΛ
  exact exists_smul_mem_of_sectionGerm_mem_germSpan F hU hy m _ _ hpΛ

end Germ

end Stacks.Algebraization

end
