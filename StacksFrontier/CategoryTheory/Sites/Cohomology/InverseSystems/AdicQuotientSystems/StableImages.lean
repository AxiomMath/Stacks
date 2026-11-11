module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InverseSystems.AdicQuotientSystems.LimitTopology
import StacksCore.Tactic.StacksAttribute

/-!
# The chain condition on the stable images

Stacks 0GYR and 0GYT: the Mittag-Leffler property and the comparison of topologies need the
chain condition only on the graded submodule `⨁ₙ Nₙ` of stable images.

Part of `StacksFrontier.CategoryTheory.Sites.Cohomology.InverseSystems.AdicQuotientSystems`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules
open scoped IsMulCommutative
open scoped DirectSum

attribute [local instance] HasDerivedCategory.standard

universe u v r w

namespace Stacks.Cohomology.AdicInverseSystems

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{r}) [∀ X : Cᵒᵖ, IsMulCommutative (O.obj.obj X)]

section AdicSystem

variable (I : Ideal ↥(GlobalSectionRing O)) (F : ℕᵒᵖ ⥤ SheafOfModules.{max u v r w} O)

variable {O I F}

/-! ### Mittag-Leffler from the chain condition on the stable images -/

section StableMittagLeffler

variable (hF : IsAdicQuotientSystem O I F) (p : ℕ)

/-- Stacks 0GYR's graded module `⨁ₙ Nₙ`, through its graded submodules: a graded submodule of
`⨁ₙ H^(p+1)(C, IⁿFₙ)` whose degree `n` part lies in the stable image
`Nₙ = ⋂_{m ≥ n} Im(H^(p+1)(C, IⁿF_m) → H^(p+1)(C, IⁿFₙ))`. -/
abbrev StableGradedSubmodule :=
  {P : GradedSubmodule hF p // ∀ n, P.carrier n ≤ stableImage O I F (p + 1) n}

/-- The comparison of the sequence `0 → I^(n+1)F_j → F_j → Fₙ → 0` with the one at `j = n + 1`,
which is the identity on `Fₙ`. -/
private def laterShortComplexHom {n j : ℕ} (hj : n + 1 ≤ j) :
    ShortComplex.mk (idealSmulι O (I ^ (n + 1)) (F.obj (op j)))
        (towerMap F (Nat.le_of_succ_le hj)) (hF.idealSmulι_comp_towerMap hj) ⟶
      adicShortComplex hF n where
  τ₁ := gradedPieceMap O I F hj
  τ₂ := towerMap F hj
  τ₃ := 𝟙 _
  comm₁₂ := idealSmulMap_comp_ι O (I ^ (n + 1)) (F.obj (op j)) (towerMap F hj)
  comm₂₃ := by
    change towerMap F hj ≫ towerMap F (Nat.le_succ n) =
      towerMap F (Nat.le_of_succ_le hj) ≫ 𝟙 _
    rw [Category.comp_id, towerMap_comp]

/-- The boundary map at stage `n` factors through the boundary map of the sequence at `j ≥ n + 1`
followed by `H^(p+1)(C, I^(n+1)F_j) → H^(p+1)(C, I^(n+1)Fₙ₊₁)`. -/
private theorem cohomologyBoundary_eq_comp {n j : ℕ} (hj : n + 1 ≤ j) :
    cohomologyBoundary hF p n = (cohomologyDeltaFunctor.{u, v, r, w} O).δ (hF.shortExact hj) p ≫
      (globalModuleCohomology.{u, v, r, w} O (p + 1)).map (gradedPieceMap O I F hj) := by
  have hnat := (cohomologyDeltaFunctor.{u, v, r, w} O).δ_naturality (hF.shortExact hj)
    (adicShortComplex_shortExact hF n) (laterShortComplexHom hF hj) p
  have hid : ((cohomologyDeltaFunctor.{u, v, r, w} O).functor p).map
      (laterShortComplexHom hF hj).τ₃ =
      𝟙 (((cohomologyDeltaFunctor.{u, v, r, w} O).functor p).obj
        (adicShortComplex hF n).X₃) :=
    ((cohomologyDeltaFunctor.{u, v, r, w} O).functor p).map_id _
  rw [hid] at hnat
  exact (Category.id_comp _).symm.trans hnat

/-- The boundary maps of Stacks 0GYR have image inside the stable images: `Im(δₙ) ⊆ Nₙ`. -/
theorem cohomologyBoundary_mem_stableImage (n : ℕ)
    (x : (globalModuleCohomology.{u, v, r, w} O p).obj (F.obj (op n))) :
    (cohomologyBoundary hF p n).hom x ∈ stableImage O I F (p + 1) (n + 1) := by
  refine (Submodule.mem_iInf _).mpr fun j => (Submodule.mem_iInf _).mpr fun hj => ?_
  exact ⟨((cohomologyDeltaFunctor.{u, v, r, w} O).δ (hF.shortExact hj) p).hom x,
    (congrArg (fun g => ModuleCat.Hom.hom g x) (cohomologyBoundary_eq_comp hF p hj)).symm⟩

/-- The boundary images of classes vanishing `c` steps earlier lie in the stable images. -/
theorem boundarySubmodule_le_stableImage (c n : ℕ) :
    boundarySubmodule hF p c n ≤ stableImage O I F (p + 1) n := by
  cases n with
  | zero => exact bot_le
  | succ n =>
    intro y hy
    obtain ⟨z, -, rfl⟩ := hy
    exact cohomologyBoundary_mem_stableImage hF p n z

/-- The boundary images of the classes vanishing `c` steps earlier, as a graded submodule of
`⨁ₙ Nₙ`. -/
def boundaryStableGradedSubmodule (c : ℕ) : StableGradedSubmodule hF p :=
  ⟨boundaryGradedSubmodule hF p c, boundarySubmodule_le_stableImage hF p c⟩

/-- The boundary graded submodules of `⨁ₙ Nₙ` increase with `c`. -/
theorem boundaryStableGradedSubmodule_monotone :
    Monotone (boundaryStableGradedSubmodule hF p) :=
  fun _ _ h => boundaryGradedSubmodule_monotone hF p h

/-- Under the ascending chain condition on graded submodules of `⨁ₙ Nₙ` there is one `c` such that
the boundary of every class of `Hᵖ(C, Fₙ)` is the boundary of a class vanishing `c` steps earlier.
-/
theorem exists_boundary_lift_vanishing_of_stableImages
    (hacc : WellFoundedGT (StableGradedSubmodule hF p)) :
    ∃ c : ℕ, ∀ (n : ℕ) (x : (globalModuleCohomology.{u, v, r, w} O p).obj (F.obj (op n))),
      ∃ y ∈ vanishingSubmodule (F ⋙ globalModuleCohomology.{u, v, r, w} O p) c n,
        (cohomologyBoundary hF p n).hom y = (cohomologyBoundary hF p n).hom x := by
  obtain ⟨c, hc⟩ := (wellFoundedGT_iff_monotone_chain_condition.mp hacc)
    ⟨boundaryStableGradedSubmodule hF p, boundaryStableGradedSubmodule_monotone hF p⟩
  refine ⟨c, fun n x => ?_⟩
  have he := congrArg (fun P : StableGradedSubmodule hF p => P.1.carrier (n + 1))
    (hc (max c (n + 1)) (le_max_left _ _))
  change boundarySubmodule hF p c (n + 1) =
    boundarySubmodule hF p (max c (n + 1)) (n + 1) at he
  change (cohomologyBoundary hF p n).hom x ∈ boundarySubmodule hF p c (n + 1)
  rw [he]
  refine ⟨x, ?_, rfl⟩
  rw [vanishingSubmodule_eq_top _ (show n < max c (n + 1) by omega)]
  trivial

/-- **Stacks Project, Tag 0GYR**, the footnote: the images of `Hᵖ(C, F_k) → Hᵖ(C, Fᵢ)` are the
stable image already at `k = i + c`, for one `c` independent of `i`. In Stacks' indexing
(`Mₙ = Hᵖ(C, Fₙ)` with Lean's `F i` standing for Stacks' `F_{i+1}`): there is `c ≥ 0` with
`Im(Mₙ → M_{n-c})` the stable image for all `n ≥ c`, the stable image being the common value of
`Im(M_k → M_{n-c})` for all `k ≥ n`. -/
@[stacks 0GYR "the footnote: a uniform shift `c` with `Im(Mₙ → M_{n-c})` the stable image"]
theorem exists_uniform_stable_image_of_stableImages
    (hacc : WellFoundedGT (StableGradedSubmodule hF p)) :
    ∃ c : ℕ, ∀ i k : ℕ, ∀ h : i + c ≤ k,
      transitionImage (F ⋙ globalModuleCohomology.{u, v, r, w} O p) i k (by omega) =
        transitionImage (F ⋙ globalModuleCohomology.{u, v, r, w} O p) i (i + c) (by omega) := by
  obtain ⟨c, hc⟩ := exists_boundary_lift_vanishing_of_stableImages hF p hacc
  refine ⟨c, fun i k h => ?_⟩
  have hstep (n : ℕ) (hn : i + c ≤ n) :
      LinearMap.range ((F ⋙ globalModuleCohomology.{u, v, r, w} O p).map
          (homOfLE ((Nat.le_add_right i c).trans (hn.trans (Nat.le_succ n)))).op).hom =
        LinearMap.range ((F ⋙ globalModuleCohomology.{u, v, r, w} O p).map
          (homOfLE ((Nat.le_add_right i c).trans hn)).op).hom := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨(F ⋙ globalModuleCohomology.{u, v, r, w} O p).map (homOfLE (Nat.le_succ n)).op z,
        congrArg (fun g => ModuleCat.Hom.hom g z)
          (towerMap_comp (F ⋙ globalModuleCohomology.{u, v, r, w} O p)
            ((Nat.le_add_right i c).trans hn) (Nat.le_succ n))⟩
    · rintro ⟨z, rfl⟩
      exact exists_lift_preserving_image hF p c hc i n hn z
  apply (ModuleCat.subobjectModule
    ((F ⋙ globalModuleCohomology.{u, v, r, w} O p).obj (op i))).injective
  change ModuleCat.subobjectModule _ (imageSubobject _) =
    ModuleCat.subobjectModule _ (imageSubobject _)
  rw [subobjectModule_image, subobjectModule_image]
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k hk ih => exact (hstep k hk).trans ih

/-- **Stacks Project, Tag 0GYR.** For an inverse system of sheaves of modules on a site with
`Fₙ = Fₙ₊₁/IⁿFₙ₊₁`, the ascending chain condition on the graded submodules of `⨁ₙ Nₙ`, where
`Nₙ = ⋂_{m ≥ n} Im(H^(p+1)(C, IⁿF_m) → H^(p+1)(C, IⁿFₙ))`, implies that the inverse system
`n ↦ Hᵖ(C, Fₙ)` satisfies the Mittag-Leffler condition. The footnote's uniform shift is
`exists_uniform_stable_image_of_stableImages`. -/
@[stacks 0GYR "the Mittag-Leffler condition; the footnote's uniform shift is \
`exists_uniform_stable_image_of_stableImages`"]
theorem isMittagLefflerCategorical_cohomology_of_stableImages
    (hacc : WellFoundedGT (StableGradedSubmodule hF p)) :
    IsMittagLefflerCategorical (F ⋙ globalModuleCohomology.{u, v, r, w} O p) := by
  obtain ⟨c, hc⟩ := exists_uniform_stable_image_of_stableImages hF p hacc
  exact fun i => ⟨i + c, Nat.le_add_right i c, hc i⟩

end StableMittagLeffler


/-! ### The limit topology from the chain condition on the stable images -/

section StableAdicTopology

variable (O I F)

/-- The homogeneous piece `Nₙ = ⋂_{m ≥ n} Im(Hᵖ(C, IⁿF_m) → Hᵖ(C, IⁿFₙ))` of the graded object
of Stacks 0GYT. -/
def stableCohomology (p n : ℕ) : Type (max u v r w) := ↥(stableImage O I F p n)

/-- The additive group structure of the stable image `Nₙ`. -/
instance (p n : ℕ) : AddCommGroup (stableCohomology O I F p n) :=
  inferInstanceAs (AddCommGroup ↥(stableImage O I F p n))

/-- The `Γ(C, O)`-module structure of the stable image `Nₙ`. -/
instance (p n : ℕ) : Module ↥(GlobalSectionRing O) (stableCohomology O I F p n) :=
  inferInstanceAs (Module ↥(GlobalSectionRing O) ↥(stableImage O I F p n))

/-- The graded object `⨁ₙ Nₙ` of stable images of Stacks 0GYT. -/
abbrev StableCohomologySum (p : ℕ) := ⨁ n, stableCohomology O I F p n

/-- The inclusion `Nₙ → Hᵖ(C, IⁿFₙ)`. -/
def stableIncl (p n : ℕ) : stableCohomology O I F p n →ₗ[↥(GlobalSectionRing O)]
    gradedCohomology O I F p n :=
  (stableImage O I F p n).subtype

/-- The degree `n` component of a homogeneous element of `⨁ₙ Nₙ` of degree `n`. -/
theorem stableEval_of (p n : ℕ) (x : stableCohomology O I F p n) :
    (DirectSum.of (stableCohomology O I F p) n x) n = x :=
  DirectSum.of_eq_same n x

/-- Reading off the degree `n` component of a homogeneous element of `⨁ₙ Nₙ` of degree `n` and
mapping it to `Hᵖ(C, Fₙ)` recovers its image. -/
theorem gradedIncl_stableIncl_of (p n : ℕ) (x : stableCohomology O I F p n) :
    gradedIncl O I F p n (stableIncl O I F p n
        ((DirectSum.of (stableCohomology O I F p) n x) n)) =
      gradedIncl O I F p n (stableIncl O I F p n x) :=
  congrArg (fun y => gradedIncl O I F p n (stableIncl O I F p n y)) (stableEval_of O I F p n x)

/-- The canonical graded action on `⨁ₙ Nₙ`: a homogeneous scalar of degree `m` acts through the
canonical degree-raising map on the ideal-power subsheaves, which preserves the stable images. -/
def IsCanonicalActionOnStable (hF : IsAdicQuotientSystem O I F) (p : ℕ)
    [Module (AssociatedGraded.gradedRing I) (StableCohomologySum O I F p)] : Prop :=
  ∀ (m n : ℕ) (a : ↥(I ^ m)) (x : stableCohomology O I F p n),
    AssociatedGraded.classOfPow I m a • DirectSum.of (stableCohomology O I F p) n x =
      DirectSum.of (stableCohomology O I F p) (m + n)
        ⟨((globalModuleCohomology.{u, v, r, w} O p).map
            (actTo hF m n (m + n) (by omega) a)).hom x.1,
          map_actTo_mem_stableImage O I F hF p m n (m + n) (by omega) a x.1 x.2⟩

/-- Stacks 0GYT's hypothesis: `⨁ₙ Nₙ` satisfies the ascending chain condition as a graded module
over `⨁ₙ Iⁿ/Iⁿ⁺¹`, for the canonical graded action. -/
def HasStableGradedACC (hF : IsAdicQuotientSystem O I F) (p : ℕ) : Prop :=
  ∃ action : Module (AssociatedGraded.gradedRing I) (StableCohomologySum O I F p),
    letI := action
    IsCanonicalActionOnStable O I F hF p ∧
      IsNoetherian (AssociatedGraded.gradedRing I) (StableCohomologySum O I F p)

/-- The canonical action on `⨁ₙ Nₙ`, with the resulting degree written as a given sum. -/
theorem isCanonicalActionOnStable_of_eq (hF : IsAdicQuotientSystem O I F) (p : ℕ)
    [Module (AssociatedGraded.gradedRing I) (StableCohomologySum O I F p)]
    (hc : IsCanonicalActionOnStable O I F hF p) (m n k : ℕ) (h : m + n = k) (a : ↥(I ^ m))
    (x : stableCohomology O I F p n) :
    AssociatedGraded.classOfPow I m a • DirectSum.of (stableCohomology O I F p) n x =
      DirectSum.of (stableCohomology O I F p) k
        ⟨((globalModuleCohomology.{u, v, r, w} O p).map
            (actTo hF m n k (by omega) a)).hom x.1,
          map_actTo_mem_stableImage O I F hF p m n k (by omega) a x.1 x.2⟩ := by
  subst k
  exact hc m n a x

/-- Stacks 0GYS's graded submodule `⨁ₙ Eₙ` is closed under the canonical graded action, in the
form not referring to a graded module structure. -/
theorem map_actTo_mem_liftingSubgroup (hF : IsAdicQuotientSystem O I F) (p k n : ℕ)
    (a : ↥(I ^ k)) (s : gradedCohomology O I F p n) (hs : s ∈ liftingSubgroup O I F p n) :
    ((globalModuleCohomology.{u, v, r, w} O p).map
        (actTo hF k n (k + n) (by omega) a)).hom s ∈ liftingSubgroup O I F p (k + n) := by
  cases n with
  | zero =>
    have hs0 : s = 0 := by
      simpa only [liftingSubgroup, AddSubgroup.mem_bot] using hs
    subst s
    rw [map_zero]
    exact (liftingSubgroup O I F p (k + 0)).zero_mem
  | succ n =>
    obtain ⟨hsStable, xl, hxl, hsx⟩ := (mem_liftingSubgroup_succ_iff O I F p n s).mp hs
    refine (mem_liftingSubgroup_succ_iff O I F p (k + n) _).mpr ⟨?_, a.1 • xl, ?_, ?_⟩
    · exact map_actTo_mem_stableImage O I F hF p k (n + 1) (k + (n + 1)) (by omega) a s hsStable
    · have hzero : a.1 • xl.1 (n + k) = 0 := by
        rw [← map_mulLift_coord O I F hF p k n a xl, hxl, map_zero]
      change a.1 • xl.1 (k + n) = 0
      rw [Nat.add_comm k n]
      exact hzero
    · exact ι_map_actTo_eq_smul_coord O I F hF p k (n + 1) (k + (n + 1)) (by omega) a s
        hsStable xl hsx

/-- Stacks 0GYS's graded submodule `⨁ₙ Eₙ`, degreewise inside the stable images `Nₙ`. -/
def stableLiftingSubgroup (p n : ℕ) : AddSubgroup (stableCohomology O I F p n) :=
  (liftingSubgroup O I F p n).comap (stableIncl O I F p n).toAddMonoidHom

/-- A class of `Nₙ` lies in `Eₙ` exactly when it does so as a class of `Hᵖ(C, IⁿFₙ)`. -/
theorem mem_stableLiftingSubgroup (p n : ℕ) (x : stableCohomology O I F p n) :
    x ∈ stableLiftingSubgroup O I F p n ↔ x.1 ∈ liftingSubgroup O I F p n := Iff.rfl

/-- The canonical graded action on `⨁ₙ Nₙ` preserves the graded submodule `⨁ₙ Eₙ`. -/
theorem stableLiftingSubgroup_classOfPow_smul (hF : IsAdicQuotientSystem O I F) (p : ℕ)
    [Module (AssociatedGraded.gradedRing I) (StableCohomologySum O I F p)]
    (hcanonical : IsCanonicalActionOnStable O I F hF p) (k : ℕ) (a : ↥(I ^ k)) (n : ℕ)
    (s : stableCohomology O I F p n) (hs : s ∈ stableLiftingSubgroup O I F p n) :
    ∃ t : stableCohomology O I F p (k + n), t ∈ stableLiftingSubgroup O I F p (k + n) ∧
      AssociatedGraded.classOfPow I k a • DirectSum.of (stableCohomology O I F p) n s =
        DirectSum.of (stableCohomology O I F p) (k + n) t := by
  refine ⟨_, ?_, hcanonical k n a s⟩
  exact map_actTo_mem_liftingSubgroup O I F hF p k n a s.1 hs

/-- Stacks 0GYT's successive approximation: one finite family of elements of `I` such that above
a uniform degree every element of `Ker(M → Hᵖ(C, Fₙ₊₁))` is a combination of elements of
`Ker(M → Hᵖ(C, Fₙ))`, modulo `Ker(M → Hᵖ(C, Fₙ₊₂))`. -/
theorem exists_approx_of_stableImages (hF : IsAdicQuotientSystem O I F) (p : ℕ)
    (hACC : HasStableGradedACC O I F hF p) :
    ∃ (t : ℕ) (a : Fin t → ↥(GlobalSectionRing O)) (c : ℕ), (∀ i, a i ∈ I) ∧
      ∀ n, c ≤ n → ∀ x : cohomologyLimit O F p, x.1 (n + 1) = 0 →
        ∃ y : Fin t → cohomologyLimit O F p,
          (∀ i, (y i).1 n = 0) ∧ (x - ∑ i, a i • y i).1 (n + 2) = 0 := by
  classical
  obtain ⟨action, hcanonical, hnoeth⟩ := hACC
  let := action
  let : IsNoetherian (AssociatedGraded.gradedRing I) (StableCohomologySum O I F p) := hnoeth
  have hgraded : ∀ (k : ℕ) (a : ↥(I ^ k)) (j : ℕ) (x : stableCohomology O I F p j),
      ∃ y : stableCohomology O I F p (k + j),
        AssociatedGraded.classOfPow I k a • DirectSum.of (stableCohomology O I F p) j x =
          DirectSum.of (stableCohomology O I F p) (k + j) y :=
    fun k a j x => ⟨_, hcanonical k j a x⟩
  have hP := stableLiftingSubgroup_classOfPow_smul O I F hF p hcanonical
  let E := AssociatedGraded.homogeneousSubmodule I (stableLiftingSubgroup O I F p) hP
  have hE := AssociatedGraded.of_mem_homogeneousSubmodule_iff I
    (stableLiftingSubgroup O I F p) hP
  have hhom : ∀ n x, x ∈ E →
      AssociatedGraded.homogeneousPart (stableCohomology O I F p) n x ∈ E := fun n x hx =>
    (hE n (x n)).mpr
      ((AssociatedGraded.mem_homogeneousSubmodule I (stableLiftingSubgroup O I F p) hP x).mp hx n)
  obtain ⟨sg, ag, c, hc⟩ :=
    AssociatedGraded.exists_eventual_degree_one_generators I hgraded E hhom
  let e := Fintype.equivFin sg
  refine ⟨Fintype.card sg, fun i => (ag (e.symm i)).1, c, ?_, ?_⟩
  · intro i
    simpa only [pow_one] using (ag (e.symm i)).2
  · intro n hn x hx
    obtain ⟨tt, htStable, ht⟩ := exists_stable_lift O I F hF p (n + 1) x hx
    have htE : DirectSum.of (stableCohomology O I F p) (n + 2) ⟨tt, htStable⟩ ∈ E :=
      (hE (n + 2) ⟨tt, htStable⟩).mpr
        ((mem_liftingSubgroup_succ_iff O I F p (n + 1) tt).mpr ⟨htStable, x, hx, ht⟩)
    obtain ⟨z, hz, htz⟩ := hc (n + 1) (by omega) ⟨tt, htStable⟩ htE
    have hzx (i : sg) : ∃ yl : cohomologyLimit O F p,
        yl.1 n = 0 ∧ gradedIncl O I F p (n + 1) (z i).1 = yl.1 (n + 1) := by
      obtain ⟨-, yl, hyl, hzy⟩ := (mem_liftingSubgroup_succ_iff O I F p n (z i).1).mp
        ((hE _ _).mp (hz i))
      exact ⟨yl, hyl, hzy⟩
    choose yl hyl hzy using hzx
    refine ⟨fun i => yl (e.symm i), fun i => hyl (e.symm i), ?_⟩
    let ev : StableCohomologySum O I F p →ₗ[↥(GlobalSectionRing O)]
        (cohomologySystem O F p).obj (op (n + 2)) :=
      (gradedIncl O I F p (n + 2)).comp ((stableIncl O I F p (n + 2)).comp
        (DirectSum.component ↥(GlobalSectionRing O) ℕ (stableCohomology O I F p) (n + 2)))
    have heval (i : sg) : ev (AssociatedGraded.classOfPow I 1 (ag i) •
        DirectSum.of (stableCohomology O I F p) (n + 1) (z i)) =
          (ag i).1 • (yl i).1 (n + 2) := by
      rw [isCanonicalActionOnStable_of_eq O I F hF p hcanonical 1 (n + 1) (n + 2) (by omega)
        (ag i) (z i)]
      exact (gradedIncl_stableIncl_of O I F p (n + 2) _).trans
        (ι_map_actTo_eq_smul_coord O I F hF p 1 (n + 1) (n + 2) (by omega) (ag i) (z i).1
          (z i).2 (yl i) (hzy i))
    have hevt : ev (DirectSum.of (stableCohomology O I F p) (n + 2) ⟨tt, htStable⟩) =
        gradedIncl O I F p (n + 2) tt :=
      gradedIncl_stableIncl_of O I F p (n + 2) ⟨tt, htStable⟩
    have hsum := congrArg ev htz
    rw [map_sum, hevt] at hsum
    simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Pi.sub_apply,
      Finset.sum_apply, Pi.smul_apply]
    refine sub_eq_zero.mpr ?_
    rw [← ht]
    change gradedIncl O I F p (n + 2) tt = _
    rw [hsum]
    calc ∑ i : sg, ev (AssociatedGraded.classOfPow I 1 (ag i) •
            DirectSum.of (stableCohomology O I F p) (n + 1) (z i))
        = ∑ i : sg, (ag i).1 • (yl i).1 (n + 2) := Finset.sum_congr rfl fun i _ => heval i
      _ = _ := (Equiv.sum_comp e.symm fun i : sg => (ag i).1 • (yl i).1 (n + 2)).symm

/-- **Stacks Project, Tag 0GYT.** For an inverse system of sheaves of modules on a site with
`Fₙ = Fₙ₊₁/IⁿFₙ₊₁`, the ascending chain condition on `⨁ₙ Nₙ` as a graded `⨁ₙ Iⁿ/Iⁿ⁺¹`-module,
where `Nₙ = ⋂_{m ≥ n} Im(Hᵖ(C, IⁿF_m) → Hᵖ(C, IⁿFₙ))`, implies that the limit topology on
`lim Hᵖ(C, Fₙ)` is the `I`-adic topology. -/
@[stacks 0GYT]
theorem limitTopology_eq_adicModuleTopology_of_stableImages
    (hF : IsAdicQuotientSystem O I F) (p : ℕ) (hACC : HasStableGradedACC O I F hF p) :
    Stacks.AdicLimit.towerLimit.limitTopology
        (fun n => ((cohomologySystem O F p).obj (op n) : Type _))
        (cohomologyTransition O F p) =
      I.adicModuleTopology (cohomologyLimit O F p) := by
  obtain ⟨t, a, c, ha, happ⟩ := exists_approx_of_stableImages O I F hF p hACC
  have happ' : ∀ n, c ≤ n → ∀ x : cohomologyLimit O F p,
      x ∈ LinearMap.ker (limitProj O F p (n + 1)) →
      ∃ y : Fin t → cohomologyLimit O F p,
        (∀ i, y i ∈ LinearMap.ker (limitProj O F p n)) ∧
        x - ∑ i, a i • y i ∈ LinearMap.ker (limitProj O F p (n + 2)) := by
    intro n hn x hx
    obtain ⟨y, hy, hxy⟩ := happ n hn x (LinearMap.mem_ker.mp hx)
    exact ⟨y, fun i => LinearMap.mem_ker.mpr (hy i), LinearMap.mem_ker.mpr hxy⟩
  rw [Stacks.AdicLimit.limitTopology_eq_iInf_induced_proj]
  refine Stacks.AdicLimit.iInf_induced_eq_adicModuleTopology I (fun n => limitProj O F p n)
    (fun i j hij => Stacks.AdicLimit.towerLimit_proj_ker_antitone _ i j hij) (fun n => ?_)
    (fun k => ?_)
  · exact ⟨n + 1, Stacks.AdicLimit.pow_smul_le_proj_ker _ I
      (fun j => pow_smul_le_ker_cohomologyTransition O I F hF p j) n⟩
  · exact ⟨c + k, Stacks.AdicLimit.proj_ker_le_pow_smul _ I a ha c happ' k⟩

end StableAdicTopology

end AdicSystem

end Stacks.Cohomology.AdicInverseSystems

end
