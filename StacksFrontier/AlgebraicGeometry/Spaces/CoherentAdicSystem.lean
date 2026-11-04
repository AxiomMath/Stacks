module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Ideal.Operations
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleKer
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafDataFromCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian

/-!
# Coherent adic systems on an algebraic space

Let `F` be an algebraic space over a scheme `S` and let `𝓘 ⊆ 𝒪_F` be a sheaf of ideals on its
small étale ringed site. This file defines the category `Coh(F, 𝓘)` of inverse systems `(E_n)` of
coherent `𝒪_F`-modules such that `E_n` is annihilated by `𝓘 ^ n` and
`E_{n + 1} / 𝓘 ^ n E_{n + 1} = E_n`, together with the subsheaf `𝓘 ^ n M` and the quotient
`M / 𝓘 ^ n M` it is built from, and shows that a map in it is surjective exactly when it is
surjective at the lowest level.

The subsheaf `𝓘 ^ n M` is the least sheaf submodule of `M` which, over every étale chart `U`,
contains `𝓘(U) ^ n • M(U)`. The inverse systems are indexed by `ℕᵒᵖ` from zero, so the term at `n`
is `E_{n + 1}` in the numbering by positive integers.

## Main definitions

* `AlgebraicGeometry.Space.idealPowerMultiple` — the subsheaf `𝓘 ^ n M`.
* `AlgebraicGeometry.Space.idealPowerQuotient` — the quotient `M / 𝓘 ^ n M`.
* `AlgebraicGeometry.Space.IsCoherentAdicSystem` — the coherence, annihilation and
  quotient-transition conditions on an inverse system of `𝒪_F`-modules.
* `AlgebraicGeometry.Space.CoherentAdicSystems` — the category `Coh(F, 𝓘)` they cut out, as a
  full subcategory of `ℕᵒᵖ ⥤ 𝒪_F`-modules.
* `AlgebraicGeometry.Space.IsPowAnnihilated` and
  `AlgebraicGeometry.Space.IsPowAnnihilatedSection` — annihilation of the sections of a module,
  respectively of one section and all of its restrictions, by `𝓘 ^ k`.
* `AlgebraicGeometry.Space.powAnnihilator` — the sheaf submodule of the sections annihilated by
  `𝓘 ^ k` after every restriction.

## Main results

* `AlgebraicGeometry.Space.idealPowerMultiple_le_iff` — the chartwise universal property
  characterizing `𝓘 ^ n M`.
* `AlgebraicGeometry.Space.le_idealPowerMultiple_obj` — `𝓘 ^ n M` contains `𝓘(U) ^ n • M(U)`
  over every chart `U`.
* `AlgebraicGeometry.Space.idealPowerMultiple_succ_le` — `𝓘 ^ (n + 1) M ≤ 𝓘 ^ n M`.
* `AlgebraicGeometry.Space.idealPowerMultiple_eq_bot_iff` — `𝓘 ^ k M` vanishes exactly when
  `𝓘 ^ k` annihilates the sections of `M` over every chart.
* `AlgebraicGeometry.Space.cokernel_π_app_eq_zero_iff` — a section dies in the quotient by a
  sheaf submodule exactly when it is a section of that submodule.
* `AlgebraicGeometry.Space.isPowAnnihilated_of_epi` — annihilation by `𝓘 ^ k` passes to a
  quotient.
* `AlgebraicGeometry.Space.isPowAnnihilated_of_mem_idealPowerMultiple` — a module all of whose
  sections lie in `𝓘 ^ a M` and which is annihilated by `𝓘 ^ j` is already annihilated by
  `𝓘 ^ k` whenever `j ≤ k + a`.
* `AlgebraicGeometry.Space.epi_iff_epi_app_zero` — a map of coherent adic systems is surjective
  in `Coh(F, 𝓘)` exactly when its component at the lowest level is surjective.

## References

* [Stacks Project, Tag 08B3](https://stacks.math.columbia.edu/tag/08B3)
* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
* [Stacks Project, Tag 08BB](https://stacks.math.columbia.edu/tag/08BB)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-! ### The subsheaf `𝓘 ^ n M` and its quotient -/

/-- The subsheaf `𝓘 ^ n M` of a module `M` on an algebraic space, for a sheaf of ideals
`𝓘 ⊆ 𝒪_F` on its small étale site.

It is the least sheaf submodule of `M` containing, over every étale chart `U`, the submodule
`𝓘(U) ^ n • M(U)`. -/
def idealPowerMultiple (n : ℕ) (M : Modules.{u, u} B S hS F hF) : M.Submodule :=
  sInf { N | ∀ U : SmallEtale B S hS F,
    chartIdeal B S hS ⟨F, hF⟩ 𝓘 U ^ n • (⊤ : Submodule (chartRing B S hS F hF U)
      (M.val.obj (op U))) ≤ N.toSubmodule.obj (op U) }

/-- The chartwise universal property characterizing the subsheaf `𝓘 ^ n M`: it is contained in
a sheaf submodule `N` exactly when `N` contains `𝓘(U) ^ n • M(U)` over every étale chart. -/
theorem idealPowerMultiple_le_iff (n : ℕ) (M : Modules.{u, u} B S hS F hF) (N : M.Submodule) :
    idealPowerMultiple B S hS F hF 𝓘 n M ≤ N ↔
      ∀ U : SmallEtale B S hS F,
        chartIdeal B S hS ⟨F, hF⟩ 𝓘 U ^ n • (⊤ : Submodule (chartRing B S hS F hF U)
          (M.val.obj (op U))) ≤ N.toSubmodule.obj (op U) := by
  refine ⟨fun h U => le_trans ?_ (h (op U)), fun h => sInf_le h⟩
  show _ ≤ (sInf ((fun P : M.Submodule => P.toSubmodule) ''
      { P : M.Submodule | ∀ V : SmallEtale B S hS F,
        chartIdeal B S hS ⟨F, hF⟩ 𝓘 V ^ n • (⊤ : Submodule (chartRing B S hS F hF V)
          (M.val.obj (op V))) ≤ P.toSubmodule.obj (op V) })).obj (op U)
  rw [PresheafOfModules.Submodule.sInf_obj]
  refine le_iInf₂ ?_
  rintro _ ⟨Q, hQ, rfl⟩
  exact hQ U

/-- Over every étale chart, the subsheaf `𝓘 ^ n M` contains `𝓘(U) ^ n • M(U)`. -/
theorem le_idealPowerMultiple_obj (n : ℕ) (M : Modules.{u, u} B S hS F hF)
    (U : SmallEtale B S hS F) :
    chartIdeal B S hS ⟨F, hF⟩ 𝓘 U ^ n • (⊤ : Submodule (chartRing B S hS F hF U)
      (M.val.obj (op U))) ≤ (idealPowerMultiple B S hS F hF 𝓘 n M).toSubmodule.obj (op U) :=
  (idealPowerMultiple_le_iff B S hS F hF 𝓘 n M _).1 le_rfl U

/-- The subsheaves `𝓘 ^ n M` decrease in `n`. -/
theorem idealPowerMultiple_succ_le (n : ℕ) (M : Modules.{u, u} B S hS F hF) :
    idealPowerMultiple B S hS F hF 𝓘 (n + 1) M ≤ idealPowerMultiple B S hS F hF 𝓘 n M := by
  rw [idealPowerMultiple_le_iff]
  refine fun U => le_trans (Submodule.smul_mono ?_ le_rfl)
    (le_idealPowerMultiple_obj B S hS F hF 𝓘 n M U)
  exact Ideal.pow_le_pow_right (Nat.le_succ n)

/-- The quotient `M / 𝓘 ^ n M` of a module on an algebraic space. -/
abbrev idealPowerQuotient (n : ℕ) (M : Modules.{u, u} B S hS F hF) :
    Modules.{u, u} B S hS F hF :=
  cokernel (idealPowerMultiple B S hS F hF 𝓘 n M).ι

/-! ### The category `Coh(F, 𝓘)` -/

/-- The defining conditions of a coherent adic system along a sheaf of ideals `𝓘 ⊆ 𝒪_F` on an
algebraic space: every term is coherent, the term at `n` is annihilated by the `(n + 1)`-st
power of `𝓘`, and it is the quotient of the next term by that same power, compatibly with the
transition map.

The system is zero-indexed: its term at `n` is `E_{n + 1}` in the numbering by positive
integers. -/
def IsCoherentAdicSystem (E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF) : Prop :=
  (∀ n : ℕ, IsCoherent B S hS F hF (E.obj (op n))) ∧
  (∀ n : ℕ, idealPowerMultiple B S hS F hF 𝓘 (n + 1) (E.obj (op n)) = ⊥) ∧
  (∀ n : ℕ, ∃ e : idealPowerQuotient B S hS F hF 𝓘 (n + 1) (E.obj (op (n + 1))) ≅
      E.obj (op n),
    cokernel.π ((idealPowerMultiple B S hS F hF 𝓘 (n + 1) (E.obj (op (n + 1)))).ι) ≫ e.hom =
      E.map (homOfLE (Nat.le_succ n)).op)

/-- The category `Coh(F, 𝓘)` of coherent adic systems on an algebraic space, as a full
subcategory of the inverse systems of `𝒪_F`-modules. -/
abbrev CoherentAdicSystems :=
  ObjectProperty.FullSubcategory (C := ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF)
    (IsCoherentAdicSystem B S hS F hF 𝓘)

/-! ### Sections of a sheaf submodule and of a sheaf quotient -/

/-- A section of the zero sheaf submodule vanishes. -/
theorem eq_zero_of_mem_bot_submodule (M : Modules.{u, u} B S hS F hF)
    (X : (SmallEtale B S hS F)ᵒᵖ) {x : M.val.obj X}
    (hx : x ∈ (⊥ : M.Submodule).obj X) : x = 0 :=
  (SheafOfModules.Submodule.mem_ker (𝟙 M) X x).mp
    ((bot_le (a := SheafOfModules.Submodule.ker (𝟙 M))) X hx)

/-- The inclusion of a sheaf submodule `P` of `M` is annihilated by `h : M ⟶ N` exactly when
`P` is contained in the kernel of `h`. -/
theorem submodule_ι_comp_eq_zero_iff {M N : Modules.{u, u} B S hS F hF}
    (P : M.Submodule) (h : M ⟶ N) :
    P.ι ≫ h = 0 ↔ P ≤ SheafOfModules.Submodule.ker h := by
  refine ⟨fun hh X x hx => congrArg (fun k : P.toSheafOfModules ⟶ N => k.val.app X ⟨x, hx⟩) hh,
    fun hh => ?_⟩
  ext X x
  exact hh X x.property

/-- A sheaf submodule which vanishes has zero inclusion. -/
theorem submodule_ι_eq_zero_of_eq_bot {M : Modules.{u, u} B S hS F hF} {P : M.Submodule}
    (hP : P = ⊥) : P.ι = 0 := by
  subst hP
  simpa using (submodule_ι_comp_eq_zero_iff B S hS F hF (⊥ : M.Submodule) (𝟙 M)).mpr bot_le

/-- A section of a module on an algebraic space dies in the quotient by a sheaf submodule
exactly when it is a section of that submodule. -/
theorem cokernel_π_app_eq_zero_iff {M : Modules.{u, u} B S hS F hF} (P : M.Submodule)
    (X : (SmallEtale B S hS F)ᵒᵖ) (s : M.val.obj X) :
    (cokernel.π P.ι).val.app X s = 0 ↔ s ∈ P.obj X := by
  let T := SheafOfModules.evaluation
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) X
  let _ : T.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  let _ : PreservesFiniteLimits T :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) X
  have hh := (ShortComplex.moduleCat_exact_iff _).mp
    ((ShortComplex.exact_cokernel P.ι).map_of_mono_of_preservesKernel T inferInstance inferInstance)
  refine ⟨fun hs => ?_, fun hs => congrArg
    (fun k : P.toSheafOfModules ⟶ cokernel P.ι => k.val.app X ⟨s, hs⟩) (cokernel.condition P.ι)⟩
  obtain ⟨t, ht⟩ := hh s hs
  exact ht ▸ t.property

/-- If an epimorphism `φ` onto `N` dies in the quotient by `P`, every section of `N` lies in `P`. -/
private theorem mem_of_epi_comp_cokernel_π_eq_zero {M N : Modules.{u, u} B S hS F hF}
    (P : N.Submodule) (φ : M ⟶ N) [Epi φ] (h : φ ≫ cokernel.π P.ι = 0)
    (X : (SmallEtale B S hS F)ᵒᵖ) (x : N.val.obj X) : x ∈ P.obj X := by
  refine (cokernel_π_app_eq_zero_iff B S hS F hF P X x).mp ?_
  rw [zero_of_epi_comp φ h]
  rfl

/-- A module on an algebraic space with no nonzero section over any étale chart is a zero
object. -/
theorem isZero_of_sections_eq_zero (M : Modules.{u, u} B S hS F hF)
    (h : ∀ (U : SmallEtale B S hS F) (x : M.val.obj (op U)), x = 0) : IsZero M := by
  refine (IsZero.iff_id_eq_zero M).mpr ?_
  ext X x
  obtain ⟨U⟩ := X
  simp [h U x]

/-! ### Annihilation by a power of `𝓘` -/

/-- Restriction of a section along the identity leaves it unchanged. -/
theorem restrictₛₗ_id (M : Modules.{u, u} B S hS F hF)
    {X : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ} (x : M.val.obj X) :
    M.val.restrictₛₗ (𝟙 X) x = x := by
  show M.val.presheaf.map (𝟙 X) x = x
  rw [M.val.presheaf.map_id X]
  rfl

/-- Restriction of sections is functorial. -/
theorem restrictₛₗ_restrictₛₗ (M : Modules.{u, u} B S hS F hF)
    {X Y Z : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : M.val.obj X) :
    M.val.restrictₛₗ g (M.val.restrictₛₗ f x) = M.val.restrictₛₗ (f ≫ g) x :=
  (PresheafOfModules.map_comp_apply M.val f g x).symm

/-- Restriction along a morphism of étale charts carries the `k`-th power of the ideal of
sections of `𝓘` into the `k`-th power of the ideal of sections over the smaller chart. -/
theorem chartRestrict_mem_chartIdeal_pow {U V : SmallEtale B S hS F} (g : V ⟶ U) (k : ℕ)
    {r : chartRing B S hS F hF U} (hr : r ∈ chartIdeal B S hS ⟨F, hF⟩ 𝓘 U ^ k) :
    chartRestrict (hF := hF) g r ∈ chartIdeal B S hS ⟨F, hF⟩ 𝓘 V ^ k := by
  have h : chartIdeal B S hS ⟨F, hF⟩ 𝓘 U ≤
      (chartIdeal B S hS ⟨F, hF⟩ 𝓘 V).comap (chartRestrict (hF := hF) g) :=
    fun x hx => 𝓘.map_mem g.op hx
  exact ((pow_le_pow_left' h k).trans (Ideal.le_comap_pow _ k)) hr

/-- `𝓘 ^ k` annihilates the sections of `M`: over every étale chart `U`, every section of
`𝓘 ^ k` over `U` kills every section of `M` over `U`. -/
def IsPowAnnihilated (k : ℕ) (M : Modules.{u, u} B S hS F hF) : Prop :=
  ∀ (U : SmallEtale B S hS F) (r : chartRing B S hS F hF U),
    r ∈ chartIdeal B S hS ⟨F, hF⟩ 𝓘 U ^ k → ∀ x : M.val.obj (op U), r • x = 0

/-- The subsheaf `𝓘 ^ k M` vanishes exactly when `𝓘 ^ k` annihilates the sections of `M` over
every étale chart. -/
theorem idealPowerMultiple_eq_bot_iff (k : ℕ) (M : Modules.{u, u} B S hS F hF) :
    idealPowerMultiple B S hS F hF 𝓘 k M = ⊥ ↔ IsPowAnnihilated B S hS F hF 𝓘 k M := by
  refine ⟨fun h U r hr x => eq_zero_of_mem_bot_submodule B S hS F hF M (op U)
    ((idealPowerMultiple_le_iff B S hS F hF 𝓘 k M ⊥).mp h.le U
      (Submodule.smul_mem_smul hr Submodule.mem_top)), fun h => ?_⟩
  refine le_antisymm ((idealPowerMultiple_le_iff B S hS F hF 𝓘 k M ⊥).mpr fun U => ?_) bot_le
  refine Submodule.smul_le.mpr fun r hr x _ => ?_
  rw [h U r hr x]
  exact Submodule.zero_mem _

/-- The inclusion of `𝓘 ^ k M` is annihilated by `h : M ⟶ N` exactly when `h` kills every
product of a section of `𝓘 ^ k` with a section of `M` over a common étale chart. -/
theorem idealPowerMultiple_ι_comp_eq_zero_iff (k : ℕ) {M N : Modules.{u, u} B S hS F hF}
    (h : M ⟶ N) :
    (idealPowerMultiple B S hS F hF 𝓘 k M).ι ≫ h = 0 ↔
      ∀ (U : SmallEtale B S hS F) (r : chartRing B S hS F hF U),
        r ∈ chartIdeal B S hS ⟨F, hF⟩ 𝓘 U ^ k →
        ∀ x : M.val.obj (op U), h.val.app (op U) (r • x) = 0 := by
  rw [submodule_ι_comp_eq_zero_iff, idealPowerMultiple_le_iff]
  exact ⟨fun hh U r hr x => hh U (Submodule.smul_mem_smul hr Submodule.mem_top),
    fun hh U => Submodule.smul_le.mpr fun r hr x _ => hh U r hr x⟩

/-- A section of `M` whose restriction to any further étale chart `V` is annihilated by
`𝓘(V) ^ k`. -/
def IsPowAnnihilatedSection (k : ℕ) (M : Modules.{u, u} B S hS F hF)
    {X : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ} (x : M.val.obj X) : Prop :=
  ∀ (V : SmallEtale B S hS F) (g : X ⟶ op V) (r : chartRing B S hS F hF V),
    r ∈ chartIdeal B S hS ⟨F, hF⟩ 𝓘 V ^ k → r • M.val.restrictₛₗ g x = 0

/-- A section annihilated by `𝓘 ^ k` after every restriction is annihilated by `𝓘 ^ k`. -/
theorem smul_eq_zero_of_isPowAnnihilatedSection (k : ℕ) (M : Modules.{u, u} B S hS F hF)
    {X : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ} {x : M.val.obj X}
    (hx : IsPowAnnihilatedSection B S hS F hF 𝓘 k M x)
    (r : chartRing B S hS F hF X.unop)
    (hr : r ∈ chartIdeal B S hS ⟨F, hF⟩ 𝓘 X.unop ^ k) : r • x = 0 := by
  have h := hx X.unop (𝟙 X) r hr
  rwa [restrictₛₗ_id] at h

/-- The sheaf submodule of the sections annihilated by `𝓘 ^ k` after every restriction. -/
def powAnnihilator (k : ℕ) (M : Modules.{u, u} B S hS F hF) : M.Submodule where
  toSubmodule :=
    { obj X :=
        { carrier := {x : M.val.obj X | IsPowAnnihilatedSection B S hS F hF 𝓘 k M x}
          add_mem' := by
            intro a b ha hb V g r hr
            rw [map_add, smul_add, ha V g r hr, hb V g r hr, add_zero]
          zero_mem' := by
            intro V g r hr
            rw [map_zero, smul_zero]
          smul_mem' := by
            intro c a ha V g r hr
            rw [map_smulₛₗ, smul_smul, mul_comm, ← smul_smul, ha V g r hr, smul_zero] }
      map := by
        intro X Y f x hx V g r hr
        rw [restrictₛₗ_restrictₛₗ B S hS F hF M f g x]
        exact hx V (f ≫ g) r hr }
  isSheaf := by
    intro X s hs V g r hr
    refine M.isSheaf.isSeparated V _ (GrothendieckTopology.pullback_stable _ g.unop hs) _ 0
      fun W i hi => ?_
    change M.val.restrictₛₗ i.op (r • M.val.restrictₛₗ g s) = M.val.restrictₛₗ i.op 0
    rw [map_zero, map_smulₛₗ, restrictₛₗ_restrictₛₗ B S hS F hF M g i.op s]
    exact smul_eq_zero_of_isPowAnnihilatedSection B S hS F hF 𝓘 k M hi
      (chartRestrict (hF := hF) i r)
      (chartRestrict_mem_chartIdeal_pow B S hS F hF 𝓘 i k hr)

/-- A module all of whose sections lie in `powAnnihilator 𝓘 k` is annihilated by `𝓘 ^ k`. -/
theorem isPowAnnihilated_of_mem_powAnnihilator (k : ℕ) (M : Modules.{u, u} B S hS F hF)
    (h : ∀ (U : SmallEtale B S hS F) (x : M.val.obj (op U)),
      x ∈ (powAnnihilator B S hS F hF 𝓘 k M).obj (op U)) :
    IsPowAnnihilated B S hS F hF 𝓘 k M := fun U r hr x =>
  smul_eq_zero_of_isPowAnnihilatedSection B S hS F hF 𝓘 k M (h U x) r hr

/-- Annihilation by a power of `𝓘` passes to a quotient: if `𝓘 ^ k` annihilates `M` and
`φ : M ⟶ N` is surjective, then `𝓘 ^ k` annihilates `N`. -/
theorem isPowAnnihilated_of_epi (k : ℕ) {M N : Modules.{u, u} B S hS F hF} (φ : M ⟶ N) [Epi φ]
    (hM : IsPowAnnihilated B S hS F hF 𝓘 k M) : IsPowAnnihilated B S hS F hF 𝓘 k N := by
  have hz : φ ≫ cokernel.π (powAnnihilator B S hS F hF 𝓘 k N).ι = 0 := by
    ext X y
    show (cokernel.π (powAnnihilator B S hS F hF 𝓘 k N).ι).val.app X (φ.val.app X y) = 0
    refine (cokernel_π_app_eq_zero_iff B S hS F hF _ X _).mpr ?_
    intro V g r hr
    have h1 : N.val.restrictₛₗ g (φ.val.app X y)
        = φ.val.app (op V) (M.val.restrictₛₗ g y) :=
      (PresheafOfModules.naturality_apply φ.val g y).symm
    have h2 : r • φ.val.app (op V) (M.val.restrictₛₗ g y)
        = φ.val.app (op V) (r • M.val.restrictₛₗ g y) :=
      ((φ.val.app (op V)).hom.map_smul r _).symm
    rw [h1, h2, hM V r hr _]
    simp
  exact isPowAnnihilated_of_mem_powAnnihilator B S hS F hF 𝓘 k N fun U x =>
    mem_of_epi_comp_cokernel_π_eq_zero B S hS F hF _ φ hz (op U) x

/-- If every section of `M` is a section of `𝓘 ^ a M`, and `𝓘 ^ j` annihilates `M` with
`j ≤ k + a`, then already `𝓘 ^ k` annihilates `M`. -/
theorem isPowAnnihilated_of_mem_idealPowerMultiple (a j k : ℕ)
    (M : Modules.{u, u} B S hS F hF)
    (hfull : ∀ (U : SmallEtale B S hS F) (x : M.val.obj (op U)),
      x ∈ (idealPowerMultiple B S hS F hF 𝓘 a M).obj (op U))
    (hj : IsPowAnnihilated B S hS F hF 𝓘 j M) (hjk : j ≤ k + a) :
    IsPowAnnihilated B S hS F hF 𝓘 k M := by
  have hle : idealPowerMultiple B S hS F hF 𝓘 a M ≤ powAnnihilator B S hS F hF 𝓘 k M := by
    refine (idealPowerMultiple_le_iff B S hS F hF 𝓘 a M _).mpr fun U =>
      Submodule.smul_le.mpr fun r hr x _ => ?_
    intro V g s hs
    rw [map_smulₛₗ, smul_smul]
    refine hj V _ (Ideal.pow_le_pow_right hjk ?_) _
    rw [pow_add]
    exact Ideal.mul_mem_mul hs (chartRestrict_mem_chartIdeal_pow B S hS F hF 𝓘 g.unop a hr)
  exact isPowAnnihilated_of_mem_powAnnihilator B S hS F hF 𝓘 k M
    fun U x => hle (op U) (hfull U x)

/-! ### Surjectivity in `Coh(F, 𝓘)` -/

/-- The transition map of a coherent adic system is surjective. -/
theorem epi_map_le_succ {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF}
    (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E) (n : ℕ) :
    Epi (E.map (homOfLE (Nat.le_succ n)).op) := by
  obtain ⟨e, he⟩ := hE.2.2 n
  rw [← he]
  exact epi_comp _ _

/-- A morphism out of the term at `n + 1` of a coherent adic system which annihilates
`𝓘 ^ (n + 1)` of that term factors through the transition map. -/
theorem exists_desc_of_transition {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF}
    (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E) (n : ℕ) {T : Modules.{u, u} B S hS F hF}
    (h : E.obj (op (n + 1)) ⟶ T)
    (hh : (idealPowerMultiple B S hS F hF 𝓘 (n + 1) (E.obj (op (n + 1)))).ι ≫ h = 0) :
    ∃ d : E.obj (op n) ⟶ T, E.map (homOfLE (Nat.le_succ n)).op ≫ d = h := by
  obtain ⟨e, he⟩ := hE.2.2 n
  refine ⟨e.inv ≫ cokernel.desc _ h hh, ?_⟩
  rw [← he, Category.assoc, ← Category.assoc e.hom, e.hom_inv_id, Category.id_comp,
    cokernel.π_desc]

/-- A morphism of coherent adic systems which is surjective at level `n` is surjective at level
`n + 1`. -/
theorem epi_app_succ_of_epi_app {E E' : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF}
    (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E) (hE' : IsCoherentAdicSystem B S hS F hF 𝓘 E')
    (f : E ⟶ E') (n : ℕ) (hn : Epi (f.app (op n))) : Epi (f.app (op (n + 1))) := by
  have hp : Epi (E.map (homOfLE (Nat.le_succ n)).op) := epi_map_le_succ B S hS F hF 𝓘 hE n
  have hann2 : IsPowAnnihilated B S hS F hF 𝓘 (n + 1 + 1) (cokernel (f.app (op (n + 1)))) :=
    isPowAnnihilated_of_epi B S hS F hF 𝓘 _ (cokernel.π (f.app (op (n + 1))))
      ((idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 (n + 1 + 1) _).mp (hE'.2.1 (n + 1)))
  have hfull : ∀ (U : SmallEtale B S hS F)
      (x : (cokernel (f.app (op (n + 1)))).val.obj (op U)),
      x ∈ (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
        (cokernel (f.app (op (n + 1))))).obj (op U) := by
    have hι : (idealPowerMultiple B S hS F hF 𝓘 (n + 1) (E'.obj (op (n + 1)))).ι ≫
        (cokernel.π (f.app (op (n + 1))) ≫ cokernel.π
          (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
            (cokernel (f.app (op (n + 1))))).ι) = 0 := by
      refine (idealPowerMultiple_ι_comp_eq_zero_iff B S hS F hF 𝓘 (n + 1) _).mpr ?_
      intro U r hr x
      show (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
          (cokernel (f.app (op (n + 1))))).ι).val.app (op U)
        ((cokernel.π (f.app (op (n + 1)))).val.app (op U) (r • x)) = 0
      rw [(((cokernel.π (f.app (op (n + 1))))).val.app (op U)).hom.map_smul r x]
      refine (cokernel_π_app_eq_zero_iff B S hS F hF _ (op U) _).mpr ?_
      exact le_idealPowerMultiple_obj B S hS F hF 𝓘 (n + 1) _ U
        (Submodule.smul_mem_smul hr Submodule.mem_top)
    obtain ⟨d, hd⟩ := exists_desc_of_transition B S hS F hF 𝓘 hE' n _ hι
    have hfd : f.app (op n) ≫ d = 0 := by
      refine (cancel_epi (E.map (homOfLE (Nat.le_succ n)).op)).mp ?_
      rw [comp_zero, ← Category.assoc, f.naturality, Category.assoc, hd, ← Category.assoc,
        cokernel.condition, zero_comp]
    intro U x
    refine mem_of_epi_comp_cokernel_π_eq_zero B S hS F hF _ (cokernel.π (f.app (op (n + 1))))
      ?_ (op U) x
    rw [← hd, zero_of_epi_comp _ hfd, comp_zero]
  have hann1 : IsPowAnnihilated B S hS F hF 𝓘 (n + 1) (cokernel (f.app (op (n + 1)))) :=
    isPowAnnihilated_of_mem_idealPowerMultiple B S hS F hF 𝓘 (n + 1) (n + 1 + 1) (n + 1) _
      hfull hann2 (by lia)
  have hbot : idealPowerMultiple B S hS F hF 𝓘 (n + 1)
      (cokernel (f.app (op (n + 1)))) = ⊥ :=
    (idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 (n + 1) _).mpr hann1
  refine Preadditive.epi_of_isZero_cokernel _
    (isZero_of_sections_eq_zero B S hS F hF _ fun U x => ?_)
  exact eq_zero_of_mem_bot_submodule B S hS F hF _ (op U) (hbot ▸ hfull U x)

/-- Surjectivity at the lowest level implies surjectivity in `Coh(F, 𝓘)`. -/
theorem epi_of_epi_app_zero {E E' : CoherentAdicSystems B S hS F hF 𝓘} (f : E ⟶ E')
    (h : Epi (f.hom.app (op 0))) : Epi f := by
  have hn (n : ℕ) : Epi (f.hom.app (op n)) := by
    induction n with
    | zero => exact h
    | succ n ih =>
        exact epi_app_succ_of_epi_app B S hS F hF 𝓘 E.property E'.property f.hom n ih
  have (X : ℕᵒᵖ) : Epi (f.hom.app X) := hn X.unop
  exact (ObjectProperty.ι _).epi_of_epi_map (NatTrans.epi_of_epi_app f.hom)

/-- Surjectivity in `Coh(F, 𝓘)` implies surjectivity at the lowest level. -/
theorem epi_app_zero_of_epi {E E' : CoherentAdicSystems B S hS F hF 𝓘} (f : E ⟶ E')
    (hf : Epi f) : Epi (f.hom.app (op 0)) := by
  have hQann : IsPowAnnihilated B S hS F hF 𝓘 1 (cokernel (f.hom.app (op 0))) :=
    isPowAnnihilated_of_epi B S hS F hF 𝓘 1 (cokernel.π (f.hom.app (op 0)))
      ((idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 1 _).mp (E'.property.2.1 0))
  have hQbot : ∀ n : ℕ, idealPowerMultiple B S hS F hF 𝓘 (n + 1)
      (cokernel (f.hom.app (op 0))) = ⊥ := fun n =>
    (idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 (n + 1) _).mpr
      fun U r hr x => hQann U r (Ideal.pow_le_pow_right (by lia) hr) x
  have hQsys : IsCoherentAdicSystem B S hS F hF 𝓘
      ((Functor.const ℕᵒᵖ).obj (cokernel (f.hom.app (op 0)))) := by
    refine ⟨fun n => isCoherent_cokernel B S hS F hF (E.property.1 0) (E'.property.1 0) _,
      hQbot, fun n => ?_⟩
    refine ⟨(cokernelIsoOfEq (submodule_ι_eq_zero_of_eq_bot B S hS F hF
      (hQbot n))).trans cokernelZeroIsoTarget, ?_⟩
    rw [Iso.trans_hom, ← Category.assoc, π_comp_cokernelIsoOfEq_hom, cokernelZeroIsoTarget_hom,
      cokernel.π_desc]
    rfl
  let H : CoherentAdicSystems B S hS F hF 𝓘 :=
    ⟨(Functor.const ℕᵒᵖ).obj (cokernel (f.hom.app (op 0))), hQsys⟩
  let a : E' ⟶ H := ObjectProperty.homMk
    { app := fun X => E'.obj.map (homOfLE (Nat.zero_le X.unop)).op ≫
        cokernel.π (f.hom.app (op 0))
      naturality := by
        intro X Y h
        show E'.obj.map h ≫ (E'.obj.map _ ≫ cokernel.π (f.hom.app (op 0))) =
          (E'.obj.map _ ≫ cokernel.π (f.hom.app (op 0))) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, ← Functor.map_comp]
        rfl }
  have hfa : f ≫ a = 0 := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    show f.hom.app X ≫ (E'.obj.map _ ≫ cokernel.π (f.hom.app (op 0))) = 0
    rw [← Category.assoc, ← f.hom.naturality, Category.assoc, cokernel.condition, comp_zero]
  have ha : a = 0 := zero_of_epi_comp f hfa
  have hq : cokernel.π (f.hom.app (op 0)) = 0 := by
    have h := congrArg (fun k : E' ⟶ H => k.hom.app (op 0)) ha
    change E'.obj.map (homOfLE (Nat.zero_le 0)).op ≫ cokernel.π (f.hom.app (op 0)) = 0 at h
    simpa using h
  refine Preadditive.epi_of_isZero_cokernel _ ((IsZero.iff_id_eq_zero _).mpr ?_)
  refine (cancel_epi (cokernel.π (f.hom.app (op 0)))).mp ?_
  simp [hq]

/-- A map of coherent adic systems on an algebraic space is surjective in `Coh(F, 𝓘)` exactly when
its component at the lowest level is surjective. -/
@[stacks 08B3]
theorem epi_iff_epi_app_zero {E E' : CoherentAdicSystems B S hS F hF 𝓘} (f : E ⟶ E') :
    Epi f ↔ Epi (f.hom.app (op 0)) :=
  ⟨fun hf => epi_app_zero_of_epi B S hS F hF 𝓘 f hf,
    fun h => epi_of_epi_app_zero B S hS F hF 𝓘 f h⟩

end AlgebraicGeometry.Space

end
