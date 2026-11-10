module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseModuleTwist
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjShiftedSectionModule
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionRing
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.GlobalSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Veronese comparison on global sections

Let `S` be a graded ring, `d ≥ 1`, `S' = S⁽ᵈ⁾`, `i : X = Proj S ≅ X' = Proj S'` the Veronese
isomorphism and `M` a graded `S`-module, with `M' = M⁽ᵈ⁾`. Global sections of `i^*𝒢` are reached
from global sections of `𝒢` by the unit of the pullback, `Γ(X', 𝒢) → Γ(X, i^*𝒢)`. This file
proves that Tag 0B5J's isomorphisms carry the canonical maps from homogeneous elements to global
sections on `X` to those on `X'`:

* for the graded ring map `S → ⨁_{n ≥ 0} Γ(X, 𝒪_X(n))` of Tag 01MP: an element `a` of `S'`, read
  in degree `nd` on `X` and carried by assertion (2), is the pullback of `a` read in degree `n`
  on `X'` (`veroneseGlobalSectionsRingMapCompatibility`);
* for the graded module map `M → ⨁_n Γ(X, M(n)~)` of Tag 01MR: likewise with
  `M(nd)~ ≅ i^*(M'(n)~)` (`veroneseGlobalSectionsModuleMapCompatibility`).

Both rest on `associatedModuleSheafVeroneseIso_degreeZeroToGlobalSections`: assertion (1) carries
the global section `m / 1` of `M̃` to the pullback of the global section `m / 1` of `M'~`, which
is checked on the standard opens.

## References

* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory DirectSum TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections (degreeZeroToGlobalSections
  degreeZeroToGlobalSections_basicOpen degreeZeroToGlobalSections_apply)
open Stacks.GradedModule (shiftedGrading)
open _root_.AlgebraicGeometry.ProjectiveSpectrum.Proj (twistGrading twistingSheaf)

namespace Stacks.Veronese

attribute [local instance_reducible] TopCat.Sheaf
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] ProjectiveSpectrum.isPrime

universe u w

/-- The sheaf map of a graded linear map carries the global section `m / 1` to `φ(m) / 1`. -/
public theorem associatedModuleSheafMap_degreeZeroToGlobalSections {A P Q : Type u}
    {ς τ υ : Type*} [CommRing A] [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    [SetLike ς A] [AddSubgroupClass ς A] (𝒜 : ℕ → ς) [GradedRing 𝒜]
    [SetLike τ P] [AddSubgroupClass τ P] (ℒ : ℤ → τ) [Decomposition ℒ] [SetLike.GradedSMul 𝒜 ℒ]
    [SetLike υ Q] [AddSubgroupClass υ Q] (𝒬 : ℤ → υ) [Decomposition 𝒬] [SetLike.GradedSMul 𝒜 𝒬]
    (φ : P →ₗ[A] Q) (hφ : ∀ i (m : P), m ∈ ℒ i → φ m ∈ 𝒬 i) (m : ℒ 0) :
    (associatedModuleSheafMap 𝒜 ℒ 𝒬 φ hφ).val.app (op ⊤) (degreeZeroToGlobalSections 𝒜 ℒ m) =
      degreeZeroToGlobalSections 𝒜 𝒬 ⟨φ m, hφ 0 m m.2⟩ :=
  Subtype.ext <| funext fun _ => LocalizedModule.map_mk _ _ _ _

variable {S : Type u} {σ : Type w} [CommRing S]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- Transport of a global section `m / 1` of a twisting sheaf along an equality of twists. -/
public theorem eqToHom_twistingSheaf_degreeZeroToGlobalSections {a b : ℤ} (h : a = b) (x : S)
    (hx : x ∈ twistGrading (S := S) 𝒮 a 0) (hx' : x ∈ twistGrading (S := S) 𝒮 b 0) :
    (eqToHom (congrArg (twistingSheaf 𝒮) h)).val.app (op ⊤)
        (degreeZeroToGlobalSections 𝒮 (twistGrading (S := S) 𝒮 a) ⟨x, hx⟩) =
      degreeZeroToGlobalSections 𝒮 (twistGrading (S := S) 𝒮 b) ⟨x, hx'⟩ := by
  subst h
  rfl

/-- Restricting from `⊤` to an open is compatible with transport along an equality of opens. -/
public theorem val_map_top_cast {X : Scheme.{u}} (F : X.Modules) {W V : X.Opens}
    (h : W = V) (s : F.val.obj (op ⊤)) :
    F.val.map (homOfLE (le_top : V ≤ ⊤)).op s =
      h ▸ F.val.map (homOfLE (le_top : W ≤ ⊤)).op s := by
  cases h
  rfl

/-- The unit of the module pullback commutes with restriction, in the `val` spelling. -/
public theorem modulesPullbackUnit_val_map {X Y : Scheme.{u}} (g : X ⟶ Y) (F : Y.Modules)
    {U V : Y.Opens} (hVU : V ≤ U) (s : F.val.obj (op U)) :
    Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g F V (F.val.map (homOfLE hVU).op s) =
      ((Scheme.Modules.pullback g).obj F).val.map
        (homOfLE (show g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U from fun _ hz => hVU hz)).op
        (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g F U s) :=
  Stacks.Tag01VSPullbackTensor.modulesPullbackUnit_map g F hVU s

/-- The restriction of the global section `m / 1` to a standard open, as a fraction with
exponent `k = 0`. -/
public theorem degreeZeroToGlobalSections_restrict {A P : Type u} {ς : Type*} [CommRing A]
    [AddCommGroup P] [Module A P] [SetLike ς A] [AddSubgroupClass ς A] (𝒜 : ℕ → ς)
    [GradedRing 𝒜] (ℒ : ℤ → AddSubgroup P) [Decomposition ℒ] [SetLike.GradedSMul 𝒜 ℒ]
    {f : A} {c : ℕ} (hf : f ∈ 𝒜 c) (hc : 0 < c) (m : ℒ 0) (k : ℕ) (hk : k = 0)
    (hm : (m : P) ∈ ℒ (k • (c : ℤ))) :
    (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒜 ℒ).val.map
        (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒜 f ≤ ⊤)).op
        (degreeZeroToGlobalSections 𝒜 ℒ m) =
      (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒜 ℒ hf hc).symm
        (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒜 ℒ hf k (m : P) hm) := by
  subst hk
  exact (LinearEquiv.eq_symm_apply _).2 (degreeZeroToGlobalSections_basicOpen 𝒜 ℒ hf hc m)

variable {P : Type u} [AddCommGroup P] [Module S P] (𝒦 : ℤ → AddSubgroup P) [Decomposition 𝒦]
  [SetLike.GradedSMul 𝒮 𝒦]

/-- The global section `m / 1` of `P'~` attached to an element `mb` of `P'` of degree `0`. -/
public abbrev veroneseGlobalSection (d : ℕ) (hd : 0 < d) (mb : veroneseSubmodule 𝒮 𝒦 d)
    (hmb : mb ∈ veroneseModuleGrading 𝒮 𝒦 d 0) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒦 d hd
    (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒦 d)).val.obj (op ⊤) := by
  letI := veroneseGradingGradedRing 𝒮 d hd
  letI := veroneseModuleGradingDecomposition 𝒮 𝒦 d hd
  exact degreeZeroToGlobalSections (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒦 d) ⟨mb, hmb⟩

/-- **Assertion (1) of Tag 0B5J on the global section `m / 1`, on one chart.** -/
public theorem associatedModuleSheafVeroneseIso_degreeZeroToGlobalSections_chart (d : ℕ)
    (hd : 0 < d) (mb : veroneseSubmodule 𝒮 𝒦 d) (hmb : mb ∈ veroneseModuleGrading 𝒮 𝒦 d 0)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒦 d hd
    (associatedModuleSheafVeroneseIso 𝒮 𝒦 d hd).hom.val.app (op (Proj.basicOpen 𝒮 f))
        ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒦).val.map
          (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒮 f ≤ ⊤)).op
          (degreeZeroToGlobalSections 𝒮 𝒦 ⟨(mb : P), by simpa using hmb⟩)) =
      ((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
          (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
            (veroneseModuleGrading 𝒮 𝒦 d))).val.map
        (homOfLE (le_top : Proj.basicOpen 𝒮 f ≤ ⊤)).op
        (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
          (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
            (veroneseModuleGrading 𝒮 𝒦 d)) ⊤ (veroneseGlobalSection 𝒮 𝒦 d hd mb hmb)) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒦 d hd
  have hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e := veronesePower_mem 𝒮 d f hf
  have hmb' : mb ∈ veroneseModuleGrading 𝒮 𝒦 d ((0 : ℕ) • (e : ℤ)) := by simpa using hmb
  refine Eq.trans (congrArg (fun t => (associatedModuleSheafVeroneseIso 𝒮 𝒦 d hd).hom.val.app
      (op (Proj.basicOpen 𝒮 f)) t)
    (degreeZeroToGlobalSections_restrict 𝒮 𝒦 hf he _ (0 * d) (zero_mul d)
      (mem_of_mem_veroneseModuleGrading 𝒮 𝒦 d 0 e hmb'))) ?_
  refine (associatedModuleSheafVeroneseIso_hom_degreeZeroFraction 𝒮 𝒦 d hd f he hf 0 mb
    hmb' hvf).trans ?_
  refine Eq.trans ?_ (val_map_top_cast
    ((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
      (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 𝒦 d)))
    (veroneseProjIso_basicOpen 𝒮 d hd f he hf) _).symm
  refine congrArg (fun t => Eq.rec (motive := fun W _ =>
      ((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
        (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 𝒦 d))).val.obj (op W)) t
      (veroneseProjIso_basicOpen 𝒮 d hd f he hf)) ?_
  refine Eq.trans ?_ (modulesPullbackUnit_val_map (veroneseProjIso 𝒮 d hd).hom
    (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒦 d)) le_top _)
  exact congrArg (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit
    (veroneseProjIso 𝒮 d hd).hom _ _)
    (degreeZeroToGlobalSections_restrict (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒦 d)
      hvf he ⟨mb, hmb⟩ 0 rfl hmb').symm

/-- **Assertion (1) of Tag 0B5J on the global section `m / 1`.** For an element `mb` of degree
`0` of the Veronese part of a graded module `P`, the isomorphism `P̃ ≅ i^*(P'~)` carries the
global section `m / 1` of `P̃` to the pullback of the global section `m / 1` of `P'~`. -/
public theorem associatedModuleSheafVeroneseIso_degreeZeroToGlobalSections (d : ℕ) (hd : 0 < d)
    (mb : veroneseSubmodule 𝒮 𝒦 d) (hmb : mb ∈ veroneseModuleGrading 𝒮 𝒦 d 0) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒦 d hd
    (associatedModuleSheafVeroneseIso 𝒮 𝒦 d hd).hom.val.app (op ⊤)
        (degreeZeroToGlobalSections 𝒮 𝒦 ⟨(mb : P), by simpa using hmb⟩) =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
        (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 𝒦 d)) ⊤ (veroneseGlobalSection 𝒮 𝒦 d hd mb hmb) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒦 d hd
  let ι := { a : S × ℕ // 0 < a.2 ∧ a.1 ∈ 𝒮 a.2 }
  let W : ι → Opens (ProjectiveSpectrum.top 𝒮) :=
    fun a => ProjectiveSpectrum.basicOpen 𝒮 a.1.1
  have heq : Set.range W = positiveBasicOpenSet (𝒮 := 𝒮) := by
    ext V
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.1.1, a.1.2, a.2.1, a.2.2, rfl⟩
    · rintro ⟨g, k, hk, hg, rfl⟩
      exact ⟨⟨(g, k), hk, hg⟩, rfl⟩
  have hW : Opens.IsBasis (Set.range W) := by
    rw [heq]
    exact positiveBasicOpenSet_isBasis 𝒮
  exact Stacks.BasisRestriction.moduleSheafSection_ext_onBasis
    ((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
      (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 𝒦 d))) W hW _ _ fun a hle =>
    (moduleSheafHom_app_restrict (associatedModuleSheafVeroneseIso 𝒮 𝒦 d hd).hom hle _).trans
      (associatedModuleSheafVeroneseIso_degreeZeroToGlobalSections_chart 𝒮 𝒦 d hd mb hmb
        a.1.1 a.2.1 a.2.2)

/-- Two additive maps out of a subgroup-like `V`, whose members are exactly the elements of
`AddSubgroup.closure s`, agree once they agree on the elements of `s`. -/
private theorem addMonoidHom_eq_of_mem_closure {G N T : Type*} [AddGroup G] [AddGroup N]
    [SetLike T G] [AddSubgroupClass T G] {V : T} {s : Set G}
    (hV : ∀ x, x ∈ V ↔ x ∈ AddSubgroup.closure s) {L R : V →+ N}
    (h : ∀ x (_ : x ∈ s) (hxV : x ∈ V), L ⟨x, hxV⟩ = R ⟨x, hxV⟩) (x : V) : L x = R x := by
  suffices ∀ y (_ : y ∈ AddSubgroup.closure s) (hyV : y ∈ V), L ⟨y, hyV⟩ = R ⟨y, hyV⟩ from
    this x.1 ((hV x.1).mp x.2) x.2
  intro y hyc
  induction hyc using AddSubgroup.closure_induction with
  | mem y hy => exact h y hy
  | zero => exact fun _ => (map_zero L).trans (map_zero R).symm
  | add a b ha' hb' ha hb =>
    intro habV
    have hab : (⟨a + b, habV⟩ : V) = ⟨a, (hV a).2 ha'⟩ + ⟨b, (hV b).2 hb'⟩ := rfl
    rw [hab, map_add, map_add, ha, hb]
  | neg a ha' ha =>
    intro haV
    have hna : (⟨-a, haV⟩ : V) = -⟨a, (hV a).2 ha'⟩ := rfl
    rw [hna, map_neg, map_neg, ha]

/-- If `e` carries `x` to the pullback unit of `y`, then `e` followed by the pullback of `ψ` carries
`x` to the pullback unit of `ψ y`. -/
private theorem trans_mapIso_app_modulesPullbackUnit {X Y : Scheme.{u}} (g : X ⟶ Y)
    {Z : X.Modules} {A B : Y.Modules} (e : Z ≅ (Scheme.Modules.pullback g).obj A) (ψ : A ≅ B)
    {x : Z.val.obj (op ⊤)} {y : A.val.obj (op ⊤)}
    (hxy : e.hom.val.app (op ⊤) x = Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g A ⊤ y) :
    (e.trans ((Scheme.Modules.pullback g).mapIso ψ)).hom.val.app (op ⊤) x =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g B ⊤ (ψ.hom.val.app (op ⊤) y) :=
  (congrArg (fun t => (((Scheme.Modules.pullback g).map ψ.hom).val.app (op ⊤)) t) hxy).trans
    (modulesPullbackUnit_naturality g ψ.hom ⊤ y)

/-- A map vanishing at `0`, applied to the components of two `lof`s, compares the matching
components when the indices correspond and `0` otherwise. -/
private theorem apply_component_eq_of_lof {R ι κ T : Type*} [Semiring R] [DecidableEq ι]
    [DecidableEq κ] {β : ι → Type*} {γ : κ → Type*} [∀ i, AddCommMonoid (β i)]
    [∀ i, Module R (β i)] [∀ i, AddCommMonoid (γ i)] [∀ i, Module R (γ i)] [Zero T]
    {a j : ι} {b k : κ} {x : ⨁ i, β i} {y : ⨁ i, γ i} {v : β j} {w : γ k}
    (hx : x = lof R ι β j v) (hy : y = lof R κ γ k w) (Φ : β a → T) (Ψ : γ b → T)
    (hΦ : Φ 0 = 0) (hΨ : Ψ 0 = 0) (hjk : j = a ↔ k = b)
    (h : ∀ (hj : j = a) (hk : k = b), Φ (hj ▸ v) = Ψ (hk ▸ w)) :
    Φ (component R ι β a x) = Ψ (component R κ γ b y) := by
  subst hx hy
  by_cases hj : j = a
  · obtain rfl := hj
    obtain rfl := hjk.1 rfl
    simpa using h rfl rfl
  · simp [component.of, hj, mt hjk.2 hj, hΦ, hΨ]

section ModuleMap

variable {M : Type u} [AddCommGroup M] [Module S M] (𝒨 : ℤ → AddSubgroup M) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- **`veroneseShiftedModuleIso` on the global section `m / 1`.** For `m` homogeneous of degree
`nd` in `M`, the isomorphism `M(nd)~ ≅ i^*(M'(n)~)` carries the global section `m / 1` of
`M(nd)~` to the pullback of the global section `m / 1` of `M'(n)~`. -/
public theorem veroneseShiftedModuleIso_degreeZeroToGlobalSections (d : ℕ) (hd : 0 < d) (n : ℤ)
    (m : M) (hm : m ∈ 𝒨 (n * d)) (hmV : m ∈ veroneseSubmodule 𝒮 𝒨 d) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    (veroneseShiftedModuleIso 𝒮 𝒨 d hd n).hom.val.app (op ⊤)
        (degreeZeroToGlobalSections 𝒮 (shiftedGrading 𝒨 (n * d))
          ⟨m, by simpa only [shiftedGrading, zero_add] using hm⟩) =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
        (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
          (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n)) ⊤
        (degreeZeroToGlobalSections (veroneseGrading 𝒮 d)
          (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n)
          ⟨⟨m, hmV⟩, by
            change m ∈ 𝒨 ((0 + n) * (d : ℤ))
            simpa only [zero_add] using hm⟩) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  let := veroneseModuleGradingDecomposition 𝒮 (shiftedGrading 𝒨 (n * d)) d hd
  let mb : veroneseSubmodule 𝒮 (shiftedGrading 𝒨 (n * d)) d :=
    (veroneseModuleShiftEquiv 𝒮 𝒨 d n).symm ⟨m, hmV⟩
  have hmb : mb ∈ veroneseModuleGrading 𝒮 (shiftedGrading 𝒨 (n * d)) d 0 := by
    change m ∈ 𝒨 (0 * (d : ℤ) + n * d)
    simpa only [zero_mul, zero_add] using hm
  refine (trans_mapIso_app_modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom _
    (veroneseShiftedSheafIso 𝒮 𝒨 d hd n)
    (associatedModuleSheafVeroneseIso_degreeZeroToGlobalSections 𝒮
      (shiftedGrading 𝒨 (n * d)) d hd mb hmb)).trans ?_
  exact congrArg (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
    _ ⊤)
    (associatedModuleSheafMap_degreeZeroToGlobalSections (veroneseGrading 𝒮 d) _ _
      (veroneseModuleShiftEquiv 𝒮 𝒨 d n).toLinearMap (veroneseModuleShiftEquiv_mem 𝒮 𝒨 d n)
      ⟨mb, hmb⟩)

/-- The compatibility with Tag 01MR on a homogeneous element of degree `kd`. -/
public theorem veroneseGlobalSectionsModuleMapCompatibility_homogeneous (d : ℕ) (hd : 0 < d)
    (n k : ℤ) (y : M) (hk : y ∈ 𝒨 (k * d)) (hyV : y ∈ veroneseSubmodule 𝒮 𝒨 d) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    (veroneseShiftedModuleIso 𝒮 𝒨 d hd n).hom.val.app (op ⊤)
        (DirectSum.component ℤ ℤ _ (n * d)
          ((Stacks.AlgebraicGeometry.ProjShiftedSections.globalSectionsModuleMap 𝒮 𝒨).hom y)) =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
        (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
          (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n)) ⊤
        (DirectSum.component ℤ ℤ _ n
          ((Stacks.AlgebraicGeometry.ProjShiftedSections.globalSectionsModuleMap
            (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d)).hom ⟨y, hyV⟩)) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  have hk' : (⟨y, hyV⟩ : veroneseSubmodule 𝒮 𝒨 d) ∈ veroneseModuleGrading 𝒮 𝒨 d k := hk
  have h1 := (Stacks.AlgebraicGeometry.ProjShiftedSections.globalSectionsModuleMap 𝒮
    𝒨).map_homogeneous (k * d) ⟨y, hk⟩
  have h2 := (Stacks.AlgebraicGeometry.ProjShiftedSections.globalSectionsModuleMap
    (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d)).map_homogeneous k ⟨⟨y, hyV⟩, hk'⟩
  refine apply_component_eq_of_lof (a := n * d) (b := n) h1 h2
    (fun t => (veroneseShiftedModuleIso 𝒮 𝒨 d hd n).hom.val.app (op ⊤) t)
    (fun t => Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
      (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
        (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n)) ⊤ t)
    (map_zero _) (map_zero _) (mul_left_inj' (by exact_mod_cast hd.ne')) ?_
  intro _ hkn
  subst hkn
  exact veroneseShiftedModuleIso_degreeZeroToGlobalSections 𝒮 𝒨 d hd k y hk hyV

/-- **Tag 0B5J's isomorphisms are compatible with the map `M → ⨁ₙ Γ(Proj, M(n)~)` of Tag 01MR.**
For every element `m` of `M' = M⁽ᵈ⁾` and every integer `n`, the degree-`nd` component of the image
of `m` under the map of Tag 01MR on `X = Proj S`, carried by `M(nd)~ ≅ i^*(M'(n)~)`, is the
pullback of the degree-`n` component of the image of `m` under the map of Tag 01MR on
`X' = Proj S'`. -/
public theorem veroneseGlobalSectionsModuleMapCompatibility (d : ℕ) (hd : 0 < d) (n : ℤ)
    (m : veroneseSubmodule 𝒮 𝒨 d) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    (veroneseShiftedModuleIso 𝒮 𝒨 d hd n).hom.val.app (op ⊤)
        (DirectSum.component ℤ ℤ _ (n * d)
          ((Stacks.AlgebraicGeometry.ProjShiftedSections.globalSectionsModuleMap 𝒮 𝒨).hom
            (m : M))) =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
        (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
          (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n)) ⊤
        (DirectSum.component ℤ ℤ _ n
          ((Stacks.AlgebraicGeometry.ProjShiftedSections.globalSectionsModuleMap
            (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d)).hom m)) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  let L : veroneseSubmodule 𝒮 𝒨 d →+ _ :=
    ((veroneseShiftedModuleIso 𝒮 𝒨 d hd n).hom.val.app (op ⊤)).hom.toAddMonoidHom.comp
      ((DirectSum.component ℤ ℤ
        (Stacks.AlgebraicGeometry.ProjShiftedSections.shiftedSectionsComponent 𝒮 𝒨)
        (n * d)).toAddMonoidHom.comp
        ((Stacks.AlgebraicGeometry.ProjShiftedSections.globalSectionsModuleMap 𝒮
          𝒨).hom.toAddMonoidHom.comp (veroneseSubmodule 𝒮 𝒨 d).subtype.toAddMonoidHom))
  let R : veroneseSubmodule 𝒮 𝒨 d →+ _ :=
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction
        (veroneseProjIso 𝒮 d hd).hom).unit.app
        (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
          (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n))) ⊤).hom.comp
      ((DirectSum.component ℤ ℤ
        (Stacks.AlgebraicGeometry.ProjShiftedSections.shiftedSectionsComponent
          (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d)) n).toAddMonoidHom.comp
        (Stacks.AlgebraicGeometry.ProjShiftedSections.globalSectionsModuleMap
          (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d)).hom.toAddMonoidHom)
  refine addMonoidHom_eq_of_mem_closure (L := L) (R := R)
    (fun _ => mem_veroneseSubmodule_iff 𝒮 𝒨 d) (fun y hy hyV => ?_) m
  obtain ⟨k, hk⟩ := (mem_veroneseModuleSet_iff 𝒨).mp hy
  exact veroneseGlobalSectionsModuleMapCompatibility_homogeneous 𝒮 𝒨 d hd n k y hk hyV

end ModuleMap

section RingMap

open _root_.AlgebraicGeometry.ProjectiveSpectrum.Proj (degreeSection twistGlobalSections
  globalSectionsRingMap)

/-- **Assertion (2) of Tag 0B5J on the global section of a homogeneous element.** For `a` in
`S_{nd} = S'_n`, the isomorphism `𝒪_X(nd) ≅ i^*𝒪_{X'}(n)` carries the global section `a` of
`𝒪_X(nd)` to the pullback of the global section `a` of `𝒪_{X'}(n)`. -/
public theorem veroneseTwistingSheafIso_degreeSection (d : ℕ) (hd : 0 < d) (n : ℕ)
    (a : veroneseSubring 𝒮 d) (ha : (a : S) ∈ 𝒮 (n * d)) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    (veroneseTwistingSheafIso 𝒮 d hd n).hom.val.app (op ⊤)
        ((eqToHom (congrArg (twistingSheaf 𝒮) (Nat.cast_mul n d))).val.app (op ⊤)
          (degreeSection 𝒮 (n * d) ⟨a, ha⟩)) =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
        (twistingSheaf (veroneseGrading 𝒮 d) n) ⊤
        (degreeSection (veroneseGrading 𝒮 d) n ⟨a, ha⟩) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d hd
  have h0 : (a : S) ∈ twistGrading (S := S) 𝒮 ((n : ℤ) * d) 0 := by
    have := (mem_twistGrading_mul_iff 𝒮 d hd (n : ℤ) 0 (a : S)).2
    simp only [zero_mul, zero_add, Nat.cast_nonneg, ite_true, Int.toNat_natCast] at this
    simpa using this ha
  let mb : veroneseSubmodule 𝒮 (twistGradingAddSubgroup 𝒮 ((n : ℤ) * d)) d :=
    ⟨a, coe_mem_veroneseSubmodule_twist 𝒮 d (n : ℤ) a⟩
  have hmb : mb ∈ veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 ((n : ℤ) * d)) d 0 := by
    change (a : S) ∈ twistGradingAddSubgroup 𝒮 ((n : ℤ) * d) (0 * (d : ℤ))
    simpa [twistGradingAddSubgroup] using h0
  refine (congrArg (fun t => (veroneseTwistingSheafIso 𝒮 d hd n).hom.val.app (op ⊤) t)
    (eqToHom_twistingSheaf_degreeZeroToGlobalSections 𝒮 (Nat.cast_mul n d) (a : S) _ h0)).trans ?_
  refine (trans_mapIso_app_modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom _
    (veroneseShiftSheafIso 𝒮 d hd n)
    (associatedModuleSheafVeroneseIso_degreeZeroToGlobalSections 𝒮
      (twistGradingAddSubgroup 𝒮 ((n : ℤ) * d)) d hd mb hmb)).trans ?_
  exact congrArg (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
    _ ⊤)
    (associatedModuleSheafMap_degreeZeroToGlobalSections (veroneseGrading 𝒮 d) _ _
      (veroneseShiftLinearEquiv 𝒮 d hd n).toLinearMap (veroneseShiftLinearEquiv_mem 𝒮 d hd n)
      ⟨mb, hmb⟩)

/-- The compatibility with Tag 01MP on a homogeneous element of degree `kd`. -/
public theorem veroneseGlobalSectionsRingMapCompatibility_homogeneous (d : ℕ) (hd : 0 < d)
    (n k : ℕ) (y : S) (hk : y ∈ 𝒮 (k * d)) (hyV : y ∈ veroneseSubring 𝒮 d) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := (globalSectionsRingMap 𝒮).gradedRing
    letI := (globalSectionsRingMap (veroneseGrading 𝒮 d)).gradedRing
    (veroneseTwistingSheafIso 𝒮 d hd n).hom.val.app (op ⊤)
        ((eqToHom (congrArg (twistingSheaf 𝒮) (Nat.cast_mul n d))).val.app (op ⊤)
          (DirectSum.component ℤ ℕ (twistGlobalSections 𝒮) (n * d)
            ((globalSectionsRingMap 𝒮).hom y))) =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
        (twistingSheaf (veroneseGrading 𝒮 d) n) ⊤
        (DirectSum.component ℤ ℕ (twistGlobalSections (veroneseGrading 𝒮 d)) n
          ((globalSectionsRingMap (veroneseGrading 𝒮 d)).hom ⟨y, hyV⟩)) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := (globalSectionsRingMap 𝒮).gradedRing
  let := (globalSectionsRingMap (veroneseGrading 𝒮 d)).gradedRing
  have hk' : (⟨y, hyV⟩ : veroneseSubring 𝒮 d) ∈ veroneseGrading 𝒮 d k := hk
  have h1 := (globalSectionsRingMap 𝒮).map_homogeneous (k * d) ⟨y, hk⟩
  have h2 := (globalSectionsRingMap (veroneseGrading 𝒮 d)).map_homogeneous k ⟨⟨y, hyV⟩, hk'⟩
  refine apply_component_eq_of_lof (a := n * d) (b := n) h1 h2
    (fun t => (veroneseTwistingSheafIso 𝒮 d hd n).hom.val.app (op ⊤)
      ((eqToHom (congrArg (twistingSheaf 𝒮) (Nat.cast_mul n d))).val.app (op ⊤) t))
    (fun t => Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
      (twistingSheaf (veroneseGrading 𝒮 d) n) ⊤ t)
    (by simp only [map_zero]) (map_zero _) (mul_left_inj' hd.ne') ?_
  intro _ hkn
  subst hkn
  exact veroneseTwistingSheafIso_degreeSection 𝒮 d hd k ⟨y, hyV⟩ hk

/-- **Tag 0B5J's isomorphisms are compatible with the graded ring map
`S → ⨁_{n ≥ 0} Γ(Proj, 𝒪(n))` of Tag 01MP.** For every element `a` of `S' = S⁽ᵈ⁾` and every
`n ≥ 0`, the degree-`nd` component of the image of `a` under the map of Tag 01MP on
`X = Proj S`, carried by the isomorphism `𝒪_X(nd) ≅ i^*𝒪_{X'}(n)` of assertion (2), is the
pullback of the degree-`n` component of the image of `a` under the map of Tag 01MP on
`X' = Proj S'`. -/
@[ega "II 8.14.13" "special case"]
public theorem veroneseGlobalSectionsRingMapCompatibility (d : ℕ) (hd : 0 < d) (n : ℕ)
    (a : veroneseSubring 𝒮 d) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := (globalSectionsRingMap 𝒮).gradedRing
    letI := (globalSectionsRingMap (veroneseGrading 𝒮 d)).gradedRing
    (veroneseTwistingSheafIso 𝒮 d hd n).hom.val.app (op ⊤)
        ((eqToHom (congrArg (twistingSheaf 𝒮) (Nat.cast_mul n d))).val.app (op ⊤)
          (DirectSum.component ℤ ℕ (twistGlobalSections 𝒮) (n * d)
            ((globalSectionsRingMap 𝒮).hom (a : S)))) =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
        (twistingSheaf (veroneseGrading 𝒮 d) n) ⊤
        (DirectSum.component ℤ ℕ (twistGlobalSections (veroneseGrading 𝒮 d)) n
          ((globalSectionsRingMap (veroneseGrading 𝒮 d)).hom a)) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := (globalSectionsRingMap 𝒮).gradedRing
  let := (globalSectionsRingMap (veroneseGrading 𝒮 d)).gradedRing
  let L : veroneseSubring 𝒮 d →+ _ :=
    ((veroneseTwistingSheafIso 𝒮 d hd n).hom.val.app (op ⊤)).hom.toAddMonoidHom.comp
      (((eqToHom (congrArg (twistingSheaf 𝒮) (Nat.cast_mul n d))).val.app
        (op ⊤)).hom.toAddMonoidHom.comp
        ((DirectSum.component ℤ ℕ (twistGlobalSections 𝒮) (n * d)).toAddMonoidHom.comp
          ((globalSectionsRingMap 𝒮).hom.toAddMonoidHom.comp
            (veroneseSubring 𝒮 d).subtype.toAddMonoidHom)))
  let R : veroneseSubring 𝒮 d →+ _ :=
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction
        (veroneseProjIso 𝒮 d hd).hom).unit.app
        (twistingSheaf (veroneseGrading 𝒮 d) n)) ⊤).hom.comp
      ((DirectSum.component ℤ ℕ (twistGlobalSections (veroneseGrading 𝒮 d)) n).toAddMonoidHom.comp
        (globalSectionsRingMap (veroneseGrading 𝒮 d)).hom.toAddMonoidHom)
  refine addMonoidHom_eq_of_mem_closure (L := L) (R := R)
    (fun _ => mem_veroneseSubring_iff 𝒮 d) (fun y hy hyV => ?_) a
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
  exact veroneseGlobalSectionsRingMapCompatibility_homogeneous 𝒮 d hd n k y hk hyV

end RingMap

end Stacks.Veronese

end
