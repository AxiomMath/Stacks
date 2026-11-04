module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseGlobalSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Veronese comparison and the map of Tag 01MR, for modules in any universe

Let `S` be a graded ring in `Type u`, `d ≥ 1`, `S' = S⁽ᵈ⁾`, `i : X = Proj S ≅ X' = Proj S'` the
Veronese isomorphism, and `M` a graded `S`-module whose carrier lies in an arbitrary universe
`Type v`, with `M' = M⁽ᵈ⁾`. The associated sheaves then have their sections in `max u v`, the
pullback `i^*` is `SheafOfModules.pullback.{max u v}`, and the canonical isomorphism of Tag 0B5J's
assertion (1) is `Stacks.Veronese.veroneseAssociatedSheafIso`.

This file proves the compatibility of these isomorphisms with the canonical map of graded
modules `M → ⨁ₙ Γ(Proj, M(n)~)` of Tag 01MR, whose formalization is stated for modules in any
universe: `veroneseGlobalSectionsModuleMapCompatibilityAny`. For modules in the universe of the
ring it is `Stacks.Veronese.veroneseGlobalSectionsModuleMapCompatibility`.

## References

* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory DirectSum TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections (degreeZeroToGlobalSections
  degreeZeroToGlobalSections_basicOpen)
open Stacks.GradedModule (shiftedGrading)

namespace Stacks.Veronese

attribute [local instance_reducible] TopCat.Sheaf
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] PresheafOfModules.presheaf SheafOfModules.toSheaf

universe u v w

section Generic

variable {X : TopCat.{u}} {𝒪 : TopCat.Sheaf RingCat X}

/-- **Two sections of a sheaf of modules agreeing on a basis are equal**, for sections in any
universe containing that of the space. -/
public theorem moduleSheafSection_ext_onBasisAny (F : SheafOfModules.{max u v} 𝒪)
    {ι : Type*} (U : ι → Opens X) (hU : Opens.IsBasis (Set.range U))
    {W : Opens X} (s t : F.val.obj (op W))
    (h : ∀ (a : ι) (hle : U a ≤ W),
      F.val.map (homOfLE hle).op s = F.val.map (homOfLE hle).op t) :
    s = t := by
  have hcover : W ≤ iSup (fun p : {a : ι // U a ≤ W} => U p.1) := by
    intro x hx
    rw [Opens.mem_iSup]
    obtain ⟨_, ⟨a, rfl⟩, hxV, hVW⟩ := Opens.isBasis_iff_nbhd.mp hU (show x ∈ W from hx)
    exact ⟨⟨a, hVW⟩, hxV⟩
  exact TopCat.Sheaf.eq_of_locally_eq' ((SheafOfModules.toSheaf 𝒪).obj F)
    (fun p : {a : ι // U a ≤ W} => U p.1) W (fun p => homOfLE p.2) hcover s t
    (fun p => h p.1 p.2)

/-- A morphism of sheaves of modules commutes with restriction, in any universe. -/
public theorem moduleSheafHom_app_restrictAny {A B : SheafOfModules.{max u v} 𝒪} (φ : A ⟶ B)
    {U V : Opens X} (hUV : V ≤ U) (s : A.val.obj (op U)) :
    (B.val.map (homOfLE hUV).op).hom ((φ.val.app (op U)).hom s) =
      (φ.val.app (op V)).hom ((A.val.map (homOfLE hUV).op).hom s) :=
  (congrArg (fun ψ => ModuleCat.Hom.hom ψ s) (φ.val.naturality (homOfLE hUV).op)).symm

end Generic

section Pullback

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The unit of the pullback of sheaves of modules with sections in `max u v`, on sections. -/
public abbrev pullbackUnitAny (G : SheafOfModules.{max u v} Y.ringCatSheaf) (U : Y.Opens)
    (s : G.val.obj (op U)) :
    ((SheafOfModules.pullback.{max u v} g.toRingCatSheafHom).obj G).val.obj (op (g ⁻¹ᵁ U)) :=
  ((SheafOfModules.pullbackPushforwardAdjunction.{max u v} g.toRingCatSheafHom).unit.app
    G).val.app (op U) s

/-- The unit of the pullback is natural. -/
public theorem pullbackUnitAny_naturality {G H : SheafOfModules.{max u v} Y.ringCatSheaf}
    (φ : G ⟶ H) (U : Y.Opens) (s : G.val.obj (op U)) :
    ((SheafOfModules.pullback.{max u v} g.toRingCatSheafHom).map φ).val.app (op (g ⁻¹ᵁ U))
        (pullbackUnitAny g G U s) = pullbackUnitAny g H U (φ.val.app (op U) s) :=
  (congrArg (fun ψ => (SheafOfModules.Hom.val ψ).app (op U) s)
    ((SheafOfModules.pullbackPushforwardAdjunction.{max u v}
      g.toRingCatSheafHom).unit.naturality φ)).symm

/-- The unit of the pullback commutes with restriction. -/
public theorem pullbackUnitAny_map (G : SheafOfModules.{max u v} Y.ringCatSheaf) {U V : Y.Opens}
    (hVU : V ≤ U) (s : G.val.obj (op U)) :
    pullbackUnitAny g G V (G.val.map (homOfLE hVU).op s) =
      ((SheafOfModules.pullback.{max u v} g.toRingCatSheafHom).obj G).val.map
        (homOfLE (show g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U from fun _ hz => hVU hz)).op
        (pullbackUnitAny g G U s) :=
  congrArg (fun ψ => ModuleCat.Hom.hom ψ s)
    (((SheafOfModules.pullbackPushforwardAdjunction.{max u v}
      g.toRingCatSheafHom).unit.app G).val.naturality (homOfLE hVU).op)

/-- Morphisms of sheaves of modules commute with transport along an equality of opens. -/
public theorem sheafOfModulesHom_app_castAny {F G : SheafOfModules.{max u v} X.ringCatSheaf}
    (φ : F ⟶ G) {U V : X.Opens} (h : U = V) (s : F.val.obj (op U)) :
    φ.val.app (op V) (h ▸ s) = h ▸ φ.val.app (op U) s := by
  cases h
  rfl

/-- Restricting from `⊤` is compatible with transport along an equality of opens. -/
public theorem val_map_top_castAny (F : SheafOfModules.{max u v} X.ringCatSheaf) {W V : X.Opens}
    (h : W = V) (s : F.val.obj (op ⊤)) :
    F.val.map (homOfLE (le_top : V ≤ ⊤)).op s =
      h ▸ F.val.map (homOfLE (le_top : W ≤ ⊤)).op s := by
  cases h
  rfl

end Pullback

variable {S : Type u} {σ : Type w} [CommRing S]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  {P : Type v} [AddCommGroup P] [Module S P] (𝒦 : ℤ → AddSubgroup P) [Decomposition 𝒦]
  [SetLike.GradedSMul 𝒮 𝒦]

/-- **Assertion (1) of Tag 0B5J read forwards on a chart, in any universe.** -/
public theorem veroneseAssociatedSheafIso_hom_standardOpen
    (d : ℕ) (hd : 0 < d) (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒦 d hd
    ∀ (hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e)
      (z : GradedModuleDegreeZeroLocalization
        (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒦 d) (veronesePower 𝒮 d f hf)),
    ((veroneseAssociatedSheafIso 𝒮 𝒦 d hd).hom.val.app (op (Proj.basicOpen 𝒮 f)))
        ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒦 hf he).symm
          (veroneseModuleAwayEquiv 𝒮 d 𝒦 f hf hd z)) =
      veroneseProjIso_basicOpen 𝒮 d hd f he hf ▸
        pullbackUnitAny (veroneseProjIso 𝒮 d hd).hom
          (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
            (veroneseModuleGrading 𝒮 𝒦 d))
          (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))
          ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
            (veroneseModuleGrading 𝒮 𝒦 d) hvf he).symm z) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒦 d hd
  intro hvf z
  exact (congrArg
      (fun t => ((veroneseAssociatedSheafIso 𝒮 𝒦 d hd).hom.val.app
        (.op (Proj.basicOpen 𝒮 f))) t)
      ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒦
          hf he).symm_apply_eq.mpr
        (veroneseAssociatedSheafIso_standardOpen 𝒮 𝒦 d hd f he hf z).symm)).trans
    (congrArg (fun φ => ModuleCat.Hom.hom ((SheafOfModules.Hom.val φ).app
        (op (Proj.basicOpen 𝒮 f))) _) (veroneseAssociatedSheafIso 𝒮 𝒦 d hd).inv_hom_id)

/-- The Veronese module comparison on a homogeneous fraction, in any universe. -/
public theorem veroneseModuleAwayEquiv_degreeZeroFractionAny (d : ℕ) (hd : 0 < d) (f : S)
    {e : ℕ} (hf : f ∈ 𝒮 e) (p : ℕ) (mb : veroneseSubmodule 𝒮 𝒦 d)
    (hmb : mb ∈ veroneseModuleGrading 𝒮 𝒦 d (p • (e : ℤ)))
    (hm : (mb : P) ∈ 𝒦 ((p * d) • (e : ℤ))) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒦 d hd
    ∀ hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e,
    veroneseModuleAwayEquiv 𝒮 d 𝒦 f hf hd
        (ProjectiveSpectrum.Proj.degreeZeroFraction (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 𝒦 d) hvf p mb hmb) =
      ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 𝒦 hf (p * d) (mb : P) hm := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒦 d hd
  intro hvf
  exact Subtype.ext (veroneseModuleAwayEquiv_mk 𝒮 d 𝒦 f hf hd p mb _ rfl)

/-- The restriction of the global section `m / 1` to a standard open, as a fraction with
exponent `k = 0`, in any universe. -/
public theorem degreeZeroToGlobalSections_restrictAny {A : Type u} {Q : Type v} {ς : Type*}
    [CommRing A] [AddCommGroup Q] [Module A Q] [SetLike ς A] [AddSubgroupClass ς A] (𝒜 : ℕ → ς)
    [GradedRing 𝒜] (ℒ : ℤ → AddSubgroup Q) [Decomposition ℒ] [SetLike.GradedSMul 𝒜 ℒ]
    {f : A} {c : ℕ} (hf : f ∈ 𝒜 c) (hc : 0 < c) (m : ℒ 0) (k : ℕ) (hk : k = 0)
    (hm : (m : Q) ∈ ℒ (k • (c : ℤ))) :
    (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒜 ℒ).val.map
        (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒜 f ≤ ⊤)).op
        (degreeZeroToGlobalSections 𝒜 ℒ m) =
      (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒜 ℒ hf hc).symm
        (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒜 ℒ hf k (m : Q) hm) := by
  subst hk
  exact (LinearEquiv.eq_symm_apply _).2 (degreeZeroToGlobalSections_basicOpen 𝒜 ℒ hf hc m)

/-- The sheaf map of a graded linear map carries the global section `m / 1` to `φ(m) / 1`, in
any universe. -/
public theorem associatedModuleSheafMap_degreeZeroToGlobalSectionsAny {A : Type u}
    {Q R : Type v} {ς τ υ : Type*} [CommRing A] [AddCommGroup Q] [Module A Q] [AddCommGroup R]
    [Module A R] [SetLike ς A] [AddSubgroupClass ς A] (𝒜 : ℕ → ς) [GradedRing 𝒜]
    [SetLike τ Q] [AddSubgroupClass τ Q] (ℒ : ℤ → τ) [Decomposition ℒ] [SetLike.GradedSMul 𝒜 ℒ]
    [SetLike υ R] [AddSubgroupClass υ R] (𝒬 : ℤ → υ) [Decomposition 𝒬] [SetLike.GradedSMul 𝒜 𝒬]
    (φ : Q →ₗ[A] R) (hφ : ∀ i (m : Q), m ∈ ℒ i → φ m ∈ 𝒬 i) (m : ℒ 0) :
    (associatedModuleSheafMap 𝒜 ℒ 𝒬 φ hφ).val.app (op ⊤) (degreeZeroToGlobalSections 𝒜 ℒ m) =
      degreeZeroToGlobalSections 𝒜 𝒬 ⟨φ m, hφ 0 m m.2⟩ :=
  Subtype.ext <| funext fun _ => LocalizedModule.map_mk _ _ _ _

/-- **Assertion (1) of Tag 0B5J on the global section `m / 1`, on one chart, in any
universe.** -/
public theorem veroneseAssociatedSheafIso_degreeZeroToGlobalSections_chart (d : ℕ) (hd : 0 < d)
    (mb : veroneseSubmodule 𝒮 𝒦 d) (hmb : mb ∈ veroneseModuleGrading 𝒮 𝒦 d 0)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒦 d hd
    (veroneseAssociatedSheafIso 𝒮 𝒦 d hd).hom.val.app (op (Proj.basicOpen 𝒮 f))
        ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒦).val.map
          (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒮 f ≤ ⊤)).op
          (degreeZeroToGlobalSections 𝒮 𝒦 ⟨(mb : P), by simpa using hmb⟩)) =
      ((SheafOfModules.pullback.{max u v} (veroneseProjIso 𝒮 d hd).hom.toRingCatSheafHom).obj
          (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
            (veroneseModuleGrading 𝒮 𝒦 d))).val.map
        (homOfLE (le_top : Proj.basicOpen 𝒮 f ≤ ⊤)).op
        (pullbackUnitAny (veroneseProjIso 𝒮 d hd).hom
          (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
            (veroneseModuleGrading 𝒮 𝒦 d)) ⊤
          (degreeZeroToGlobalSections (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒦 d)
            ⟨mb, hmb⟩)) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒦 d hd
  have hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e := veronesePower_mem 𝒮 d f hf
  have hmb' : mb ∈ veroneseModuleGrading 𝒮 𝒦 d ((0 : ℕ) • (e : ℤ)) := by simpa using hmb
  have hm0 : (mb : P) ∈ 𝒦 ((0 * d) • (e : ℤ)) := by
    simpa using (mem_veroneseModuleGrading 𝒮 𝒦).mp hmb
  refine Eq.trans (congrArg (fun t => (veroneseAssociatedSheafIso 𝒮 𝒦 d hd).hom.val.app
      (op (Proj.basicOpen 𝒮 f)) t)
    ((degreeZeroToGlobalSections_restrictAny 𝒮 𝒦 hf he _ (0 * d) (zero_mul d) hm0).trans
      (congrArg (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒦 hf he).symm
        (veroneseModuleAwayEquiv_degreeZeroFractionAny 𝒮 𝒦 d hd f hf 0 mb hmb' hm0
          hvf).symm))) ?_
  refine (veroneseAssociatedSheafIso_hom_standardOpen 𝒮 𝒦 d hd f he hf hvf _).trans ?_
  refine Eq.trans ?_ (val_map_top_castAny
    ((SheafOfModules.pullback.{max u v} (veroneseProjIso 𝒮 d hd).hom.toRingCatSheafHom).obj
      (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 𝒦 d)))
    (veroneseProjIso_basicOpen 𝒮 d hd f he hf) _).symm
  refine congrArg (fun t => Eq.rec (motive := fun W _ =>
      ((SheafOfModules.pullback.{max u v} (veroneseProjIso 𝒮 d hd).hom.toRingCatSheafHom).obj
        (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 𝒦 d))).val.obj (op W)) t
      (veroneseProjIso_basicOpen 𝒮 d hd f he hf)) ?_
  refine Eq.trans ?_ (pullbackUnitAny_map (veroneseProjIso 𝒮 d hd).hom
    (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒦 d)) le_top _)
  exact congrArg (pullbackUnitAny (veroneseProjIso 𝒮 d hd).hom _ _)
    (degreeZeroToGlobalSections_restrictAny (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒦 d)
      hvf he ⟨mb, hmb⟩ 0 rfl hmb').symm

/-- **Assertion (1) of Tag 0B5J on the global section `m / 1`, in any universe.** -/
public theorem veroneseAssociatedSheafIso_degreeZeroToGlobalSections (d : ℕ) (hd : 0 < d)
    (mb : veroneseSubmodule 𝒮 𝒦 d) (hmb : mb ∈ veroneseModuleGrading 𝒮 𝒦 d 0) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒦 d hd
    (veroneseAssociatedSheafIso 𝒮 𝒦 d hd).hom.val.app (op ⊤)
        (degreeZeroToGlobalSections 𝒮 𝒦 ⟨(mb : P), by simpa using hmb⟩) =
      pullbackUnitAny (veroneseProjIso 𝒮 d hd).hom
        (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
          (veroneseModuleGrading 𝒮 𝒦 d)) ⊤
        (degreeZeroToGlobalSections (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒦 d)
          ⟨mb, hmb⟩) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒦 d hd
  let ι := { a : S × ℕ // 0 < a.2 ∧ a.1 ∈ 𝒮 a.2 }
  let W : ι → Opens (ProjectiveSpectrum.top 𝒮) :=
    fun a => ProjectiveSpectrum.basicOpen 𝒮 a.1.1
  have heq : Set.range W = positiveBasicOpenSet (𝒮 := 𝒮) :=
    Set.ext fun _ => ⟨fun ⟨a, h⟩ => ⟨a.1.1, a.1.2, a.2.1, a.2.2, h.symm⟩,
      fun ⟨g, k, hk, hg, h⟩ => ⟨⟨(g, k), hk, hg⟩, h.symm⟩⟩
  have hW : Opens.IsBasis (Set.range W) := by
    rw [heq]
    exact positiveBasicOpenSet_isBasis 𝒮
  refine moduleSheafSection_ext_onBasisAny
    ((SheafOfModules.pullback.{max u v} (veroneseProjIso 𝒮 d hd).hom.toRingCatSheafHom).obj
      (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 𝒦 d))) W hW _ _ fun a hle =>
    (moduleSheafHom_app_restrictAny (veroneseAssociatedSheafIso 𝒮 𝒦 d hd).hom hle _).trans
      (veroneseAssociatedSheafIso_degreeZeroToGlobalSections_chart 𝒮 𝒦 d hd mb hmb
        a.1.1 a.2.1 a.2.2)

section ModuleMap

variable {M : Type v} [AddCommGroup M] [Module S M] (𝒨 : ℤ → AddSubgroup M) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- **Assertion (1) of Tag 0B5J at the shift `M(nd)`, for a module in any universe**: the
canonical isomorphism `M(nd)~ ≅ i^*(M(nd)'~)` followed by `M(nd)' = M'(n)`. -/
public noncomputable def veroneseShiftedSheafIsoAny (d : ℕ) (hd : 0 < d) (n : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (n * d)) ≅
      (SheafOfModules.pullback.{max u v} (veroneseProjIso 𝒮 d hd).hom.toRingCatSheafHom).obj
        (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
          (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n)) := by
  letI := veroneseGradingGradedRing 𝒮 d hd
  letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  exact (veroneseAssociatedSheafIso 𝒮 (shiftedGrading 𝒨 (n * d)) d hd).trans
    ((SheafOfModules.pullback.{max u v} (veroneseProjIso 𝒮 d hd).hom.toRingCatSheafHom).mapIso
      (veroneseShiftedSheafIso 𝒮 𝒨 d hd n))

/-- `veroneseShiftedSheafIsoAny` on the global section `m / 1`. -/
public theorem veroneseShiftedSheafIsoAny_degreeZeroToGlobalSections (d : ℕ) (hd : 0 < d)
    (n : ℤ) (m : M) (hm : m ∈ 𝒨 (n * d)) (hmV : m ∈ veroneseSubmodule 𝒮 𝒨 d) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    (veroneseShiftedSheafIsoAny 𝒮 𝒨 d hd n).hom.val.app (op ⊤)
        (degreeZeroToGlobalSections 𝒮 (shiftedGrading 𝒨 (n * d))
          ⟨m, by simpa only [shiftedGrading, zero_add] using hm⟩) =
      pullbackUnitAny (veroneseProjIso 𝒮 d hd).hom
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
    show m ∈ 𝒨 (0 * (d : ℤ) + n * d)
    simpa only [zero_mul, zero_add] using hm
  refine (congrArg (fun t => (((SheafOfModules.pullback.{max u v}
      (veroneseProjIso 𝒮 d hd).hom.toRingCatSheafHom).map
      (veroneseShiftedSheafIso 𝒮 𝒨 d hd n).hom).val.app (op ⊤)) t)
    (veroneseAssociatedSheafIso_degreeZeroToGlobalSections 𝒮
      (shiftedGrading 𝒨 (n * d)) d hd mb hmb)).trans ?_
  refine (pullbackUnitAny_naturality (veroneseProjIso 𝒮 d hd).hom
    (veroneseShiftedSheafIso 𝒮 𝒨 d hd n).hom ⊤ _).trans ?_
  exact congrArg (pullbackUnitAny (veroneseProjIso 𝒮 d hd).hom _ ⊤)
    (associatedModuleSheafMap_degreeZeroToGlobalSectionsAny (veroneseGrading 𝒮 d) _ _
      (veroneseModuleShiftEquiv 𝒮 𝒨 d n).toLinearMap (veroneseModuleShiftEquiv_mem 𝒮 𝒨 d n)
      ⟨mb, hmb⟩)

/-- The compatibility with Tag 01MR on a homogeneous element of degree `kd`, in any
universe. -/
public theorem veroneseGlobalSectionsModuleMapCompatibilityAny_homogeneous (d : ℕ) (hd : 0 < d)
    (n k : ℤ) (y : M) (hk : y ∈ 𝒨 (k * d)) (hyV : y ∈ veroneseSubmodule 𝒮 𝒨 d) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    (veroneseShiftedSheafIsoAny 𝒮 𝒨 d hd n).hom.val.app (op ⊤)
        (DirectSum.component ℤ ℤ _ (n * d)
          ((Stacks.AlgebraicGeometry.ProjShiftedSections.globalSectionsModuleMap 𝒮 𝒨).hom y)) =
      pullbackUnitAny (veroneseProjIso 𝒮 d hd).hom
        (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
          (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n)) ⊤
        (DirectSum.component ℤ ℤ _ n
          ((Stacks.AlgebraicGeometry.ProjShiftedSections.globalSectionsModuleMap
            (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d)).hom ⟨y, hyV⟩)) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  have hk' : (⟨y, hyV⟩ : veroneseSubmodule 𝒮 𝒨 d) ∈ veroneseModuleGrading 𝒮 𝒨 d k := hk
  let β₁ := Stacks.AlgebraicGeometry.ProjShiftedSections.shiftedSectionsComponent 𝒮 𝒨
  let β₂ := Stacks.AlgebraicGeometry.ProjShiftedSections.shiftedSectionsComponent
    (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d)
  have c1 := congrArg (DirectSum.component ℤ ℤ β₁ (n * d))
    ((Stacks.AlgebraicGeometry.ProjShiftedSections.globalSectionsModuleMap 𝒮 𝒨).map_homogeneous
      (k * d) ⟨y, hk⟩)
  have c2 := congrArg (DirectSum.component ℤ ℤ β₂ n)
    ((Stacks.AlgebraicGeometry.ProjShiftedSections.globalSectionsModuleMap
      (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d)).map_homogeneous k ⟨⟨y, hyV⟩, hk'⟩)
  let s₁ := degreeZeroToGlobalSections 𝒮 (shiftedGrading 𝒨 (k * d))
    ⟨y, by simpa only [shiftedGrading, zero_add] using hk⟩
  let s₂ := degreeZeroToGlobalSections (veroneseGrading 𝒮 d)
    (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) k)
    ⟨⟨y, hyV⟩, by simpa only [shiftedGrading, zero_add] using hk'⟩
  by_cases hkn : k = n
  · subst hkn
    refine (congrArg (fun t => (veroneseShiftedSheafIsoAny 𝒮 𝒨 d hd k).hom.val.app (op ⊤) t)
      (c1.trans (DirectSum.component.lof_self ℤ (M := β₁) (k * d) s₁))).trans
      ((veroneseShiftedSheafIsoAny_degreeZeroToGlobalSections 𝒮 𝒨 d hd k y hk hyV).trans ?_)
    exact congrArg (pullbackUnitAny (veroneseProjIso 𝒮 d hd).hom _ ⊤)
      (c2.trans (DirectSum.component.lof_self ℤ (M := β₂) k s₂)).symm
  · have hkn' : k * (d : ℤ) ≠ n * d := fun h =>
      hkn (mul_right_cancel₀ (by exact_mod_cast hd.ne') h)
    have e1 := (DirectSum.component.of ℤ (M := β₁) (n * d) (k * d) s₁).trans (dite_eq_right hkn')
    have e2 := (DirectSum.component.of ℤ (M := β₂) n k s₂).trans (dite_eq_right hkn)
    refine (congrArg (fun t => (veroneseShiftedSheafIsoAny 𝒮 𝒨 d hd n).hom.val.app (op ⊤) t)
      (c1.trans e1)).trans ((map_zero _).trans ?_)
    exact ((congrArg (pullbackUnitAny (veroneseProjIso 𝒮 d hd).hom _ ⊤) (c2.trans e2)).trans
      (map_zero _)).symm

/-- **Tag 0B5J's isomorphisms are compatible with the map `M → ⨁ₙ Γ(Proj, M(n)~)` of Tag 01MR,
for a graded module in any universe.** For every element `m` of `M' = M⁽ᵈ⁾` and every integer
`n`, the degree-`nd` component of the image of `m` under the map of Tag 01MR on `X = Proj S`,
carried by `M(nd)~ ≅ i^*(M'(n)~)`, is the pullback of the degree-`n` component of the image of
`m` under the map of Tag 01MR on `X' = Proj S'`. -/
@[ega "II 8.14.13" "special case"]
public theorem veroneseGlobalSectionsModuleMapCompatibilityAny (d : ℕ) (hd : 0 < d) (n : ℤ)
    (m : veroneseSubmodule 𝒮 𝒨 d) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    (veroneseShiftedSheafIsoAny 𝒮 𝒨 d hd n).hom.val.app (op ⊤)
        (DirectSum.component ℤ ℤ _ (n * d)
          ((Stacks.AlgebraicGeometry.ProjShiftedSections.globalSectionsModuleMap 𝒮 𝒨).hom
            (m : M))) =
      pullbackUnitAny (veroneseProjIso 𝒮 d hd).hom
        (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
          (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n)) ⊤
        (DirectSum.component ℤ ℤ _ n
          ((Stacks.AlgebraicGeometry.ProjShiftedSections.globalSectionsModuleMap
            (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d)).hom m)) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  let L : veroneseSubmodule 𝒮 𝒨 d →+ _ :=
    ((veroneseShiftedSheafIsoAny 𝒮 𝒨 d hd n).hom.val.app (op ⊤)).hom.toAddMonoidHom.comp
      ((DirectSum.component ℤ ℤ
        (Stacks.AlgebraicGeometry.ProjShiftedSections.shiftedSectionsComponent 𝒮 𝒨)
        (n * d)).toAddMonoidHom.comp
        ((Stacks.AlgebraicGeometry.ProjShiftedSections.globalSectionsModuleMap 𝒮
          𝒨).hom.toAddMonoidHom.comp (veroneseSubmodule 𝒮 𝒨 d).subtype.toAddMonoidHom))
  let R : veroneseSubmodule 𝒮 𝒨 d →+ _ :=
    (((SheafOfModules.pullbackPushforwardAdjunction.{max u v}
        (veroneseProjIso 𝒮 d hd).hom.toRingCatSheafHom).unit.app
        (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
          (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n))).val.app
          (op ⊤)).hom.toAddMonoidHom.comp
      ((DirectSum.component ℤ ℤ
        (Stacks.AlgebraicGeometry.ProjShiftedSections.shiftedSectionsComponent
          (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d)) n).toAddMonoidHom.comp
        (Stacks.AlgebraicGeometry.ProjShiftedSections.globalSectionsModuleMap
          (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d)).hom.toAddMonoidHom)
  have key : ∀ x (hxc : x ∈ AddSubgroup.closure (veroneseModuleSet 𝒨 d))
      (hxV : x ∈ veroneseSubmodule 𝒮 𝒨 d), L ⟨x, hxV⟩ = R ⟨x, hxV⟩ := by
    intro x hxc
    induction hxc using AddSubgroup.closure_induction with
    | mem y hy =>
      intro hyV
      obtain ⟨k, hk⟩ := (mem_veroneseModuleSet_iff 𝒨).mp hy
      exact veroneseGlobalSectionsModuleMapCompatibilityAny_homogeneous 𝒮 𝒨 d hd n k y hk hyV
    | zero =>
      intro hzV
      exact (map_zero L).trans (map_zero R).symm
    | add a b ha' hb' ha hb =>
      intro habV
      have haV := (mem_veroneseSubmodule_iff 𝒮 𝒨 d).mpr ha'
      have hbV := (mem_veroneseSubmodule_iff 𝒮 𝒨 d).mpr hb'
      have hab : (⟨a + b, habV⟩ : veroneseSubmodule 𝒮 𝒨 d) = ⟨a, haV⟩ + ⟨b, hbV⟩ := rfl
      exact (congrArg L hab).trans ((map_add L _ _).trans
        ((congrArg₂ (· + ·) (ha haV) (hb hbV)).trans ((map_add R _ _).symm.trans
          (congrArg R hab.symm))))
    | neg a ha' ha =>
      intro haV'
      have haV := (mem_veroneseSubmodule_iff 𝒮 𝒨 d).mpr ha'
      have hna : (⟨-a, haV'⟩ : veroneseSubmodule 𝒮 𝒨 d) = -⟨a, haV⟩ := rfl
      exact (congrArg L hna).trans ((map_neg L _).trans ((congrArg Neg.neg (ha haV)).trans
        ((map_neg R _).symm.trans (congrArg R hna.symm))))
  exact key m.1 ((mem_veroneseSubmodule_iff 𝒮 𝒨 d).mp m.2) m.2

end ModuleMap

end Stacks.Veronese

end
