module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.Topology.NoetherianSpace
public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.NowhereDense.Defs
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.NowhereDense
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalGeneration.ZeroDimensionalSupport
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Embedded
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.DimensionOne
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulay
public import StacksFrontier.Topology.Dimension.Equidimensional
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks
public import StacksFrontier.Topology.Sheaves.Modules.Support
public import StacksFrontier.Topology.Sheaves.Modules.SupportSection
public import StacksFrontier.Topology.Sheaves.Modules.SupportedSectionsSheaf
import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.BaseChange

/-!
# Automatic properties of proper curves

Let `X` be a proper scheme of dimension one over a field `k`. If every global regular function
on `X` comes from `k`, then `X` is connected, Cohen-Macaulay and equidimensional.

## Main results

* `AlgebraicGeometry.connectedSpace_of_isIso_globalSections` proves connectedness.
* `AlgebraicGeometry.isCohenMacaulay_of_isIso_globalSections_of_dimension_one` proves the
  Cohen-Macaulay property.
* `AlgebraicGeometry.equidimensional_of_isIso_globalSections_of_dimension_one` proves
  equidimensionality.

## Implementation notes

The equality `H^0(X, O_X) = k` is expressed canonically by requiring the homomorphism from `k`
to `Gamma(X, top)` induced by the structure morphism to be an isomorphism. The standard
identification of the global sections of `Spec k` with `k` is included explicitly in this map.
Connectedness does not use properness or the dimension hypothesis, so that conclusion is stated
under the weaker hypotheses it needs. The Cohen-Macaulay and equidimensional conclusions retain
the properness and dimension-one hypotheses.

## References

* [Stacks Project, Tag 0BY5](https://stacks.math.columbia.edu/tag/0BY5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.CoherentSubquotients

private theorem one_ne_zero_sections_of_nonempty_open (X : Scheme.{u})
    (U : X.Opens) (hU : (U : Set X).Nonempty) :
    (1 : Γ(X, U)) ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ := hU
  have h' := congrArg (fun s : Γ(X, U) => X.presheaf.germ U x hx s) h
  have hzero : (1 : X.presheaf.stalk x) = 0 := by simpa only [map_one, map_zero] using h'
  exact one_ne_zero hzero

private theorem connectedSpace_of_globalSections_no_idempotents
    (X : Scheme.{u}) [Nonempty X]
    (hidem : ∀ s : Γ(X, ⊤), s * s = s → s = 0 ∨ s = 1) :
    ConnectedSpace X := by
  rw [connectedSpace_iff_clopen]
  refine ⟨inferInstance, ?_⟩
  intro U hU
  let Uo : X.Opens := ⟨U, hU.isOpen⟩
  let V : X.Opens := ⟨Uᶜ, hU.isClosed.isOpen_compl⟩
  let W : Bool → X.Opens := fun b => if b then V else Uo
  have hcover : (⊤ : X.Opens) ≤ iSup W := by
    rw [SetLike.le_def]
    intro x hx
    by_cases hxU : x ∈ U
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨false, by simpa [W, Uo] using hxU⟩
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨true, by simpa [W, V] using hxU⟩
  let sf : (b : Bool) → Γ(X, W b) := fun b => if b then 0 else 1
  have hsub : ∀ i j, i ≠ j → Subsingleton Γ(X, W i ⊓ W j) := by
    intro i j hij
    have h : W i ⊓ W j = ⊥ := by
      apply TopologicalSpace.Opens.ext
      cases i <;> cases j <;> simp_all [W, Uo, V]
    rw [h]
    exact inferInstance
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf W sf := by
    intro i j
    cases i <;> cases j
    · simp [W, sf]
    · exact (hsub false true (by simp)).elim _ _
    · exact (hsub true false (by simp)).elim _ _
    · simp [W, sf]
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing'
    (U := W) (V := ⊤) (iUV := fun i => homOfLE (le_top)) hcover sf hcompat
  have hs_idem : s * s = s := by
    apply X.sheaf.eq_of_locally_eq' W ⊤ (fun _ => homOfLE (le_top)) hcover
    intro b
    rw [map_mul, hs b]
    cases b
    · exact one_mul _
    · exact zero_mul _
  rcases hidem s hs_idem with hs0 | hs1
  · left
    ext x
    constructor
    · intro hx
      have hone : (1 : Γ(X, Uo)) = 0 := by
        calc
          1 = X.presheaf.map (homOfLE (le_top : Uo ≤ ⊤)).op s := (hs false).symm
          _ = 0 := by simp [hs0]
      exact False.elim <| one_ne_zero_sections_of_nonempty_open X Uo ⟨x, hx⟩ hone
    · intro hx
      exact hx.elim
  · right
    ext x
    constructor
    · intro _
      trivial
    · intro _
      by_contra hxU
      have hzero : (0 : Γ(X, V)) = 1 := by
        calc
          0 = X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s := (hs true).symm
          _ = 1 := by simp [hs1]
      have hxV : x ∈ (V : Set X) := by simpa [V] using hxU
      exact one_ne_zero_sections_of_nonempty_open X V ⟨x, hxV⟩ hzero.symm

private theorem topologicalKrullDim_le_zero_of_nowhereDense_closed
    (X : Type u) [TopologicalSpace X] [NoetherianSpace X]
    (hX : topologicalKrullDim X ≤ 1) {S : Set X}
    (hSclosed : IsClosed S) (hSnd : IsNowhereDense S) :
    topologicalKrullDim S ≤ 0 := by
  unfold topologicalKrullDim
  rw [Order.krullDim_nonpos_iff_forall_isMax]
  intro A
  by_contra hAmax
  obtain ⟨B, hAB⟩ := not_isMax_iff.mp hAmax
  let incl : S → X := Subtype.val
  let hIncl : Topology.IsInducing incl := Topology.IsInducing.subtypeVal
  let mA := IrreducibleCloseds.map incl hIncl.continuous A
  let mB := IrreducibleCloseds.map incl hIncl.continuous B
  have hmAB : mA < mB :=
    (IrreducibleCloseds.map_strictMono_of_isInducing hIncl) hAB
  have hXle : Order.krullDim (IrreducibleCloseds X) ≤ 1 := by
    change topologicalKrullDim X ≤ 1
    exact hX
  have hmBmax : IsMax mB := by
    rcases (Order.krullDim_le_one_iff.mp hXle) mB with hmin | hmax
    · exact False.elim <| (isMin_iff_forall_not_lt.mp hmin) mA hmAB
    · exact hmax
  have hmBsub : (mB : Set X) ⊆ S := by
    change closure (incl '' (B : Set S)) ⊆ S
    apply closure_minimal _ hSclosed
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  have hmBcomp : (mB : Set X) ∈ irreducibleComponents X := by
    rw [irreducibleComponents]
    refine ⟨mB.isIrreducible, ?_⟩
    intro T hT hTB
    let CT : IrreducibleCloseds X := ⟨closure T, hT.closure, isClosed_closure⟩
    have hBTC : mB ≤ CT := by
      change (mB : Set X) ⊆ closure T
      exact hTB.trans subset_closure
    have hCTB : CT ≤ mB := hmBmax hBTC
    exact Set.Subset.trans subset_closure hCTB
  obtain ⟨U, hUopen, hUne, hUS⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent (mB : Set X) hmBcomp
  have hInonempty : (interior S).Nonempty := hUne.mono (interior_maximal (hUS.trans hmBsub) hUopen)
  change interior (closure S) = ∅ at hSnd
  rw [hSclosed.closure_eq] at hSnd
  obtain ⟨x, hx⟩ := hInonempty
  rw [hSnd] at hx
  exact hx.elim

/-- A space of Krull dimension one has no zero-dimensional full subspace. -/
private theorem false_of_topologicalKrullDim_univ_le_zero {X : Type u} [TopologicalSpace X]
    (hX : topologicalKrullDim X = 1) (h : topologicalKrullDim (Set.univ : Set X) ≤ 0) :
    False := by
  rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph, hX] at h
  norm_num at h

private noncomputable def structureModuleSheaf (X : Scheme.{u}) :
    RingedSpace.ModuleSheaf X.toRingedSpace :=
  ⟨(SheafOfModules.unit X.ringCatSheaf).val,
    (SheafOfModules.unit X.ringCatSheaf).isSheaf⟩

private lemma sections_eq_of_eval_top_eq {X : Scheme.{u}} (L : X.Modules)
    (a b : L.sections) (h : a.eval (op ⊤) = b.eval (op ⊤)) : a = b := by
  apply PresheafOfModules.sections_ext
  intro U
  have ha := a.property (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  have hb := b.property (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  change L.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op
      (a.eval (op ⊤)) = a.eval U at ha
  change L.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op
      (b.eval (op ⊤)) = b.eval U at hb
  change a.eval U = b.eval U
  rw [← ha, ← hb]
  exact congrArg (L.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op) h

private theorem structureModuleSheaf_support_eq_univ (X : Scheme.{u}) :
    (structureModuleSheaf X).supp = Set.univ := by
  let M := structureModuleSheaf X
  ext x
  rw [RingedSpace.ModuleSheaf.supp]
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  change ∃ a : M.abPresheaf.stalk x, a ≠ 0
  refine ⟨M.sectionGerm ⊤ x (by simp) (1 : Γ(X, ⊤)), ?_⟩
  intro hz
  obtain ⟨V, hxV, i, hi⟩ :=
    (M.sectionGerm_eq_zero_iff ⊤ x (by simp) (1 : Γ(X, ⊤))).mp hz
  have hzero : (1 : Γ(X, V)) = 0 := by
    have hmap : M.toPresheaf.map i.op (1 : Γ(X, ⊤)) = (1 : Γ(X, V)) := by
      simp only [M, structureModuleSheaf, SheafOfModules.unit]
      exact PresheafOfModules.unit_map_one _ _
    rw [hmap] at hi
    exact hi
  exact one_ne_zero_sections_of_nonempty_open X V ⟨x, hxV⟩ hzero

private noncomputable def subtypeHomeomorphOfEqUniv {X : Type u}
    [TopologicalSpace X] {S : Set X} (hS : S = Set.univ) : ↥S ≃ₜ X := by
  have hmem : ∀ x : X, x ∈ S := by intro x; rw [hS]; trivial
  let e : ↥S ≃ X :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, hmem x⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun _ => rfl }
  refine Homeomorph.mk e continuous_subtype_val ?_
  change Continuous (fun x : X => e.symm x)
  exact continuous_id.subtype_mk hmem

private theorem subobject_support_dim_le_zero_of_nowhereDense
    {X : Scheme.{u}} [NoetherianSpace X]
    (hX : topologicalKrullDim X ≤ 1) (F : X.Modules) (K : Subobject F)
    (hK : IsNowhereDenseCoherentSubobject F K)
    (hFsupp : (⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf X.toRingedSpace).supp =
      Set.univ) :
    topologicalKrullDim
      ((⟨(K : X.Modules).val, (K : X.Modules).isSheaf⟩ :
        RingedSpace.ModuleSheaf X.toRingedSpace).supp) ≤ 0 := by
  let FM : RingedSpace.ModuleSheaf X.toRingedSpace := ⟨F.val, F.isSheaf⟩
  let KM : RingedSpace.ModuleSheaf X.toRingedSpace :=
    ⟨(K : X.Modules).val, (K : X.Modules).isSheaf⟩
  let S := KM.supp
  let T : Set (↥FM.supp) := {x | (x : X) ∈ S}
  have hT : IsNowhereDense T := by
    change IsNowhereDense {x : ↥FM.supp | (x : X) ∈ KM.supp}
    exact hK.2
  let e : ↥FM.supp ≃ₜ X := subtypeHomeomorphOfEqUniv hFsupp
  have heq : e '' T = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, by rw [hFsupp]; trivial⟩, hx, rfl⟩
  have hSnd : IsNowhereDense S := by
    change interior (closure S) = ∅
    rw [← heq, ← e.image_closure, ← e.image_interior]
    simpa using congrArg (fun A : Set (↥FM.supp) => e '' A) hT
  have hCnd : IsNowhereDense (closure S) := by
    change interior (closure (closure S)) = ∅
    rw [closure_closure]
    exact hSnd
  have hCdim : topologicalKrullDim (closure S) ≤ 0 :=
    topologicalKrullDim_le_zero_of_nowhereDense_closed X hX isClosed_closure hCnd
  let inc : ↥S → ↥(closure S) := fun x => ⟨x.1, subset_closure x.2⟩
  have hcomp : Topology.IsInducing (Subtype.val ∘ inc) := by
    change Topology.IsInducing (fun x : ↥S => x.1)
    exact Topology.IsInducing.subtypeVal
  have hinc : Topology.IsInducing inc :=
    (Topology.IsInducing.of_comp_iff
      (Topology.IsInducing.subtypeVal (t := closure S))).mp hcomp
  calc
    topologicalKrullDim S ≤ topologicalKrullDim (closure S) :=
      hinc.topologicalKrullDim_le
    _ ≤ 0 := hCdim

private theorem moduleSheaf_supp_eq_sheafOfModules_supp {X : Scheme.{u}}
    (F : X.Modules) :
    (⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf X.toRingedSpace).supp =
      SheafOfModules.supp F := by
  simpa [SheafOfModules.moduleSheafOfModules] using
    (SheafOfModules.supp_eq_moduleSheaf_supp F)

private theorem associatedPrimeStacks_subset_of_injective
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) (hφ : Function.Injective φ)
    {p : Ideal R} (hp : IsAssociatedPrimeStacks R M p) :
    IsAssociatedPrimeStacks R N p := by
  rcases hp with ⟨hp, m, hm⟩
  refine ⟨hp, φ m, ?_⟩
  ext r
  rw [Submodule.mem_colon_span_singleton, Submodule.mem_bot, ← map_smul,
    map_eq_zero_iff φ hφ]
  rw [← hm, Submodule.mem_colon_span_singleton]
  simp only [Submodule.mem_bot]

theorem associatedPoints_subset_of_moduleIso {X : Scheme.{u}} {F G : X.Modules}
    (e : F ≅ G) : Stacks.Divisors.associatedPoints F ⊆ Stacks.Divisors.associatedPoints G := by
  intro x hx
  rw [Stacks.Divisors.mem_associatedPoints_iff] at hx ⊢
  simp only [Stacks.Divisors.IsAssociatedPoint] at hx ⊢
  change IsAssociatedPrimeStacks _ (OXModule.stalk F x) _ at hx
  change IsAssociatedPrimeStacks _ (OXModule.stalk G x) _
  have : IsIso ((SheafOfModules.forget X.ringCatSheaf).map e.hom) :=
    Functor.map_isIso _ e.hom
  have : Mono e.hom.val := by
    change Mono ((SheafOfModules.forget X.ringCatSheaf).map e.hom)
    infer_instance
  have hmono : Mono ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map e.hom.val) :=
    Functor.map_mono _ e.hom.val
  exact associatedPrimeStacks_subset_of_injective
    (OXModule.stalkLinearMap F G e.hom x)
    (OXModule.inj_of_mono_val F G e.hom hmono x) hx

private theorem hasNoEmbeddedAssociatedPoints_of_moduleIso {X : Scheme.{u}}
    {F G : X.Modules} (e : F ≅ G)
    (hF : HasNoEmbeddedAssociatedPoints F) :
    HasNoEmbeddedAssociatedPoints G := by
  have hp := associatedPoints_eq_of_moduleIso e
  intro x ⟨hx, y, hy, hspec, hne⟩
  apply hF x
  refine ⟨?_, y, ?_, hspec, hne⟩
  · rw [← Stacks.Divisors.mem_associatedPoints_iff, hp]
    exact hx
  · rw [← Stacks.Divisors.mem_associatedPoints_iff, hp]
    exact hy

private theorem structureSection_unit_support_eq_univ (X : Scheme.{u})
    (s t : Γ(X, ⊤)) (hst : s * t = 1) :
    (structureModuleSheaf X).suppSection ⊤ s = Set.univ := by
  ext x
  change (∃ hx : x ∈ (⊤ : X.Opens),
    (structureModuleSheaf X).sectionGerm ⊤ x hx s ≠ 0) ↔ True
  simp only [iff_true]
  refine ⟨by simp, ?_⟩
  intro hz
  let R := X.toRingedSpace.presheafRing
  let hx : x ∈ (⊤ : X.Opens) := by simp
  obtain ⟨V, hxV, i, hsi⟩ :=
    ((structureModuleSheaf X).sectionGerm_eq_zero_iff ⊤ x hx s).mp hz
  have hsir : (R.map i.op).hom s = 0 := by
    change (R.map i.op).hom s = 0 at hsi
    exact hsi
  have hstV := congrArg (fun a : Γ(X, ⊤) => (R.map i.op).hom a) hst
  have hmul : (R.map i.op).hom (s * t) =
      (R.map i.op).hom s * (R.map i.op).hom t := (R.map i.op).hom.map_mul s t
  have hone : (R.map i.op).hom (1 : Γ(X, ⊤)) = 1 := (R.map i.op).hom.map_one
  rw [hmul, hone, hsir] at hstV
  rw [zero_mul] at hstV
  exact one_ne_zero_sections_of_nonempty_open X V ⟨x, hxV⟩ hstV.symm

private theorem scheme_unitHomEquiv_comp_apply {X : Scheme.{u}} {M N : X.Modules}
    (f : SheafOfModules.unit X.ringCatSheaf ⟶ M) (p : M ⟶ N) :
    N.unitHomEquiv (f ≫ p) = SheafOfModules.sectionsMap p (M.unitHomEquiv f) := by
  rfl

-- The additional imports introduce an alternative quiver instance. Keep the morphism
-- binders in the public statements elaborated exactly as in the statement of Tag 0BY5.
/-- **Stacks Project, Tag 0BY5.** A scheme over a field whose only global regular functions
are constants is connected. -/
@[stacks 0BY5 "connectedness", sga "3 VIB 12.3" "connectedness of N"]
theorem connectedSpace_of_isIso_globalSections
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] :
    ConnectedSpace X := by
  have : Nonempty X := by
    by_contra hne
    let : IsEmpty X := not_nonempty_iff.mp hne
    have htop : (⊤ : X.Opens) = ⊥ := by
      apply TopologicalSpace.Opens.ext
      ext x
      exact isEmptyElim x
    have : Subsingleton (Γ(X, ⊤)) := by
      rw [htop]
      infer_instance
    let g := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop
    let φ : k →+* Γ(X, ⊤) := g.hom
    have hφ : φ 1 = φ 0 := Subsingleton.elim _ _
    have h10 : (1 : k) = 0 := by
      have hinj : Function.Injective φ := (ConcreteCategory.bijective_of_isIso g).1
      apply hinj
      simpa using hφ
    exact one_ne_zero h10
  apply connectedSpace_of_globalSections_no_idempotents X
  intro s hs
  let φ : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  have hbij := ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)
  have hφinj : Function.Injective φ := hbij.1
  obtain ⟨a, hφa⟩ := hbij.2 s
  have ha : a * a = a := by
    apply hφinj
    rw [map_mul, hφa, hs]
  have hfactor : a * (a - 1) = 0 := by
    calc
      a * (a - 1) = a * a - a := by ring
      _ = 0 := by rw [ha]; ring
  rcases mul_eq_zero.mp hfactor with ha0 | ha1
  · left
    calc
      s = φ a := hφa.symm
      _ = φ 0 := by rw [ha0]
      _ = 0 := map_zero φ
  · right
    have haone : a = 1 := sub_eq_zero.mp ha1
    calc
      s = φ a := hφa.symm
      _ = φ 1 := by rw [haone]
      _ = 1 := map_one φ

-- The sheaf argument repeatedly elaborates across the scheme-module and sheaf-module APIs.
/-- **Stacks Project, Tag 0BY5.** A proper one-dimensional scheme over a field whose only
global regular functions are constants is Cohen–Macaulay. -/
@[stacks 0BY5 "Cohen–Macaulayness"]
theorem isCohenMacaulay_of_isIso_globalSections_of_dimension_one
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] :
    IsCohenMacaulay X := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : AlgebraicGeometry.IsNoetherian X := AlgebraicGeometry.IsNoetherian.mk
  let : NoetherianSpace X := inferInstance
  have hdimle : topologicalKrullDim X ≤ 1 := by rw [hdim]
  let R : TopCat.Sheaf RingCat.{u} X := X.ringCatSheaf
  let F : X.Modules := SheafOfModules.unit R
  let : F.IsCoherent := Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  obtain ⟨K, hK, hmax⟩ :=
    exists_greatest_isNowhereDenseCoherentSubobject F
  let Kobj : X.Modules := Subobject.underlying.obj K
  let : Kobj.IsCoherent := hK.1
  have hFsupp : (⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf X.toRingedSpace).supp =
      Set.univ := by
    exact structureModuleSheaf_support_eq_univ X
  have hKdim := subobject_support_dim_le_zero_of_nowhereDense hdimle F K hK hFsupp
  have hKdimGen : topologicalKrullDim (SheafOfModules.supp Kobj) ≤ 0 := by
    rw [← moduleSheaf_supp_eq_sheafOfModules_supp Kobj]
    simpa [Kobj] using hKdim
  obtain ⟨gs⟩ := nonempty_generatingSections_of_support_dim_le_zero
    Kobj hKdimGen
  let FM : RingedSpace.ModuleSheaf X.toRingedSpace := ⟨F.val, F.isSheaf⟩
  let KM : RingedSpace.ModuleSheaf X.toRingedSpace := ⟨Kobj.val, Kobj.isSheaf⟩
  let kmap : PresheafOfModules.Hom KM.toPresheaf FM.toPresheaf := K.arrow.val
  have hsection0 (i : gs.I) :
      SheafOfModules.sectionsMap K.arrow (gs.s i) =
        F.unitHomEquiv (0 : SheafOfModules.unit R ⟶ F) := by
    let t : Γ(X, ⊤) := (SheafOfModules.sectionsMap K.arrow (gs.s i)).eval (op ⊤)
    let s : ↑(KM.toPresheaf.obj (op (⊤ : X.Opens))) := (gs.s i).eval (op ⊤)
    have htopzero : t = 0 := by
      let g := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop
      let φ : k →+* Γ(X, ⊤) := g.hom
      obtain ⟨a, hta⟩ := (ConcreteCategory.bijective_of_isIso g).2 t
      by_contra ht
      have ha : a ≠ 0 := by
        intro ha
        apply ht
        calc
          t = φ a := hta.symm
          _ = 0 := by rw [ha]; simp
      have hunit : φ a * φ a⁻¹ = 1 := by simp [← map_mul, ha]
      have hfull : FM.suppSection ⊤ t = Set.univ := by
        change (structureModuleSheaf X).suppSection ⊤ t = Set.univ
        rw [← hta]
        exact structureSection_unit_support_eq_univ X (φ a) (φ a⁻¹) hunit
      have hmaptop : kmap.app (op ⊤) s = t := by rfl
      have hmap : FM.suppSection ⊤ t ⊆ KM.suppSection ⊤ s := by
        rw [← hmaptop]
        exact KM.suppSection_map_subset FM kmap ⊤ s
      have hsection_le : KM.suppSection ⊤ s ⊆ KM.supp := by
        intro x hx
        change ∃ a : KM.abPresheaf.stalk x, a ≠ 0
        refine ⟨KM.sectionGerm ⊤ x (by simp) s, ?_⟩
        simpa [RingedSpace.ModuleSheaf.suppSection] using hx
      have htop : (Set.univ : Set X) ⊆ KM.supp := by
        simpa [hfull] using hmap.trans hsection_le
      have hMsupp : KM.supp = Set.univ := by
        apply Set.eq_univ_iff_forall.mpr
        intro x
        exact htop (Set.mem_univ x)
      have hKdim' : topologicalKrullDim KM.supp ≤ 0 := hKdim
      rw [hMsupp] at hKdim'
      exact false_of_topologicalKrullDim_univ_le_zero hdim hKdim'
    let z : F.sections := F.unitHomEquiv
      (0 : SheafOfModules.unit R ⟶ F)
    have hz : z.eval (op ⊤) = 0 := by
      let : Module (R.obj.obj (op ⊤))
          (F.val.obj (op ⊤)) := (F.val.obj (op ⊤)).isModule
      let : Module (R.obj.obj (op ⊤))
          ((SheafOfModules.unit R).val.obj (op ⊤)) :=
        ((SheafOfModules.unit R).val.obj (op ⊤)).isModule
      let oneU : ↑((SheafOfModules.unit R).val.obj (op ⊤)) :=
        (1 : R.obj.obj (op ⊤))
      change (F.unitHomEquiv
        (0 : SheafOfModules.unit R ⟶ F)).val (op ⊤) = 0
      rw [SheafOfModules.unitHomEquiv_apply_coe]
      change (0 : ↑((SheafOfModules.unit R).val.obj (op ⊤)) →ₗ[
        R.obj.obj (op ⊤)] ↑(F.val.obj (op ⊤))) oneU = 0
      exact LinearMap.zero_apply _
    apply sections_eq_of_eval_top_eq F _ z
    change t = z.eval (op ⊤)
    exact htopzero.trans hz.symm
  have hcomp : gs.π ≫ K.arrow = 0 := by
    apply F.freeHomEquiv.injective
    funext i
    change F.unitHomEquiv (SheafOfModules.ιFree i ≫ (gs.π ≫ K.arrow)) =
      F.unitHomEquiv (SheafOfModules.ιFree i ≫
        (0 : SheafOfModules.free (R := R) gs.I ⟶ F))
    have hgsi : SheafOfModules.ιFree i ≫ gs.π =
        Kobj.unitHomEquiv.symm (gs.s i) := by
      calc
        SheafOfModules.ιFree i ≫ gs.π =
          Kobj.unitHomEquiv.symm (Kobj.freeHomEquiv gs.π i) :=
          (Kobj.unitHomEquiv_symm_freeHomEquiv_apply gs.π i).symm
        _ = Kobj.unitHomEquiv.symm (gs.s i) := by
          simp [SheafOfModules.GeneratingSections.π]
    calc
      F.unitHomEquiv (SheafOfModules.ιFree i ≫ (gs.π ≫ K.arrow)) =
          F.unitHomEquiv (Kobj.unitHomEquiv.symm (gs.s i) ≫ K.arrow) := by
            have hassoc : SheafOfModules.ιFree i ≫ (gs.π ≫ K.arrow) =
                (SheafOfModules.ιFree i ≫ gs.π) ≫ K.arrow :=
              (Category.assoc _ _ _).symm
            rw [hassoc, hgsi]
      _ = SheafOfModules.sectionsMap K.arrow (gs.s i) := by
        simpa using scheme_unitHomEquiv_comp_apply
          (Kobj.unitHomEquiv.symm (gs.s i)) K.arrow
      _ = F.unitHomEquiv (0 : SheafOfModules.unit R ⟶ F) := hsection0 i
      _ = F.unitHomEquiv (SheafOfModules.ιFree i ≫
          (0 : SheafOfModules.free (R := R) gs.I ⟶ F)) := by
            exact congrArg F.unitHomEquiv (comp_zero (f := SheafOfModules.ιFree i)).symm
  let : Epi gs.π := gs.epi
  have hKarrow : K.arrow = 0 := by
    apply (cancel_epi gs.π).mp
    exact hcomp.trans (comp_zero (f := gs.π)).symm
  have hquot := cokernel_hasNoEmbeddedAssociatedPoints F K hK hmax
  have hπiso : IsIso (cokernel.π K.arrow) := by
    rw [hKarrow]
    infer_instance
  have hF : HasNoEmbeddedAssociatedPoints F :=
    hasNoEmbeddedAssociatedPoints_of_moduleIso ((asIso (cokernel.π K.arrow)).symm) hquot
  have hno : HasNoEmbeddedPoints X := by
    simpa only [HasNoEmbeddedPoints, IsEmbeddedPoint,
      IsEmbeddedAssociatedPoint] using hF
  exact (isCohenMacaulay_iff_hasNoEmbeddedPoints_of_topologicalKrullDim_le_one
    X hdimle).2 hno

private theorem irreducibleComponent_dim_one_of_connected_dim_one
    {X : Type u} [TopologicalSpace X] [T0Space X] [NoetherianSpace X]
    [ConnectedSpace X] (hX : topologicalKrullDim X = 1)
    (C : Set X) (hC : C ∈ irreducibleComponents X) :
    topologicalKrullDim C = 1 := by
  have hCdim : topologicalKrullDim C ≤ 1 := by
    calc
      topologicalKrullDim C ≤ topologicalKrullDim X := topologicalKrullDim_subspace_le X C
      _ = 1 := hX
  have hCnonempty : C.Nonempty := hC.1.nonempty
  have hCnotzero : ¬ topologicalKrullDim C ≤ 0 := by
    intro hCzero
    let : IrreducibleSpace C := Subtype.irreducibleSpace hC.1
    have hmax := (Order.krullDim_nonpos_iff_forall_isMax.mp hCzero)
    have hclosure_eq_univ : ∀ x : C, closure ({x} : Set C) = Set.univ := by
      intro x
      let A : IrreducibleCloseds C :=
        ⟨closure ({x} : Set C), isIrreducible_singleton.closure, isClosed_closure⟩
      let B : IrreducibleCloseds C :=
        ⟨Set.univ, IrreducibleSpace.isIrreducible_univ C, isClosed_univ⟩
      have hAmax : IsMax A := hmax A
      have hAB : A ≤ B := Set.subset_univ _
      have hBA : B ≤ A := hAmax hAB
      have hEq : A = B := le_antisymm hAB hBA
      have hEq := congrArg (fun Z : IrreducibleCloseds C => (Z : Set C)) hEq
      simpa [A, B] using hEq
    have hsub : Subsingleton C := by
      refine ⟨fun x y => ?_⟩
      have hyx : y ⤳ x := specializes_iff_mem_closure.mpr (by rw [hclosure_eq_univ y]; simp)
      have hxy : x ⤳ y := specializes_iff_mem_closure.mpr (by rw [hclosure_eq_univ x]; simp)
      exact (hxy.antisymm hyx).eq
    have hopen : IsOpen C := by
      obtain ⟨U, hUopen, hUnonempty, hUC⟩ :=
        NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
      have hUC' : C ⊆ U := by
        intro x hx
        obtain ⟨y, hy⟩ := hUnonempty
        have hxy : (⟨x, hx⟩ : C) = ⟨y, hUC hy⟩ := Subsingleton.elim _ _
        have hxy' : x = y := congrArg Subtype.val hxy
        simpa [hxy'] using hy
      have hEq : U = C := Set.Subset.antisymm hUC hUC'
      exact hEq ▸ hUopen
    have hclosed : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
    have hclopen : IsClopen C := ⟨hclosed, hopen⟩
    obtain hCempty | hCuniv :=
      (connectedSpace_iff_clopen.mp (inferInstance : ConnectedSpace X)).2 C hclopen
    · exact hCnonempty.ne_empty hCempty
    · rw [hCuniv] at hCzero
      exact false_of_topologicalKrullDim_univ_le_zero hX hCzero
  have hdeq : topologicalKrullDim C = 1 := by
    cases hdim : topologicalKrullDim C with
    | bot =>
        apply False.elim
        apply hCnotzero
        rw [hdim]
        norm_num
    | coe e =>
        cases e with
        | top =>
            apply False.elim
            have hlt' : (1 : ℕ∞) < ⊤ := WithTop.coe_lt_top (1 : ℕ)
            have hlt : (1 : WithBot ℕ∞) < (↑(⊤ : ℕ∞) : WithBot ℕ∞) :=
              WithBot.coe_lt_coe.mpr hlt'
            have hle := hCdim
            rw [hdim] at hle
            exact (not_le_of_gt hlt) hle
        | coe n =>
            cases n with
            | zero =>
                apply False.elim
                apply hCnotzero
                rw [hdim]
                norm_num
            | succ n =>
                have hn : n = 0 := by
                  have hnle : n + 1 ≤ 1 := by
                    have hle := hCdim
                    rw [hdim] at hle
                    norm_cast at hle
                  omega
                subst n
                simp
  exact hdeq

/-- **Stacks Project, Tag 0BY5.** A proper one-dimensional scheme over a field whose only
global regular functions are constants is equidimensional. -/
@[stacks 0BY5 "equidimensionality"]
theorem equidimensional_of_isIso_globalSections_of_dimension_one
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] :
    TopologicalSpace.Equidimensional X := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : AlgebraicGeometry.IsNoetherian X := AlgebraicGeometry.IsNoetherian.mk
  let : NoetherianSpace X := inferInstance
  let : ConnectedSpace X := connectedSpace_of_isIso_globalSections k f
  intro C hC D hD
  rw [irreducibleComponent_dim_one_of_connected_dim_one hdim C hC,
    irreducibleComponent_dim_one_of_connected_dim_one hdim D hD]

end AlgebraicGeometry

end
