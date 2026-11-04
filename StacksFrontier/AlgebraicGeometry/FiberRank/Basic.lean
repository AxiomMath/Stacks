module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Data.List.TFAE
public import Mathlib.LinearAlgebra.Basis.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeTFAE
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeLocallySurjective
public import StacksFrontier.AlgebraicGeometry.CurveTensorEuler.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibre rank of a module on a scheme and finite local freeness

For a module on a scheme, flatness together with finite presentation, finite local freeness,
and the corresponding conditions on stalks are equivalent. This file defines the fibre rank
appearing in Stacks Tag 05P2 and proves the implications between that tag's conditions which
run through the stalks.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.fiberRank` is the dimension, over the residue field at a
  point, of the residue-field fibre of a sheaf of modules at that point. It is the rank
  function of condition (5) of Stacks Tag 05P2.

## Main results

* `AlgebraicGeometry.Scheme.Modules.free_stalk_of_isFlat` is the implication (1) ⟹ (2) of
  Stacks Tag 05P2, and `pointwise_isLocallyFree_of_free_stalks` is the implication (2) ⟹ (3).
* `AlgebraicGeometry.Scheme.Modules.isFlat_of_isLocallyFree` and
  `isFlat_of_isFiniteLocallyFree` are the exactness half of the implication (4) ⟹ (1):
  tensoring by a (finite) locally free module is exact. The finite-presentation half is
  `Stacks.FiniteLocallyFree.isFinitePresentation`.
* `AlgebraicGeometry.Scheme.Modules.isFiniteType_and_free_stalks_and_isLocallyConstant_fiberRank`
  is the implication (4) ⟹ (5), and `isLocallyConstant_fiberRank` its rank half.
* `AlgebraicGeometry.Scheme.Modules.flat_finitePresentation_locallyFree_tfae` is the equivalence
  of conditions (1), (2), (3) and (4) of Stacks Tag 05P2.
* `AlgebraicGeometry.Scheme.Modules.isLocallyFree_iff_pointwise` identifies the sheaf-theoretic
  local freeness of Mathlib with the pointwise trivialization condition, and
  `nonempty_restrict_iso_free_of_isLocallyFreeData` is the trivialization carried by one member
  of a locally free covering.
* `Stacks.FiniteLocallyFree.ModuleTFAE.fiberRank_eq_card_of_trivialization` computes the fibre
  rank on a member of a locally free covering, and
  `exists_isFiniteLocallyFreeOfRankData_of_pointwise` assembles pointwise trivializations of a
  fixed rank into one local free basis of that rank.
* `AlgebraicGeometry.Scheme.Modules.span_germs_near` propagates a stalkwise spanning family to
  a neighbourhood, for a module of finite type.

## Implementation notes

The converse implication (5) ⟹ (3) and the resulting five-way equivalence of Stacks Tag 05P2
are in `StacksFrontier.AlgebraicGeometry.FiberRank.LocallyFree`, which is where the tag is
attached. Its germ-level inputs are proved here: `span_germs_near` propagates a stalkwise
spanning family to a neighbourhood, and `exists_combination_of_germ_mem_span` turns a germ-level
linear combination into one on sections.

Local freeness has two inequivalent spellings in this library, and both occur here. Mathlib's
`SheafOfModules.IsLocallyFree` is a class asserting the existence of `LocalGeneratorsData`,
while `AlgebraicGeometry.Scheme.Modules.IsLocallyFree`
(`StacksFrontier/RingTheory/Module/LocallyFree/SheafBridge.lean`) is the pointwise statement that
every point has a trivializing neighbourhood. They are bridged by `isLocallyFree_iff_pointwise`.
Because the latter is in scope here, the dot-notation `F.IsLocallyFree` would resolve to the
pointwise one; every occurrence of Mathlib's notion is therefore written out as
`_root_.SheafOfModules.IsLocallyFree`.

The scalar action of the structure sheaf on sections resolves only in the `RingCat` spelling
`X.ringCatSheaf.obj.obj (op U)`, not in the `CommRingCat` one `X.presheaf.obj (op U)`; section
level statements here are written in the former, as
`Stacks.SheafOfModules.LocallySurjective.LocalLinComb` is, while
stalk-level statements use the `CommRingCat` stalk. `PresheafOfModules.germ_smul` crosses
between them and is applied rather than restated.

## References

* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct

universe u v

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.FiniteLocallyFree.ModuleTFAE
  (localGeneratorsDataOfTrivializations localGeneratorsDataOfTrivializations_isLocallyFreeData)

section LocallyFreeBridge

/-- The free sheaf on an open `U` of a scheme, read through the equivalence between sheaves of
modules over the restricted structure sheaf and sheaves of modules on `U` as a scheme. -/
private def freeOverEquivIso {X : Scheme.{u}} (U : X.Opens) (I : Type u) :
    _root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅
      (Scheme.Modules.overEquiv U).functor.obj
        (_root_.SheafOfModules.free (R := X.ringCatSheaf.over U) I) := by
  let F := (Scheme.Modules.overEquiv U).functor
  haveI : PreservesColimitsOfShape.{u, u} (Discrete I) F :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} F
  exact @_root_.SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F I this (Iso.refl _)

/-- On a member of a locally free covering, the module restricts to the free module on that
member's family of generators. -/
public theorem nonempty_restrict_iso_free_of_isLocallyFreeData
    {X : Scheme.{u}} (F : X.Modules) (q : F.LocalGeneratorsData.{u})
    (hq : q.IsLocallyFreeData) (i : q.I) :
    Nonempty (F.restrict (Scheme.Opens.ι (q.X i)) ≅
      _root_.SheafOfModules.free.{u} (q.generators i).I) := by
  let G := (Scheme.Modules.overEquiv (q.X i)).functor
  have : IsIso (q.generators i).π := hq.isIso i
  exact ⟨(freeOverEquivIso (q.X i) (q.generators i).I ≪≫
    G.mapIso (asIso (q.generators i).π) ≪≫
    (Scheme.Modules.overFunctorEquiv (q.X i)).app F).symm⟩

/-- Local generators data which is a local free basis trivializes `F` near every point. -/
private theorem pointwise_of_isLocallyFreeData
    {X : Scheme.{u}} (F : X.Modules) (q : F.LocalGeneratorsData.{u})
    (hq : q.IsLocallyFreeData) : Scheme.Modules.IsLocallyFree F := by
  intro x
  have hcov : TopologicalSpace.IsOpenCover q.X :=
    (Opens.coversTop_iff X q.X).mp q.coversTop
  obtain ⟨i, hxi⟩ := hcov.exists_mem x
  exact ⟨q.X i, hxi, (q.generators i).I,
    nonempty_restrict_iso_free_of_isLocallyFreeData F q hq i⟩

/-- Mathlib's local freeness of a sheaf of modules on a scheme agrees with the pointwise
condition that every point has a trivializing neighbourhood. -/
theorem isLocallyFree_iff_pointwise {X : Scheme.{u}} (F : X.Modules) :
    _root_.SheafOfModules.IsLocallyFree F ↔ Scheme.Modules.IsLocallyFree F := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨q : F.LocalGeneratorsData.{u}, hq⟩ := h.exists_isLocallyFreeData
    exact pointwise_of_isLocallyFreeData F q hq
  · choose U hU I e using h
    exact _root_.SheafOfModules.IsLocallyFree.mk.{u, u, u} (M := F)
      ⟨localGeneratorsDataOfTrivializations F U hU I e,
        localGeneratorsDataOfTrivializations_isLocallyFreeData F U hU I e⟩

/-- Pointwise trivializations whose index types all have `r` elements assemble into local
generators data which is a local free basis of rank `r`. This is the rank-indexed companion of
`isLocallyFree_iff_pointwise`: the conclusion is the defining datum of
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`. -/
public theorem exists_isFiniteLocallyFreeOfRankData_of_pointwise
    {X : Scheme.{u}} (F : X.Modules) (r : ℕ)
    (h : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (I : Type u), Nonempty (I ≃ Fin r) ∧
      Nonempty (F.restrict U.ι ≅ _root_.SheafOfModules.free.{u} I)) :
    ∃ q : F.LocalGeneratorsData.{u},
      q.IsLocallyFreeData ∧ ∀ i, Nonempty ((q.generators i).I ≃ Fin r) := by
  classical
  choose U hU I hrank e using h
  exact ⟨localGeneratorsDataOfTrivializations F U hU I e,
    localGeneratorsDataOfTrivializations_isLocallyFreeData F U hU I e, hrank⟩

end LocallyFreeBridge

section FiberRank

/-- A finite basis of `V` over `k` makes the rank of the base change along any field extension
the cardinality of the indexing type. This step mentions no scheme; stating it separately keeps
the expensive unification of the two stalk spellings out of it. -/
@[ega "I 6.4.6" "special case"]
private theorem finrank_baseChange_eq_card
    {k : Type u} [CommRing k] {V : Type u} [AddCommGroup V] [Module k V]
    {K : Type u} [Field K] [Algebra k K] {I : Type u} [Finite I]
    (b : Module.Basis I k V) :
    Module.finrank K (K ⊗[k] V) = Nat.card I := by
  classical
  let : Fintype I := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact Module.finrank_eq_card_basis (b.baseChange K)

/-- On a trivializing open, the fibre rank is the cardinality of the trivializing index set.

The trivialization is a parameter rather than a `let`-bound construction, so that unification
never unfolds it; with the construction inlined this step exceeds the heartbeat budget. -/
public theorem fiberRank_eq_card_of_trivialization
    {X : Scheme.{u}} (F : X.Modules) (x : X) {U : X.Opens} (hxU : x ∈ U)
    (t : LocallyFreeRank.Trivialization X.toTopCat X.ringCatSheaf F U) [Finite t.ι] :
    fiberRank F x = Nat.card t.ι := by
  obtain ⟨e⟩ := LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp
    X.toTopCat X.sheaf F x hxU t
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Algebra (X.presheaf.stalk x) (X.residueField x) := (X.residue x).hom.toAlgebra
  exact finrank_baseChange_eq_card ((Finsupp.basisSingleOne (ι := t.ι)).map e.symm)

/-- For a finite type module with free stalk at `x`, the fibre rank at `x` is the rank of the
stalk. -/
public alias fiberRank_eq_finrank_stalk :=
  Stacks.FiniteLocallyFree.ModuleTFAE.fiberRank_eq_finrank

/-- **The fibre rank of a finite locally free module of constant rank `r` is `r`, at every
point.** The trivializing cover of the fixed-rank class has every indexing type equivalent to
`Fin r`, and the fibre rank on a member of that cover is the cardinality of its indexing
type. -/
public theorem fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank {X : Scheme.{u}} (F : X.Modules)
    (r : ℕ) [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (x : X) : fiberRank F x = r := by
  obtain ⟨q, hq, hr⟩ := hF.exists_isFiniteLocallyFreeOfRankData
  have hcov : TopologicalSpace.IsOpenCover q.X := (Opens.coversTop_iff X q.X).mp q.coversTop
  obtain ⟨i, hxi⟩ := hcov.exists_mem x
  obtain ⟨e⟩ := hr i
  have : Finite (q.generators i).I := Finite.of_equiv (Fin r) e.symm
  rw [Stacks.FiniteLocallyFree.ModuleTFAE.fiberRank_eq_card_of_trivialization F q hq i x hxi,
    Nat.card_congr e,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The fibre rank of a module whose stalk at `x` vanishes is zero at `x`: the residue-field
fibre is a base change of that stalk. -/
public theorem fiberRank_eq_zero_of_subsingleton_stalk {X : Scheme.{u}} (F : X.Modules) (x : X)
    (h : Subsingleton (ToType (F.presheaf.stalk x))) : fiberRank F x = 0 := by
  let A := ToType (X.presheaf.stalk x)
  let M := ToType (F.presheaf.stalk x)
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Algebra A (X.residueField x) := (X.residue x).hom.toAlgebra
  let : Subsingleton M := h
  show Module.finrank (X.residueField x) (X.residueField x ⊗[A] M) = 0
  exact Module.finrank_zero_of_subsingleton

end FiberRank

section Flat

/-- A locally free sheaf of modules on a scheme is flat, i.e. tensoring by it is an exact
endofunctor. Flatness is detected on stalks by Tag 05NE, and the stalks of a locally free
module are free.

This is the **exactness half of the implication (4) ⟹ (1) of Stacks Tag 05P2**. The
finite-presentation half is `Stacks.FiniteLocallyFree.isFinitePresentation`. No finiteness is
needed here, so the hypothesis is local freeness rather than finite local freeness. -/
@[ega "0 5.4.1" "special case", ega "IV 2.1.12" "(b) ⇒ (a) with U = X"]
theorem isFlat_of_isLocallyFree {X : Scheme.{u}} (F : X.Modules)
    [h : _root_.SheafOfModules.IsLocallyFree.{u, u, u} F] :
    AlgebraicGeometry.SheafOfModules.IsFlat
      (C := TopologicalSpace.Opens X.toTopCat)
      (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) F := by
  obtain ⟨q : F.LocalGeneratorsData.{u}, hq⟩ := h.exists_isLocallyFreeData
  apply (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat X.sheaf F).2
  intro x
  let A := ToType (X.presheaf.stalk x)
  let M := ToType (F.presheaf.stalk x)
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Module.Free A M :=
    Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFreeData_stalkFree F q hq x
  show Module.Flat A M
  exact Module.Flat.of_free

/-- A finite locally free sheaf of modules on a scheme is flat. Together with
`Stacks.FiniteLocallyFree.isFinitePresentation` this is the full implication
(4) ⟹ (1) of Stacks Tag 05P2. -/
theorem isFlat_of_isFiniteLocallyFree {X : Scheme.{u}} (F : X.Modules)
    [Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F] :
    AlgebraicGeometry.SheafOfModules.IsFlat
      (C := TopologicalSpace.Opens X.toTopCat)
      (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) F :=
  have : _root_.SheafOfModules.IsLocallyFree.{u, u, u} F :=
    Stacks.FiniteLocallyFree.instIsLocallyFree.{u, u, u} F
  isFlat_of_isLocallyFree F

end Flat

section FiniteLocallyFree

/-- On a trivializing open of a finite type module, the trivializing index set is finite: the
stalk is a finite module and the trivialization exhibits a basis for it indexed by that set. -/
private theorem finite_trivialization_index {X : Scheme.{u}} (F : X.Modules) [F.IsFiniteType]
    (x : X) {U : X.Opens} (hxU : x ∈ U)
    (t : LocallyFreeRank.Trivialization X.toTopCat X.ringCatSheaf F U) :
    Finite t.ι := by
  obtain ⟨a⟩ := LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp
    X.toTopCat X.sheaf F x hxU t
  let A := ToType (X.presheaf.stalk x)
  let M := ToType (F.presheaf.stalk x)
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Module.Finite A M := _root_.SheafOfModules.finite_stalk X.sheaf F x
  let : IsLocalRing A := X.isLocalRing x
  exact Module.Finite.finite_basis
    (((Finsupp.basisSingleOne (ι := t.ι) (R := A)).map a.symm : Module.Basis t.ι A M))

/-- A locally free module of finite type is finite locally free: each trivializing chart may be
taken with a finite index set, because the stalk at a point of the chart is a finite module. -/
theorem isFiniteLocallyFree_of_isLocallyFree_of_isFiniteType
    {X : Scheme.{u}} (F : X.Modules) (hfree : Scheme.Modules.IsLocallyFree F)
    [F.IsFiniteType] :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F := by
  classical
  choose U hU I e using hfree
  let q := localGeneratorsDataOfTrivializations F U hU I e
  have hq : q.IsLocallyFreeData :=
    localGeneratorsDataOfTrivializations_isLocallyFreeData F U hU I e
  have hfinite : q.IsFiniteType := ⟨fun i => ⟨finite_trivialization_index F i (hU i)
    (LocallyFreeRank.trivializationOfLocalGenerators F q hq i)⟩⟩
  exact ⟨q, hq, hfinite⟩

end FiniteLocallyFree


section Germs

/-- Finitely many stalk elements are simultaneously the germs of sections on one neighbourhood
contained in a prescribed open. -/
theorem finite_germ_lifts {C : Type v} [Category.{u} C] [HasColimits C]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [PreservesFilteredColimits (CategoryTheory.forget C)] {Y : TopCat.{u}}
    (G : TopCat.Presheaf C Y) {I : Type*} [Finite I] (x : Y)
    (m : I → ToType (G.stalk x)) {V : TopologicalSpace.Opens Y} (hxV : x ∈ V) :
    ∃ (U : TopologicalSpace.Opens Y) (_ : U ≤ V) (hxU : x ∈ U)
      (s : I → ToType (G.obj (op U))),
      ∀ i, (ConcreteCategory.hom (G.germ U x hxU)) (s i) = m i := by
  classical
  choose U hU s hs using fun i => G.exists_germ_eq (m i)
  let W := V ⊓ ⨅ i, U i
  have hxW : x ∈ W := ⟨hxV, by
    rw [TopologicalSpace.Opens.coe_iInf]; exact Set.mem_iInter.mpr hU⟩
  have hWU (i : I) : W ≤ U i := inf_le_right.trans (iInf_le U i)
  refine ⟨W, inf_le_left, hxW,
    fun i => (ConcreteCategory.hom (G.map (homOfLE (hWU i)).op)) (s i), ?_⟩
  intro i
  rw [TopCat.Presheaf.germ_res_apply]
  exact hs i

/-- Taking germs is compatible with restriction of sections. -/
theorem germ_map_section {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Opens} (f : U ⟶ V) (x : X) (hx : x ∈ U) (s : F.val.presheaf.obj (op V)) :
    TopCat.Presheaf.germ F.val.presheaf U x hx (F.val.presheaf.map f.op s) =
      TopCat.Presheaf.germ F.val.presheaf V x (leOfHom f hx) s :=
  TopCat.Presheaf.germ_res_apply F.val.presheaf f x hx s

/-- A section whose germ lies in the span of the germs of finitely many sections is, on a
smaller neighbourhood, an actual linear combination of them.

The scalars are written in the `RingCat` spelling of the structure sheaf and the restricted
sections are ascribed to `F.val.obj`, which is the spelling in which the scalar action on
sections resolves; see `Stacks.SheafOfModules.LocallySurjective.LocalLinComb`. -/
theorem exists_combination_of_germ_mem_span {X : Scheme.{u}} (F : X.Modules)
    {I : Type u} [Fintype I] {V U : X.Opens} (s : I → F.val.presheaf.obj (op V))
    (t : F.val.presheaf.obj (op U)) (x : X) (hxV : x ∈ V) (hxU : x ∈ U)
    (h :
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      TopCat.Presheaf.germ F.val.presheaf U x hxU t ∈ Submodule.span (X.presheaf.stalk x)
        (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf V x hxV (s i))) :
    ∃ (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V), x ∈ W ∧
      ∃ c : I → X.ringCatSheaf.obj.obj (op W),
        (F.val.presheaf.map (homOfLE hWU).op t : F.val.obj (op W)) =
          ∑ i, c i • (F.val.presheaf.map (homOfLE hWV).op (s i) : F.val.obj (op W)) := by
  let : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp h
  obtain ⟨W, hW, hxW, a, ha⟩ := finite_germ_lifts X.presheaf x c
    (V := U ⊓ V) ⟨hxU, hxV⟩
  have hWU := hW.trans inf_le_left
  have hWV := hW.trans inf_le_right
  -- `finite_germ_lifts` produces the scalars in the `CommRingCat` spelling of the structure
  -- sheaf; the scalar action on sections resolves only in the `RingCat` spelling, and the two
  -- section types are equal by `rfl`.
  let a' : I → X.ringCatSheaf.obj.obj (op W) := fun i => a i
  let z : F.val.obj (op W) :=
    ∑ i, a' i • (F.val.presheaf.map (homOfLE hWV).op (s i) : F.val.obj (op W))
  have hz : TopCat.Presheaf.germ F.val.presheaf W x hxW z =
      TopCat.Presheaf.germ F.val.presheaf U x hxU t :=
    (map_sum (ConcreteCategory.hom (TopCat.Presheaf.germ F.val.presheaf W x hxW)) _ _).trans
      (Eq.trans (Finset.sum_congr rfl fun i _ =>
        (PresheafOfModules.germ_smul (R := X.presheaf) F.val x W hxW (a i)
            (F.val.presheaf.map (homOfLE hWV).op (s i) : F.val.obj (op W))).trans (by
          rw [ha i]
          congr 1
          exact TopCat.Presheaf.germ_res_apply F.val.presheaf _ _ _ _)) hc)
  obtain ⟨W', hxW', f, g, heq⟩ :=
    TopCat.Presheaf.germ_eq F.val.presheaf x hxW hxU z t hz
  refine ⟨W', leOfHom g, (leOfHom f).trans hWV, hxW',
    fun i => (X.presheaf.map f.op (a i) : X.ringCatSheaf.obj.obj (op W')), ?_⟩
  have hgt : (F.val.presheaf.map g.op t : F.val.obj (op W')) =
      F.val.presheaf.map f.op z := heq.symm
  refine Eq.trans hgt ?_
  refine Eq.trans (map_sum (ConcreteCategory.hom (F.val.presheaf.map f.op)) _ _) ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (PresheafOfModules.map_smul F.val f.op (a' i)
    (F.val.presheaf.map (homOfLE hWV).op (s i) : F.val.obj (op W))).trans ?_
  congr 1
  exact ((F.val.presheaf.map_comp (homOfLE hWV).op f.op).symm.trans
    (congrArg F.val.presheaf.map (by apply Subsingleton.elim))).symm ▸ rfl


/-- The germ of a scalar multiple of a restricted section is the scalar's germ times the germ of
the section. -/
private theorem germ_smul_map_section {X : Scheme.{u}} (F : X.Modules) {V W : X.Opens}
    (hWV : W ≤ V) (y : X) (hyW : y ∈ W) (c : X.ringCatSheaf.obj.obj (op W))
    (s : F.val.presheaf.obj (op V)) :
    letI : Module (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val y
    TopCat.Presheaf.germ F.val.presheaf W y hyW
        (c • (F.val.presheaf.map (homOfLE hWV).op s : F.val.obj (op W))) =
      X.presheaf.germ W y hyW c • TopCat.Presheaf.germ F.val.presheaf V y (hWV hyW) s :=
  (PresheafOfModules.germ_smul (R := X.presheaf) F.val y W hyW c
    (F.val.presheaf.map (homOfLE hWV).op s : F.val.obj (op W))).trans
    (congrArg (fun w : ToType (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) =>
        X.presheaf.germ W y hyW c • w)
      (germ_map_section F (homOfLE hWV) y hyW s))

/-- The germs of a family of local generators span the stalk at every point of their domain. -/
theorem span_germs_of_local_generators {X : Scheme.{u}} (F : X.Modules)
    {J : Type u} [Fintype J] {V : X.Opens} (t : J → F.val.presheaf.obj (op V))
    (ht : Stacks.SheafOfModules.LocallySurjective.LocalLinComb (X := X.toRingedSpace) V t)
    (y : X) (hy : y ∈ V) :
    letI : Module (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val y
    ⊤ ≤ Submodule.span (X.presheaf.stalk y)
      (Set.range fun j => TopCat.Presheaf.germ F.val.presheaf V y hy (t j)) := by
  let : Module (X.presheaf.stalk y)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val y
  -- the statement's `letI` must be zeta-reduced away before `intro` can reach the `≤`
  show ⊤ ≤ Submodule.span (X.presheaf.stalk y)
    (Set.range fun j => TopCat.Presheaf.germ F.val.presheaf V y hy (t j))
  intro m _
  obtain ⟨U, hUV, hyU, s, hs⟩ := TopCat.Presheaf.exists_le_germ_eq F.val.presheaf m hy
  obtain ⟨W, hWU, hyW, c, hc⟩ := ht U hUV s y hyU
  have hm : TopCat.Presheaf.germ F.val.presheaf W y hyW
      (F.val.presheaf.map (homOfLE hWU).op s) = m := by
    rwa [TopCat.Presheaf.germ_res_apply]
  have hsum := map_sum (ConcreteCategory.hom (TopCat.Presheaf.germ F.val.presheaf W y hyW))
    (fun j => c j • (F.val.presheaf.map (homOfLE (le_trans hWU hUV)).op (t j) :
      F.val.obj (op W))) Finset.univ
  rw [← hm, hc, hsum]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact Eq.mpr (congrArg (· ∈ _) (germ_smul_map_section F (le_trans hWU hUV) y hyW (c j) (t j)))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

/-- Spanning the stalk at one point propagates to a whole neighbourhood, for a module of
finite type. -/
theorem span_germs_near {X : Scheme.{u}} (F : X.Modules) [F.IsFiniteType]
    {I : Type u} [Finite I] {U : X.Opens} (s : I → F.val.presheaf.obj (op U))
    (x : X) (hxU : x ∈ U)
    (hx :
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      ⊤ ≤ Submodule.span (X.presheaf.stalk x)
        (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf U x hxU (s i))) :
    ∃ (W : X.Opens) (hWU : W ≤ U), x ∈ W ∧ ∀ y (hy : y ∈ W),
      letI : Module (X.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val y
      ⊤ ≤ Submodule.span (X.presheaf.stalk y)
        (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf U y (hWU hy) (s i)) := by
  classical
  let : Fintype I := Fintype.ofFinite _
  obtain ⟨V, hxV, J, hJ, t, ht⟩ :=
    Stacks.SheafOfModules.LocallySurjective.exists_local_generators (X := X.toRingedSpace) (F := F)
      (inferInstanceAs (_root_.SheafOfModules.IsFiniteType.{u, u, u} F)) x
  let := hJ
  have hmem (j : J) :
      let : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      TopCat.Presheaf.germ F.val.presheaf V x hxV (t j) ∈ Submodule.span (X.presheaf.stalk x)
        (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf U x hxU (s i)) :=
    hx Submodule.mem_top
  choose W hWV hWU hxW c hc using fun j =>
    exists_combination_of_germ_mem_span F s (t j) x hxU hxV (hmem j)
  let Z := (U ⊓ V) ⊓ ⨅ j, W j
  have hZU : Z ≤ U := inf_le_left.trans inf_le_left
  have hZV : Z ≤ V := inf_le_left.trans inf_le_right
  have hZW (j : J) : Z ≤ W j := inf_le_right.trans (iInf_le W j)
  refine ⟨Z, hZU, ⟨⟨hxU, hxV⟩, by
    rw [TopologicalSpace.Opens.coe_iInf]; exact Set.mem_iInter.mpr hxW⟩, ?_⟩
  intro y hy
  let : Module (X.presheaf.stalk y)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val y
  show ⊤ ≤ Submodule.span (X.presheaf.stalk y)
    (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf U y (hZU hy) (s i))
  intro m hm
  refine Submodule.span_le.mpr ?_
    (span_germs_of_local_generators F t ht y (hZV hy) hm)
  rintro _ ⟨j, rfl⟩
  -- The germ of `t j` at `y` through `V` equals its germ through `W j` after restriction.
  -- Stating that equation in the goal's own spelling is what lets `rw` fire: the two sides
  -- carry syntactically different membership proofs, which defeats a direct rewrite with
  -- `germ_res_apply`.
  have hgerm :
      TopCat.Presheaf.germ F.val.presheaf V y (hZV hy) (t j) =
        TopCat.Presheaf.germ F.val.presheaf (W j) y (hZW j hy)
          (F.val.presheaf.map (homOfLE (hWV j)).op (t j)) :=
    (germ_map_section F (homOfLE (hWV j)) y (hZW j hy) (t j)).symm
  have hsum := map_sum
    (ConcreteCategory.hom (TopCat.Presheaf.germ F.val.presheaf (W j) y (hZW j hy)))
    (fun i => c j i • (F.val.presheaf.map (homOfLE (hWU j)).op (s i) :
      F.val.obj (op (W j)))) Finset.univ
  show TopCat.Presheaf.germ F.val.presheaf V y (hZV hy) (t j) ∈ _
  rw [hgerm, hc j, hsum]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact Eq.mpr (congrArg (· ∈ _)
    (germ_smul_map_section F (hWU j) y (hZW j hy) (c j i) (s i)))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

end Germs



section Implications

/-- A module of finite presentation is of finite type. Mathlib proves this as an anonymous
instance, but its `IsFiniteType` carries a universe parameter that the statement of the class
does not determine, so instance search does not find it at the instantiation `X.Modules`
presents; this names the derivation once. -/
theorem isFiniteType_of_isFinitePresentation {X : Scheme.{u}} (F : X.Modules)
    (hfp : F.IsFinitePresentation) : _root_.SheafOfModules.IsFiniteType.{u, u, u} F := by
  obtain ⟨σ, hσ⟩ :=
    _root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
  -- `σ.localGeneratorsData.generators i` is by definition `(σ.presentation i).generators`,
  -- whose finiteness is the `isFiniteType_generators` field of `σ.IsFinitePresentation`.
  -- Mathlib's corresponding instance is proved under a transparency option, so it is not
  -- found here; this builds the datum directly instead.
  refine { exists_localGeneratorsData :=
    ⟨σ.localGeneratorsData, { isFiniteType := fun i => ?_ }⟩ }
  exact (hσ.isFinite_presentation i).isFiniteType_generators


/-- A flat module of finite presentation has free stalks: the stalk is a finite flat module
over a local ring. This is the implication (1) ⟹ (2) of Stacks Tag 05P2. -/
theorem free_stalk_of_isFlat {X : Scheme.{u}} (F : X.Modules) (hfp : F.IsFinitePresentation)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      (C := TopologicalSpace.Opens X.toTopCat)
      (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) F) (x : X) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  let A := ToType (X.presheaf.stalk x)
  let M := ToType (F.presheaf.stalk x)
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let := isFiniteType_of_isFinitePresentation F hfp
  let : Module.Finite A M := _root_.SheafOfModules.finite_stalk X.sheaf F x
  let : Module.Flat A M :=
    (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat X.sheaf F).mp hflat x
  let : IsLocalRing A := X.isLocalRing x
  exact Module.free_of_flat_of_isLocalRing

/-- A module of finite presentation whose stalks are free is locally free. This is the
implication (2) ⟹ (3) of Stacks Tag 05P2.

Tag 0B8J produces the local trivialization from a free stalk, but states it over the
`RingCat` stalk of the structure sheaf, while freeness of the stalk is given over the
`CommRingCat` one. The two are transported into each other by
`SemilinearStalk.commStalkRingEquiv`, whose compatibility with the two scalar actions is
`SemilinearStalk.comm_smul_eq`. -/
theorem pointwise_isLocallyFree_of_free_stalks {X : Scheme.{u}} (F : X.Modules)
    (hfp : F.IsFinitePresentation)
    (hstalk : ∀ x : X,
      letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x)) :
    Scheme.Modules.IsLocallyFree F := by
  classical
  let : F.IsFinitePresentation := hfp
  intro x
  let A := ToType (X.presheaf.stalk x)
  let B := ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
    (X.sheaf.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x)
  let M := ToType (F.presheaf.stalk x)
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Module B M :=
    PresheafOfModules.instModuleCarrierStalkRingCatCarrierAbPresheafOpensCarrier F.val x
  let := isFiniteType_of_isFinitePresentation F hfp
  let : Module.Finite A M := _root_.SheafOfModules.finite_stalk X.sheaf F x
  let eBA : B ≃+* A := SemilinearStalk.commStalkRingEquiv X.sheaf.obj x
  let eAB := eBA.symm
  let : RingHomInvPair (↑eAB : A →+* B) (↑eBA : B →+* A) := RingHomInvPair.of_ringEquiv eAB
  let : RingHomInvPair (↑eBA : B →+* A) (↑eAB : A →+* B) := RingHomInvPair.of_ringEquiv eBA
  have hsmul (t : B) (m : M) : eBA t • m = t • m :=
    SemilinearStalk.comm_smul_eq X.sheaf.obj x F.val t m
  let eM : M ≃ₛₗ[(↑eAB : A →+* B)] M :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a m
        have h := hsmul (eAB a) m
        change eBA (eAB a) • m = eAB a • m at h
        calc
          a • m = eBA (eAB a) • m := by rw [RingEquiv.apply_symm_apply]
          _ = eAB a • m := h }
  let : Module.Free A M := hstalk x
  let : Module.Free B M := Module.Free.of_equiv eM
  let : Module.Finite B M :=
    Module.Finite.of_surjective (R := A) (S := B) (M := M) (P := M)
      (σ := (↑eAB : A →+* B)) eM eM.surjective
  let b := Module.Free.chooseBasis B M
  let I := Module.Free.ChooseBasisIndex B M
  let : Fintype I := Fintype.ofFinite _
  let r := Fintype.card I
  let e := (Fintype.equivFin I).trans Equiv.ulift.symm
  have hiso : Nonempty (M ≃ₗ[B] (ULift.{u} (Fin r) →₀ B)) := ⟨(b.reindex e).repr⟩
  obtain ⟨U, hxU, hIso⟩ :=
    Stacks.SheafOfModules.exists_iso_free_over_of_stalk_iso_free F hfp x r hiso
  obtain ⟨hIso⟩ := hIso
  let G := (Scheme.Modules.overEquiv U).functor
  exact ⟨U, hxU, ULift.{u} (Fin r),
    ⟨((Scheme.Modules.overFunctorEquiv U).app F).symm ≪≫ G.mapIso hIso ≪≫
      (freeOverEquivIso U (ULift.{u} (Fin r))).symm⟩⟩

/-- The fibre rank of a finite locally free module is locally constant: on a trivializing
chart it is the cardinality of the trivializing index set. This is the rank half of the
implication (4) ⟹ (5) of Stacks Tag 05P2. -/
theorem isLocallyConstant_fiberRank {X : Scheme.{u}} (F : X.Modules)
    [h : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F] :
    IsLocallyConstant (fiberRank F) := by
  obtain ⟨q : F.LocalGeneratorsData.{u}, hfree, hfinite⟩ := h.exists_isFiniteLocallyFreeData
  have hcov : TopologicalSpace.IsOpenCover q.X :=
    (Opens.coversTop_iff X q.X).mp q.coversTop
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  obtain ⟨i, hxi⟩ := hcov.exists_mem x
  let : Finite (q.generators i).I := (hfinite.isFiniteType i).finite
  refine ⟨q.X i, (q.X i).isOpen, hxi, fun y hy => ?_⟩
  exact (Stacks.FiniteLocallyFree.ModuleTFAE.fiberRank_eq_card_of_trivialization
      F q hfree i y hy).trans
    (Stacks.FiniteLocallyFree.ModuleTFAE.fiberRank_eq_card_of_trivialization
      F q hfree i x hxi).symm

/-- Clause (5) of Stacks Tag 05P2 holds for a finite locally free module: it is of finite
type, its stalks are free, and its fibre rank is locally constant. This is the implication
(4) ⟹ (5). -/
theorem isFiniteType_and_free_stalks_and_isLocallyConstant_fiberRank
    {X : Scheme.{u}} (F : X.Modules)
    [h : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F] :
    _root_.SheafOfModules.IsFiniteType.{u, u, u} F ∧
      (∀ x : X,
        letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) F.val x
        Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x)) ∧
      IsLocallyConstant (fiberRank F) := by
  obtain ⟨q : F.LocalGeneratorsData.{u}, hfree, hfinite⟩ := h.exists_isFiniteLocallyFreeData
  refine ⟨Stacks.FiniteLocallyFree.isFiniteType F, fun x => ?_, isLocallyConstant_fiberRank F⟩
  exact Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFreeData_stalkFree F q hfree x

/-- Four of the five conditions of **Stacks Project, Tag 05P2** for a sheaf of modules on a
scheme: flatness together with finite presentation, finite presentation together with freeness
of all stalks, local freeness together with finite type, and finite local freeness, the last of
these in the `Stacks.FiniteLocallyFree.IsFiniteLocallyFree` spelling.

The tag's fifth condition — finite type, free stalks and locally constant fibre rank — is not
part of this equivalence; the implication (4) ⟹ (5) is
`isFiniteType_and_free_stalks_and_isLocallyConstant_fiberRank` and the converse (5) ⟹ (3) is
proved in `StacksFrontier.AlgebraicGeometry.FiberRank.LocallyFree`, where the five-way equivalence
`flat_finitePresentation_locallyFree_fiberRank_tfae` carries the `@[stacks 05P2]` attribute. No
attribute is attached here. -/
@[ega "0 5.4.1" "partial", ega "IV 2.1.12" "special case"]
theorem flat_finitePresentation_locallyFree_tfae {X : Scheme.{u}} (F : X.Modules) :
    List.TFAE [
      AlgebraicGeometry.SheafOfModules.IsFlat
          (C := TopologicalSpace.Opens X.toTopCat)
          (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) F ∧
        F.IsFinitePresentation,
      F.IsFinitePresentation ∧
        (∀ x : X,
          letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
            PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
              (R := X.presheaf) F.val x
          Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x)),
      _root_.SheafOfModules.IsLocallyFree.{u, u, u} F ∧
        _root_.SheafOfModules.IsFiniteType.{u, u, u} F,
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F] := by
  tfae_have 1 → 2 := by
    rintro ⟨hflat, hfp⟩
    exact ⟨hfp, fun x => free_stalk_of_isFlat F hfp hflat x⟩
  tfae_have 2 → 3 := by
    rintro ⟨hfp, hstalk⟩
    exact ⟨(isLocallyFree_iff_pointwise F).mpr
        (pointwise_isLocallyFree_of_free_stalks F hfp hstalk),
      isFiniteType_of_isFinitePresentation F hfp⟩
  tfae_have 3 → 4 := by
    rintro ⟨hfree, htype⟩
    let := htype
    exact isFiniteLocallyFree_of_isLocallyFree_of_isFiniteType F
      ((isLocallyFree_iff_pointwise F).mp hfree)
  tfae_have 4 → 1 := fun _ =>
    ⟨isFlat_of_isFiniteLocallyFree F, Stacks.FiniteLocallyFree.isFinitePresentation F⟩
  tfae_finish

end Implications

end AlgebraicGeometry.Scheme.Modules
