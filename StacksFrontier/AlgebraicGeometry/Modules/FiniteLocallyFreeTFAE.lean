module

public import StacksFrontier.AlgebraicGeometry.CurveTensorEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Data.List.TFAE
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteProjective
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeLocallySurjective
public import Mathlib.LinearAlgebra.Basis.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite locally free sheaves on schemes

For a quasi-coherent module on a scheme, flatness and finite presentation, finite
local freeness, and the corresponding conditions on stalks and fibre ranks are
equivalent.

## Main definitions

* `fiberRank` is the dimension of the residue-field fibre of a module
  at a point.

## Main results

* `finiteLocallyFree_tfae` gives the five characterizations of a finite
  locally free quasi-coherent module.

## Implementation notes

The five entries of `List.TFAE` are the conditions in the source, in order.
The rank in the fifth entry is natural-number valued rather than integer-valued;
the source assumes finite type there, so all its values are finite nonnegative
integers. Local constancy is unchanged by the embedding into the integers.

## References

* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct
open AlgebraicGeometry.Scheme.Modules (fiberRank)

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules.presheaf
attribute [local implicit_reducible] PresheafOfModules.presheaf

universe u v w

namespace Stacks.FiniteLocallyFree.ModuleTFAE

/-- A local generator family covers every point of the base. -/
private theorem exists_mem_localGeneratorsData {X : Scheme.{u}} {F : X.Modules}
    (q : F.LocalGeneratorsData.{u}) (x : X) : ∃ i, x ∈ q.X i :=
  ((Opens.coversTop_iff X q.X).mp q.coversTop).exists_mem x

/-- An isomorphism `F|_U ≅ free I` in the over-category gives one on the restriction. -/
private theorem nonempty_restrict_iso_free {X : Scheme.{u}} (F : X.Modules) (U : X.Opens)
    {I : Type u} (e : F.over U ≅ SheafOfModules.free I) :
    Nonempty (F.restrict U.ι ≅ SheafOfModules.free I) :=
  ⟨((Scheme.Modules.overFunctorEquiv U).app F).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫ (Stacks.Modules.freeOverEquivIso U I).symm⟩

private theorem localGeneratorsData_to_pointwiseLocallyFree
    {X : Scheme.{u}} (F : X.Modules) (q : F.LocalGeneratorsData.{u})
    (hq : q.IsLocallyFreeData) : F.IsLocallyFree := by
  intro x
  obtain ⟨i, hxi⟩ := exists_mem_localGeneratorsData q x
  have : IsIso (q.generators i).π := hq.isIso i
  exact ⟨q.X i, hxi, (q.generators i).I,
    nonempty_restrict_iso_free F _ (asIso (q.generators i).π).symm⟩

private theorem finitePresentation_of_finiteLocallyFreeData
    {X : Scheme.{u}} (F : X.Modules) (q : F.LocalGeneratorsData.{u})
    (hq : q.IsLocallyFreeData) (hfinite : q.IsFiniteType) :
    SheafOfModules.IsFinitePresentation.{u, u, u} F := by
  let : q.IsLocallyFreeData := hq
  let σ := q.quasiCoherentData
  apply SheafOfModules.IsFinitePresentation.mk
  refine ⟨σ, ?_⟩
  constructor
  intro i
  constructor
  · change (q.generators i).IsFiniteType
    exact ⟨(hfinite.isFiniteType i).finite⟩
  · change (σ.presentation i).relations.IsFiniteType
    have hrel : Finite (ULift.{u, 0} Empty) := by
      let : Finite Empty := inferInstance
      exact Finite.of_equiv Empty Equiv.ulift.symm
    exact ⟨hrel⟩

private noncomputable def localGeneratorsTrivialization
    {X : Scheme.{u}} (F : X.Modules)
    (q : F.LocalGeneratorsData.{u}) (hq : q.IsLocallyFreeData) (i : q.I) :
    LocallyFreeRank.Trivialization X.toTopCat
      (LocallyFreeRank.toRingSheaf X.toTopCat X.sheaf) F (q.X i) := by
  let U := q.X i
  let R := LocallyFreeRank.toRingSheaf X.toTopCat X.sheaf
  let E := U.sheafOfModulesEquivOver R
  have hπ : IsIso (q.generators i).π := hq.isIso i
  let e : SheafOfModules.free (q.generators i).I ≅ F.over U := asIso (q.generators i).π
  let eFree : SheafOfModules.free (q.generators i).I ≅
      E.functor.obj (SheafOfModules.free (q.generators i).I) :=
    SheafOfModules.mapFreeIso E.functor (q.generators i).I
      (U.sheafOfModulesEquivOverUnit R)
  refine ⟨(q.generators i).I, ?_⟩
  exact (eFree ≪≫ E.functor.mapIso e ≪≫
    LocallyFreeRank.restrictModIsoOver X.toTopCat U R F).symm


private lemma finite_stalk_of_finiteType
    {Y : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u})
    (F : SheafOfModules.{u} ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R))
    [F.IsFiniteType] (x : Y) :
    letI : Module (TopCat.Presheaf.stalk (C := CommRingCat.{u})
        ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat).obj R) x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x
    Module.Finite (TopCat.Presheaf.stalk (C := CommRingCat.{u})
        ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat).obj R) x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) := by
  let : Module (TopCat.Presheaf.stalk (C := CommRingCat.{u})
      ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat).obj R) x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  obtain ⟨U₀, _, ⟨i, ⟨g₀⟩⟩, hxU₀⟩ := σ.coversTop ⊤ x (by trivial)
  let V := σ.X i
  have hxV : x ∈ V := (leOfHom g₀) hxU₀
  let gs := σ.generators i
  have : Finite gs.I := (hσ.isFiniteType i).finite
  let : Fintype gs.I := Fintype.ofFinite _
  let s (j : gs.I) : ↑(TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
    TopCat.Presheaf.germ F.val.presheaf V x hxV
      ((gs.s j).val (op (Over.mk (𝟙 V))))
  let S := Submodule.span
    (TopCat.Presheaf.stalk (C := CommRingCat.{u})
      ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat).obj R) x) (Set.range s)
  have hS : S = ⊤ := by
    apply top_unique
    intro m _
    obtain ⟨U, hUV, hxU, t, ht⟩ :=
      TopCat.Presheaf.exists_le_germ_eq F.val.presheaf m hxV
    have := SheafOfModules.isLocallySurjective_toSheaf_of_epi gs.π
    have hmem := Presheaf.imageSieve_mem ((Opens.grothendieckTopology Y).over V)
      ((SheafOfModules.toSheaf _).map gs.π).hom (U := op (Over.mk (homOfLE hUV))) t
    rw [GrothendieckTopology.mem_over_iff] at hmem
    obtain ⟨W, f, ⟨Z, g, h, ⟨a, ha⟩, hf⟩, hxW⟩ := hmem x hxU
    have hWU : W ≤ U := leOfHom f
    let Wo : Over V := Over.mk (homOfLE (le_trans hWU hUV))
    let k : Wo ⟶ Z := Over.homMk h (Subsingleton.elim _ _)
    let a' := (SheafOfModules.free (R :=
      ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R).over V)
      gs.I).val.presheaf.map k.op a
    have hbase : ∀ u : ToType (F.val.presheaf.obj (op U)),
        F.val.presheaf.map h.op (F.val.presheaf.map ((Over.forget V).map g).op u)
          = F.val.presheaf.map f.op u := by
      intro u
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hf]
    have key : gs.π.val.app (op Wo) a' = F.val.presheaf.map f.op t := by
      have hn := congrArg (fun q => q a)
        (((SheafOfModules.toSheaf _).map gs.π).hom.naturality k.op)
      dsimp only [ConcreteCategory.comp_apply] at hn
      exact hn.trans
        ((congrArg (fun b => (F.over V).val.presheaf.map k.op b) ha).trans (hbase t))
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp
      (SheafOfModules.free_image_mem_span gs.s (op Wo) a')
    have hm : TopCat.Presheaf.germ F.val.presheaf W x hxW
        (F.val.presheaf.map f.op t) = m := by
      rw [TopCat.Presheaf.germ_res_apply]
      exact ht
    let e (j : gs.I) : ↑(((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat.{u})).obj R).obj.obj (op W)) := c j
    let τ (j : gs.I) : ↑(F.val.obj (op W)) := (gs.s j).val (op Wo)
    have hjg : ∀ j : gs.I, TopCat.Presheaf.germ F.val.presheaf W x hxW (τ j) = s j := by
      intro j
      change TopCat.Presheaf.germ F.val.presheaf W x hxW ((gs.s j).val (op Wo)) = s j
      have hj := PresheafOfModules.sections_property (gs.s j)
        (Over.homMk (homOfLE (le_trans hWU hUV)) : Wo ⟶ Over.mk (𝟙 V)).op
      rw [← hj]
      exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
    have hc' : (∑ j : gs.I, e j • τ j) = F.val.presheaf.map f.op t := hc.trans key
    have hgs : ∀ j : gs.I, TopCat.Presheaf.germ F.val.presheaf W x hxW (e j • τ j)
        = @SMul.smul
            ↑(TopCat.Presheaf.stalk (C := CommRingCat.{u})
              ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat).obj R) x)
            ↑(TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) _
            (TopCat.Presheaf.germ (C := CommRingCat.{u})
              ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat).obj R) W x hxW (e j))
            (TopCat.Presheaf.germ F.val.presheaf W x hxW (τ j)) := fun j =>
      PresheafOfModules.germ_smul F.val x W hxW (e j) (τ j)
    have hmsum : m = ∑ j : gs.I, @SMul.smul
        ↑(TopCat.Presheaf.stalk (C := CommRingCat.{u})
          ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat).obj R) x)
        ↑(TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) _
        (TopCat.Presheaf.germ (C := CommRingCat.{u})
          ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat).obj R) W x hxW (e j))
        (TopCat.Presheaf.germ F.val.presheaf W x hxW (τ j)) :=
      hm.symm.trans
        ((congrArg (fun z => TopCat.Presheaf.germ F.val.presheaf W x hxW z) hc'.symm).trans
          ((map_sum _ _ _).trans (Finset.sum_congr rfl fun j _ => hgs j)))
    rw [hmsum]
    refine S.sum_mem fun j _ => S.smul_mem _ ?_
    rw [hjg j]
    exact Submodule.subset_span ⟨j, rfl⟩
  exact ⟨hS ▸ Submodule.fg_span (Set.finite_range s)⟩

theorem isIso_generatingSections_equivOfIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] (I : Type u)
    {N : SheafOfModules.{u} R} (e : SheafOfModules.free I ≅ N) :
    IsIso (((SheafOfModules.free.generatingSections I).equivOfIso e).π) := by
  change IsIso (((SheafOfModules.free.generatingSections I).ofEpi e.hom).π)
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  rw [SheafOfModules.free.generatingSections_π]
  dsimp [SheafOfModules.free.generatingSections]
  change IsIso (𝟙 (SheafOfModules.free I) ≫ e.hom)
  simpa only [Category.id_comp] using e.isIso_hom

public noncomputable def localGeneratorsDataOfTrivializations
    {X : Scheme.{u}} (F : X.Modules) (U : X → X.Opens)
    (hU : ∀ x, x ∈ U x) (I : X → Type u)
    (e : ∀ x, Nonempty (F.restrict (U x).ι ≅ SheafOfModules.free (I x))) :
    F.LocalGeneratorsData.{u} := {
  I := X
  X := U
  coversTop := by
    rw [Opens.coversTop_iff, TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    simp only [TopologicalSpace.Opens.mem_iSup]
    exact ⟨x, hU x⟩
  generators := fun x => by
    let G := (Scheme.Modules.overEquiv (U x)).functor
    let eFree := Stacks.Modules.freeOverEquivIso (U x) (I x)
    let eOver : SheafOfModules.free (I x) ≅ F.over (U x) :=
      G.preimageIso (eFree.symm ≪≫ (e x).some.symm ≪≫
        ((Scheme.Modules.overFunctorEquiv (U x)).app F).symm)
    exact (SheafOfModules.free.generatingSections (I x)).equivOfIso eOver }

public theorem localGeneratorsDataOfTrivializations_isLocallyFreeData
    {X : Scheme.{u}} (F : X.Modules) (U : X → X.Opens)
    (hU : ∀ x, x ∈ U x) (I : X → Type u)
    (e : ∀ x, Nonempty (F.restrict (U x).ι ≅ SheafOfModules.free (I x))) :
    (localGeneratorsDataOfTrivializations F U hU I e).IsLocallyFreeData := by
  refine { isIso := ?_ }
  intro i
  dsimp [localGeneratorsDataOfTrivializations]
  change IsIso (((SheafOfModules.free.generatingSections (I i)).equivOfIso
    (let G := (Scheme.Modules.overEquiv (U i)).functor
     let eFree := Stacks.Modules.freeOverEquivIso (U i) (I i)
     G.preimageIso (eFree.symm ≪≫ (e i).some.symm ≪≫
       ((Scheme.Modules.overFunctorEquiv (U i)).app F).symm))).π)
  exact isIso_generatingSections_equivOfIso (I i) _

private theorem isLocallyFree_iff_pointwiseLocallyFree
    {X : Scheme.{u}} (F : X.Modules) :
    SheafOfModules.IsLocallyFree F ↔ Scheme.Modules.IsLocallyFree F := by
  constructor
  · intro h
    obtain ⟨q : F.LocalGeneratorsData.{u}, hq⟩ := h.exists_isLocallyFreeData
    exact localGeneratorsData_to_pointwiseLocallyFree F q hq
  · intro h
    choose U hU I e using h
    exact SheafOfModules.IsLocallyFree.mk.{u, u, u} (M := F)
      ⟨localGeneratorsDataOfTrivializations F U hU I e,
        localGeneratorsDataOfTrivializations_isLocallyFreeData F U hU I e⟩

private theorem comm_smul_germ_at_stalk
    {V : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} V)
    (M : PresheafOfModules (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (U : Opens V) (x : V) (hx : x ∈ U)
    (r : R.obj (op U)) (m : M.obj (op U)) :
    R.germ U x hx r • TopCat.Presheaf.germ M.presheaf U x hx m =
      TopCat.Presheaf.germ (C := RingCat.{u})
        (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) U x hx r •
        TopCat.Presheaf.germ M.presheaf U x hx m := by
  rw [← PresheafOfModules.germ_smul M x U hx r m]
  exact PresheafOfModules.germ_ringCat_smul M x U hx r m

private noncomputable def commStalkRingEquivU
    {V : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} V) (x : V) :
    TopCat.Presheaf.stalk (C := RingCat.{u})
        (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x ≃+*
      TopCat.Presheaf.stalk (C := CommRingCat.{u}) R x :=
  (preservesColimitIso (forget₂ CommRingCat.{u} RingCat.{u})
    ((OpenNhds.inclusion x).op ⋙ R)).symm.ringCatIsoToRingEquiv

private theorem commStalkRingEquivU_germ
    {V : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} V) (x : V)
    (U : Opens V) (hx : x ∈ U) (r : R.obj (op U)) :
    commStalkRingEquivU R x
      (TopCat.Presheaf.germ (C := RingCat.{u})
        (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) U x hx r) = R.germ U x hx r := by
  have h := ι_preservesColimitIso_inv (forget₂ CommRingCat.{u} RingCat.{u})
    ((OpenNhds.inclusion x).op ⋙ R) (op ⟨U, hx⟩)
  exact congrArg (fun φ => (ConcreteCategory.hom φ) r) h

private theorem comm_smul_eq_at_stalk
    {V : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} V) (x : V)
    (M : PresheafOfModules (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (s : TopCat.Presheaf.stalk (C := RingCat.{u})
      (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) :
    commStalkRingEquivU R x s • m = s • m := by
  obtain ⟨U₁, hU₁, r₀, hr⟩ := TopCat.Presheaf.exists_germ_eq
    (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) s
  obtain ⟨U₂, hU₂, m₀, hm⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
  have hmem : x ∈ U₁ ⊓ U₂ := ⟨hU₁, hU₂⟩
  have hr' : TopCat.Presheaf.germ (C := RingCat.{u})
      (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) (U₁ ⊓ U₂) x hmem
      ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map
        (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op r₀) = s := by
    rw [TopCat.Presheaf.germ_res_apply (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})
      (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) x hmem r₀]
    exact hr
  have hm' : TopCat.Presheaf.germ M.presheaf (U₁ ⊓ U₂) x hmem
      (M.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op m₀) = m := by
    rw [TopCat.Presheaf.germ_res_apply M.presheaf
      (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) x hmem m₀]
    exact hm
  rw [← hr', ← hm', commStalkRingEquivU_germ]
  exact comm_smul_germ_at_stalk R M (U₁ ⊓ U₂) x hmem _ _

/-- The index type of `localGeneratorsTrivialization` is the generating family it was built
from. Isolated as its own declaration because the projection unfolds a tactic-built
structure through the scheme-to-ringed-space restriction diagram. -/
private lemma localGeneratorsTrivialization_ι {X : Scheme.{u}} (F : X.Modules)
    (q : F.LocalGeneratorsData.{u}) (hq : q.IsLocallyFreeData) (i : q.I) :
    (localGeneratorsTrivialization F q hq i).ι = (q.generators i).I := rfl

/-- The stalk of a trivialised sheaf at a point of the trivialising open has a basis indexed
by any type identified with the index type of the trivialisation. The trivialisation is a
variable here so that nothing has to be unfolded. -/
private lemma nonempty_stalk_basis_of {X : Scheme.{u}} (F : X.Modules)
    {U : X.Opens} (x : X) (hxU : x ∈ U) (ι : Type u)
    (t : LocallyFreeRank.Trivialization X.toTopCat
      (LocallyFreeRank.toRingSheaf X.toTopCat X.sheaf) F U) (hι : t.ι = ι) :
    Nonempty (Module.Basis ι (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x))) := by
  obtain ⟨a⟩ := LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp
    X.toTopCat X.sheaf F x hxU t
  subst hι
  exact ⟨Finsupp.basisSingleOne.map a.symm⟩

/-- A trivialised sheaf of finite type has a finite index set on the trivialising open. The
trivialisation is a variable so that the instance work is done with nothing to unfold. -/
private lemma finite_generators_of_trivialization {X : Scheme.{u}} (F : X.Modules)
    [F.IsFiniteType] {U : X.Opens} (x : X) (hxU : x ∈ U) (ι : Type u)
    (t : LocallyFreeRank.Trivialization X.toTopCat
      (LocallyFreeRank.toRingSheaf X.toTopCat X.sheaf) F U) (hι : t.ι = ι) :
    Finite ι := by
  let : IsLocalRing (ToType (X.presheaf.stalk x)) := X.isLocalRing x
  let : Module.Finite (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) :=
    finite_stalk_of_finiteType X.sheaf F x
  obtain ⟨b⟩ := nonempty_stalk_basis_of F x hxU ι t hι
  exact Module.Finite.finite_basis b

private lemma finite_generators_of_locallyFree {X : Scheme.{u}} (F : X.Modules)
    [F.IsFiniteType] (q : F.LocalGeneratorsData.{u}) (hq : q.IsLocallyFreeData)
    (i : q.I) (x : X) (hxi : x ∈ q.X i) : Finite (q.generators i).I :=
  finite_generators_of_trivialization F x hxi (q.generators i).I
    (localGeneratorsTrivialization F q hq i) (localGeneratorsTrivialization_ι F q hq i)

private theorem finiteLocallyFree_of_locallyFree_finiteType
    {X : Scheme.{u}} (F : X.Modules) (hfree : F.IsLocallyFree)
    [F.IsFiniteType] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (C := TopologicalSpace.Opens X) (J := Opens.grothendieckTopology X)
      (R := X.ringCatSheaf) F := by
  classical
  choose U hU I e using hfree
  let q := localGeneratorsDataOfTrivializations F U hU I e
  have hq : q.IsLocallyFreeData :=
    localGeneratorsDataOfTrivializations_isLocallyFreeData F U hU I e
  have hfinite : q.IsFiniteType :=
    { isFiniteType := fun i => ⟨finite_generators_of_locallyFree F q hq i i (hU i)⟩ }
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.mk.{u, u, u}
    (C := TopologicalSpace.Opens X) (J := Opens.grothendieckTopology X)
    (R := X.ringCatSheaf) (M := F) ⟨q, hq, hfinite⟩

theorem finiteLocallyFreeData_stalkFree
    {X : Scheme.{u}} (F : X.Modules) (q : F.LocalGeneratorsData.{u})
    (hq : q.IsLocallyFreeData) (x : X) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  obtain ⟨i, hxi⟩ := exists_mem_localGeneratorsData q x
  let t := localGeneratorsTrivialization F q hq i
  obtain ⟨e⟩ := LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp
    X.toTopCat X.sheaf F x hxi t
  let k : Type u := ToType (X.presheaf.stalk x)
  let : Module k (ToType (F.presheaf.stalk x)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let b : Module.Basis t.ι k (t.ι →₀ k) := Finsupp.basisSingleOne
  exact Module.Free.of_basis (b.map e.symm)

private theorem finiteLocallyFreeData_flat
    {X : Scheme.{u}} (F : X.Modules) (q : F.LocalGeneratorsData.{u})
    (hq : q.IsLocallyFreeData) [F.IsQuasicoherent] :
    AlgebraicGeometry.SheafOfModules.IsFlat (C := TopologicalSpace.Opens X.toTopCat)
      (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) F := by
  apply (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat X.sheaf F).2
  intro x
  let R := ToType (X.presheaf.stalk x)
  let M := ToType (F.presheaf.stalk x)
  let : Module R M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  have hfree : Module.Free R M :=
    finiteLocallyFreeData_stalkFree F q hq x
  let : Module.Free R M := hfree
  change Module.Flat R M
  exact Module.Flat.of_free

/-- The fibre rank at `x` is the cardinality of any basis of the stalk at `x`. -/
private theorem fiberRank_eq_card_of_basis {X : Scheme.{u}} (F : X.Modules) (x : X)
    {ι : Type u} [Finite ι]
    (b : Module.Basis ι (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x))) :
    fiberRank F x = Nat.card ι := by
  let : Fintype ι := Fintype.ofFinite _
  let : Algebra (ToType (X.presheaf.stalk x)) (X.residueField x) :=
    (X.residue x).hom.toAlgebra
  change Module.finrank (X.residueField x)
    (X.residueField x ⊗[ToType (X.presheaf.stalk x)]
      ToType (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) = Nat.card ι
  rw [Nat.card_eq_fintype_card]
  exact Module.finrank_eq_card_basis (b.baseChange (X.residueField x))

/-- The fibre rank of a trivialised sheaf at a point of the trivialising open is the size of
the index set. The trivialisation is a variable so that nothing has to be unfolded. -/
private theorem fiberRank_eq_card_of_trivializationAux {X : Scheme.{u}} (F : X.Modules)
    {U : X.Opens} (x : X) (hxU : x ∈ U) (ι : Type u) [Finite ι]
    (t : LocallyFreeRank.Trivialization X.toTopCat
      (LocallyFreeRank.toRingSheaf X.toTopCat X.sheaf) F U) (hι : t.ι = ι) :
    fiberRank F x = Nat.card ι := by
  obtain ⟨bF⟩ := nonempty_stalk_basis_of F x hxU ι t hι
  exact fiberRank_eq_card_of_basis F x bF

public theorem fiberRank_eq_card_of_trivialization
    {X : Scheme.{u}} (F : X.Modules) (q : F.LocalGeneratorsData.{u})
    (hq : q.IsLocallyFreeData) (i : q.I) (x : X) (hxi : x ∈ q.X i)
    [Finite (q.generators i).I] :
    fiberRank F x = Nat.card (q.generators i).I :=
  fiberRank_eq_card_of_trivializationAux F x hxi (q.generators i).I
    (localGeneratorsTrivialization F q hq i) (localGeneratorsTrivialization_ι F q hq i)

section

private lemma finite_germ_lifts {C : Type v} [Category.{u} C] [HasColimits C]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
    [PreservesFilteredColimits (forget C)] {Y : TopCat.{u}}
    (G : TopCat.Presheaf C Y) {I : Type*} [Finite I] (x : Y)
    (m : I → ToType (G.stalk x)) {V : Opens Y} (hxV : x ∈ V) :
    ∃ (U : Opens Y) (_hUV : U ≤ V) (hxU : x ∈ U)
      (s : I → ToType (G.obj (op U))),
      ∀ i, (ConcreteCategory.hom (G.germ U x hxU)) (s i) = m i := by
  classical
  choose U hU s hs using fun i => G.exists_germ_eq (m i)
  let W := V ⊓ ⨅ i, U i
  have hxW : x ∈ W := ⟨hxV, by
    rw [Opens.coe_iInf]; exact Set.mem_iInter.mpr hU⟩
  have hWU (i : I) : W ≤ U i := inf_le_right.trans (iInf_le U i)
  refine ⟨W, inf_le_left, hxW,
    fun i => (ConcreteCategory.hom (G.map (homOfLE (hWU i)).op)) (s i), ?_⟩
  intro i
  rw [TopCat.Presheaf.germ_res_apply]
  exact hs i

private lemma germ_smul_section {X : Scheme.{u}} (F : X.Modules)
    (x : X) (U : X.Opens) (hx : x ∈ U) (r : X.ringCatSheaf.obj.obj (op U))
    (m : F.val.obj (op U)) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    TopCat.Presheaf.germ F.val.presheaf U x hx (r • m) =
      X.presheaf.germ U x hx r • TopCat.Presheaf.germ F.val.presheaf U x hx m :=
  PresheafOfModules.germ_smul (R := X.presheaf) F.val x U hx r m

private lemma germ_map_section {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Opens} (f : U ⟶ V) (x : X) (hx : x ∈ U) (s : F.val.obj (op V)) :
    TopCat.Presheaf.germ F.val.presheaf U x hx (F.val.map f.op s) =
      TopCat.Presheaf.germ F.val.presheaf V x (leOfHom f hx) s :=
  TopCat.Presheaf.germ_res_apply F.val.presheaf f x hx s

private lemma germ_smul_map_section {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Opens} (f : U ⟶ V) (x : X) (hx : x ∈ U) (r : X.ringCatSheaf.obj.obj (op U))
    (s : F.val.obj (op V)) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    TopCat.Presheaf.germ F.val.presheaf U x hx (r • F.val.map f.op s) =
      X.presheaf.germ U x hx r •
        TopCat.Presheaf.germ F.val.presheaf V x (leOfHom f hx) s :=
  (germ_smul_section F x U hx r _).trans
    (congrArg _ (germ_map_section F f x hx s))

private lemma val_map_comp_apply {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
    (f : W ⟶ V) (g : V ⟶ U) (s : F.val.obj (op U)) :
    F.val.presheaf.map f.op (F.val.presheaf.map g.op s)
      = F.val.presheaf.map (f ≫ g).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]

private lemma exists_combination_of_germ_mem_span {X : Scheme.{u}} (F : X.Modules)
    {I : Type u} [Fintype I] {V U : X.Opens} (s : I → F.val.obj (op V))
    (t : F.val.obj (op U)) (x : X) (hxV : x ∈ V) (hxU : x ∈ U)
    (h :
      letI : Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      TopCat.Presheaf.germ F.val.presheaf U x hxU t ∈ Submodule.span (X.presheaf.stalk x)
        (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf V x hxV (s i))) :
    ∃ (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V), x ∈ W ∧
      ∃ c : I → X.ringCatSheaf.obj.obj (op W),
        F.val.map (homOfLE hWU).op t =
          ∑ i, @HSMul.hSMul ↑(X.ringCatSheaf.obj.obj (op W)) ↑(F.val.obj (op W))
            ↑(F.val.obj (op W)) _ (c i) (F.val.map (homOfLE hWV).op (s i)) := by
  let : Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) F.val x
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp h
  obtain ⟨W, hW, hxW, a, ha⟩ := finite_germ_lifts X.presheaf x c
    (V := U ⊓ V) ⟨hxU, hxV⟩
  have hWU := hW.trans inf_le_left
  have hWV := hW.trans inf_le_right
  let aW (i : I) : ↑(X.ringCatSheaf.obj.obj (op W)) := a i
  let sW (i : I) : ↑(F.val.obj (op W)) := F.val.map (homOfLE hWV).op (s i)
  have ha' (i : I) : X.presheaf.germ W x hxW (aW i) = c i := ha i
  have hterm (i : I) : TopCat.Presheaf.germ F.val.presheaf W x hxW (aW i • sW i)
      = c i • TopCat.Presheaf.germ F.val.presheaf V x hxV (s i) := by
    refine (germ_smul_map_section F (homOfLE hWV) x hxW (aW i) (s i)).trans ?_
    rw [ha' i]
  have hz : TopCat.Presheaf.germ F.val.presheaf W x hxW (∑ i, aW i • sW i) =
      TopCat.Presheaf.germ F.val.presheaf U x hxU t :=
    (map_sum _ _ _).trans ((Finset.sum_congr rfl fun i _ => hterm i).trans hc)
  obtain ⟨W', hxW', f, g, heq⟩ := TopCat.Presheaf.germ_eq F.val.presheaf x hxW hxU
    (∑ i, aW i • sW i) t hz
  refine ⟨W', leOfHom g, (leOfHom f).trans hWV, hxW',
    fun i => X.ringCatSheaf.obj.map f.op (aW i), ?_⟩
  refine (congrArg (fun q : W' ⟶ U => F.val.presheaf.map q.op t)
    (Subsingleton.elim (homOfLE (leOfHom g)) g)).trans ?_
  refine heq.symm.trans ?_
  refine (map_sum _ _ _).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (PresheafOfModules.map_smul F.val f.op (aW i) (sW i)).trans ?_
  refine congrArg (fun w : ↑(F.val.obj (op W')) =>
    X.ringCatSheaf.obj.map f.op (aW i) • w) ?_
  refine (val_map_comp_apply F f (homOfLE hWV) (s i)).trans ?_
  exact congrArg (fun q : W' ⟶ V => F.val.presheaf.map q.op (s i))
    (Subsingleton.elim (f ≫ homOfLE hWV) (homOfLE ((leOfHom f).trans hWV)))

private lemma span_germs_of_local_generators {X : Scheme.{u}} (F : X.Modules)
    {J : Type u} [Fintype J] {V : X.Opens} (t : J → F.val.obj (op V))
    (ht : Stacks.SheafOfModules.LocallySurjective.LocalLinComb (X := X.toRingedSpace) V t)
    (y : X) (hy : y ∈ V) :
    letI : Module (X.presheaf.stalk y) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val y
    Submodule.span (X.presheaf.stalk y)
      (Set.range fun j => TopCat.Presheaf.germ F.val.presheaf V y hy (t j)) = ⊤ := by
  let : Module (X.presheaf.stalk y) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) F.val y
  refine Submodule.eq_top_iff'.mpr fun m => ?_
  obtain ⟨U, hUV, hyU, s, hs⟩ := TopCat.Presheaf.exists_le_germ_eq F.val.presheaf m hy
  obtain ⟨W, hWU, hyW, c, hc⟩ := ht U hUV s y hyU
  have hm : m = ∑ j : J, X.presheaf.germ W y hyW (c j) •
      TopCat.Presheaf.germ F.val.presheaf V y hy (t j) := by
    refine hs.symm.trans ?_
    refine (TopCat.Presheaf.germ_res_apply F.val.presheaf (homOfLE hWU) y hyW s).symm.trans ?_
    refine (congrArg (fun z => TopCat.Presheaf.germ F.val.presheaf W y hyW z) hc).trans ?_
    refine (map_sum _ _ _).trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    exact germ_smul_map_section F (homOfLE (le_trans hWU hUV)) y hyW (c j) (t j)
  rw [hm]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

private lemma span_germs_near {X : Scheme.{u}} (F : X.Modules) [F.IsFiniteType]
    {I : Type u} [Finite I] {U : X.Opens} (s : I → F.val.obj (op U))
    (x : X) (hxU : x ∈ U)
    (hx :
      letI : Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf U x hxU (s i)) = ⊤) :
    ∃ (W : X.Opens) (hWU : W ≤ U), x ∈ W ∧ ∀ y (hy : y ∈ W),
      letI : Module (X.presheaf.stalk y) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val y
      Submodule.span (X.presheaf.stalk y)
        (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf U y (hWU hy) (s i)) = ⊤ := by
  classical
  let : Fintype I := Fintype.ofFinite _
  obtain ⟨V, hxV, J, hJ, t, ht⟩ :=
    Stacks.SheafOfModules.LocallySurjective.exists_local_generators
      (X := X.toRingedSpace) (F := F) inferInstance x
  let := hJ
  have hmem (j : J) :
      letI : Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      TopCat.Presheaf.germ F.val.presheaf V x hxV (t j) ∈ Submodule.span (X.presheaf.stalk x)
        (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf U x hxU (s i)) := by
    rw [hx]; trivial
  choose W hWV hWU hxW c hc using fun j =>
    exists_combination_of_germ_mem_span F s (t j) x hxU hxV (hmem j)
  let Z := (U ⊓ V) ⊓ ⨅ j, W j
  have hZU : Z ≤ U := inf_le_left.trans inf_le_left
  have hZV : Z ≤ V := inf_le_left.trans inf_le_right
  have hZW (j : J) : Z ≤ W j := inf_le_right.trans (iInf_le W j)
  refine ⟨Z, hZU, ⟨⟨hxU, hxV⟩, by
    rw [Opens.coe_iInf]; exact Set.mem_iInter.mpr hxW⟩, ?_⟩
  intro y hy
  let : Module (X.presheaf.stalk y) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) F.val y
  rw [← top_le_iff, ← span_germs_of_local_generators F t ht y (hZV hy)]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  change TopCat.Presheaf.germ F.val.presheaf V y (hZV hy) (t j) ∈ _
  rw [← germ_map_section F (homOfLE (hWV j)) y (hZW j hy) (t j), hc j, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hterm : TopCat.Presheaf.germ F.val.presheaf (W j) y (hZW j hy)
      (@HSMul.hSMul ↑(X.ringCatSheaf.obj.obj (op (W j))) ↑(F.val.obj (op (W j)))
        ↑(F.val.obj (op (W j))) _ (c j i) (F.val.map (homOfLE (hWU j)).op (s i)))
      = X.presheaf.germ (W j) y (hZW j hy) (c j i) •
        TopCat.Presheaf.germ F.val.presheaf U y (hZU hy) (s i) :=
    germ_smul_map_section F (homOfLE (hWU j)) y (hZW j hy) (c j i) (s i)
  rw [hterm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private lemma linearIndependent_of_span_of_card_eq {R : Type*} [CommRing R] [Nontrivial R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    {I : Type*} [Fintype I] (s : I → M)
    (hs : Submodule.span R (Set.range s) = ⊤) (hr : Fintype.card I = Module.finrank R M) :
    LinearIndependent R s := by
  let f := Finsupp.linearCombination R s
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hs
  let e : (I →₀ R) ≃ₗ[R] M := LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_finsupp_self]; exact hr)
  have hinj := Module.End.injective_of_surjective R (I →₀ R)
    (f := e.symm.toLinearMap.comp f) (e.symm.surjective.comp hf)
  exact fun a b hab => hinj (congrArg e.symm hab)

private def sectionOver {X : Scheme.{u}} (F : X.Modules) {U : X.Opens}
    (s : F.val.obj (op U)) : (F.over U).sections :=
  PresheafOfModules.sectionsMk
    (fun V => F.val.map V.unop.hom.op s) (by
      intro V W f
      change F.val.presheaf.map f.unop.left.op (F.val.presheaf.map V.unop.hom.op s) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Over.w]
      rfl)

private lemma freeHomOver_apply {X : Scheme.{u}} (F : X.Modules) {U : X.Opens}
    {I : Type u} (s : I → F.val.obj (op U)) (i : I) (V : (Over U)ᵒᵖ) :
    ((F.over U).freeHomEquiv.symm (fun i => sectionOver F (s i))).val.app V
      ((SheafOfModules.freeSection i).val V) = F.val.map V.unop.hom.op (s i) := by
  have h := SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
    (fun i => sectionOver F (s i)) i
  exact congrArg (fun t => t.val V) h

private lemma isIso_freeHomOver_of_stalkwise_basis {X : Scheme.{u}} (F : X.Modules)
    {U : X.Opens} {I : Type u} [Finite I] (s : I → F.val.obj (op U))
    (hs : ∀ x (hx : x ∈ U),
      letI : Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf U x hx (s i)) = ⊤)
    (hli : ∀ x (hx : x ∈ U),
      letI : Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      LinearIndependent (X.presheaf.stalk x)
        (fun i => TopCat.Presheaf.germ F.val.presheaf U x hx (s i))) :
    IsIso ((F.over U).freeHomEquiv.symm (fun i => sectionOver F (s i))) := by
  classical
  let : Fintype I := Fintype.ofFinite _
  let P := SheafOfModules.free (R := X.ringCatSheaf.over U) I
  let f : P ⟶ F.over U := (F.over U).freeHomEquiv.symm (fun i => sectionOver F (s i))
  have hf (i : I) (V : (Over U)ᵒᵖ) :
      f.val.app V ((SheafOfModules.freeSection i).val V) =
        F.val.map V.unop.hom.op (s i) := freeHomOver_apply F s i V
  have hinj (V : (Over U)ᵒᵖ) : Function.Injective (f.val.app V) := by
    apply (injective_iff_map_eq_zero _).2
    intro a ha
    have hspan := SheafOfModules.free_image_mem_span
      (R := X.ringCatSheaf.over U) (M := P) (fun i : I => SheafOfModules.freeSection i) V a
    have hid : P.freeHomEquiv.symm (fun i : I => SheafOfModules.freeSection i) = 𝟙 P :=
      P.freeHomEquiv.symm_apply_apply (𝟙 P)
    rw [hid] at hspan
    change a ∈ _ at hspan
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hspan
    let cV (i : I) : ↑(X.ringCatSheaf.obj.obj (op V.unop.left)) := c i
    let sV (i : I) : ↑(F.val.obj (op V.unop.left)) := F.val.map V.unop.hom.op (s i)
    have heq : (∑ i, cV i • sV i) = 0 := by
      have h := congrArg (f.val.app V) hc
      simp only [map_sum, map_smul, hf, ha] at h
      exact h
    have hc0 (i : I) : c i = 0 := by
      apply TopCat.Presheaf.section_ext X.sheaf V.unop.left
      intro x hx
      let : Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      have hg := congrArg (TopCat.Presheaf.germ F.val.presheaf V.unop.left x hx) heq
      have hterm (j : I) :
          TopCat.Presheaf.germ F.val.presheaf V.unop.left x hx (cV j • sV j) =
          X.presheaf.germ V.unop.left x hx (cV j) •
            TopCat.Presheaf.germ F.val.presheaf U x (leOfHom V.unop.hom hx) (s j) := by
        exact germ_smul_map_section F V.unop.hom x hx (cV j) (s j)
      simp only [map_sum, map_zero, hterm] at hg
      have hz := (Fintype.linearIndependent_iff.mp (hli x (leOfHom V.unop.hom hx))) _ hg i
      change X.presheaf.germ V.unop.left x hx (cV i) =
        X.presheaf.germ V.unop.left x hx 0
      exact hz.trans (map_zero _).symm
    rw [← hc]
    simp [hc0]
  have : Mono f.val := PresheafOfModules.mono_of_injective (fun {V} => hinj V)
  have : Mono f := (SheafOfModules.forget _).mono_of_mono_map (show Mono f.val from inferInstance)
  let A := SheafOfModules.toSheaf (X.ringCatSheaf.over U)
  have : Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X).over U)
      (A.map f).hom := by
    constructor
    intro V t
    rw [GrothendieckTopology.mem_over_iff]
    intro x hx
    have hmem :
        letI : Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
        TopCat.Presheaf.germ F.val.presheaf V.left x hx t ∈ Submodule.span (X.presheaf.stalk x)
          (Set.range fun i =>
            TopCat.Presheaf.germ F.val.presheaf U x (leOfHom V.hom hx) (s i)) := by
      rw [hs]; trivial
    obtain ⟨W, hWV, hWU, hxW, c, hc⟩ :=
      exists_combination_of_germ_mem_span F s t x (leOfHom V.hom hx) hx hmem
    let W' : Over U := Over.mk (homOfLE hWU)
    let g : W' ⟶ V := Over.homMk (homOfLE hWV)
    let cW (i : I) : ↑((X.ringCatSheaf.over U).obj.obj (op W')) := c i
    refine ⟨W, homOfLE hWV, ?_, hxW⟩
    refine ⟨W', g, 𝟙 W, ?_, rfl⟩
    let a : P.val.obj (op W') := ∑ i,
      @SMul.smul ((X.ringCatSheaf.over U).obj.obj (op W')) (P.val.obj (op W'))
        (P.val.obj (op W')).isModule.toSMul (c i)
        ((SheafOfModules.freeSection (R := X.ringCatSheaf.over U) i).val (op W'))
    refine ⟨a, ?_⟩
    change f.val.app (op W') a = F.val.map (homOfLE hWV).op t
    dsimp only [a]
    rw [map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hc.symm
    refine ((f.val.app (op W')).hom.map_smul (cW i) _).trans ?_
    exact congrArg (fun m : ↑((F.over U).val.obj (op W')) => cW i • m) (hf i (op W'))
  have : Epi (A.map f) :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat (A.map f)).mp inferInstance
  have : Epi f := A.epi_of_epi_map inferInstance
  exact isIso_of_mono_of_epi f

/-- For a finite type module with free stalk at `x`, the fibre rank at `x` is the rank of the
stalk. -/
lemma fiberRank_eq_finrank {X : Scheme.{u}} (F : X.Modules) (x : X)
    [F.IsFiniteType]
    (hfree :
      letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x)) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    fiberRank F x = Module.finrank (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  let A := ToType (X.presheaf.stalk x)
  let M := ToType (F.presheaf.stalk x)
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Module.Free A M := hfree
  let : Module.Finite A M := finite_stalk_of_finiteType X.sheaf F x
  let : IsLocalRing A := X.isLocalRing x
  let b := Module.Free.chooseBasis A M
  exact (fiberRank_eq_card_of_basis F x b).trans (Module.finrank_eq_nat_card_basis b).symm

private lemma locallyFree_of_free_stalks_of_locallyConstant_fiberRank
    {X : Scheme.{u}} (F : X.Modules) [F.IsFiniteType]
    (hfree : ∀ x : X,
      letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x))
    (hrank : IsLocallyConstant (fiberRank F)) : F.IsLocallyFree := by
  classical
  intro x
  let A := ToType (X.presheaf.stalk x)
  let M := ToType (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Module.Free A M := hfree x
  let : Module.Finite A M := finite_stalk_of_finiteType X.sheaf F x
  let : IsLocalRing A := X.isLocalRing x
  let b := Module.Free.chooseBasis A M
  let I := Module.Free.ChooseBasisIndex A M
  let : Fintype I := Fintype.ofFinite _
  obtain ⟨V, hVo, hxV, hV⟩ := (IsLocallyConstant.iff_exists_open _).mp hrank x
  obtain ⟨U, hUV, hxU, s, hs⟩ :=
    finite_germ_lifts F.val.presheaf x (fun i : I => b i) (V := ⟨V, hVo⟩) hxV
  obtain ⟨W, hWU, hxW, hW⟩ := span_germs_near F s x hxU (by
    simpa only [hs] using b.span_eq)
  let t : I → F.val.obj (op W) := fun i => F.val.map (homOfLE hWU).op (s i)
  have htspan (y : X) (hy : y ∈ W) :
      letI : Module (X.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val y
      Submodule.span (X.presheaf.stalk y)
        (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf W y hy (t i)) = ⊤ := by
    simpa only [t, germ_map_section] using hW y hy
  have htli (y : X) (hy : y ∈ W) :
      letI : Module (X.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val y
      LinearIndependent (X.presheaf.stalk y)
        (fun i => TopCat.Presheaf.germ F.val.presheaf W y hy (t i)) := by
    let : Module (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val y
    let : Module.Free (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) := hfree y
    let : Module.Finite (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
      finite_stalk_of_finiteType X.sheaf F y
    let : IsLocalRing (X.presheaf.stalk y) := X.isLocalRing y
    apply linearIndependent_of_span_of_card_eq
      (R := ToType (X.presheaf.stalk y))
      (M := ToType (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y)) _ (htspan y hy)
    calc
      Fintype.card I = Module.finrank A M := (Module.finrank_eq_card_basis b).symm
      _ = fiberRank F x := (fiberRank_eq_finrank F x (hfree x)).symm
      _ = fiberRank F y := (hV y (hUV (hWU hy))).symm
      _ = _ := fiberRank_eq_finrank F y (hfree y)
  let f := (F.over W).freeHomEquiv.symm (fun i => sectionOver F (t i))
  have : IsIso f := isIso_freeHomOver_of_stalkwise_basis F t htspan htli
  exact ⟨W, hxW, I, nonempty_restrict_iso_free F W (asIso f).symm⟩

end

/-- A quasi-coherent sheaf of modules on a scheme is finite locally free exactly
when it satisfies any of the five equivalent flatness, presentation, stalk, or
rank conditions.

`AlgebraicGeometry.Scheme.Modules.flat_finitePresentation_locallyFree_fiberRank_tfae` in
`StacksFrontier.AlgebraicGeometry.FiberRank.LocallyFree` carries the tag too, and states the same
list of five conditions without assuming quasi-coherence, so it implies this statement outright.
Both carry the tag: a Stacks tag is registered once per clause or part of its statement, and more
than one carrier is expected rather than a defect. -/
@[stacks 05P2, ega "III 7.3.4"]
theorem finiteLocallyFree_tfae {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] :
    List.TFAE [
      AlgebraicGeometry.SheafOfModules.IsFlat F ∧ F.IsFinitePresentation,
      F.IsFinitePresentation ∧
        (∀ x : X,
          letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
            PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
              (R := X.presheaf) F.val x
          Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x)),
      SheafOfModules.IsLocallyFree F ∧ F.IsFiniteType,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F,
      F.IsFiniteType ∧
        (∀ x : X,
          letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
            PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
              (R := X.presheaf) F.val x
          Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x)) ∧
        IsLocallyConstant (fiberRank F)] := by
  tfae_have 4 → 3 := by
    intro h
    obtain ⟨q : F.LocalGeneratorsData.{u}, hfree, hfinite⟩ :=
      h.exists_isFiniteLocallyFreeData
    let : q.IsLocallyFreeData := hfree
    have htype : SheafOfModules.IsFiniteType.{u, u, u} F := by
      exact SheafOfModules.IsFiniteType.mk.{u, u, u} ⟨q, hfinite⟩
    exact ⟨SheafOfModules.IsLocallyFree.mk.{u, u, u} (M := F) ⟨q, hfree⟩, htype⟩
  tfae_have 3 → 4 := by
    rintro ⟨hfree, htype⟩
    let : F.IsFiniteType := htype
    exact finiteLocallyFree_of_locallyFree_finiteType F
      ((isLocallyFree_iff_pointwiseLocallyFree F).mp hfree)
  tfae_have 2 → 3 := by
    rintro ⟨hfp, hstalk⟩
    let : F.IsFinitePresentation := hfp
    let : F.IsFiniteType :=
      SheafOfModules.instIsFiniteTypeOfIsFinitePresentation.{u, u, u} F
    refine ⟨(isLocallyFree_iff_pointwiseLocallyFree F).mpr ?_, inferInstance⟩
    intro x
    let A := ToType (X.presheaf.stalk x)
    let B := ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (X.sheaf.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x)
    let M := ToType (F.presheaf.stalk x)
    let : Module A M :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    let : Module B M :=
      PresheafOfModules.instModuleCarrierStalkRingCatCarrierAbPresheafOpensCarrier
        F.val x
    let : Module.Finite A M := finite_stalk_of_finiteType X.sheaf F x
    let eBA : B ≃+* A := commStalkRingEquivU X.sheaf.obj x
    let eAB := eBA.symm
    let : RingHomInvPair (↑eAB : A →+* B) (↑eBA : B →+* A) :=
      RingHomInvPair.of_ringEquiv eAB
    let : RingHomInvPair (↑eBA : B →+* A) (↑eAB : A →+* B) :=
      RingHomInvPair.of_ringEquiv eBA
    have hsmul (s : B) (m : M) : eBA s • m = s • m :=
      comm_smul_eq_at_stalk X.sheaf.obj x F.val s m
    let eM : M ≃ₛₗ[(↑eAB : A →+* B)] M := {
      toFun := id
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
    have hfreeB : Module.Free B M := Module.Free.of_equiv eM
    have hfiniteB : Module.Finite B M :=
      Module.Finite.of_surjective (R := A) (S := B) (M := M) (P := M)
        (σ := (↑eAB : A →+* B)) eM eM.surjective
    let : Module.Free B M := hfreeB
    let : Module.Finite B M := hfiniteB
    let b := Module.Free.chooseBasis B M
    let I := Module.Free.ChooseBasisIndex B M
    let : Fintype I := Fintype.ofFinite _
    let r := Fintype.card I
    let e := (Fintype.equivFin I).trans Equiv.ulift.symm
    have hx : Nonempty (M ≃ₗ[B] (ULift.{u} (Fin r) →₀ B)) :=
      ⟨(b.reindex e).repr⟩
    obtain ⟨U, hxU, hIso⟩ := Stacks.SheafOfModules.exists_iso_free_over_of_stalk_iso_free
      F hfp x r hx
    obtain ⟨hIso⟩ := hIso
    exact ⟨U, hxU, ULift.{u} (Fin r), nonempty_restrict_iso_free F U hIso⟩
  tfae_have 1 → 2 := by
    rintro ⟨hflat, hfp⟩
    let : F.IsFinitePresentation := hfp
    let : F.IsFiniteType :=
      SheafOfModules.instIsFiniteTypeOfIsFinitePresentation.{u, u, u} F
    refine ⟨hfp, ?_⟩
    intro x
    let A := ToType (X.presheaf.stalk x)
    let M := ToType (F.presheaf.stalk x)
    let : Module A M :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    let : Module.Finite A M := finite_stalk_of_finiteType X.sheaf F x
    have hflatx := (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat X.sheaf F).mp hflat x
    let : Module.Flat A M := hflatx
    let : IsLocalRing A := X.isLocalRing x
    exact Module.free_of_flat_of_isLocalRing
  tfae_have 4 → 2 := by
    intro h
    obtain ⟨q : F.LocalGeneratorsData.{u}, hfree, hfinite⟩ :=
      h.exists_isFiniteLocallyFreeData
    refine ⟨finitePresentation_of_finiteLocallyFreeData F q hfree hfinite, ?_⟩
    intro x
    exact finiteLocallyFreeData_stalkFree F q hfree x
  tfae_have 4 → 5 := by
    intro h
    obtain ⟨q : F.LocalGeneratorsData.{u}, hfree, hfinite⟩ :=
      h.exists_isFiniteLocallyFreeData
    have htype : F.IsFiniteType := by
      exact SheafOfModules.IsFiniteType.mk.{u, u, u}
        ⟨q, hfinite⟩
    refine ⟨htype, ?_, ?_⟩
    · intro x
      exact finiteLocallyFreeData_stalkFree F q hfree x
    · rw [IsLocallyConstant.iff_exists_open]
      intro x
      obtain ⟨i, hxi⟩ := exists_mem_localGeneratorsData q x
      let : Finite (q.generators i).I := hfinite.isFiniteType i |>.finite
      refine ⟨q.X i, (q.X i).isOpen, hxi, ?_⟩
      intro y hy
      exact (fiberRank_eq_card_of_trivialization F q hfree i y hy).trans
        (fiberRank_eq_card_of_trivialization F q hfree i x hxi).symm
  tfae_have 4 → 1 := by
    intro h
    obtain ⟨q : F.LocalGeneratorsData.{u}, hfree, hfinite⟩ :=
      h.exists_isFiniteLocallyFreeData
    exact ⟨finiteLocallyFreeData_flat F q hfree,
      finitePresentation_of_finiteLocallyFreeData F q hfree hfinite⟩
  tfae_have 5 → 3 := by
    rintro ⟨htype, hfree, hrank⟩
    let : F.IsFiniteType := htype
    exact ⟨(isLocallyFree_iff_pointwiseLocallyFree F).mpr
      (locallyFree_of_free_stalks_of_locallyConstant_fiberRank F hfree hrank), htype⟩
  tfae_finish

end Stacks.FiniteLocallyFree.ModuleTFAE
