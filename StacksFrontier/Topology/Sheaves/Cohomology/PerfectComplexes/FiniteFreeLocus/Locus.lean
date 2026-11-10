module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.Topology.Sheaves.Module
public import Mathlib.Topology.Sheaves.Over
public import Mathlib.Topology.Sheaves.Points
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftColimits
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksFrontier.Algebra.Homology.StrictlyPerfectLiftModuleUniverse
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.FiniteFreeLocus.UniverseLift

/-!
# The finite free locus and the stalks of the opcycles of a strictly perfect complex

Let `(X, 𝒪_X)` be a ringed space. This file defines the set of points `x` at which every
cohomology stalk `H^i(E)_x` of an object `E` of `D(𝒪_X)` is a finite free `𝒪_{X, x}`-module,
the locus of [Stacks, Tag 0GT1], together with the stalks and the finite local freeness used to
state it, and proves the stalk-level facts about strictly perfect complexes that the proof of
the tag rests on.

## Main definitions

* `Stacks.Cohomology.PerfectComplexes.cohomologyFiniteFreeLocus`: the set of points at which
  all cohomology stalks of an object of `D(𝒪_X)` are finite free.
* `Stacks.Cohomology.PerfectComplexes.moduleSheafStalk`: the stalk of an `𝒪_X`-module, as a
  module over the stalk of the structure sheaf of rings.
* `Stacks.Cohomology.PerfectComplexes.IsFiniteLocallyFree`: finite local freeness of an
  `𝒪_X`-module, i.e. `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` of the lifted
  module sheaf.

## Implementation notes

The stalk of the structure sheaf is `structureSheafStalk`, the colimit over `OpenNhds x` of
the universe-lifted sections, and the stalk of a module is `moduleStalkFunctor`. When the two
universes agree, `structureSheafStalkIso` identifies the former with `X.presheaf.stalk x` and
transports its local-ring instance, so the hypothesis of the tag can be supplied in its usual
form.

The terms of a strictly perfect complex `P` are direct summands of finite free modules, hence
so are its opcycles in each degree; at a point with local stalk at which all cohomology stalks
of `P` are finite free, the stalks of these opcycles are finite free, and the opcycles of the
universe lift of `P` are of finite presentation.

## References

* [Stacks Project, Tag 0GT1](https://stacks.math.columbia.edu/tag/0GT1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
  AlgebraicGeometry.RingedSpace.PseudoCoherence

namespace Stacks.Cohomology.PerfectComplexes

universe u v d

attribute [local instance] HasDerivedCategory.standard

/-- `RingCat.{max u v}` has all colimits indexed by `v`-small categories. -/
local instance : HasColimitsOfSize.{v, v} RingCat.{max u v} :=
  hasColimitsOfSizeShrink.{v, v, max u v, max u v} _

/-- The stalk at `x` of the structure sheaf of rings of `X`, formed as the colimit of the
universe-lifted sections over the open neighbourhoods of `x`. -/
abbrev structureSheafStalk (X : RingedSpace.{u, v}) (x : X) : RingCat.{max u v} :=
  colimit ((OpenNhds.inclusion x).op ⋙ (structureSheafULift X).obj)

/-- The stalk at `x`, as a functor on `𝒪_X`-modules valued in modules over the stalk
`structureSheafStalk X x` of the structure sheaf. -/
abbrev moduleStalkFunctor (X : RingedSpace.{u, v}) (x : X) :
    OXMod.{u, v} X ⥤ ModuleCat.{max u v} ↑(structureSheafStalk X x) :=
  liftModulesFunctor X ⋙
    sheafColimitFunctor (structureSheafULift X) (OpenNhds.inclusion x).op

/-- The stalk at `x` of an `𝒪_X`-module, as a module over `structureSheafStalk X x`. -/
abbrev moduleSheafStalk {X : RingedSpace.{u, v}} (M : OXMod.{u, v} X) (x : X) :
    ModuleCat.{max u v} ↑(structureSheafStalk X x) :=
  (moduleStalkFunctor X x).obj M

/-- Finite local freeness of an `𝒪_X`-module, expressed through
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` for its universe lift. -/
abbrev IsFiniteLocallyFree {X : RingedSpace.{u, v}} (M : OXMod.{u, v} X) : Prop := by
  letI (U : Opens X) : HasSheafify ((Opens.grothendieckTopology X.carrier).over U)
      AddCommGrpCat.{max u v} :=
    hasSheafifyEssentiallySmallSite.{v, max u v, v, (max u v) + 1, max u v} _ _
  letI (U : Opens X) : ((Opens.grothendieckTopology X.carrier).over U).WEqualsLocallyBijective
      AddCommGrpCat.{max u v} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, max u v, v,
      (max u v) + 1, max u v} _
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (moduleSheafULift M)

/-- When the universe of the rings is the universe of the space, the stalk formed from the
universe-lifted sections is the stalk of the structure sheaf. -/
def structureSheafStalkIso (X : RingedSpace.{u, u}) (x : X) :
    structureSheafStalk X x ≅ (forget₂ CommRingCat RingCat).obj (X.presheaf.stalk x) := by
  let e : (OpenNhds.inclusion x).op ⋙ (structureSheafULift X).obj ≅
      (OpenNhds.inclusion x).op ⋙ (structureSheafOfRings X).obj :=
    NatIso.ofComponents (fun U => ULift.ringEquiv.toRingCatIso) (by intros; rfl)
  exact (HasColimit.isoOfNatIso e) ≪≫
    (preservesColimitIso (forget₂ CommRingCat RingCat)
      ((OpenNhds.inclusion x).op ⋙ X.presheaf)).symm

/-- If the stalks of `𝒪_X` are local rings, so are the stalks formed from the
universe-lifted sections. -/
instance (X : RingedSpace.{u, u}) (x : X) [IsLocalRing (X.presheaf.stalk x)] :
    IsLocalRing (structureSheafStalk X x) :=
  (structureSheafStalkIso X x).symm.ringCatIsoToRingEquiv.isLocalRing

/-- The set of points at which every cohomology sheaf of an object of `D(𝒪_X)` has a
finite free stalk. -/
@[stacks 0GT1 "the locus"]
def cohomologyFiniteFreeLocus {X : RingedSpace.{u, v}}
    [HasDerivedCategory.{d} (OXMod.{u, v} X)]
    (E : DerivedCategory (OXMod.{u, v} X)) : Set X :=
  {x | ∀ i : ℤ,
    let M := (DerivedCategory.homologyFunctor (OXMod.{u, v} X) i).obj E
    Module.Finite (structureSheafStalk X x) (moduleSheafStalk M x) ∧
    Module.Free (structureSheafStalk X x) (moduleSheafStalk M x)}


/-- The functor between the categories of open neighbourhoods induced by an open embedding of
an open subset is final after passing to opposite categories. -/
private lemma final_functorNhds_op {X : TopCat.{v}} (U : Opens X)
    (y : ((Opens.toTopCat X).obj U : Type v)) : (U.isOpenEmbedding.functorNhds y).op.Final := by
  have : (U.isOpenEmbedding.functorNhds y).Initial :=
    Functor.initial_of_adjunction (U.isOpenEmbedding.adjunctionNhds y)
  infer_instance

/-- Finite freeness of the colimit of a module diagram is unchanged by restricting both the ring
and the module diagram along a final functor. -/
private lemma finite_free_colimit_whisker_iff
    {J J' : Type v} [SmallCategory J] [SmallCategory J'] [IsFiltered J] [IsFiltered J']
    (G : J ⥤ J') [G.Final] (A : J' ⥤ RingCat.{max u v}) (B : J' ⥤ Ab.{max u v})
    (B' : J ⥤ Ab.{max u v}) (eB : B' ≅ G ⋙ B)
    [∀ j, Module ((G ⋙ A).obj j) (B'.obj j)] [Module ↑(colimit A) ↑(colimit B)]
    (hB : ∀ {i j} (f : i ⟶ j) r m,
      B'.map f (r • m) = (G ⋙ A).map f r • B'.map f m)
    (hι : ∀ j (r : (G ⋙ A).obj j) (m : B'.obj j),
      (colimit.ι B (G.obj j)).hom (eB.hom.app j (r • m)) =
        (colimit.ι A (G.obj j)).hom r • (colimit.ι B (G.obj j)).hom (eB.hom.app j m)) :
    letI : Module ↑(colimit (G ⋙ A)) ↑(colimit B') :=
      IsColimit.module (G ⋙ A) B' hB (colimit.isColimit _) (colimit.isColimit _)
    (Module.Finite ↑(colimit (G ⋙ A)) ↑(colimit B') ∧
      Module.Free ↑(colimit (G ⋙ A)) ↑(colimit B')) ↔
    (Module.Finite ↑(colimit A) ↑(colimit B) ∧ Module.Free ↑(colimit A) ↑(colimit B)) := by
  let : Module ↑(colimit (G ⋙ A)) ↑(colimit B') :=
    IsColimit.module (G ⋙ A) B' hB (colimit.isColimit _) (colimit.isColimit _)
  let cR : Cocone (G ⋙ A) := (colimit.cocone A).whisker G
  let cM : Cocone B' := (Cocone.precompose eB.hom).obj ((colimit.cocone B).whisker G)
  let hcR : IsColimit cR := (Functor.Final.isColimitWhiskerEquiv G _).symm (colimit.isColimit A)
  let hcM : IsColimit cM := (IsColimit.precomposeHomEquiv eB _).symm
    ((Functor.Final.isColimitWhiskerEquiv G _).symm (colimit.isColimit B))
  let : Module cR.pt cM.pt := ‹Module ↑(colimit A) ↑(colimit B)›
  let e := colimitModuleEquiv (G ⋙ A) B' hB cR hcR cM hcM hι
  let q := ((colimit.isColimit (G ⋙ A)).coconePointUniqueUpToIso hcR).ringCatIsoToRingEquiv
  let : RingHomInvPair q.toRingHom q.symm.toRingHom := RingHomInvPair.of_ringEquiv q
  let : RingHomInvPair q.symm.toRingHom q.toRingHom := RingHomInvPair.of_ringEquiv_symm q
  refine ⟨fun ⟨_, _⟩ => ?_, fun h => ?_⟩
  · change Module.Finite ↑cR.pt ↑cM.pt ∧ Module.Free ↑cR.pt ↑cM.pt
    exact ⟨Module.Finite.of_surjective e.toLinearMap e.surjective, Module.Free.of_equiv e⟩
  · let : Module.Finite cR.pt cM.pt := h.1
    let : Module.Free cR.pt cM.pt := h.2
    exact ⟨Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective,
      Module.Free.of_equiv e.symm⟩

/-- A sheaf of modules isomorphic to a finite free one on an open set has finite free stalks at
the points of that open set. -/
lemma finite_free_stalkColimit_of_chart
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    (M : SheafOfModules.{max u v} R) (U : Opens X) (x : U)
    [HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{max u v}]
    [((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (I : Type (max u v)) [Finite I] (e : M.over U ≅ SheafOfModules.free I) :
    Module.Finite ↑(colimit ((OpenNhds.inclusion (x : X)).op ⋙ R.obj))
      ((sheafColimitFunctor R (OpenNhds.inclusion (x : X)).op).obj M) ∧
    Module.Free ↑(colimit ((OpenNhds.inclusion (x : X)).op ⋙ R.obj))
      ((sheafColimitFunctor R (OpenNhds.inclusion (x : X)).op).obj M) := by
  let F := (OpenNhds.inclusion (X := TopCat.of U) x ⋙ U.overEquivalence.inverse).op
  let A := (OpenNhds.inclusion (x : X)).op ⋙ R.obj
  let N := (OpenNhds.inclusion (x : X)).op ⋙ M.val.presheaf
  let T := sheafColimitFunctor (R.over U) F
  let G : (OpenNhds (X := TopCat.of U) x)ᵒᵖ ⥤ (OpenNhds (x : X))ᵒᵖ :=
    (U.isOpenEmbedding.functorNhds (opensPoint U x)).op
  have : G.Final := final_functorNhds_op U (opensPoint U x)
  let (j : (OpenNhds (x : X))ᵒᵖ) : Module (A.obj j) (N.obj j) :=
    (M.val.obj ((OpenNhds.inclusion (x : X)).op.obj j)).isModule
  let (j : (OpenNhds (X := TopCat.of U) x)ᵒᵖ) :
      Module ((G ⋙ A).obj j) ((F ⋙ (M.over U).val.presheaf).obj j) :=
    ((M.over U).val.obj (F.obj j)).isModule
  let : Module ↑(colimit A) ↑(colimit N) :=
    ((sheafColimitFunctor R (OpenNhds.inclusion (x : X)).op).obj M).isModule
  have h := finite_free_sheafColimit_free (R.over U) F I
  let := h.1
  let := h.2
  have h' : Module.Finite ↑(colimit (F ⋙ (R.over U).obj)) ↑(T.obj (M.over U)) ∧
      Module.Free ↑(colimit (F ⋙ (R.over U).obj)) ↑(T.obj (M.over U)) :=
    ⟨Module.Finite.equiv (T.mapIso e).symm.toLinearEquiv,
      Module.Free.of_equiv (T.mapIso e).symm.toLinearEquiv⟩
  exact (finite_free_colimit_whisker_iff G A N (F ⋙ (M.over U).val.presheaf)
    (NatIso.ofComponents (fun _ => Iso.refl _))
    (fun f r m => (M.over U).val.map_smul _ _ _)
    (fun j r m => IsColimit.ι_smul A N (fun f r m => M.val.map_smul _ _ _)
      (colimit.isColimit A) (colimit.isColimit N) (G.obj j) r m)).mp h'

/-- An isomorphism of `𝒪_X`-modules induces a linear isomorphism of stalks. -/
private def moduleStalkEquiv {X : RingedSpace.{u, v}} {M N : OXMod.{u, v} X}
    (e : M ≅ N) (x : X) :
    moduleSheafStalk M x ≃ₗ[structureSheafStalk X x] moduleSheafStalk N x :=
  ((moduleStalkFunctor X x).mapIso e).toLinearEquiv

/-- Finite freeness of the stalk at a point depends only on the isomorphism class of the
`𝒪_X`-module. -/
lemma finite_free_stalk_iff_of_iso {X : RingedSpace.{u, v}}
    {M N : OXMod.{u, v} X} (e : M ≅ N) (x : X) :
    (Module.Finite (structureSheafStalk X x) (moduleSheafStalk M x) ∧
      Module.Free (structureSheafStalk X x) (moduleSheafStalk M x)) ↔
    (Module.Finite (structureSheafStalk X x) (moduleSheafStalk N x) ∧
      Module.Free (structureSheafStalk X x) (moduleSheafStalk N x)) :=
  ⟨fun ⟨_, _⟩ => ⟨Module.Finite.equiv (moduleStalkEquiv e x),
      Module.Free.of_equiv (moduleStalkEquiv e x)⟩,
    fun ⟨_, _⟩ => ⟨Module.Finite.equiv (moduleStalkEquiv e.symm x),
      Module.Free.of_equiv (moduleStalkEquiv e.symm x)⟩⟩


/-- The finite free locus depends only on the isomorphism class of the object of `D(𝒪_X)`. -/
lemma cohomologyFiniteFreeLocus_eq_of_iso {X : RingedSpace.{u, v}}
    [HasDerivedCategory.{d} (OXMod.{u, v} X)]
    {E F : DerivedCategory (OXMod.{u, v} X)} (e : E ≅ F) :
    cohomologyFiniteFreeLocus E = cohomologyFiniteFreeLocus F := by
  ext x
  exact forall_congr' fun i => finite_free_stalk_iff_of_iso
    ((DerivedCategory.homologyFunctor (OXMod.{u, v} X) i).mapIso e) x

/-- The finite free locus of the object represented by a complex is cut out by the cohomology
sheaves of that complex. -/
lemma cohomologyFiniteFreeLocus_Q {X : RingedSpace.{u, v}}
    [HasDerivedCategory.{d} (OXMod.{u, v} X)] (K : CochainComplex (OXMod.{u, v} X) ℤ) :
    cohomologyFiniteFreeLocus (DerivedCategory.Q.obj K) =
      {x | ∀ i : ℤ,
        Module.Finite (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x) ∧
        Module.Free (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x)} := by
  ext x
  exact forall_congr' fun i => finite_free_stalk_iff_of_iso
    ((DerivedCategory.homologyFunctorFactors (OXMod.{u, v} X) i).app K) x

/-- A sheaf of modules on a space is finite locally free exactly when every point has an open
neighbourhood on which the sheaf is isomorphic to a finite free one. -/
lemma isFiniteLocallyFree_iff_exists_local_free
    {Y : TopCat.{v}} {R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    [∀ U, HasWeakSheafify ((Opens.grothendieckTopology Y).over U) AddCommGrpCat.{u}]
    [∀ U, ((Opens.grothendieckTopology Y).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (M : SheafOfModules.{u} R) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree M ↔
      ∀ y : Y, ∃ U : Opens Y, y ∈ U ∧ ∃ n : ℕ,
        Nonempty (M.over U ≅ SheafOfModules.free (ULift.{u} (Fin n))) := by
  classical
  refine ⟨fun h y => ?_, fun h => ?_⟩
  · obtain ⟨q, hq, hqfin⟩ := h.exists_isFiniteLocallyFreeData
    obtain ⟨j, hj⟩ := ((Opens.coversTop_iff Y q.X).mp q.coversTop).exists_mem y
    let : (q.generators j).IsFiniteType := hqfin.isFiniteType j
    let : Fintype (q.generators j).I := Fintype.ofFinite _
    let : IsIso (q.generators j).π := hq.isIso j
    let n := Fintype.card (q.generators j).I
    let e : (q.generators j).I ≃ ULift.{u} (Fin n) :=
      (Fintype.equivFin _).trans Equiv.ulift.symm
    exact ⟨q.X j, hj, n,
      ⟨(asIso (q.generators j).π).symm ≪≫ SheafOfModules.freeFunctor.mapIso e.toIso⟩⟩
  · choose U hy n e using h
    let q : M.LocalGeneratorsData.{v} := {
      I := Y
      X := U
      coversTop := (Opens.coversTop_iff Y U).mpr
        (Opens.ext <| Set.eq_univ_of_forall fun y => le_iSup U y (hy y))
      generators y := {
        I := ULift.{u} (Fin (n y))
        s := (M.over (U y)).freeHomEquiv (e y).some.inv
        epi := by
          rw [Equiv.symm_apply_apply]
          infer_instance } }
    refine ⟨⟨q, ⟨fun y => ?_⟩, ⟨fun y => ?_⟩⟩⟩
    · change IsIso ((M.over (U y)).freeHomEquiv.symm
        ((M.over (U y)).freeHomEquiv (e y).some.inv))
      rw [Equiv.symm_apply_apply]
      infer_instance
    · exact ⟨inferInstanceAs (Finite (ULift.{u} (Fin (n y))))⟩

/-- The stalks of the zero module are finite free. -/
private lemma finite_free_stalk_of_isZero {X : RingedSpace.{u, v}}
    (M : OXMod.{u, v} X) (hM : IsZero M) (x : X) :
    Module.Finite (structureSheafStalk X x) (moduleSheafStalk M x) ∧
      Module.Free (structureSheafStalk X x) (moduleSheafStalk M x) := by
  let D := (OpenNhds.inclusion x).op ⋙ (moduleSheafULift M).val.presheaf
  have hD (i : (OpenNhds x)ᵒᵖ) : Subsingleton (D.obj i) := by
    let U := (OpenNhds.inclusion x).op.obj i
    have hz (a : M.val.obj U) : a = 0 :=
      congrArg (fun f : M ⟶ M => f.val.app U a) (hM.eq_of_src (𝟙 M) 0)
    let : Subsingleton (M.val.obj U) := ⟨fun a b => (hz a).trans (hz b).symm⟩
    exact inferInstanceAs (Subsingleton (ULift.{u} (M.val.obj U)))
  let : PreservesFilteredColimitsOfSize.{v, v} (forget Ab.{max u v}) :=
    preservesFilteredColimitsOfSize_shrink _
  have hz (m : ↑(colimit D)) : m = 0 := by
    obtain ⟨i, m, rfl⟩ := Concrete.colimit_exists_rep D m
    let := hD i
    rw [Subsingleton.elim m 0]
    exact (colimit.ι D i).hom.map_zero
  let : Subsingleton ↑(colimit D) := ⟨fun a b => (hz a).trans (hz b).symm⟩
  let : Subsingleton ↑(moduleSheafStalk M x) := inferInstanceAs (Subsingleton ↑(colimit D))
  exact ⟨inferInstance, inferInstance⟩

/-- In a degree where a complex vanishes, the cohomology stalks are finite free. -/
private lemma finite_free_homology_stalk_of_isZero_X {X : RingedSpace.{u, v}}
    (K : CochainComplex (OXMod.{u, v} X) ℤ) (i : ℤ) (h : IsZero (K.X i)) (x : X) :
    Module.Finite (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x) ∧
      Module.Free (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x) :=
  finite_free_stalk_of_isZero _ ((K.sc i).isZero_homology_of_isZero_X₂ h) x


/-- Only the degrees in which the complex does not vanish contribute to the finite free locus. -/
private lemma cohomologyFiniteFreeLocus_Q_eq_iInter {X : RingedSpace.{u, v}}
    [HasDerivedCategory.{d} (OXMod.{u, v} X)] (K : CochainComplex (OXMod.{u, v} X) ℤ) :
    cohomologyFiniteFreeLocus (DerivedCategory.Q.obj K) =
      ⋂ i ∈ {i : ℤ | ¬ IsZero (K.X i)},
        {x | Module.Finite (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x) ∧
          Module.Free (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x)} := by
  classical
  rw [cohomologyFiniteFreeLocus_Q]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  refine ⟨fun h i _ => h i, fun h i => ?_⟩
  by_cases hi : IsZero (K.X i)
  · exact finite_free_homology_stalk_of_isZero_X K i hi x
  · exact h i hi

/-- The two spellings of finite freeness of the stalk -- through the colimit functor and
through `moduleSheafStalk` -- agree by definition. -/
lemma finite_free_sheafColimit_iff_stalk
    {X : RingedSpace.{u, v}} (M : OXMod.{u, v} X) (x : X) :
    (let Y := X
      let F := (OpenNhds.inclusion (X := Y.carrier) x).op
      let N := moduleSheafULift M
      Module.Finite ↑(colimit (F ⋙ (structureSheafULift Y).obj))
          ((sheafColimitFunctor (structureSheafULift Y) F).obj N) ∧
        Module.Free ↑(colimit (F ⋙ (structureSheafULift Y).obj))
          ((sheafColimitFunctor (structureSheafULift Y) F).obj N)) ↔
    Module.Finite (structureSheafStalk X x) (moduleSheafStalk M x) ∧
      Module.Free (structureSheafStalk X x) (moduleSheafStalk M x) :=
  Iff.rfl

/-- The previous equivalence read from right to left, with the colimit side written out. Stating
it separately keeps the identification of the stalk with the neighbourhood colimit out of the
proofs that use it, where it would be re-checked against a large goal. -/
lemma finite_free_sheafColimit_moduleULift
    {X : RingedSpace.{u, v}} (M : OXMod.{u, v} X) (x : X)
    (h : Module.Finite (structureSheafStalk X x) (moduleSheafStalk M x) ∧
      Module.Free (structureSheafStalk X x) (moduleSheafStalk M x)) :
    Module.Finite ↑(colimit ((OpenNhds.inclusion x).op ⋙ (structureSheafULift X).obj))
        ((sheafColimitFunctor (structureSheafULift X) (OpenNhds.inclusion x).op).obj
          (moduleSheafULift M)) ∧
      Module.Free ↑(colimit ((OpenNhds.inclusion x).op ⋙ (structureSheafULift X).obj))
        ((sheafColimitFunctor (structureSheafULift X) (OpenNhds.inclusion x).op).obj
          (moduleSheafULift M)) :=
  (finite_free_sheafColimit_iff_stalk M x).mpr h

/-- Restriction to an open set does not change stalks at its points: the restricted module has
finite free stalk at a point of the open set exactly when the original module does. -/
lemma finite_free_stalk_restrict_iff
    {X : RingedSpace.{u, v}} (M : OXMod.{u, v} X) (U : Opens X) (x : U) :
    (let Y := X.restrict U.isOpenEmbedding
      let F := (OpenNhds.inclusion (restrictPoint U x)).op
      let N := moduleSheafULift ((restrictModules X U).obj M)
      Module.Finite ↑(colimit (F ⋙ (structureSheafULift Y).obj))
          ((sheafColimitFunctor (structureSheafULift Y) F).obj N) ∧
        Module.Free ↑(colimit (F ⋙ (structureSheafULift Y).obj))
          ((sheafColimitFunctor (structureSheafULift Y) F).obj N)) ↔
    Module.Finite (structureSheafStalk X x) (moduleSheafStalk M x) ∧
      Module.Free (structureSheafStalk X x) (moduleSheafStalk M x) := by
  let A := (OpenNhds.inclusion (x : X)).op ⋙ (structureSheafULift X).obj
  let B := (OpenNhds.inclusion (x : X)).op ⋙ (moduleSheafULift M).val.presheaf
  let G : (OpenNhds (restrictPoint U x))ᵒᵖ ⥤ (OpenNhds (x : X))ᵒᵖ :=
    (U.isOpenEmbedding.functorNhds (opensPoint U x)).op
  have : G.Final := final_functorNhds_op U (opensPoint U x)
  let Y := X.restrict U.isOpenEmbedding
  let F := (OpenNhds.inclusion (restrictPoint U x)).op
  let N := moduleSheafULift ((restrictModules X U).obj M)
  let (j : (OpenNhds (x : X))ᵒᵖ) : Module (A.obj j) (B.obj j) :=
    ((moduleSheafULift M).val.obj ((OpenNhds.inclusion (x : X)).op.obj j)).isModule
  let (j : (OpenNhds (restrictPoint U x))ᵒᵖ) :
      Module ((G ⋙ A).obj j) ((F ⋙ N.val.presheaf).obj j) := (N.val.obj (F.obj j)).isModule
  let : Module ↑(colimit A) ↑(colimit B) := by
    change Module (structureSheafStalk X x) (moduleSheafStalk M x)
    infer_instance
  exact finite_free_colimit_whisker_iff G A B (F ⋙ N.val.presheaf)
    (NatIso.ofComponents (fun _ => Iso.refl _))
    (fun f r m => N.val.map_smul (F.map f) r m)
    (fun j r m => IsColimit.ι_smul A B (fun f r m => (moduleSheafULift M).val.map_smul _ _ _)
      (colimit.isColimit A) (colimit.isColimit B) (G.obj j) r m)

section


variable {C : Type v} [SmallCategory C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J Ab.{u}] [J.WEqualsLocallyBijective Ab.{u}]
  [∀ X, HasSheafify (J.over X) Ab.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective Ab.{u}]

/-- A sheaf of modules carrying a finite presentation is of finite presentation. -/
lemma isFinitePresentation_of_finite_presentation
    {M : SheafOfModules.{u} R} (p : M.Presentation) [p.IsFinite] :
    M.IsFinitePresentation := by
  refine ⟨⟨p.quasicoherentData, ⟨fun X => ?_⟩⟩⟩
  exact ⟨⟨inferInstanceAs (Finite p.generators.I)⟩, ⟨inferInstanceAs (Finite p.relations.I)⟩⟩

/-- A presentation of the cokernel of a map between retracts of free sheaves of modules, with
generators and relations indexed by the two index types. -/
def cokernelPresentationOfRetracts
    {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    {I K : Type u} (rM : Retract M (SheafOfModules.free I))
    (rN : Retract N (SheafOfModules.free K)) : (cokernel f).Presentation := by
  let a := 𝟙 _ - rN.r ≫ rN.i
  let b := rM.r ≫ f ≫ rN.i
  let e := SheafOfModules.freeSumIso (R := R) K I
  let g := e.inv ≫ coprod.desc a b
  let q := rN.r ≫ cokernel.π f
  have ha : a ≫ q = 0 := by simp [a, q, Preadditive.sub_comp]
  have hb : b ≫ q = 0 := by simp [b, q]
  have hdesc : coprod.desc a b ≫ q = 0 := by
    apply coprod.hom_ext <;>
      simp only [coprod.inl_desc_assoc, coprod.inr_desc_assoc, ha, hb, comp_zero]
  have hg : g ≫ q = 0 := by
    simp [g, hdesc]
  refine SheafOfModules.presentationOfIsCokernelFree g q hg
    (CokernelCofork.IsColimit.ofπ q hg (fun k hk => ?_) (fun k hk => ?_)
      (fun k hk m hm => ?_))
  · have h : b ≫ k = 0 := by
      simpa [g, coprod.inr_desc] using congrArg (fun z => coprod.inr ≫ e.hom ≫ z) hk
    have hf : f ≫ rN.i ≫ k = 0 := by
      simpa [b, rM.retract_assoc] using congrArg (fun z => rM.i ≫ z) h
    exact cokernel.desc f (rN.i ≫ k) hf
  · change rN.r ≫ cokernel.π f ≫ cokernel.desc _ _ _ = k
    rw [cokernel.π_desc]
    have h : a ≫ k = 0 := by
      simpa [g, coprod.inl_desc] using congrArg (fun z => coprod.inl ≫ e.hom ≫ z) hk
    exact (sub_eq_zero.mp (by simpa [a, Preadditive.sub_comp] using h)).symm
  · apply (cancel_epi (cokernel.π f)).mp
    simp only [cokernel.π_desc]
    simpa [q, rN.retract_assoc] using congrArg (fun z => rN.i ≫ z) hm

/-- The cokernel of a map between retracts of finite free sheaves of modules is of finite
presentation. -/
private lemma cokernel_isFinitePresentation_of_retracts
    {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    {I K : Type u} [Finite I] [Finite K]
    (rM : Retract M (SheafOfModules.free I))
    (rN : Retract N (SheafOfModules.free K)) : (cokernel f).IsFinitePresentation := by
  let p := cokernelPresentationOfRetracts f rM rN
  have : p.IsFinite := ⟨⟨inferInstanceAs (Finite K)⟩, ⟨inferInstanceAs (Finite (K ⊕ I))⟩⟩
  exact isFinitePresentation_of_finite_presentation p

end

section


universe w t
variable {C : Type w} [Category.{t} C]
/-- A retract of a projective object is projective. -/
lemma projective_of_retract {P Q : C} (r : Retract P Q) [Projective Q] :
    Projective P where
  factors f e _ := by
    obtain ⟨g, hg⟩ := Projective.factors (r.r ≫ f) e
    exact ⟨r.i ≫ g, by simp [hg, Category.assoc]⟩

variable [Abelian C]
/-- If both the target and the cokernel of a morphism are projective, so is its image. -/
lemma projective_image_of_projective_cokernel {P Q : C} (f : P ⟶ Q)
    [Projective Q] [Projective (cokernel f)] : Projective (Abelian.image f) := by
  let S := ShortComplex.mk (kernel.ι (cokernel.π f)) (cokernel.π f) (kernel.condition _)
  have hS : S.ShortExact := { exact := S.exact_of_f_is_kernel (kernelIsKernel _) }
  let s := hS.splittingOfProjective
  exact projective_of_retract (⟨S.f, s.r, s.f_r⟩ : Retract (Abelian.image f) Q)

/-- The homology of a short complex is the kernel of the induced map from its opcycles to the
coimage of its second map, which is an epimorphism. -/
lemma exists_shortExact_homologyι (S : ShortComplex C) :
    ∃ (q : S.opcycles ⟶ Abelian.coimage S.g) (hw : S.homologyι ≫ q = 0),
      (ShortComplex.mk S.homologyι q hw).ShortExact := by
  have hz : S.f ≫ Abelian.coimage.π S.g = 0 := by
    rw [← cancel_mono (Abelian.factorThruCoimage S.g), Category.assoc]
    simp
  let q := S.descOpcycles (Abelian.coimage.π S.g) hz
  have hq : S.pOpcycles ≫ q = Abelian.coimage.π S.g := S.p_descOpcycles _ _
  have : Epi q := epi_of_epi_fac hq
  have hqg : q ≫ Abelian.factorThruCoimage S.g = S.fromOpcycles := by
    rw [← cancel_epi S.pOpcycles, ← Category.assoc, hq]
    simp
  have hw : S.homologyι ≫ q = 0 := by
    rw [← cancel_mono (Abelian.factorThruCoimage S.g), Category.assoc, hqg]
    simp
  have ht : IsLimit (KernelFork.ofι S.homologyι hw) :=
    KernelFork.IsLimit.ofι _ _
      (fun a ha => S.liftHomology a (by rw [← hqg, ← Category.assoc, ha, zero_comp]))
      (fun a ha => by simp)
      (fun a ha b hb => (cancel_mono S.homologyι).mp (by simpa using hb))
  exact ⟨q, hw, { exact := (ShortComplex.mk S.homologyι q hw).exact_of_f_is_kernel ht }⟩

/-- The opcycles of a short complex are projective as soon as its third term, the cokernel of
its second map and its homology are. -/
private lemma projective_opcycles_of_projective_cokernel (S : ShortComplex C)
    [Projective S.X₃] [Projective (cokernel S.g)] [Projective S.homology] :
    Projective S.opcycles := by
  let : Projective (Abelian.image S.g) := projective_image_of_projective_cokernel S.g
  let : Projective (Abelian.coimage S.g) :=
    Projective.of_iso (Abelian.coimageIsoImage S.g).symm inferInstance
  obtain ⟨q, hw, hT⟩ := exists_shortExact_homologyι S
  exact Projective.of_iso hT.splittingOfProjective.isoBinaryBiproduct.symm inferInstance

/-- In a complex that vanishes in high degrees and has projective terms and projective homology,
every object of opcycles is projective. -/
private lemma projective_opcycles_of_boundedAbove (K : CochainComplex C ℤ)
    (hb : BddAbove {i : ℤ | ¬ IsZero (K.X i)})
    [∀ i, Projective (K.X i)] [∀ i, Projective (K.homology i)] (i : ℤ) :
    Projective (K.opcycles i) := by
  obtain ⟨b, hb⟩ := hb
  have hzero (j : ℤ) (hj : b < j) : IsZero (K.X j) :=
    of_not_not fun hz => not_le_of_gt hj (hb hz)
  have hup (j : ℤ) (hj : b < j) : Projective (K.opcycles j) :=
    Projective.of_iso ((K.sc j).opcyclesIsoX₂
      ((hzero j hj).eq_of_tgt _ _)).symm (hzero j hj).projective
  refine Int.inductionOn' i (b + 1) (hup _ (by omega)) (fun j hj _ => hup (j + 1) (by omega)) ?_
  · intro j _ ih
    let : Projective (K.opcycles j) := ih
    have hprev : (ComplexShape.up ℤ).prev j = j - 1 :=
      (ComplexShape.up ℤ).prev_eq' (by change j - 1 + 1 = j; omega)
    have hnext : (ComplexShape.up ℤ).next (j - 1) = j :=
      (ComplexShape.up ℤ).next_eq' (by change j - 1 + 1 = j; omega)
    have hp : Projective (cokernel (K.d (j - 1) j)) := by
      have he := Projective.of_iso (K.sc j).opcyclesIsoCokernel ih
      change Projective (cokernel (K.d ((ComplexShape.up ℤ).prev j) j)) at he
      rwa [hprev] at he
    let : Projective (cokernel ((K.sc (j - 1)).g)) := by
      change Projective (cokernel (K.d (j - 1) ((ComplexShape.up ℤ).next (j - 1))))
      rwa [hnext]
    let : Projective ((K.sc (j - 1)).X₃) := inferInstanceAs
      (Projective (K.X ((ComplexShape.up ℤ).next (j - 1))))
    let : Projective ((K.sc (j - 1)).homology) := inferInstanceAs
      (Projective (K.homology (j - 1)))
    exact projective_opcycles_of_projective_cokernel (K.sc (j - 1))

/-- The image under a homology-preserving functor of the opcycles of a complex vanishing in high
degrees is projective, given that the images of the terms and of the homology are. -/
private lemma projective_map_opcycles_of_boundedAbove
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesHomology]
    (K : CochainComplex C ℤ) (hb : BddAbove {i : ℤ | ¬ IsZero (K.X i)})
    (hX : ∀ i, Projective (F.obj (K.X i)))
    (hH : ∀ i, Projective (F.obj (K.homology i))) (i : ℤ) :
    Projective (F.obj (K.opcycles i)) := by
  let L := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let : ∀ i, Projective (L.X i) := hX
  let : ∀ i, Projective (L.homology i) := fun i =>
    Projective.of_iso ((K.sc i).mapHomologyIso F).symm (hH i)
  have hbL : BddAbove {i : ℤ | ¬ IsZero (L.X i)} := hb.mono fun _ hi h => hi (F.map_isZero h)
  exact Projective.of_iso ((K.sc i).mapOpcyclesIso F)
    (projective_opcycles_of_boundedAbove L hbL i)

end

/-- For a complex of sheaves of modules vanishing in high degrees whose terms are retracts of
finite free sheaves, the stalk of each object of opcycles is a finitely generated projective
module, provided the stalks of the homology are projective. -/
private lemma stalk_opcycles_finite_projective
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    [HasSheafify (Opens.grothendieckTopology X) Ab.{max u v}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective Ab.{max u v}]
    (K : CochainComplex (SheafOfModules.{max u v} R) ℤ)
    (hb : BddAbove {i : ℤ | ¬ IsZero (K.X i)})
    (hX : ∀ i, ∃ n : ℕ,
      Nonempty (Retract (K.X i) (SheafOfModules.free (ULift.{max u v} (Fin n)))))
    (x : X)
    (hH : ∀ i, Projective ((sheafColimitFunctor R (OpenNhds.inclusion x).op).obj
      (K.homology i))) (i : ℤ) :
    let T := sheafColimitFunctor R (OpenNhds.inclusion x).op
    Module.Finite ↑(colimit ((OpenNhds.inclusion x).op ⋙ R.obj))
      (T.obj (K.opcycles i)) ∧ Projective (T.obj (K.opcycles i)) := by
  let T := sheafColimitFunctor R (OpenNhds.inclusion x).op
  let S := colimit ((OpenNhds.inclusion x).op ⋙ R.obj)
  let : T.Additive := sheafColimitFunctor_additive R _
  let : PreservesFiniteLimits T := sheafColimitFunctor_preservesFiniteLimits R x
  let : PreservesFiniteColimits T := sheafColimitFunctor_preservesFiniteColimits R x
  have hterm (j : ℤ) : Module.Finite S (T.obj (K.X j)) ∧ Projective (T.obj (K.X j)) := by
    obtain ⟨n, ⟨r⟩⟩ := hX j
    have hfree := finite_free_sheafColimit_free R (OpenNhds.inclusion x).op
      (ULift.{max u v} (Fin n))
    let : Module.Finite S (T.obj (SheafOfModules.free (ULift.{max u v} (Fin n)))) := hfree.1
    let : Module.Free S (T.obj (SheafOfModules.free (ULift.{max u v} (Fin n)))) := hfree.2
    let r' := r.map T
    have hsurj : Function.Surjective r'.r.hom := fun m =>
      ⟨r'.i m, ConcreteCategory.congr_hom r'.retract m⟩
    exact ⟨Module.Finite.of_surjective r'.r.hom hsurj, projective_of_retract r'⟩
  let : Module.Finite S (T.obj (K.X i)) := (hterm i).1
  exact ⟨Module.Finite.of_surjective (T.map (K.pOpcycles i)).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance),
    projective_map_opcycles_of_boundedAbove T K hb (fun i => (hterm i).2) hH i⟩

section

attribute [local instance] liftModulesFunctor_additive

/-- Presheaves of abelian groups on the open sets of `X` admit a sheafification. -/
local instance (X : RingedSpace.{u, v}) :
    HasSheafify (Opens.grothendieckTopology X.carrier) Ab.{max u v} :=
  hasSheafifyEssentiallySmallSite.{v, max u v, v, (max u v) + 1, max u v} _ _

/-- On the open sets of `X`, a morphism of presheaves of abelian groups becomes an isomorphism
after sheafification exactly when it is locally bijective. -/
local instance (X : RingedSpace.{u, v}) :
    (Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective Ab.{max u v} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, max u v, v,
    (max u v) + 1, max u v} _

/-- Presheaves of abelian groups on the open subsets of `U` admit a sheafification. -/
local instance (X : RingedSpace.{u, v}) (U : Opens X) :
    HasSheafify ((Opens.grothendieckTopology X.carrier).over U) Ab.{max u v} :=
  hasSheafifyEssentiallySmallSite.{v, max u v, v, (max u v) + 1, max u v} _ _

/-- On the open subsets of `U`, a morphism of presheaves of abelian groups becomes an
isomorphism after sheafification exactly when it is locally bijective. -/
local instance (X : RingedSpace.{u, v}) (U : Opens X) :
    ((Opens.grothendieckTopology X.carrier).over U).WEqualsLocallyBijective Ab.{max u v} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, max u v, v,
    (max u v) + 1, max u v} _

/-- A filtered colimit of rings with commutative terms is commutative. -/
@[instance_reducible] def commRingFilteredColimit
    {C : Type v} [SmallCategory C] [IsFiltered C] (R : C ⥤ RingCat.{max u v})
    (hcomm : ∀ j (a b : R.obj j), a * b = b * a) : CommRing ↑(colimit R) where
  __ := (inferInstance : Ring ↑(colimit R))
  mul_comm a b := by
    let : PreservesFilteredColimitsOfSize.{v, v} (forget RingCat.{max u v}) :=
      preservesFilteredColimitsOfSize_shrink _
    obtain ⟨i, a, rfl⟩ := Concrete.colimit_exists_rep R a
    obtain ⟨j, b, rfl⟩ := Concrete.colimit_exists_rep R b
    let k := IsFiltered.max i j
    let f := IsFiltered.leftToMax i j
    let g := IsFiltered.rightToMax i j
    have ha : colimit.ι R i a = colimit.ι R k (R.map f a) :=
      (ConcreteCategory.congr_hom (colimit.w R f) a).symm
    have hb : colimit.ι R j b = colimit.ι R k (R.map g b) :=
      (ConcreteCategory.congr_hom (colimit.w R g) b).symm
    rw [ha, hb, ← map_mul, ← map_mul, hcomm]

/-- The stalk of the structure sheaf of rings is commutative, the structure sheaf being a sheaf
of commutative rings. -/
@[instance_reducible] def structureSheafStalkCommRing (X : RingedSpace.{u, v}) (x : X) :
    CommRing (structureSheafStalk X x) :=
  commRingFilteredColimit
    ((OpenNhds.inclusion x).op ⋙ (structureSheafULift X).obj) (fun j a b => by
    change ULift.up (a.down * b.down) = ULift.up (b.down * a.down)
    exact congrArg ULift.up
      (@mul_comm (X.presheaf.obj ((OpenNhds.inclusion x).op.obj j)) _ a.down b.down))

/-- Over a local stalk the finitely generated projective stalks of the opcycles of the previous
lemma are finite free. -/
private lemma stalk_opcycles_finite_free
    {X : RingedSpace.{u, v}} (K : CochainComplex
      (SheafOfModules.{max u v} (structureSheafULift X)) ℤ)
    (hb : BddAbove {i : ℤ | ¬ IsZero (K.X i)})
    (hX : ∀ i, ∃ n : ℕ,
      Nonempty (Retract (K.X i) (SheafOfModules.free (ULift.{max u v} (Fin n)))))
    (x : X) [IsLocalRing (structureSheafStalk X x)]
    (hH : ∀ i, Projective ((sheafColimitFunctor (structureSheafULift X)
      (OpenNhds.inclusion x).op).obj (K.homology i))) (i : ℤ) :
    let T := sheafColimitFunctor (structureSheafULift X) (OpenNhds.inclusion x).op
    Module.Finite (structureSheafStalk X x) (T.obj (K.opcycles i)) ∧
      Module.Free (structureSheafStalk X x) (T.obj (K.opcycles i)) := by
  let : CommRing (structureSheafStalk X x) := structureSheafStalkCommRing X x
  obtain ⟨hfin, hproj⟩ := stalk_opcycles_finite_projective
    (structureSheafULift X) K hb hX x hH i
  exact ⟨hfin, Module.free_of_flat_of_isLocalRing⟩

/-- The opcycles of the universe lift of a strictly perfect complex are of finite presentation,
being cokernels of maps between retracts of finite free sheaves of modules. -/
private lemma lifted_opcycles_isFinitePresentation
    {X : RingedSpace.{u, v}} (K : CochainComplex (OXMod.{u, v} X) ℤ)
    (hK : IsStrictlyPerfect K) (i : ℤ) :
    (((liftModulesFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).opcycles i
      |>.IsFinitePresentation := by
  let L := ((liftModulesFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  obtain ⟨n, ⟨r⟩⟩ := exists_retract_free_liftModulesFunctor
    (K.X ((ComplexShape.up ℤ).prev i)) (hK.directSummand _)
  obtain ⟨m, ⟨s⟩⟩ := exists_retract_free_liftModulesFunctor (K.X i) (hK.directSummand _)
  exact (SheafOfModules.isFinitePresentation (structureSheafULift X)).prop_of_iso
    (L.sc i).opcyclesIsoCokernel.symm (cokernel_isFinitePresentation_of_retracts _ r s)

/-- The universe lift of a strictly perfect complex vanishes outside finitely many degrees. -/
private lemma lifted_complex_bounded
    {X : RingedSpace.{u, v}} (K : CochainComplex (OXMod.{u, v} X) ℤ)
    (hK : IsStrictlyPerfect K) :
    {i : ℤ | ¬ IsZero
      ((((liftModulesFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).X i)}.Finite :=
  hK.bounded.subset (fun _ hi h => hi ((liftModulesFunctor X).map_isZero h))

/-- If all cohomology stalks of a strictly perfect complex at a point with local stalk are
finite free, so are the stalks of the opcycles of its universe lift. -/
lemma lifted_opcycles_stalk_finite_free
    {X : RingedSpace.{u, v}} (K : CochainComplex (OXMod.{u, v} X) ℤ)
    (hK : IsStrictlyPerfect K) (x : X) [IsLocalRing (structureSheafStalk X x)]
    (hH : ∀ i, Module.Finite (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x) ∧
      Module.Free (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x)) (i : ℤ) :
    let L := ((liftModulesFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    let T := sheafColimitFunctor (structureSheafULift X) (OpenNhds.inclusion x).op
    Module.Finite (structureSheafStalk X x) (T.obj (L.opcycles i)) ∧
      Module.Free (structureSheafStalk X x) (T.obj (L.opcycles i)) := by
  let L := ((liftModulesFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let T := sheafColimitFunctor (structureSheafULift X) (OpenNhds.inclusion x).op
  let : (liftModulesFunctor X).PreservesHomology := liftModulesFunctor_preservesHomology X
  apply stalk_opcycles_finite_free L (lifted_complex_bounded K hK).bddAbove
    (fun j => exists_retract_free_liftModulesFunctor (K.X j) (hK.directSummand j)) x _ i
  intro j
  have h := (finite_free_sheafColimit_iff_stalk (K.homology j) x).mpr (hH j)
  let : Module.Free (structureSheafStalk X x)
      (T.obj ((liftModulesFunctor X).obj (K.homology j))) := h.2
  have hproj : Projective (T.obj ((liftModulesFunctor X).obj (K.homology j))) :=
    inferInstance
  exact Projective.of_iso (T.mapIso ((K.sc j).mapHomologyIso (liftModulesFunctor X))).symm
    hproj

end

end Stacks.Cohomology.PerfectComplexes

end
