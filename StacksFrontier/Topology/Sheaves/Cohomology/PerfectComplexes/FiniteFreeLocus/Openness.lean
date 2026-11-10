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
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.FiniteFreeLocus.StrictlyPerfectCharts

/-!
# The finite free locus of the cohomology of a perfect complex is open

Let `(X, 𝒪_X)` be a ringed space all of whose structure-sheaf stalks are local rings, and let
`E` be a perfect object of `D(𝒪_X)`. This file proves [Stacks, Tag 0GT1]: the set of points `x`
at which every cohomology stalk `H^i(E)_x` is a finite free `𝒪_{X, x}`-module is open, every
cohomology sheaf `H^i(E)` is finite locally free after restriction to that open set, and it is
the largest open set with that property.

## Main results

* `Stacks.Cohomology.PerfectComplexes.isOpen_cohomologyFiniteFreeLocus`: the locus is open.
* `Stacks.Cohomology.PerfectComplexes.isFiniteLocallyFree_homology_restrict_locus`: on the
  locus every cohomology sheaf is finite locally free.
* `Stacks.Cohomology.PerfectComplexes.le_cohomologyFiniteFreeLocus_of_isFiniteLocallyFree`: an
  open set on which all cohomology sheaves are finite locally free is contained in the locus.

## Implementation notes

**Shape of the proof.** Perfectness gives, locally on `X`, a strictly perfect complex `P`
quasi-isomorphic to a representative of `E`. The terms of `P` are direct summands of finite
free modules, hence so are its opcycles in each degree, which makes each `H^i(P)` the homology
of a short complex whose outer terms have finite free stalks and whose cokernel is a direct
summand of a finite free module. [Stacks, Tag 08C6] splits off that summand on a smaller open
set, and [Stacks, Tag 0B8J] turns a finite free stalk of a finitely presented module into a
free chart on an open neighbourhood. Intersecting the finitely many charts obtained from the
finitely many nonzero degrees of `P` gives the neighbourhood on which all cohomology sheaves
are simultaneously free, which proves both openness and finite local freeness; maximality is
immediate, since a free chart has finite free stalks.

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

section

universe w
open CategoryTheory.Functor
attribute [local instance] liftModulesFunctor_additive
/-- Presheaves of abelian groups on the open sets of `B` admit a sheafification. -/
local instance (B : Type v) [TopologicalSpace B] :
    HasSheafify (Opens.grothendieckTopology B) Ab.{max u v} :=
  hasSheafifyEssentiallySmallSite.{v, max u v, v, (max u v) + 1, max u v} _ _
/-- On the open sets of `B`, a morphism of presheaves of abelian groups becomes an isomorphism
after sheafification exactly when it is locally bijective. -/
local instance (B : Type v) [TopologicalSpace B] :
    (Opens.grothendieckTopology B).WEqualsLocallyBijective Ab.{max u v} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, max u v, v,
    (max u v) + 1, max u v} _
/-- Presheaves of abelian groups on the open subsets of `U` admit a sheafification. -/
local instance (B : Type v) [TopologicalSpace B] (U : Opens B) :
    HasSheafify ((Opens.grothendieckTopology B).over U) Ab.{max u v} :=
  hasSheafifyEssentiallySmallSite.{v, max u v, v, (max u v) + 1, max u v} _ _
/-- On the open subsets of `U`, a morphism of presheaves of abelian groups becomes an
isomorphism after sheafification exactly when it is locally bijective. -/
local instance (B : Type v) [TopologicalSpace B] (U : Opens B) :
    ((Opens.grothendieckTopology B).over U).WEqualsLocallyBijective Ab.{max u v} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, max u v, v,
    (max u v) + 1, max u v} _

/-- The same space with the universe of the sections of its structure sheaf raised, so that the
ring universe contains the universe of the space. -/
private def ringedSpaceRingULift (X : RingedSpace.{u, v}) : RingedSpace.{max u v, v} where
  carrier := X.carrier
  presheaf := {
    obj U := CommRingCat.of (ULift.{v} (X.presheaf.obj U))
    map f := CommRingCat.ofHom
      (ULift.ringEquiv.symm.toRingHom.comp ((X.presheaf.map f).hom.comp
        ULift.ringEquiv.toRingHom))
    map_id := by intro U; ext r; simp
    map_comp := by intro U V W f g; ext r; simp }
  IsSheaf := by
    apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat RingCat)
    exact (structureSheafULift X).property

/-- `𝒪_X^{⊕n}` is the free sheaf of modules on `ULift (Fin n)`. -/
private def finiteFreeIsoFree (X : RingedSpace.{max u v, v}) (n : ℕ) :
    finiteFree X n ≅ SheafOfModules.free (R := structureSheafOfRings X)
      (ULift.{max u v} (Fin n)) :=
  biproduct.whiskerEquiv Equiv.ulift.symm (fun _ => Iso.refl (structureModule X)) ≪≫
    biproduct.isoCoproduct _

/-- A retract of a free sheaf of modules on `ULift (Fin n)` is a direct summand of a finite free
`𝒪_X`-module. -/
private lemma directSummand_of_retract_free
    {X : RingedSpace.{max u v, v}} (M : OXMod.{max u v, max u v} X) (n : ℕ)
    (r : Retract M (SheafOfModules.free (ULift.{max u v} (Fin n)))) :
    IsDirectSummandOfFiniteFree M :=
  (isDirectSummandOfFiniteFree_iff_retract M).mpr
    ⟨n, ⟨r.trans (finiteFreeIsoFree X n).symm.retract⟩⟩

/-- A functor preserves finite limits if its composite with a finite-limit-reflecting functor is
isomorphic to a finite-limit-preserving functor. -/
private lemma preservesFiniteLimits_of_comp_iso {C D E : Type*} [Category C] [Category D]
    [Category E] (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (hH : PreservesFiniteLimits H)
    [ReflectsFiniteLimits G] (e : F ⋙ G ≅ H) : PreservesFiniteLimits F := by
  have : PreservesFiniteLimits (F ⋙ G) := preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves F G

/-- Restriction of sheaves of modules to the slice over an open set preserves finite limits. -/
private lemma overFunctor_preservesFiniteLimits
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    (U : Opens X) : PreservesFiniteLimits (SheafOfModules.overFunctor.{max u v} R U) := by
  let A := SheafOfModules.toSheaf.{max u v} R ⋙
    sheafToPresheaf (Opens.grothendieckTopology X) Ab.{max u v}
  let G := SheafOfModules.toSheaf.{max u v} (R.over U) ⋙
    sheafToPresheaf ((Opens.grothendieckTopology X).over U) Ab.{max u v}
  let B := (whiskeringLeft _ _ Ab.{max u v}).obj (Over.forget U).op
  let : PreservesFiniteLimits A := by dsimp [A]; infer_instance
  let : PreservesFiniteLimits B := by dsimp [B]; infer_instance
  exact preservesFiniteLimits_of_comp_iso _ G _ (comp_preservesFiniteLimits A B) (Iso.refl _)

attribute [local instance] overFunctor_preservesFiniteLimits

/-- Restriction of sheaves of modules to the slice over an open set preserves homology. -/
private lemma overFunctor_preservesHomology
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    (U : Opens X) : (SheafOfModules.overFunctor.{max u v} R U).PreservesHomology := by
  let : (SheafOfModules.overFunctor.{max u v} R U).IsLeftAdjoint := by
    dsimp [SheafOfModules.overFunctor]
    infer_instance
  infer_instance

/-- Restriction of sheaves of modules to an open subspace, as a functor to modules over the
restricted sheaf of rings. -/
private def restrictSheafModules
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    (U : Opens X) : SheafOfModules.{max u v} R ⥤
      SheafOfModules.{max u v} (U.sheafRestrict.obj R) := by
  let : U.isOpenEmbedding.functor.IsContinuous (Opens.grothendieckTopology U)
      (Opens.grothendieckTopology X) := U.isOpenEmbedding.functor_isContinuous
  exact SheafOfModules.pushforward.{max u v} (F := U.isOpenEmbedding.functor)
    (𝟙 (U.sheafRestrict.obj R))

/-- Restriction of sheaves of modules to an open subspace is additive. -/
private lemma restrictSheafModules_additive
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    (U : Opens X) : (restrictSheafModules R U).Additive where
  map_add := by intro M N f g; ext V m; rfl

attribute [local instance] restrictSheafModules_additive

/-- Restriction of sheaves of modules to an open subspace is a left adjoint. -/
private lemma restrictSheafModules_isLeftAdjoint
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    (U : Opens X) : (restrictSheafModules R U).IsLeftAdjoint := by
  let J := Opens.grothendieckTopology U
  let K := Opens.grothendieckTopology X
  let F := U.isOpenEmbedding.functor
  let : F.IsContinuous J K := U.isOpenEmbedding.functor_isContinuous
  let : F.IsLeftAdjoint := U.isOpenEmbedding.isOpenMap.adjunction.isLeftAdjoint
  let : F.IsCocontinuous J K :=
    (U.isOpenEmbedding.isOpenMap.adjunction.isCocontinuous_iff_coverPreserving J K).mpr
      (coverPreserving_opens_map U.inclusion')
  exact pushforward_isLeftAdjoint _ (IsIso.id _)

/-- Restriction of sheaves of modules to an open subspace preserves finite limits. -/
private lemma restrictSheafModules_preservesFiniteLimits
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    (U : Opens X) : PreservesFiniteLimits (restrictSheafModules R U) := by
  let A := SheafOfModules.toSheaf.{max u v} R ⋙
    sheafToPresheaf (Opens.grothendieckTopology X) Ab.{max u v}
  let G := SheafOfModules.toSheaf.{max u v} (U.sheafRestrict.obj R) ⋙
    sheafToPresheaf (Opens.grothendieckTopology U) Ab.{max u v}
  let B := (whiskeringLeft _ _ Ab.{max u v}).obj U.isOpenEmbedding.functor.op
  let : PreservesFiniteLimits A := by dsimp [A]; infer_instance
  let : PreservesFiniteLimits B := by dsimp [B]; infer_instance
  exact preservesFiniteLimits_of_comp_iso _ G _ (comp_preservesFiniteLimits A B) (Iso.refl _)

attribute [local instance] restrictSheafModules_isLeftAdjoint
  restrictSheafModules_preservesFiniteLimits

/-- Restriction of sheaves of modules to an open subspace preserves homology. -/
private lemma restrictSheafModules_preservesHomology
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    (U : Opens X) : (restrictSheafModules R U).PreservesHomology := by
  infer_instance

/-- A short exact sequence whose third term is a direct summand of a finite free module splits
after restriction to a small enough open set; this is [Stacks, Tag 08C6]. -/
private lemma exists_over_retract_of_shortExact
    {X : RingedSpace.{max u v, v}} (S : ShortComplex (OXMod.{max u v, max u v} X))
    (hS : S.ShortExact) (h₃ : IsDirectSummandOfFiniteFree S.X₃) (x : X) :
    ∃ U : Opens X, x ∈ U ∧ Nonempty (Retract (S.X₁.over U) (S.X₂.over U)) := by
  let := hS.epi_g
  let := hS.mono_f
  obtain ⟨U, hxU, l, hl⟩ :=
    StrictlyPerfect.exists_over_lift_of_isDirectSummandOfFiniteFree (𝟙 S.X₃) S.g h₃ x
  let F := SheafOfModules.overFunctor (structureSheafOfRings X) U
  let : F.PreservesHomology := overFunctor_preservesHomology _ U
  have hT : (S.map F).ShortExact := hS.map F
  let s := ShortComplex.Splitting.ofExactOfSection (S.map F) hT.exact l
    (by simpa using hl) hT.mono_f
  exact ⟨U, hxU, ⟨⟨(S.map F).f, s.r, s.f_r⟩⟩⟩

/-- Restriction to an open subspace carries a free sheaf of modules to the free sheaf of modules
on the same index type. -/
private def restrictFreeIso
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    (U : Opens X) (I : Type (max u v)) :
    (restrictSheafModules R U).obj (SheafOfModules.free I) ≅ SheafOfModules.free I := by
  let : (restrictSheafModules R U).IsLeftAdjoint := restrictSheafModules_isLeftAdjoint R U
  exact (SheafOfModules.mapFreeIso (restrictSheafModules R U) I (Iso.refl _)).symm

/-- Restriction to an open subspace carries a retract of a free sheaf of modules to a retract of
the free sheaf of modules on the same index type. -/
private def restrictRetractFree
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    {M : SheafOfModules.{max u v} R} {I : Type (max u v)}
    (r : Retract M (SheafOfModules.free I)) (U : Opens X) :
    Retract ((restrictSheafModules R U).obj M) (SheafOfModules.free I) :=
  (r.map (restrictSheafModules R U)).trans (restrictFreeIso R U I).retract

/-- A retract of a free sheaf of modules in the slice over an open set is a retract of the free
sheaf of modules after restriction to the corresponding open subspace. -/
private def overRetractFreeToRestrict
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    {M : SheafOfModules.{max u v} R} {I : Type (max u v)} (U : Opens X)
    (r : Retract (M.over U) (SheafOfModules.free I)) :
    Retract ((restrictSheafModules R U).obj M) (SheafOfModules.free I) := by
  let E := U.sheafOfModulesEquivOver R
  exact (r.map E.functor).trans
    (SheafOfModules.mapFreeIso E.functor I (Iso.refl _)).symm.retract

/-- Transport of a retract along restriction to an open subspace: a retract in the slice over an
open set, composed with a retract of a free sheaf exhibited on the restriction of the larger
term, exhibits the restriction of the smaller term as a retract of that free sheaf. The
identification of restriction with the slice equivalence is performed here, once and on
variables, rather than inside the proofs that use it on large concrete terms. -/
private def retractFreeRestrictOfOverRetract
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    {M N : SheafOfModules.{max u v} R} {I : Type (max u v)} (U : Opens X)
    (r : Retract (M.over U) (N.over U))
    (s : Retract ((restrictSheafModules R U).obj N) (SheafOfModules.free I)) :
    Retract ((restrictSheafModules R U).obj M) (SheafOfModules.free I) :=
  (r.map (U.sheafOfModulesEquivOver R).functor).trans s

/-- Opens of an open subspace of `X` contained in a given one are the same as opens of `X`
contained in its image. -/
private lemma openEmbedding_over_isEquivalence {X : TopCat.{v}} (U : Opens X) (V : Opens U) :
    (Over.post (X := opensOfRestrict U V) U.isOpenEmbedding.functor).IsEquivalence := by
  let F := U.isOpenEmbedding.functor
  let : Mono U.inclusion' := (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  let : F.Full := U.isOpenEmbedding.isOpenMap.functorFullOfMono
  let G := Opens.map U.inclusion'
  let : (Over.post (X := opensOfRestrict U V) F).EssSurj := by
    refine ⟨fun Z => ?_⟩
    have hZU : Z.left ≤ U := by
      intro x hx
      obtain ⟨y, _, rfl⟩ := Z.hom.le hx
      exact y.property
    let W := G.obj Z.left
    let f : W ⟶ V := G.map Z.hom ≫ eqToHom (Opens.map_functor_eq V)
    refine ⟨Over.mk f, ⟨Over.isoMk (eqToIso ?_)⟩⟩
    change F.obj W = Z.left
    exact (Opens.functor_map_eq_inf U Z.left).trans (inf_eq_left.mpr hZU)
  exact { }

/-- A trivialisation of the restriction of a sheaf of modules to an open subspace, over an open
set of that subspace, is the same thing as a trivialisation of the sheaf over the
corresponding open set of the ambient space. -/
private lemma chart_restriction_iff
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    (M : SheafOfModules.{max u v} R) (U : Opens X) (V : Opens U)
    (I : Type (max u v)) :
    Nonempty (((restrictSheafModules R U).obj M).over V ≅ SheafOfModules.free I) ↔
      Nonempty (M.over (U.isOpenEmbedding.functor.obj V) ≅ SheafOfModules.free I) := by
  let V' := opensOfRestrict U V
  let J := Opens.grothendieckTopology ((Opens.toTopCat X).obj U : Type v)
  let K := Opens.grothendieckTopology X
  let F := U.isOpenEmbedding.functor
  let : F.IsContinuous J K := U.isOpenEmbedding.functor_isContinuous
  let : F.IsCocontinuous J K :=
    (U.isOpenEmbedding.isOpenMap.adjunction.isCocontinuous_iff_coverPreserving J K).mpr
      (coverPreserving_opens_map U.inclusion')
  let G := Over.post (X := V') F
  let : G.IsEquivalence := openEmbedding_over_isEquivalence U V
  let e := G.asEquivalence
  let : G.IsContinuous (J.over V') (K.over (F.obj V')) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous F J K).overPost V')
  let : G.IsCocontinuous (J.over V') (K.over (F.obj V')) := inferInstance
  let : e.functor.IsContinuous (J.over V') (K.over (F.obj V')) :=
    ‹G.IsContinuous (J.over V') (K.over (F.obj V'))›
  let : e.functor.IsCocontinuous (J.over V') (K.over (F.obj V')) :=
    ‹G.IsCocontinuous (J.over V') (K.over (F.obj V'))›
  let : e.inverse.IsContinuous (K.over (F.obj V')) (J.over V') :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((e.toAdjunction.isCocontinuous_iff_coverPreserving _ _).mp inferInstance)
  let E := modulesEquivalence (J.over V') (K.over (F.obj V')) e (R.over (F.obj V'))
  let ε : SheafOfModules.unit _ ≅ E.functor.obj (SheafOfModules.unit _) := Iso.refl _
  refine ⟨fun ⟨eV⟩ => ?_,
    fun ⟨eV⟩ => ⟨E.functor.mapIso eV ≪≫ (SheafOfModules.mapFreeIso E.functor I ε).symm⟩⟩
  let e' : E.functor.obj (M.over (F.obj V)) ≅ E.functor.obj (SheafOfModules.free I) :=
    eV ≪≫ SheafOfModules.mapFreeIso E.functor I ε
  exact ⟨(Functor.FullyFaithful.ofFullyFaithful E.functor).preimageIso e'⟩

/-- A trivialisation of a restricted sheaf of modules gives a trivialisation of the sheaf itself
over the corresponding open set of the ambient space. -/
private lemma chart_of_restriction
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    (M : SheafOfModules.{max u v} R) (U : Opens X) (V : Opens U)
    (I : Type (max u v))
    (eV : ((restrictSheafModules R U).obj M).over V ≅ SheafOfModules.free I) :
    Nonempty (M.over (U.isOpenEmbedding.functor.obj V) ≅ SheafOfModules.free I) :=
  (chart_restriction_iff R M U V I).mp ⟨eV⟩

/-- The stalk of the restriction of a sheaf of modules to an open subspace at a point of that
subspace is finite free whenever the stalk of the original sheaf is. -/
private lemma finite_free_stalk_restriction
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    (M : SheafOfModules.{max u v} R) (U : Opens X) (x : U)
    (hM : Module.Finite ↑(colimit ((OpenNhds.inclusion (x : X)).op ⋙ R.obj))
        ((sheafColimitFunctor R (OpenNhds.inclusion (x : X)).op).obj M) ∧
      Module.Free ↑(colimit ((OpenNhds.inclusion (x : X)).op ⋙ R.obj))
        ((sheafColimitFunctor R (OpenNhds.inclusion (x : X)).op).obj M)) :
    let S := U.sheafRestrict.obj R
    let N := (restrictSheafModules R U).obj M
    Module.Finite ↑(colimit ((OpenNhds.inclusion (X := TopCat.of U) x).op ⋙ S.obj))
        ((sheafColimitFunctor S (OpenNhds.inclusion (X := TopCat.of U) x).op).obj N) ∧
      Module.Free ↑(colimit ((OpenNhds.inclusion (X := TopCat.of U) x).op ⋙ S.obj))
        ((sheafColimitFunctor S (OpenNhds.inclusion (X := TopCat.of U) x).op).obj N) := by
  let S := U.sheafRestrict.obj R
  let N := (restrictSheafModules R U).obj M
  let F := (OpenNhds.inclusion (X := TopCat.of U) x).op
  let y := opensPoint U x
  have : (U.isOpenEmbedding.functorNhds y).Initial :=
    Functor.initial_of_adjunction (U.isOpenEmbedding.adjunctionNhds y)
  let G : (OpenNhds (X := TopCat.of (U : Type v)) x)ᵒᵖ ⥤ (OpenNhds (x : X))ᵒᵖ :=
    (U.isOpenEmbedding.functorNhds y).op
  have : G.Final := by
    change ((U.isOpenEmbedding.functorNhds y).op).Final
    infer_instance
  let DR := (OpenNhds.inclusion (x : X)).op ⋙ R.obj
  let DM := (OpenNhds.inclusion (x : X)).op ⋙ M.val.presheaf
  let cR : Cocone (F ⋙ S.obj) := (colimit.cocone DR).whisker G
  let cM : Cocone (F ⋙ N.val.presheaf) := (colimit.cocone DM).whisker G
  let hcR : IsColimit cR := (Functor.Final.isColimitWhiskerEquiv G _).symm
    (colimit.isColimit DR)
  let hcM : IsColimit cM := (Functor.Final.isColimitWhiskerEquiv G _).symm
    (colimit.isColimit DM)
  let (j : (OpenNhds (X := TopCat.of U) x)ᵒᵖ) : Module ((F ⋙ S.obj).obj j)
      ((F ⋙ N.val.presheaf).obj j) := (N.val.obj (F.obj j)).isModule
  let (j : (OpenNhds (x : X))ᵒᵖ) : Module (DR.obj j) (DM.obj j) :=
    (M.val.obj ((OpenNhds.inclusion (x : X)).op.obj j)).isModule
  let : Module cR.pt cM.pt :=
    ((sheafColimitFunctor R (OpenNhds.inclusion (x : X)).op).obj M).isModule
  let : Module ↑(colimit (F ⋙ S.obj)) ↑(colimit (F ⋙ N.val.presheaf)) :=
    ((sheafColimitFunctor S F).obj N).isModule
  let e := colimitModuleEquiv (F ⋙ S.obj) (F ⋙ N.val.presheaf)
    (fun f r m => N.val.map_smul _ _ _) cR hcR cM hcM
    (fun j r m => IsColimit.ι_smul DR DM (fun f r m => M.val.map_smul _ _ _)
      (colimit.isColimit DR) (colimit.isColimit DM) (G.obj j) r m)
  let q := ((colimit.isColimit (F ⋙ S.obj)).coconePointUniqueUpToIso hcR).ringCatIsoToRingEquiv
  let : RingHomInvPair q.toRingHom q.symm.toRingHom := RingHomInvPair.of_ringEquiv q
  let : RingHomInvPair q.symm.toRingHom q.toRingHom := RingHomInvPair.of_ringEquiv_symm q
  let : Module.Finite cR.pt cM.pt := hM.1
  let : Module.Free cR.pt cM.pt := hM.2
  exact ⟨Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective,
    Module.Free.of_equiv e.symm⟩

/-- A retract of a free sheaf of modules on a finite index type admits a finite presentation. -/
private lemma exists_finite_presentation_of_retract_free
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    (M : SheafOfModules.{max u v} R) {I : Type (max u v)} [Finite I]
    (r : Retract M (SheafOfModules.free I)) : ∃ p : M.Presentation, p.IsFinite := by
  let a := 𝟙 _ - r.r ≫ r.i
  have ha : a ≫ r.r = 0 := by simp [a, Preadditive.sub_comp]
  let h := CokernelCofork.IsColimit.ofπ r.r ha
    (fun k hk => r.i ≫ k)
    (fun k hk => (sub_eq_zero.mp (by simpa [a, Preadditive.sub_comp] using hk)).symm)
    (fun k hk m hm => by simpa [r.retract_assoc] using congrArg (fun f => r.i ≫ f) hm)
  let p := SheafOfModules.presentationOfIsCokernelFree a r.r ha h
  refine ⟨p, ?_⟩
  constructor <;> constructor <;> change Finite I <;> infer_instance

/-- A retract of a finite free sheaf of modules with finite free stalk at a point is finite free
on an open neighbourhood of that point. -/
private lemma exists_chart_of_retract_free
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    (M : SheafOfModules.{max u v} R) {I : Type (max u v)} [Finite I]
    (r : Retract M (SheafOfModules.free I)) (x : X)
    (hx : Module.Finite ↑(colimit ((OpenNhds.inclusion x).op ⋙ R.obj))
        ((sheafColimitFunctor R (OpenNhds.inclusion x).op).obj M) ∧
      Module.Free ↑(colimit ((OpenNhds.inclusion x).op ⋙ R.obj))
        ((sheafColimitFunctor R (OpenNhds.inclusion x).op).obj M)) :
    ∃ U : Opens X, x ∈ U ∧ ∃ n : ℕ,
      Nonempty (M.over U ≅ SheafOfModules.free (ULift.{max u v} (Fin n))) := by
  obtain ⟨p, hp⟩ := exists_finite_presentation_of_retract_free R M r
  exact exists_chart_of_presentation R M p hp x hx

/-- The homology of a short complex sits in a short exact sequence between its opcycles and the
coimage of its second map. -/
private lemma exists_homology_opcycles_shortExact
    {C : Type*} [Category C] [Abelian C] (S : ShortComplex C) :
    ∃ q : S.opcycles ⟶ Abelian.coimage S.g,
      ∃ hq : S.homologyι ≫ q = 0,
        (ShortComplex.mk S.homologyι q hq).ShortExact := by
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
  let T := ShortComplex.mk S.homologyι q hw
  have ht : IsLimit (KernelFork.ofι S.homologyι hw) :=
    KernelFork.IsLimit.ofι _ _
      (fun a ha => S.liftHomology a (by rw [← hqg, ← Category.assoc, ha, zero_comp]))
      (fun a ha => by simp)
      (fun a ha b hb => (cancel_mono S.homologyι).mp (by simpa using hb))
  have hT : T.ShortExact := { exact := T.exact_of_f_is_kernel ht }
  exact ⟨q, hw, hT⟩

-- `kernel` and `cokernel` of sheaves of modules reduce to Mathlib's `getLimitCone` and
-- `getColimitCocone`, which the module system does not expose, so the defeq checks
-- against them exhaust the default budget without making progress.
/-- The homology of a short complex whose third term and whose opcycles are retracts of finite
free sheaves and whose cokernel is a direct summand of a finite free module is finite free on
an open neighbourhood of any point at which its stalk is finite free. -/
private lemma exists_chart_homology_of_retracts
    {X : RingedSpace.{max u v, v}} (S : ShortComplex (OXMod.{max u v, max u v} X))
    (n m : ℕ)
    (r₃ : Retract S.X₃ (SheafOfModules.free (ULift.{max u v} (Fin n))))
    (rC : Retract S.opcycles (SheafOfModules.free (ULift.{max u v} (Fin m))))
    (hQ : IsDirectSummandOfFiniteFree (cokernel S.g)) (x : X)
    (hx : Module.Finite ↑(colimit ((OpenNhds.inclusion x).op ⋙ (structureSheafOfRings X).obj))
        ((sheafColimitFunctor (structureSheafOfRings X) (OpenNhds.inclusion x).op).obj S.homology) ∧
      Module.Free ↑(colimit ((OpenNhds.inclusion x).op ⋙ (structureSheafOfRings X).obj))
        ((sheafColimitFunctor (structureSheafOfRings X) (OpenNhds.inclusion x).op).obj
          S.homology)) :
    ∃ W : Opens X, x ∈ W ∧ ∃ k : ℕ,
      Nonempty (S.homology.over W ≅ SheafOfModules.free (ULift.{max u v} (Fin k))) := by
  let R := structureSheafOfRings X
  let A := ShortComplex.mk (kernel.ι (cokernel.π S.g)) (cokernel.π S.g) (kernel.condition _)
  have hA : A.ShortExact := { exact := A.exact_of_f_is_kernel (kernelIsKernel _) }
  obtain ⟨U, hxU, ⟨rU⟩⟩ := exists_over_retract_of_shortExact A hA hQ x
  let Y := X.restrict U.isOpenEmbedding
  let F : OXMod.{max u v, max u v} X ⥤ OXMod.{max u v, max u v} Y := restrictSheafModules R U
  let : F.Additive := restrictSheafModules_additive R U
  let rIm : Retract (F.obj (Abelian.image S.g))
      (SheafOfModules.free (ULift.{max u v} (Fin n))) :=
    retractFreeRestrictOfOverRetract R U rU (restrictRetractFree R r₃ U)
  let rCoim : Retract (F.obj (Abelian.coimage S.g))
      (SheafOfModules.free (ULift.{max u v} (Fin n))) :=
    (F.mapIso (Abelian.coimageIsoImage S.g)).retract.trans rIm
  obtain ⟨q, hq, hB⟩ := exists_homology_opcycles_shortExact S
  let B := ShortComplex.mk S.homologyι q hq
  let : F.PreservesHomology := restrictSheafModules_preservesHomology R U
  let : Mono B.f := hB.mono_f
  let : Epi B.g := hB.epi_g
  let : PreservesFiniteLimits F := restrictSheafModules_preservesFiniteLimits R U
  let : F.IsLeftAdjoint := restrictSheafModules_isLeftAdjoint R U
  have hBF : (B.map F).ShortExact := hB.map F
  have hCoim : IsDirectSummandOfFiniteFree (X := Y) ((B.map F).X₃) :=
    directSummand_of_retract_free (X := Y) _ n rCoim
  obtain ⟨V, hxV, ⟨rV⟩⟩ := exists_over_retract_of_shortExact (X := Y)
    (B.map F) hBF hCoim ⟨x, hxU⟩
  let G := restrictSheafModules (structureSheafOfRings Y) V
  let rH : Retract (G.obj (F.obj S.homology))
      (SheafOfModules.free (ULift.{max u v} (Fin m))) :=
    retractFreeRestrictOfOverRetract (structureSheafOfRings Y) V rV
      (restrictRetractFree (structureSheafOfRings Y) (restrictRetractFree R rC U) V)
  have hxU' := finite_free_stalk_restriction R S.homology U ⟨x, hxU⟩ hx
  have hxV' := finite_free_stalk_restriction (structureSheafOfRings Y)
    (F.obj S.homology) V ⟨⟨x, hxU⟩, hxV⟩ hxU'
  obtain ⟨W, hxW, k, ⟨eW⟩⟩ := exists_chart_of_retract_free
    (structureSheafOfRings (Y.restrict V.isOpenEmbedding)) _ rH ⟨⟨x, hxU⟩, hxV⟩ hxV'
  obtain ⟨eV⟩ := chart_of_restriction (structureSheafOfRings Y) (F.obj S.homology) V W _ eW
  obtain ⟨eU⟩ := chart_of_restriction R S.homology U (V.isOpenEmbedding.functor.obj W) _ eV
  exact ⟨U.isOpenEmbedding.functor.obj (V.isOpenEmbedding.functor.obj W),
    ⟨⟨x, hxU⟩, ⟨⟨⟨x, hxU⟩, hxV⟩, hxW, rfl⟩, rfl⟩, k, ⟨eU⟩⟩

/-- A trivialisation of a sheaf of modules over an open set restricts to a trivialisation over
any smaller open set. -/
private def chartMono
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    (M : SheafOfModules.{max u v} R) {U V : Opens X} (hUV : U ≤ V)
    {I : Type (max u v)} (e : M.over V ≅ SheafOfModules.free I) :
    M.over U ≅ SheafOfModules.free I := by
  let f : U ⟶ V := homOfLE hUV
  let F := SheafOfModules.overMap R f
  exact ((SheafOfModules.overFunctorMap R f).app M).symm ≪≫ F.mapIso e ≪≫
    (SheafOfModules.mapFreeIso F I (SheafOfModules.overMapUnitIso (R := R) f).symm).symm

/-- Finite freeness of the stalk at a point is preserved by an isomorphism of sheaves of
modules. -/
private lemma finite_free_sheafColimit_of_iso
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    {M N : SheafOfModules.{max u v} R} (e : M ≅ N) (x : X)
    (h : Module.Finite ↑(colimit ((OpenNhds.inclusion x).op ⋙ R.obj))
        ((sheafColimitFunctor R (OpenNhds.inclusion x).op).obj M) ∧
      Module.Free ↑(colimit ((OpenNhds.inclusion x).op ⋙ R.obj))
        ((sheafColimitFunctor R (OpenNhds.inclusion x).op).obj M)) :
    Module.Finite ↑(colimit ((OpenNhds.inclusion x).op ⋙ R.obj))
        ((sheafColimitFunctor R (OpenNhds.inclusion x).op).obj N) ∧
      Module.Free ↑(colimit ((OpenNhds.inclusion x).op ⋙ R.obj))
        ((sheafColimitFunctor R (OpenNhds.inclusion x).op).obj N) := by
  let T := sheafColimitFunctor R (OpenNhds.inclusion x).op
  let e' : T.obj M ≅ T.obj N := T.mapIso e
  let := h.1
  let := h.2
  exact ⟨Module.Finite.equiv e'.toLinearEquiv, Module.Free.of_equiv e'.toLinearEquiv⟩

/-- Transporting a finite free stalk along the universe lift and across
`CategoryTheory.ShortComplex.mapHomologyIso`, with the colimit side of both the ring and the
module written out. The two spellings of the stalk differ only up to definitional unfolding of
the colimit module structure, so stating the step separately has the comparison carried out
against a written type instead of inside the proof that uses it. -/
private lemma finite_free_sheafColimit_mapSc_homology
    {X : RingedSpace.{u, v}} (K : CochainComplex (OXMod.{u, v} X) ℤ) (x : X) (i : ℤ)
    (h : Module.Finite (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x) ∧
      Module.Free (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x)) :
    Module.Finite ↑(colimit ((OpenNhds.inclusion x).op ⋙ (structureSheafULift X).obj))
        ((sheafColimitFunctor (structureSheafULift X) (OpenNhds.inclusion x).op).obj
          ((K.sc i).map (liftModulesFunctor X)).homology) ∧
      Module.Free ↑(colimit ((OpenNhds.inclusion x).op ⋙ (structureSheafULift X).obj))
        ((sheafColimitFunctor (structureSheafULift X) (OpenNhds.inclusion x).op).obj
          ((K.sc i).map (liftModulesFunctor X)).homology) := by
  let : (liftModulesFunctor X).PreservesHomology := liftModulesFunctor_preservesHomology X
  exact finite_free_sheafColimit_of_iso (structureSheafULift X)
    ((K.sc i).mapHomologyIso (liftModulesFunctor X)).symm x
    (finite_free_sheafColimit_moduleULift (K.homology i) x h)

/-- If all cohomology stalks of a strictly perfect complex at a point with local stalk are
finite free, the universe lift of each cohomology sheaf is finite free on an open
neighbourhood of that point. -/
private lemma exists_chart_lifted_homology
    {X : RingedSpace.{u, v}} (K : CochainComplex (OXMod.{u, v} X) ℤ)
    (hK : IsStrictlyPerfect K) (x : X) [IsLocalRing (structureSheafStalk X x)]
    (hx : ∀ j, Module.Finite (structureSheafStalk X x) (moduleSheafStalk (K.homology j) x) ∧
      Module.Free (structureSheafStalk X x) (moduleSheafStalk (K.homology j) x)) (i : ℤ) :
    ∃ U : Opens X, x ∈ U ∧ ∃ n : ℕ,
      Nonempty ((moduleSheafULift (K.homology i)).over U ≅
        SheafOfModules.free (ULift.{max u v} (Fin n))) := by
  let Y := ringedSpaceRingULift X
  let R := structureSheafULift X
  let L : CochainComplex (OXMod.{max u v, max u v} Y) ℤ :=
    ((liftModulesFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let S := L.sc i
  let j := (ComplexShape.up ℤ).next i
  have hprev : (ComplexShape.up ℤ).prev j = i :=
    (ComplexShape.up ℤ).prev_eq' ((ComplexShape.up ℤ).next_eq' rfl).symm
  let eQ : L.opcycles j ≅ cokernel S.g := by
    have e := (L.sc j).opcyclesIsoCokernel
    change L.opcycles j ≅ cokernel (L.d ((ComplexShape.up ℤ).prev j) j) at e
    rwa [hprev] at e
  obtain ⟨UC, hxC, m, ⟨eC⟩⟩ := exists_chart_lifted_opcycles K hK x hx i
  obtain ⟨UQ, hxQ, n, ⟨eqQ⟩⟩ := exists_chart_lifted_opcycles K hK x hx j
  let U : Opens Y := UC ⊓ UQ
  let F : OXMod.{max u v, max u v} Y ⥤ OXMod.{max u v, max u v} (Y.restrict U.isOpenEmbedding) :=
    restrictSheafModules (structureSheafOfRings Y) U
  let : F.Additive := restrictSheafModules_additive _ U
  let : F.PreservesHomology := restrictSheafModules_preservesHomology _ U
  let : F.IsLeftAdjoint := restrictSheafModules_isLeftAdjoint _ U
  let eCU : S.opcycles.over U ≅ SheafOfModules.free (ULift.{max u v} (Fin m)) :=
    chartMono R _ (show U ≤ UC from inf_le_left) eC
  let eQU : (cokernel S.g).over U ≅ SheafOfModules.free (ULift.{max u v} (Fin n)) :=
    (SheafOfModules.overFunctor R U).mapIso eQ.symm ≪≫
      chartMono R _ (show U ≤ UQ from inf_le_right) eqQ
  let rC : Retract (S.map F).opcycles (SheafOfModules.free (ULift.{max u v} (Fin m))) :=
    (S.mapOpcyclesIso F).retract.trans (overRetractFreeToRestrict R U eCU.retract)
  let rQ : Retract (cokernel (S.map F).g) (SheafOfModules.free (ULift.{max u v} (Fin n))) :=
    (PreservesCokernel.iso F S.g).symm.retract.trans (overRetractFreeToRestrict R U eQU.retract)
  have hQ := directSummand_of_retract_free (X := Y.restrict U.isOpenEmbedding) _ n rQ
  obtain ⟨a, ⟨r₃⟩⟩ := exists_retract_free_liftModulesFunctor (K.X j) (hK.directSummand j)
  let r₃' : Retract (S.map F).X₃ (SheafOfModules.free (ULift.{max u v} (Fin a))) :=
    restrictRetractFree R r₃ U
  let : (liftModulesFunctor X).PreservesHomology := liftModulesFunctor_preservesHomology X
  have hxL := finite_free_sheafColimit_mapSc_homology K x i (hx i)
  have hxU := finite_free_stalk_restriction R S.homology U ⟨x, hxC, hxQ⟩ hxL
  have hxS := finite_free_sheafColimit_of_iso (structureSheafOfRings (Y.restrict U.isOpenEmbedding))
    (S.mapHomologyIso F).symm ⟨x, hxC, hxQ⟩ hxU
  obtain ⟨V, hxV, k, ⟨eV⟩⟩ := exists_chart_homology_of_retracts
    (X := Y.restrict U.isOpenEmbedding) (S.map F) a m r₃' rC hQ ⟨x, hxC, hxQ⟩ hxS
  let eV' : (F.obj S.homology).over V ≅ SheafOfModules.free (ULift.{max u v} (Fin k)) :=
    (SheafOfModules.overFunctor _ V).mapIso (S.mapHomologyIso F).symm ≪≫ eV
  obtain ⟨eW⟩ := chart_of_restriction R S.homology U V _ eV'
  let W := U.isOpenEmbedding.functor.obj V
  exact ⟨W, ⟨⟨x, hxC, hxQ⟩, hxV, rfl⟩, k, ⟨(SheafOfModules.overFunctor R W).mapIso
    ((K.sc i).mapHomologyIso (liftModulesFunctor X)).symm ≪≫ eW⟩⟩

/-- A trivialisation of a sheaf of modules over an open set gives, after restriction to another
open set, a trivialisation over an open neighbourhood of any point of the latter lying in the
former. -/
private lemma exists_chart_restriction_of_chart
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    (M : SheafOfModules.{max u v} R) (U V : Opens X)
    (x : U) (hx : (x : X) ∈ V) (n : ℕ)
    (e : M.over V ≅ SheafOfModules.free (ULift.{max u v} (Fin n))) :
    ∃ W : Opens U, x ∈ W ∧ Nonempty
      (((restrictSheafModules R U).obj M).over W ≅
        SheafOfModules.free (ULift.{max u v} (Fin n))) := by
  let W := (Opens.map U.inclusion').obj V
  have hWV : U.isOpenEmbedding.functor.obj W ≤ V := by
    rw [Opens.functor_map_eq_inf]
    exact inf_le_left
  exact ⟨W, hx, (chart_restriction_iff R M U W _).mpr ⟨chartMono R M hWV e⟩⟩

/-- At a point of the finite free locus of a perfect object, the universe lift of each cohomology
sheaf is finite free on an open neighbourhood. -/
private lemma exists_chart_cohomology_of_mem
    {X : RingedSpace.{u, v}} [∀ x : X, IsLocalRing (structureSheafStalk X x)]
    [HasDerivedCategory.{w} (OXMod.{u, v} X)]
    (E : DerivedCategory (OXMod.{u, v} X)) (hE : IsPerfect E)
    (x : X) (hx : x ∈ cohomologyFiniteFreeLocus E) (i : ℤ) :
    ∃ U : Opens X, x ∈ U ∧ ∃ n : ℕ,
      Nonempty ((moduleSheafULift
        ((DerivedCategory.homologyFunctor (OXMod.{u, v} X) i).obj E)).over U ≅
          SheafOfModules.free (ULift.{max u v} (Fin n))) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  have hxK : x ∈ cohomologyFiniteFreeLocus (DerivedCategory.Q.obj K) := by
    rwa [cohomologyFiniteFreeLocus_eq_of_iso e]
  rw [cohomologyFiniteFreeLocus_Q] at hxK
  obtain ⟨I, U, hU, hP⟩ := hK
  have hxU : x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxU
  obtain ⟨P, hP, f, hf⟩ := hP j
  let : QuasiIso f := hf
  let Y := X.restrict (U j).isOpenEmbedding
  let : IsLocalRing (structureSheafStalk Y ⟨x, hj⟩) :=
    isLocalRing_structureSheafStalk_restrict X (U j) ⟨x, hj⟩
  have hPH := finite_free_homology_stalk_of_local_quasiIso K (U j) P f ⟨x, hj⟩ hxK
  obtain ⟨V, hxV, n, ⟨eV⟩⟩ := exists_chart_lifted_homology P hP ⟨x, hj⟩ hPH i
  let M := (DerivedCategory.homologyFunctor (OXMod.{u, v} X) i).obj E
  let F := restrictModules X (U j)
  let : F.PreservesHomology := restrictModules_preservesHomology X (U j)
  let eK : K.homology i ≅ M :=
    ((DerivedCategory.homologyFunctorFactors (OXMod.{u, v} X) i).app K).symm ≪≫
      (DerivedCategory.homologyFunctor (OXMod.{u, v} X) i).mapIso e
  let eP : P.homology i ≅ F.obj M :=
    asIso (HomologicalComplex.homologyMap f i) ≪≫ (K.sc i).mapHomologyIso F ≪≫ F.mapIso eK
  let eP' := (liftModulesFunctor Y).mapIso eP
  let eV' : (moduleSheafULift (F.obj M)).over V ≅
      SheafOfModules.free (ULift.{max u v} (Fin n)) :=
    (SheafOfModules.overFunctor (structureSheafULift Y) V).mapIso eP'.symm ≪≫ eV
  obtain ⟨eW⟩ := chart_of_restriction (structureSheafULift X) (moduleSheafULift M)
    (U j) V _ eV'
  exact ⟨(U j).isOpenEmbedding.functor.obj V, ⟨⟨x, hj⟩, hxV, rfl⟩, n, ⟨eW⟩⟩

/-- A sheaf of modules is finite locally free exactly when every point has an open neighbourhood
on which it is isomorphic to a finite free one. -/
private lemma isFiniteLocallyFree_iff_exists_local_free'
    {Y : TopCat.{v}} {R : Sheaf (Opens.grothendieckTopology Y) RingCat.{max u v}}
    (M : SheafOfModules.{max u v} R) :
    SheafOfModules.IsFiniteLocallyFree M ↔ ∀ y : Y, ∃ U : Opens Y, y ∈ U ∧ ∃ n : ℕ,
      Nonempty (M.over U ≅ SheafOfModules.free (ULift.{max u v} (Fin n))) :=
  isFiniteLocallyFree_iff_exists_local_free M

/-- If the restriction of a sheaf of modules to an open set is finite locally free, its stalks at
the points of that open set are finite free. -/
private lemma finite_free_stalk_of_isFiniteLocallyFree_restrict
    {X : RingedSpace.{u, v}} (M : OXMod.{u, v} X) (V : Opens X)
    (hM : IsFiniteLocallyFree ((restrictModules X V).obj M)) (x : V) :
    Module.Finite (structureSheafStalk X x) (moduleSheafStalk M x) ∧
      Module.Free (structureSheafStalk X x) (moduleSheafStalk M x) := by
  let Y := X.restrict V.isOpenEmbedding
  obtain ⟨W, hxW, n, ⟨e⟩⟩ :=
    (isFiniteLocallyFree_iff_exists_local_free'
      (moduleSheafULift ((restrictModules X V).obj M))).mp hM x
  exact (finite_free_stalk_restrict_iff M V x).mp <|
    finite_free_stalkColimit_of_chart (structureSheafULift Y)
      (moduleSheafULift ((restrictModules X V).obj M)) W
      ⟨x, hxW⟩ (ULift.{max u v} (Fin n)) e

end

/-- The locus where all cohomology stalks of a perfect object are finite free is open. -/
@[stacks 0GT1 "openness"]
theorem isOpen_cohomologyFiniteFreeLocus
    {X : RingedSpace.{u, v}}
    [∀ x : X, IsLocalRing (structureSheafStalk X x)]
    [HasDerivedCategory.{d} (OXMod.{u, v} X)]
    (E : DerivedCategory (OXMod.{u, v} X)) (hE : IsPerfect E) :
    IsOpen (cohomologyFiniteFreeLocus E) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  rw [← cohomologyFiniteFreeLocus_eq_of_iso e, cohomologyFiniteFreeLocus_Q, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨I, U, hU, hP⟩ := hK
  have hxU : x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxU
  obtain ⟨P, hP, f, hf⟩ := hP j
  let : QuasiIso f := hf
  let Y := X.restrict (U j).isOpenEmbedding
  let (y : Y) : IsLocalRing (structureSheafStalk Y y) :=
    isLocalRing_structureSheafStalk_restrict X (U j) y
  have hPH := finite_free_homology_stalk_of_local_quasiIso K (U j) P f ⟨x, hj⟩ hx
  obtain ⟨V, hxV, hV⟩ := exists_open_finite_free_homology_stalk P hP ⟨x, hj⟩ hPH
  let W := (U j).isOpenEmbedding.functor.obj V
  have hxW : x ∈ W := ⟨⟨x, hj⟩, hxV, rfl⟩
  refine Filter.mem_of_superset (W.isOpen.mem_nhds hxW) ?_
  rintro _ ⟨z, hz, rfl⟩ i
  exact finite_free_homology_stalk_of_local_quasiIso_reverse K (U j) P f z i (hV z hz i)

/-- On the finite free locus of a perfect object every cohomology sheaf is finite locally
free. -/
@[stacks 0GT1 "finite locally free"]
theorem isFiniteLocallyFree_homology_restrict_locus
    {X : RingedSpace.{u, v}}
    [∀ x : X, IsLocalRing (structureSheafStalk X x)]
    [HasDerivedCategory.{d} (OXMod.{u, v} X)]
    (E : DerivedCategory (OXMod.{u, v} X)) (hE : IsPerfect E)
    (i : ℤ) :
    IsFiniteLocallyFree
      ((restrictModules X
        ⟨cohomologyFiniteFreeLocus E,
          isOpen_cohomologyFiniteFreeLocus E hE⟩).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, v} X) i).obj E)) := by
  let V : Opens X := ⟨cohomologyFiniteFreeLocus E,
    isOpen_cohomologyFiniteFreeLocus E hE⟩
  refine (isFiniteLocallyFree_iff_exists_local_free' _).mpr fun x => ?_
  let M := (DerivedCategory.homologyFunctor (OXMod.{u, v} X) i).obj E
  obtain ⟨W, hxW, n, ⟨eW⟩⟩ := exists_chart_cohomology_of_mem E hE x.val x.property i
  obtain ⟨Z, hxZ, eZ⟩ := exists_chart_restriction_of_chart (structureSheafULift X)
    (moduleSheafULift M) V W x hxW n eW
  exact ⟨Z, hxZ, n, eZ⟩

/-- An open set on which all cohomology sheaves of a perfect object are finite locally free is
contained in its finite free locus; together with the previous result this says the locus is
the largest such open set. -/
@[stacks 0GT1 "maximality"]
theorem le_cohomologyFiniteFreeLocus_of_isFiniteLocallyFree
    {X : RingedSpace.{u, v}}
    [∀ x : X, IsLocalRing (structureSheafStalk X x)]
    [HasDerivedCategory.{d} (OXMod.{u, v} X)]
    (E : DerivedCategory (OXMod.{u, v} X)) (hE : IsPerfect E)
    (V : Opens X)
    (hV : ∀ i : ℤ, IsFiniteLocallyFree
      ((restrictModules X V).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, v} X) i).obj E))) :
    V ≤ ⟨cohomologyFiniteFreeLocus E,
      isOpen_cohomologyFiniteFreeLocus E hE⟩ := by
  intro x hx i
  exact finite_free_stalk_of_isFiniteLocallyFree_restrict
    ((DerivedCategory.homologyFunctor (OXMod.{u, v} X) i).obj E) V (hV i) ⟨x, hx⟩

end Stacks.Cohomology.PerfectComplexes

end
