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

/-!
# Universe-lifted sheaves of modules and their colimits along neighbourhoods

This file sets up the universe-lifting machinery used to state and prove [Stacks, Tag 0GT1]
(the finite free locus of the cohomology of a perfect complex) for a ringed space
`X : RingedSpace.{u, v}`.

## Main definitions

* `Stacks.Cohomology.PerfectComplexes.structureSheafULift`: the structure sheaf in a universe
  containing both the rings and the space.
* `Stacks.Cohomology.PerfectComplexes.liftModulesFunctor`: an `𝒪_X`-module regarded as a sheaf of
  modules over `structureSheafULift X`.
* `Stacks.Cohomology.PerfectComplexes.sheafColimitFunctor`: the colimit of the sections of a
  sheaf of modules along a filtered diagram, as a module over the colimit of the rings.

## Implementation notes

**Why the sections are lifted.** For a ringed space `X : RingedSpace.{u, v}` the structure
sheaf takes values in `RingCat.{u}` while the site `Opens X` lives in universe `v`, and
Mathlib's `SheafOfModules` and its finite-local-freeness predicate require the module sections
and the coefficient rings to share one universe. `structureSheafULift` and `moduleSheafULift`
therefore wrap sections in `ULift`, placing both in `max u v`. Nothing but the universe of the
sections changes, `liftModulesFunctor` being fully faithful on underlying presheaves.

**Stalks as neighbourhood colimits.** `TopCat.Presheaf.stalk` needs the colimit to exist at the
size of the site, so for mixed universes the stalk is taken as the colimit over `OpenNhds x`
directly, through `sheafColimitFunctor`, which equips the colimit of the sections of a sheaf of
modules along a filtered diagram with its action by the colimit of the rings. This file proves
that this colimit is exact and sends finite free sheaves to finite free modules.

## References

* [Stacks Project, Tag 0GT1](https://stacks.math.columbia.edu/tag/0GT1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
  AlgebraicGeometry.RingedSpace.PseudoCoherence

namespace Stacks.Cohomology.PerfectComplexes

universe u v d

attribute [local instance] HasDerivedCategory.standard

/-- A point of an open set `U` of a space `X`, read as a point of the open subspace `U`. -/
def opensPoint {X : TopCat.{v}} (U : Opens X) (x : U) :
    ((Opens.toTopCat X).obj U : Type v) := x

/-- An open set of an open set `U` of a space `X`, read as an open set of the open subspace
`U`. The ascription pins the ambient space to the bundled form `(Opens.toTopCat X).obj U`, which
is the spelling the `Over` and site instances are stated at; without it `Category (Over V)`
cannot be synthesized. -/
def opensOfRestrict {X : TopCat.{v}} (U : Opens X) (V : Opens U) :
    Opens ((Opens.toTopCat X).obj U : Type v) := V

/-- A point of an open set `U` of a ringed space `X`, read as a point of the open ringed
subspace `X` restricted to `U`. -/
def restrictPoint {X : RingedSpace.{u, v}} (U : Opens X) (x : U) :
    ((X.restrict U.isOpenEmbedding).carrier : Type v) := x

/-- Raise the universe of rings without changing their elements or operations. -/
def ringULift : RingCat.{u} ⥤ RingCat.{max u v} where
  obj R := RingCat.of (ULift.{v} R)
  map f := RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp (f.hom.comp ULift.ringEquiv.toRingHom))

/-- The structure sheaf in a universe containing both the rings and the space. -/
def structureSheafULift (X : RingedSpace.{u, v}) :
    Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{max u v} where
  obj := (structureSheafOfRings X).obj ⋙ ringULift.{u, v}
  property := by
    let : PreservesLimitsOfSize.{v, v} (forget CommRingCat.{u}) :=
      Functor.instPreservesLimitsOfSizeOfIsRightAdjoint _
    let : ReflectsLimitsOfSize.{v, v} (forget RingCat.{max u v}) :=
      ringForget_reflectsLimits
    apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget RingCat.{max u v})
    exact Presheaf.isSheaf_comp_of_isSheaf _ _ uliftFunctor.{v}
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget CommRingCat.{u}) X.sheaf.property)

section


/-- Regard an `𝒪_X`-module with sections in `max u v` as a sheaf of modules over the
universe-lifted structure sheaf, by restricting the scalars along `ULift R ≃+* R`. -/
def liftModuleScalars (X : RingedSpace.{u, v}) :
    OXMod.{u, max u v} X ⥤ SheafOfModules.{max u v} (structureSheafULift X) where
  obj M := by
    let (U : (Opens X)ᵒᵖ) : Module ((structureSheafULift X).obj.obj U)
        (M.val.presheaf.obj U) := Module.compHom _ ULift.ringEquiv.toRingHom
    exact {
      val := PresheafOfModules.ofPresheaf M.val.presheaf
        (fun _ _ f r m => M.val.map_smul f r.down m)
      isSheaf := M.isSheaf }
  map f := { val := {
    app := fun U => ModuleCat.ofHom {
      __ := (f.val.app U).hom.toAddMonoidHom
      map_smul' := fun r m => (f.val.app U).hom.map_smul r.down m }
    naturality := fun g => by ext m; exact congrArg (fun h => h m) (f.val.naturality g) } }

/-- Regard a sheaf of modules over the universe-lifted structure sheaf as an `𝒪_X`-module,
the inverse of `liftModuleScalars`. -/
private def unliftModuleScalars (X : RingedSpace.{u, v}) :
    SheafOfModules.{max u v} (structureSheafULift X) ⥤ OXMod.{u, max u v} X where
  obj M := by
    let (U : (Opens X)ᵒᵖ) :
        Module (ULift.{v} ((structureSheafOfRings X).obj.obj U)) (M.val.presheaf.obj U) :=
      (M.val.obj U).isModule
    let (U : (Opens X)ᵒᵖ) : Module ((structureSheafOfRings X).obj.obj U)
        (M.val.presheaf.obj U) := Module.compHom _
          (ULift.ringEquiv : ULift.{v} ((structureSheafOfRings X).obj.obj U) ≃+* _).symm.toRingHom
    exact {
      val := PresheafOfModules.ofPresheaf M.val.presheaf
        (fun _ _ f r m => M.val.map_smul f (ULift.up r) m)
      isSheaf := M.isSheaf }
  map f := { val := {
    app := fun U => ModuleCat.ofHom {
      __ := (f.val.app U).hom.toAddMonoidHom
      map_smul' := fun r m => (f.val.app U).hom.map_smul (ULift.up r) m }
    naturality := fun g => by ext m; exact congrArg (fun h => h m) (f.val.naturality g) } }

/-- Modules over the structure sheaf and modules over its universe lift are the same thing:
only the spelling of the coefficient ring changes. -/
private def liftModuleScalarsEquivalence (X : RingedSpace.{u, v}) :
    OXMod.{u, max u v} X ≌ SheafOfModules.{max u v} (structureSheafULift X) where
  functor := liftModuleScalars X
  inverse := unliftModuleScalars X
  unitIso := NatIso.ofComponents (fun M => Iso.refl _) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun M => Iso.refl _) (by intros; rfl)

/-- An `𝒪_X`-module, regarded as a sheaf of modules over the universe-lifted structure
sheaf of rings: the sections are wrapped in `ULift` and the scalar action is restricted along
the ring equivalence `ULift R ≃+* R`. -/
def liftModulesFunctor (X : RingedSpace.{u, v}) :
    OXMod.{u, v} X ⥤ SheafOfModules.{max u v} (structureSheafULift X) :=
  moduleULift.{u, v} X ⋙ liftModuleScalars X

/-- The universe lift of an `𝒪_X`-module, a sheaf of modules over `structureSheafULift X`. -/
abbrev moduleSheafULift {X : RingedSpace.{u, v}} (M : OXMod.{u, v} X) :
    SheafOfModules.{max u v} (structureSheafULift X) := (liftModulesFunctor X).obj M


/-- Rewriting the coefficient ring along the universe lift is additive. -/
private lemma liftModuleScalars_additive (X : RingedSpace.{u, v}) :
    (liftModuleScalars X).Additive where
  map_add := by intros; ext U m; rfl

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

/-- The universe lift of `𝒪_X^{⊕n}` is the free sheaf of modules on `ULift (Fin n)`. -/
private def liftFiniteFreeIso (X : RingedSpace.{u, v}) (n : ℕ) :
    (liftModuleScalars X).obj ((moduleULift.{v, u} X).obj (finiteFree X n)) ≅
      SheafOfModules.free (R := structureSheafULift X) (ULift.{max u v} (Fin n)) := by
  let : HasFiniteBiproducts (SheafOfModules.{max u v} (structureSheafULift X)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let F := moduleULift.{v, u} X ⋙ liftModuleScalars X
  let : (liftModuleScalars X).Additive := liftModuleScalars_additive X
  let e : F.obj (structureModule X) ≅ SheafOfModules.unit (structureSheafULift X) := Iso.refl _
  let e₁ := F.mapBiproduct (fun _ : Fin n => structureModule X)
  let e₂ : (⨁ fun _ : Fin n => F.obj (structureModule X)) ≅
      (⨁ fun _ : ULift.{max u v} (Fin n) => SheafOfModules.unit (structureSheafULift X)) :=
    biproduct.whiskerEquiv Equiv.ulift.symm (fun _ => e)
  exact e₁ ≪≫ e₂ ≪≫ biproduct.isoCoproduct _

/-- The universe lift of a direct summand of a finite free `𝒪_X`-module is a retract of a
free sheaf of modules on a finite index type. -/
lemma exists_retract_free_liftModulesFunctor
    {X : RingedSpace.{u, v}} (M : OXMod.{u, v} X)
    (hM : IsDirectSummandOfFiniteFree M) :
    ∃ n : ℕ, Nonempty (Retract ((liftModulesFunctor X).obj M)
      (SheafOfModules.free (ULift.{max u v} (Fin n)))) := by
  obtain ⟨n, ⟨r⟩⟩ := hM
  exact ⟨n, ⟨(r.map (liftModuleScalars X)).trans (liftFiniteFreeIso X n).retract⟩⟩


end

/-- `RingCat.{max u v}` has all colimits indexed by `v`-small categories. -/
local instance : HasColimitsOfSize.{v, v} RingCat.{max u v} :=
  hasColimitsOfSizeShrink.{v, v, max u v, max u v} _


section


universe w

section

variable {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J Ab.{v}] [J.WEqualsLocallyBijective Ab.{v}]
  [HasSheafify J Ab.{max u v}] [J.WEqualsLocallyBijective Ab.{max u v}]

omit [HasSheafify J Ab.{v}] [J.WEqualsLocallyBijective Ab.{v}]
  [J.WEqualsLocallyBijective Ab.{max u v}] in
/-- Raising the universe of the sections of a sheaf of abelian groups preserves finite limits. -/
private lemma sheafUlift_preservesFiniteLimits :
    PreservesFiniteLimits (sheafCompose J AddCommGrpCat.uliftFunctor.{u, v}) := by
  let F := sheafCompose J AddCommGrpCat.uliftFunctor.{u, v}
  let G := sheafToPresheaf J Ab.{max u v}
  let : PreservesFiniteLimits (F ⋙ G) := by
    change PreservesFiniteLimits (sheafToPresheaf J Ab.{v} ⋙
      (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{u, v})
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves F G

/-- Raising the universe of the sections of a sheaf of abelian groups preserves finite
colimits. -/
private lemma sheafUlift_preservesFiniteColimits :
    PreservesFiniteColimits (sheafCompose J AddCommGrpCat.uliftFunctor.{u, v}) := by
  let F := sheafCompose J AddCommGrpCat.uliftFunctor.{u, v}
  let L := presheafToSheaf J Ab.{v}
  let G := sheafToPresheaf J Ab.{v}
  let : J.PreservesSheafification AddCommGrpCat.uliftFunctor.{u, v} :=
    Stacks.Sheaves.UniverseLift.preservesSheafification_uliftFunctor.{v, v, v, u} (J := J)
  let e := sheafComposeNatIso J AddCommGrpCat.uliftFunctor.{u, v}
    (sheafificationAdjunction J Ab.{v}) (sheafificationAdjunction J Ab.{max u v})
  let : PreservesFiniteColimits (L ⋙ F) := preservesFiniteColimits_of_natIso e
  refine ⟨fun D _ _ => ⟨fun {K} => ?_⟩⟩
  have : PreservesColimit ((K ⋙ G) ⋙ L) F :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves L (colimit.isColimit (K ⋙ G)))
      (isColimitOfPreserves (L ⋙ F) (colimit.isColimit (K ⋙ G)))
  exact preservesColimit_of_iso_diagram F
    ((Functor.associator K G L) ≪≫ Functor.isoWhiskerLeft K
      (asIso (sheafificationAdjunction J Ab.{v}).counit) ≪≫ K.rightUnitor)

end

/-- Presheaves of abelian groups on the open sets of a space admit a sheafification. -/
private instance (X : TopCat.{v}) : HasSheafify (Opens.grothendieckTopology X) Ab.{max u v} :=
  hasSheafifyEssentiallySmallSite.{v, max u v, v, (max u v) + 1, max u v} _ _

/-- On the open sets of a space, a morphism of presheaves of abelian groups becomes an
isomorphism after sheafification exactly when it is locally bijective. -/
private instance (X : TopCat.{v}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective Ab.{max u v} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, max u v, v,
    (max u v) + 1, max u v} _

/-- Raising the universe of the sections of an `𝒪_X`-module preserves homology. -/
private lemma moduleULift_preservesHomology (X : RingedSpace.{u, v}) :
    (moduleULift.{u, v} X).PreservesHomology := by
  let J := Opens.grothendieckTopology X.carrier
  let F := moduleULift.{u, v} X
  let G := SheafOfModules.toSheaf.{max u v} (structureSheafOfRings X)
  let A := SheafOfModules.toSheaf.{v} (structureSheafOfRings X)
  let B := sheafCompose J AddCommGrpCat.uliftFunctor.{u, v}
  let : PreservesFiniteColimits G :=
    Stacks.SheafOfModules.toSheaf_preservesFiniteColimits.{max u v} _
  let : PreservesFiniteColimits A :=
    Stacks.SheafOfModules.toSheaf_preservesFiniteColimits.{v} _
  let : PreservesFiniteLimits B := sheafUlift_preservesFiniteLimits J
  let : PreservesFiniteColimits B := sheafUlift_preservesFiniteColimits J
  let e : F ⋙ G ≅ A ⋙ B := Iso.refl _
  let : PreservesFiniteLimits (F ⋙ G) := preservesFiniteLimits_of_natIso e.symm
  let : PreservesFiniteColimits (F ⋙ G) := preservesFiniteColimits_of_natIso e.symm
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  apply G.reflects_exact_of_faithful
  exact hS.map (F ⋙ G)

/-- The universe lift of `𝒪_X`-modules is additive. -/
lemma liftModulesFunctor_additive (X : RingedSpace.{u, v}) :
    (liftModulesFunctor X).Additive := by
  let : (liftModuleScalars X).Additive := liftModuleScalars_additive X
  change (moduleULift.{u, v} X ⋙ liftModuleScalars X).Additive
  infer_instance

attribute [local instance] liftModulesFunctor_additive

/-- The universe lift of `𝒪_X`-modules preserves homology. -/
lemma liftModulesFunctor_preservesHomology (X : RingedSpace.{u, v}) :
    (liftModulesFunctor X).PreservesHomology := by
  let J := Opens.grothendieckTopology X.carrier
  let : (moduleULift.{u, v} X).PreservesHomology := moduleULift_preservesHomology X
  let : (liftModuleScalars X).IsEquivalence :=
    (liftModuleScalarsEquivalence X).isEquivalence_functor
  let : (liftModuleScalars X).Additive := liftModuleScalars_additive X
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  exact (hS.map (moduleULift.{u, v} X)).map (liftModuleScalars X)

/-- The open neighbourhoods of a point are the elements of the fibre of the one-point
Grothendieck topology at that point. -/
private def openNhdsEquivPointElements {X : TopCat.{v}} (x : X) :
    OpenNhds x ≌ (Opens.pointGrothendieckTopology x).fiber.Elements where
  functor := {
    obj := fun U => .mk (obj := U.1) ⟨⟨U.2⟩⟩
    map := fun f => Functor.Elements.homMk (homOfLE (leOfHom f)) rfl }
  inverse := {
    obj := fun U => ⟨U.obj, U.val.down.down⟩
    map := fun f => homOfLE (leOfHom f.hom) }
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The colimit over the open neighbourhoods of a point, i.e. the stalk at it, on presheaves of
abelian groups whose sections lie in a universe containing that of the space. -/
private def neighbourhoodColimitFunctor {X : TopCat.{v}} (x : X) :
    ((Opens X)ᵒᵖ ⥤ Ab.{max u v}) ⥤ Ab.{max u v} :=
  (Functor.whiskeringLeft _ _ _).obj (OpenNhds.inclusion x).op ⋙ colim

/-- The neighbourhood colimit at a point is the fibre functor of the one-point Grothendieck
topology there. -/
private def neighbourhoodColimitIsoPointFiber {X : TopCat.{v}} (x : X) :
    neighbourhoodColimitFunctor.{u} x ≅
      (Opens.pointGrothendieckTopology x).presheafFiber (A := Ab.{max u v}) := by
  let E := (openNhdsEquivPointElements x).functor.op
  let P := (Functor.Elements.π (Opens.pointGrothendieckTopology x).fiber).op
  refine NatIso.ofComponents (fun M => Functor.Final.colimitIso E (P ⋙ M)) ?_
  intro M N f
  exact (Functor.Final.colimIso E (E := Ab.{max u v})).hom.naturality
    (Functor.whiskerLeft P f)

/-- Taking the stalk of a sheaf of abelian groups at a point preserves finite limits. -/
private lemma neighbourhoodSheafColimit_preservesFiniteLimits {X : TopCat.{v}} (x : X) :
    PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology X) Ab.{max u v} ⋙
        neighbourhoodColimitFunctor.{u} x) := by
  let : AB5OfSize.{v, v} Ab.{max u v} := AB5OfSize_shrink.{v, v, u, u} _
  let : PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology X) Ab.{max u v} ⋙
        (Opens.pointGrothendieckTopology x).presheafFiber) :=
    inferInstanceAs (PreservesFiniteLimits
      ((Opens.pointGrothendieckTopology x).sheafFiber (A := Ab.{max u v})))
  exact preservesFiniteLimits_of_natIso
    (Functor.isoWhiskerLeft _ (neighbourhoodColimitIsoPointFiber.{u} x).symm)

/-- Taking the stalk of a sheaf of abelian groups at a point preserves finite colimits. -/
private lemma neighbourhoodSheafColimit_preservesFiniteColimits {X : TopCat.{v}} (x : X) :
    PreservesFiniteColimits
      (sheafToPresheaf (Opens.grothendieckTopology X) Ab.{max u v} ⋙
        neighbourhoodColimitFunctor.{u} x) := by
  let : PreservesFiniteColimits
      (sheafToPresheaf (Opens.grothendieckTopology X) Ab.{max u v} ⋙
        (Opens.pointGrothendieckTopology x).presheafFiber) :=
    inferInstanceAs (PreservesFiniteColimits
      ((Opens.pointGrothendieckTopology x).sheafFiber (A := Ab.{max u v})))
  exact preservesFiniteColimits_of_natIso
    (Functor.isoWhiskerLeft _ (neighbourhoodColimitIsoPointFiber.{u} x).symm)

end

/-- A morphism of filtered diagrams of modules over a filtered diagram of rings induces a
linear map on the colimits. -/
def colimitLinearMap
    {C : Type v} [SmallCategory C] [IsFiltered C]
    (R : C ⥤ RingCat.{max u v}) (M N : C ⥤ Ab.{max u v})
    [∀ c, Module (R.obj c) (M.obj c)] [∀ c, Module (R.obj c) (N.obj c)]
    (hM : ∀ {i j} (f : i ⟶ j) r m, M.map f (r • m) = R.map f r • M.map f m)
    (hN : ∀ {i j} (f : i ⟶ j) r n, N.map f (r • n) = R.map f r • N.map f n)
    (f : M ⟶ N) (hf : ∀ c (r : R.obj c) (m : M.obj c),
      f.app c (r • m) = r • f.app c m) :
    letI : Module ↑(colimit R) ↑(colimit M) :=
      IsColimit.module R M hM (colimit.isColimit R) (colimit.isColimit M)
    letI : Module ↑(colimit R) ↑(colimit N) :=
      IsColimit.module R N hN (colimit.isColimit R) (colimit.isColimit N)
    ↑(colimit M) →ₗ[↑(colimit R)] ↑(colimit N) := by
  letI : Module ↑(colimit R) ↑(colimit M) :=
      IsColimit.module R M hM (colimit.isColimit R) (colimit.isColimit M)
  letI : Module ↑(colimit R) ↑(colimit N) :=
      IsColimit.module R N hN (colimit.isColimit R) (colimit.isColimit N)
  refine { (colimMap f).hom with map_smul' := ?_ }
  intro r m
  let : PreservesFilteredColimitsOfSize.{v, v} (forget RingCat.{max u v}) :=
    preservesFilteredColimitsOfSize_shrink _
  let : PreservesFilteredColimitsOfSize.{v, v} (forget Ab.{max u v}) :=
    preservesFilteredColimitsOfSize_shrink _
  obtain ⟨i, r, rfl⟩ := Concrete.colimit_exists_rep R r
  obtain ⟨j, m, rfl⟩ := Concrete.colimit_exists_rep M m
  let k := IsFiltered.max i j
  let a := IsFiltered.leftToMax i j
  let b := IsFiltered.rightToMax i j
  have hr : colimit.ι R i r = colimit.ι R k (R.map a r) :=
    (ConcreteCategory.congr_hom (colimit.w R a) r).symm
  have hm : colimit.ι M j m = colimit.ι M k (M.map b m) :=
    (ConcreteCategory.congr_hom (colimit.w M b) m).symm
  have hιM (r : R.obj k) (m : M.obj k) :
      colimit.ι M k (r • m) = colimit.ι R k r • colimit.ι M k m :=
    IsColimit.ι_smul R M hM (colimit.isColimit R) (colimit.isColimit M) k r m
  have hιN (r : R.obj k) (n : N.obj k) :
      colimit.ι N k (r • n) = colimit.ι R k r • colimit.ι N k n :=
    IsColimit.ι_smul R N hN (colimit.isColimit R) (colimit.isColimit N) k r n
  change colimMap f (colimit.ι R i r • colimit.ι M j m) =
    colimit.ι R i r • colimMap f (colimit.ι M j m)
  rw [hr, hm, ← hιM]
  change (colimit.ι M k ≫ colimMap f) _ = _
  rw [ι_colimMap]
  change colimit.ι N k (f.app k (_ • _)) = _
  rw [hf, hιN]
  congr 1
  exact (ConcreteCategory.congr_hom (ι_colimMap f k) (M.map b m)).symm


section

/-- Any colimit cocone of a filtered diagram of modules is isomorphic to the chosen colimit,
semilinearly over the induced isomorphism of the two colimits of rings. -/
def colimitModuleEquiv
    {C : Type v} [SmallCategory C] [IsFiltered C]
    (R : C ⥤ RingCat.{max u v}) (M : C ⥤ Ab.{max u v})
    [∀ c, Module (R.obj c) (M.obj c)]
    (hM : ∀ {i j} (f : i ⟶ j) r m, M.map f (r • m) = R.map f r • M.map f m)
    (cR : Cocone R) (hcR : IsColimit cR) (cM : Cocone M) (hcM : IsColimit cM)
    [Module cR.pt cM.pt]
    (hι : ∀ i (r : R.obj i) (m : M.obj i),
      (cM.ι.app i).hom (r • m) =
        @HSMul.hSMul ↑cR.pt ↑cM.pt ↑cM.pt inferInstance
          ((cR.ι.app i).hom r) ((cM.ι.app i).hom m)) :
    letI : Module ↑(colimit R) ↑(colimit M) :=
      IsColimit.module R M hM (colimit.isColimit R) (colimit.isColimit M)
    let e : colimit R ≅ cR.pt := (colimit.isColimit R).coconePointUniqueUpToIso hcR
    let eR := e.ringCatIsoToRingEquiv
    letI : RingHomInvPair eR.toRingHom eR.symm.toRingHom := RingHomInvPair.of_ringEquiv eR
    letI : RingHomInvPair eR.symm.toRingHom eR.toRingHom := RingHomInvPair.of_ringEquiv_symm eR
    LinearEquiv eR.toRingHom (σ' := eR.symm.toRingHom)
      ↑(colimit M) ↑cM.pt := by
  letI : Module ↑(colimit R) ↑(colimit M) :=
    IsColimit.module R M hM (colimit.isColimit R) (colimit.isColimit M)
  let eR : colimit R ≅ cR.pt := (colimit.isColimit R).coconePointUniqueUpToIso hcR
  let eM : colimit M ≅ cM.pt := (colimit.isColimit M).coconePointUniqueUpToIso hcM
  let q := ((colimit.isColimit R).coconePointUniqueUpToIso hcR).ringCatIsoToRingEquiv
  letI : RingHomInvPair q.toRingHom q.symm.toRingHom := RingHomInvPair.of_ringEquiv q
  letI : RingHomInvPair q.symm.toRingHom q.toRingHom := RingHomInvPair.of_ringEquiv_symm q
  refine { eM.addCommGroupIsoToAddEquiv with map_smul' := ?_ }
  intro r m
  let : PreservesFilteredColimitsOfSize.{v, v} (forget RingCat.{max u v}) :=
    preservesFilteredColimitsOfSize_shrink _
  let : PreservesFilteredColimitsOfSize.{v, v} (forget Ab.{max u v}) :=
    preservesFilteredColimitsOfSize_shrink _
  obtain ⟨i, r, rfl⟩ := Concrete.colimit_exists_rep R r
  obtain ⟨j, m, rfl⟩ := Concrete.colimit_exists_rep M m
  let k := IsFiltered.max i j
  have hr : colimit.ι R i r =
      colimit.ι R k (R.map (IsFiltered.leftToMax i j) r) :=
    (ConcreteCategory.congr_hom (colimit.w R (IsFiltered.leftToMax i j)) r).symm
  have hm : colimit.ι M j m =
      colimit.ι M k (M.map (IsFiltered.rightToMax i j) m) :=
    (ConcreteCategory.congr_hom (colimit.w M (IsFiltered.rightToMax i j)) m).symm
  have hR (a : R.obj k) : eR.hom (colimit.ι R k a) = cR.ι.app k a :=
    ConcreteCategory.congr_hom
      ((colimit.isColimit R).comp_coconePointUniqueUpToIso_hom hcR k) a
  have hN (a : M.obj k) : eM.hom (colimit.ι M k a) = cM.ι.app k a :=
    ConcreteCategory.congr_hom
      ((colimit.isColimit M).comp_coconePointUniqueUpToIso_hom hcM k) a
  change eM.hom (colimit.ι R i r • colimit.ι M j m) =
    eR.hom (colimit.ι R i r) • eM.hom (colimit.ι M j m)
  have hC (r : R.obj k) (m : M.obj k) :
      colimit.ι M k (r • m) = colimit.ι R k r • colimit.ι M k m :=
    IsColimit.ι_smul R M hM (colimit.isColimit R) (colimit.isColimit M) k r m
  rw [hr, hm, ← hC, hN, hR, hN]
  exact hι k _ _

/-- The morphism of presheaves of abelian groups underlying a morphism of sheaves of modules,
written as a morphism between the section presheaves `M.val.presheaf ⟶ N.val.presheaf`, which
is the spelling the colimit constructions below use. -/
def sectionsMap {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{max u v}} {M N : SheafOfModules.{max u v} R} (f : M ⟶ N) :
    M.val.presheaf ⟶ N.val.presheaf :=
  (PresheafOfModules.toPresheaf R.obj).map f.val

/-- `sectionsMap` sends the identity of `M` to the identity of its underlying presheaf. -/
@[simp]
lemma sectionsMap_id {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{max u v}} (M : SheafOfModules.{max u v} R) :
    sectionsMap (𝟙 M) = 𝟙 M.val.presheaf := by
  ext j m
  rfl

/-- `sectionsMap` sends a composite `f ≫ g` to the composite of `sectionsMap f` and
`sectionsMap g`. -/
@[simp]
lemma sectionsMap_comp {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{max u v}} {M N P : SheafOfModules.{max u v} R}
    (f : M ⟶ N) (g : N ⟶ P) :
    sectionsMap (f ≫ g) = sectionsMap f ≫ sectionsMap g := by
  ext j m
  rfl

/-- The colimit of the sections of a sheaf of modules along a filtered diagram of objects of
the site, as a module over the corresponding colimit of rings. -/
def sheafColimitFunctor
    {C D : Type v} [SmallCategory C] [SmallCategory D] [IsFiltered D]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{max u v}) (F : D ⥤ Cᵒᵖ) :
    SheafOfModules.{max u v} R ⥤ ModuleCat.{max u v} (↑(colimit (F ⋙ R.obj)) : Type (max u v)) where
  obj M := by
    letI (j : D) : Module ((F ⋙ R.obj).obj j) ((F ⋙ M.val.presheaf).obj j) :=
      (M.val.obj (F.obj j)).isModule
    letI : Module ↑(colimit (F ⋙ R.obj)) ↑(colimit (F ⋙ M.val.presheaf)) :=
      IsColimit.module (F ⋙ R.obj) (F ⋙ M.val.presheaf)
      (fun f r m => M.val.map_smul (F.map f) r m)
      (colimit.isColimit _) (colimit.isColimit _)
    exact ModuleCat.of _ (↑(colimit (F ⋙ M.val.presheaf)) : Type (max u v))
  map {M N} f := by
    letI (j : D) : Module ((F ⋙ R.obj).obj j) ((F ⋙ M.val.presheaf).obj j) :=
      (M.val.obj (F.obj j)).isModule
    letI (j : D) : Module ((F ⋙ R.obj).obj j) ((F ⋙ N.val.presheaf).obj j) :=
      (N.val.obj (F.obj j)).isModule
    letI : Module ↑(colimit (F ⋙ R.obj)) ↑(colimit (F ⋙ M.val.presheaf)) :=
      IsColimit.module (F ⋙ R.obj) (F ⋙ M.val.presheaf)
        (fun g r m => M.val.map_smul _ _ _) (colimit.isColimit _) (colimit.isColimit _)
    letI : Module ↑(colimit (F ⋙ R.obj)) ↑(colimit (F ⋙ N.val.presheaf)) :=
      IsColimit.module (F ⋙ R.obj) (F ⋙ N.val.presheaf)
        (fun g r m => N.val.map_smul _ _ _) (colimit.isColimit _) (colimit.isColimit _)
    exact ModuleCat.ofHom (colimitLinearMap (F ⋙ R.obj)
      (F ⋙ M.val.presheaf) (F ⋙ N.val.presheaf)
      (fun g r m => M.val.map_smul _ _ _)
      (fun g r m => N.val.map_smul _ _ _)
      (Functor.whiskerLeft F (sectionsMap f))
      (fun j r m => (f.val.app (F.obj j)).hom.map_smul r m))
  map_id M := by
    apply ModuleCat.hom_ext
    apply DFunLike.ext
    intro m
    change colimMap (C := Ab) (Functor.whiskerLeft F (sectionsMap (𝟙 M))) m = m
    rw [sectionsMap_id, Functor.whiskerLeft_id', colimMap_eq]
    exact ConcreteCategory.congr_hom (colim.map_id (F ⋙ M.val.presheaf)) m
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply DFunLike.ext
    intro m
    change colimMap (C := Ab) (Functor.whiskerLeft F (sectionsMap (f ≫ g))) m =
      colimMap (C := Ab) (Functor.whiskerLeft F (sectionsMap g))
        (colimMap (C := Ab) (Functor.whiskerLeft F (sectionsMap f)) m)
    rw [sectionsMap_comp, Functor.whiskerLeft_comp, colimMap_eq, colimMap_eq, colimMap_eq,
      Functor.map_comp, ConcreteCategory.comp_apply]

/-- Taking the colimit of the sections of a sheaf of modules along a filtered diagram is
additive. -/
lemma sheafColimitFunctor_additive
    {C D : Type v} [SmallCategory C] [SmallCategory D] [IsFiltered D]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{max u v}) (F : D ⥤ Cᵒᵖ) :
    (sheafColimitFunctor R F).Additive where
  map_add {M N} f g := by
    let t (f : M ⟶ N) : (F ⋙ M.val.presheaf) ⟶ (F ⋙ N.val.presheaf) :=
      Functor.whiskerLeft F (sectionsMap f)
    have h : colimMap (t (f + g)) = colimMap (t f) + colimMap (t g) := by
      refine colimit.hom_ext fun j => ?_
      simp only [ι_colimMap, Preadditive.comp_add]
      ext m
      exact (colimit.ι (F ⋙ N.val.presheaf) j).hom.map_add _ _
    ext m
    exact ConcreteCategory.congr_hom h m


/-- The underlying abelian-group stalk of a sheaf of modules is the neighbourhood colimit of its
underlying sheaf of abelian groups. -/
private def sheafColimitFunctorCompForget₂Iso
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v}) (x : X) :
    sheafColimitFunctor R (OpenNhds.inclusion x).op ⋙ forget₂ (ModuleCat.{max u v}
      (↑(colimit ((OpenNhds.inclusion x).op ⋙ R.obj)) : Type (max u v))) Ab.{max u v} ≅
    SheafOfModules.toSheaf.{max u v} R ⋙
      (sheafToPresheaf (Opens.grothendieckTopology X) Ab.{max u v} ⋙
        neighbourhoodColimitFunctor.{u} x) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- Taking the stalk of a sheaf of modules at a point preserves finite limits. -/
lemma sheafColimitFunctor_preservesFiniteLimits
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    (x : X) : PreservesFiniteLimits (sheafColimitFunctor R (OpenNhds.inclusion x).op) := by
  let : PreservesFiniteLimits (sheafToPresheaf (Opens.grothendieckTopology X) Ab.{max u v} ⋙
    neighbourhoodColimitFunctor.{u} x) := neighbourhoodSheafColimit_preservesFiniteLimits x
  let : PreservesFiniteLimits (sheafColimitFunctor R (OpenNhds.inclusion x).op ⋙ _) :=
    preservesFiniteLimits_of_natIso (sheafColimitFunctorCompForget₂Iso.{u} R x).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (forget₂ _ Ab.{max u v})

/-- Taking the stalk of a sheaf of modules at a point preserves finite colimits. -/
lemma sheafColimitFunctor_preservesFiniteColimits
    {X : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{max u v})
    (x : X) : PreservesFiniteColimits (sheafColimitFunctor R (OpenNhds.inclusion x).op) := by
  let : PreservesFiniteColimits (SheafOfModules.toSheaf.{max u v} R) :=
    Stacks.SheafOfModules.toSheaf_preservesFiniteColimits.{max u v} R
  let : PreservesFiniteColimits (sheafToPresheaf (Opens.grothendieckTopology X) Ab.{max u v} ⋙
    neighbourhoodColimitFunctor.{u} x) := neighbourhoodSheafColimit_preservesFiniteColimits x
  let : PreservesFiniteColimits (sheafColimitFunctor R (OpenNhds.inclusion x).op ⋙ _) :=
    preservesFiniteColimits_of_natIso (sheafColimitFunctorCompForget₂Iso.{u} R x).symm
  exact preservesFiniteColimits_of_reflects_of_preserves _ (forget₂ _ Ab.{max u v})

/-- The colimit of the sections of the unit sheaf of modules is the colimit of the rings itself,
hence free of rank one over it. -/
private lemma finite_free_sheafColimit_unit
    {C D : Type v} [SmallCategory C] [SmallCategory D] [IsFiltered D]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{max u v}) (F : D ⥤ Cᵒᵖ) :
    Module.Finite ↑(colimit (F ⋙ R.obj))
      ((sheafColimitFunctor R F).obj (SheafOfModules.unit R)) ∧
    Module.Free ↑(colimit (F ⋙ R.obj))
      ((sheafColimitFunctor R F).obj (SheafOfModules.unit R)) := by
  let A := F ⋙ R.obj
  let M := F ⋙ (SheafOfModules.unit R).val.presheaf
  let U := forget₂ RingCat.{max u v} Ab.{max u v}
  let : PreservesFilteredColimitsOfSize.{v, v} U :=
    preservesFilteredColimitsOfSize_shrink U
  let cM : Cocone M := U.mapCocone (colimit.cocone A)
  let hcM : IsColimit cM := isColimitOfPreserves U (colimit.isColimit A)
  let (j : D) : Module (A.obj j) (M.obj j) :=
    ((SheafOfModules.unit R).val.obj (F.obj j)).isModule
  let : Module ↑(colimit.cocone A).pt ↑cM.pt := by
    dsimp [cM, U]
    infer_instance
  let : Module ↑(colimit A) ↑(colimit M) :=
    ((sheafColimitFunctor R F).obj (SheafOfModules.unit R)).isModule
  let e := colimitModuleEquiv A M
    (fun g r m => (SheafOfModules.unit R).val.map_smul (F.map g) r m)
    (colimit.cocone A) (colimit.isColimit A) cM hcM
    (fun j r m => (colimit.ι A j).hom.map_mul r m)
  let : Module.Finite ↑(colimit.cocone A).pt cM.pt := Module.Finite.self _
  let : Module.Free ↑(colimit.cocone A).pt cM.pt := Module.Free.self _
  let q := ((colimit.isColimit A).coconePointUniqueUpToIso
    (colimit.isColimit A)).ringCatIsoToRingEquiv
  let : RingHomInvPair q.toRingHom q.symm.toRingHom := RingHomInvPair.of_ringEquiv q
  let : RingHomInvPair q.symm.toRingHom q.toRingHom := RingHomInvPair.of_ringEquiv_symm q
  exact ⟨Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective,
    Module.Free.of_equiv e.symm⟩

/-- The colimit of the sections of a free sheaf of modules on a finite index type is finite free
over the colimit of the rings. -/
lemma finite_free_sheafColimit_free
    {C D : Type v} [SmallCategory C] [SmallCategory D] [IsFiltered D]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{max u v}) (F : D ⥤ Cᵒᵖ)
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (I : Type (max u v)) [Finite I] :
    Module.Finite ↑(colimit (F ⋙ R.obj))
      ((sheafColimitFunctor R F).obj (SheafOfModules.free I)) ∧
    Module.Free ↑(colimit (F ⋙ R.obj))
      ((sheafColimitFunctor R F).obj (SheafOfModules.free I)) := by
  classical
  let T := sheafColimitFunctor R F
  let : T.Additive := sheafColimitFunctor_additive R F
  have h := finite_free_sheafColimit_unit R F
  let := h.1
  let := h.2
  let : ∀ _ : I, Module.Finite ↑(colimit (F ⋙ R.obj))
      ↑(T.obj (SheafOfModules.unit R)) := fun _ => h.1
  let : ∀ _ : I, Module.Free ↑(colimit (F ⋙ R.obj))
      ↑(T.obj (SheafOfModules.unit R)) := fun _ => h.2
  let : Fintype I := Fintype.ofFinite I
  let e := PreservesCoproduct.iso T (fun _ : I => SheafOfModules.unit R) ≪≫
    ModuleCat.coprodIsoDirectSum (fun _ : I => T.obj (SheafOfModules.unit R))
  let e' := e.toLinearEquiv.trans DFinsupp.linearEquivFunOnFintype
  exact ⟨Module.Finite.equiv e'.symm, Module.Free.of_equiv e'.symm⟩


end

end Stacks.Cohomology.PerfectComplexes

end
