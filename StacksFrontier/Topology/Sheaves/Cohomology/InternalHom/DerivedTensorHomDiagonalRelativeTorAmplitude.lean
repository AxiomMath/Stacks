module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentTriangle
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TransportAlongIso
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackAmplitude
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackPerfectAndPseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalLocal
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.ModulesSpelling
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.RingedSiteComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0ATN part (3) relative to a flat morphism

Let `h : X' ⟶ X` be a flat morphism of ringed spaces, `A ∈ D(𝒪_X)` pseudo-coherent,
`N ∈ D(𝒪_X)` locally bounded below and `F ∈ D(𝒪_{X'})`. Stacks 0ATN part (3) on `X'` would ask
`F` to have finite Tor dimension over `𝒪_{X'}`. Here `F` is only asked to have Tor amplitude
bounded below *relative to `h`*: near every point of `X'` there is an integer `a` such that
`F ⊗^L Lh^*N'` has no cohomology below `a + b` for every `N' ∈ D(𝒪_X)` with no cohomology below
`b`. Then the diagonal of Stacks 0BYS on `X'`,

`F ⊗^L RSheafHom(Lh^*A, Lh^*N) ⟶ RSheafHom(Lh^*A, F ⊗^L Lh^*N)`,

is an isomorphism.

## Main definitions

* `LocallyHasRelativeTorAmplitudeGE`: Tor amplitude bounded below relative to a morphism of ringed
  spaces, locally on the source.

## Main results

* `isIso_derivedTensorHomDiagonal_derivedPullback_of_locallyHasRelativeTorAmplitudeGE`: the
  statement above.
* `exists_mem_isIso_homologyMap_restrictDerived_derivedTensorHomDiagonal`: its degree-`n` form
  near a point.
* `exists_distTriang_jShriek`: the global triangle of a local strictly perfect approximation.
* `restrictDerivedIsoDerivedPullback`: restriction to the slice over an open is derived pullback
  to the open subspace, transported to the slice.

## References

* [Stacks Project, Tag 0ATN](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Tag 0BYS](https://stacks.math.columbia.edu/tag/0BYS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry Stacks.Cohomology.HigherDirectImage

namespace Stacks.Cohomology.DerivedInternalHomPullback

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf


attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor


section Bridge

variable (Y : AlgebraicGeometry.RingedSpace.{u, u}) (W : TopologicalSpace.Opens Y.carrier)

/-- An exact functor read on derived categories preserves upper bounds on cohomology. -/
@[sga "6 I 2.13" "special case"]
theorem isLE_mapDerivedCategory_obj {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (K : DerivedCategory C) (a : ℤ)
    (hK : K.IsLE a) : (F.mapDerivedCategory.obj K).IsLE a := by
  rw [DerivedCategory.isLE_iff] at hK ⊢
  intro i hi
  exact (F.map_isZero (hK i hi)).of_iso
    ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F i).app K)

/-- Pullback to an open subspace, in the spelling of the restricted ringed space. -/
abbrev restrictPullback : StrictlyPerfect.OXMod.{u, u} Y ⥤
    StrictlyPerfect.OXMod.{u, u} (Y.restrict W.isOpenEmbedding) :=
  RingedSpaceModuleAdjunction.modulePullback (openSubspaceInclusion Y W)

/-- Pullback to an open subspace is additive. -/
theorem restrictPullback_additive : (restrictPullback Y W).Additive :=
  RingedSpaceModuleAdjunction.modulePullback_additive _

/-- Pullback to an open subspace preserves homology. -/
private theorem restrictPullback_preservesHomology
    [(restrictPullback Y W).PreservesZeroMorphisms] :
    (restrictPullback Y W).PreservesHomology :=
  have : AlgebraicGeometry.SheafedSpace.IsOpenImmersion (openSubspaceInclusion Y W) :=
    AlgebraicGeometry.SheafedSpace.IsOpenImmersion.ofRestrict Y W.isOpenEmbedding
  Stacks.Cohomology.DerivedOpenImmersion.modulePullbackOpenImmersion_preservesHomology _

/-- Pullback to an open subspace is left exact. -/
theorem restrictPullback_preservesFiniteLimits : PreservesFiniteLimits (restrictPullback Y W) :=
  have := restrictPullback_additive Y W
  have := restrictPullback_preservesHomology Y W
  Functor.preservesFiniteLimits_of_preservesHomology (restrictPullback Y W)

/-- Pullback to an open subspace is right exact. -/
theorem restrictPullback_preservesFiniteColimits :
    PreservesFiniteColimits (restrictPullback Y W) :=
  have := restrictPullback_additive Y W
  have := restrictPullback_preservesHomology Y W
  Functor.preservesFiniteColimits_of_preservesHomology (restrictPullback Y W)

/-- Pullback to an open subspace followed by the transport to the slice is additive. -/
theorem restrictPullbackBackward_additive :
    (restrictPullback Y W ⋙
      AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictBackward Y W).Additive :=
  have := restrictPullback_additive Y W
  inferInstance

/-- Pullback to an open subspace followed by the transport to the slice is left exact. -/
theorem restrictPullbackBackward_preservesFiniteLimits :
    PreservesFiniteLimits (restrictPullback Y W ⋙
      AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictBackward Y W) :=
  have := restrictPullback_preservesFiniteLimits Y W
  inferInstance

/-- Pullback to an open subspace followed by the transport to the slice is right exact. -/
theorem restrictPullbackBackward_preservesFiniteColimits :
    PreservesFiniteColimits (restrictPullback Y W ⋙
      AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictBackward Y W) :=
  have := restrictPullback_preservesFiniteColimits Y W
  inferInstance

/-- Restriction to the slice, read in the spelling of the structure sheaf of rings of the
space. -/
def overFunctorIsoRestrictPullback :
    _root_.SheafOfModules.overFunctor.{u} (StrictlyPerfect.structureSheafOfRings Y) W ≅
      restrictPullback Y W ⋙ AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictBackward Y W :=
  (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModulesCompBackwardIso Y W).symm ≪≫
    Functor.isoWhiskerRight
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.restrictModulesIsoPullback Y W) _

/-- **Restriction to the slice over an open is the derived pullback to the open subspace,
transported along the equivalence of module categories.** -/
def restrictDerivedIsoDerivedPullback :
    AlgebraicGeometry.RingedSite.restrictDerived (Stacks.SheafOfModules.ringedSite Y.sheaf) W ≅
      derivedPullbackFunctor (openSubspaceInclusion Y W) ⋙
        (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictBackward Y W).mapDerivedCategory :=
  haveI : AlgebraicGeometry.SheafedSpace.IsOpenImmersion (openSubspaceInclusion Y W) :=
    AlgebraicGeometry.SheafedSpace.IsOpenImmersion.ofRestrict Y W.isOpenEmbedding
  @Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _ _ _ _ _ _ _
      (_root_.SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite Y.sheaf).O) W)
      _ inferInstance inferInstance inferInstance
      (restrictPullbackBackward_additive Y W) (restrictPullbackBackward_preservesFiniteLimits Y W)
      (restrictPullbackBackward_preservesFiniteColimits Y W) (overFunctorIsoRestrictPullback Y W) ≪≫
    @Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _
      (restrictPullback Y W) (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictBackward Y W)
      (restrictPullback_additive Y W) (restrictPullback_preservesFiniteLimits Y W)
      (restrictPullback_preservesFiniteColimits Y W) inferInstance inferInstance inferInstance ≪≫
    Functor.isoWhiskerRight
      (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso
        (openSubspaceInclusion Y W)).symm _


/-- A lower bound on cohomology after derived pullback to an open subspace gives the same bound
after restriction to the slice over that open. -/
theorem isGE_restrictDerived_of_isGE
    (G : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) (c : ℤ)
    (hG : ((derivedPullbackFunctor (openSubspaceInclusion Y W)).obj G).IsGE c) :
    ((AlgebraicGeometry.RingedSite.restrictDerived (Stacks.SheafOfModules.ringedSite Y.sheaf)
      W).obj G).IsGE c := by
  have h' := isGE_mapDerivedCategory_obj
    (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictBackward Y W) _ c hG
  rw [DerivedCategory.isGE_iff] at h' ⊢
  intro i hi
  exact (h' i hi).of_iso ((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      ((Stacks.SheafOfModules.ringedSite Y.sheaf).over W).O)) i).mapIso
    ((restrictDerivedIsoDerivedPullback Y W).app G))

/-- An upper bound on cohomology after derived pullback to an open subspace gives the same bound
after restriction to the slice over that open. -/
theorem isLE_restrictDerived_of_isLE
    (G : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) (c : ℤ)
    (hG : ((derivedPullbackFunctor (openSubspaceInclusion Y W)).obj G).IsLE c) :
    ((AlgebraicGeometry.RingedSite.restrictDerived (Stacks.SheafOfModules.ringedSite Y.sheaf)
      W).obj G).IsLE c := by
  have h' := isLE_mapDerivedCategory_obj
    (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictBackward Y W) _ c hG
  rw [DerivedCategory.isLE_iff] at h' ⊢
  intro i hi
  exact (h' i hi).of_iso ((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      ((Stacks.SheafOfModules.ringedSite Y.sheaf).over W).O)) i).mapIso
    ((restrictDerivedIsoDerivedPullback Y W).app G))

end Bridge

section Predicate

variable {X' X : AlgebraicGeometry.RingedSpace.{u, u}} (h : X' ⟶ X)

/-- **Tor amplitude bounded below relative to `h : X' ⟶ X`, locally on `X'`.** Every point of
`X'` has an open neighbourhood `U` and an integer `a` such that, for every `N ∈ D(𝒪_X)` whose
cohomology vanishes below `b`, the restriction to `U` of `F ⊗^L_{𝒪_{X'}} Lh^*N` has no
cohomology below `a + b`. Since `F ⊗^L_{𝒪_{X'}} Lh^*N = F ⊗^L_{h^{-1}𝒪_X} h^{-1}N`, this is a
lower bound on the Tor amplitude of `F` over `h^{-1}𝒪_X`, tested against the objects pulled back
from `X`. -/
def LocallyHasRelativeTorAmplitudeGE
    (F : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X')) :
    Prop :=
  ∀ x' : X'.carrier, ∃ U : TopologicalSpace.Opens X'.carrier, x' ∈ U ∧ ∃ a : ℤ,
    ∀ (N : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))
      (b : ℤ), N.IsGE b →
        ((derivedPullbackFunctor (openSubspaceInclusion X' U)).obj
          ((internalHomTensorUncurried X').obj (F, (derivedPullbackFunctor h).obj N))).IsGE
            (a + b)

end Predicate

section Lift

variable {Z Y : AlgebraicGeometry.RingedSpace.{u, u}}

/-- A morphism with image in an open `U` has image in the image of the inclusion of `U`. -/
theorem range_subset_range_openSubspaceInclusion (g : Z ⟶ Y)
    (U : TopologicalSpace.Opens Y.carrier) (hg : ∀ z : Z.carrier, g.hom.base z ∈ U) :
    Set.range g.hom.base ⊆ Set.range (openSubspaceInclusion Y U).hom.base := by
  rintro _ ⟨z, rfl⟩
  exact ⟨⟨_, hg z⟩, rfl⟩

/-- **A morphism of ringed spaces whose image lies in an open subspace factors through it.** -/
def liftOpenSubspace (g : Z ⟶ Y) (U : TopologicalSpace.Opens Y.carrier)
    (hg : ∀ z : Z.carrier, g.hom.base z ∈ U) : Z ⟶ restrictToOpen Y U :=
  haveI : AlgebraicGeometry.SheafedSpace.IsOpenImmersion (openSubspaceInclusion Y U) :=
    AlgebraicGeometry.SheafedSpace.IsOpenImmersion.ofRestrict Y U.isOpenEmbedding
  InducedCategory.homMk (AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift
    (openSubspaceInclusion Y U).hom g.hom (range_subset_range_openSubspaceInclusion g U hg))

/-- The factorization through an open subspace followed by its inclusion is the morphism. -/
@[reassoc]
theorem liftOpenSubspace_fac (g : Z ⟶ Y) (U : TopologicalSpace.Opens Y.carrier)
    (hg : ∀ z : Z.carrier, g.hom.base z ∈ U) :
    liftOpenSubspace g U hg ≫ openSubspaceInclusion Y U = g := by
  have : AlgebraicGeometry.SheafedSpace.IsOpenImmersion (openSubspaceInclusion Y U) :=
    AlgebraicGeometry.SheafedSpace.IsOpenImmersion.ofRestrict Y U.isOpenEmbedding
  exact InducedCategory.hom_ext <| AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_fac _ _
    (range_subset_range_openSubspaceInclusion g U hg)

/-- **The factorization of a flat morphism through an open subspace is flat.** -/
theorem isFlat_liftOpenSubspace (g : Z ⟶ Y) (U : TopologicalSpace.Opens Y.carrier)
    (hg : ∀ z : Z.carrier, g.hom.base z ∈ U) (hflat : AlgebraicGeometry.IsFlat g) :
    AlgebraicGeometry.IsFlat (liftOpenSubspace g U hg) := by
  intro z
  have e : (liftOpenSubspace g U hg).hom ≫ (openSubspaceInclusion Y U).hom = g.hom :=
    congrArg (fun φ => φ.hom) (liftOpenSubspace_fac g U hg)
  have hc := AlgebraicGeometry.PresheafedSpace.stalkMap.congr_hom _ _ e z
  rw [AlgebraicGeometry.PresheafedSpace.stalkMap.comp] at hc
  have hι : IsIso ((openSubspaceInclusion Y U).hom.stalkMap
      ((liftOpenSubspace g U hg).hom.base z)) :=
    AlgebraicGeometry.PresheafedSpace.ofRestrict_stalkMap_isIso Y.toPresheafedSpace _ _
  have hE : ∀ {A B : CommRingCat.{u}} (p : A = B), (eqToHom p).hom.Flat :=
    fun p => RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (eqToHom p))
  refine @flat_of_eq_comp _ _ _ _ hι _ _ ?_ hc.symm
  exact RingHom.Flat.comp (hE _) (hflat z)

/-- A composite of flat morphisms of ringed spaces is flat. -/
@[ega "0 6.7.5"]
theorem isFlat_comp {A B C : AlgebraicGeometry.RingedSpace.{u, u}} (f : A ⟶ B) (g : B ⟶ C)
    (hf : AlgebraicGeometry.IsFlat f) (hg : AlgebraicGeometry.IsFlat g) :
    AlgebraicGeometry.IsFlat (f ≫ g) := fun x => by
  have e := AlgebraicGeometry.PresheafedSpace.stalkMap.comp f.hom g.hom x
  change ((f.hom ≫ g.hom).stalkMap x).hom.Flat
  rw [e]
  exact RingHom.Flat.comp (hg _) (hf x)

/-- The inclusion of an open subspace into a larger one. -/
def openSubspaceLE (X : AlgebraicGeometry.RingedSpace.{u, u})
    {V W : TopologicalSpace.Opens X.carrier} (hVW : V ≤ W) :
    restrictToOpen X V ⟶ restrictToOpen X W :=
  liftOpenSubspace (openSubspaceInclusion X V) W (fun z => hVW z.2)

/-- The inclusion of an open subspace into a larger one is flat. -/
theorem isFlat_openSubspaceLE (X : AlgebraicGeometry.RingedSpace.{u, u})
    {V W : TopologicalSpace.Opens X.carrier} (hVW : V ≤ W) :
    AlgebraicGeometry.IsFlat (openSubspaceLE X hVW) :=
  isFlat_liftOpenSubspace _ _ _ (isFlat_openSubspaceInclusion X V)

/-- **Derived pullback along the two sides of a commutative square.** -/
def derivedPullbackSquareIso {A B C D : AlgebraicGeometry.RingedSpace.{u, u}}
    {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C} {d : C ⟶ D} (w : a ≫ b = c ≫ d) :
    derivedPullbackFunctor b ⋙ derivedPullbackFunctor a ≅
      derivedPullbackFunctor d ⋙ derivedPullbackFunctor c :=
  Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical a b ≪≫
    eqToIso (congrArg (fun q => derivedPullbackFunctor q) w) ≪≫
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical c d).symm

end Lift

/-- For an adjunction with invertible unit the right adjoint inverts every counit morphism. -/
theorem isIso_map_counit_of_isIso_unit {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [IsIso adj.unit] (Y : D) :
    IsIso (R.map (adj.counit.app Y)) := by
  have h : adj.unit.app (R.obj Y) ≫ R.map (adj.counit.app Y) = 𝟙 _ :=
    adj.right_triangle_components Y
  have : IsIso (adj.unit.app (R.obj Y) ≫ R.map (adj.counit.app Y)) := by
    rw [h]; infer_instance
  exact IsIso.of_isIso_comp_left (adj.unit.app (R.obj Y)) _

section Triangle

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}

/-- **The global triangle of a local approximation.** Let `U` be an open of `X`, `A ∈ D(𝒪_X)`
pseudo-coherent, and `α : P ⟶ A|_U` a morphism from the class of a strictly perfect complex on
`U` which is an isomorphism on cohomology above `m` and surjective in degree `m`. Its transpose
`β : j_!P ⟶ A` under `j_! ⊣ (-)|_U` sits in a distinguished triangle `j_!P ⟶ A ⟶ Z ⟶ (j_!P)[1]`
whose third vertex restricts on `U` to a pseudo-coherent object with no cohomology above
`m - 1`. -/
theorem exists_distTriang_jShriek
    (A : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))
    (hA : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) A)
    (U : TopologicalSpace.Opens X.carrier)
    (P : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules (restrictToOpen X U)) ℤ)
    (hP : StrictlyPerfect.IsStrictlyPerfect (X := restrictToOpen X U) P)
    (α : DerivedCategory.Q.obj P ⟶ (derivedPullbackFunctor (openSubspaceInclusion X U)).obj A)
    (m : ℤ)
    (hiso : ∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor _ m).map α)) :
    ∃ (Z : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))
      (β : (ExtensionByZeroModules.jShriek U (structureSheafRing X)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj P) ⟶ A) (g : A ⟶ Z)
      (δ : Z ⟶ ((ExtensionByZeroModules.jShriek U (structureSheafRing X)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj P))⟦(1 : ℤ)⟧),
      Triangle.mk β g δ ∈ distTriang _ ∧
        ((derivedPullbackFunctor (openSubspaceInclusion X U)).obj Z).IsLE (m - 1) ∧
        AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent
          (X := restrictToOpen X U)
          ((derivedPullbackFunctor (openSubspaceInclusion X U)).obj Z) := by
  let adj : (ExtensionByZeroModules.jShriek U (structureSheafRing X)).mapDerivedCategory ⊣
      derivedPullbackFunctor (openSubspaceInclusion X U) :=
    Stacks.Cohomology.DerivedOpenImmersion.jShriekDerivedPullbackAdjunction X U
  have : IsIso adj.unit :=
    Stacks.Cohomology.DerivedOpenImmersion.isIso_jShriekDerivedPullbackAdjunction_unit X U
  let β := (adj.homEquiv _ _).symm α
  obtain ⟨Z, g, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle β
  let : (derivedPullbackFunctor (openSubspaceInclusion X U)).CommShift ℤ :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift _
  have : (derivedPullbackFunctor (openSubspaceInclusion X U)).IsTriangulated :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated _
  have hT' := (derivedPullbackFunctor (openSubspaceInclusion X U)).map_distinguished _ hT
  have hfac : adj.unit.app (DerivedCategory.Q.obj P) ≫
      (derivedPullbackFunctor (openSubspaceInclusion X U)).map β = α :=
    (adj.homEquiv_unit _ _ β).symm.trans ((adj.homEquiv _ _).apply_symm_apply α)
  have hcomp : ∀ i : ℤ, (DerivedCategory.homologyFunctor
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules (restrictToOpen X U)) i).map
      (adj.unit.app (DerivedCategory.Q.obj P)) ≫ (DerivedCategory.homologyFunctor
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules (restrictToOpen X U)) i).map
        ((derivedPullbackFunctor (openSubspaceInclusion X U)).map β) =
      (DerivedCategory.homologyFunctor
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules (restrictToOpen X U))
          i).map α :=
    fun i => (Functor.map_comp _ _ _).symm.trans (congrArg _ hfac)
  have hu : ∀ i : ℤ, IsIso ((DerivedCategory.homologyFunctor
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules (restrictToOpen X U)) i).map
        (adj.unit.app (DerivedCategory.Q.obj P))) := fun i =>
    @Functor.map_isIso _ _ _ _ _ _ _ _ (NatIso.isIso_app_of_isIso adj.unit _)
  have hiso' : ∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules (restrictToOpen X U)) i).map
      ((derivedPullbackFunctor (openSubspaceInclusion X U)).map β)) := fun i hi =>
    @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ (hu i) (hiso i hi) (hcomp i)
  have hepi' : Epi ((DerivedCategory.homologyFunctor
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules (restrictToOpen X U)) m).map
      ((derivedPullbackFunctor (openSubspaceInclusion X U)).map β)) :=
    @epi_of_epi_fac _ _ _ _ _ _ _ _ hepi (hcomp m)
  have hLE := DerivedCategory.isLE_three_of_homologyMap_mor₁ _ hT' m hiso' hepi'
  refine ⟨Z, β, g, δ, hT, hLE, ?_⟩
  have hA' : AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := X) A := hA
  exact AlgebraicGeometry.RingedSpace.isPseudoCoherent_obj₃_of_distinguished_modules _ hT'
    (AlgebraicGeometry.RingedSpace.isPseudoCoherent_of_iso_Q_obj_modules P hP _
      (@asIso _ _ _ _ (adj.unit.app (DerivedCategory.Q.obj P))
        (NatIso.isIso_app_of_isIso adj.unit _)))
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherent_derivedPullback
      (openSubspaceInclusion X U) A hA')

end Triangle

section Local

variable {X' X : AlgebraicGeometry.RingedSpace.{u, u}} (h : X' ⟶ X)

/-- The restriction of `h` to an open `V` of `X'` mapping into an open `U` of `X`. -/
def restrictLift (V : TopologicalSpace.Opens X'.carrier) (U : TopologicalSpace.Opens X.carrier)
    (hVU : V ≤ preimageOpen h U) : restrictToOpen X' V ⟶ restrictToOpen X U :=
  liftOpenSubspace (openSubspaceInclusion X' V ≫ h) U (fun z => hVU z.2)

/-- The restriction of `h` followed by the inclusion of `U` is the inclusion of `V` followed by
`h`. -/
theorem restrictLift_fac (V : TopologicalSpace.Opens X'.carrier)
    (U : TopologicalSpace.Opens X.carrier) (hVU : V ≤ preimageOpen h U) :
    openSubspaceInclusion X' V ≫ h = restrictLift h V U hVU ≫ openSubspaceInclusion X U :=
  (liftOpenSubspace_fac _ _ _).symm

/-- `Lh^*` followed by restriction to `V` is restriction to `U` followed by the restricted
derived pullback. -/
def restrictLiftIso (V : TopologicalSpace.Opens X'.carrier) (U : TopologicalSpace.Opens X.carrier)
    (hVU : V ≤ preimageOpen h U) :
    derivedPullbackFunctor h ⋙ derivedPullbackFunctor (openSubspaceInclusion X' V) ≅
      derivedPullbackFunctor (openSubspaceInclusion X U) ⋙
        derivedPullbackFunctor (restrictLift h V U hVU) :=
  derivedPullbackSquareIso (restrictLift_fac h V U hVU)

/-- Restriction to a smaller open is restriction to the larger one followed by restriction
along the inclusion. -/
def openSubspaceLEIso (V W : TopologicalSpace.Opens X'.carrier) (hVW : V ≤ W) :
    derivedPullbackFunctor (openSubspaceInclusion X' W) ⋙
        derivedPullbackFunctor (openSubspaceLE X' hVW) ≅
      derivedPullbackFunctor (openSubspaceInclusion X' V) :=
  Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical (openSubspaceLE X' hVW)
      (openSubspaceInclusion X' W) ≪≫
    eqToIso (congrArg (fun q => derivedPullbackFunctor q)
      (liftOpenSubspace_fac (openSubspaceInclusion X' V) W (fun z => hVW z.2)))

/-- A lower bound on cohomology after restriction to an open passes to every smaller open. -/
theorem isGE_derivedPullback_openSubspace_of_le (V W : TopologicalSpace.Opens X'.carrier)
    (hVW : V ≤ W)
    (G : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X'))
    (c : ℤ) (hG : ((derivedPullbackFunctor (openSubspaceInclusion X' W)).obj G).IsGE c) :
    ((derivedPullbackFunctor (openSubspaceInclusion X' V)).obj G).IsGE c := by
  have : ((derivedPullbackFunctor (openSubspaceInclusion X' W) ⋙
      derivedPullbackFunctor (openSubspaceLE X' hVW)).obj G).IsGE c :=
    isGE_derivedPullback_obj_of_isFlat _ (isFlat_openSubspaceLE X' hVW) _ c hG
  exact DerivedCategory.TStructure.t.isGE_of_iso ((openSubspaceLEIso V W hVW).app G) c

/-- A morphism whose derived pullback to an open subspace is invertible restricts to an
isomorphism on the slice over that open. -/
theorem isIso_restrictDerived_map_of_isIso (V : TopologicalSpace.Opens X'.carrier)
    {A B : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X')}
    (φ : A ⟶ B) (hφ : IsIso ((derivedPullbackFunctor (openSubspaceInclusion X' V)).map φ)) :
    IsIso ((AlgebraicGeometry.RingedSite.restrictDerived
      (Stacks.SheafOfModules.ringedSite X'.sheaf) V).map φ) := by
  refine (NatIso.isIso_map_iff (restrictDerivedIsoDerivedPullback X' V) φ).2 ?_
  exact Iso.isIso_hom ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictBackward
    X' V).mapDerivedCategory.mapIso (@asIso _ _ _ _ _ hφ))

/-- **The degree-`n` invertibility of the diagonal near a point.** Every point of `X'` has an
open neighbourhood `V` on whose slice the diagonal at the restrictions of `F`, `Lh^*N` and `Lh^*A`
is invertible on `Hⁿ`. -/
theorem exists_mem_isIso_homologyMap_restrictDerived_derivedTensorHomDiagonal
    (hh : AlgebraicGeometry.IsFlat h)
    (A : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))
    (hA : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) A)
    (N : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))
    (hN : AlgebraicGeometry.RingedSpace.IsLocallyBoundedBelow X N)
    (F : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X'))
    (hF : LocallyHasRelativeTorAmplitudeGE h F) (n : ℤ) (x' : X'.carrier) :
    ∃ V : TopologicalSpace.Opens X'.carrier, x' ∈ V ∧
      IsIso ((DerivedCategory.homologyFunctor _ n).map
        (AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal
          ((Stacks.SheafOfModules.ringedSite X'.sheaf).over V)
          ((AlgebraicGeometry.RingedSite.restrictDerived
            (Stacks.SheafOfModules.ringedSite X'.sheaf) V).obj F)
          ((AlgebraicGeometry.RingedSite.restrictDerived
            (Stacks.SheafOfModules.ringedSite X'.sheaf) V).obj ((derivedPullbackFunctor h).obj N))
          ((AlgebraicGeometry.RingedSite.restrictDerived
            (Stacks.SheafOfModules.ringedSite X'.sheaf) V).obj
              ((derivedPullbackFunctor h).obj A)))) := by
  obtain ⟨U', hxU', a, hFa⟩ := hF x'
  obtain ⟨B, hxB, b, hNb⟩ := exists_isGE_derivedPullback_openSubspace X N hN (h.hom.base x')
  obtain ⟨E, hE, ⟨eA⟩⟩ := hA
  obtain ⟨U, hxU, P₀, hP₀, α₀, hα₁, hα₂⟩ := hE (a + b - n - 1) (h.hom.base x')
  let eA' : (DerivedCategory.Q (C := AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      X)).obj E ≅ A := eA
  let α : (DerivedCategory.Q (C := AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      (restrictToOpen X U))).obj P₀ ⟶ (derivedPullbackFunctor (openSubspaceInclusion X U)).obj A :=
    DerivedCategory.Q.map α₀ ≫ (derivedPullbackOpenSubspaceQIso X U E).inv ≫
      (derivedPullbackFunctor (openSubspaceInclusion X U)).map eA'.hom
  let H := fun i : ℤ => DerivedCategory.homologyFunctor
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules (restrictToOpen X U)) i
  let eα := (derivedPullbackOpenSubspaceQIso X U E).symm ≪≫
    (derivedPullbackFunctor (openSubspaceInclusion X U)).mapIso eA'
  have hαfac : ∀ i : ℤ, (H i).map α = (H i).map (DerivedCategory.Q.map α₀) ≫ (H i).map eα.hom :=
    fun i => Functor.map_comp _ _ _
  have hiso : ∀ i : ℤ, a + b - n - 1 < i → IsIso ((H i).map α) := fun i hi => by
    rw [hαfac i]
    exact IsIso.comp_isIso'
      ((DerivedCategory.isIso_homologyFunctor_map_Q_map_iff α₀ i).2 (hα₁ i hi))
      (Iso.isIso_hom ((H i).mapIso eα))
  have hepi : Epi ((H (a + b - n - 1)).map α) := by
    rw [hαfac]
    exact epi_comp' ((DerivedCategory.epi_homologyFunctor_map_Q_map_iff α₀ _).2 hα₂)
      (IsIso.epi_of_iso _)
  obtain ⟨Z₀, β, g, δ, hT, hZle, hZpc⟩ :=
    exists_distTriang_jShriek A ⟨E, hE, ⟨eA⟩⟩ U P₀ hP₀ α (a + b - n - 1) hiso hepi
  let adjB : (ExtensionByZeroModules.jShriek B (structureSheafRing X)).mapDerivedCategory ⊣
      derivedPullbackFunctor (openSubspaceInclusion X B) :=
    Stacks.Cohomology.DerivedOpenImmersion.jShriekDerivedPullbackAdjunction X B
  have : IsIso adjB.unit :=
    Stacks.Cohomology.DerivedOpenImmersion.isIso_jShriekDerivedPullbackAdjunction_unit X B
  let N' := (ExtensionByZeroModules.jShriek B (structureSheafRing X)).mapDerivedCategory.obj
    ((derivedPullbackFunctor (openSubspaceInclusion X B)).obj N)
  have hN' : N'.IsGE b := isGE_mapDerivedCategory_obj _ _ b hNb
  let adjU : (ExtensionByZeroModules.jShriek U (structureSheafRing X)).mapDerivedCategory ⊣
      derivedPullbackFunctor (openSubspaceInclusion X U) :=
    Stacks.Cohomology.DerivedOpenImmersion.jShriekDerivedPullbackAdjunction X U
  have : IsIso adjU.unit :=
    Stacks.Cohomology.DerivedOpenImmersion.isIso_jShriekDerivedPullbackAdjunction_unit X U
  let G₀ := ((Stacks.SheafOfModules.derivedSheafHom (restrictToOpen X U).sheaf).obj
    (op ((derivedPullbackFunctor (openSubspaceInclusion X U)).obj Z₀))).obj
      ((derivedPullbackFunctor (openSubspaceInclusion X U)).obj N')
  have hG₀ : G₀.IsGE (b - (a + b - n - 1 - 1)) :=
    AlgebraicGeometry.RingedSite.isGE_derivedSheafHom
      (Stacks.SheafOfModules.ringedSite (restrictToOpen X U).sheaf) _ _ _ b hZle
      (isGE_derivedPullback_obj_of_isFlat _ (isFlat_openSubspaceInclusion X U) N' b hN')
  let N₂ := (ExtensionByZeroModules.jShriek U (structureSheafRing X)).mapDerivedCategory.obj G₀
  have hN₂ : N₂.IsGE (b - (a + b - n - 1 - 1)) := isGE_mapDerivedCategory_obj _ _ _ hG₀
  let V : TopologicalSpace.Opens X'.carrier := U' ⊓ preimageOpen h U ⊓ preimageOpen h B
  have hxV : x' ∈ V := ⟨⟨hxU', hxU⟩, hxB⟩
  have hVU : V ≤ preimageOpen h U := inf_le_left.trans inf_le_right
  have hVB : V ≤ preimageOpen h B := inf_le_right
  have hVU' : V ≤ U' := inf_le_left.trans inf_le_left
  refine ⟨V, hxV, ?_⟩
  let : (derivedPullbackFunctor h).CommShift ℤ :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift _
  have : (derivedPullbackFunctor h).IsTriangulated :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated _
  have hT' := (derivedPullbackFunctor h).map_distinguished _ hT
  let gU := restrictLift h V U hVU
  have : (RingedSpaceModuleAdjunction.modulePullback gU).Additive :=
    RingedSpaceModuleAdjunction.modulePullback_additive _
  let Ps :=
    ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictBackward X' V).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
      (((RingedSpaceModuleAdjunction.modulePullback gU).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P₀)
  have hPs : _root_.IsStrictlyPerfect ((StrictlyPerfect.structureSheafOfRings X').over V) Ps :=
    Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex
      (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictBackward X' V)
      (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictBackwardUnitIso X' V)
      ((AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_iff
        (restrictToOpen X' V) _).1
        (Stacks.StrictlyPerfect.Pullback.isStrictlyPerfect_modulePullback gU P₀ hP₀))
  have ePs : (DerivedCategory.Q (C := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          ((Stacks.SheafOfModules.ringedSite X'.sheaf).over V).O))).obj Ps ≅
      (AlgebraicGeometry.RingedSite.restrictDerived
      (Stacks.SheafOfModules.ringedSite X'.sheaf) V).obj ((derivedPullbackFunctor h).obj
        ((ExtensionByZeroModules.jShriek U (structureSheafRing X)).mapDerivedCategory.obj
          (DerivedCategory.Q.obj P₀))) := by
    let e1 : (derivedPullbackFunctor (openSubspaceInclusion X' V)).obj
        ((derivedPullbackFunctor h).obj
          ((ExtensionByZeroModules.jShriek U (structureSheafRing X)).mapDerivedCategory.obj
            (DerivedCategory.Q.obj P₀))) ≅
        DerivedCategory.Q.obj
          (((RingedSpaceModuleAdjunction.modulePullback gU).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P₀) :=
      (restrictLiftIso h V U hVU).app _ ≪≫ (derivedPullbackFunctor gU).mapIso
          (@asIso _ _ _ _ (adjU.unit.app (DerivedCategory.Q.obj P₀))
            (NatIso.isIso_app_of_isIso adjU.unit _)).symm ≪≫
        AlgebraicGeometry.DerivedFibreBetti.derivedPullbackQIsoOfKFlat gU P₀
          (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_of_isStrictlyPerfect P₀ hP₀)
    exact ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictBackward
        X' V).mapDerivedCategoryFactors.app _).symm ≪≫
      (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictBackward
        X' V).mapDerivedCategory.mapIso e1.symm ≪≫
      ((restrictDerivedIsoDerivedPullback X' V).app _).symm
  have hf : IsIso ((AlgebraicGeometry.RingedSite.restrictDerived
      (Stacks.SheafOfModules.ringedSite X'.sheaf) V).map
        ((derivedPullbackFunctor h).map (adjB.counit.app N))) := by
    refine isIso_restrictDerived_map_of_isIso V _ ?_
    exact (NatIso.isIso_map_iff (restrictLiftIso h V B hVB) _).2 <|
      Iso.isIso_hom ((derivedPullbackFunctor (restrictLift h V B hVB)).mapIso
        (@asIso _ _ _ _ _ (isIso_map_counit_of_isIso_unit adjB N)))
  have hgU : AlgebraicGeometry.IsFlat gU :=
    isFlat_liftOpenSubspace _ _ _ (isFlat_comp _ _ (isFlat_openSubspaceInclusion X' V) hh)
  let sq := restrictLiftIso h V U hVU
  have hZ : ((AlgebraicGeometry.RingedSite.restrictDerived
      (Stacks.SheafOfModules.ringedSite X'.sheaf) V).obj ((derivedPullbackFunctor h).obj Z₀)).IsLE
        (a + b - n - 1 - 1) := by
    refine isLE_restrictDerived_of_isLE X' V _ _ ?_
    have : ((derivedPullbackFunctor (openSubspaceInclusion X U) ⋙
        derivedPullbackFunctor gU).obj Z₀).IsLE (a + b - n - 1 - 1) :=
      isLE_derivedPullback_obj_of_isFlat gU hgU _ _ hZle
    exact DerivedCategory.TStructure.t.isLE_of_iso (sq.app Z₀).symm _
  have hc : ((AlgebraicGeometry.RingedSite.restrictDerived
      (Stacks.SheafOfModules.ringedSite X'.sheaf) V).obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor
          (Stacks.SheafOfModules.ringedSite X'.sheaf)).obj F).obj
            ((derivedPullbackFunctor h).obj N'))).IsGE (a + b) :=
    isGE_restrictDerived_of_isGE X' V _ _
      (isGE_derivedPullback_openSubspace_of_le V U' hVU' _ _ (hFa N' b hN'))
  have hd : ((AlgebraicGeometry.RingedSite.restrictDerived
      (Stacks.SheafOfModules.ringedSite X'.sheaf) V).obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor
          (Stacks.SheafOfModules.ringedSite X'.sheaf)).obj F).obj
            (((AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor
              (Stacks.SheafOfModules.ringedSite X'.sheaf)).obj
                (op ((derivedPullbackFunctor h).obj Z₀))).obj
                  ((derivedPullbackFunctor h).obj N')))).IsGE
          (a + (b - (a + b - n - 1 - 1))) := by
    refine isGE_restrictDerived_of_isGE X' V _ _ ?_
    let W := restrictToOpen X' V
    let RH := Stacks.SheafOfModules.derivedSheafHom W.sheaf
    have hZpc' : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent
        (X := restrictToOpen X U) ((derivedPullbackFunctor (openSubspaceInclusion X U)).obj Z₀) :=
      hZpc
    have hN'loc := AlgebraicGeometry.RingedSpace.isLocallyBoundedBelow_of_isGE_modules
      ((derivedPullbackFunctor (openSubspaceInclusion X U)).obj N') b
      (isGE_derivedPullback_obj_of_isFlat _ (isFlat_openSubspaceInclusion X U) N' b hN')
    have := isIso_derivedPullbackSheafHomMap_of_isPseudoCoherent gU hgU _ hZpc' _ hN'loc
    let φ : (derivedPullbackFunctor (openSubspaceInclusion X' V)).obj
        (((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).obj
          (op ((derivedPullbackFunctor h).obj Z₀))).obj ((derivedPullbackFunctor h).obj N')) ≅
        (derivedPullbackFunctor (openSubspaceInclusion X' V)).obj
          ((derivedPullbackFunctor h).obj N₂) :=
      @asIso _ _ _ _ (derivedPullbackSheafHomMap (openSubspaceInclusion X' V)
          ((derivedPullbackFunctor h).obj Z₀) ((derivedPullbackFunctor h).obj N'))
        (Stacks.Cohomology.DerivedOpenImmersion.isIso_derivedPullbackSheafHomMap_ofRestrict
          X' V ((derivedPullbackFunctor h).obj Z₀) ((derivedPullbackFunctor h).obj N')) ≪≫
        (RH.mapIso (sq.app Z₀).symm.op).app _ ≪≫ (RH.obj _).mapIso (sq.app N') ≪≫
        (asIso (derivedPullbackSheafHomMap gU
          ((derivedPullbackFunctor (openSubspaceInclusion X U)).obj Z₀)
          ((derivedPullbackFunctor (openSubspaceInclusion X U)).obj N'))).symm ≪≫
        (derivedPullbackFunctor gU).mapIso
          (@asIso _ _ _ _ (adjU.unit.app G₀) (NatIso.isIso_app_of_isIso adjU.unit G₀)) ≪≫
        (sq.app N₂).symm
    let e : (derivedPullbackFunctor (openSubspaceInclusion X' V)).obj
        ((internalHomTensorUncurried X').obj (F, (derivedPullbackFunctor h).obj N₂)) ≅
        (derivedPullbackFunctor (openSubspaceInclusion X' V)).obj
          ((internalHomTensorUncurried X').obj (F,
            ((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).obj
              (op ((derivedPullbackFunctor h).obj Z₀))).obj ((derivedPullbackFunctor h).obj N'))) :=
      (pullbackTensorIso (openSubspaceInclusion X' V)).app (F, (derivedPullbackFunctor h).obj N₂) ≪≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor
          (Stacks.SheafOfModules.ringedSite W.sheaf)).obj
            ((derivedPullbackFunctor (openSubspaceInclusion X' V)).obj F)).mapIso φ.symm ≪≫
        ((pullbackTensorIso (openSubspaceInclusion X' V)).app (F,
          ((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).obj
            (op ((derivedPullbackFunctor h).obj Z₀))).obj ((derivedPullbackFunctor h).obj N'))).symm
    have := isGE_derivedPullback_openSubspace_of_le V U' hVU' _ _ (hFa N₂ _ hN₂)
    exact DerivedCategory.TStructure.t.isGE_of_iso e _
  exact RingedSite.isIso_homologyMap_restrictDerived_derivedTensorHomDiagonal_of_distTriang
    (Stacks.SheafOfModules.ringedSite X'.sheaf) V F ((derivedPullbackFunctor h).obj N)
    ((derivedPullbackFunctor h).obj N') ((derivedPullbackFunctor h).map (adjB.counit.app N)) hf
    _ _ _ hT' hPs ePs (a + b - n - 1) (a + b) (a + (b - (a + b - n - 1 - 1))) n hZ hc hd
    (by omega) (by omega)


/-- **Stacks 0ATN part (3) relative to a flat morphism.** Let `h : X' ⟶ X` be a flat morphism of
ringed spaces, `A ∈ D(𝒪_X)` pseudo-coherent, `N ∈ D(𝒪_X)` locally bounded below, and
`F ∈ D(𝒪_{X'})` locally of Tor amplitude bounded below relative to `h`. Then the diagonal of
Stacks 0BYS on `X'`,

`F ⊗^L RSheafHom(Lh^*A, Lh^*N) ⟶ RSheafHom(Lh^*A, F ⊗^L Lh^*N)`,

is an isomorphism. -/
theorem isIso_derivedTensorHomDiagonal_derivedPullback_of_locallyHasRelativeTorAmplitudeGE
    (hh : AlgebraicGeometry.IsFlat h)
    (A : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))
    (hA : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) A)
    (N : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))
    (hN : AlgebraicGeometry.RingedSpace.IsLocallyBoundedBelow X N)
    (F : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X'))
    (hF : LocallyHasRelativeTorAmplitudeGE h F) :
    IsIso ((Stacks.SheafOfModules.ringedSite X'.sheaf).derivedTensorHomDiagonal F
      ((derivedPullbackFunctor h).obj N) ((derivedPullbackFunctor h).obj A)) := by
  refine (Stacks.SheafOfModules.ringedSite X'.sheaf).isIso_derivedTensorHomDiagonal_of_locally
    _ _ _ ?_
  intro n
  choose V hV hiso using
    exists_mem_isIso_homologyMap_restrictDerived_derivedTensorHomDiagonal h hh A hA N hN F hF n
  refine ⟨X'.carrier, V, ?_, hiso⟩
  rw [Opens.coversTop_iff]
  exact eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hV x⟩

end Local

end Stacks.Cohomology.DerivedInternalHomPullback

end
