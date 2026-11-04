module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectnessLocalOnSmallEtale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalModelsGeneral
public import StacksFrontier.CategoryTheory.Sites.CoversTopRefinement
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedCharacterization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.Functoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero

/-!
# Perfectness is local along a family of étale morphisms covering an algebraic space

Let `X` be an algebraic space over a scheme `S` and let `fᵢ : Yᵢ ⟶ X` be a family of étale
morphisms of algebraic spaces whose charts cover `X`, in the sense that the composites with the
`fᵢ` of the étale charts of the `Yᵢ` cover the final object of the small étale site of `X`.  If
the restriction `E|_{Yᵢ}` of an object `E` of `D(𝒪_X)` is perfect for every `i`, then `E` is
perfect.

## Main results

* `CategoryTheory.GrothendieckTopology.coversTop_sigma_subtype`: a covering family of objects
  coming from several sites through continuous functors may be refined to the images of the
  objects satisfying a property which holds locally on each of those sites.
* `AlgebraicGeometry.Space.exists_strictlyPerfect_model_postcomp`: a strictly perfect model of
  `E|_Y` over an étale chart `V` of `Y` is carried by the slice equivalence of Stacks 04M0 to a
  strictly perfect model of `E` over the composite chart of `X`.
* `AlgebraicGeometry.Space.isPerfect_of_isPerfect_etaleModulePullback`: **perfectness is local
  along a covering family of étale morphisms.**

## Implementation notes

Perfectness is read through local models in the derived category,
`AlgebraicGeometry.RingedSite.isPerfect_of_forall_coveringFamily_strictlyPerfect_general`, which
is stated with the objects and the morphisms of the site at independent universes and therefore
applies to the small étale ringed site of an algebraic space.  The local models of `E|_Y` are
transported along the slice equivalence
`AlgebraicGeometry.Space.SmallEtale.postcompOverEquivalence` of Stacks 04M0, with the identity as
structure map in both directions — the two structure sheaves agree on the nose — exactly as in
`AlgebraicGeometry.Space.hasGlobalPresentation_over_postcomp_iff`.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08G6](https://stacks.math.columbia.edu/tag/08G6)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v u' v' w

namespace CategoryTheory.GrothendieckTopology

/-- **Refining a covering family coming from several sites.**  Let `uᵢ : Cᵢ ⥤ D` be continuous
functors whose images together cover the final object of `D`, and let `pᵢ` be a property of the
objects of `Cᵢ` which holds on a covering of every object.  Then the images of the objects
satisfying the property cover the final object of `D`. -/
theorem coversTop_sigma_subtype {ι : Type w} {C : ι → Type u} [∀ i, Category.{v} (C i)]
    {D : Type u'} [Category.{v'} D] (u : ∀ i, C i ⥤ D) (J : ∀ i, GrothendieckTopology (C i))
    (K : GrothendieckTopology D) [∀ i, (u i).IsContinuous (J i) K]
    (hTop : K.CoversTop (fun x : Σ i, C i => (u x.1).obj x.2)) (p : ∀ i, C i → Prop)
    (hp : ∀ i (U : C i), ∃ S : Presieve U, Sieve.generate S ∈ J i U ∧
      ∀ ⦃V : C i⦄ (g : V ⟶ U), S g → p i V) :
    K.CoversTop (fun x : {x : Σ i, C i // p x.1 x.2} => (u x.1.1).obj x.1.2) := by
  intro U
  apply K.transitive (hTop U)
  rintro V g ⟨⟨i, W⟩, ⟨k⟩⟩
  obtain ⟨S, hS, hpS⟩ := hp i W
  apply K.superset_covering _
    (K.pullback_stable k ((CoverPreserving.of_isContinuous (u i) (J i) K).cover_preserve hS))
  rintro Z q ⟨A, a, b, ⟨A', l, a', ha', -⟩, -⟩
  exact ⟨⟨⟨i, A'⟩, hpS a' ha'⟩, ⟨b ≫ (u i).map l⟩⟩

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry.RingedSite

section ModelRestriction

variable (X : RingedSite.{u, v, w})
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{w}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [hDer : ∀ V : X.C, HasDerivedCategory.{u'} (SheafOfModules.{w}
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O).over V))]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{v'}
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O))]

attribute [local instance] ovFunctorLimits ovFunctorColimits overMapLimits overMapColimits
  locallyOverRingSheafHasDerivedCategory

/-- **A strictly perfect model in the derived category descends along an arrow of the site.**
If `P ≅ E|_U` in `D(O|_U)` for a strictly perfect complex `P`, then restricting along `k : V ⟶ U`
gives a strictly perfect complex isomorphic to `E|_V` in `D(O|_V)`. -/
theorem exists_strictlyPerfect_model_of_hom
    (E : DerivedCategory
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O)))
    {U V : X.C} (k : V ⟶ U)
    (P : CochainComplex (SheafOfModules.{w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O).over U)) ℤ)
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O).over U) P)
    (α : DerivedCategory.Q.obj P ≅
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O)
        U).mapDerivedCategory.obj E) :
    ∃ P' : CochainComplex (SheafOfModules.{w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O).over V)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O).over V) P' ∧
        Nonempty (DerivedCategory.Q.obj P' ≅
          (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O)
            V).mapDerivedCategory.obj E) := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O
  let M := SheafOfModules.overMap.{w} R k
  refine ⟨(M.mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general R k hP, ⟨?_⟩⟩
  exact (M.mapDerivedCategoryFactors.app P).symm ≪≫ M.mapDerivedCategory.mapIso α ≪≫
    ((Functor.mapDerivedCategoryComp (SheafOfModules.overFunctor.{w} R U) M).app E).symm ≪≫
      (asIso (NatTrans.mapDerivedCategory (SheafOfModules.overFunctorMap.{w} R k).hom)).app E

end ModelRestriction

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

attribute [local instance] RingedSite.ovFunctorLimits RingedSite.ovFunctorColimits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

section Transfer

variable (f : Y ⟶ X) (hf : IsEtale B S hS f.hom) (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C)

/-- The structure sheaf of the small étale site of `X` restricted to the composite chart. -/
abbrev postcompSliceRingX :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over
    ((smallEtaleRingedSitePostcomp B S hS f hf).obj V)

/-- The structure sheaf of the small étale site of `Y` restricted to the chart `V`. -/
abbrev postcompSliceRingY :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).over V

/-- The structure map of restriction along the slice comparison of Stacks 04M0: the identity. -/
abbrev postcompSliceRingMap :
    postcompSliceRingY B S hS V ⟶
    ((smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V).functor.sheafPushforwardContinuous
      RingCat.{u} ((smallEtaleRingedSite B S hS Y.1 Y.2).J.over V)
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over
        ((smallEtaleRingedSitePostcomp B S hS f hf).obj V))).obj
      (postcompSliceRingX B S hS f hf V) :=
  𝟙 _

/-- The structure map of restriction along the inverse slice comparison: the identity. -/
abbrev postcompSliceRingMapInv :
    postcompSliceRingX B S hS f hf V ⟶
    ((smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V).inverse.sheafPushforwardContinuous
      RingCat.{u} ((smallEtaleRingedSite B S hS X.1 X.2).J.over
        ((smallEtaleRingedSitePostcomp B S hS f hf).obj V))
      ((smallEtaleRingedSite B S hS Y.1 Y.2).J.over V)).obj (postcompSliceRingY B S hS V) :=
  𝟙 _

/-- The counit of the slice equivalence, whiskered into the structure sheaf of the composite
chart, is the composite of the two identity structure maps `postcompSliceRingMapInv` and
`postcompSliceRingMap`. -/
theorem postcompSliceRingMap_H₁ :
    Functor.whiskerRight
        (NatTrans.op (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V).counit)
      (postcompSliceRingX B S hS f hf V).obj =
      (postcompSliceRingMapInv B S hS f hf V).hom ≫
        (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V).inverse.op.whiskerLeft
          (postcompSliceRingMap B S hS f hf V).hom := by
  ext : 2
  exact rfl

/-- The composite of the two identity structure maps `postcompSliceRingMap` and
`postcompSliceRingMapInv` with the unit of the slice equivalence, whiskered into the structure
sheaf of the chart `V`, is the identity. -/
theorem postcompSliceRingMap_H₂ :
    (postcompSliceRingMap B S hS f hf V).hom ≫
        (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V).functor.op.whiskerLeft
          (postcompSliceRingMapInv B S hS f hf V).hom ≫
        Functor.whiskerRight
            (NatTrans.op (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V).unit)
          (postcompSliceRingY B S hS V).obj =
      𝟙 (postcompSliceRingY B S hS V).obj := by
  ext : 2
  exact rfl

/-- **The slice equivalence of Stacks 04M0 on sheaves of modules.**  Modules on the slice of the
small étale site of `X` at the composite chart `f ∘ V` are modules on the slice of the small
étale site of `Y` at `V`. -/
abbrev postcompSliceModuleEquivalence :
    SheafOfModules.{u} (postcompSliceRingX B S hS f hf V) ≌
      SheafOfModules.{u} (postcompSliceRingY B S hS V) :=
  SheafOfModules.pushforwardPushforwardEquivalence.{u}
    (smallEtaleRingedSitePostcompOverEquivalence B S hS f hf V)
    (postcompSliceRingMap B S hS f hf V) (postcompSliceRingMapInv B S hS f hf V)
    (postcompSliceRingMap_H₁ B S hS f hf V) (postcompSliceRingMap_H₂ B S hS f hf V)

/-- **Restricting an étale pullback to a chart is restricting the module to the composite chart,
read through the slice equivalence.**  Both have the same sections over every object. -/
def overEtaleModulePullbackIso :
    SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
        ((smallEtaleRingedSitePostcomp B S hS f hf).obj V) ⋙
      (postcompSliceModuleEquivalence B S hS f hf V).functor ≅
    etaleModulePullback B S hS f hf ⋙
      SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) V :=
  NatIso.ofComponents
    (fun M => (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intro A A' a; ext; rfl)))
    (by intro M N g; ext : 3; rfl)

/-- The inverse slice equivalence carries the structure sheaf to the structure sheaf: both have
the same sections over every object. -/
def postcompSliceUnitIso :
    (postcompSliceModuleEquivalence B S hS f hf V).inverse.obj
        (SheafOfModules.unit (postcompSliceRingY B S hS V)) ≅
      SheafOfModules.unit (postcompSliceRingX B S hS f hf V) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intro A A' a; ext; rfl))

/-- The inverse of the slice equivalence on sheaves of modules is additive. -/
instance postcompSliceModuleEquivalence_inverse_additive :
    (postcompSliceModuleEquivalence B S hS f hf V).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The slice equivalence on sheaves of modules is additive. -/
instance postcompSliceModuleEquivalence_functor_additive :
    (postcompSliceModuleEquivalence B S hS f hf V).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **A strictly perfect model of `E|_Y` over a chart `V` of `Y` gives one of `E` over the
composite chart of `X`.**  The model is carried across by the slice equivalence of Stacks 04M0,
which is exact and matches up the two structure sheaves, and the restriction of `E|_Y` to `V`
is carried to the restriction of `E` to the composite chart by
`AlgebraicGeometry.Space.overEtaleModulePullbackIso`. -/
theorem exists_strictlyPerfect_model_postcomp
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (P : CochainComplex (SheafOfModules.{u} (postcompSliceRingY B S hS V)) ℤ)
    (hP : IsStrictlyPerfect (postcompSliceRingY B S hS V) P)
    (α : DerivedCategory.Q.obj P ≅
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
          V).mapDerivedCategory.obj
        ((etaleModulePullback B S hS f hf).mapDerivedCategory.obj E)) :
    ∃ P' : CochainComplex (SheafOfModules.{u} (postcompSliceRingX B S hS f hf V)) ℤ,
      IsStrictlyPerfect (postcompSliceRingX B S hS f hf V) P' ∧
        Nonempty (DerivedCategory.Q.obj P' ≅
          (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
              ((smallEtaleRingedSitePostcomp B S hS f hf).obj V)).mapDerivedCategory.obj E) := by
  let e := postcompSliceModuleEquivalence B S hS f hf V
  let G := e.inverse
  let oY := SheafOfModules.overFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) V
  let oX := SheafOfModules.overFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
      ((smallEtaleRingedSitePostcomp B S hS f hf).obj V)
  let pull := etaleModulePullback B S hS f hf
  -- the module-level identification `oX ≅ pull ⋙ oY ⋙ G`
  let κ : oX ≅ (pull ⋙ oY) ⋙ G :=
    Functor.isoWhiskerLeft oX e.unitIso ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (overEtaleModulePullbackIso B S hS f hf V) G
  refine ⟨(G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    SheafOfModules.isStrictlyPerfect_map G (postcompSliceUnitIso B S hS f hf V) hP, ⟨?_⟩⟩
  exact (G.mapDerivedCategoryFactors.app P).symm ≪≫
    G.mapDerivedCategory.mapIso (α ≪≫ ((Functor.mapDerivedCategoryComp pull oY).app E).symm) ≪≫
      ((Functor.mapDerivedCategoryComp (pull ⋙ oY) G).app E).symm ≪≫
        (asIso (NatTrans.mapDerivedCategory κ.inv)).app E

end Transfer

section Restriction

variable (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)

/-- The slice equivalence of Stacks 04M0 carries the structure sheaf to the structure sheaf: both
have the same sections over every object. -/
def postcompSliceUnitIsoFunctor (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C) :
    (postcompSliceModuleEquivalence B S hS f hf V).functor.obj
        (SheafOfModules.unit (postcompSliceRingX B S hS f hf V)) ≅
      SheafOfModules.unit (postcompSliceRingY B S hS V) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intro A A' a; ext; rfl))

/-- **A strictly perfect model of `E` over the composite chart of `X` gives one of `E|_Y` over the
chart `V` of `Y`**, carried across by the slice equivalence of Stacks 04M0. -/
theorem exists_strictlyPerfect_model_of_postcomp
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C)
    (P : CochainComplex (SheafOfModules.{u} (postcompSliceRingX B S hS f hf V)) ℤ)
    (hP : IsStrictlyPerfect (postcompSliceRingX B S hS f hf V) P)
    (α : DerivedCategory.Q.obj P ≅
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
          ((smallEtaleRingedSitePostcomp B S hS f hf).obj V)).mapDerivedCategory.obj E) :
    ∃ P' : CochainComplex (SheafOfModules.{u} (postcompSliceRingY B S hS V)) ℤ,
      IsStrictlyPerfect (postcompSliceRingY B S hS V) P' ∧
        Nonempty (DerivedCategory.Q.obj P' ≅
          (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
              V).mapDerivedCategory.obj
            ((etaleModulePullback B S hS f hf).mapDerivedCategory.obj E)) := by
  let F := (postcompSliceModuleEquivalence B S hS f hf V).functor
  let oY := SheafOfModules.overFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) V
  let oX := SheafOfModules.overFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
      ((smallEtaleRingedSitePostcomp B S hS f hf).obj V)
  let pull := etaleModulePullback B S hS f hf
  refine ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    SheafOfModules.isStrictlyPerfect_map F (postcompSliceUnitIsoFunctor B S hS f hf V) hP, ⟨?_⟩⟩
  exact (F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso α ≪≫
    ((Functor.mapDerivedCategoryComp oX F).app E).symm ≪≫
      (asIso (NatTrans.mapDerivedCategory (overEtaleModulePullbackIso B S hS f hf V).hom)).app E ≪≫
        (Functor.mapDerivedCategoryComp pull oY).app E

attribute [local instance] smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective RingedSite.overMapLimits RingedSite.overMapColimits

/-- A quasi-isomorphism `P ⟶ F K` and an isomorphism `K ≅ E` in the derived category give an
isomorphism `P ≅ F E` in the derived category. -/
private def isoOfQuasiIsoMapDerivedCategory {C₁ : Type*} [Category C₁] [Abelian C₁]
    [HasDerivedCategory C₁] {C₂ : Type*} [Category C₂] [Abelian C₂] [HasDerivedCategory C₂]
    (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K : CochainComplex C₁ ℤ} {P : CochainComplex C₂ ℤ}
    (q : P ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) [QuasiIso q]
    {E : DerivedCategory C₁} (eK : DerivedCategory.Q.obj K ≅ E) :
    DerivedCategory.Q.obj P ≅ F.mapDerivedCategory.obj E :=
  asIso (DerivedCategory.Q.map q) ≪≫ (F.mapDerivedCategoryFactors.app K).symm ≪≫
    F.mapDerivedCategory.mapIso eK

/-- A cover of the composite chart of `X` pulls back to a cover of the chart of `Y`. -/
private theorem generate_functorPullback_postcomp_mem
    (W : (smallEtaleRingedSite B S hS Y.1 Y.2).C)
    (T : Presieve ((smallEtaleRingedSitePostcomp B S hS f hf).obj W))
    (hT : Sieve.generate T ∈ (smallEtaleRingedSite B S hS X.1 X.2).J
      ((smallEtaleRingedSitePostcomp B S hS f hf).obj W)) :
    Sieve.generate
      ((Sieve.generate T).functorPullback (smallEtaleRingedSitePostcomp B S hS f hf)).arrows ∈
        (smallEtaleRingedSite B S hS Y.1 Y.2).J W := by
  rw [Sieve.generate_sieve]
  exact SmallEtale.smallEtalePostcomp_cover_lift B S hS f hf W _ hT

/-- **Perfectness is preserved by restriction along an étale morphism.**  A covering of the
composite chart of `X` carrying strictly perfect models lifts to a covering of the chart of `Y`
(`AlgebraicGeometry.Space.SmallEtale.smallEtalePostcomp_cover_lift`); the models descend along
the arrows of the lifted covering and are carried across by the slice equivalence of
Stacks 04M0. -/
theorem isPerfect_etaleModulePullback_standard
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect
      ((etaleModulePullback B S hS f hf).mapDerivedCategory.obj E) := by
  refine RingedSite.isPerfect_of_forall_coveringFamily_strictlyPerfect_general _ _ (fun W => ?_)
  obtain ⟨K, hK, ⟨eK⟩⟩ := hE
  obtain ⟨T, hT, hmod⟩ := hK ((smallEtaleRingedSitePostcomp B S hS f hf).obj W)
  refine ⟨_, generate_functorPullback_postcomp_mem B S hS f hf W T hT, ?_⟩
  · rintro V g ⟨Z, h, s, hs, -⟩
    obtain ⟨P, hP, q, hq⟩ := hmod s hs
    obtain ⟨P₁, hP₁, ⟨α₁⟩⟩ := RingedSite.exists_strictlyPerfect_model_of_hom _ E h P hP
      (isoOfQuasiIsoMapDerivedCategory _ q eK)
    exact exists_strictlyPerfect_model_of_postcomp B S hS f hf E V P₁ hP₁ α₁

/-- **`m`-pseudo-coherence is preserved by restriction along an étale morphism.**  As for
perfectness: the local approximations over a covering of the composite chart of `X` descend
along the arrows of the lifted covering of the chart of `Y` and are carried across by the slice
equivalence of Stacks 04M0, which is exact. -/
theorem isPseudoCoherentFrom_etaleModulePullback
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (m : ℤ)
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E m) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherentFrom
      ((etaleModulePullback B S hS f hf).mapDerivedCategory.obj E) m := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := hE
  let pull := etaleModulePullback B S hS f hf
  refine ⟨(pull.mapHomologicalComplex (ComplexShape.up ℤ)).obj K, fun W => ?_,
    ⟨(pull.mapDerivedCategoryFactors.app K).symm ≪≫ pull.mapDerivedCategory.mapIso eK⟩⟩
  obtain ⟨T, hT, hmod⟩ := hK ((smallEtaleRingedSitePostcomp B S hS f hf).obj W)
  refine ⟨_, generate_functorPullback_postcomp_mem B S hS f hf W T hT, ?_⟩
  · rintro V g ⟨Z, h, s, hs, -⟩
    obtain ⟨P, hP, α, hiso, hepi⟩ := hmod s hs
    let R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O
    let M := SheafOfModules.overMap.{u} R h
    let F := (postcompSliceModuleEquivalence B S hS f hf V).functor
    let c₁ : (M.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((smallEtaleRingedSite B S hS X.1 X.2).restrictComplex K Z) ≅
        (smallEtaleRingedSite B S hS X.1 X.2).restrictComplex K
          ((smallEtaleRingedSitePostcomp B S hS f hf).obj V) :=
      (Stacks.SheafOfModules.overFunctorMapComplexIso.{u} R h).app K
    let c₂ : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((smallEtaleRingedSite B S hS X.1 X.2).restrictComplex K
            ((smallEtaleRingedSitePostcomp B S hS f hf).obj V)) ≅
        (smallEtaleRingedSite B S hS Y.1 Y.2).restrictComplex
          ((pull.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) V :=
      (Functor.mapHomologicalComplexCompIso (overEtaleModulePullbackIso B S hS f hf V)
          (ComplexShape.up ℤ)).app K ≪≫
        ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).app K).symm
    let β : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((M.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
        (smallEtaleRingedSite B S hS Y.1 Y.2).restrictComplex
          ((pull.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) V :=
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((M.mapHomologicalComplex (ComplexShape.up ℤ)).map α ≫ c₁.hom) ≫ c₂.hom
    refine ⟨_, SheafOfModules.isStrictlyPerfect_map F (postcompSliceUnitIsoFunctor B S hS f hf V)
      (Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general R h hP), β, ?_, ?_⟩
    · intro j hj
      refine RingedSite.isIso_homologyMap_comp_iso _ c₂ j
        (Stacks.PseudoCoherence.DerivedCharacterization.isIso_homologyMap_mapHomologicalComplex
          F _ j ?_)
      exact RingedSite.isIso_homologyMap_comp_iso _ c₁ j
        (Stacks.PseudoCoherence.DerivedCharacterization.isIso_homologyMap_mapHomologicalComplex
          M α j (hiso j hj))
    · refine RingedSite.epi_homologyMap_comp_iso _ c₂ m
        (Stacks.PseudoCoherence.DerivedCharacterization.epi_homologyMap_mapHomologicalComplex
          F _ m ?_)
      exact RingedSite.epi_homologyMap_comp_iso _ c₁ m
        (Stacks.PseudoCoherence.DerivedCharacterization.epi_homologyMap_mapHomologicalComplex
          M α m hepi)

end Restriction

section Descent

attribute [local instance] smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

/-- **Perfectness is local along a family of étale morphisms whose charts cover the space.**  Let
`fᵢ : Yᵢ ⟶ X` be étale morphisms of algebraic spaces such that the composites with the `fᵢ` of
the étale charts of the `Yᵢ` cover the final object of the small étale site of `X`.  An object
`E` of `D(𝒪_X)` all of whose restrictions `E|_{Yᵢ}` are perfect is perfect.

Each `E|_{Yᵢ}` has strictly perfect local models on a covering of every chart of `Yᵢ`; the images
of the charts carrying a model still cover `X`
(`CategoryTheory.GrothendieckTopology.coversTop_sigma_subtype`), and over each of them the
model is carried to `X` by `AlgebraicGeometry.Space.exists_strictlyPerfect_model_postcomp`.  So
`E` has strictly perfect local models on a covering of every chart of `X`, and is perfect by
Stacks 08G6, part (1). -/
theorem isPerfect_of_forall_isPerfect_etaleModulePullback {ι : Type*}
    (Y : ι → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)
    (hcov : (smallEtaleRingedSite B S hS X.1 X.2).J.CoversTop
      (fun x : Σ i, (smallEtaleRingedSite B S hS (Y i).1 (Y i).2).C =>
        (smallEtaleRingedSitePostcomp B S hS (f x.1) (hf x.1)).obj x.2))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : ∀ i, (smallEtaleRingedSite B S hS (Y i).1 (Y i).2).IsPerfect
      ((etaleModulePullback B S hS (f i) (hf i)).mapDerivedCategory.obj E)) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E := by
  classical
  let p : ∀ i, (smallEtaleRingedSite B S hS (Y i).1 (Y i).2).C → Prop := fun i W =>
    ∃ P : CochainComplex (SheafOfModules.{u} (postcompSliceRingY B S hS W)) ℤ,
      IsStrictlyPerfect (postcompSliceRingY B S hS W) P ∧
        Nonempty (DerivedCategory.Q.obj P ≅
          (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS (Y i).1 (Y i).2).O) W).mapDerivedCategory.obj
            ((etaleModulePullback B S hS (f i) (hf i)).mapDerivedCategory.obj E))
  have hp : ∀ i (U : (smallEtaleRingedSite B S hS (Y i).1 (Y i).2).C),
      ∃ T : Presieve U, Sieve.generate T ∈ (smallEtaleRingedSite B S hS (Y i).1 (Y i).2).J U ∧
        ∀ ⦃V⦄ (g : V ⟶ U), T g → p i V := by
    intro i U
    obtain ⟨K, hK, ⟨eK⟩⟩ := hE i
    obtain ⟨T, hT, hmod⟩ := hK U
    refine ⟨T, hT, fun V g hg => ?_⟩
    obtain ⟨P, hP, q, hq⟩ := hmod g hg
    exact ⟨P, hP, ⟨isoOfQuasiIsoMapDerivedCategory _ q eK⟩⟩
  have : ∀ i, (smallEtaleRingedSitePostcomp B S hS (f i) (hf i)).IsContinuous
      (smallEtaleRingedSite B S hS (Y i).1 (Y i).2).J (smallEtaleRingedSite B S hS X.1 X.2).J :=
    fun i => smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS (f i) (hf i)
  refine RingedSite.isPerfect_of_forall_coveringFamily_strictlyPerfect_general _ E
    (fun U => ⟨(Sieve.ofObjects
      (fun x : {x : Σ i, (smallEtaleRingedSite B S hS (Y i).1 (Y i).2).C // p x.1 x.2} =>
        (smallEtaleRingedSitePostcomp B S hS (f x.1.1) (hf x.1.1)).obj x.1.2) U).arrows, ?_, ?_⟩)
  · rw [Sieve.generate_sieve]
    exact GrothendieckTopology.coversTop_sigma_subtype
      (fun i => smallEtaleRingedSitePostcomp B S hS (f i) (hf i))
      (fun i => (smallEtaleRingedSite B S hS (Y i).1 (Y i).2).J)
      (smallEtaleRingedSite B S hS X.1 X.2).J hcov p hp U
  · rintro V g ⟨⟨⟨i, W⟩, P, hP, ⟨α⟩⟩, ⟨k⟩⟩
    obtain ⟨P', hP', ⟨α'⟩⟩ := exists_strictlyPerfect_model_postcomp B S hS (f i) (hf i) W E P hP α
    exact RingedSite.exists_strictlyPerfect_model_of_hom _ E k P' hP' α'

end Descent

end AlgebraicGeometry.Space

end
