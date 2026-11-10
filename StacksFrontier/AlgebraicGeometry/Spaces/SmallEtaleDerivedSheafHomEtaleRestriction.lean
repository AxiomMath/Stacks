module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceEquivalenceOfIso
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectHomDescentLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelLinear
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomPostSlice

/-!
# Étale restriction commutes with the derived internal Hom on algebraic spaces

Let `u : U ⟶ X` be an étale morphism of algebraic spaces, not necessarily a scheme chart. For `K`,
`E` in `D(𝒪_X)`,

`Lu^* R𝓗om(K, E) ≅ R𝓗om(Lu^*K, Lu^*E)`.

The derived internal Hom of an algebraic space is that of the equi-universe model of its small
étale ringed site, read through the derived equivalence with the model
(`AlgebraicGeometry.Space.smallEtaleDerivedSheafHom`). On the models, `Lu^*` is the restriction
along the functor `Φ_u : model(U) ⥤ model(X)` obtained from postcomposition with `u` by the two
model equivalences, and every slice functor of `Φ_u` is an equivalence: on the small étale sites
this is Stacks 04M0 (`AlgebraicGeometry.Space.SmallEtale.postcompOverEquivalence`), and the model
equivalences induce equivalences of slices. So the transport of the derived internal Hom along a
functor which is an equivalence on every slice,
`AlgebraicGeometry.RingedSite.postSliceDerivedSheafHomNatIso`, applies; the transport of a
K-injective complex stays K-injective because `u^*` has the exact left adjoint `u_!`.

## Main definitions

* `AlgebraicGeometry.Space.etaleModelFunctor`: the functor `Φ_u` between the models.
* `AlgebraicGeometry.Space.etaleModelRingMap`: its structure map, the composite of the structure
  maps of the three functors it is built from.
* `AlgebraicGeometry.Space.etaleModelRestrictionIso`: on modules, restriction along `Φ_u` is `u^*`
  read on the models.
* `AlgebraicGeometry.Space.smallEtaleDerivedSheafHomEtaleRestrictionIso`: **the comparison**
  `Lu^* R𝓗om(K, E) ≅ R𝓗om(Lu^*K, Lu^*E)`.

## References

* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U X : AlgebraicSpaces B S hS} (f : U ⟶ X) (hf : IsEtale B S hS f.hom)

/-! ### The functor between the models -/

/-- Postcomposition with an étale morphism followed by the inverse model equivalence of the
target: `Et(U) ⥤ Et(X) ⥤ model(X)`. -/
abbrev etalePostcompModelFunctor :
    (smallEtaleRingedSite B S hS U.1 U.2).C ⥤ (smallEtaleModelRingedSite B S hS X.1 X.2).C :=
  smallEtalePostcomp B S hS f hf ⋙ (smallEtaleModelEquivalence B S hS X.1).inverse

/-- **Postcomposition with an étale morphism, read on the equi-universe models**:
`model(U) ⥤ Et(U) ⥤ Et(X) ⥤ model(X)`. -/
abbrev etaleModelFunctor :
    (smallEtaleModelRingedSite B S hS U.1 U.2).C ⥤ (smallEtaleModelRingedSite B S hS X.1 X.2).C :=
  (smallEtaleModelEquivalence B S hS U.1).functor ⋙ etalePostcompModelFunctor B S hS f hf

/-- Postcomposition with an étale morphism followed by the inverse model equivalence of the
target is continuous. -/
instance etalePostcompModelFunctor_isContinuous :
    (etalePostcompModelFunctor B S hS f hf).IsContinuous
      (smallEtaleRingedSite B S hS U.1 U.2).J (smallEtaleModelRingedSite B S hS X.1 X.2).J :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ (smallEtaleRingedSite B S hS X.1 X.2).J _
    (smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS f hf)
    (smallEtaleModelRingedSite_inverse_isContinuous B S hS X.1 X.2)

/-- `Φ_u` is continuous. -/
instance etaleModelFunctor_isContinuous :
    (etaleModelFunctor B S hS f hf).IsContinuous
      (smallEtaleModelRingedSite B S hS U.1 U.2).J (smallEtaleModelRingedSite B S hS X.1 X.2).J :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ (smallEtaleRingedSite B S hS U.1 U.2).J _
    (smallEtaleModelRingedSite_functor_isContinuous B S hS U.1 U.2)
    (etalePostcompModelFunctor_isContinuous B S hS f hf)

/-- The structure map of the composite of postcomposition with `u` and the inverse model
equivalence of `X`: the structure map of postcomposition is the identity, and that of the inverse
model equivalence is the counit of the model equivalence. -/
abbrev etalePostcompModelRingMap :
    Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS U.1 U.2).O ⟶
      ((etalePostcompModelFunctor B S hS f hf).sheafPushforwardContinuous RingCat.{u}
          (smallEtaleRingedSite B S hS U.1 U.2).J
          (smallEtaleModelRingedSite B S hS X.1 X.2).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O) :=
  𝟙 _ ≫ ((smallEtalePostcomp B S hS f hf).sheafPushforwardContinuous RingCat.{u}
      (smallEtaleRingedSite B S hS U.1 U.2).J (smallEtaleRingedSite B S hS X.1 X.2).J).map
    (@Stacks.SheafOfModules.reindexBackSharp _ _ _ _ (smallEtaleRingedSite B S hS X.1 X.2).J
      (smallEtaleModelRingedSite B S hS X.1 X.2).J (smallEtaleModelEquivalence B S hS X.1)
      (smallEtaleModelRingedSite_functor_isContinuous B S hS X.1 X.2)
      (smallEtaleModelRingedSite_inverse_isContinuous B S hS X.1 X.2)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))

/-- **The structure map of `Φ_u`**: the composite of the structure maps of the model
equivalence of `U` (the identity), of postcomposition with `u` (the identity) and of the inverse
model equivalence of `X` (the counit). -/
abbrev etaleModelRingMap :
    Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS U.1 U.2).O ⟶
      ((etaleModelFunctor B S hS f hf).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleModelRingedSite B S hS U.1 U.2).J
        (smallEtaleModelRingedSite B S hS X.1 X.2).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O) :=
  𝟙 _ ≫ ((smallEtaleModelEquivalence B S hS U.1).functor.sheafPushforwardContinuous RingCat.{u}
      (smallEtaleModelRingedSite B S hS U.1 U.2).J (smallEtaleRingedSite B S hS U.1 U.2).J).map
    (etalePostcompModelRingMap B S hS f hf)

/-! ### Restriction along `Φ_u` is `u^*` read on the models -/

/-- Restriction of modules along `Φ_u`. -/
abbrev etaleModelRestriction :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleModelRingedSite B S hS X.1 X.2).O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleModelRingedSite B S hS U.1 U.2).O) :=
  SheafOfModules.pushforward.{u} (etaleModelRingMap B S hS f hf)

/-- Restriction of modules along postcomposition with `u` followed by the inverse model
equivalence of `X`. -/
abbrev etalePostcompModelRestriction :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleModelRingedSite B S hS X.1 X.2).O) ⥤
      Modules.{u, u} B S hS U.1 U.2 :=
  SheafOfModules.pushforward.{u} (etalePostcompModelRingMap B S hS f hf)

/-- Back from the model of `X` and restriction along `u` is restriction along the composite. -/
def etalePostcompModelRestrictionIso :
    (modulesEquivModelModules B S hS X.1 X.2).inverse ⋙ etaleModulePullback.{u, u} B S hS f hf ≅
      etalePostcompModelRestriction B S hS f hf := by
  refine Iso.trans ?_ ((@SheafOfModules.pushforwardComp _ _ _ _ _ _ _ _ _ _ _
    (smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS f hf)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS U.1 U.2).O)) _ _ _
    (smallEtaleModelRingedSite_inverse_isContinuous B S hS X.1 X.2)
    (@Stacks.SheafOfModules.reindexBackSharp _ _ _ _ (smallEtaleRingedSite B S hS X.1 X.2).J
      (smallEtaleModelRingedSite B S hS X.1 X.2).J (smallEtaleModelEquivalence B S hS X.1)
      (smallEtaleModelRingedSite_functor_isContinuous B S hS X.1 X.2)
      (smallEtaleModelRingedSite_inverse_isContinuous B S hS X.1 X.2)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) ≪≫ ?_)
  · exact Iso.refl _
  · exact Iso.refl _

/-- **On modules, restriction along `Φ_u` is `u^*` read on the models**: back from the model of
`X`, restrict along `u`, forward to the model of `U`. -/
def etaleModelRestrictionIso :
    (modulesEquivModelModules B S hS X.1 X.2).inverse ⋙ etaleModulePullback.{u, u} B S hS f hf ⋙
        (modulesEquivModelModules B S hS U.1 U.2).functor ≅
      etaleModelRestriction B S hS f hf := by
  refine (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (etalePostcompModelRestrictionIso B S hS f hf) _ ≪≫ ?_
  refine Iso.trans ?_ ((@SheafOfModules.pushforwardComp _ _ _ _ _ _ _ _ _ _ _
      (smallEtaleModelRingedSite_functor_isContinuous B S hS U.1 U.2)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS U.1 U.2).O))
      _ _ _ (etalePostcompModelFunctor_isContinuous B S hS f hf)
      (etalePostcompModelRingMap B S hS f hf)) ≪≫ ?_)
  · exact Iso.refl _
  · exact Iso.refl _

/-- Restriction along `Φ_u` preserves finite limits. -/
instance etaleModelRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (etaleModelRestriction B S hS f hf) :=
  haveI := preservesFiniteLimits_etaleModulePullback B S hS f hf
  preservesFiniteLimits_of_natIso (etaleModelRestrictionIso B S hS f hf)

/-- Restriction along `Φ_u` preserves finite colimits. -/
instance etaleModelRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (etaleModelRestriction B S hS f hf) :=
  haveI := preservesFiniteColimits_etaleModulePullback B S hS f hf
  preservesFiniteColimits_of_natIso (etaleModelRestrictionIso B S hS f hf)

/-- Restriction along `Φ_u` is additive. -/
instance etaleModelRestriction_additive :
    (SheafOfModules.pushforward.{u} (etaleModelRingMap B S hS f hf)).Additive where
  map_add := by intros; rfl

/-- Extension by zero along `u`, read on the models: the left adjoint of restriction along
`Φ_u`. -/
abbrev etaleModelExtension :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleModelRingedSite B S hS U.1 U.2).O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleModelRingedSite B S hS X.1 X.2).O) :=
  (modulesEquivModelModules B S hS U.1 U.2).inverse ⋙ etaleModuleLowerShriek B S hS f hf ⋙
    (modulesEquivModelModules B S hS X.1 X.2).functor

/-- Extension by zero along `u`, read on the models, is left adjoint to restriction along
`Φ_u`. -/
def etaleModelExtensionAdjunction :
    etaleModelExtension B S hS f hf ⊣
      SheafOfModules.pushforward.{u} (etaleModelRingMap B S hS f hf) :=
  ((((modulesEquivModelModules B S hS U.1 U.2).symm.toAdjunction).comp
      (etaleModuleLowerShriekAdjunction B S hS f hf)).comp
    (modulesEquivModelModules B S hS X.1 X.2).toAdjunction).ofNatIsoRight
    (etaleModelRestrictionIso B S hS f hf)

/-- Extension by zero along `u`, read on the models, preserves finite limits. -/
instance etaleModelExtension_preservesFiniteLimits :
    PreservesFiniteLimits (etaleModelExtension B S hS f hf) :=
  haveI := preservesFiniteLimits_etaleModuleLowerShriek B S hS f hf
  inferInstanceAs (PreservesFiniteLimits ((modulesEquivModelModules B S hS U.1 U.2).inverse ⋙
    etaleModuleLowerShriek B S hS f hf ⋙ (modulesEquivModelModules B S hS X.1 X.2).functor))

/-- Extension by zero along `u`, read on the models, preserves finite colimits. -/
instance etaleModelExtension_preservesFiniteColimits :
    PreservesFiniteColimits (etaleModelExtension B S hS f hf) :=
  haveI := preservesFiniteColimits_etaleModuleLowerShriek B S hS f hf
  inferInstanceAs (PreservesFiniteColimits ((modulesEquivModelModules B S hS U.1 U.2).inverse ⋙
    etaleModuleLowerShriek B S hS f hf ⋙ (modulesEquivModelModules B S hS X.1 X.2).functor))

/-- Extension by zero along `u`, read on the models, is additive. -/
instance etaleModelExtension_additive : (etaleModelExtension B S hS f hf).Additive :=
  (etaleModelExtensionAdjunction B S hS f hf).left_adjoint_additive

/-- **Restriction along `Φ_u` preserves K-injective complexes** (Stacks 08BJ): it has the exact
left adjoint `u_!`. -/
theorem etaleModelRestriction_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleModelRingedSite B S hS X.1 X.2).O)) ℤ) (hI : I.IsKInjective) :
    ((RingedSite.postSlicePushComplex (etaleModelFunctor B S hS f hf)
      (etaleModelRingMap B S hS f hf)).obj I).IsKInjective :=
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact
    (SheafOfModules.pushforward.{u} (etaleModelRingMap B S hS f hf))
    (etaleModelExtension B S hS f hf) (etaleModelExtensionAdjunction B S hS f hf) I

/-! ### `Φ_u` is an equivalence on every slice -/

/-- Sheaves of modules on the slice of the model of `U` at `W` and on the slice of the small étale
site of `U` at the underlying chart agree. -/
abbrev etaleModelSliceEquivSource (W : SmallEtaleModel B S hS U.1) :=
  @Stacks.SheafOfModules.reindexEquivalence.{u, u, _, _, _, _} _ _ _ _
    ((SmallEtale.topology B S hS U.1).over ((smallEtaleModelEquivalence B S hS U.1).functor.obj W))
    ((smallEtaleModelTopology B S hS U.1).over W)
    (Over.postEquiv W (smallEtaleModelEquivalence B S hS U.1)) _ _
    ((ringedToposStructureRingSheaf B S hS U).over
      ((smallEtaleModelEquivalence B S hS U.1).functor.obj W))

/-- Sheaves of modules on the slice of the small étale site of `U` at a chart `V` and on the slice
of the small étale site of `X` at the composite chart agree (Stacks 04M0). -/
abbrev etaleModelSliceEquivMiddle (V : SmallEtale B S hS U.1) :=
  @Stacks.SheafOfModules.reindexEquivalence.{u, u, _, _, _, _} _ _ _ _
    ((SmallEtale.topology B S hS X.1).over ((smallEtalePostcomp B S hS f hf).obj V))
    ((SmallEtale.topology B S hS U.1).over V)
    (SmallEtale.postcompOverEquivalence B S hS f hf V) _ _
    ((ringedToposStructureRingSheaf B S hS X).over ((smallEtalePostcomp B S hS f hf).obj V))

/-- Sheaves of modules on the slice of the model of `X` at the model object of a chart `V'` and
on the slice of the small étale site of `X` at `V'` agree. -/
abbrev etaleModelSliceEquivTarget (V' : SmallEtale B S hS X.1) :=
  haveI : (smallEtaleModelEquivalence B S hS X.1).symm.functor.IsContinuous
      (SmallEtale.topology B S hS X.1) (smallEtaleModelTopology B S hS X.1) :=
    inferInstanceAs ((smallEtaleModelEquivalence B S hS X.1).inverse.IsContinuous _ _)
  haveI : (smallEtaleModelEquivalence B S hS X.1).symm.inverse.IsContinuous
      (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1) :=
    inferInstanceAs ((smallEtaleModelEquivalence B S hS X.1).functor.IsContinuous _ _)
  Stacks.SheafOfModules.InternalHom.siteEquivModulesOverOfIso.{_, _, _, _, u, u}
    (J := SmallEtale.topology B S hS X.1) (K := smallEtaleModelTopology B S hS X.1)
    (smallEtaleModelEquivalence B S hS X.1).symm
    (Stacks.SheafOfModules.reindexBackSharp (J' := smallEtaleModelTopology B S hS X.1)
      (smallEtaleModelEquivalence B S hS X.1) (ringedToposStructureRingSheaf B S hS X)) V'


/-- **`Φ_u` is an equivalence on the slice at `W`**: the composite of the slice equivalences of
the model equivalence of `U`, of postcomposition with `u` (Stacks 04M0) and of the inverse model
equivalence of `X`, with its functor written as the slice functor of `Φ_u`. -/
def etaleModelSliceSiteEquiv (W : SmallEtaleModel B S hS U.1) :
    CategoryTheory.Over W ≌ CategoryTheory.Over (((smallEtaleModelEquivalence B S hS U.1).functor ⋙
      (smallEtalePostcomp B S hS f hf ⋙ (smallEtaleModelEquivalence B S hS X.1).inverse)).obj W) :=
  ((Over.postEquiv W (smallEtaleModelEquivalence B S hS U.1)).trans
    ((SmallEtale.postcompOverEquivalence B S hS f hf
      ((smallEtaleModelEquivalence B S hS U.1).functor.obj W)).trans
    (Over.postEquiv ((smallEtalePostcomp B S hS f hf).obj
      ((smallEtaleModelEquivalence B S hS U.1).functor.obj W))
        (smallEtaleModelEquivalence B S hS X.1).symm))).changeFunctor
    (G := Over.post (X := W) ((smallEtaleModelEquivalence B S hS U.1).functor ⋙
      (smallEtalePostcomp B S hS f hf ⋙ (smallEtaleModelEquivalence B S hS X.1).inverse)))
    (Iso.refl _)

/-- The structure map of `Φ_u` is invertible. -/
theorem isIso_etaleModelRingMap : IsIso (etaleModelRingMap B S hS f hf) := by
  have hb : IsIso (@Stacks.SheafOfModules.reindexBackSharp _ _ _ _
      (smallEtaleRingedSite B S hS X.1 X.2).J
      (smallEtaleModelRingedSite B S hS X.1 X.2).J (smallEtaleModelEquivalence B S hS X.1)
      (smallEtaleModelRingedSite_functor_isContinuous B S hS X.1 X.2)
      (smallEtaleModelRingedSite_inverse_isContinuous B S hS X.1 X.2)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) :=
    isIso_reindexBackSharp_smallEtaleModel B S hS X
  have h₂ : IsIso (etalePostcompModelRingMap B S hS f hf) :=
    IsIso.comp_isIso' (IsIso.id _) (@Functor.map_isIso _ _ _ _ _ _ _ _ hb)
  exact IsIso.comp_isIso' (IsIso.id _) (@Functor.map_isIso _ _ _ _ _ _ _ _ h₂)

/-- The structure map of `Φ_u` localized at `W` is invertible. -/
theorem isIso_postSlicePhi_etaleModel (W : (smallEtaleModelRingedSite B S hS U.1 U.2).C) :
    IsIso (RingedSite.postSlicePhi (etaleModelFunctor B S hS f hf)
      (etaleModelRingMap B S hS f hf) W) := by
  have h₀ := ((sheafToPresheaf _ _).mapIso
    (@asIso _ _ _ _ _ (isIso_etaleModelRingMap B S hS f hf))).isIso_hom
  have h₁ : IsIso ((sheafToPresheaf _ _).map
      (RingedSite.postSlicePhi (etaleModelFunctor B S hS f hf)
        (etaleModelRingMap B S hS f hf) W)) :=
    (Functor.isoWhiskerLeft (Over.forget W).op (@asIso _ _ _ _ _ h₀)).isIso_hom
  exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (sheafToPresheaf _ _) h₁ _

/-- The inverse of the slice equivalence of `Φ_u` is continuous. -/
theorem etaleModelSliceSiteEquiv_inverse_isContinuous (W : SmallEtaleModel B S hS U.1) :
    (etaleModelSliceSiteEquiv B S hS f hf W).inverse.IsContinuous
      ((smallEtaleModelTopology B S hS X.1).over
        (((smallEtaleModelEquivalence B S hS U.1).functor ⋙
          (smallEtalePostcomp B S hS f hf ⋙
            (smallEtaleModelEquivalence B S hS X.1).inverse)).obj W))
      ((smallEtaleModelTopology B S hS U.1).over W) := by
  have : (smallEtaleModelEquivalence B S hS X.1).symm.functor.IsContinuous
      (SmallEtale.topology B S hS X.1) (smallEtaleModelTopology B S hS X.1) :=
    inferInstanceAs ((smallEtaleModelEquivalence B S hS X.1).inverse.IsContinuous _ _)
  have : (smallEtaleModelEquivalence B S hS X.1).symm.inverse.IsContinuous
      (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1) :=
    inferInstanceAs ((smallEtaleModelEquivalence B S hS X.1).functor.IsContinuous _ _)
  let V := (smallEtaleModelEquivalence B S hS U.1).functor.obj W
  have hA := Over.postEquivInverseIsContinuous (J := smallEtaleModelTopology B S hS U.1)
    (K := SmallEtale.topology B S hS U.1) (smallEtaleModelEquivalence B S hS U.1) W
  have hB := SmallEtale.isContinuous_postcompOverInverse B S hS f hf V
  have hC := Over.postEquivInverseIsContinuous (J := SmallEtale.topology B S hS X.1)
    (K := smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquivalence B S hS X.1).symm
    ((smallEtalePostcomp B S hS f hf).obj V)
  exact @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _
    ((SmallEtale.topology B S hS U.1).over V) _
    (@Functor.isContinuous_comp _ _ _ _ _ _ _ _ _
      ((SmallEtale.topology B S hS X.1).over ((smallEtalePostcomp B S hS f hf).obj V)) _ hC hB) hA

/-- **Every slice functor of `Φ_u` induces a fully faithful functor on sheaves of modules**: it is
the functor of the equivalence of sheaves of modules induced by the slice equivalence of `Φ_u`,
whose structure map is invertible. -/
def etaleModelSliceFullyFaithful (W : (smallEtaleModelRingedSite B S hS U.1 U.2).C) :
    (RingedSite.postSliceFunctor (etaleModelFunctor B S hS f hf)
      (etaleModelRingMap B S hS f hf) W).FullyFaithful := by
  let W' : SmallEtaleModel B S hS U.1 := W
  let C := CategoryTheory.Over W'
  let D := CategoryTheory.Over (((smallEtaleModelEquivalence B S hS U.1).functor ⋙
    (smallEtalePostcomp B S hS f hf ⋙ (smallEtaleModelEquivalence B S hS X.1).inverse)).obj W')
  let iC : Category C := inferInstance
  let iD : Category D := inferInstance
  let J : GrothendieckTopology C := (smallEtaleModelTopology B S hS U.1).over W'
  let K : GrothendieckTopology D := (smallEtaleModelTopology B S hS X.1).over
    (((smallEtaleModelEquivalence B S hS U.1).functor ⋙
      (smallEtalePostcomp B S hS f hf ⋙ (smallEtaleModelEquivalence B S hS X.1).inverse)).obj W')
  let eqv : C ≌ D := etaleModelSliceSiteEquiv B S hS f hf W'
  have i₁ : eqv.functor.IsContinuous J K :=
    RingedSite.postSlice_isContinuous (etaleModelFunctor B S hS f hf) W
  have i₂ : eqv.inverse.IsContinuous K J :=
    etaleModelSliceSiteEquiv_inverse_isContinuous B S hS f hf W'
  let Sr : Sheaf J RingCat.{u} :=
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS U.1 U.2).O).over W
  let Rr : Sheaf K RingCat.{u} :=
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O).over
      ((etaleModelFunctor B S hS f hf).obj W)
  let ρ : Sr ⟶
      (@Functor.sheafPushforwardContinuous _ _ _ _ eqv.functor RingCat.{u} _ J K i₁).obj Rr :=
    RingedSite.postSlicePhi (etaleModelFunctor B S hS f hf) (etaleModelRingMap B S hS f hf) W
  have hρ : IsIso ρ := isIso_postSlicePhi_etaleModel B S hS f hf W
  exact (@SheafOfModules.pushforwardPushforwardEquivalence C iC D iD J K eqv Sr Rr i₁ i₂ ρ
    (@Stacks.SheafOfModules.InternalHom.inverseStructureMapOfIso C iC D iD J K eqv i₁ i₂ Sr Rr ρ hρ)
    (@Stacks.SheafOfModules.InternalHom.whiskerRight_counit_eq_inverseStructureMapOfIso
      C iC D iD J K eqv i₁ i₂ Sr Rr ρ hρ)
    (@Stacks.SheafOfModules.InternalHom.comp_inverseStructureMapOfIso_unit
      C iC D iD J K eqv i₁ i₂ Sr Rr ρ hρ)).fullyFaithfulFunctor

/-! ### The comparison on derived categories -/

/-- On modules, the model equivalence intertwines `u^*` and restriction along `Φ_u`. -/
def etaleModelModulesSquareIso :
    (modulesEquivModelModules B S hS X.1 X.2).functor ⋙ etaleModelRestriction B S hS f hf ≅
      etaleModulePullback.{u, u} B S hS f hf ⋙ (modulesEquivModelModules B S hS U.1 U.2).functor :=
  Functor.isoWhiskerLeft _ (etaleModelRestrictionIso B S hS f hf).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (modulesEquivModelModules B S hS X.1 X.2).unitIso.symm _ ≪≫
    Functor.leftUnitor _

section Derived

/- `D(𝒪_X)` and the derived equivalence with the model are stated at the standard model of the
derived category (`AlgebraicGeometry.Space.smallEtaleModelDerivedEquivalence`); at plain priority
another `HasDerivedCategory` instance on the sheaves of modules of the model is found first, and
the statements below do not typecheck. -/
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

/-- **On derived categories, the model equivalence intertwines `u^*` and restriction along
`Φ_u`.** -/
def etaleModelDerivedSquareIso :
    (smallEtaleModelDerivedEquivalence B S hS X).functor ⋙
        (etaleModelRestriction B S hS f hf).mapDerivedCategory ≅
      (etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory ⋙
        (smallEtaleModelDerivedEquivalence B S hS U).functor :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (modulesEquivModelModules B S hS X.1 X.2).functor (etaleModelRestriction B S hS f hf)).symm ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso
      ((modulesEquivModelModules B S hS X.1 X.2).functor ⋙ etaleModelRestriction B S hS f hf)
      (etaleModulePullback.{u, u} B S hS f hf ⋙ (modulesEquivModelModules B S hS U.1 U.2).functor)
      (etaleModelModulesSquareIso B S hS f hf) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (etaleModulePullback.{u, u} B S hS f hf) (modulesEquivModelModules B S hS U.1 U.2).functor

/-- **Restriction along `Φ_u` commutes with the derived internal Hom of the models**: the
transport of `AlgebraicGeometry.RingedSite.postSliceDerivedSheafHomNatIso` at `Φ_u`. -/
def etaleModelDerivedSheafHomIso
    (A C : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleModelRingedSite B S hS X.1 X.2).O))) :
    (etaleModelRestriction B S hS f hf).mapDerivedCategory.obj
        (((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).obj
          (op A)).obj C) ≅
      ((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS U.1 U.2)).obj
        (op ((etaleModelRestriction B S hS f hf).mapDerivedCategory.obj A))).obj
          ((etaleModelRestriction B S hS f hf).mapDerivedCategory.obj C) :=
  @RingedSite.postSliceDerivedSheafHomNatIso (smallEtaleModelRingedSite B S hS X.1 X.2)
    (smallEtaleModelRingedSite B S hS U.1 U.2) (etaleModelFunctor B S hS f hf)
    (etaleModelFunctor_isContinuous B S hS f hf) (etaleModelRingMap B S hS f hf)
    (etaleModelSliceFullyFaithful B S hS f hf)
    (etaleModelRestriction_preservesFiniteLimits B S hS f hf)
    (etaleModelRestriction_preservesFiniteColimits B S hS f hf)
    (etaleModelRestriction_isKInjective B S hS f hf) A C

/- The abelian structure of the modules is the one `DerivedCategory.Qh` and the derived pullback
read, as in the file `RelativelyPerfectHomDescentLocalization.lean` of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent`. -/
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

/-- **Étale restriction commutes with the derived internal Hom on algebraic spaces.** For an
étale morphism `u : U ⟶ X` of algebraic spaces, not necessarily a scheme chart, and `K`, `E` in
`D(𝒪_X)`, `Lu^* R𝓗om(K, E) ≅ R𝓗om(Lu^*K, Lu^*E)`.

On the equi-universe models `Lu^*` is restriction along the functor `Φ_u` induced by
postcomposition with `u` (`AlgebraicGeometry.Space.etaleModelDerivedSquareIso`), every slice
functor of which is an equivalence (`AlgebraicGeometry.Space.etaleModelSliceFullyFaithful`,
Stacks 04M0); the comparison is then
`AlgebraicGeometry.RingedSite.postSliceDerivedSheafHomNatIso`, which on K-injective models is the
class of the restriction of internal Hom complexes, as in Stacks 08JB. -/
def smallEtaleDerivedSheafHomEtaleRestrictionIso
    (K E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedModulePullback B S hS f).obj
        (((smallEtaleDerivedSheafHom B S hS X).obj (op K)).obj E) ≅
      ((smallEtaleDerivedSheafHom B S hS U).obj
        (op ((smallEtaleDerivedModulePullback B S hS f).obj K))).obj
          ((smallEtaleDerivedModulePullback B S hS f).obj E) :=
  let eX := smallEtaleModelDerivedEquivalence B S hS X
  let eU := smallEtaleModelDerivedEquivalence B S hS U
  let pb := smallEtaleDerivedModulePullbackIsoOfIsEtale B S hS f hf
  let sq := etaleModelDerivedSquareIso B S hS f hf
  let H' := RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS U.1 U.2)
  pb.app _ ≪≫ eU.unitIso.app _ ≪≫
    eU.inverse.mapIso ((sq.app _).symm ≪≫
      (etaleModelRestriction B S hS f hf).mapDerivedCategory.mapIso (eX.counitIso.app _) ≪≫
      etaleModelDerivedSheafHomIso B S hS f hf (eX.functor.obj K) (eX.functor.obj E) ≪≫
      (H'.mapIso (sq.app K).op).symm.app _ ≪≫ (H'.obj _).mapIso (sq.app E)) ≪≫
    ((smallEtaleDerivedSheafHom B S hS U).mapIso (pb.app K).op).app _ ≪≫
    ((smallEtaleDerivedSheafHom B S hS U).obj _).mapIso (pb.app E).symm

end Derived

end AlgebraicGeometry.Space

end
