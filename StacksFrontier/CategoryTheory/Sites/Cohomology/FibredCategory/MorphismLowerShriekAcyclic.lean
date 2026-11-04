module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.DerivedLowerShriekFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ProjectionLowerShriekAcyclic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriekAndPerfection.MorphismOfFibredCategoriesSection
import StacksCore.Tactic.StacksAttribute

/-!
# The acyclicity statement of Stacks 07AC for a 1-morphism of fibred categories

Let `u : C' ⥤ C` be a 1-morphism of fibred categories over a ringed site `(D, O_D)`, as in the
standing data of Stacks 08PA. This file discharges, with no hypothesis, the acyclicity statement
with which Stacks 07AC builds the left derived functor `Lg_!` of lower shriek along `u`: the
lower-shriek functor `g_!` on abelian sheaves carries every bounded above acyclic complex whose
terms are direct sums of the free abelian sheaves `j_{U'!} ℤ_{U'}` to an acyclic complex.

The argument is the one that `ProjectionLowerShriekAcyclic.lean` runs for the projection of a
fibred category, with the section of Stacks 08PB in place of the section of Stacks 08P9. By
`Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekAcyclic_of_ext_vanishing` everything
reduces to the object-level vanishing of Stacks 0D6X,

```
Ext^n(j_{U'!} ℤ_{U'}, g⁻¹ I) = 0   for I an injective abelian sheaf on C and n ≥ 1,
```

and that vanishing is dimension shifting against the restriction along the strongly cartesian
lifts at `U'`, read over the slice `D/p(u(U'))` of the base. Two facts make the argument go
through for `u`, and both are already available: that restriction is exact and preserves
injectives, because the cartesian section is right adjoint to the localized source projection;
and — this is the content of Stacks 08PB — the cartesian lifts at `U'` are carried by `u` to the
cartesian lifts at `u(U')`, so the restriction of `g⁻¹ I` is the restriction of `I` along the
cartesian lifts at `u(U')`, which is injective because that restriction preserves injectives.

## Main definitions

* `Stacks.Sites.FibredCategory.MorphismSituation.totalSituation`: the target fibred category,
  read as the standing data of Stacks 08P8 over the same base.
* `Stacks.Sites.FibredCategory.MorphismSituation.morphismLiftRestriction`: restriction along the
  strongly cartesian lifts at `U'`, from abelian sheaves on the source fibred category to abelian
  sheaves on the slice `D/p(u(U'))` of the base.

## Main results

* `Stacks.Sites.FibredCategory.MorphismSituation.morphismLiftRestriction_exact`: that restriction
  is exact and preserves injective objects.
* `Stacks.Sites.FibredCategory.MorphismSituation.morphismLiftRestrictionInverseImageIso`: it
  carries `g⁻¹ I` to the restriction of `I` along the cartesian lifts at `u(U')`.
* `MorphismSituation.subsingleton_ext_extensionByZeroUnitAb_abelianInverseImage`: **Stacks 0D6X
  for a 1-morphism of fibred categories**.
* `Stacks.Sites.FibredCategory.MorphismSituation.abelianLowerShriekAcyclic`: **the acyclicity
  statement of Stacks 07AC for `g_!`, discharged**, with no hypothesis.
* `MorphismSituation.hasPointwiseLeftDerivedFunctor_abelianLowerShriekOnHomotopy`: **Stacks 07AC
  for `g_!`**, existence of `Lg_!`, with no hypothesis.

## References

* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 08PA](https://stacks.math.columbia.edu/tag/08PA)
* [Stacks Project, Tag 08PB](https://stacks.math.columbia.edu/tag/08PB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace Stacks.Sites.FibredCategory

namespace MorphismSituation

universe u₀ u₁ u₂ v₀ v₁ v₂ w

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})

/-- Abelian sheaves on the source fibred category form a Grothendieck abelian category. This is
what gives them `Ext` groups in the universe of the sections; the same statement for the target
and for the base is `isGrothendieckAbelian_totalSheaves` and `isGrothendieckAbelian_baseSheaves`
in `DerivedLowerShriekFunctoriality.lean`. -/
instance isGrothendieckAbelian_sourceSheaves :
    IsGrothendieckAbelian.{max w u₀ u₁ u₂ v₀ v₁ v₂}
      (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  isGrothendieckAbelian_sheaf_addCommGrpCat.{u₂, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceTopology

/-- **The target fibred category, as the standing data of Stacks 08P8.** The same base ringed
site, with the target fibred category and its structure functor. -/
abbrev totalSituation : FibredCategorySituation.{u₀, v₀, u₁, v₁, max w u₀ u₁ u₂ v₀ v₁ v₂} where
  base := S.base
  C := S.total
  p := S.p

variable (U' : S.source)

/-- The functor `D/p(u(U')) ⥤ C'` sending `V ⟶ p(u(U'))` to the source of the chosen strongly
cartesian lift of `V ⟶ p'(U')` with target `U'`. -/
abbrev morphismLiftRestrictionFunctor : Over (S.p.obj (S.u.obj U')) ⥤ S.source :=
  sourceSliceCartesianSectionFunctor S U' ⋙ Over.forget U'

/-- **Restriction along the cartesian lifts at `U'`**, from abelian sheaves on the source fibred
category to abelian sheaves on the slice `D/p(u(U'))` of the base: the restriction `j_{U'}⁻¹` to
`C'/U'` followed by the inverse image `(σ')⁻¹ = π'_{U',*}` of the section of Stacks 08PB. -/
abbrev morphismLiftRestriction :
    Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} ⥤
      Sheaf (S.base.J.over (S.p.obj (S.u.obj U')))
        AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  letI := sourceSliceCartesianSection_isContinuous S U'
  S.sourceTopology.overPullback AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} U' ⋙
    (sourceSliceCartesianSectionFunctor S U').sheafPushforwardContinuous
      AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} (S.base.J.over (S.p.obj (S.u.obj U')))
      (S.sourceTopology.over U')

/-- The restriction along the cartesian lifts at `U'` preserves finite limits, finite colimits
and injective objects. Both factors are restrictions along functors which are continuous and
cocontinuous, hence exact; `j_{U'}⁻¹` preserves injectives because extension by zero is left
exact, and `(σ')⁻¹` because it is right adjoint to `(π'_{U'})⁻¹`, restriction along the
continuous localized source projection, which preserves monomorphisms. -/
theorem morphismLiftRestriction_exact :
    PreservesFiniteLimits (morphismLiftRestriction S U') ∧
      PreservesFiniteColimits (morphismLiftRestriction S U') ∧
        (morphismLiftRestriction S U').PreservesInjectiveObjects := by
  let v := sourceSliceCartesianSectionFunctor S U'
  let A := AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
  let JU := S.sourceTopology.over U'
  let K := S.base.J.over (S.p.obj (S.u.obj U'))
  have := sourceSliceProjection_isContinuous S U'
  have := sourceSliceCartesianSection_isContinuous S U'
  have := sourceSliceCartesianSection_isCocontinuous S U'
  have : ∀ W : S.source, HasSheafify (S.sourceTopology.over W) A := fun W =>
    hasSheafify_addCommGrpCat.{max u₂ v₂, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂} (S.sourceTopology.over W)
  have : HasSheafify K A :=
    hasSheafify_addCommGrpCat.{max u₀ v₀, v₀, max w u₀ u₁ u₂ v₀ v₁ v₂} K
  have : S.sourceTopology.WEqualsLocallyBijective A :=
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u₂, v₂,
      max w u₀ u₁ u₂ v₀ v₁ v₂} (J := S.sourceTopology)
  have : JU.WEqualsLocallyBijective A :=
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{max u₂ v₂, v₂,
      max w u₀ u₁ u₂ v₀ v₁ v₂} (J := JU)
  let adj := (sourceSliceCartesianSection_adjunction S U').sheafPushforwardAdjunction A
    (J := JU) (K := K)
  have hj₁ : PreservesFiniteLimits (S.sourceTopology.overPullback A U') := inferInstance
  have hj₂ : PreservesFiniteColimits (S.sourceTopology.overPullback A U') :=
    Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overPullback.{v₂, u₂,
      max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceTopology U'
  have hj₃ : (S.sourceTopology.overPullback A U').PreservesInjectiveObjects :=
    Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overPullback.{v₂, u₂,
      max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceTopology U'
  have hv₁ : PreservesFiniteLimits (v.sheafPushforwardContinuous A K JU) :=
    Functor.preservesFiniteLimits_sheafPushforwardContinuous K JU _ A
  have hv₂ : PreservesFiniteColimits (v.sheafPushforwardContinuous A K JU) :=
    Functor.preservesFiniteColimits_sheafPushforwardContinuous_of_isAlmostCocontinuous _ K JU
      (isAlmostCocontinuous_of_isCocontinuous _ K JU)
  have : PreservesFiniteLimits
      ((sourceSliceProjection S U').sheafPushforwardContinuous A JU K) :=
    Functor.preservesFiniteLimits_sheafPushforwardContinuous JU K _ A
  have : ((sourceSliceProjection S U').sheafPushforwardContinuous
      A JU K).PreservesMonomorphisms := preservesMonomorphisms_of_preservesLimitsOfShape _
  have : (v.sheafPushforwardContinuous A K JU).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  exact ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _, inferInstance⟩

/-- The object of the source fibred category reached from the terminal object of `D/p(u(U'))`,
the chosen strongly cartesian lift of the identity, is isomorphic to `U'`: a strongly cartesian
morphism lying over an isomorphism is an isomorphism. -/
def morphismLiftRestrictionFunctorObjIso :
    (morphismLiftRestrictionFunctor S U').obj (Over.mk (𝟙 (S.p.obj (S.u.obj U')))) ≅ U' :=
  let v := sourceSliceCartesianSectionFunctor S U'
  let T : Over (S.p.obj (S.u.obj U')) := Over.mk (𝟙 (S.p.obj (S.u.obj U')))
  have : IsIso (S.p'.map (v.obj T).hom) := by
    let e := (sourceSliceCartesianSection_base S U').app T
    have hleft : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    have : IsIso (S.p'.map (v.obj T).hom ≫ eqToHom (p'_obj_eq S U')) := by
      have hw : S.p'.map (v.obj T).hom ≫ eqToHom (p'_obj_eq S U') =
          e.hom.left ≫ T.hom := (Over.w e.hom).symm
      rw [hw]
      change IsIso (e.hom.left ≫ 𝟙 _)
      infer_instance
    exact IsIso.of_isIso_comp_right (S.p'.map (v.obj T).hom) (eqToHom (p'_obj_eq S U'))
  have := sourceSliceCartesianSection_isCartesian S U' T
  have : IsIso (v.obj T).hom :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso S.p' (S.p'.map (v.obj T).hom) _
  asIso (v.obj T).hom

/-- **The cartesian lifts at `U'` are carried by `u` to the cartesian lifts at `u(U')`
(Stacks 08PB).** So restriction along the cartesian lifts at `U'` of the inverse image `g⁻¹ I` of
an abelian sheaf on the target fibred category is restriction of `I` along the cartesian lifts at
`u(U')`. -/
def morphismLiftRestrictionInverseImageIso :
    S.abelianInverseImage ⋙ morphismLiftRestriction S U' ≅
      (totalSituation S).cartesianLiftRestriction (S.u.obj U') := by
  let A := AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
  let T := localizedProjectionSection (totalSituation S) (S.u.obj U')
  have := sourceSliceCartesianSection_isContinuous S U'
  have := T.cartesianSection_isContinuous
  haveI hpost : (Over.post S.u : Over U' ⥤ Over (S.u.obj U')).IsContinuous
      (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U')) :=
    isContinuous_overPost_u S U'
  haveI : (Over.forget U' ⋙ S.u).IsContinuous (S.sourceTopology.over U') S.totalTopology :=
    Functor.isContinuous_comp (Over.forget U') S.u (S.sourceTopology.over U') S.sourceTopology
      S.totalTopology
  haveI : ((Over.post S.u : Over U' ⥤ Over (S.u.obj U')) ⋙
      Over.forget (S.u.obj U')).IsContinuous (S.sourceTopology.over U') S.totalTopology :=
    Functor.isContinuous_comp (Over.post S.u) (Over.forget (S.u.obj U'))
      (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U')) S.totalTopology
  -- `j_{U'}⁻¹ ∘ g⁻¹ = (Over.post u)⁻¹ ∘ j_{u(U')}⁻¹`, both being restriction along
  -- `Over.forget U' ⋙ u = Over.post u ⋙ Over.forget (u U')`.
  let stepA : S.abelianInverseImage ⋙
      S.sourceTopology.overPullback A U' ≅
      S.totalTopology.overPullback A (S.u.obj U') ⋙
        (Over.post S.u : Over U' ⥤ Over (S.u.obj U')).sheafPushforwardContinuous A
          (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U')) :=
    Functor.sheafPushforwardContinuousComp'
        (Iso.refl (Over.forget U' ⋙ S.u)) A (S.sourceTopology.over U') S.sourceTopology
        S.totalTopology ≪≫
      (Functor.sheafPushforwardContinuousComp'
        (Iso.refl ((Over.post S.u : Over U' ⥤ Over (S.u.obj U')) ⋙
          Over.forget (S.u.obj U'))) A (S.sourceTopology.over U')
        (S.totalTopology.over (S.u.obj U')) S.totalTopology).symm
  -- `(σ')⁻¹ ∘ (Over.post u)⁻¹ = σ⁻¹`, by Stacks 08PB.
  let stepB : (Over.post S.u : Over U' ⥤ Over (S.u.obj U')).sheafPushforwardContinuous A
        (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U')) ⋙
      (sourceSliceCartesianSectionFunctor S U').sheafPushforwardContinuous A
        (S.base.J.over (S.p.obj (S.u.obj U'))) (S.sourceTopology.over U') ≅
      T.cartesianSectionFunctor.sheafPushforwardContinuous A
        (S.base.J.over (S.p.obj (S.u.obj U'))) (S.totalTopology.over (S.u.obj U')) :=
    Functor.sheafPushforwardContinuousComp' (sourceSliceCartesianSectionFunctorComp S U' T) A
      (S.base.J.over (S.p.obj (S.u.obj U'))) (S.sourceTopology.over U')
      (S.totalTopology.over (S.u.obj U'))
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight stepA _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ stepB

/-- **Stacks 0D6X for a 1-morphism of fibred categories.** The restriction `g⁻¹ I` of an injective
abelian sheaf on the target fibred category has vanishing cohomology `Ext^n(j_{U'!} ℤ_{U'}, g⁻¹ I)`
over every object `U'` of the source fibred category in positive degrees.

Restriction along the strongly cartesian lifts at `U'` is exact, preserves injectives and carries
`g⁻¹ I` to the restriction of `I` along the cartesian lifts at `u(U')`, which is injective because
that restriction preserves injectives too; morphisms out of `j_{U'!} ℤ_{U'}` are sections over
`U'`, which is the value of the first restriction at the terminal object of `D/p(u(U'))`.
Dimension shifting (`Stacks.Cohomology.subsingleton_ext_of_injective_map`) concludes. -/
theorem subsingleton_ext_extensionByZeroUnitAb_abelianInverseImage
    (I : Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) [Injective I]
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (Abelian.Ext
      (Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb.{max w u₀ u₁ u₂ v₀ v₁ v₂}
        S.sourceTopology U')
      (S.abelianInverseImage.obj I) n) := by
  let A := AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
  let T : Over (S.p.obj (S.u.obj U')) := Over.mk (𝟙 (S.p.obj (S.u.obj U')))
  let W : S.source := (morphismLiftRestrictionFunctor S U').obj T
  obtain ⟨h₁, h₂, h₃⟩ := morphismLiftRestriction_exact S U'
  obtain ⟨-, -, h₃'⟩ := (totalSituation S).cartesianLiftRestriction_exact (S.u.obj U')
  have : ∀ V : S.base.C, HasSheafify (S.base.J.over V) A := fun V =>
    hasSheafify_addCommGrpCat.{max u₀ v₀, v₀, max w u₀ u₁ u₂ v₀ v₁ v₂} (S.base.J.over V)
  have hI : Injective ((morphismLiftRestriction S U').obj (S.abelianInverseImage.obj I)) :=
    Injective.of_iso ((morphismLiftRestrictionInverseImageIso S U').app I).symm
      (((totalSituation S).cartesianLiftRestriction (S.u.obj U')).injective_obj I)
  let eU : Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb.{max w u₀ u₁ u₂ v₀ v₁ v₂}
      S.sourceTopology U' ≅
      Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb.{max w u₀ u₁ u₂ v₀ v₁ v₂}
        S.sourceTopology W :=
    (Presheaf.freeAbelianSheaf.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceTopology).mapIso
      (uliftYoneda.{max w u₀ u₁ u₂ v₀ v₁ v₂}.mapIso
        (morphismLiftRestrictionFunctorObjIso S U').symm)
  refine Stacks.Cohomology.subsingleton_ext_of_iso eU n ?_
  have : EnoughInjectives (Sheaf S.sourceTopology A) := inferInstance
  have : (morphismLiftRestriction S U').PreservesZeroMorphisms := by
    let := sourceSliceCartesianSection_isContinuous S U'
    have : (S.sourceTopology.overPullback A U').Additive :=
      Functor.additive_sheafPushforwardContinuous (Over.forget U') (S.sourceTopology.over U')
        S.sourceTopology A
    have : ((sourceSliceCartesianSectionFunctor S U').sheafPushforwardContinuous A
        (S.base.J.over (S.p.obj (S.u.obj U'))) (S.sourceTopology.over U')).Additive :=
      Functor.additive_sheafPushforwardContinuous _ _ _ A
    have : (morphismLiftRestriction S U').Additive :=
      inferInstanceAs (Functor.Additive (_ ⋙ _))
    exact Functor.preservesZeroMorphisms_of_additive _
  refine Stacks.Cohomology.subsingleton_ext_of_injective_map (morphismLiftRestriction S U')
    _ (fun Y Z g hg f => ?_) n hn _ hI
  obtain ⟨⟨sec, hsec⟩⟩ := hg
  let Ev := fun F : Sheaf S.sourceTopology A =>
    Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAbHomEquiv.{
      max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceTopology W F
  let x : ((morphismLiftRestriction S U').obj Z).obj.obj (Opposite.op T) := Ev Z f
  let y : Y.obj.obj (Opposite.op W) := (sec.hom.app (Opposite.op T)).hom x
  refine ⟨(Ev Y).symm y, (Ev Z).injective ?_⟩
  rw [Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAbHomEquiv_naturality]
  simp only [Ev, Equiv.apply_symm_apply]
  exact congrArg (fun φ => φ.hom.app (Opposite.op T) x) hsec

/-- **The acyclicity statement of Stacks 07AC for a 1-morphism of fibred categories,
discharged.** The lower-shriek functor `g_!` on abelian sheaves carries every bounded above
acyclic complex whose terms are direct sums of the free abelian sheaves `j_{U'!} ℤ_{U'}` to an
acyclic complex. By
`Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekAcyclic_of_ext_vanishing` this is the
object-level vanishing of Stacks 0D6X, which is
`subsingleton_ext_extensionByZeroUnitAb_abelianInverseImage`. -/
theorem abelianLowerShriekAcyclic : S.AbelianLowerShriekAcyclic :=
  Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekAcyclic_of_ext_vanishing.{
    max w u₀ u₁ u₂ v₀ v₁ v₂, max w u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₁, u₁}
    S.sourceTopology S.totalTopology S.u
    fun V I _ n hn => subsingleton_ext_extensionByZeroUnitAb_abelianInverseImage S V I n hn

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 07AC for `g_!`**, existence, with no hypothesis: the left derived functor `Lg_!` of
degreewise lower shriek along the 1-morphism exists at every object. -/
instance hasPointwiseLeftDerivedFunctor_abelianLowerShriekOnHomotopy :
    (S.abelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf S.sourceTopology
        AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) (ComplexShape.up ℤ)) :=
  S.hasPointwiseLeftDerivedAbelianLowerShriek S.abelianLowerShriekAcyclic

end Derived

end MorphismSituation

end Stacks.Sites.FibredCategory

end
