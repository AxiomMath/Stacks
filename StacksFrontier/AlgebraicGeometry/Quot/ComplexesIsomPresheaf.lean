module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackLifts
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsomConeChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OverSchemeLocus

/-!
# The isomorphism presheaves of the stack of relatively perfect complexes

Let `f : X ⟶ Y` be a proper, flat, finitely presented morphism of algebraic spaces, the standing
data of Stacks 0DLE, and let `𝒳 = Complexes_{X/Y}`, fibred in groupoids over `(Sch/S)_fppf` by
Stacks 0DLF.  For two objects `x = (T, E)` and `y = (T, E')` of `𝒳` over the same test scheme
`T` over `Y`, this file identifies the presheaf `Isom(x, y)` of Stacks 02ZB on `(Sch/T)` with the
functor

`(T' ⟶ T) ↦ {isomorphisms E_{T'} ⟶ E'_{T'} in D(𝒪_{X_{T'}})}`,

`E_{T'}`, `E'_{T'}` being the derived pullbacks along `X_{T'} = X_T ×_T T' ⟶ X_T`.  This is the
identification with which the proofs of Stacks 0DLG and Stacks 0DPW begin ("we have to show that
`Isom(E, E')` is an algebraic space"), and its right-hand side is
`AlgebraicGeometry.Space.relativeDerivedIsomFunctor` for the projection `X_T ⟶ T`.

The identification is made in two steps.

1. The explicit pullback of `x` along `g : T' ⟶ T` is `(T', L(X_g)^*E)`, with the identity as
   its comparison of complexes (`AlgebraicGeometry.Space.ComplexesSituation.pullbackObject`);
   these lifts are strongly cartesian, because `𝒳` is fibred in groupoids, and they form a
   `CategoryTheory.Functor.CartesianLiftSystem`.  A section of `Isom(x, y)` over `g` is then a
   morphism of `𝒳` from `(T', L(X_g)^*E)` to `y` over `g`, that is an isomorphism
   `L(X_g)^*E' ⟶ L(X_g)^*E`, and restriction is precomposition with the transition morphisms.
   So `Isom(x, y)` is the relative Isom functor of the family of base changes
   `X ×_Y T' ⟶ X_T` (`AlgebraicGeometry.Space.ComplexesSituation.complexesIsomPresheafIso`).
2. The base changes `X ×_Y T'` and `X_T ×_T T'` are canonically isomorphic over `X_T`, both being
   fibre products of `X_T ⟶ T` with `T' ⟶ T`, so the two relative Isom functors are isomorphic
   (`CategoryTheory.PullbackData.relIsoFunctorConeChangeIso`).

The same comparison carries condition (2) of Stacks 0DLD for `E` over `T` to the vanishing of the
negative self-extensions of `E` on every fibre of `X_T ⟶ T` in the form
`AlgebraicGeometry.Space.HasNoNegativeFibreExtOver` that Stacks 0DLC is stated with
(`AlgebraicGeometry.Space.ComplexesSituation.hasNoNegativeFibreExtOver_of_hasNoNegativeFibreExt`).

## Main definitions

* `AlgebraicGeometry.Space.ComplexesSituation.complexesStack`: `Complexes_{X/Y}` as a category
  fibred in groupoids over `(Sch/S)_fppf`.
* `AlgebraicGeometry.Space.ComplexesSituation.overTest` and `overTestHom`: the test scheme
  `T' ⟶ T ⟶ Y` of an object `T' ⟶ T` of `(Sch/T)` and its morphism to `T`.
* `AlgebraicGeometry.Space.ComplexesSituation.complexesIsomPresheafIso`: **`Isom(x, y)` is the
  relative derived Isom functor of `E'` and `E` along `X_T ⟶ T`.**
* `AlgebraicGeometry.Space.ComplexesSituation.complexesIsomPresheafIsoRelativeDerivedIsomFunctor`:
  the same, with `E` and `E'` in the order of the source.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.hasNoNegativeFibreExtOver_of_hasNoNegativeFibreExt`:
  condition (2) of Stacks 0DLD for `E` over `T`, read on the test schemes over `T`.

## References

* [Stacks Project, Tag 0DLG](https://stacks.math.columbia.edu/tag/0DLG)
* [Stacks Project, Tag 0DPW](https://stacks.math.columbia.edu/tag/0DPW)
* [Stacks Project, Tag 0DLF](https://stacks.math.columbia.edu/tag/0DLF)
* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ComplexesSituation

variable {D : ComplexesSituation B S hS} (T : SchemesOver D.Y)

/-- **The family of base changes `X_T ×_T T' ⟶ X_T`** of the projection `X_T ⟶ T` over the
objects `T' ⟶ T` of `(Sch/T)`: the family of
`AlgebraicGeometry.Space.relativeDerivedIsomFunctor`, restricted to `(Sch/T)`. -/
abbrev overSchemesCone :=
  (PullbackData.ConeTo.ofOver (baseChangeOver (D.projection T))).precomp (overSchemeTest T.left)

/-- The square presenting `X ×_Y T'` as the fibre product of `X_T ⟶ T` and `T' ⟶ T`. -/
theorem isPullback_overTest (g : Over T.left) :
    IsPullback (D.relativeMap (overTestHom T g)) (D.projection ((overTest T).obj g))
      (D.projection T) ((schemeSpaceFunctor B S hS).map g.hom) :=
  isPullback_baseChangeMap D.f (overTestHom T g)

/-- The square presenting `X_T ×_T T'` as the fibre product of `X_T ⟶ T` and `T' ⟶ T`. -/
theorem isPullback_overSchemeTest (g : Over T.left) :
    IsPullback (baseChangeProjection (D.projection T) ((overSchemeTest T.left).obj g))
      (baseChangeInclusion (D.projection T) ((overSchemeTest T.left).obj g))
      (D.projection T) ((schemeSpaceFunctor B S hS).map g.hom) :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS (D.projection T) _

/-- **The comparison `X ×_Y T' ≅ X_T ×_T T'`** of the two fibre products of `X_T ⟶ T` and
`T' ⟶ T`. -/
def overTestSpaceIso (g : Over T.left) :
    D.space ((overTest T).obj g) ≅
      baseChangeSpace (D.projection T) ((overSchemeTest T.left).obj g) :=
  (isPullback_overTest T g).isoIsPullback _ _ (isPullback_overSchemeTest T g)

/-- The comparison `X ×_Y T' ≅ X_T ×_T T'` followed by the projection to `X_T` is the base change
map `X ×_Y T' ⟶ X_T`. -/
@[reassoc (attr := simp)]
theorem overTestSpaceIso_hom_projection (g : Over T.left) :
    (overTestSpaceIso T g).hom ≫
        baseChangeProjection (D.projection T) ((overSchemeTest T.left).obj g) =
      D.relativeMap (overTestHom T g) :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The comparison `X ×_Y T' ≅ X_T ×_T T'` followed by the map to `T'` is the projection
`X ×_Y T' ⟶ T'`. -/
@[reassoc (attr := simp)]
theorem overTestSpaceIso_hom_inclusion (g : Over T.left) :
    (overTestSpaceIso T g).hom ≫
        baseChangeInclusion (D.projection T) ((overSchemeTest T.left).obj g) =
      D.projection ((overTest T).obj g) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The comparisons `X ×_Y T' ≅ X_T ×_T T'` are natural in `T' ⟶ T`. -/
def overTestSpaceNatIso :
    overTestSpaces T ≅
      overSchemeTest T.left ⋙ baseChangeOver (D.projection T) ⋙ Over.forget (D.space T) :=
  NatIso.ofComponents (fun g => overTestSpaceIso T g) (fun {g₁ g₂} h => by
    change D.relativeMap ((overTest T).map h) ≫ (overTestSpaceIso T g₂).hom =
      (overTestSpaceIso T g₁).hom ≫ baseChangeMap (D.projection T) ((overSchemeTest T.left).map h)
    refine (isPullback_overSchemeTest T g₂).hom_ext ?_ ?_
    · rw [Category.assoc, overTestSpaceIso_hom_projection, Category.assoc,
        baseChangeMap_comp_projection, overTestSpaceIso_hom_projection,
        relativeMap_overTest_comp]
    · rw [Category.assoc, overTestSpaceIso_hom_inclusion, Category.assoc,
        baseChangeMap_comp_inclusion, overTestSpaceIso_hom_inclusion_assoc]
      exact baseChangeMap_comp_inclusion D.f ((overTest T).map h))

/-- The natural comparison `X ×_Y T' ≅ X_T ×_T T'` carries the leg `X_T ×_T T' ⟶ X_T` of
`overSchemesCone` to the leg `X ×_Y T' ⟶ X_T` of `overTestCone`. -/
theorem overTestSpaceNatIso_hom_app_leg (g : Over T.left) :
    (overTestSpaceNatIso T).hom.app g ≫ (overSchemesCone T).leg g = (overTestCone T).leg g :=
  overTestSpaceIso_hom_projection T g


/-! ### Condition (2) of Stacks 0DLD on the test schemes over `T` -/

/-- A fully faithful functor commuting with the shifts reflects the vanishing of `Ext^i`. -/
theorem _root_.CategoryTheory.Functor.subsingleton_shift_of_fullyFaithful {C : Type*}
    {C' : Type*} [Category* C] [Category* C'] [HasShift C ℤ] [HasShift C' ℤ] (F : C ⥤ C')
    (hF : F.FullyFaithful) [F.CommShift ℤ] (X : C) (i : ℤ)
    (h : Subsingleton (F.obj X ⟶ (F.obj X)⟦i⟧)) : Subsingleton (X ⟶ X⟦i⟧) :=
  ⟨fun _ _ => hF.map_injective ((cancel_mono ((F.commShiftIso i).hom.app X)).1
    (@Subsingleton.elim _ h _ _))⟩

/-- The derived pullback along a morphism of algebraic spaces commutes with the shifts. -/
instance smallEtaleDerivedPullbackData_pull_commShift {X X' : AlgebraicSpaces B S hS}
    (f : X ⟶ X') : ((smallEtaleDerivedPullbackData B S hS).pull f).CommShift ℤ := by
  rw [smallEtaleDerivedPullbackData_pull]
  haveI := hasDerivedModulePullbacks B S hS f
  exact Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback_commShift
    (smallEtaleRingedToposHom B S hS f)

/-- A test scheme over the algebraic space `T` is the image of an object of `(Sch/T)`. -/
theorem exists_overSchemeTest_obj_eq
    (T₀ : SchemesOver ((schemeSpaceFunctor B S hS).obj T.left)) :
    ∃ g : Over T.left, (overSchemeTest T.left).obj g = T₀ := by
  obtain ⟨L, R, f⟩ := T₀
  obtain ⟨g₀, rfl⟩ : ∃ g₀ : L ⟶ T.left, (schemeSpaceFunctor B S hS).map g₀ = f :=
    ⟨Yoneda.fullyFaithful.preimage f.hom,
      ObjectProperty.hom_ext _ (Yoneda.fullyFaithful.map_preimage _)⟩
  obtain rfl : R = ⟨⟨⟩⟩ := rfl
  exact ⟨Over.mk g₀, rfl⟩

/-- **Condition (2) of Stacks 0DLD, read on the test schemes over `T`.**  If the negative
self-extensions of `E` vanish on every fibre of `X_T ⟶ T` over a field-valued point, in the
form of Stacks 0DLE, then they vanish in the form
`AlgebraicGeometry.Space.HasNoNegativeFibreExtOver` for the projection `X_T ⟶ T`, in which
Stacks 0DLC is stated: the fibre `X_T ×_T T₀` is the fibre `X ×_Y T₀`. -/
theorem hasNoNegativeFibreExtOver_of_hasNoNegativeFibreExt (E : derivedModules B S hS (D.space T))
    (hE : D.HasNoNegativeFibreExt T E)
    (T' : SchemesOver ((schemeSpaceFunctor B S hS).obj T.left)) :
    HasNoNegativeFibreExtOver (D.projection T) E E T' := by
  intro T₀ hT₀ _ i hi
  obtain ⟨g, rfl⟩ := exists_overSchemeTest_obj_eq T T₀
  have h := hE ((overTest T).obj g) hT₀ (overTestHom T g) i hi
  let e := overTestSpaceIso T g
  let c := (smallEtaleDerivedPullbackData B S hS).triangle (overTestSpaceIso_hom_projection T g)
  refine @Functor.subsingleton_shift_of_fullyFaithful _ _ _ _ _ _ _
    ((smallEtaleDerivedPullbackData B S hS).pullFullyFaithfulOfIso e) inferInstance _ i ?_
  exact Equiv.subsingleton ((c.app E).homCongr ((shiftFunctor _ i).mapIso (c.app E))).symm


/-! ### `Isom(x, y)` as a relative derived Isom functor -/

section IsomPresheaf

attribute [local instance] complexesCategory

variable (A : ComplexesObject D) (E' : derivedModules B S hS (D.space A.T))
  (h₁ : D.IsRelativelyPerfect A.T E') (h₂ : D.HasNoNegativeFibreExt A.T E')

/-- The object `(T, E')` of `Complexes_{X/Y}` over the test scheme of a given object `(T, E)`. -/
abbrev sameTest : ComplexesObject D := ⟨A.T, E', h₁, h₂⟩

/-- A morphism of `Complexes_{X/Y}` lies over the underlying morphism of schemes of its base
map. -/
theorem isHomLift_of_base_left {x y : ComplexesObject D} (φ : x ⟶ y)
    (f : x.T.left ⟶ y.T.left) (hf : (φ : ComplexesHom x y).base.left = f) :
    (complexesFunctor D).IsHomLift f φ := by
  have e : (complexesFunctor D).map φ = f := hf
  rw [← e]
  exact IsHomLift.map (p := complexesFunctor D) φ

/-- An isomorphism `L(X_g)^*E' ⟶ L(X_g)^*E` as a morphism of `Complexes_{X/Y}` from the explicit
pullback `(T', L(X_g)^*E)` to `(T, E')`. -/
def isomHom (g : Over A.T.left)
    (α : (smallEtaleDerivedPullbackData B S hS).relHomObj (overTestCone A.T) E' A.E g)
    (hα : IsIso α) : overTestObject A g ⟶ sameTest A E' h₁ h₂ :=
  show ComplexesHom (overTestObject A g) (sameTest A E' h₁ h₂) from ⟨overTestHom A.T g, α, hα⟩

/-- An isomorphism `L(X_g)^*E' ⟶ L(X_g)^*E` as a morphism of `Complexes_{X/Y}` from the explicit
pullback `(T', L(X_g)^*E)` to `(T, E')` over `g`. -/
def isomToHomOver (g : Over A.T.left)
    (α : (smallEtaleDerivedPullbackData B S hS).relHomObj (overTestCone A.T) E' A.E g)
    (hα : IsIso α) : (overTestLiftSystem A).homOver (sameTest A E' h₁ h₂) g :=
  ⟨isomHom A E' h₁ h₂ g α hα, isHomLift_of_base_left (isomHom A E' h₁ h₂ g α hα) g.hom rfl⟩

/-- The base map of `isomHom` is the morphism of test schemes of `g`. -/
theorem isomHom_base (g : Over A.T.left)
    (α : (smallEtaleDerivedPullbackData B S hS).relHomObj (overTestCone A.T) E' A.E g)
    (hα : IsIso α) : (isomHom A E' h₁ h₂ g α hα : ComplexesHom _ _).base = overTestHom A.T g :=
  rfl

/-- The morphism of complexes of `isomHom` for `α` is `α`. -/
theorem isomHom_fibre (g : Over A.T.left)
    (α : (smallEtaleDerivedPullbackData B S hS).relHomObj (overTestCone A.T) E' A.E g)
    (hα : IsIso α) : HEq (isomHom A E' h₁ h₂ g α hα : ComplexesHom _ _).fibre α :=
  HEq.rfl

/-- A morphism over `g` from the explicit pullback `(T', L(X_g)^*E)` to `(T, E')` has the
morphism of test schemes of `g` as its base map. -/
theorem homOver_base (g : Over A.T.left)
    (φ : (overTestLiftSystem A).homOver (sameTest A E' h₁ h₂) g) :
    (φ.1 : ComplexesHom _ _).base = overTestHom A.T g := by
  have h : g.hom = (complexesFunctor D).map φ.1 :=
    @IsHomLift.eq_of_isHomLift _ _ _ _ (complexesFunctor D) (overTestObject A g)
      (sameTest A E' h₁ h₂) g.hom φ.1 φ.2
  exact CostructuredArrow.hom_ext _ _ h.symm

/-- Distinct isomorphisms `L(X_g)^*E' ⟶ L(X_g)^*E` give distinct morphisms over `g`. -/
theorem isomToHomOver_injective (g : Over A.T.left) :
    Function.Injective (fun α : ((smallEtaleDerivedPullbackData B S hS).relIsoFunctor
        (overTestCone A.T) (smallEtaleDerivedPullbackData_isCoherent B S hS) E' A.E).obj
          (op g) => isomToHomOver A E' h₁ h₂ g α.1 α.2) := by
  intro α β hαβ
  have h : (isomHom A E' h₁ h₂ g α.1 α.2 : ComplexesHom _ _) =
      (isomHom A E' h₁ h₂ g β.1 β.2 : ComplexesHom _ _) := congrArg Subtype.val hαβ
  injection h with _ h2
  exact Subtype.ext h2

/-- Every morphism over `g` from the explicit pullback `(T', L(X_g)^*E)` to `(T, E')` comes from
an isomorphism `L(X_g)^*E' ⟶ L(X_g)^*E`. -/
theorem isomToHomOver_surjective (g : Over A.T.left) :
    Function.Surjective (fun α : ((smallEtaleDerivedPullbackData B S hS).relIsoFunctor
        (overTestCone A.T) (smallEtaleDerivedPullbackData_isCoherent B S hS) E' A.E).obj
          (op g) => isomToHomOver A E' h₁ h₂ g α.1 α.2) := by
  intro φ
  have hb := homOver_base A E' h₁ h₂ g φ
  obtain ⟨⟨b, f, hf⟩, hφ⟩ := φ
  change b = overTestHom A.T g at hb
  subst hb
  exact ⟨⟨f, hf⟩, rfl⟩

/-- **The sections of `Isom((T, E), (T, E'))` over `g`, read on the explicit pullbacks, are the
isomorphisms `L(X_g)^*E' ⟶ L(X_g)^*E`.** -/
def isomEquivHomOver (g : Over A.T.left) :
    ((smallEtaleDerivedPullbackData B S hS).relIsoFunctor (overTestCone A.T)
      (smallEtaleDerivedPullbackData_isCoherent B S hS) E' A.E).obj (op g) ≃
      (overTestLiftSystem A).homOver (sameTest A E' h₁ h₂) g :=
  Equiv.ofBijective _ ⟨isomToHomOver_injective A E' h₁ h₂ g, isomToHomOver_surjective A E' h₁ h₂ g⟩

/-- The composition comparison along `X_{g₁ ⟶ g₂}` and `X_{g₂}` is the comparison of the family
of base changes `X ×_Y T' ⟶ X_T`, read through the identification of the composite. -/
theorem compComparison_overTestCone {g₁ g₂ : Over A.T.left} (h : g₁ ⟶ g₂) :
    D.compComparison ((overTest A.T).map h) (overTestObjectHom A g₂ : ComplexesHom _ _).base =
      eqToIso (congrArg (fun k : _ ⟶ A.T =>
          (smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap k))
        (overTest_map_comp_overTestHom A.T h)) ≪≫
        (smallEtaleDerivedPullbackData B S hS).triangle ((overTestCone A.T).w h) :=
  (smallEtaleDerivedPullbackData B S hS).triangle_congr _ _
    (congrArg (fun k : _ ⟶ A.T => D.relativeMap k) (overTest_map_comp_overTestHom A.T h))

/-- Restriction of isomorphisms along `g₁ ⟶ g₂` is precomposition with the transition morphism of
the explicit pullbacks. -/
theorem isomToHomOver_relHomMap {g₁ g₂ : Over A.T.left} (h : g₁ ⟶ g₂)
    (q : ((smallEtaleDerivedPullbackData B S hS).relIsoFunctor (overTestCone A.T)
      (smallEtaleDerivedPullbackData_isCoherent B S hS) E' A.E).obj (op g₂)) :
    (isomEquivHomOver A E' h₁ h₂ g₁ (((smallEtaleDerivedPullbackData B S hS).relIsoFunctor
        (overTestCone A.T) (smallEtaleDerivedPullbackData_isCoherent B S hS) E' A.E).map
          h.op q)).1 =
      (overTestLiftSystem A).trans h ≫ (isomEquivHomOver A E' h₁ h₂ g₂ q).1 := by
  show isomHom A E' h₁ h₂ g₁ _ _ =
    ComplexesHom.comp (overTestTrans A h) (isomHom A E' h₁ h₂ g₂ q.1 q.2)
  have key := fillIn_comp_eq_of_heq A E' h₁ h₂ (y := overTestObject A g₂)
    (z := overTestObject A g₁) (overTestObjectHom A g₂) ((overTest A.T).map h)
    (overTestTrans_eq A h) inferInstance rfl (heq_of_eq (overTestObjectHom_fibre A g₂))
    _ (isomHom A E' h₁ h₂ g₂ q.1 q.2) rfl HEq.rfl
    (overTest_map_comp_overTestHom A.T h)
    ((smallEtaleDerivedPullbackData B S hS).triangle ((overTestCone A.T).w h))
    (compComparison_overTestCone A h) rfl
    (isomHom A E' h₁ h₂ g₁ (((smallEtaleDerivedPullbackData B S hS).relIsoFunctor
        (overTestCone A.T) (smallEtaleDerivedPullbackData_isCoherent B S hS) E' A.E).map
          h.op q).1 (((smallEtaleDerivedPullbackData B S hS).relIsoFunctor
        (overTestCone A.T) (smallEtaleDerivedPullbackData_isCoherent B S hS) E' A.E).map
          h.op q).2) rfl HEq.rfl
  exact key.symm

/-- **`Mor((T, E), (T, E'))` is the relative derived Isom functor of `E'` and `E`** along the
family of base changes `X ×_Y T' ⟶ X_T`. -/
def complexesMorPresheafIso :
    (smallEtaleDerivedPullbackData B S hS).relIsoFunctor (overTestCone A.T)
        (smallEtaleDerivedPullbackData_isCoherent B S hS) E' A.E ≅
      Functor.morPresheaf (complexesFunctor D) ⟨A, rfl⟩ ⟨sameTest A E' h₁ h₂, rfl⟩ :=
  (overTestLiftSystem A).morPresheafIso ⟨sameTest A E' h₁ h₂, rfl⟩ _
    (isomEquivHomOver A E' h₁ h₂) (fun h q => isomToHomOver_relHomMap A E' h₁ h₂ h q)

/-- **`Isom((T, E), (T, E'))` is the relative derived Isom functor of `E'` and `E`** along the
family of base changes `X ×_Y T' ⟶ X_T`: the fibres of `Complexes_{X/Y}` are groupoids, so
`Isom = Mor`, and `Mor` is computed on the explicit pullbacks. -/
def complexesIsomPresheafIso :
    (complexesFunctor D).isomPresheaf ⟨A, rfl⟩ ⟨sameTest A E' h₁ h₂, rfl⟩ ≅
      (smallEtaleDerivedPullbackData B S hS).relIsoFunctor (overTestCone A.T)
        (smallEtaleDerivedPullbackData_isCoherent B S hS) E' A.E :=
  Functor.isomPresheafIsoMorPresheafOfGroupoid _ (isGroupoid_fiber_complexesFunctor D) _ _ ≪≫
    (complexesMorPresheafIso A E' h₁ h₂).symm

/-- **The fibres of the diagonal of `Complexes_{X/Y}`, read on `(Sch/T)`, are the relative
derived Isom functor of the projection `X_T ⟶ T`**: for objects `x = (T, E)` and `y = (T, E')`
over the same test scheme, `Isom(x, y)` is the functor
`(T' ⟶ T) ↦ {isomorphisms E_{T'} ⟶ E'_{T'} in D(𝒪_{X_T ×_T T'})}`.  This is the identification
with which the proofs of Stacks 0DLG and Stacks 0DPW begin. -/
def complexesIsomPresheafIsoRelativeDerivedIsomFunctor :
    (complexesFunctor D).isomPresheaf ⟨A, rfl⟩ ⟨sameTest A E' h₁ h₂, rfl⟩ ≅
      (overSchemeTest A.T.left).op ⋙ relativeDerivedIsomFunctor (D.projection A.T) A.E E' :=
  complexesIsomPresheafIso A E' h₁ h₂ ≪≫
    (PullbackData.relIsoFunctorConeChangeIso (overTestCone A.T) (overSchemesCone A.T)
      (overTestSpaceNatIso A.T) (overTestSpaceNatIso_hom_app_leg A.T)
      (smallEtaleDerivedPullbackData_isCoherent B S hS) E' A.E).symm ≪≫
    PullbackData.relIsoFunctorSymmIso (overSchemesCone A.T)
      (smallEtaleDerivedPullbackData_isCoherent B S hS) E' A.E ≪≫
    PullbackData.relIsoFunctorPrecompIso _ (smallEtaleDerivedPullbackData_isCoherent B S hS)
      (overSchemeTest A.T.left) A.E E'

end IsomPresheaf


end ComplexesSituation

end AlgebraicGeometry.Space

end
