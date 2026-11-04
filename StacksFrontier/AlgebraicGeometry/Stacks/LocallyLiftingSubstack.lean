module

public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.FullSubcategoryBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomPresheafFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangedFlatPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaAlgebraicSpaceSources
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableStackInSetoids
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoidRelativeProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOverFieldTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstackExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeFlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeFromMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack

/-!
# The substack of objects locally lifting along a 1-morphism

Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism from a category fibred in groupoids to an algebraic stack over
`S`. An object `ξ` of `𝒳` *lifts locally to `f`* when the arrows `k : V ⟶ p(ξ)` along which `ξ`
receives a morphism from the image of an object of `𝒰` form a covering sieve for the fppf
topology. These objects form a strictly full subcategory of `𝒳`, and this file proves that it is
an algebraic stack through which `f` factors by a surjective, flat 1-morphism, locally of finite
presentation, as soon as `𝒰` is an algebraic space and the first projection of the
self-intersection `𝒰 ×_𝒳 𝒰 ⟶ 𝒰` is surjective, flat and locally of finite presentation.

This is the construction which in the Stacks project is phrased as "the quotient stack `[U/R]`
of the restricted groupoid is algebraic by Stacks 06FI, and `[U/R] ⟶ 𝒳` is fully faithful by
Stacks 046S and 04ZZ": the substack constructed here is the essential image of `[U/R] ⟶ 𝒳`. The
algebraicity is obtained without Artin's theorem Stacks 06DC, which the library's Stacks 06FI
carries as a hypothesis, because the substack sits inside the algebraic stack `𝒳`: its inclusion
is representable by algebraic spaces by the bootstrap theorem Stacks 04S6, and Stacks 05UM applies.

## Main definitions

* `AlgebraicGeometry.Stack.liftingSieve`: the sieve of arrows along which an object lifts to `f`.
* `AlgebraicGeometry.Stack.LocallyLifts`: the objects lifting locally to `f`.
* `AlgebraicGeometry.Stack.toLocallyLifting`: the factorization of `f` through them.

## Main results

* `AlgebraicGeometry.Stack.isStack_locallyLifts`: the subcategory is a stack, by Stacks 04TU.
* `AlgebraicGeometry.Stack.hasRepresentableDiagonal_fullSubcategoryBased`: a full subcategory of
  an algebraic stack has representable diagonal.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_liftedSelfSquare`: the self-intersection of `f` over
  `𝒳` is also its self-intersection over the subcategory.
* `AlgebraicGeometry.Stack.hasRelativeProperty_toLocallyLifting`: the factorization inherits
  every relative property of the projection of the self-intersection, by Stacks 045D.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_locallyLiftingInclusion`: the
  inclusion is representable by algebraic spaces, by Stacks 04S6.
* `AlgebraicGeometry.Stack.exists_isAlgebraicStack_locallyLifts`: the assembled statement.
* `AlgebraicGeometry.Stack.exists_isAlgebraicStack_locallyLifts_of_fieldSpectrum`: the same for a
  point with values in a field, where only local finite presentation of the projection of the
  self-intersection is asked for.
* `AlgebraicGeometry.Stack.exists_isResidualGerbeAt_of_fieldSpectrum`: the residual gerbe at the
  image of such a point exists.

## References

* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04TU](https://stacks.math.columbia.edu/tag/04TU)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 06FI](https://stacks.math.columbia.edu/tag/06FI)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS}
  {𝒰 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒰 ⟶ 𝒳.val)

/-- The sieve of the arrows along which an object of `𝒳` lifts to `f`. -/
def liftingSieve (ξ : 𝒳.val.val.obj) : Sieve (𝒳.val.val.p.obj ξ) where
  arrows V k := ∃ (z : 𝒰.val.obj) (φ : (CatFiberedInGroupoids.homFunctor f).obj z ⟶ ξ),
    𝒳.val.val.p.IsHomLift k φ
  downward_closed := by
    rintro V W k ⟨z, φ, hφ⟩ g
    have hz : 𝒰.val.p.obj z = V := by
      rw [← IsHomLift.domain_eq 𝒳.val.val.p k φ]
      exact (Functor.congr_obj f.hom.w z).symm
    obtain ⟨z', ψ, hψ⟩ := 𝒰.property.exists_lift g z hz
    refine ⟨z', (CatFiberedInGroupoids.homFunctor f).map ψ ≫ φ, ?_⟩
    have : 𝒳.val.val.p.IsHomLift g ((CatFiberedInGroupoids.homFunctor f).map ψ) :=
      Functor.isHomLift_map_of_comp_eq f.hom.w g ψ
    infer_instance

/-- The objects of `𝒳` which lift to `f` locally for the fppf topology. -/
def LocallyLifts : ObjectProperty 𝒳.val.val.obj := fun ξ =>
  liftingSieve f ξ ∈ BigFppfOver.topology B S hS (𝒳.val.val.p.obj ξ)

variable {f}

/-- Every object of `𝒳` admitting a morphism to one lifting locally lifts locally. -/
theorem locallyLifts_of_hom {a b : 𝒳.val.val.obj} (m : a ⟶ b) (hb : LocallyLifts f b) :
    LocallyLifts f a := by
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    ((BigFppfOver.topology B S hS).pullback_stable (𝒳.val.val.p.map m) hb)
  rintro V k ⟨z, φ, hφ⟩
  have hd := IsHomLift.domain_eq 𝒳.val.val.p (k ≫ 𝒳.val.val.p.map m) φ
  obtain ⟨χ, ⟨hχ, -⟩, -⟩ := 𝒳.val.property.unique_lift m φ (eqToHom hd ≫ k) (by
      rw [IsHomLift.fac' 𝒳.val.val.p (k ≫ 𝒳.val.val.p.map m) φ]
      simp)
  exact ⟨z, χ, IsHomLift.of_fac' _ _ _ hd rfl (by rw [hχ]; simp)⟩

/-- The image of an object of `𝒰` lifts locally, along the maximal sieve. -/
theorem locallyLifts_obj (z : 𝒰.val.obj) :
    LocallyLifts f ((CatFiberedInGroupoids.homFunctor f).obj z) :=
  (BigFppfOver.topology B S hS).covering_of_eq_top
    (Sieve.id_mem_iff_eq_top.1 ⟨z, 𝟙 _, inferInstance⟩)

/-- Local lifting is local on the base: an object whose pullbacks along a covering family lift
locally lifts locally. -/
theorem locallyLifts_locallyClosed :
    haveI : 𝒳.val.val.p.IsPreFibered := 𝒳.val.property.isFibered.toIsPreFibered
    Functor.LocallyClosed 𝒳.val.val.p (LocallyLifts f) (BigFppfOver.topology B S hS) := by
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.property.isFibered
  intro U ι Uᵢ fᵢ hcov x hx
  obtain ⟨x, rfl⟩ := x
  refine Functor.isoOverId_of_prop ?_
  refine (BigFppfOver.topology B S hS).transitive hcov _ ?_
  rintro W g ⟨W', h, g', ⟨i⟩, rfl⟩
  rw [Sieve.pullback_comp]
  refine (BigFppfOver.topology B S hS).pullback_stable h ?_
  obtain ⟨y', hy', e, he⟩ := hx i
  have hy := locallyLifts_of_hom e.hom hy'
  set y := Functor.pullbackFiber 𝒳.val.val.p ⟨x, rfl⟩ (fᵢ i)
  have hyU : 𝒳.val.val.p.obj y.1 = Uᵢ i := y.2
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    ((BigFppfOver.topology B S hS).pullback_stable (eqToHom hyU.symm) hy)
  rintro V k ⟨z, φ, hφ⟩
  have hφ' : 𝒳.val.val.p.IsHomLift k φ :=
    (IsHomLift.lift_comp_eqToHom_iff _ _ _ _).1 hφ
  have hπ : 𝒳.val.val.p.IsHomLift (fᵢ i)
      (Functor.IsPreFibered.pullbackMap (rfl : 𝒳.val.val.p.obj x = _) (fᵢ i)) := inferInstance
  exact ⟨z, φ ≫ Functor.IsPreFibered.pullbackMap (rfl : 𝒳.val.val.p.obj x = _) (fᵢ i),
    inferInstance⟩

variable (f) in
/-- **The full subcategory of objects lifting locally to `f` is a stack**, by Stacks 04TU. -/
theorem isStack_locallyLifts :
    (fullSubcategoryBased 𝒳 (LocallyLifts f)).p.IsStack (BigFppfOver.topology B S hS) :=
  Functor.IsStack.fullSubcategory 𝒳.val.val.p _ 𝒳.property.2.1.1 (LocallyLifts f)
    (fun _ φ _ hx => Functor.isoOverId_of_prop (locallyLifts_of_hom φ hx))
    locallyLifts_locallyClosed

section Diagonal

variable (𝒳) in
/-- The full subcategory of `𝒳` cut out by a property inherited along morphisms, as a category
fibred in groupoids over the big fppf site of `S`. -/
abbrev fullSubcategoryCFG {P : ObjectProperty 𝒳.val.val.obj}
    (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a) :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (fullSubcategoryBased 𝒳 P)
    (isFiberedInGroupoids_fullSubcategoryBased 𝒳 hP)

variable (𝒳) in
/-- **The diagonal of a full subcategory of an algebraic stack is representable**: its
isomorphism sheaves are those of `𝒳`, by `AlgebraicGeometry.Stack.liftedIsomPresheafIso`. -/
theorem hasRepresentableDiagonal_fullSubcategoryBased {P : ObjectProperty 𝒳.val.val.obj}
    (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a) :
    HasRepresentableDiagonal B S hS (fullSubcategoryCFG 𝒳 hP) := by
  have h𝒳 := (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳.val).1
    𝒳.property.2.2.1
  refine (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS
    (fullSubcategoryCFG 𝒳 hP)).2 ?_
  have : (fullSubcategoryCFG 𝒳 hP).val.p.IsFibered := (fullSubcategoryCFG 𝒳 hP).property.isFibered
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.property.isFibered
  intro U x y
  let ι := fullSubcategoryBasedInclusion 𝒳 P
  have hF : Functor.IsFibredOneMorphism (fullSubcategoryCFG 𝒳 hP).val.p 𝒳.val.val.p
      ι.toFunctor :=
    { comp_eq := ι.w
      map_isStronglyCartesian := fun f _ _ φ _ => by
        have : 𝒳.val.val.p.IsHomLift f (ι.toFunctor.map φ) :=
          Functor.isHomLift_map_of_comp_eq (p := (fullSubcategoryCFG 𝒳 hP).val.p) ι.w f φ
        exact 𝒳.val.property.isStronglyCartesian_homLift f (ι.toFunctor.map φ) }
  have : ι.toFunctor.Full := ObjectProperty.full_ι P
  have : ι.toFunctor.Faithful := ObjectProperty.faithful_ι P
  let e : (fullSubcategoryCFG 𝒳 hP).val.p.isomPresheaf x y ⋙ uliftFunctor.{u, u} ≅
      𝒳.val.val.p.isomPresheaf ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj x)
        ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj y) :=
    liftedIsomPresheafIso hF (fullSubcategoryCFG 𝒳 hP).property 𝒳.val.property x y
  obtain ⟨F, hFalg, ⟨e'⟩⟩ := h𝒳 U ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj x)
    ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj y)
  exact ⟨F, hFalg, ⟨e' ≪≫ Functor.isoWhiskerLeft _ uliftFunctorTrivial.{u} ≪≫
    Functor.rightUnitor _ ≪≫ (Functor.isoWhiskerLeft (Over.iteratedSliceBackward U).op e).symm ≪≫
    (Functor.associator _ _ _).symm⟩⟩

end Diagonal

section Lift

variable (f)

/-- The full subcategory of objects lifting locally to `f`, as a category fibred in groupoids. -/
abbrev locallyLiftingCFG : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  fullSubcategoryCFG 𝒳 (P := LocallyLifts f) locallyLifts_of_hom

/-- The inclusion of the objects lifting locally to `f`. -/
abbrev locallyLiftingInclusion : locallyLiftingCFG f ⟶ 𝒳.val :=
  Bicategory.InducedBicategory.mkHom (fullSubcategoryBasedInclusion 𝒳 (LocallyLifts f))

/-- The factorization of `f` through the objects lifting locally to it. -/
abbrev toLocallyLifting : 𝒰 ⟶ locallyLiftingCFG f :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := ObjectProperty.lift _ (CatFiberedInGroupoids.homFunctor f) locallyLifts_obj
      w := f.hom.w }

/-- The factorization `toLocallyLifting f` composed with the inclusion `locallyLiftingInclusion f`
is `f`. -/
theorem toLocallyLifting_comp_inclusion :
    toLocallyLifting f ≫ locallyLiftingInclusion f = f := rfl

end Lift

section Square

/-- A morphism of a full subcategory lies over what its underlying morphism lies over. -/
theorem isHomLift_restrict {P : ObjectProperty 𝒳.val.val.obj} {a b : P.FullSubcategory}
    (φ : a ⟶ b) {R T : BigFppfOver B S hS} (g : R ⟶ T)
    (h : 𝒳.val.val.p.IsHomLift g φ.hom) : (P.ι ⋙ 𝒳.val.val.p).IsHomLift g φ :=
  IsHomLift.of_fac' _ g φ (IsHomLift.domain_eq 𝒳.val.val.p g φ.hom)
    (IsHomLift.codomain_eq 𝒳.val.val.p g φ.hom) (IsHomLift.fac' 𝒳.val.val.p g φ.hom)

variable (f)

/-- The canonical self-intersection square of `f` over `𝒳`. -/
abbrev selfSquare : Bicategory.TwoCommSq f f :=
  CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f f

/-- The filler of the self-intersection square of `f`, lifted through the fully faithful
inclusion of the objects lifting locally to `f`. -/
noncomputable def liftedSelfIso :
    (selfSquare f).fst ≫ toLocallyLifting f ≅ (selfSquare f).snd ≫ toLocallyLifting f :=
  Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso
    (((ObjectProperty.fullyFaithfulι (LocallyLifts f)).whiskeringRight _).preimageIso
      (CatFiberedInGroupoids.underlyingIso (selfSquare f).iso))
    (fun t => isHomLift_restrict _ _ ((selfSquare f).iso.hom.hom.isHomLift' t)))

/-- The self-intersection square of `f` read over the objects lifting locally to `f`. -/
noncomputable def liftedSelfSquare :
    Bicategory.TwoCommSq (toLocallyLifting f) (toLocallyLifting f) where
  pt := (selfSquare f).pt
  fst := (selfSquare f).fst
  snd := (selfSquare f).snd
  iso := liftedSelfIso f

/-- The comparison of the lifted square with the canonical 2-fibre product over the objects
lifting locally to `f` is an equivalence. -/
theorem isEquivalence_liftLiftedSelfSquare :
    (CatFiberedInGroupoids.liftTwoFibreProductSquare.{u, u, u + 1, u + 1} (toLocallyLifting f)
      (toLocallyLifting f) (liftedSelfSquare f)).hom.toFunctor.IsEquivalence := by
  set L := (CatFiberedInGroupoids.liftTwoFibreProductSquare.{u, u, u + 1, u + 1}
    (toLocallyLifting f) (toLocallyLifting f) (liftedSelfSquare f)).hom.toFunctor
  have hfaith : L.Faithful := by
    refine ⟨fun {t t'} m m' h => ?_⟩
    have ha := congrArg TwoFibreProductOver.Hom.a h
    have hb := congrArg TwoFibreProductOver.Hom.b h
    exact TwoFibreProductOver.Hom.ext' ha hb
  have hfull : L.Full := by
    refine ⟨fun {t t'} Φ => ?_⟩
    refine ⟨{ hbase := Φ.hbase, a := Φ.a, b := Φ.b, ha := Φ.ha, hb := Φ.hb, w := ?_ },
      TwoFibreProductOver.Hom.ext' rfl rfl⟩
    exact congrArg (fun φ => φ.hom) Φ.w
  have hess : L.EssSurj := by
    refine ⟨fun s => ?_⟩
    have hv : 𝒳.val.val.p.IsHomLift (𝟙 s.base) s.iso.hom.hom := by
      have := s.vertical
      exact IsHomLift.of_fac' _ _ _
        (IsHomLift.domain_eq (locallyLiftingCFG f).val.p (𝟙 s.base) s.iso.hom)
        (IsHomLift.codomain_eq (locallyLiftingCFG f).val.p (𝟙 s.base) s.iso.hom)
        (IsHomLift.fac' (locallyLiftingCFG f).val.p (𝟙 s.base) s.iso.hom)
    let t : (liftedSelfSquare f).pt.val.obj :=
      { base := s.base, x := s.x, y := s.y, hx := s.hx, hy := s.hy,
        iso := (LocallyLifts f).ι.mapIso s.iso, vertical := hv }
    exact ⟨t, ⟨Iso.refl _⟩⟩
  exact Functor.IsEquivalence.mk

end Square

section RelativeProperty

variable (f)

/-- The lifted self-intersection square is a 2-fibre product over the objects lifting locally to
`f`. -/
noncomputable def isTwoFibreProduct_liftedSelfSquare :
    Bicategory.IsTwoFibreProduct (liftedSelfSquare f) :=
  Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (toLocallyLifting f) (toLocallyLifting f))
    (CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u, u + 1, u + 1}
      (toLocallyLifting f) (toLocallyLifting f) (liftedSelfSquare f))
    (isEquivalence_liftLiftedSelfSquare f)

/-- The factorization of `f` through the objects lifting locally to it is representable by
algebraic spaces when the source of `f` is an algebraic space. -/
theorem isRepresentableByAlgebraicSpaces_toLocallyLifting
    (h𝒰 : IsRepresentableByAlgebraicSpace B S hS 𝒰) :
    IsRepresentableByAlgebraicSpaces B S hS (toLocallyLifting f).hom :=
  isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace_source B S hS
    (hasRepresentableDiagonal_fullSubcategoryBased 𝒳 locallyLifts_of_hom) h𝒰 (toLocallyLifting f)

/-- **The factorization of `f` inherits every relative property of the projection of its
self-intersection**, by Stacks 045D: every object of the substack lifts to it locally. -/
theorem hasRelativeProperty_toLocallyLifting
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (h𝒰 : IsRepresentableByAlgebraicSpace B S hS 𝒰)
    (hR : ∃ h, HasRelativeProperty B S hS P (selfSquare f).fst h) :
    HasRelativeProperty B S hS P (toLocallyLifting f)
      (isRepresentableByAlgebraicSpaces_toLocallyLifting f h𝒰) := by
  obtain ⟨_, hR⟩ := hR
  refine hasRelativeProperty_of_baseChange.{u, u, u + 1, u} B S hS 𝒰 (locallyLiftingCFG f) 𝒰 P
    (toLocallyLifting f) (toLocallyLifting f) (liftedSelfSquare f)
    (isTwoFibreProduct_liftedSelfSquare f) _ ?_ hR
  rintro U ⟨y, rfl⟩
  refine ⟨liftingSieve f y.obj, y.property, ?_⟩
  rintro V k ⟨z, φ, hφ⟩
  exact ⟨z, ObjectProperty.homMk φ, isHomLift_restrict _ _ hφ⟩

end RelativeProperty

section Algebraic

variable (f)

/-- **The inclusion of the objects lifting locally to `f` is representable by algebraic spaces**,
as soon as the source of `f` is an algebraic space and the projection of the self-intersection of
`f` is surjective, flat and locally of finite presentation. -/
theorem isRepresentableByAlgebraicSpaces_locallyLiftingInclusion
    (h𝒰 : IsRepresentableByAlgebraicSpace B S hS 𝒰)
    (hsurj : ∃ h, HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS)
      (selfSquare f).fst h)
    (hflat : ∃ h, HasRelativeProperty.{u, u, u + 1, u} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) => Space.IsFlat B S hS k.hom)
      (selfSquare f).fst h)
    (hlfp : ∃ h, HasRelativeProperty.{u, u, u + 1, u} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS k.hom) (selfSquare f).fst h) :
    IsRepresentableByAlgebraicSpaces B S hS (locallyLiftingInclusion f).hom := by
  refine isRepresentableByAlgebraicSpaces_of_forall_twoFibreProduct B S hS 𝒳.val
    (locallyLiftingCFG f) (locallyLiftingInclusion f).hom fun V y => ?_
  rw [isRepresentableByAlgebraicSpace_twoFibreProduct_swap_iff]
  have hy : IsRepresentableByAlgebraicSpaces B S hS y :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V)
      (Bicategory.InducedBicategory.mkHom y)
  let q : twoFibreProduct B S hS 𝒳.val (locallyLiftingCFG f) (schemeFibredCategory B S hS V)
      (locallyLiftingInclusion f).hom y ⟶ locallyLiftingCFG f :=
    Bicategory.InducedBicategory.mkHom (twoFibreProductFst B S hS 𝒳.val (locallyLiftingCFG f)
      (schemeFibredCategory B S hS V) (locallyLiftingInclusion f).hom y)
  have hq : IsRepresentableByAlgebraicSpaces B S hS q.hom :=
    isRepresentableByAlgebraicSpaces_twoFibreProductFst B S hS 𝒳.val _ _ _ y hy
  have hWstack := isStack_of_isRepresentableByAlgebraicSpaces B S hS q hq (isStack_locallyLifts f)
  have : (fullSubcategoryBasedInclusion 𝒳 (LocallyLifts f)).toFunctor.Faithful :=
    ObjectProperty.faithful_ι _
  have hWset := Functor.isStackInSetoids_structureFunctor (BigFppfOver.topology B S hS)
    (locallyLiftingCFG f).property
    (isStackInSetoids_of_isRepresentableByAlgebraicSpace B S hS _
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V)) hWstack
  exact isRepresentableByAlgebraicSpace_of_isStackInSetoids_of_baseChange B S hS
    (toLocallyLifting f) q hWset h𝒰 (isRepresentableByAlgebraicSpaces_toLocallyLifting f h𝒰)
    (hasRelativeProperty_toLocallyLifting f _ h𝒰 hsurj)
    (hasRelativeProperty_toLocallyLifting f _ h𝒰 hflat)
    (hasRelativeProperty_toLocallyLifting f _ h𝒰 hlfp) hq

end Algebraic

section Assembly

/-- **The locally lifting substack of a 1-morphism out of a scheme.** Let `f : U ⟶ 𝒳` be a
1-morphism from (the algebraic stack of) a scheme `U` to an algebraic stack, and suppose that the
first projection `U ×_𝒳 U ⟶ U` of its self-intersection is surjective, flat and locally of finite
presentation. Then the strictly full subcategory of `𝒳` of the objects which lift to `f` locally
for the fppf topology is an algebraic stack, and `f` factors through it by a 1-morphism which is
surjective, flat and locally of finite presentation. -/
theorem exists_isAlgebraicStack_locallyLifts (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (U : BigFppfOver B S hS) (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hsurj : ∃ h, HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) (selfSquare f.hom).fst h)
    (hflat : ∃ h, HasRelativeProperty.{u, u, u + 1, u} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) => Space.IsFlat B S hS k.hom)
      (selfSquare f.hom).fst h)
    (hlfp : ∃ h, HasRelativeProperty.{u, u, u + 1, u} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS k.hom) (selfSquare f.hom).fst h) :
    ∃ hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 (LocallyLifts f.hom)),
      ∃ g : schemeStack.{u, w} B S hS U ⟶ fullSubcategoryAlgebraicStack 𝒳 _ hP,
        g ≫ fullSubcategoryInclusion 𝒳 _ hP = f ∧
          AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g ∧ IsSurjective B S hS g ∧
            AlgebraicStacks.IsFlat B S hS g := by
  have h𝒰 := isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U
  have hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 (LocallyLifts f.hom)) :=
    isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces B S hS
      (locallyLiftingInclusion f.hom)
      (isRepresentableByAlgebraicSpaces_locallyLiftingInclusion f.hom h𝒰 hsurj hflat hlfp)
      𝒳.property
  let 𝒵 := fullSubcategoryAlgebraicStack 𝒳 _ hP
  let g : schemeStack.{u, w} B S hS U ⟶ 𝒵 :=
    Bicategory.InducedBicategory.mkHom (toLocallyLifting f.hom)
  have hg : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom :=
    isRepresentableByAlgebraicSpaces_toLocallyLifting f.hom h𝒰
  refine ⟨hP, g, rfl, ?_, ?_, ?_⟩
  · exact (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      (schemeStack.{u, w} B S hS U).property 𝒵.property g.hom).2
      (hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty B S hS _ 𝒵.property
        g.hom hg (hasRelativeProperty_toLocallyLifting f.hom _ h𝒰 hlfp))
  · exact (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS g hg).2
      (hasRelativeProperty_toLocallyLifting f.hom _ h𝒰 hsurj)
  · exact (AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS g).2
      (hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty B S hS _ 𝒵.property
        g.hom hg (hasRelativeProperty_toLocallyLifting f.hom _ h𝒰 hflat))

section Field

variable (f)

/-- The diagonal of the self-intersection of `f`: the tautological object `(z, z, 𝟙)`. -/
abbrev selfSquareDiagonal : 𝒰 ⟶ (selfSquare f).pt :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.lift 𝒰.val.p 𝒰.val.p 𝒳.val.val.p
        (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f) 𝒰.val.p
        (𝟭 _) (𝟭 _) (Functor.id_comp _) (Functor.id_comp _) (Iso.refl _)
        (fun w => IsHomLift.id (f.hom.w_obj w))
      w := TwoFibreProductOver.lift_comp_structureFunctor .. }

/-- The diagonal is a section of the first projection. -/
theorem selfSquareDiagonal_comp_fst : selfSquareDiagonal f ≫ (selfSquare f).fst = 𝟙 𝒰 := rfl

end Field

/-- **The locally lifting substack of a point with values in a field.** Let `F` be the spectrum of
a field and `f : F ⟶ 𝒳` a 1-morphism to an algebraic stack such that the first projection of the
self-intersection `F ×_𝒳 F ⟶ F` is locally of finite presentation. Then the strictly full
subcategory of `𝒳` of the objects lifting locally to `f` is an algebraic stack, and `f` factors
through it by a 1-morphism which is surjective, flat and locally of finite presentation.

The projection of the self-intersection is flat because its target is the spectrum of a field
(`AlgebraicGeometry.Space.isFlat_to_field`), and surjective because the diagonal is a section of
it; so `AlgebraicGeometry.Stack.exists_isAlgebraicStack_locallyLifts` applies. -/
theorem exists_isAlgebraicStack_locallyLifts_of_fieldSpectrum (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (F : FieldSpectrum B S hS) (f : schemeStack.{u, w} B S hS F.base ⟶ 𝒳)
    (hlfp : ∃ h, HasRelativeProperty.{u, u, u + 1, u} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS k.hom) (selfSquare f.hom).fst h) :
    ∃ hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 (LocallyLifts f.hom)),
      ∃ g : schemeStack.{u, w} B S hS F.base ⟶ fullSubcategoryAlgebraicStack 𝒳 _ hP,
        g ≫ fullSubcategoryInclusion 𝒳 _ hP = f ∧
          AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g ∧ IsSurjective B S hS g ∧
            AlgebraicStacks.IsFlat B S hS g := by
  have h𝒰 := isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS F.base
  have hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property h𝒰 f.hom
  obtain ⟨R, hR, ⟨eR⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳.val
    (schemeFibredCategory B S hS F.base) (schemeFibredCategory B S hS F.base) f.hom.hom
    f.hom.hom hf h𝒰
  let eU := PresheafOfCategories.sliceElementsEquivalenceOver F.base
  obtain ⟨hrep, hlfp'⟩ := hlfp
  have hU := isAlgebraicSpace_yoneda B S hS F.base
  have hflat : ∃ h, HasRelativeProperty.{u, u, u + 1, u} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) => Space.IsFlat B S hS k.hom)
      (selfSquare f.hom).fst h :=
    ⟨hrep, (hasRelativeProperty_iff_prop_representingMap B S hS _ _ hrep R (yoneda.obj F.base)
      hR hU eR eU).2 (Space.isFlat_to_field B S hS hR F.isSpec _)⟩
  have hsec := (representingMap_comp B S hS (𝒜 := (schemeStack.{u, w} B S hS F.base).val)
    (ℬ := (selfSquare f.hom).pt) (𝒞 := (schemeStack.{u, w} B S hS F.base).val)
    (yoneda.obj F.base) R (yoneda.obj F.base) eU eR eU
    (selfSquareDiagonal f.hom) (selfSquare f.hom).fst).symm
  rw [selfSquareDiagonal_comp_fst] at hsec
  replace hsec := hsec.trans
    (representingMap_id B S hS (schemeStack.{u, w} B S hS F.base).val (yoneda.obj F.base) eU)
  have hsurj : ∃ h, HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) (selfSquare f.hom).fst h := by
    refine ⟨hrep, (hasRelativeProperty_iff_prop_representingMap B S hS _ _ hrep R
      (yoneda.obj F.base) hR hU eR eU).2 ?_⟩
    intro x
    have h2 := congrFun (congrArg (Space.pointsMap B S hS (yoneda.obj F.base)) hsec) x
    rw [Space.pointsMap_comp, Space.pointsMap_id] at h2
    exact ⟨_, h2⟩
  exact exists_isAlgebraicStack_locallyLifts 𝒳 F.base f hsurj hflat ⟨hrep, hlfp'⟩

/-- **A residual gerbe from a point with values in a field.** Let `F` be the spectrum of a field
and `f : F ⟶ 𝒳` a 1-morphism to an algebraic stack such that the first projection of the
self-intersection `F ×_𝒳 F ⟶ F` is locally of finite presentation. Then the residual gerbe of `𝒳`
at the image of the point of `F` exists, in the form of the specification
`AlgebraicGeometry.Stack.IsResidualGerbeAt` of Stacks 06MT.

The substack of `AlgebraicGeometry.Stack.exists_isAlgebraicStack_locallyLifts_of_fieldSpectrum`
maps fully faithfully to `𝒳`, is covered by `F` surjectively, flatly and locally of finite
presentation, and its points all map to the image of the point of `F`; so its essential image is
the residual gerbe by `AlgebraicGeometry.Stack.exists_isResidualGerbeAt_of_full_of_faithful`. -/
theorem exists_isResidualGerbeAt_of_fieldSpectrum (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (F : FieldSpectrum B S hS) (f : schemeStack.{u, w} B S hS F.base ⟶ 𝒳)
    (hlfp : ∃ h, HasRelativeProperty.{u, u, u + 1, u} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS k.hom) (selfSquare f.hom).fst h)
    (q : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS F.base)) :
    ∃ P : ObjectProperty 𝒳.val.val.obj,
      IsResidualGerbeAt B S hS 𝒳 (AlgebraicStacks.pointsMap B S hS f q) P := by
  obtain ⟨hP, g, hg, hglfp, hgsurj, hgflat⟩ :=
    exists_isAlgebraicStack_locallyLifts_of_fieldSpectrum 𝒳 F f hlfp
  have hfull : (CatFiberedInGroupoids.homFunctor
      (fullSubcategoryInclusion 𝒳 (LocallyLifts f.hom) hP).hom).Full :=
    ObjectProperty.full_ι _
  have hfaith : (CatFiberedInGroupoids.homFunctor
      (fullSubcategoryInclusion 𝒳 (LocallyLifts f.hom) hP).hom).Faithful :=
    ObjectProperty.faithful_ι _
  have hcomp : ∀ q', AlgebraicStacks.pointsMap B S hS
      (fullSubcategoryInclusion 𝒳 (LocallyLifts f.hom) hP)
      (AlgebraicStacks.pointsMap B S hS g q') = AlgebraicStacks.pointsMap B S hS f q' :=
    fun q' => (congrFun (AlgebraicStacks.pointsMap_comp B S hS g
      (fullSubcategoryInclusion 𝒳 (LocallyLifts f.hom) hP)) q').symm.trans
      (congrArg (fun h => AlgebraicStacks.pointsMap B S hS h q') hg)
  have himg : Set.range (AlgebraicStacks.pointsMap B S hS
      (fullSubcategoryInclusion 𝒳 (LocallyLifts f.hom) hP)) =
      {AlgebraicStacks.pointsMap B S hS f q} := by
    ext z
    constructor
    · rintro ⟨z', rfl⟩
      obtain ⟨q', rfl⟩ := hgsurj z'
      rw [hcomp, (subsingleton_points_fieldSpectrumStack.{u, w} B S hS F).elim q' q]
      rfl
    · rintro rfl
      exact ⟨_, hcomp q⟩
  obtain ⟨P, -, hres, -⟩ := exists_isResidualGerbeAt_of_full_of_faithful B S hS 𝒳 _
    (fullSubcategoryInclusion 𝒳 (LocallyLifts f.hom) hP) hfull hfaith
    ⟨F, g, hglfp, hgsurj, hgflat⟩ _ himg
  exact ⟨P, hres⟩

end Assembly

end AlgebraicGeometry.Stack

end
