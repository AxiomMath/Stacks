module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocus
public import StacksFrontier.AlgebraicGeometry.Quot.RelHomFunctorConeComparison
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomFunctor
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomPresheafSliceAlgebraic
public import StacksFrontier.CategoryTheory.Sites.Stack.MorPresheafCartesianLifts

/-!
# The diagonal of `Complexes_{X/B}` (Stacks 0DLG)

## Main results

* `exists_mono_equalizer`: the equalizer of two morphisms from a scheme to an algebraic space is
  a scheme.
* `isomPresheafIsoRelIso`: the isomorphism sheaf of two objects of `Complexes_{X/B}` over the same
  test scheme `T` is the relative Isom functor of their complexes.
* `isULiftAlgebraic_isomPresheaf`: this isomorphism sheaf is a lift of an algebraic presheaf on the
  slice over `T`, granted Stacks 0DLC, part (3), and the vanishing of the negative fibre
  extensions between the two complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace CategoryTheory.Functor

/-- Composing, through a comparison `τ : Lab ≅ Lb ⋙ La`, the identity of `Lb M` with the inverse
of `τ` at `M` followed by an isomorphism `ρ : Lab ≅ L'` gives `ρ` at `M`. -/
theorem fibreComp_symm_app_trans_id {C₀ : Type*} {C₁ : Type*} {C₂ : Type*} [Category* C₀]
    [Category* C₁] [Category* C₂] {La : C₁ ⥤ C₀} {Lb : C₂ ⥤ C₁} {Lab L' : C₂ ⥤ C₀}
    (τ : Lab ≅ Lb ⋙ La) (ρ : Lab ≅ L') (M : C₂) :
    fibreComp τ (τ.symm.app M ≪≫ ρ.app M).hom (𝟙 (Lb.obj M)) = ρ.hom.app M := by
  simp [fibreComp]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : ComplexesSituation B S hS)

attribute [local instance] complexesCategory

/-! ### The equalizer of two morphisms from a scheme to an algebraic space -/

omit D in
/-- **The equalizer of two morphisms from a scheme to an algebraic space is a scheme.**  For
`a, b : U ⟶ Y` with `U` a scheme of the site and `Y` an algebraic space over `S`, there is a
monomorphism `j : Z ⟶ U` of schemes of the site through which a morphism `g : V ⟶ U` factors if
and only if `g ≫ a = g ≫ b`. -/
theorem exists_mono_equalizer {U : BigFppfOver B S hS} {Y : AlgebraicSpaces B S hS}
    (a b : (schemeSpaceFunctor B S hS).obj U ⟶ Y) :
    ∃ (Z : BigFppfOver B S hS) (j : Z ⟶ U), Mono j ∧
      ∀ {V : BigFppfOver B S hS} (g : V ⟶ U),
        (∃ k : V ⟶ Z, k ≫ j = g) ↔
          (schemeSpaceFunctor B S hS).map g ≫ a = (schemeSpaceFunctor B S hS).map g ≫ b := by
  have hd := Y.2.diagonal_representable
  let pair : yoneda.obj U ⟶ Y.1 ⨯ Y.1 := prod.lift a.hom b.hom
  have hpb := hd.isPullback pair
  refine ⟨hd.pullback pair, hd.snd pair, yoneda.mono_of_mono_map hpb.mono_snd_of_mono, ?_⟩
  intro V g
  constructor
  · rintro ⟨k, rfl⟩
    have h1 : yoneda.map (hd.snd pair) ≫ pair = hd.fst pair ≫ diag Y.1 := hpb.w.symm
    have ha := congrArg (· ≫ prod.fst) h1
    have hb := congrArg (· ≫ prod.snd) h1
    simp only [Category.assoc, limit.lift_π, prod.comp_lift, Category.comp_id, BinaryFan.mk_pt,
      BinaryFan.mk_fst, BinaryFan.mk_snd, pair] at ha hb
    rw [Functor.map_comp, Category.assoc, Category.assoc]
    congr 1
    exact ObjectProperty.hom_ext _ (ha.trans hb.symm)
  · intro h
    have h' : yoneda.map g ≫ a.hom = yoneda.map g ≫ b.hom := congrArg (·.hom) h
    have hw : (yoneda.map g ≫ a.hom) ≫ diag Y.1 = yoneda.map g ≫ pair := by
      refine prod.hom_ext ?_ ?_
      · simp [pair]
        rfl
      · simp [pair, h']
        rfl
    refine ⟨yoneda.preimage (hpb.lift _ _ hw), yoneda.map_injective ?_⟩
    rw [Functor.map_comp, Functor.map_preimage, hpb.lift_snd]

/-! ### Functors of points over a scheme, on the slice -/

omit D in
variable (B S hS) in
/-- A scheme `V ⟶ Z` over a scheme `Z` of the site, as a test scheme over the algebraic space `Z`
represents. -/
@[simps]
def overToSchemesOver (Z : BigFppfOver B S hS) :
    Over Z ⥤ SchemesOver ((schemeSpaceFunctor B S hS).obj Z) where
  obj g := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g.hom)
  map {g₁ g₂} h := CostructuredArrow.homMk h.left (by
    simp only [CostructuredArrow.mk_hom_eq_self, ← Functor.map_comp, Over.w h])
  map_id g := by ext; simp
  map_comp h₁ h₂ := by ext; simp

omit D in
/-- **The points over `Z` of an algebraic space over `Z`, on the slice over `Z`, are the fibre
presheaf of Stacks 00Y1.** -/
def overToSchemesOverPointsIso {Z : BigFppfOver B S hS} {H : AlgebraicSpaces B S hS}
    (p : H ⟶ (schemeSpaceFunctor B S hS).obj Z) :
    (overToSchemesOver B S hS Z).op ⋙ spacePointsOver p ≅
      OverShriek.fiber (𝟙 (yoneda.obj Z)) p.hom :=
  NatIso.ofComponents (fun g => Equiv.toIso (Equiv.subtypeEquivRight (fun x => by
    change _ = yonedaEquiv (yoneda.map g.unop.hom) ↔ _ = g.unop.hom
    rw [yonedaEquiv_yoneda_map]
    exact Iff.rfl))) (fun _ => rfl)

omit D in
/-- A functor on the test schemes over a scheme `Z` which is an algebraic space affine and of
finite presentation over `Z` is, on the slice over `Z`, a lift of an algebraic presheaf. -/
theorem isULiftAlgebraicOverSlice_of_isAffineFinitePresentation {Z : BigFppfOver B S hS}
    {R : (SchemesOver ((schemeSpaceFunctor B S hS).obj Z))ᵒᵖ ⥤ Type (u + 1)}
    (hR : IsAffineFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj Z) R) :
    Stack.IsULiftAlgebraicOverSlice.{u, u + 1} ((overToSchemesOver B S hS Z).op ⋙ R) := by
  obtain ⟨H, p, -, -, ⟨e⟩⟩ := hR
  exact ⟨OverShriek.fiber (𝟙 (yoneda.obj Z)) p.hom,
    Stack.IsAlgebraicOverSlice.of_over (Over.mk p.hom) H.2,
    ⟨Functor.isoWhiskerRight (overToSchemesOverPointsIso p).symm uliftFunctor.{u + 1} ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e⟩⟩

/-! ### The morphism to the base of an object of a fibre -/

/-- The morphism to the base `Y` of an object `(T, g, E)` of `Complexes_{X/Y}` lying over a scheme
`U`: the structure morphism `g` of its test scheme, read on `U` through the identification of `U`
with the underlying scheme of the test scheme. -/
def baseMapOver {U : BigFppfOver B S hS} (a : ComplexesObject D) (ha : a.T.left = U) :
    (schemeSpaceFunctor B S hS).obj U ⟶ D.Y :=
  (schemeSpaceFunctor B S hS).map (eqToHom ha.symm) ≫ a.T.hom

/-- **A morphism of `Complexes_{X/Y}` lying over `f` intertwines the morphisms to the base.** -/
theorem map_comp_baseMapOver {V U : BigFppfOver B S hS} {a b : ComplexesObject D}
    (φ : a ⟶ b) (f : V ⟶ U) [(complexesFunctor D).IsHomLift f φ] (ha : a.T.left = V)
    (hb : b.T.left = U) :
    (schemeSpaceFunctor B S hS).map f ≫ D.baseMapOver b hb = D.baseMapOver a ha := by
  have hfac := IsHomLift.fac' (complexesFunctor D) f φ
  have hw := CostructuredArrow.w (φ : ComplexesHom a b).base
  change (φ : ComplexesHom a b).base.left = _ at hfac
  subst ha hb
  change (φ : ComplexesHom a b).base.left = 𝟙 _ ≫ f ≫ 𝟙 _ at hfac
  dsimp only [baseMapOver]
  rw [← hw, hfac]
  simp

/-- The morphism to the base of an object of the fibre of `p : Complexes_{X/Y} ⥤ (Sch/S)_fppf`
over a scheme `U`. -/
abbrev fiberBaseMap {U : BigFppfOver B S hS} (x : (complexesFunctor D).Fiber U) :
    (schemeSpaceFunctor B S hS).obj U ⟶ D.Y :=
  D.baseMapOver x.1 x.2

variable {D}

/-- **The isomorphism sheaf lives over the equalizer of the two base maps.**  If the restrictions
of `x` and `y` along `g : V ⟶ U` are isomorphic in the fibre over `V`, the two morphisms
`U ⟶ Y` agree after composition with `g`. -/
theorem fiberBaseMap_eq_of_hom {U V : BigFppfOver B S hS}
    [(complexesFunctor D).IsFibered] (x y : (complexesFunctor D).Fiber U) (g : V ⟶ U)
    (m : (complexesFunctor D).pullbackFiber x g ⟶ (complexesFunctor D).pullbackFiber y g) :
    (schemeSpaceFunctor B S hS).map g ≫ D.fiberBaseMap x =
      (schemeSpaceFunctor B S hS).map g ≫ D.fiberBaseMap y := by
  let x' := (complexesFunctor D).pullbackFiber x g
  let y' := (complexesFunctor D).pullbackFiber y g
  have hx := D.map_comp_baseMapOver (Functor.IsPreFibered.pullbackMap x.2 g) g x'.2 x.2
  have hy := D.map_comp_baseMapOver (Functor.IsPreFibered.pullbackMap y.2 g) g y'.2 y.2
  have := m.2
  have hm := D.map_comp_baseMapOver m.1 (𝟙 V) x'.2 y'.2
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hm
  rw [hx, hy]
  exact hm.symm

/-! ### The test schemes over a test scheme -/

variable (D) in
/-- A scheme `V ⟶ T.left` over the underlying scheme of a test scheme `T` over `Y`, read as a test
scheme over `Y` through `T`. -/
@[simps]
def sliceTest (T : SchemesOver D.Y) : Over T.left ⥤ SchemesOver D.Y where
  obj g := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g.hom ≫ T.hom)
  map {g₁ g₂} h := CostructuredArrow.homMk h.left (by
    simp only [CostructuredArrow.mk_hom_eq_self, ← Category.assoc, ← Functor.map_comp,
      Over.w h])
  map_id g := by ext; simp
  map_comp h₁ h₂ := by ext; simp

variable (D) in
/-- The morphism of test schemes over `Y` from `V ⟶ T.left ⟶ Y` to `T`. -/
def sliceTestHom (T : SchemesOver D.Y) (g : Over T.left) : (sliceTest D T).obj g ⟶ T :=
  CostructuredArrow.homMk g.hom rfl

/-- The underlying morphism of schemes of `sliceTestHom D T g` is `g.hom`. -/
@[simp]
theorem sliceTestHom_left (T : SchemesOver D.Y) (g : Over T.left) :
    (sliceTestHom D T g).left = g.hom :=
  rfl

/-- The morphisms `sliceTestHom` to `T` commute with the morphisms of test schemes induced by
morphisms over `T.left`. -/
@[reassoc (attr := simp)]
theorem sliceTest_map_comp_sliceTestHom (T : SchemesOver D.Y) {g₁ g₂ : Over T.left}
    (h : g₁ ⟶ g₂) : (sliceTest D T).map h ≫ sliceTestHom D T g₂ = sliceTestHom D T g₁ :=
  CostructuredArrow.hom_ext _ _ (Over.w h)

/-! ### The two models of the base changes over a test scheme -/

variable (D) in
/-- The base change `X_V = X ×_Y V` along `V ⟶ T.left ⟶ Y` is the base change `X_T ×_T V` of the
projection `X_T ⟶ T`: both are fibre products of `X_T ⟶ T` and `V ⟶ T`. -/
def sliceTestSpaceIsoApp (T : SchemesOver D.Y) (g : Over T.left) :
    D.space ((sliceTest D T).obj g) ≅
      overBaseChange (D.projection T) (Over.mk ((schemeSpaceFunctor B S hS).map g.hom)) :=
  (isPullback_baseChangeMap D.f (sliceTestHom D T g)).isoIsPullback _ _
    (AlgebraicSpaces.isPullback_fiberProduct B S hS (D.projection T)
      ((schemeSpaceFunctor B S hS).map g.hom))

/-- Under `sliceTestSpaceIsoApp`, the projection of `X_T ×_T V` to `X_T` is the morphism
`X_V ⟶ X_T`. -/
theorem sliceTestSpaceIsoApp_hom_projection (T : SchemesOver D.Y) (g : Over T.left) :
    (sliceTestSpaceIsoApp D T g).hom ≫
        overProjection (D.projection T) (Over.mk ((schemeSpaceFunctor B S hS).map g.hom)) =
      D.relativeMap (sliceTestHom D T g) :=
  (isPullback_baseChangeMap D.f (sliceTestHom D T g)).isoIsPullback_hom_fst _ _ _

/-- Under `sliceTestSpaceIsoApp`, the projection of `X_T ×_T V` to `V` is the projection
`X_V ⟶ V`. -/
theorem sliceTestSpaceIsoApp_hom_inclusion (T : SchemesOver D.Y) (g : Over T.left) :
    (sliceTestSpaceIsoApp D T g).hom ≫
        overInclusion (D.projection T) (Over.mk ((schemeSpaceFunctor B S hS).map g.hom)) =
      D.projection ((sliceTest D T).obj g) :=
  (isPullback_baseChangeMap D.f (sliceTestHom D T g)).isoIsPullback_hom_snd _ _ _

variable (D) in
/-- The comparison of the two models of the base changes over a test scheme, as a natural
isomorphism of functors on the slice. -/
def sliceTestSpaceIso (T : SchemesOver D.Y) :
    sliceTest D T ⋙ baseChangeOver D.f ⋙ Over.forget D.X ≅
      (overToSchemesOver B S hS T.left ⋙ schemesOverToOver _) ⋙
        overBaseChangeFunctor (D.projection T) ⋙ Over.forget (D.space T) :=
  NatIso.ofComponents (sliceTestSpaceIsoApp D T) <| by
    intro g₁ g₂ h
    refine overBaseChange_hom_ext (D.projection T) ?_ ?_
    · have e1 := sliceTestSpaceIsoApp_hom_projection T g₂
      have e2 := sliceTestSpaceIsoApp_hom_projection T g₁
      have e3 := overBaseChangeMap_comp_projection (D.projection T)
        ((overToSchemesOver B S hS T.left ⋙ schemesOverToOver _).map h)
      have e4 : D.relativeMap ((sliceTest D T).map h) ≫ D.relativeMap (sliceTestHom D T g₂) =
          D.relativeMap (sliceTestHom D T g₁) :=
        (baseChangeMap_comp D.f _ _).symm.trans
          (congrArg (baseChangeMap D.f) (sliceTest_map_comp_sliceTestHom T h))
      simp only [Functor.comp_map]
      exact ((congrArg (D.relativeMap ((sliceTest D T).map h) ≫ ·) e1).trans e4).trans
        ((congrArg ((sliceTestSpaceIsoApp D T g₁).hom ≫ ·) e3).trans e2).symm
    · have e1 := sliceTestSpaceIsoApp_hom_inclusion T g₂
      have e2 := sliceTestSpaceIsoApp_hom_inclusion T g₁
      have e3 := overBaseChangeMap_comp_inclusion (D.projection T)
        ((overToSchemesOver B S hS T.left ⋙ schemesOverToOver _).map h)
      have e4 := baseChangeMap_comp_inclusion D.f ((sliceTest D T).map h)
      simp only [Functor.comp_map]
      exact ((congrArg (D.relativeMap ((sliceTest D T).map h) ≫ ·) e1).trans e4).trans
        (((congrArg ((sliceTestSpaceIsoApp D T g₁).hom ≫ ·) e3).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e2))).symm)

/-! ### The explicit pullbacks of an object over its own test scheme -/

section SameTestScheme

variable (T : SchemesOver D.Y) (E : derivedModules B S hS (D.space T))
  (hE : D.IsRelativelyPerfect T E) (hX : D.HasNoNegativeFibreExt T E)

/-- The pullback of the object `(T, E)` of `Complexes_{X/Y}` along `g : V ⟶ T.left`, as an object
of the fibre over `V`: the object of Stacks 0DLF over the test scheme `V ⟶ T.left ⟶ Y`. -/
abbrev sliceTestObj (g : Over T.left) : ComplexesObject D where
  T := (sliceTest D T).obj g
  E := ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (sliceTestHom D T g))).obj E
  relativelyPerfect := relativelyPerfectBaseChange D _ E hE
  noNegativeFibreExt := D.hasNoNegativeFibreExt_pull _ E hX

/-- `AlgebraicGeometry.Space.ComplexesSituation.sliceTestObj` as an object of the fibre. -/
abbrev sliceTestFiber (g : Over T.left) : (complexesFunctor D).Fiber g.left :=
  ⟨sliceTestObj T E hE hX g, rfl⟩

/-- The morphism from the pullback of `(T, E)` along `g` to `(T, E)`. -/
def sliceTestLift (g : Over T.left) :
    ComplexesHom (sliceTestObj T E hE hX g) (⟨T, E, hE, hX⟩ : ComplexesObject D) where
  base := sliceTestHom D T g
  fibre := 𝟙 _
  isIso_fibre := inferInstance

/-- The morphism `sliceTestLift T E hE hX g` lies over `g.hom`. -/
instance (g : Over T.left) : (complexesFunctor D).IsHomLift g.hom (sliceTestLift T E hE hX g) :=
  IsHomLift.map (complexesFunctor D) (sliceTestLift T E hE hX g)

/-- The pullbacks of `(T, E)` along the schemes over `T.left` form a family of cartesian lifts. -/
def sliceTestLiftFamily :
    Functor.CartesianLiftFamily (complexesFunctor D)
      (⟨⟨T, E, hE, hX⟩, rfl⟩ : (complexesFunctor D).Fiber T.left) :=
  Functor.CartesianLiftFamily.ofStronglyCartesian (sliceTestFiber T E hE hX)
    (sliceTestLift T E hE hX) (fun g =>
      (complexesFunctor_isFiberedInGroupoids D).isStronglyCartesian (sliceTestLift T E hE hX g))

/-- The explicit transition morphism between two pullbacks of `(T, E)`: the morphism of test
schemes, with the composition comparison of the derived pullbacks. -/
def sliceTestTrans {g₁ g₂ : Over T.left} (h : g₁ ⟶ g₂) :
    ComplexesHom (sliceTestObj T E hE hX g₁) (sliceTestObj T E hE hX g₂) where
  base := (sliceTest D T).map h
  fibre := ((D.compComparison _ _).symm.app E ≪≫
    (D.relativeMapComparison (sliceTest_map_comp_sliceTestHom T h)).app E).hom
  isIso_fibre := Iso.isIso_hom _

/-- The explicit transition morphism `sliceTestTrans T E hE hX h` lies over `h.left`. -/
theorem isHomLift_sliceTestTrans {g₁ g₂ : Over T.left} (h : g₁ ⟶ g₂) :
    (complexesFunctor D).IsHomLift h.left
      (sliceTestTrans T E hE hX h : (sliceTestObj T E hE hX g₁) ⟶ _) := by
  have := IsHomLift.map (complexesFunctor D)
    (sliceTestTrans T E hE hX h : (sliceTestObj T E hE hX g₁) ⟶ _)
  rwa [complexesFunctor_map] at this

/-- The explicit transition morphism is compatible with the morphisms to `(T, E)`. -/
theorem sliceTestTrans_comp_lift {g₁ g₂ : Over T.left} (h : g₁ ⟶ g₂) :
    (sliceTestTrans T E hE hX h).comp (sliceTestLift T E hE hX g₂) =
      sliceTestLift T E hE hX g₁ := by
  refine ComplexesHom.ext (sliceTest_map_comp_sliceTestHom T h) ?_
  have h0 : ((sliceTestTrans T E hE hX h).comp (sliceTestLift T E hE hX g₂)).fibre =
      (D.relativeMapComparison (sliceTest_map_comp_sliceTestHom T h)).hom.app E :=
    (ComplexesHom.comp_fibre _ _).trans (Functor.fibreComp_symm_app_trans_id
      (D.compComparison ((sliceTest D T).map h) (sliceTestHom D T g₂))
      (D.relativeMapComparison (sliceTest_map_comp_sliceTestHom T h)) E)
  rw [h0, relativeMapComparison_hom_app]
  exact (eqToHom_trans _ _).trans (eqToHom_refl _ _)

/-- The transition morphisms of the family of pullbacks are the explicit ones. -/
theorem sliceTestLiftFamily_trans {g₁ g₂ : Over T.left} (h : g₁ ⟶ g₂) :
    (sliceTestLiftFamily T E hE hX).trans h = (sliceTestTrans T E hE hX h : _ ⟶ _) :=
  @Functor.CartesianLiftFamily.trans_eq _ _ _ _ _ _ _ (sliceTestLiftFamily T E hE hX) _ _ h
    _ (isHomLift_sliceTestTrans T E hE hX h) (sliceTestTrans_comp_lift T E hE hX h)

variable (D) in
/-- **The cone of base changes over a test scheme.**  For a test scheme `T` over `Y`, the base
changes `X_V` along the test schemes `V ⟶ T.left ⟶ Y`, with the morphisms `X_V ⟶ X_T`. -/
def sliceTestCone (T : SchemesOver D.Y) :
    PullbackData.ConeTo (sliceTest D T ⋙ baseChangeOver D.f ⋙ Over.forget D.X) (D.space T) where
  leg g := D.relativeMap (sliceTestHom D T g)
  w h := (baseChangeMap_comp D.f _ _).symm.trans
    (congrArg (baseChangeMap D.f) (sliceTest_map_comp_sliceTestHom T h))

variable (E' : derivedModules B S hS (D.space T)) (hE' : D.IsRelativelyPerfect T E')
  (hX' : D.HasNoNegativeFibreExt T E')

/-- The morphism of `Complexes_{X/Y}` from the pullback of `(T, E)` along `g` to `(T, E')` with a
given comparison of complexes. -/
def sliceTestHomOf (g : Over T.left)
    (α : (smallEtaleDerivedPullbackData B S hS).relHomObj (sliceTestCone D T) E' E g)
    (hα : IsIso α) : ComplexesHom (sliceTestObj T E hE hX g) ⟨T, E', hE', hX'⟩ where
  base := sliceTestHom D T g
  fibre := α
  isIso_fibre := hα

/-- The morphism `sliceTestHomOf T E hE hX E' hE' hX' g α hα` lies over `g.hom`. -/
theorem isHomLift_sliceTestHomOf (g : Over T.left)
    (α : (smallEtaleDerivedPullbackData B S hS).relHomObj (sliceTestCone D T) E' E g)
    (hα : IsIso α) :
    (complexesFunctor D).IsHomLift g.hom
      (sliceTestHomOf T E hE hX E' hE' hX' g α hα : sliceTestObj T E hE hX g ⟶ _) :=
  IsHomLift.map (complexesFunctor D)
    (sliceTestHomOf T E hE hX E' hE' hX' g α hα : sliceTestObj T E hE hX g ⟶ _)

/-- The morphisms from the pullback of `(T, E)` along `g` to `(T, E')` lying over `g` are the
isomorphisms between the pullbacks of `E'` and `E` to `X_V`. -/
def homOverEquiv (g : Over T.left) :
    ((smallEtaleDerivedPullbackData B S hS).relHomIsoFunctor
        (smallEtaleDerivedPullbackData_isCoherent B S hS) (sliceTestCone D T) E' E).obj (op g) ≃
      ((sliceTestLiftFamily T E hE hX).homOverPresheaf
        (⟨T, E', hE', hX'⟩ : ComplexesObject D)).obj (op g) :=
  Equiv.ofBijective
    (fun α => ⟨(sliceTestHomOf T E hE hX E' hE' hX' g α.1 α.2 : _ ⟶ _),
      isHomLift_sliceTestHomOf T E hE hX E' hE' hX' g α.1 α.2⟩) (by
    constructor
    · rintro ⟨α, hα⟩ ⟨β, hβ⟩ h
      exact Subtype.ext (eq_of_heq (ComplexesHom.mk.inj (congrArg Subtype.val h)).2)
    · rintro ⟨φ, hφ⟩
      have hfac := @IsHomLift.fac' _ _ _ _ (complexesFunctor D) _ _ _ _ g.hom φ hφ
      change (φ : ComplexesHom _ _).base.left = 𝟙 _ ≫ g.hom ≫ 𝟙 _ at hfac
      have hb : (φ : ComplexesHom _ _).base = sliceTestHom D T g :=
        CostructuredArrow.hom_ext _ _ (by rw [hfac, Category.id_comp, Category.comp_id]; rfl)
      obtain ⟨b, f, hf⟩ := φ
      obtain rfl : b = sliceTestHom D T g := hb
      exact ⟨⟨f, hf⟩, rfl⟩)

/-- The restriction of a morphism `sliceTestHomOf` along `h : g₁ ⟶ g₂` is the morphism
`sliceTestHomOf` of the conjugated comparison. -/
theorem sliceTestHomOf_restrict {g₁ g₂ : Over T.left} (h : g₁ ⟶ g₂)
    (α : (smallEtaleDerivedPullbackData B S hS).relHomObj (sliceTestCone D T) E' E g₂)
    (hα : IsIso α) (hα' : IsIso ((smallEtaleDerivedPullbackData B S hS).relHomMap
      (sliceTestCone D T) E' E h α)) :
    (sliceTestHomOf T E hE hX E' hE' hX' g₁
        ((smallEtaleDerivedPullbackData B S hS).relHomMap (sliceTestCone D T) E' E h α) hα' :
          _ ⟶ _) =
      (sliceTestLiftFamily T E hE hX).trans h ≫
        (sliceTestHomOf T E hE hX E' hE' hX' g₂ α hα : _ ⟶ _) := by
  rw [sliceTestLiftFamily_trans]
  refine ComplexesHom.ext (sliceTest_map_comp_sliceTestHom T h).symm ?_
  refine Eq.trans ?_ (ComplexesHom.comp_fibre (sliceTestTrans T E hE hX h)
    (sliceTestHomOf T E hE hX E' hE' hX' g₂ α hα)).symm
  exact PullbackData.eqToHom_comp_conjHom_triangle (smallEtaleDerivedPullbackData B S hS)
    (D.relativeMap ((sliceTest D T).map h)) (D.relativeMap (sliceTestHom D T g₂))
    (baseChangeMap_comp D.f ((sliceTest D T).map h) (sliceTestHom D T g₂))
    (congrArg D.relativeMap (sliceTest_map_comp_sliceTestHom T h)) ((sliceTestCone D T).w h) α

/-- The morphism underlying `homOverEquiv` applied to `α` is `sliceTestHomOf` of `α`. -/
theorem homOverEquiv_apply_coe (g : Over T.left)
    (α : ((smallEtaleDerivedPullbackData B S hS).relHomIsoFunctor
        (smallEtaleDerivedPullbackData_isCoherent B S hS) (sliceTestCone D T) E' E).obj (op g)) :
    (homOverEquiv T E hE hX E' hE' hX' g α).1 =
      (sliceTestHomOf T E hE hX E' hE' hX' g α.1 α.2 : _ ⟶ _) := rfl

/-- Equal comparisons `α = β` give equal morphisms `sliceTestHomOf`. -/
theorem sliceTestHomOf_congr (g : Over T.left)
    {α β : (smallEtaleDerivedPullbackData B S hS).relHomObj (sliceTestCone D T) E' E g}
    (e : α = β) (hα : IsIso α) (hβ : IsIso β) :
    sliceTestHomOf T E hE hX E' hE' hX' g α hα = sliceTestHomOf T E hE hX E' hE' hX' g β hβ := by
  subst e
  rfl

/-- The bijections `homOverEquiv` are natural in the scheme over `T.left`. -/
theorem homOverEquiv_naturality {g₁ g₂ : Over T.left} (h : g₁ ⟶ g₂)
    (α : ((smallEtaleDerivedPullbackData B S hS).relHomIsoFunctor
        (smallEtaleDerivedPullbackData_isCoherent B S hS) (sliceTestCone D T) E' E).obj (op g₂)) :
    homOverEquiv T E hE hX E' hE' hX' g₁
        (((smallEtaleDerivedPullbackData B S hS).relHomIsoFunctor
          (smallEtaleDerivedPullbackData_isCoherent B S hS) (sliceTestCone D T) E' E).map h.op α) =
      ((sliceTestLiftFamily T E hE hX).homOverPresheaf (⟨T, E', hE', hX'⟩ : ComplexesObject D)).map
        h.op (homOverEquiv T E hE hX E' hE' hX' g₂ α) := by
  let X := ((smallEtaleDerivedPullbackData B S hS).relHomIsoFunctor
    (smallEtaleDerivedPullbackData_isCoherent B S hS) (sliceTestCone D T) E' E).map h.op α
  have e := PullbackData.relHomIsoFunctor_map_coe (smallEtaleDerivedPullbackData B S hS)
    (smallEtaleDerivedPullbackData_isCoherent B S hS) (sliceTestCone D T) E' E h α
  have e1 := homOverEquiv_apply_coe T E hE hX E' hE' hX' g₁ X
  have e2 := Functor.CartesianLiftFamily.homOverPresheaf_map_coe (sliceTestLiftFamily T E hE hX)
    (⟨T, E', hE', hX'⟩ : ComplexesObject D) h (homOverEquiv T E hE hX E' hE' hX' g₂ α)
  have e3 := homOverEquiv_apply_coe T E hE hX E' hE' hX' g₂ α
  have e4 := sliceTestHomOf_congr T E hE hX E' hE' hX' g₁ e X.2 (e ▸ X.2)
  have e5 := sliceTestHomOf_restrict T E hE hX E' hE' hX' h α.1 α.2 (e ▸ X.2)
  refine Subtype.ext (e1.trans (e4.trans (e5.trans ?_)))
  rw [e2, e3]

/-- **The presheaf of morphisms out of the pullbacks of `(T, E)` into `(T, E')` lying over the
base is the relative Isom functor of the pullbacks of `E'` and `E`.** -/
def relIsoIsoHomOver :
    (smallEtaleDerivedPullbackData B S hS).relHomIsoFunctor
        (smallEtaleDerivedPullbackData_isCoherent B S hS) (sliceTestCone D T) E' E ≅
      (sliceTestLiftFamily T E hE hX).homOverPresheaf (⟨T, E', hE', hX'⟩ : ComplexesObject D) :=
  NatIso.ofComponents (fun g => (homOverEquiv T E hE hX E' hE' hX' g.unop).toIso) <| by
    rintro ⟨g₂⟩ ⟨g₁⟩ ⟨h⟩
    ext α : 3
    exact homOverEquiv_naturality T E hE hX E' hE' hX' h α

omit E hE hX E' hE' hX' in
/-- The projection `X_T ⟶ T` of a base change is proper. -/
theorem projection_isProper : IsProper B S hS (D.projection T).hom :=
  (isProper_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom) D.proper

omit E hE hX E' hE' hX' in
/-- The projection `X_T ⟶ T` of a base change is of finite presentation. -/
theorem projection_isFinitePresentation : IsFinitePresentation B S hS (D.projection T).hom :=
  (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom) D.finitePresentation

omit E hE hX E' hE' hX' in
/-- The relative Hom functor of two objects perfect relative to `T` whose negative fibre
extensions vanish is, on the slice over `T.left`, a lift of an algebraic presheaf: Stacks 0DLC,
part (3), in the case `W = T`. -/
theorem isULiftAlgebraic_relHom (h0DLC3 : RelativeDerivedHomRepresentableOfFibres B S hS)
    (K L : derivedModules B S hS (D.space T)) (hK : D.IsRelativelyPerfect T K)
    (hL : D.IsRelativelyPerfect T L)
    (hKL : ∀ T₀ : SchemesOver ((schemeSpaceFunctor B S hS).obj T.left),
      Stack.IsFieldObject B S hS T₀.left → HasNoNegativeExtAt (D.projection T) K L T₀) :
    Stack.IsULiftAlgebraicOverSlice.{u, u + 1}
      ((overToSchemesOver B S hS T.left ⋙ schemesOverToOver _).op ⋙
        (smallEtaleDerivedPullbackData B S hS).relHomFunctor
          (smallEtaleDerivedPullbackData_isCoherent B S hS)
          (overBaseChangeCone (D.projection T)) K L) :=
  isULiftAlgebraicOverSlice_of_isAffineFinitePresentation
    (h0DLC3 (D.projection T) (projection_isProper T) (D.projection_isFlat T)
      (projection_isFinitePresentation T) K L hK.1 hL hKL)

/-- **The isomorphism sheaf of two objects over the same test scheme is the relative Isom functor
of their complexes.** -/
def isomPresheafIsoRelIso :
    letI : (complexesFunctor D).IsFibered := (complexesFunctor_isFiberedInGroupoids D).isFibered
    (complexesFunctor D).isomPresheaf
        (⟨⟨T, E, hE, hX⟩, rfl⟩ : (complexesFunctor D).Fiber T.left) ⟨⟨T, E', hE', hX'⟩, rfl⟩ ≅
      (smallEtaleDerivedPullbackData B S hS).relHomIsoFunctor
        (smallEtaleDerivedPullbackData_isCoherent B S hS) (sliceTestCone D T) E' E :=
  letI : (complexesFunctor D).IsFibered := (complexesFunctor_isFiberedInGroupoids D).isFibered
  Stack.isomPresheafIsoMorPresheaf (complexesFunctor D)
      (complexesFunctor_isFiberedInGroupoids D) _ _ ≪≫
    (sliceTestLiftFamily T E hE hX).morPresheafIso
      (⟨⟨T, E', hE', hX'⟩, rfl⟩ : (complexesFunctor D).Fiber T.left) ≪≫
    (relIsoIsoHomOver T E hE hX E' hE' hX').symm

/-- **The isomorphism sheaf of two objects over the same test scheme is a lift of an algebraic
presheaf on the slice**, granted Stacks 0DLC, part (3), in the case `W = T`, and the vanishing of
the negative fibre extensions between the two complexes in both directions. -/
theorem isULiftAlgebraic_isomPresheaf (h0DLC3 : RelativeDerivedHomRepresentableOfFibres B S hS)
    (hEE' : ∀ T₀ : SchemesOver ((schemeSpaceFunctor B S hS).obj T.left),
      Stack.IsFieldObject B S hS T₀.left → HasNoNegativeExtAt (D.projection T) E E' T₀)
    (hE'E : ∀ T₀ : SchemesOver ((schemeSpaceFunctor B S hS).obj T.left),
      Stack.IsFieldObject B S hS T₀.left → HasNoNegativeExtAt (D.projection T) E' E T₀)
    (hEE : ∀ T₀ : SchemesOver ((schemeSpaceFunctor B S hS).obj T.left),
      Stack.IsFieldObject B S hS T₀.left → HasNoNegativeExtAt (D.projection T) E E T₀)
    (hE'E' : ∀ T₀ : SchemesOver ((schemeSpaceFunctor B S hS).obj T.left),
      Stack.IsFieldObject B S hS T₀.left → HasNoNegativeExtAt (D.projection T) E' E' T₀) :
    letI : (complexesFunctor D).IsFibered := (complexesFunctor_isFiberedInGroupoids D).isFibered
    Stack.IsULiftAlgebraicOverSlice.{u, u + 1}
      ((complexesFunctor D).isomPresheaf
        (⟨⟨T, E, hE, hX⟩, rfl⟩ : (complexesFunctor D).Fiber T.left) ⟨⟨T, E', hE', hX'⟩, rfl⟩) := by
  let : (complexesFunctor D).IsFibered := (complexesFunctor_isFiberedInGroupoids D).isFibered
  let Ψ := overToSchemesOver B S hS T.left ⋙ schemesOverToOver _
  let P := smallEtaleDerivedPullbackData B S hS
  let hP := smallEtaleDerivedPullbackData_isCoherent B S hS
  let κ := overBaseChangeCone (D.projection T)
  obtain ⟨hT⟩ := PullbackData.isTerminal_comp_unitPresheaf.{u + 1} Ψ.op
  have hU := Stack.IsULiftAlgebraicOverSlice.of_isTerminal.{u, u + 1} hT
  have hpair : ∀ F G : _ ⥤ Type (u + 1), Stack.IsULiftAlgebraicOverSlice.{u, u + 1} (Ψ.op ⋙ F) →
      Stack.IsULiftAlgebraicOverSlice.{u, u + 1} (Ψ.op ⋙ G) →
      Stack.IsULiftAlgebraicOverSlice.{u, u + 1} (Ψ.op ⋙ PullbackData.pairPresheaf F G) :=
    fun F G hF hG => Stack.IsULiftAlgebraicOverSlice.of_isPullback
      (PullbackData.isPullback_whiskerLeft Ψ.op (PullbackData.isPullback_pairPresheaf F G))
      hF hG hU
  have hA := hpair _ _ (isULiftAlgebraic_relHom T h0DLC3 E' E hE' hE hE'E)
    (isULiftAlgebraic_relHom T h0DLC3 E E' hE hE' hEE')
  have hB := hpair _ _ (isULiftAlgebraic_relHom T h0DLC3 E' E' hE' hE' hE'E')
    (isULiftAlgebraic_relHom T h0DLC3 E E hE hE hEE)
  have hJ := Stack.IsULiftAlgebraicOverSlice.of_isPullback
    (PullbackData.isPullback_whiskerLeft Ψ.op (P.isPullback_relHomIsoFunctor hP κ E' E)) hA hU hB
  refine Stack.IsULiftAlgebraicOverSlice.of_iso ?_ hJ
  exact P.relHomIsoFunctorConeIso hP (sliceTestCone D T) κ Ψ (sliceTestSpaceIso D T)
      (sliceTestSpaceIsoApp_hom_projection T) E' E ≪≫
    (isomPresheafIsoRelIso T E hE hX E' hE' hX').symm

end SameTestScheme

end AlgebraicGeometry.Space.ComplexesSituation

end
