module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesBandParam
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesBandQuasicoherentLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesLiftsHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesPostcompParamComp
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesSelfIntersectionEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesAmbientComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartReadingInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpaceQuasicoherentUniverse

/-!
# The band of the gerbe of smooth lifts, read on the charts of a frame

Let `p : 𝒞 ⟶ W_{spaces,étale}` be the gerbe of smooth lifts of Stacks 0CJP along a first order
thickening, `𝒢` its band (Stacks 0CJY) and `ξ` an object of `𝒞` over an étale open `U` of `W`.
Over every étale scheme chart `T ⟶ U` the object `ξ` restricts to a smooth lift `ξ_T`
(`AlgebraicGeometry.Stack.EtaleSmoothLift.frameAt`, the construction of Stacks 0CJT), so that a
section of `𝒢` over `T` is an automorphism of `ξ_T`, that is a parameter
`Δ^*Ω_{I_T/T'} ⟶ 𝒞_{T/T'}` (Stacks 0CKH), and its datum of Stacks 0CK6 along `ξ_T ⟶ ξ`, read
through Stacks 03LU and 04CQ, is a morphism of the pullbacks to `T` of the two modules
`Δ^*Ω_{I/U'}` and `𝒞_{U/U'}` on `U`. This file shows that this reading identifies the band
module of `AlgebraicGeometry.Stack.EtaleSmoothLift.bandModule`, pulled back to `U`, with the
internal Hom `𝓗om(Δ^*Ω_{I/U'}, 𝒞_{U/U'})`, so that it is quasi-coherent: the identification in
the proof of Stacks 0CKG (2).

## References

* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
* [Stacks Project, Tag 0CJY](https://stacks.math.columbia.edu/tag/0CJY)
* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Functor

universe w v₁ u₁ v₂ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮] {p : 𝒮 ⥤ 𝒞}
  [p.IsFibered] {J : GrothendieckTopology 𝒞} {𝒢 : Sheaf J CommGrpCat.{max v₂ w}}
  (θ : ∀ (U : 𝒞) (x : p.Fiber U),
    (Over.forget U).op ⋙ 𝒢.obj ⋙ forget CommGrpCat.{max v₂ w} ≅
      p.morPresheaf x x ⋙ uliftFunctor.{w, v₂})

/-- **The banding commutes with every morphism of `𝒮`**: for `ψ : y ⟶ x` over `g : V ⟶ U`, the
automorphism of `y` given by the restriction of a section `a` is carried by `ψ` to the
automorphism of `x` given by `a`. -/
theorem fiberInclusion_bandFrame_comp_of_isHomLift [∀ U : 𝒞, IsGroupoid (p.Fiber U)]
    (h₂ : ∀ (U : 𝒞) (ξ ζ : p.Fiber U) (φ : ξ ⟶ ζ) (g : Over U) (a : 𝒢.obj.obj (op g.left)),
      ((θ U ζ).hom.app (op g) a).down =
        pullbackFiberHom (CategoryTheory.inv φ) g.hom ≫ ((θ U ξ).hom.app (op g) a).down ≫
          pullbackFiberHom φ g.hom)
    (h₃ : ∀ (U : 𝒞) (ξ : p.Fiber U) (g : Over U) (a : 𝒢.obj.obj (op g.left)),
      ((θ U ξ).hom.app (op g) a).down =
        (pullbackFiberIdIso (pullbackFiber p ξ g.hom)).inv ≫
          ((θ g.left (pullbackFiber p ξ g.hom)).hom.app (op (Over.mk (𝟙 g.left))) a).down ≫
            (pullbackFiberIdIso (pullbackFiber p ξ g.hom)).hom)
    {U V : 𝒞} (g : V ⟶ U) (x : p.Fiber U) (y : p.Fiber V) (ψ : y.1 ⟶ x.1) [p.IsHomLift g ψ]
    (a : 𝒢.obj.obj (op U)) :
    Fiber.fiberInclusion.map (bandFrame θ V y (𝒢.obj.map g.op a)) ≫ ψ =
      ψ ≫ Fiber.fiberInclusion.map (bandFrame θ U x a) := by
  have : p.IsCartesian g (IsPreFibered.pullbackMap x.2 g) :=
    IsPreFibered.pullbackMap.IsCartesian x.2 g
  let φ : y ⟶ pullbackFiber p x g :=
    Fiber.homMk p V (IsCartesian.map p g (IsPreFibered.pullbackMap x.2 g) ψ)
  have hφ : Fiber.fiberInclusion.map φ ≫ IsPreFibered.pullbackMap x.2 g = ψ :=
    IsCartesian.fac p g (IsPreFibered.pullbackMap x.2 g) ψ
  have hconj := bandFrame_conj θ h₂ V y (pullbackFiber p x g) (asIso φ) (𝒢.obj.map g.op a)
  have key : bandFrame θ V y (𝒢.obj.map g.op a) ≫ φ =
      φ ≫ bandFrame θ V (pullbackFiber p x g) (𝒢.obj.map g.op a) := by
    rw [hconj]
    simp
  have hres : Fiber.fiberInclusion.map
        (bandFrame θ V (pullbackFiber p x g) (𝒢.obj.map g.op a)) ≫
        IsPreFibered.pullbackMap x.2 g =
      IsPreFibered.pullbackMap x.2 g ≫ Fiber.fiberInclusion.map (bandFrame θ U x a) :=
    (congrArg (fun t => Fiber.fiberInclusion.map t ≫ IsPreFibered.pullbackMap x.2 g)
      (bandFrame_res θ h₃ U V g x a)).trans (pullbackFiberHom_fac _ _)
  refine (congrArg (Fiber.fiberInclusion.map (bandFrame θ V y (𝒢.obj.map g.op a)) ≫ ·)
    hφ.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ IsPreFibered.pullbackMap x.2 g)
    ((Fiber.fiberInclusion.map_comp _ _).symm.trans
      ((congrArg Fiber.fiberInclusion.map key).trans (Fiber.fiberInclusion.map_comp _ _)))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (Fiber.fiberInclusion.map φ ≫ ·) hres).trans ?_
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hφ)

end CategoryTheory.Functor

namespace CategoryTheory.Iso

/-- The inverse of `CategoryTheory.Iso.homCongr` is additive. -/
theorem homCongr_symm_add {C : Type*} [Category C] [Preadditive C] {X X₁ Y Y₁ : C}
    (α : X ≅ X₁) (β : Y ≅ Y₁) (f g : X₁ ⟶ Y₁) :
    (α.homCongr β).symm (f + g) = (α.homCongr β).symm f + (α.homCongr β).symm g := by
  simp only [Iso.homCongr_symm, Iso.homCongr_apply, Preadditive.add_comp, Preadditive.comp_add]

/-- A double composite is additive in its last factor. -/
theorem comp_comp_add {C : Type*} [Category C] [Preadditive C] {W X Y Z : C} (a : W ⟶ X)
    (b : X ⟶ Y) (c c' : Y ⟶ Z) : a ≫ b ≫ (c + c') = a ≫ b ≫ c + a ≫ b ≫ c' := by
  simp only [Preadditive.comp_add]

/-- Precomposition with an `eqToHom` is bijective. -/
theorem eqToHom_comp_bijective {C : Type*} [Category C] {X Y Z : C} (h : X = Y) :
    Function.Bijective (fun f : Y ⟶ Z => eqToHom h ≫ f) := by
  subst h
  exact ⟨fun f g hfg => by simpa using hfg, fun g => ⟨g, by simp⟩⟩

/-- Transport of the inverse of `Iso.homCongr` across a heterogeneous equality of morphisms out
of equal objects. -/
theorem homCongr_symm_eq_of_heq {C : Type*} [Category C] {X₀ X₁ X' Y₀ Y : C}
    (α : X₀ ≅ X₁) (β : Y₀ ≅ Y) (h : X₁ = X') (e : X₁ ⟶ Y) (p : X' ⟶ Y) (he : HEq e p) :
    (α.homCongr β).symm e = ((α ≪≫ eqToIso h).homCongr β).symm p := by
  subst h
  rw [eq_of_heq he]
  simp

end CategoryTheory.Iso

namespace AlgebraicGeometry.Stack.EtaleSmoothLift

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

attribute [local instance] isFibered_proj

section Projection

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)

/-- A morphism into a closed subspace is determined by its composite with the inclusion. -/
theorem subspaceInclusion_cancel {X Z : AlgebraicSpaces B S hS}
    {G : Space.ClosedSubspaces B S hS X.1}
    {a b : Z ⟶ ⟨G.1.toFunctor, G.2.1⟩}
    (h : a ≫ Space.subspaceInclusion B S hS X G = b ≫ Space.subspaceInclusion B S hS X G) :
    a = b :=
  ObjectProperty.hom_ext _ ((cancel_mono G.1.ι).1 (congrArg (fun t => t.hom) h))

/-- The inverse of `AlgebraicGeometry.Stack.EtaleSmoothLift.zProjection`: `U ⟶ i(U)`. -/
def zSection (ξ : EtaleSmoothLift B S hS ι hι W x hx) :
    ξ.base.obj.left ⟶ liftsZSpace hι₁ ξ :=
  ObjectProperty.homMk (Subfunctor.lift ξ.inclusion.hom (by
    rintro V _ ⟨v, rfl⟩
    exact ⟨v, rfl⟩))

/-- The composite of `zSection` with the inclusion of `i(U)` into `U'` is the inclusion
`U ⟶ U'`. -/
theorem zSection_comp_subspaceInclusion (ξ : EtaleSmoothLift B S hS ι hι W x hx) :
    zSection hι₁ ξ ≫ Space.subspaceInclusion B S hS ξ.ambient (liftsZ hι₁ ξ) = ξ.inclusion :=
  ObjectProperty.hom_ext _ rfl

/-- `zSection` followed by `zProjection` is the identity of `U`. -/
theorem zSection_comp_zProjection (ξ : EtaleSmoothLift B S hS ι hι W x hx) :
    zSection hι₁ ξ ≫ zProjection hι₁ ξ = 𝟙 _ := by
  have := ξ.mono_inclusion
  rw [← cancel_mono ξ.inclusion, Category.assoc, zProjection_comp_inclusion,
    zSection_comp_subspaceInclusion, Category.id_comp]

/-- `zProjection` followed by `zSection` is the identity of `i(U)`. -/
theorem zProjection_comp_zSection (ξ : EtaleSmoothLift B S hS ι hι W x hx) :
    zProjection hι₁ ξ ≫ zSection hι₁ ξ = 𝟙 _ :=
  subspaceInclusion_cancel (X := ξ.ambient) ((Category.assoc _ _ _).trans
    ((congrArg (zProjection hι₁ ξ ≫ ·) (zSection_comp_subspaceInclusion hι₁ ξ)).trans
      ((zProjection_comp_inclusion hι₁ ξ).trans (Category.id_comp _).symm)))

/-- The projection `i(U) ⟶ U` is an isomorphism, with inverse `zSection`. -/
instance isIso_zProjection (ξ : EtaleSmoothLift B S hS ι hι W x hx) :
    IsIso (zProjection hι₁ ξ) :=
  ⟨zSection hι₁ ξ, zProjection_comp_zSection hι₁ ξ, zSection_comp_zProjection hι₁ ξ⟩

end Projection

section Frames

variable (ξ : EtaleSmoothLift B S hS ι hι W x hx)

/-- The étale open of `W` underlying an étale scheme chart `T` of the base `U` of `ξ`. -/
abbrev frameChartBase (T : Space.SmallEtale B S hS ξ.base.obj.left.1) :
    Space.SpacesEtale B S hS W :=
  (Space.comparisonFunctor B S hS W).obj
    ((Space.smallEtalePostcomp B S hS ξ.base.obj.hom ξ.base.property).obj T)

/-- The étale chart `T ⟶ U`, as a morphism of the spaces-étale site of `W`. -/
def frameChartHom (T : Space.SmallEtale B S hS ξ.base.obj.left.1) :
    frameChartBase ξ T ⟶ ξ.base :=
  ObjectProperty.homMk (Over.homMk (Space.chartToSpace B S hS ξ.base.obj.left T)
    (ObjectProperty.hom_ext _ rfl))

/-- A morphism of étale scheme charts of `U`, as a morphism of the spaces-étale site of `W`. -/
abbrev frameChartMap {T' T : Space.SmallEtale B S hS ξ.base.obj.left.1} (f : T' ⟶ T) :
    frameChartBase ξ T' ⟶ frameChartBase ξ T :=
  (Space.comparisonFunctor B S hS W).map
    ((Space.smallEtalePostcomp B S hS ξ.base.obj.hom ξ.base.property).map f)

/-- A morphism of charts `T' ⟶ T` followed by the chart `T ⟶ U` is the chart `T' ⟶ U`. -/
theorem frameChartMap_comp_frameChartHom {T' T : Space.SmallEtale B S hS ξ.base.obj.left.1}
    (f : T' ⟶ T) : frameChartMap ξ f ≫ frameChartHom ξ T = frameChartHom ξ T' :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext
    (Space.chartMap_comp_chartToSpace B S hS ξ.base.obj.left f))

/-- The closed immersion `U ⟶ U'` restricted along the chart `T ⟶ U` is the base change of an
étale morphism `V' ⟶ U'`. -/
theorem frameData (T : Space.SmallEtale B S hS ξ.base.obj.left.1) :
    ∃ (V' : AlgebraicSpaces B S hS) (j : (frameChartBase ξ T).obj.left ⟶ V')
      (f' : V' ⟶ ξ.ambient), Space.IsEtale B S hS f'.hom ∧
        IsPullback j (frameChartHom ξ T).hom.left f' ξ.inclusion :=
  ξ.isThickeningHom_inclusion.exists_isPullback (frameChartHom ξ T).hom.left
    (Space.SpacesEtale.isEtale_toSpaces_map B S hS W (frameChartHom ξ T))

/-- **The restriction of `ξ` to an étale scheme chart `T` of its base** (Stacks 0CJT). -/
def frameAt (T : Space.SmallEtale B S hS ξ.base.obj.left.1) : EtaleSmoothLift B S hS ι hι W x hx :=
  ofIsPullback ξ (frameChartHom ξ T) (frameData ξ T).choose_spec.choose
    (frameData ξ T).choose_spec.choose_spec.choose
    (frameData ξ T).choose_spec.choose_spec.choose_spec.1
    (frameData ξ T).choose_spec.choose_spec.choose_spec.2

/-- The morphism `ξ_T ⟶ ξ` over the chart. -/
def frameHom (T : Space.SmallEtale B S hS ξ.base.obj.left.1) : frameAt ξ T ⟶ ξ :=
  ofIsPullbackHom ξ (frameChartHom ξ T) (frameData ξ T).choose_spec.choose
    (frameData ξ T).choose_spec.choose_spec.choose
    (frameData ξ T).choose_spec.choose_spec.choose_spec.1
    (frameData ξ T).choose_spec.choose_spec.choose_spec.2

/-- The morphism of bases underlying `ξ_T ⟶ ξ` is the chart `T ⟶ U`. -/
theorem frameHom_base (T : Space.SmallEtale B S hS ξ.base.obj.left.1) :
    Hom.base (frameHom ξ T) = frameChartHom ξ T :=
  rfl

/-- `ξ_T` as an object of the fibre over the chart. -/
abbrev frameFiber (T : Space.SmallEtale B S hS ξ.base.obj.left.1) :
    (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber (frameChartBase ξ T) :=
  ⟨frameAt ξ T, rfl⟩

/-- The comparison `ξ_{T'} ⟶ ξ_T` along a morphism of charts. -/
def frameTransition {T' T : Space.SmallEtale B S hS ξ.base.obj.left.1} (f : T' ⟶ T) :
    frameAt ξ T' ⟶ frameAt ξ T :=
  fillIn (frameHom ξ T) (frameHom ξ T') (frameChartMap ξ f) (frameChartMap_comp_frameChartHom ξ f)

/-- The comparison `ξ_{T'} ⟶ ξ_T` followed by `ξ_T ⟶ ξ` is `ξ_{T'} ⟶ ξ`. -/
theorem frameTransition_comp {T' T : Space.SmallEtale B S hS ξ.base.obj.left.1} (f : T' ⟶ T) :
    frameTransition ξ f ≫ frameHom ξ T = frameHom ξ T' :=
  fillIn_comp _ _ _ _

/-- The comparison `ξ_{T'} ⟶ ξ_T` lies over the morphism of charts `T' ⟶ T`. -/
instance isHomLift_frameTransition {T' T : Space.SmallEtale B S hS ξ.base.obj.left.1}
    (f : T' ⟶ T) :
    (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift (frameChartMap ξ f)
      (frameTransition ξ f) :=
  inferInstanceAs ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift
    ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).map (frameTransition ξ f))
    (frameTransition ξ f))

end Frames

section Reading

attribute [local irreducible] Space.modulePullback Space.smallEtaleRingedSite Space.structureSheaf
  Space.smallEtaleRingedToposHom Space.chartFunctor Space.comparisonFunctor
  Space.modulePullbackCompIso

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)

/-- **The reading of the parameters along a morphism of smooth lifts restricts**, along a
morphism `n` with `n ≫ m = m'` (`AlgebraicGeometry.Stack.EtaleSmoothLift.readParam_comp_eq`,
for a composite given up to equality). -/
theorem readParam_comp {η' η ξ : EtaleSmoothLift B S hS ι hι W x hx} (n : Hom η' η)
    (m : Hom η ξ) (m' : Hom η' ξ) (hm : n.comp m = m') (τ' : Hom η' η') (τ : Hom η η)
    (hτ' : τ'.base = 𝟙 η'.base) (hτ : τ.base = 𝟙 η.base) (h : τ'.comp n = n.comp τ) :
    (Iso.homCongr ((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ m')
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (conormalRestrictionAlongFinal hι₁ m')).symm
        (postcompParamEdge hι₁ m' (autParam hι₁ η' τ' hτ')) =
      Space.QuasiCoherentDescent.restrictForm B S hS (liftsZRestriction hι₁ n) (liftsZMap hι₁ m)
        (liftsZMap hι₁ m') (by subst hm; exact liftsZRestriction_comp_liftsZMap hι₁ n m)
        ((Iso.homCongr ((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ m)
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (conormalRestrictionAlongFinal hι₁ m)).symm
        (postcompParamEdge hι₁ m (autParam hι₁ η τ hτ))) := by
  subst hm
  exact readParam_comp_eq hι₁ m n τ' τ hτ' hτ h

end Reading

section Chart

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)
  (ξ : EtaleSmoothLift B S hS ι hι W x hx)

/-- The identification `U ≅ i(U) ⊂ U'` of the base of `ξ` with its closed image. -/
def frameInclusion :
    ξ.base.obj.left ⟶ ⟨(baseSubspace hι₁ ξ).1.toFunctor, (baseSubspace hι₁ ξ).2.1⟩ :=
  ObjectProperty.homMk (Subfunctor.toRange ξ.inclusion.hom)

/-- The identification `U ≅ i(U)` followed by the inclusion `i(U) ⊂ U'` is the inclusion
`U ⟶ U'`. -/
theorem frameInclusion_comp :
    frameInclusion hι₁ ξ ≫ Space.subspaceInclusion B S hS ξ.ambient (baseSubspace hι₁ ξ) =
      ξ.inclusion :=
  ObjectProperty.hom_ext _ (Subfunctor.toRange_ι _)

/-- The identification `U ≅ i(U)` is étale. -/
theorem isEtale_frameInclusion : Space.IsEtale B S hS (frameInclusion hι₁ ξ).hom :=
  @Space.isEtale_of_isIso B S hS _ _ _ ξ.isThickeningHom_inclusion.1

/-- A morphism out of `U` into a closed image, compatible with the inclusions into the target of
`m`, is the composite of `zSection` with the restriction of `m` to closed images. -/
private theorem zSection_comp_eq_of_comp_inclusion {η' η : EtaleSmoothLift B S hS ι hι W x hx}
    (m : Hom η' η) {G : Space.ClosedSubspaces B S hS η.ambient.1}
    {r : (⟨(liftsZ hι₁ η').1.toFunctor, (liftsZ hι₁ η').2.1⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨G.1.toFunctor, G.2.1⟩}
    (hr : Space.subspaceInclusion B S hS η'.ambient (liftsZ hι₁ η') ≫ m.ambient =
      r ≫ Space.subspaceInclusion B S hS η.ambient G)
    {e : η'.base.obj.left ⟶ ⟨G.1.toFunctor, G.2.1⟩}
    (he : e ≫ Space.subspaceInclusion B S hS η.ambient G = η'.inclusion ≫ m.ambient) :
    zSection hι₁ η' ≫ r = e :=
  subspaceInclusion_cancel (X := η.ambient) (G := G)
    ((Category.assoc _ _ _).trans ((congrArg (zSection hι₁ η' ≫ ·) hr.symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ m.ambient)
        (zSection_comp_subspaceInclusion hι₁ η')).trans he.symm))))

/-- The chart `T ⟶ U`, read on the closed images: `f ∘ (T ≅ j(T)) = (U ≅ i(U)) ∘ φ_T`. -/
theorem frameChart_comp (T : Space.SmallEtale B S hS ξ.base.obj.left.1) :
    zSection hι₁ (frameAt ξ T) ≫ liftsZMap hι₁ (frameHom ξ T) =
      Space.chartToSpace B S hS ξ.base.obj.left T ≫ frameInclusion hι₁ ξ :=
  zSection_comp_eq_of_comp_inclusion hι₁ (frameHom ξ T) (liftsZMap_square hι₁ _)
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (frameInclusion_comp hι₁ ξ)).trans
      (frameHom ξ T).inclusion_comp.symm))

/-- The comparison of the frames over two charts, read on the closed images, is the morphism of
charts. -/
theorem zSection_comp_liftsZRestriction {T' T : Space.SmallEtale B S hS ξ.base.obj.left.1}
    (f : T' ⟶ T) :
    zSection hι₁ (frameAt ξ T') ≫ liftsZRestriction hι₁ (frameTransition ξ f) =
      Space.chartMap B S hS ξ.base.obj.left f ≫ zSection hι₁ (frameAt ξ T) :=
  zSection_comp_eq_of_comp_inclusion hι₁ (frameTransition ξ f)
    (liftsZRestriction_square hι₁ _)
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (zSection_comp_subspaceInclusion hι₁ _)).trans
      (frameTransition ξ f).inclusion_comp.symm))

end Chart

section BandReading

attribute [local irreducible] Space.modulePullback Space.smallEtaleRingedToposHom
  Space.modulePullbackCompIso

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)
  (ξ : EtaleSmoothLift B S hS ι hι W x hx)
variable {𝒢 : Sheaf (Space.SpacesEtale.topology B S hS W) CommGrpCat.{u + 1}}
  (θ : ∀ (U : Space.SpacesEtale B S hS W)
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U),
    (Over.forget U).op ⋙ 𝒢.obj ⋙ forget CommGrpCat.{u + 1} ≅
      (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).morPresheaf ζ ζ ⋙
        uliftFunctor.{u + 1, u + 1})

/-- **The reading of the band on the charts of a frame is natural** (Stacks 0CKG (2)): the reading
over `T'` of the restriction of a section along a morphism of charts `f : T' ⟶ T` is the restricted
reading of Stacks 03LU, along `f`, of its reading over `T`. -/
theorem bandRead_naturality (h₂ : ∀ (U : Space.SpacesEtale B S hS W)
    (ζ ζ' : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (φ : ζ ⟶ ζ') (g : Over U)
    (a : 𝒢.obj.obj (op g.left)),
      haveI : ∀ U, IsGroupoid ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) :=
        isFiberedInGroupoids_proj.fiber_isGroupoid
      ((θ U ζ').hom.app (op g) a).down =
        Functor.pullbackFiberHom (CategoryTheory.inv φ) g.hom ≫
          ((θ U ζ).hom.app (op g) a).down ≫ Functor.pullbackFiberHom φ g.hom)
    (h₃ : ∀ (U : Space.SpacesEtale B S hS W)
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (g : Over U)
    (a : 𝒢.obj.obj (op g.left)),
      ((θ U ζ).hom.app (op g) a).down =
        (Functor.pullbackFiberIdIso (Functor.pullbackFiber
          (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) ζ g.hom)).inv ≫
          ((θ g.left (Functor.pullbackFiber (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) ζ
            g.hom)).hom.app (op (Over.mk (𝟙 g.left))) a).down ≫
          (Functor.pullbackFiberIdIso (Functor.pullbackFiber
            (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) ζ g.hom)).hom)
    {T' T : Space.SmallEtale B S hS ξ.base.obj.left.1} (f : T' ⟶ T)
    (a : 𝒢.obj.obj (op (frameChartBase ξ T))) :
    Space.QuasiCoherentDescent.restrictForm B S hS (zSection hι₁ (frameAt ξ T'))
      (liftsZMap hι₁ (frameHom ξ T'))
      (Space.chartToSpace B S hS ξ.base.obj.left T' ≫ frameInclusion hι₁ ξ)
      (frameChart_comp hι₁ ξ T')
      ((Iso.homCongr ((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (frameHom ξ T'))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (conormalRestrictionAlongFinal hι₁ (frameHom ξ T'))).symm
        (postcompParamEdge hι₁ (frameHom ξ T') (autParam hι₁ (frameAt ξ T')
          (Functor.Fiber.fiberInclusion.map (Functor.bandFrame θ (frameChartBase ξ T')
          (frameFiber ξ T') (𝒢.obj.map (frameChartMap ξ f).op a))) (base_eq_id_of_fiber _)))) =
      Space.QuasiCoherentDescent.restrictForm B S hS (Space.chartMap B S hS ξ.base.obj.left f)
        (Space.chartToSpace B S hS ξ.base.obj.left T ≫ frameInclusion hι₁ ξ)
        (Space.chartToSpace B S hS ξ.base.obj.left T' ≫ frameInclusion hι₁ ξ)
        (by rw [← Category.assoc, Space.chartMap_comp_chartToSpace])
        (Space.QuasiCoherentDescent.restrictForm B S hS (zSection hι₁ (frameAt ξ T))
      (liftsZMap hι₁ (frameHom ξ T))
      (Space.chartToSpace B S hS ξ.base.obj.left T ≫ frameInclusion hι₁ ξ)
      (frameChart_comp hι₁ ξ T)
      ((Iso.homCongr ((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (frameHom ξ T))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (conormalRestrictionAlongFinal hι₁ (frameHom ξ T))).symm
        (postcompParamEdge hι₁ (frameHom ξ T) (autParam hι₁ (frameAt ξ T)
          (Functor.Fiber.fiberInclusion.map (Functor.bandFrame θ (frameChartBase ξ T)
          (frameFiber ξ T) (a))) (base_eq_id_of_fiber _))))) := by
  have : ∀ U, IsGroupoid ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) :=
    isFiberedInGroupoids_proj.fiber_isGroupoid
  have := isHomLift_frameTransition ξ f
  have hcomm := Functor.fiberInclusion_bandFrame_comp_of_isHomLift θ h₂ h₃ (frameChartMap ξ f)
    (frameFiber ξ T) (frameFiber ξ T') (frameTransition ξ f) a
  have hst₁ : (zSection hι₁ (frameAt ξ T') ≫ liftsZRestriction hι₁ (frameTransition ξ f)) ≫
      liftsZMap hι₁ (frameHom ξ T) =
        Space.chartToSpace B S hS ξ.base.obj.left T' ≫ frameInclusion hι₁ ξ :=
    (Category.assoc _ _ _).trans ((congrArg (zSection hι₁ (frameAt ξ T') ≫ ·)
      ((liftsZRestriction_comp_liftsZMap hι₁ (frameTransition ξ f) (frameHom ξ T)).trans
        (congrArg (liftsZMap hι₁) (frameTransition_comp ξ f)))).trans (frameChart_comp hι₁ ξ T'))
  have hst₂ : (Space.chartMap B S hS ξ.base.obj.left f ≫ zSection hι₁ (frameAt ξ T)) ≫
      liftsZMap hι₁ (frameHom ξ T) =
        Space.chartToSpace B S hS ξ.base.obj.left T' ≫ frameInclusion hι₁ ξ :=
    (Category.assoc _ _ _).trans ((congrArg (Space.chartMap B S hS ξ.base.obj.left f ≫ ·)
      (frameChart_comp hι₁ ξ T)).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ frameInclusion hι₁ ξ)
          (Space.chartMap_comp_chartToSpace B S hS ξ.base.obj.left f))))
  rw [readParam_comp hι₁ (frameTransition ξ f) (frameHom ξ T) (frameHom ξ T')
    (frameTransition_comp ξ f) _ _ (base_eq_id_of_fiber _) (base_eq_id_of_fiber _) hcomm]
  refine (Space.QuasiCoherentDescent.restrictForm_comp B S hS _ _ _ _ _ _ rfl _ _ hst₁ _).trans ?_
  refine (Space.restrictForm_congr_left B S hS (zSection_comp_liftsZRestriction hι₁ ξ f) _ hst₁
    hst₂ _).trans ?_
  exact (Space.QuasiCoherentDescent.restrictForm_comp B S hS _ _ _ _ (frameChart_comp hι₁ ξ T) _
    rfl _ _ hst₂ _).symm

/-- **The datum of Stacks 0CK6 along `Φ_m` is additive.** -/
theorem postcompParam_add {η ξ : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom η ξ)
    (θ₁ θ₂ : LiftsActingGroup hι₁ η) :
    postcompParam hι₁ m (θ₁ + θ₂) = postcompParam hι₁ m θ₁ + postcompParam hι₁ m θ₂ := by
  unfold postcompParam Space.postcompDerivationDatum
  exact Iso.comp_comp_add _ _ _ _

/-- The datum of Stacks 0CK6 along `m`, read over the edge, is a bijection on parameters. -/
theorem postcompParamEdge_bijective {η ξ : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom η ξ) :
    Function.Bijective (postcompParamEdge hι₁ m) :=
  (Iso.eqToHom_comp_bijective _).comp (postcompParam_bijective m hι₁)

/-- The composite of `liftsZMap` with `diagonalRestriction`, with its middle object the closed
subspace `liftsW₀`, is `liftsEdge` followed by `selfIntersectionMapRestriction`. -/
theorem liftsZMap_comp_diagonalRestriction_liftsW₀ {η : EtaleSmoothLift B S hS ι hι W x hx}
    (m : Hom η ξ) :
    @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _
        ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩ (liftsZMap hι₁ m)
        (diagonalRestriction hι₁ ξ) =
      @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (liftsEdge hι₁ η)
        (selfIntersectionMapRestriction hι₁ m) :=
  liftsZMap_comp_diagonalRestriction hι₁ m

/-- The reading of the datum of Stacks 0CK6 over the edge, as a reading of the datum itself. -/
theorem readEdge_eq {η : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom η ξ)
    (θ : LiftsActingGroup hι₁ η) :
    (Iso.homCongr ((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (conormalRestrictionAlongFinal hι₁ (m))).symm
              (postcompParamEdge hι₁ m θ) =
      ((((((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) ≪≫ eqToIso (congrArg (fun e =>
              (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ
              (m)))).homCongr
        (conormalRestrictionAlongFinal hι₁ (m))).symm) (postcompParam hι₁ m θ) :=
  Iso.homCongr_symm_eq_of_heq _ _ _ _ _ (heq_postcompParamEdge hι₁ m θ)

/-- The reading of the datum of Stacks 0CK6 along `m` is additive in the parameter. -/
theorem readEdge_add {η : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom η ξ)
    (θ₁ θ₂ : LiftsActingGroup hι₁ η) :
    ((((((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) ≪≫ eqToIso (congrArg (fun e =>
              (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ
              (m)))).homCongr
        (conormalRestrictionAlongFinal hι₁ (m))).symm) (postcompParam hι₁ m (θ₁ + θ₂)) =
      ((((((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) ≪≫ eqToIso (congrArg (fun e =>
              (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ
              (m)))).homCongr
        (conormalRestrictionAlongFinal hι₁ (m))).symm) (postcompParam hι₁ m θ₁) +
          ((((((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) ≪≫ eqToIso (congrArg (fun e =>
              (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ
              (m)))).homCongr
        (conormalRestrictionAlongFinal hι₁ (m))).symm) (postcompParam hι₁ m θ₂) :=
  (congrArg _ (postcompParam_add hι₁ m θ₁ θ₂)).trans (Iso.homCongr_symm_add _ _ _ _)

/-- The reading of the datum of Stacks 0CK6 along `m` commutes with multiplication by a global
function on the closed image of the base of `η`. -/
theorem readEdge_smul {η : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom η ξ)
    (θ : LiftsActingGroup hι₁ η) (t : Space.globalFunctions' B S hS (liftsZSpace hι₁ η).1) :
    ((((((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) ≪≫ eqToIso (congrArg (fun e =>
              (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ
              (m)))).homCongr
        (conormalRestrictionAlongFinal hι₁ (m))).symm) (postcompParam hι₁ m (θ ≫
          Space.globalFunctionsSmul B S hS (X := liftsZSpace hι₁ η) t
          (Space.conormalModule B S hS η.ambient (liftsZ hι₁ η)))) =
      ((((((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) ≪≫ eqToIso (congrArg (fun e =>
              (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ
              (m)))).homCongr
        (conormalRestrictionAlongFinal hι₁ (m))).symm) (postcompParam hι₁ m θ) ≫
          Space.globalFunctionsSmul B S hS t _ :=
  (congrArg _ (postcompParam_comp_globalFunctionsSmul hι₁ m θ t)).trans
    (Space.homCongr_symm_comp_globalFunctionsSmul B S hS _ _ _ t)

/-- The parameter of an automorphism depends only on the automorphism, not on the proof that it
lies over the identity. -/
theorem autParam_eq_of_eq {η : EtaleSmoothLift B S hS ι hι W x hx} {σ σ' : Hom η η}
    (h : σ = σ') (hσ : σ.base = 𝟙 η.base) (hσ' : σ'.base = 𝟙 η.base) :
    autParam hι₁ η σ hσ = autParam hι₁ η σ' hσ' := by
  subst h
  rfl

/-- **The reading of the band on a chart, in the datum form.** -/
theorem bandRead_eq (T : Space.SmallEtale B S hS ξ.base.obj.left.1)
    (a : 𝒢.obj.obj (op (frameChartBase ξ T))) :
    Space.QuasiCoherentDescent.restrictForm B S hS (zSection hι₁ (frameAt ξ T))
      (liftsZMap hι₁ (frameHom ξ T))
      (Space.chartToSpace B S hS ξ.base.obj.left T ≫ frameInclusion hι₁ ξ)
      (frameChart_comp hι₁ ξ T)
      ((Iso.homCongr ((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (frameHom ξ T))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (conormalRestrictionAlongFinal hι₁ (frameHom ξ T))).symm
        (postcompParamEdge hι₁ (frameHom ξ T) (autParam hι₁ (frameAt ξ T)
          (Functor.Fiber.fiberInclusion.map (Functor.bandFrame θ (frameChartBase ξ T)
          (frameFiber ξ T) (a))) (base_eq_id_of_fiber _)))) =
      Space.QuasiCoherentDescent.restrictForm B S hS (zSection hι₁ (frameAt ξ T))
      (liftsZMap hι₁ (frameHom ξ T))
      (Space.chartToSpace B S hS ξ.base.obj.left T ≫ frameInclusion hι₁ ξ)
      (frameChart_comp hι₁ ξ T)
      (((((((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (frameHom ξ T))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) ≪≫ eqToIso (congrArg (fun e =>
              (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ
              (frameHom ξ T)))).homCongr
        (conormalRestrictionAlongFinal hι₁ (frameHom ξ T))).symm) (postcompParam hι₁ (frameHom ξ T)
          (autParam hι₁ (frameAt ξ T) (Functor.Fiber.fiberInclusion.map (Functor.bandFrame θ
          (frameChartBase ξ T) (frameFiber ξ T) (a))) (base_eq_id_of_fiber _)))) :=
  congrArg (fun t => Space.QuasiCoherentDescent.restrictForm B S hS (zSection hι₁ (frameAt ξ T))
      (liftsZMap hι₁ (frameHom ξ T))
      (Space.chartToSpace B S hS ξ.base.obj.left T ≫ frameInclusion hι₁ ξ)
      (frameChart_comp hι₁ ξ T) t) (readEdge_eq hι₁ ξ (frameHom ξ T) _)

/-- **The reading of the band, in the datum form, is natural.** -/
theorem bandRead₂_naturality (h₂ : ∀ (U : Space.SpacesEtale B S hS W)
    (ζ ζ' : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (φ : ζ ⟶ ζ') (g : Over U)
    (a : 𝒢.obj.obj (op g.left)),
      haveI : ∀ U, IsGroupoid ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) :=
        isFiberedInGroupoids_proj.fiber_isGroupoid
      ((θ U ζ').hom.app (op g) a).down =
        Functor.pullbackFiberHom (CategoryTheory.inv φ) g.hom ≫
          ((θ U ζ).hom.app (op g) a).down ≫ Functor.pullbackFiberHom φ g.hom)
    (h₃ : ∀ (U : Space.SpacesEtale B S hS W)
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (g : Over U)
    (a : 𝒢.obj.obj (op g.left)),
      ((θ U ζ).hom.app (op g) a).down =
        (Functor.pullbackFiberIdIso (Functor.pullbackFiber
          (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) ζ g.hom)).inv ≫
          ((θ g.left (Functor.pullbackFiber (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) ζ
            g.hom)).hom.app (op (Over.mk (𝟙 g.left))) a).down ≫
          (Functor.pullbackFiberIdIso (Functor.pullbackFiber
            (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) ζ g.hom)).hom)
    {T' T : Space.SmallEtale B S hS ξ.base.obj.left.1} (f : T' ⟶ T)
    (a : 𝒢.obj.obj (op (frameChartBase ξ T))) :
    Space.QuasiCoherentDescent.restrictForm B S hS (zSection hι₁ (frameAt ξ T'))
      (liftsZMap hι₁ (frameHom ξ T'))
      (Space.chartToSpace B S hS ξ.base.obj.left T' ≫ frameInclusion hι₁ ξ)
      (frameChart_comp hι₁ ξ T')
      (((((((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (frameHom ξ T'))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) ≪≫ eqToIso (congrArg (fun e =>
              (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ
              (frameHom ξ T')))).homCongr
        (conormalRestrictionAlongFinal hι₁ (frameHom ξ T'))).symm) (postcompParam hι₁
          (frameHom ξ T') (autParam hι₁ (frameAt ξ T') (Functor.Fiber.fiberInclusion.map
          (Functor.bandFrame θ (frameChartBase ξ T') (frameFiber ξ T') (𝒢.obj.map
          (frameChartMap ξ f).op a))) (base_eq_id_of_fiber _)))) =
      Space.QuasiCoherentDescent.restrictForm B S hS (Space.chartMap B S hS ξ.base.obj.left f)
        (Space.chartToSpace B S hS ξ.base.obj.left T ≫ frameInclusion hι₁ ξ)
        (Space.chartToSpace B S hS ξ.base.obj.left T' ≫ frameInclusion hι₁ ξ)
        (by rw [← Category.assoc, Space.chartMap_comp_chartToSpace])
        (Space.QuasiCoherentDescent.restrictForm B S hS (zSection hι₁ (frameAt ξ T))
      (liftsZMap hι₁ (frameHom ξ T))
      (Space.chartToSpace B S hS ξ.base.obj.left T ≫ frameInclusion hι₁ ξ)
      (frameChart_comp hι₁ ξ T)
      (((((((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (frameHom ξ T))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) ≪≫ eqToIso (congrArg (fun e =>
              (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ
              (frameHom ξ T)))).homCongr
        (conormalRestrictionAlongFinal hι₁ (frameHom ξ T))).symm) (postcompParam hι₁ (frameHom ξ T)
          (autParam hι₁ (frameAt ξ T) (Functor.Fiber.fiberInclusion.map (Functor.bandFrame θ
          (frameChartBase ξ T) (frameFiber ξ T) (a))) (base_eq_id_of_fiber _))))) :=
  (bandRead_eq hι₁ ξ θ T' _).symm.trans ((bandRead_naturality hι₁ ξ θ h₂ h₃ f a).trans
    (congrArg _ (bandRead_eq hι₁ ξ θ T a)))

include θ in
/-- The parameter of the banding of a product is the sum of the parameters. -/
theorem paramOf_bandFrame_mul (h₁ : ∀ (U : Space.SpacesEtale B S hS W)
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (g : Over U)
    (a b : 𝒢.obj.obj (op g.left)),
      ((θ U ζ).hom.app (op g) (a * b)).down =
        ((θ U ζ).hom.app (op g) a).down ≫ ((θ U ζ).hom.app (op g) b).down)
    {U : Space.SpacesEtale B S hS W}
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (a b : 𝒢.obj.obj (op U)) :
    paramOf hι₁ (Functor.bandFrame θ U ζ (a * b)) =
      paramOf hι₁ (Functor.bandFrame θ U ζ a) + paramOf hι₁ (Functor.bandFrame θ U ζ b) :=
  (congrArg (paramOf hι₁) (Functor.bandFrame_mul θ h₁ U ζ a b)).trans (paramOf_comp hι₁ _ _)

end BandReading

end AlgebraicGeometry.Stack.EtaleSmoothLift
