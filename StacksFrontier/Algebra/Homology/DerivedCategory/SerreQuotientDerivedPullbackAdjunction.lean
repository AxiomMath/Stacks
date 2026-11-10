module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedSerreInducedTStructure
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedCategoryBIsoClosedInstance
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactAdjunctionUnboundedSource
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.CategoryTheory.Functor.Derived.TotalLeftDerivedAtLeftOrthogonal
public import StacksFrontier.CategoryTheory.Triangulated.VerdierRightLocalizingHom

/-!
# Derived pullback and derived direct image on Verdier quotients by a weak Serre part

Let `A₁`, `A₂` be abelian categories and let `𝒮ᵢ ⊆ 𝒜ᵢ` be weak Serre subcategories of `Aᵢ`.
Write `Dᵢ = D_{𝒜ᵢ}(Aᵢ)` and `Dᵢ/Nᵢ` for its Verdier quotient by `Nᵢ = D_{𝒮ᵢ}(Aᵢ)`, and `Dᵢ⁺/Nᵢ⁺`
for the bounded below version. This file is the formal content of **Stacks 07BE**, with
`Aᵢ` the fppf modules of `𝒴`, resp. `𝒳`, `𝒜ᵢ = LQCoh^fbc` and `𝒮ᵢ = Parasitic ∩ LQCoh^fbc`.

Let `L ⊣ R` be an adjunction `A₁ ⇄ A₂` with `L` exact. Then:

1. if `L` carries `𝒜₁` into `𝒜₂`, the exact functor `L : D(A₁) ⥤ D(A₂)` restricts to
   `D₁ ⥤ D₂` (`DerivedCategoryB.derivedCategoryBMap`), commuting with the inclusions;
2. if every object of `D₁` is the target of a morphism of the inverted class out of an object
   left orthogonal to `N₁` (the colocalization of **Stacks 07BA**), every functor out of `D₁`,
   in particular `D₁ ⥤ D₂ ⥤ D₂/N₂`, is left derivable with respect to the localization
   `D₁ ⥤ D₁/N₁`, and its total left derived functor is
   `Lq : D₁/N₁ ⥤ D₂/N₂` (`DerivedCategoryB.serreQuotientDerivedPullback`);
3. if moreover `R⁺` carries `D₂⁺` into `D₁⁺` and `N₂⁺` into `N₁⁺`, so that it induces
   `Rq : D₂⁺/N₂⁺ ⥤ D₁⁺/N₁⁺` (`DerivedCategoryB.serreQuotientPushforwardPlus`), then
   `Hom_{D₂/N₂}(Lq A, B) ≃ Hom_{D₁/N₁}(A, Rq B)` for `A` in `D₁/N₁` and `B` in `D₂⁺/N₂⁺`, the
   latter read in the unbounded quotients (`DerivedCategoryB.serreQuotientHomEquiv`), naturally
   in both variables.

## Main definitions

* `DerivedCategoryB.serreQuotientW`, `DerivedCategoryB.serreQuotientWPlus`: the classes of
  morphisms inverted by `Dᵢ ⥤ Dᵢ/Nᵢ` and `Dᵢ⁺ ⥤ Dᵢ⁺/Nᵢ⁺`; these are the shapes of
  `AlgebraicGeometry.Stack.derivedQuasicoherentWUnivLE` and
  `AlgebraicGeometry.Stack.derivedQuasicoherentWPlus`.
* `DerivedCategoryB.serreQuotientPlusToSerreQuotient`: `D⁺/N⁺ ⥤ D/N`.
* `DerivedCategoryB.derivedCategoryBMap`, `DerivedCategoryB.serreQuotientDerivedPullback`,
  `DerivedCategoryB.serreQuotientPushforwardPlus`: the three functors above.
* `DerivedCategoryB.serreQuotientHomEquiv`: the adjointness.

## Implementation notes

The proof is the source's. For `A = q(E)` choose the colocalization `E' ⟶ E`; then
`Lq(A) = q(L E')` because `E'` computes the left derived functor
(`CategoryTheory.ObjectProperty.isIso_totalLeftDerivedCounit_app_of_leftOrthogonal`), and
`Hom_{D₁/N₁}(q E', q M) = Hom(E', M)` because `E'` is left orthogonal to `N₁`. On the other side
`L E'` is left orthogonal to `N₂⁺`, since `Hom(L E', P) = Hom(E', R⁺ P)`
(`CategoryTheory.Adjunction.unboundedHomEquiv`) and `R⁺P` lies in `N₁`; and `D₂⁺` is right
`N₂`-localizing inside `D₂`, by truncation, so
`Hom_{D₂/N₂}(q(L E'), q H) = Hom(L E', H)` for `H` bounded below
(`CategoryTheory.ObjectProperty.map_bijective_of_leftOrthogonal_inf`). This replaces the
colimit over `H ⟶ H'` of the source by the cofinality of bounded below `H'` that right
localizing expresses.

The bijection is built as `a ↦ Lq(a) ≫ c_B` for a natural transformation
`c : Rq ⋙ j₁ ⋙ Lq ⟶ j₂` (`DerivedCategoryB.serreQuotientCounit`), so that it is natural in both
variables by construction and only its bijectivity has to be checked.

## References

* [Stacks Project, Tag 05S9](https://stacks.math.columbia.edu/tag/05S9)
* [Stacks Project, Tag 05SV](https://stacks.math.columbia.edu/tag/05SV)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 07BA](https://stacks.math.columbia.edu/tag/07BA)
* [Stacks Project, Tag 07BC](https://stacks.math.columbia.edu/tag/07BC)
* [Stacks Project, Tag 07BE](https://stacks.math.columbia.edu/tag/07BE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

universe v₁ u₁ w₁ v₂ u₂ w₂

namespace DerivedCategoryB

open DerivedCategory ObjectProperty WeakSerre

section Single

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  (𝒜 𝒮 : ObjectProperty A)

/-- The class of morphisms of `D_𝒜(A)` whose cone, taken in `D(A)`, lies in `D_𝒮(A)`: the
morphisms the Verdier quotient `D_𝒜(A)/D_𝒮(A)` inverts. -/
abbrev serreQuotientW : MorphismProperty (derivedCategoryB 𝒜).FullSubcategory :=
  MorphismProperty.inverseImage (derivedCategoryB 𝒮).trW (derivedCategoryB 𝒜).ι

/-- The subcategory `D⁺_𝒜(A)` of `D⁺(A)`. -/
abbrev derivedCategoryBInPlus : ObjectProperty (DerivedCategory.Plus A) :=
  (derivedCategoryB 𝒜).inverseImage DerivedCategory.Plus.ι

/-- The class of morphisms of `D⁺_𝒜(A)` whose cone, taken in `D⁺(A)`, lies in `D⁺_𝒮(A)`. -/
abbrev serreQuotientWPlus : MorphismProperty (derivedCategoryBInPlus 𝒜).FullSubcategory :=
  MorphismProperty.inverseImage (derivedCategoryBInPlus 𝒮).trW (derivedCategoryBInPlus 𝒜).ι

/-- `D_𝒮(A)` read inside `D_𝒜(A)`. -/
abbrev serreQuotientKernel : ObjectProperty (derivedCategoryB 𝒜).FullSubcategory :=
  (derivedCategoryB 𝒮).inverseImage (derivedCategoryB 𝒜).ι

/-- The bounded below objects of `D_𝒜(A)`. -/
abbrev boundedBelowPart : ObjectProperty (derivedCategoryB 𝒜).FullSubcategory :=
  (TStructure.t : TStructure (DerivedCategory A)).plus.inverseImage (derivedCategoryB 𝒜).ι

/-- The inclusion `D⁺_𝒜(A) ⥤ D_𝒜(A)`. -/
def plusInclusion :
    (derivedCategoryBInPlus 𝒜).FullSubcategory ⥤ (derivedCategoryB 𝒜).FullSubcategory :=
  (derivedCategoryB 𝒜).lift ((derivedCategoryBInPlus 𝒜).ι ⋙ DerivedCategory.Plus.ι)
    fun K => K.property

variable [𝒮.IsClosedUnderIsomorphisms]

/-- The inclusion `D⁺_𝒜(A) ⥤ D_𝒜(A)` followed by the quotient functor inverts what
`D⁺_𝒜(A) ⥤ D⁺_𝒜(A)/D⁺_𝒮(A)` inverts. -/
theorem plusInclusion_inverts :
    (serreQuotientWPlus 𝒜 𝒮).IsInvertedBy
      (plusInclusion 𝒜 ⋙ (serreQuotientW 𝒜 𝒮).Q) := fun _ _ _ hs =>
  MorphismProperty.Q_inverts _ _
    (((derivedCategoryB 𝒮).inverseImage_trW_iff DerivedCategory.Plus.ι _).1 hs)

/-- The functor `D⁺_𝒜(A)/D⁺_𝒮(A) ⥤ D_𝒜(A)/D_𝒮(A)` induced by the inclusion. -/
def serreQuotientPlusToSerreQuotient :
    (serreQuotientWPlus 𝒜 𝒮).Localization ⥤ (serreQuotientW 𝒜 𝒮).Localization :=
  Localization.Construction.lift _ (plusInclusion_inverts 𝒜 𝒮)

/-- The functor `serreQuotientPlusToSerreQuotient` composed with the localization functor of
`D⁺_𝒜(A)` is the inclusion followed by the localization functor of `D_𝒜(A)`. -/
theorem serreQuotientPlusToSerreQuotient_fac :
    (serreQuotientWPlus 𝒜 𝒮).Q ⋙ serreQuotientPlusToSerreQuotient 𝒜 𝒮 =
      plusInclusion 𝒜 ⋙ (serreQuotientW 𝒜 𝒮).Q :=
  Localization.Construction.fac _ _

variable [𝒜.IsWeakSerreClass] [𝒮.IsWeakSerreClass]

omit [𝒮.IsWeakSerreClass] in
/-- The inverted class is the class attached to the triangulated subcategory `D_𝒮(A)` of the
triangulated category `D_𝒜(A)`. -/
theorem serreQuotientW_eq_trW : serreQuotientW 𝒜 𝒮 = (serreQuotientKernel 𝒜 𝒮).trW := by
  ext X Y f
  exact ((derivedCategoryB 𝒮).inverseImage_trW_iff (derivedCategoryB 𝒜).ι f).symm

/-- **The bounded below part of `D_𝒜(A)` is right `D_𝒮(A)`-localizing**: a morphism `X ⟶ Y`
with `X` in `D_𝒮(A)` and `Y` in `D^{≥ n}` factors through `τ_{≥ n} X`, which lies in
`D_𝒜(A) ∩ D_𝒮(A) ∩ D⁺(A)`. -/
instance isVerdierRightLocalizing_boundedBelowPart :
    (boundedBelowPart 𝒜).IsVerdierRightLocalizing (serreQuotientKernel 𝒜 𝒮) where
  fac {X Y} f hX hY := by
    obtain ⟨n, hn⟩ := hY
    have : TStructure.t.IsGE Y.obj n := hn
    let Z : (derivedCategoryB 𝒜).FullSubcategory :=
      ⟨(TStructure.t.truncGE n).obj X.obj, derivedCategoryB_truncGE_obj 𝒜
        (isWeakSerre_of_isWeakSerreClass 𝒜) n X.obj X.property⟩
    exact ⟨Z, ObjectProperty.homMk ((TStructure.t.truncGEπ n).app X.obj),
      ObjectProperty.homMk (TStructure.t.descTruncGE f.hom n),
      ⟨n, (inferInstance : TStructure.t.IsGE ((TStructure.t.truncGE n).obj X.obj) n)⟩,
      derivedCategoryB_truncGE_obj 𝒮 (isWeakSerre_of_isWeakSerreClass 𝒮) n X.obj hX,
      ObjectProperty.hom_ext _ (TStructure.t.π_descTruncGE f.hom n)⟩

/-- The colocalization hypothesis of **Stacks 07BA**: every object of `D_𝒜(A)` receives a
morphism of the inverted class from an object left orthogonal to `D_𝒮(A)`. -/
def HasColocalizations : Prop :=
  ∀ K : (derivedCategoryB 𝒜).FullSubcategory, ∃ (K' : (derivedCategoryB 𝒜).FullSubcategory)
    (s : K' ⟶ K), serreQuotientW 𝒜 𝒮 s ∧ (serreQuotientKernel 𝒜 𝒮).leftOrthogonal K'

variable {𝒜 𝒮}

/-- **Every functor out of `D_𝒜(A)` is left derivable** with respect to the Verdier quotient by
`D_𝒮(A)`, in the sense of **Stacks 05SV**, once the colocalization of **Stacks 07BA** exists. -/
theorem isLeftDerivable_of_hasColocalizations {H : Type*} [Category* H]
    (F : (derivedCategoryB 𝒜).FullSubcategory ⥤ H) (hres : HasColocalizations 𝒜 𝒮) :
    F.IsLeftDerivable (serreQuotientW 𝒜 𝒮) := by
  rw [serreQuotientW_eq_trW]
  exact (serreQuotientKernel 𝒜 𝒮).isLeftDerivable_trW_of_leftOrthogonal_resolutions F
    fun K => by
      obtain ⟨K', s, hs, hK'⟩ := hres K
      exact ⟨K', s, serreQuotientW_eq_trW 𝒜 𝒮 ▸ hs, hK'⟩

/-- Every functor out of `D_𝒜(A)` has a pointwise left derived functor with respect to the
Verdier quotient by `D_𝒮(A)`, once the colocalization of **Stacks 07BA** exists. -/
theorem hasPointwiseLeftDerivedFunctor_of_hasColocalizations {H : Type*} [Category* H]
    (F : (derivedCategoryB 𝒜).FullSubcategory ⥤ H) (hres : HasColocalizations 𝒜 𝒮) :
    F.HasPointwiseLeftDerivedFunctor (serreQuotientW 𝒜 𝒮) := by
  rw [serreQuotientW_eq_trW]
  exact (serreQuotientKernel 𝒜 𝒮).hasPointwiseLeftDerivedFunctor_of_leftOrthogonal_resolutions
    F fun K => by
      obtain ⟨K', s, hs, hK'⟩ := hres K
      exact ⟨K', s, serreQuotientW_eq_trW 𝒜 𝒮 ▸ hs, hK'⟩

end Single

/-- On the image of a morphism under the localization functor, the functor lifted through
`CategoryTheory.Localization.Construction` acts as the functor it was lifted from. -/
theorem constructionLift_map_Q {C D : Type*} [Category* C] [Category* D] {W : MorphismProperty C}
    (G : C ⥤ D) (hG : W.IsInvertedBy G) {X Y : C} (f : X ⟶ Y) :
    (Localization.Construction.lift G hG).map (W.Q.map f) = G.map f :=
  (rfl : _ = 𝟙 _ ≫ G.map f).trans (Category.id_comp _)

section Pullback

variable {A₁ : Type u₁} [Category.{v₁} A₁] [Abelian A₁] [HasDerivedCategory.{w₁} A₁]
  {A₂ : Type u₂} [Category.{v₂} A₂] [Abelian A₂] [HasDerivedCategory.{w₂} A₂]
  {𝒜₁ 𝒮₁ : ObjectProperty A₁} {𝒜₂ 𝒮₂ : ObjectProperty A₂}
  (L : A₁ ⥤ A₂) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- **The exact functor `L` restricted to `D_{𝒜₁}(A₁) ⥤ D_{𝒜₂}(A₂)`**, when `L` carries `𝒜₁`
into `𝒜₂`: since `L` is exact the cohomology objects of `L K` are the images of those of `K`. -/
def derivedCategoryBMap [𝒜₂.IsClosedUnderIsomorphisms] (hL : ∀ M, 𝒜₁ M → 𝒜₂ (L.obj M)) :
    (derivedCategoryB 𝒜₁).FullSubcategory ⥤ (derivedCategoryB 𝒜₂).FullSubcategory :=
  (derivedCategoryB 𝒜₂).lift ((derivedCategoryB 𝒜₁).ι ⋙ L.mapDerivedCategory) fun K n =>
    𝒜₂.prop_of_iso ((L.mapDerivedCategoryHomologyIso n).app K.obj).symm (hL _ (K.property n))

/-- The restriction of `L` commutes with the inclusions into the derived categories. -/
theorem derivedCategoryBMap_comp_ι [𝒜₂.IsClosedUnderIsomorphisms]
    (hL : ∀ M, 𝒜₁ M → 𝒜₂ (L.obj M)) :
    derivedCategoryBMap L hL ⋙ (derivedCategoryB 𝒜₂).ι =
      (derivedCategoryB 𝒜₁).ι ⋙ L.mapDerivedCategory :=
  rfl

variable [𝒜₁.IsWeakSerreClass] [𝒮₁.IsWeakSerreClass] [𝒜₂.IsWeakSerreClass]
  (hL : ∀ M, 𝒜₁ M → 𝒜₂ (L.obj M)) (hres : HasColocalizations 𝒜₁ 𝒮₁)

/-- The composite `D_{𝒜₁}(A₁) ⥤ D_{𝒜₂}(A₂) ⥤ D_{𝒜₂}(A₂)/D_{𝒮₂}(A₂)` whose left derived functor is
`DerivedCategoryB.serreQuotientDerivedPullback`. -/
abbrev serreQuotientPullbackComp :
    (derivedCategoryB 𝒜₁).FullSubcategory ⥤ (serreQuotientW 𝒜₂ 𝒮₂).Localization :=
  derivedCategoryBMap L hL ⋙ (serreQuotientW 𝒜₂ 𝒮₂).Q

include hres in
/-- The functor `serreQuotientPullbackComp` has a pointwise left derived functor with respect to
`serreQuotientW 𝒜₁ 𝒮₁`. -/
theorem hasPointwiseLeftDerivedFunctor_serreQuotientPullbackComp :
    (serreQuotientPullbackComp (𝒮₂ := 𝒮₂) L hL).HasPointwiseLeftDerivedFunctor
      (serreQuotientW 𝒜₁ 𝒮₁) :=
  hasPointwiseLeftDerivedFunctor_of_hasColocalizations _ hres

include hres in
/-- The functor `serreQuotientPullbackComp` has a left derived functor with respect to
`serreQuotientW 𝒜₁ 𝒮₁`. -/
theorem hasLeftDerivedFunctor_serreQuotientPullbackComp :
    (serreQuotientPullbackComp (𝒮₂ := 𝒮₂) L hL).HasLeftDerivedFunctor
      (serreQuotientW 𝒜₁ 𝒮₁) :=
  have := hasPointwiseLeftDerivedFunctor_serreQuotientPullbackComp (𝒮₂ := 𝒮₂) L hL hres
  Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _

/-- **The derived pullback `Lq : D_{𝒜₁}(A₁)/D_{𝒮₁}(A₁) ⥤ D_{𝒜₂}(A₂)/D_{𝒮₂}(A₂)`**: the total left
derived functor of `D_{𝒜₁}(A₁) ⥤ D_{𝒜₂}(A₂) ⥤ D_{𝒜₂}(A₂)/D_{𝒮₂}(A₂)` with respect to the
quotient functor of `D_{𝒜₁}(A₁)`. -/
def serreQuotientDerivedPullback :
    (serreQuotientW 𝒜₁ 𝒮₁).Localization ⥤ (serreQuotientW 𝒜₂ 𝒮₂).Localization :=
  have := hasLeftDerivedFunctor_serreQuotientPullbackComp (𝒮₂ := 𝒮₂) L hL hres
  (serreQuotientPullbackComp L hL).totalLeftDerived (serreQuotientW 𝒜₁ 𝒮₁).Q
    (serreQuotientW 𝒜₁ 𝒮₁)

/-- The counit `q(L E) ⟵ Lq(q E)` of the left derived functor. -/
def serreQuotientDerivedPullbackCounit :
    (serreQuotientW 𝒜₁ 𝒮₁).Q ⋙ serreQuotientDerivedPullback (𝒮₂ := 𝒮₂) L hL hres ⟶
      serreQuotientPullbackComp L hL :=
  have := hasLeftDerivedFunctor_serreQuotientPullbackComp (𝒮₂ := 𝒮₂) L hL hres
  (serreQuotientPullbackComp L hL).totalLeftDerivedCounit (serreQuotientW 𝒜₁ 𝒮₁).Q
    (serreQuotientW 𝒜₁ 𝒮₁)

/-- `serreQuotientDerivedPullback` together with `serreQuotientDerivedPullbackCounit` is a left
derived functor of `serreQuotientPullbackComp` with respect to `serreQuotientW 𝒜₁ 𝒮₁`. -/
instance isLeftDerivedFunctor_serreQuotientDerivedPullback :
    (serreQuotientDerivedPullback (𝒮₂ := 𝒮₂) L hL hres).IsLeftDerivedFunctor
    (serreQuotientDerivedPullbackCounit L hL hres) (serreQuotientW 𝒜₁ 𝒮₁) := by
  have := hasLeftDerivedFunctor_serreQuotientPullbackComp (𝒮₂ := 𝒮₂) L hL hres
  dsimp only [serreQuotientDerivedPullback, serreQuotientDerivedPullbackCounit]
  infer_instance

/-- The localization functor of `D_𝒜(A)` is a localization at the class attached to the
triangulated subcategory `D_𝒮(A)`. -/
theorem isLocalization_serreQuotientW_Q_trW {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] (𝒜 𝒮 : ObjectProperty A) [𝒜.IsWeakSerreClass]
    [𝒮.IsWeakSerreClass] :
    (serreQuotientW 𝒜 𝒮).Q.IsLocalization (serreQuotientKernel 𝒜 𝒮).trW := by
  rw [← serreQuotientW_eq_trW]
  infer_instance

/-- **An object left orthogonal to `D_{𝒮₁}(A₁)` computes the derived pullback**: the counit
`Lq(q E') ⟶ q(L E')` is an isomorphism. -/
theorem isIso_serreQuotientDerivedPullbackCounit_app {E' : (derivedCategoryB 𝒜₁).FullSubcategory}
    (hE' : (serreQuotientKernel 𝒜₁ 𝒮₁).leftOrthogonal E') :
    IsIso ((serreQuotientDerivedPullbackCounit (𝒮₂ := 𝒮₂) L hL hres).app E') := by
  have key : ∀ W' : MorphismProperty (derivedCategoryB 𝒜₁).FullSubcategory,
      W' = (serreQuotientKernel 𝒜₁ 𝒮₁).trW →
      ∀ [(serreQuotientPullbackComp (𝒮₂ := 𝒮₂) L hL).HasPointwiseLeftDerivedFunctor W']
        [(serreQuotientW 𝒜₁ 𝒮₁).Q.IsLocalization W'],
      have := (serreQuotientPullbackComp (𝒮₂ := 𝒮₂) L
        hL).hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor W'
      IsIso (((serreQuotientPullbackComp (𝒮₂ := 𝒮₂) L hL).totalLeftDerivedCounit
        (serreQuotientW 𝒜₁ 𝒮₁).Q W').app E') := by
    rintro _ rfl _ _
    exact (serreQuotientKernel 𝒜₁ 𝒮₁).isIso_totalLeftDerivedCounit_app_of_leftOrthogonal _ _ hE'
  have := hasPointwiseLeftDerivedFunctor_serreQuotientPullbackComp (𝒮₂ := 𝒮₂) L hL hres
  exact key _ (serreQuotientW_eq_trW 𝒜₁ 𝒮₁)

end Pullback

section Adjunction

variable {A₁ : Type u₁} [Category.{v₁} A₁] [Abelian A₁] [HasDerivedCategory.{w₁} A₁]
  {A₂ : Type u₂} [Category.{v₂} A₂] [Abelian A₂] [HasDerivedCategory.{w₂} A₂]
  [EnoughInjectives A₁] [EnoughInjectives A₂]
  {𝒜₁ 𝒮₁ : ObjectProperty A₁} {𝒜₂ 𝒮₂ : ObjectProperty A₂}
  [𝒜₁.IsWeakSerreClass] [𝒮₁.IsWeakSerreClass] [𝒜₂.IsWeakSerreClass] [𝒮₂.IsWeakSerreClass]
  {L : A₁ ⥤ A₂} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  {R : A₂ ⥤ A₁} [R.Additive] (adj : L ⊣ R)
  (hL : ∀ M, 𝒜₁ M → 𝒜₂ (L.obj M)) (hres : HasColocalizations 𝒜₁ 𝒮₁)
  (hR𝒜 : ∀ K : DerivedCategory.Plus A₂, derivedCategoryB 𝒜₂ K.obj →
    derivedCategoryB 𝒜₁ (R.rightDerivedFunctorPlus.obj K).obj)
  (hR𝒮 : ∀ K : DerivedCategory.Plus A₂, derivedCategoryB 𝒮₂ K.obj →
    derivedCategoryB 𝒮₁ (R.rightDerivedFunctorPlus.obj K).obj)

variable (R) in
/-- **The total right derived functor `R⁺` restricted to `D⁺_{𝒜₂}(A₂) ⥤ D⁺_{𝒜₁}(A₁)`**. -/
def derivedCategoryBInPlusMap :
    (derivedCategoryBInPlus 𝒜₂).FullSubcategory ⥤ (derivedCategoryBInPlus 𝒜₁).FullSubcategory :=
  (derivedCategoryBInPlus 𝒜₁).lift ((derivedCategoryBInPlus 𝒜₂).ι ⋙ R.rightDerivedFunctorPlus)
    fun K => hR𝒜 K.obj K.property

include hR𝒮 in
omit [EnoughInjectives A₁] [𝒜₁.IsWeakSerreClass] [𝒮₁.IsWeakSerreClass] [𝒜₂.IsWeakSerreClass]
    [𝒮₂.IsWeakSerreClass] in
/-- `R⁺` followed by the quotient functor inverts the class of `D⁺_{𝒜₂}(A₂) ⥤ D⁺/N⁺`: being
triangulated, `R⁺` carries a cone to a cone, and it carries `D⁺_{𝒮₂}` into `D⁺_{𝒮₁}`. -/
theorem derivedCategoryBInPlusMap_inverts :
    (serreQuotientWPlus 𝒜₂ 𝒮₂).IsInvertedBy
      (derivedCategoryBInPlusMap R hR𝒜 ⋙ (serreQuotientWPlus 𝒜₁ 𝒮₁).Q) := by
  rintro X Y s ⟨Z, g, h, hT, hZ⟩
  apply MorphismProperty.Q_inverts
  let := R.commShiftRightDerivedFunctorPlus
  have := R.isTriangulated_rightDerivedFunctorPlus
  exact ⟨_, _, _, R.rightDerivedFunctorPlus.map_distinguished _ hT, hR𝒮 _ hZ⟩

variable (R) in
/-- **The derived direct image `Rq : D⁺_{𝒜₂}(A₂)/D⁺_{𝒮₂}(A₂) ⥤ D⁺_{𝒜₁}(A₁)/D⁺_{𝒮₁}(A₁)`**
induced by `R⁺` on the bounded below Verdier quotients. -/
def serreQuotientPushforwardPlus :
    (serreQuotientWPlus 𝒜₂ 𝒮₂).Localization ⥤ (serreQuotientWPlus 𝒜₁ 𝒮₁).Localization :=
  Localization.Construction.lift _ (derivedCategoryBInPlusMap_inverts hR𝒜 hR𝒮)

/-- The counit of `L⁺ ⊣ R⁺`, read on `D⁺_{𝒜₂}(A₂)` as a natural transformation
`incl ∘ R⁺ ⋙ L ⟶ incl`. -/
def derivedCategoryBPlusCounit :
    derivedCategoryBInPlusMap R hR𝒜 ⋙ plusInclusion 𝒜₁ ⋙ derivedCategoryBMap L hL ⟶
      plusInclusion 𝒜₂ where
  app H := ObjectProperty.homMk (adj.plusCounit H.obj)
  naturality _ _ f := ObjectProperty.hom_ext _ (adj.plusCounit_naturality f.hom)

/-- The natural transformation on representatives underlying
`DerivedCategoryB.serreQuotientCounit`. -/
def serreQuotientCounitAux :
    (serreQuotientWPlus 𝒜₂ 𝒮₂).Q ⋙ serreQuotientPushforwardPlus R hR𝒜 hR𝒮 ⋙
        serreQuotientPlusToSerreQuotient 𝒜₁ 𝒮₁ ⋙ serreQuotientDerivedPullback L hL hres ⟶
      (serreQuotientWPlus 𝒜₂ 𝒮₂).Q ⋙ serreQuotientPlusToSerreQuotient 𝒜₂ 𝒮₂ where
  app H := (serreQuotientDerivedPullbackCounit L hL hres).app
      ((plusInclusion 𝒜₁).obj ((derivedCategoryBInPlusMap R hR𝒜).obj H)) ≫
    (serreQuotientW 𝒜₂ 𝒮₂).Q.map ((derivedCategoryBPlusCounit adj hL hR𝒜).app H)
  naturality H H' f := by
    have h₁₂ : (serreQuotientPlusToSerreQuotient 𝒜₁ 𝒮₁).map
        ((serreQuotientPushforwardPlus R hR𝒜 hR𝒮).map ((serreQuotientWPlus 𝒜₂ 𝒮₂).Q.map f)) =
        (serreQuotientW 𝒜₁ 𝒮₁).Q.map ((plusInclusion 𝒜₁).map
          ((derivedCategoryBInPlusMap R hR𝒜).map f)) :=
      (congrArg (serreQuotientPlusToSerreQuotient 𝒜₁ 𝒮₁).map
        (constructionLift_map_Q _ _ f)).trans (constructionLift_map_Q _ _ _)
    have h₃ : (serreQuotientPlusToSerreQuotient 𝒜₂ 𝒮₂).map ((serreQuotientWPlus 𝒜₂ 𝒮₂).Q.map f) =
        (serreQuotientW 𝒜₂ 𝒮₂).Q.map ((plusInclusion 𝒜₂).map f) :=
      constructionLift_map_Q _ _ f
    have h₄ := (serreQuotientDerivedPullbackCounit (𝒮₂ := 𝒮₂) L hL hres).naturality
      ((plusInclusion 𝒜₁).map ((derivedCategoryBInPlusMap R hR𝒜).map f))
    have h₅ := (derivedCategoryBPlusCounit adj hL hR𝒜).naturality f
    dsimp only [Functor.comp_map, Functor.comp_obj] at h₄ h₅ ⊢
    rw [h₁₂, h₃]
    have k : (serreQuotientDerivedPullback L hL hres).map ((serreQuotientW 𝒜₁ 𝒮₁).Q.map
        ((plusInclusion 𝒜₁).map ((derivedCategoryBInPlusMap R hR𝒜).map f))) ≫
        (serreQuotientDerivedPullbackCounit L hL hres).app
          ((plusInclusion 𝒜₁).obj ((derivedCategoryBInPlusMap R hR𝒜).obj H')) ≫
        (serreQuotientW 𝒜₂ 𝒮₂).Q.map ((derivedCategoryBPlusCounit adj hL hR𝒜).app H') =
        ((serreQuotientDerivedPullbackCounit L hL hres).app
          ((plusInclusion 𝒜₁).obj ((derivedCategoryBInPlusMap R hR𝒜).obj H)) ≫
        (serreQuotientW 𝒜₂ 𝒮₂).Q.map ((derivedCategoryBPlusCounit adj hL hR𝒜).app H)) ≫
          (serreQuotientW 𝒜₂ 𝒮₂).Q.map ((plusInclusion 𝒜₂).map f) := by
      rw [reassoc_of% h₄, ← Functor.map_comp, Category.assoc, ← Functor.map_comp, h₅]
    exact k

/-- **The counit `c : Rq ⋙ j₁ ⋙ Lq ⟶ j₂`** through which the adjointness of **Stacks 07BE** is
defined: on `B = q⁺(H)` it is `Lq(q(R⁺H)) ⟶ q(L R⁺ H) ⟶ q(H)`, the counit of the derived functor
followed by the counit of `L⁺ ⊣ R⁺`. -/
def serreQuotientCounit :
    serreQuotientPushforwardPlus R hR𝒜 hR𝒮 ⋙ serreQuotientPlusToSerreQuotient 𝒜₁ 𝒮₁ ⋙
        serreQuotientDerivedPullback L hL hres ⟶
      serreQuotientPlusToSerreQuotient 𝒜₂ 𝒮₂ :=
  Localization.Construction.natTransExtension (serreQuotientCounitAux adj hL hres hR𝒜 hR𝒮)

/-- On the image `q⁺(H)` of an object `H`, the counit `serreQuotientCounit` is
`serreQuotientCounitAux` at `H`. -/
theorem serreQuotientCounit_app_Q (H : (derivedCategoryBInPlus 𝒜₂).FullSubcategory) :
    (serreQuotientCounit adj hL hres hR𝒜 hR𝒮).app ((serreQuotientWPlus 𝒜₂ 𝒮₂).Q.obj H) =
      (serreQuotientCounitAux adj hL hres hR𝒜 hR𝒮).app H :=
  Localization.Construction.NatTransExtension.app_eq _ H

/-- The map underlying `DerivedCategoryB.serreQuotientHomEquiv`: `a ↦ Lq(a) ≫ c_B`. -/
def serreQuotientHomMap (A : (serreQuotientW 𝒜₁ 𝒮₁).Localization)
    (B : (serreQuotientWPlus 𝒜₂ 𝒮₂).Localization)
    (a : A ⟶ (serreQuotientPlusToSerreQuotient 𝒜₁ 𝒮₁).obj
      ((serreQuotientPushforwardPlus R hR𝒜 hR𝒮).obj B)) :
    (serreQuotientDerivedPullback L hL hres).obj A ⟶
      (serreQuotientPlusToSerreQuotient 𝒜₂ 𝒮₂).obj B :=
  (serreQuotientDerivedPullback L hL hres).map a ≫
    (serreQuotientCounit adj hL hres hR𝒜 hR𝒮).app B

/-- Precomposition with an isomorphism is bijective. -/
private theorem bijective_comp_left_of_isIso {C : Type*} [Category* C] {X Y Z : C} (f : X ⟶ Y)
    [IsIso f] : Function.Bijective fun g : Y ⟶ Z => f ≫ g :=
  ⟨fun _ _ h => (cancel_epi _).1 h, fun g => ⟨inv f ≫ g, by simp⟩⟩

/-- Morphisms of a full subcategory are morphisms of the ambient category. -/
theorem bijective_homMk {C : Type*} [Category* C] {P : ObjectProperty C} (X Y : P.FullSubcategory) :
    Function.Bijective (ObjectProperty.homMk : (X.obj ⟶ Y.obj) → (X ⟶ Y)) :=
  ⟨fun _ _ h => congrArg InducedCategory.Hom.hom h,
    fun g => ⟨g.hom, ObjectProperty.hom_ext _ rfl⟩⟩

include adj hR𝒜 hR𝒮 in
omit [𝒜₁.IsWeakSerreClass] [𝒮₁.IsWeakSerreClass] [𝒮₂.IsWeakSerreClass] in
/-- **`L E'` is left orthogonal to the bounded below part of `D_{𝒮₂}(A₂)`** as soon as `E'` is
left orthogonal to `D_{𝒮₁}(A₁)`: `Hom(L E', P) = Hom(E', R⁺ P)` and `R⁺ P` lies in
`D_{𝒮₁}(A₁)`. -/
theorem leftOrthogonal_derivedCategoryBMap_obj {E' : (derivedCategoryB 𝒜₁).FullSubcategory}
    (hE' : (serreQuotientKernel 𝒜₁ 𝒮₁).leftOrthogonal E') :
    (boundedBelowPart 𝒜₂ ⊓ serreQuotientKernel 𝒜₂ 𝒮₂).leftOrthogonal
      ((derivedCategoryBMap L hL).obj E') := by
  intro P g hP
  let P' : DerivedCategory.Plus A₂ := ⟨P.obj, hP.1⟩
  let Y : (derivedCategoryB 𝒜₁).FullSubcategory :=
    ⟨(R.rightDerivedFunctorPlus.obj P').obj, hR𝒜 P' P.property⟩
  have h0 : (ObjectProperty.homMk (adj.unboundedHomEquiv E'.obj P' g.hom) : E' ⟶ Y) = 0 :=
    hE' _ (hR𝒮 P' hP.2)
  have h1 : adj.unboundedHomEquiv E'.obj P' g.hom = 0 := congrArg InducedCategory.Hom.hom h0
  apply ObjectProperty.hom_ext
  have h2 := (adj.unboundedHomEquiv E'.obj P').symm_apply_apply g.hom
  rw [h1, Adjunction.unboundedHomEquiv_symm_apply, Functor.map_zero, zero_comp] at h2
  exact h2.symm

/-- **The adjointness on representatives.** For `E'` left orthogonal to `D_{𝒮₁}(A₁)` and `H` in
`D⁺_{𝒜₂}(A₂)`, `a ↦ Lq(a) ≫ c` is a bijection
`Hom(q E', j₁ Rq q⁺ H) ≃ Hom(Lq q E', j₂ q⁺ H)`. -/
theorem bijective_serreQuotientHomMap_of_leftOrthogonal
    {E' : (derivedCategoryB 𝒜₁).FullSubcategory}
    (hE' : (serreQuotientKernel 𝒜₁ 𝒮₁).leftOrthogonal E')
    (H : (derivedCategoryBInPlus 𝒜₂).FullSubcategory) :
    Function.Bijective (serreQuotientHomMap adj hL hres hR𝒜 hR𝒮
      ((serreQuotientW 𝒜₁ 𝒮₁).Q.obj E') ((serreQuotientWPlus 𝒜₂ 𝒮₂).Q.obj H)) := by
  have := isLocalization_serreQuotientW_Q_trW 𝒜₁ 𝒮₁
  have := isLocalization_serreQuotientW_Q_trW 𝒜₂ 𝒮₂
  let Y := (plusInclusion 𝒜₁).obj ((derivedCategoryBInPlusMap R hR𝒜).obj H)
  let ψ₁ : (E'.obj ⟶ (R.rightDerivedFunctorPlus.obj H.obj).obj) →
      ((serreQuotientW 𝒜₁ 𝒮₁).Q.obj E' ⟶ (serreQuotientW 𝒜₁ 𝒮₁).Q.obj Y) := fun b =>
    (serreQuotientW 𝒜₁ 𝒮₁).Q.map (ObjectProperty.homMk b : E' ⟶ Y)
  have hψ₁ : Function.Bijective ψ₁ :=
    (leftOrthogonal.map_bijective_of_isTriangulated hE' (serreQuotientW 𝒜₁ 𝒮₁).Q Y).comp
      (bijective_homMk E' Y)
  let M := (derivedCategoryBMap L hL).obj E'
  let ψ₂ : (E'.obj ⟶ (R.rightDerivedFunctorPlus.obj H.obj).obj) →
      ((serreQuotientDerivedPullback L hL hres).obj ((serreQuotientW 𝒜₁ 𝒮₁).Q.obj E') ⟶
        (serreQuotientW 𝒜₂ 𝒮₂).Q.obj ((plusInclusion 𝒜₂).obj H)) := fun b =>
    (serreQuotientDerivedPullbackCounit L hL hres).app E' ≫
      (serreQuotientW 𝒜₂ 𝒮₂).Q.map
        (ObjectProperty.homMk ((adj.unboundedHomEquiv E'.obj H.obj).symm b) :
          M ⟶ (plusInclusion 𝒜₂).obj H)
  have hψ₂ : Function.Bijective ψ₂ := by
    have : IsIso ((serreQuotientDerivedPullbackCounit (𝒮₂ := 𝒮₂) L hL hres).app E') :=
      isIso_serreQuotientDerivedPullbackCounit_app (𝒮₂ := 𝒮₂) L hL hres hE'
    have hQ := map_bijective_of_leftOrthogonal_inf (boundedBelowPart 𝒜₂)
      (serreQuotientKernel 𝒜₂ 𝒮₂) (serreQuotientW 𝒜₂ 𝒮₂).Q
      (leftOrthogonal_derivedCategoryBMap_obj adj hL hR𝒜 hR𝒮 hE')
      (H := (plusInclusion 𝒜₂).obj H) H.obj.property
    have hm := (bijective_homMk M ((plusInclusion 𝒜₂).obj H)).comp
      (adj.unboundedHomEquiv E'.obj H.obj).symm.bijective
    exact (bijective_comp_left_of_isIso _).comp (hQ.comp hm)
  have key : serreQuotientHomMap adj hL hres hR𝒜 hR𝒮
      ((serreQuotientW 𝒜₁ 𝒮₁).Q.obj E') ((serreQuotientWPlus 𝒜₂ 𝒮₂).Q.obj H) ∘ ψ₁ = ψ₂ := by
    funext b
    change (serreQuotientDerivedPullback L hL hres).map
        ((serreQuotientW 𝒜₁ 𝒮₁).Q.map (ObjectProperty.homMk b : E' ⟶ Y)) ≫
        (serreQuotientCounit adj hL hres hR𝒜 hR𝒮).app ((serreQuotientWPlus 𝒜₂ 𝒮₂).Q.obj H) = _
    rw [serreQuotientCounit_app_Q]
    have h₄ := (serreQuotientDerivedPullbackCounit (𝒮₂ := 𝒮₂) L hL hres).naturality
      (ObjectProperty.homMk b : E' ⟶ Y)
    dsimp only [Functor.comp_map, Functor.comp_obj] at h₄
    have k : (serreQuotientDerivedPullback L hL hres).map
        ((serreQuotientW 𝒜₁ 𝒮₁).Q.map (ObjectProperty.homMk b : E' ⟶ Y)) ≫
        (serreQuotientDerivedPullbackCounit L hL hres).app Y ≫
          (serreQuotientW 𝒜₂ 𝒮₂).Q.map ((derivedCategoryBPlusCounit adj hL hR𝒜).app H) =
        (serreQuotientDerivedPullbackCounit L hL hres).app E' ≫
          (serreQuotientW 𝒜₂ 𝒮₂).Q.map
            (ObjectProperty.homMk ((adj.unboundedHomEquiv E'.obj H.obj).symm b) :
              M ⟶ (plusInclusion 𝒜₂).obj H) := by
      rw [reassoc_of% h₄, ← Functor.map_comp]
      congr 2
    exact k
  rw [← key] at hψ₂
  exact (Function.Bijective.of_comp_iff _ hψ₁).1 hψ₂

/-- `a ↦ Lq(a) ≫ c_B` is natural in `A`. -/
theorem serreQuotientHomMap_comp {A A' : (serreQuotientW 𝒜₁ 𝒮₁).Localization} (e : A' ⟶ A)
    (B : (serreQuotientWPlus 𝒜₂ 𝒮₂).Localization)
    (a : A ⟶ (serreQuotientPlusToSerreQuotient 𝒜₁ 𝒮₁).obj
      ((serreQuotientPushforwardPlus R hR𝒜 hR𝒮).obj B)) :
    serreQuotientHomMap adj hL hres hR𝒜 hR𝒮 A' B (e ≫ a) =
      (serreQuotientDerivedPullback L hL hres).map e ≫
        serreQuotientHomMap adj hL hres hR𝒜 hR𝒮 A B a := by
  simp only [serreQuotientHomMap, Functor.map_comp, Category.assoc]

/-- **The adjointness of Stacks 07BE, as a bijection.** For every `A` in `D_{𝒜₁}(A₁)/D_{𝒮₁}(A₁)`
and every `B` in `D⁺_{𝒜₂}(A₂)/D⁺_{𝒮₂}(A₂)`, `a ↦ Lq(a) ≫ c_B` is a bijection
`Hom(A, j₁ (Rq B)) ≃ Hom(Lq A, j₂ B)`. -/
theorem bijective_serreQuotientHomMap (A : (serreQuotientW 𝒜₁ 𝒮₁).Localization)
    (B : (serreQuotientWPlus 𝒜₂ 𝒮₂).Localization) :
    Function.Bijective (serreQuotientHomMap adj hL hres hR𝒜 hR𝒮 A B) := by
  obtain ⟨E, rfl⟩ := (Localization.Construction.objEquiv (serreQuotientW 𝒜₁ 𝒮₁)).surjective A
  obtain ⟨H, rfl⟩ :=
    (Localization.Construction.objEquiv (serreQuotientWPlus 𝒜₂ 𝒮₂)).surjective B
  obtain ⟨E', s, hs, hE'⟩ := hres E
  have : IsIso ((serreQuotientW 𝒜₁ 𝒮₁).Q.map s) := Localization.inverts _ _ _ hs
  have h' := bijective_serreQuotientHomMap_of_leftOrthogonal adj hL hres hR𝒜 hR𝒮 hE' H
  have hnat : serreQuotientHomMap adj hL hres hR𝒜 hR𝒮 ((serreQuotientW 𝒜₁ 𝒮₁).Q.obj E')
      ((serreQuotientWPlus 𝒜₂ 𝒮₂).Q.obj H) ∘
        (fun a => (serreQuotientW 𝒜₁ 𝒮₁).Q.map s ≫ a) =
      (fun g => (serreQuotientDerivedPullback L hL hres).map
        ((serreQuotientW 𝒜₁ 𝒮₁).Q.map s) ≫ g) ∘
        serreQuotientHomMap adj hL hres hR𝒜 hR𝒮 ((serreQuotientW 𝒜₁ 𝒮₁).Q.obj E)
          ((serreQuotientWPlus 𝒜₂ 𝒮₂).Q.obj H) := by
    funext a
    exact serreQuotientHomMap_comp adj hL hres hR𝒜 hR𝒮 _ _ a
  have := h'.comp (bijective_comp_left_of_isIso ((serreQuotientW 𝒜₁ 𝒮₁).Q.map s))
  rw [hnat] at this
  exact (Function.Bijective.of_comp_iff'
    (bijective_comp_left_of_isIso
      ((serreQuotientDerivedPullback L hL hres).map ((serreQuotientW 𝒜₁ 𝒮₁).Q.map s))) _).1 this

/-- **Stacks 07BE, the adjointness.** For `A` in `D_{𝒜₁}(A₁)/D_{𝒮₁}(A₁)` and `B` in
`D⁺_{𝒜₂}(A₂)/D⁺_{𝒮₂}(A₂)`,

`Hom(Lq A, j₂ B) ≃ Hom(A, j₁ (Rq B))`,

where `j₁`, `j₂` are the functors from the bounded below Verdier quotients to the unbounded
ones. -/
def serreQuotientHomEquiv (A : (serreQuotientW 𝒜₁ 𝒮₁).Localization)
    (B : (serreQuotientWPlus 𝒜₂ 𝒮₂).Localization) :
    ((serreQuotientDerivedPullback L hL hres).obj A ⟶
        (serreQuotientPlusToSerreQuotient 𝒜₂ 𝒮₂).obj B) ≃
      (A ⟶ (serreQuotientPlusToSerreQuotient 𝒜₁ 𝒮₁).obj
        ((serreQuotientPushforwardPlus R hR𝒜 hR𝒮).obj B)) :=
  (Equiv.ofBijective _ (bijective_serreQuotientHomMap adj hL hres hR𝒜 hR𝒮 A B)).symm

/-- The inverse of `serreQuotientHomEquiv` sends `a` to `Lq(a) ≫ c_B`. -/
theorem serreQuotientHomEquiv_symm_apply (A : (serreQuotientW 𝒜₁ 𝒮₁).Localization)
    (B : (serreQuotientWPlus 𝒜₂ 𝒮₂).Localization)
    (a : A ⟶ (serreQuotientPlusToSerreQuotient 𝒜₁ 𝒮₁).obj
      ((serreQuotientPushforwardPlus R hR𝒜 hR𝒮).obj B)) :
    (serreQuotientHomEquiv adj hL hres hR𝒜 hR𝒮 A B).symm a =
      (serreQuotientDerivedPullback L hL hres).map a ≫
        (serreQuotientCounit adj hL hres hR𝒜 hR𝒮).app B :=
  rfl

/-- Naturality of the adjointness in the first variable. -/
theorem serreQuotientHomEquiv_naturality_left {A A' : (serreQuotientW 𝒜₁ 𝒮₁).Localization}
    (e : A' ⟶ A) (B : (serreQuotientWPlus 𝒜₂ 𝒮₂).Localization)
    (g : (serreQuotientDerivedPullback L hL hres).obj A ⟶
      (serreQuotientPlusToSerreQuotient 𝒜₂ 𝒮₂).obj B) :
    serreQuotientHomEquiv adj hL hres hR𝒜 hR𝒮 A' B
        ((serreQuotientDerivedPullback L hL hres).map e ≫ g) =
      e ≫ serreQuotientHomEquiv adj hL hres hR𝒜 hR𝒮 A B g := by
  apply (serreQuotientHomEquiv adj hL hres hR𝒜 hR𝒮 A' B).symm.injective
  rw [Equiv.symm_apply_apply, serreQuotientHomEquiv_symm_apply, Functor.map_comp,
    Category.assoc, ← serreQuotientHomEquiv_symm_apply, Equiv.symm_apply_apply]

/-- Naturality of the adjointness in the second variable. -/
theorem serreQuotientHomEquiv_naturality_right (A : (serreQuotientW 𝒜₁ 𝒮₁).Localization)
    {B B' : (serreQuotientWPlus 𝒜₂ 𝒮₂).Localization} (k : B ⟶ B')
    (g : (serreQuotientDerivedPullback L hL hres).obj A ⟶
      (serreQuotientPlusToSerreQuotient 𝒜₂ 𝒮₂).obj B) :
    serreQuotientHomEquiv adj hL hres hR𝒜 hR𝒮 A B'
        (g ≫ (serreQuotientPlusToSerreQuotient 𝒜₂ 𝒮₂).map k) =
      serreQuotientHomEquiv adj hL hres hR𝒜 hR𝒮 A B g ≫
        (serreQuotientPlusToSerreQuotient 𝒜₁ 𝒮₁).map
          ((serreQuotientPushforwardPlus R hR𝒜 hR𝒮).map k) := by
  apply (serreQuotientHomEquiv adj hL hres hR𝒜 hR𝒮 A B').symm.injective
  have hc := (serreQuotientCounit adj hL hres hR𝒜 hR𝒮).naturality k
  dsimp only [Functor.comp_map] at hc
  rw [Equiv.symm_apply_apply, serreQuotientHomEquiv_symm_apply, Functor.map_comp,
    Category.assoc, hc, ← Category.assoc, ← serreQuotientHomEquiv_symm_apply,
    Equiv.symm_apply_apply]

end Adjunction

end DerivedCategoryB
