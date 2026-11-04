module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekGeometricStalkSurjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundedSetBaseChangeTransfer
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BaseChangeCommutationProjections
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackSections
public import StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategoriesAppIsIso
public import StacksFrontier.CategoryTheory.Sites.PullbackSectionsComparisonValued

/-!
# Extension from the small to the big étale site commutes with a base-changing direct image

Let `B` be a big étale site and `f : T ⟶ S` a morphism of it. Write `π_S` for the projection
from the big étale topos over `S` to the small étale topos of `S`, `f_small` for the morphism of
small étale topoi and `f_big` for that of big étale topoi. Since `π_S ∘ f_big = f_small ∘ π_T`
there is a canonical base change map

`π_S⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_T⁻¹`,

the mate of the identification `π_{T,*} ⋙ f_{small,*} = f_{big,*} ⋙ π_{S,*}`. This file proves
that it is an isomorphism as soon as the base change map
`g⁻¹ f_{small,*} ⟶ f'_{small,*} (g')⁻¹` of the small étale sites is an isomorphism for the
fibre square of `f` along every object `g : S' ⟶ S` of the big étale site over `S`. For `f`
proper that is proper base change for sheaves of sets, Stacks 0A3U, and the conclusion is
Stacks 0DDJ (1).

The construction, the cube identity and the criterion are stated for sheaves with values in an
arbitrary category `A`, the inverse images `π⁻¹` being given as left adjoints of the restrictions
`π_*`: for sheaves of sets they are those of the morphisms of topoi
`AlgebraicGeometry.bigEtaleToSmallEtaleMorphism`, and for abelian sheaves the sheaf pullbacks, as
used by `StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.FiniteDirectImage` and
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.DerivedProperDirectImage`.

## Main definitions

* `AlgebraicGeometry.bigSmallEtaleDirectImageSquare` — the identification
  `π_{T,*} ⋙ f_{small,*} = f_{big,*} ⋙ π_{S,*}` of direct images.
* `AlgebraicGeometry.bigSmallEtaleBaseChange` — its mate, the base change map
  `π_S⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_T⁻¹`.

## Main results

* `AlgebraicGeometry.isIso_bigSmallEtaleBaseChange_of_forall_isIso_mateEquiv` — at any
  coefficients, the base change map of the big and small sites is invertible once the small-site
  base change maps of the fibre squares are;
  `AlgebraicGeometry.isIso_bigSmallEtaleBaseChange_of_forall_isIso` is the case of sheaves of sets.
* `AlgebraicGeometry.isIso_bigSmallEtaleBaseChange_of_isIso_smallEtaleSetBaseChange` — the same,
  with the hypothesis in the form of the conclusion of Stacks 0A3U.

## Implementation notes

The argument is the pasting law for mates, in the form
`Stacks.CategoryTheory.isIso_map_mateEquiv_symm_app_of_isIso`. For an object `g : S' ⟶ S` of
the big étale site over `S`, restriction `ρ_g` along `i_g : S'_étale ⟶ (Sch/S)_étale` carries the
base change map to one which, up to the canonical identifications `ρ_g ∘ π_S⁻¹ = g⁻¹` of
`AlgebraicGeometry.etaleSmallPullbackIso` and `ρ_g ∘ f_{big,*} = f'_{small,*} ∘ ρ_{g'}`, is the
small-site base change map of the fibre square. The only identity to be checked is one between
2-cells built from direct images, which are all restrictions along functors of sites; evaluated
at a sheaf and an object it is an identity of morphisms of the big étale site over `T`, checked
on the two projections of a fibre product. Sections at `g` itself are sections of `ρ_g` at the
final object of `S'_étale`, so the restrictions `ρ_g` jointly detect isomorphisms.

The coefficient-general sheaf pullback comparison used here is
`CategoryTheory.sheafPullbackIsoOfInitialValued` (and `..._unit`), a generalization of
`CategoryTheory.sheafPullbackIsoOfInitial`; the projection lemma for the factored
composition comparison is `AlgebraicGeometry.SmallEtale.factoredCompIso_inv_app_fst`;
`AlgebraicGeometry.smallEtaleBaseChangeNatTrans` and
`AlgebraicGeometry.SmallEtale.smallEtaleBaseChangeMate_eq_boundedBaseChangeMate` take one
universe.

## References

* [Stacks Project, Tag 0DDJ](https://stacks.math.columbia.edu/tag/0DDJ)
* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.TwoSquare
open Opposite

universe u v v₁ u₁

namespace AlgebraicGeometry

/-! ### The base change map of the big and small étale sites -/

section BaseChange

variable (B : BigEtaleSite.{u})

/-- The adjunction `π_S⁻¹ ⊣ π_{S,*}` of the projection from the big étale topos over `S` to the
small étale topos of `S`, with its right adjoint spelled as restriction along the inclusion of
the small étale site, which it is by definition. -/
public def bigEtaleProjectionAdjunction (S : B.Scheme) :
    (bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage ⊣
      (SmallEtale.inclusion B S.obj S.property).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S.obj S.property) (BigEtaleOver.topology B S.obj S.property) :=
  (bigEtaleToSmallEtaleMorphism B S.obj S.property).adj

variable (A : Type u₁) [Category.{v₁} A]

/-- The direct image `π_{S,*}` of the projection from the big étale topos over `S` to the small
étale topos of `S`, at coefficients `A`: restriction of sheaves along the inclusion of the small
étale site of `S` into the big étale site over `S`. -/
public abbrev bigEtaleProjectionPushforward (S : B.Scheme) :
    Sheaf (BigEtaleOver.topology B S.obj S.property) A ⥤
      Sheaf (SmallEtale.topology B S.obj S.property) A :=
  (SmallEtale.inclusion B S.obj S.property).sheafPushforwardContinuous A
    (SmallEtale.topology B S.obj S.property) (BigEtaleOver.topology B S.obj S.property)

variable {T S : B.Scheme} (f : T ⟶ S)

/-- **The identification `π_{T,*} ⋙ f_{small,*} = f_{big,*} ⋙ π_{S,*}` of direct images.** Both
composites are restriction of sheaves along the same functor of sites,
`AlgebraicGeometry.smallEtaleBaseChange_comp_inclusion`. Here `f_{big,*}` is restriction along
`Over.pullback f`, which is the direct image of `AlgebraicGeometry.bigEtaleMorphism` by
`AlgebraicGeometry.bigEtaleMorphismPushforwardIso`. -/
public def bigSmallEtaleDirectImageSquare :
    TwoSquare (bigEtaleProjectionPushforward B A T)
      ((Over.pullback f).sheafPushforwardContinuous A
        (BigEtaleOver.topology B S.obj S.property) (BigEtaleOver.topology B T.obj T.property))
      (B.smallPushforward f A) (bigEtaleProjectionPushforward B A S) :=
  letI : (smallEtaleBaseChange B f ⋙ SmallEtale.inclusion B T.obj T.property).IsContinuous
      (SmallEtale.topology B S.obj S.property) (BigEtaleOver.topology B T.obj T.property) :=
    Functor.isContinuous_comp _ _ _ (SmallEtale.topology B T.obj T.property) _
  letI : (SmallEtale.inclusion B S.obj S.property ⋙ Over.pullback f).IsContinuous
      (SmallEtale.topology B S.obj S.property) (BigEtaleOver.topology B T.obj T.property) :=
    Functor.isContinuous_comp _ _ _ (BigEtaleOver.topology B S.obj S.property) _
  TwoSquare.mk _ _ _ _
    (Functor.sheafPushforwardContinuousNatTrans
      (eqToIso (smallEtaleBaseChange_comp_inclusion B f)).inv A
      (SmallEtale.topology B S.obj S.property) (BigEtaleOver.topology B T.obj T.property))

/-- **The base change map `π_S⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_T⁻¹`** of the square of topoi
`π_S ∘ f_big = f_small ∘ π_T`, at coefficients `A`: the mate of
`AlgebraicGeometry.bigSmallEtaleDirectImageSquare` along adjunctions `π_T⁻¹ ⊣ π_{T,*}` and
`π_S⁻¹ ⊣ π_{S,*}`. The inverse images are taken as data, with their adjunctions: for sheaves of
sets they are those of the morphisms of topoi `AlgebraicGeometry.bigEtaleToSmallEtaleMorphism`,
`AlgebraicGeometry.bigEtaleProjectionAdjunction`, and for other coefficients the sheaf pullbacks
along the inclusions of the small étale sites. -/
public def bigSmallEtaleBaseChange
    {LT : Sheaf (SmallEtale.topology B T.obj T.property) A ⥤
      Sheaf (BigEtaleOver.topology B T.obj T.property) A}
    {LS : Sheaf (SmallEtale.topology B S.obj S.property) A ⥤
      Sheaf (BigEtaleOver.topology B S.obj S.property) A}
    (adjT : LT ⊣ bigEtaleProjectionPushforward B A T)
    (adjS : LS ⊣ bigEtaleProjectionPushforward B A S) :
    B.smallPushforward f A ⋙ LS ⟶
      LT ⋙ (Over.pullback f).sheafPushforwardContinuous A
        (BigEtaleOver.topology B S.obj S.property) (BigEtaleOver.topology B T.obj T.property) :=
  ((mateEquiv adjT adjS).symm (bigSmallEtaleDirectImageSquare B A f)).natTrans

end BaseChange

/-! ### Restriction to a small étale site and the comparison of inverse images -/

section Restriction

variable (B : BigEtaleSite.{u}) (A : Type u₁) [Category.{v₁} A] (S : B.Scheme)
  (U : BigEtaleOver B S.obj S.property)

/-- Restriction `ρ_U` of sheaves on the big étale site over `S` to the small étale site of an
object `U` of it, along `i_U : U_étale ⟶ (Sch/S)_étale`. -/
public abbrev bigEtaleRestriction :
    Sheaf (BigEtaleOver.topology B S.obj S.property) A ⥤
      Sheaf (SmallEtale.topology B U.left.obj U.left.property) A :=
  (smallEtaleToBigEtaleFunctor B U.left S U.hom).sheafPushforwardContinuous A
    (SmallEtale.topology B U.left.obj U.left.property) (BigEtaleOver.topology B S.obj S.property)

/-- The comparison `π_{S,*} ⟶ ρ_U ⋙ (U ⟶ S)_{small,*}` of direct images: restriction along the
counits `V ×_S U ⟶ V` of `AlgebraicGeometry.etaleCounit`. -/
public def bigEtaleRestrictionCounitSquare :
    TwoSquare (bigEtaleProjectionPushforward B A S) (bigEtaleRestriction B A S U) (𝟭 _)
      (B.smallPushforward U.hom A) :=
  letI : (smallEtaleBaseChange B U.hom ⋙ smallEtaleToBigEtaleFunctor B U.left S U.hom).IsContinuous
      (SmallEtale.topology B S.obj S.property) (BigEtaleOver.topology B S.obj S.property) :=
    Functor.isContinuous_comp _ _ _ (SmallEtale.topology B U.left.obj U.left.property) _
  TwoSquare.mk _ _ _ _
    (Functor.sheafPushforwardContinuousNatTrans (etaleCounit B U.hom) A
      (SmallEtale.topology B S.obj S.property) (BigEtaleOver.topology B S.obj S.property))

variable {LS : Sheaf (SmallEtale.topology B S.obj S.property) A ⥤
    Sheaf (BigEtaleOver.topology B S.obj S.property) A}
  (adjS : LS ⊣ bigEtaleProjectionPushforward B A S)
  [((smallEtaleBaseChange B U.hom).sheafPushforwardContinuous A
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B U.left.obj U.left.property)).IsRightAdjoint]
  [∀ F : (SmallEtale B U.left.obj U.left.property)ᵒᵖ ⥤ A,
    (smallEtaleToBigEtaleFunctor B U.left S U.hom).op.HasPointwiseRightKanExtension F]

/-- The comparison `(U ⟶ S)⁻¹ ⟶ π_S⁻¹ ⋙ ρ_U` of inverse images, as a 2-square: the small étale
pullback along `U ⟶ S` is the inverse image along `π_S` followed by restriction to `U`, by
`CategoryTheory.sheafPullbackIsoOfInitialValued` applied to the factorization of base change along
`U ⟶ S` through `i_U`, whose comparison arrows are initial by
`AlgebraicGeometry.etaleCounitInitial`. For sheaves of sets and the inverse image of
`AlgebraicGeometry.bigEtaleToSmallEtaleMorphism` this is
`AlgebraicGeometry.etaleSmallPullbackIso`. -/
public def bigEtaleRestrictionPullbackSquare :
    TwoSquare (𝟭 _) LS (B.smallInverseImage U.hom A) (bigEtaleRestriction B A S U) :=
  TwoSquare.mk _ _ _ _ (sheafPullbackIsoOfInitialValued
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B U.left.obj U.left.property)
      (BigEtaleOver.topology B S.obj S.property)
      (smallEtaleBaseChange B U.hom)
      (smallEtaleToBigEtaleFunctor B U.left S U.hom)
      (SmallEtale.inclusion B S.obj S.property)
      (etaleCounit B U.hom) LS adjS (etaleCounitInitial B U.hom)).hom

/-- The comparison `AlgebraicGeometry.bigEtaleRestrictionPullbackSquare` of inverse images is
invertible: it is the forward map of the isomorphism `sheafPullbackIsoOfInitialValued`. -/
public instance isIso_bigEtaleRestrictionPullbackSquare :
    IsIso (bigEtaleRestrictionPullbackSquare B A S U adjS).natTrans := by
  dsimp only [bigEtaleRestrictionPullbackSquare, TwoSquare.mk, TwoSquare.natTrans]
  infer_instance

/-- **The mate of the comparison of inverse images is restriction along the counits.** Under the
adjunctions `π_S⁻¹ ⊣ π_{S,*}` and `(U ⟶ S)⁻¹ ⊣ (U ⟶ S)_*`, the 2-square
`AlgebraicGeometry.bigEtaleRestrictionPullbackSquare` corresponds to
`AlgebraicGeometry.bigEtaleRestrictionCounitSquare`. This is the equation
`CategoryTheory.sheafPullbackIsoOfInitialValued_unit` pinning down the comparison. -/
public theorem mateEquiv_bigEtaleRestrictionPullbackSquare :
    mateEquiv adjS (B.smallPullbackAdjunction U.hom A)
        (bigEtaleRestrictionPullbackSquare B A S U adjS) =
      bigEtaleRestrictionCounitSquare B A S U := by
  suffices h : bigEtaleRestrictionPullbackSquare B A S U adjS =
      (mateEquiv adjS (B.smallPullbackAdjunction U.hom A)).symm
        (bigEtaleRestrictionCounitSquare B A S U) by
    rw [h, Equiv.apply_symm_apply]
  refine TwoSquare.ext _ _ fun F => ?_
  apply ((B.smallPullbackAdjunction U.hom A).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Eq.trans ?_ (unit_mateEquiv_symm adjS
    (B.smallPullbackAdjunction U.hom A) (bigEtaleRestrictionCounitSquare B A S U) F)
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
  exact sheafPullbackIsoOfInitialValued_unit
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B U.left.obj U.left.property)
    (BigEtaleOver.topology B S.obj S.property)
    (smallEtaleBaseChange B U.hom)
    (smallEtaleToBigEtaleFunctor B U.left S U.hom)
    (SmallEtale.inclusion B S.obj S.property)
    (etaleCounit B U.hom) LS adjS (etaleCounitInitial B U.hom) F V

end Restriction

/-! ### The fibre square of `f` along an object of the big étale site -/

section FibreSquare

variable (B : BigEtaleSite.{u}) (A : Type u₁) [Category.{v₁} A] {T S : B.Scheme} (f : T ⟶ S)
  (U : BigEtaleOver B S.obj S.property)

/-- The projection `U ×_S T ⟶ U` of the fibre square of `f` along `U`, with its source spelled
as the underlying object of `(Over.pullback f).obj U`. -/
public abbrev bigEtaleFibreFst : ((Over.pullback f).obj U).left ⟶ U.left :=
  pullback.fst U.hom f

/-- The fibre square of `f` along `U`: `U ×_S T` with its two projections. -/
public theorem bigEtaleFibreSquare_isPullback :
    IsPullback ((Over.pullback f).obj U).hom (bigEtaleFibreFst B f U) f U.hom :=
  (IsPullback.of_hasPullback U.hom f).flip

/-- **Restriction commutes with the big direct image along `f`.** Restriction to the small
étale site of `U ×_S T` followed by the small direct image along `U ×_S T ⟶ U` is the big
direct image along `f` followed by restriction to the small étale site of `U`. -/
public def bigEtaleRestrictionDirectImageSquare :
    bigEtaleRestriction B A T ((Over.pullback f).obj U) ⋙
        B.smallPushforward (bigEtaleFibreFst B f U) A ⟶
      (Over.pullback f).sheafPushforwardContinuous A
          (BigEtaleOver.topology B S.obj S.property) (BigEtaleOver.topology B T.obj T.property) ⋙
        bigEtaleRestriction B A S U :=
  letI : (smallEtaleToBigEtaleFunctor B U.left S U.hom ⋙ Over.pullback f).IsContinuous
      (SmallEtale.topology B U.left.obj U.left.property)
      (BigEtaleOver.topology B T.obj T.property) :=
    Functor.isContinuous_comp _ _ _ (BigEtaleOver.topology B S.obj S.property) _
  letI : (smallEtaleBaseChange B (bigEtaleFibreFst B f U) ⋙
      smallEtaleToBigEtaleFunctor B ((Over.pullback f).obj U).left T
        ((Over.pullback f).obj U).hom).IsContinuous
      (SmallEtale.topology B U.left.obj U.left.property)
      (BigEtaleOver.topology B T.obj T.property) :=
    Functor.isContinuous_comp _ _ _
      (SmallEtale.topology B ((Over.pullback f).obj U).left.obj
        ((Over.pullback f).obj U).left.property) _
  (Functor.sheafPushforwardContinuousIso
    (smallEtaleCartesianIndexIso B ((Over.pullback f).obj U).hom (bigEtaleFibreFst B f U) f
      U.hom (bigEtaleFibreSquare_isPullback B f U))
    A (SmallEtale.topology B U.left.obj U.left.property)
    (BigEtaleOver.topology B T.obj T.property)).inv

/-- The comparison `AlgebraicGeometry.bigEtaleRestrictionDirectImageSquare` of direct images is
invertible: it is the inverse of the isomorphism of restrictions induced by the cartesian square
`AlgebraicGeometry.bigEtaleFibreSquare_isPullback`. -/
public instance isIso_bigEtaleRestrictionDirectImageSquare :
    IsIso (bigEtaleRestrictionDirectImageSquare B A f U) :=
  letI : (smallEtaleToBigEtaleFunctor B U.left S U.hom ⋙ Over.pullback f).IsContinuous
      (SmallEtale.topology B U.left.obj U.left.property)
      (BigEtaleOver.topology B T.obj T.property) :=
    Functor.isContinuous_comp _ _ _ (BigEtaleOver.topology B S.obj S.property) _
  letI : (smallEtaleBaseChange B (bigEtaleFibreFst B f U) ⋙
      smallEtaleToBigEtaleFunctor B ((Over.pullback f).obj U).left T
        ((Over.pullback f).obj U).hom).IsContinuous
      (SmallEtale.topology B U.left.obj U.left.property)
      (BigEtaleOver.topology B T.obj T.property) :=
    Functor.isContinuous_comp _ _ _
      (SmallEtale.topology B ((Over.pullback f).obj U).left.obj
        ((Over.pullback f).obj U).left.property) _
  Iso.isIso_inv (Functor.sheafPushforwardContinuousIso
    (smallEtaleCartesianIndexIso B ((Over.pullback f).obj U).hom (bigEtaleFibreFst B f U) f
      U.hom (bigEtaleFibreSquare_isPullback B f U))
    A (SmallEtale.topology B U.left.obj U.left.property)
    (BigEtaleOver.topology B T.obj T.property))

end FibreSquare

/-! ### The cube identity -/

section Cube

variable (B : BigEtaleSite.{u}) (A : Type u₁) [Category.{v₁} A] {T S : B.Scheme} (f : T ⟶ S)
  (U : BigEtaleOver B S.obj S.property)
  [∀ {X Y : B.Scheme} (k : X ⟶ Y), ((smallEtaleBaseChange B k).sheafPushforwardContinuous A
    (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)).IsRightAdjoint]
  [∀ (X Y : B.Scheme) (k : X ⟶ Y) (F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A),
    (smallEtaleToBigEtaleFunctor B X Y k).op.HasPointwiseRightKanExtension F]
  {LT : Sheaf (SmallEtale.topology B T.obj T.property) A ⥤
    Sheaf (BigEtaleOver.topology B T.obj T.property) A}
  {LS : Sheaf (SmallEtale.topology B S.obj S.property) A ⥤
    Sheaf (BigEtaleOver.topology B S.obj S.property) A}
  (adjT : LT ⊣ bigEtaleProjectionPushforward B A T)
  (adjS : LS ⊣ bigEtaleProjectionPushforward B A S)

/-- A chain of five composable morphisms ending in `z`, computed in four steps. -/
private lemma fst_chain {𝒞 : Type*} [Category* 𝒞] {A₀ A₁ A₂ A₃ A₄ Z P₁ B₀ : 𝒞}
    (k : A₀ ⟶ A₁) (e₂ : A₁ ⟶ A₂) (e₁ : A₂ ⟶ A₃) (c : A₃ ⟶ A₄) (z : A₄ ⟶ Z) (q : A₃ ⟶ Z)
    (r : A₂ ⟶ Z) (s₁ : A₁ ⟶ P₁) (s₂ : P₁ ⟶ Z) (t : A₀ ⟶ P₁) (m : A₀ ⟶ B₀) (n : B₀ ⟶ A₄)
    (h₁ : c ≫ z = q) (h₂ : e₁ ≫ q = r) (h₃ : e₂ ≫ r = s₁ ≫ s₂) (h₄ : k ≫ s₁ = t)
    (h₅ : m ≫ n ≫ z = t ≫ s₂) :
    (k ≫ e₂ ≫ e₁ ≫ c) ≫ z = (m ≫ n) ≫ z := by
  simp only [Category.assoc, h₁, h₂, h₅]
  rw [h₃, ← Category.assoc, h₄]

/-- Three restrictions of a presheaf, the middle one along the image of a composite under a
functor, agree with two as soon as the composites agree. -/
private lemma presheaf_map_three_eq_two {𝒞 𝒟 ℰ : Type*} [Category* 𝒞] [Category* 𝒟]
    [Category* ℰ] (P : 𝒞ᵒᵖ ⥤ 𝒟) (G : ℰ ⥤ 𝒞) {E₁ E₂ E₃ : ℰ} {X₀ X₄ Y : 𝒞}
    (a : G.obj E₁ ⟶ X₀) (b : E₂ ⟶ E₁) (c : E₃ ⟶ E₂) (d : X₄ ⟶ G.obj E₃)
    (e : Y ⟶ X₀) (k : X₄ ⟶ Y) (h : d ≫ G.map c ≫ G.map b ≫ a = k ≫ e) :
    P.map a.op ≫ P.map (G.map (c ≫ b)).op ≫ P.map d.op = P.map e.op ≫ P.map k.op := by
  simp only [← P.map_comp, ← op_comp, G.map_comp, Category.assoc, h]

/-- Two identities in front of a composite cancel. -/
private lemma id_id_comp_eq {𝒞 : Type*} [Category* 𝒞] {X Y Z W V : 𝒞} (i₁ i₂ : X ⟶ X)
    (x : X ⟶ Y) (y : Y ⟶ Z) (z : Z ⟶ W) (p : X ⟶ V) (q : V ⟶ W) (h₁ : i₁ = 𝟙 X)
    (h₂ : i₂ = 𝟙 X) (h : x ≫ y ≫ z = p ≫ q) : ((i₁ ≫ i₂) ≫ x ≫ y) ≫ z = p ≫ q := by
  subst h₁ h₂
  simpa only [Category.id_comp, Category.assoc] using h

/-- **The cube identity for the base change map of the big and small étale sites.** -/
public theorem bigSmallEtale_cube_eq :
    ((mateEquiv adjT
          (B.smallPullbackAdjunction ((Over.pullback f).obj U).hom A)
          (bigEtaleRestrictionPullbackSquare B A T ((Over.pullback f).obj U) adjT) ≫ᵥ
        SmallEtale.boundedBaseChangeMate B A f U.hom ((Over.pullback f).obj U).hom
          (bigEtaleFibreFst B f U) (((Over.pullback f).obj U).hom ≫ f) rfl
          pullback.condition).whiskerRight
        ((Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv)).whiskerLeft
      (bigEtaleRestrictionDirectImageSquare B A f U) =
    bigSmallEtaleDirectImageSquare B A f ≫ᵥ
      mateEquiv adjS (B.smallPullbackAdjunction U.hom A)
        (bigEtaleRestrictionPullbackSquare B A S U adjS) := by
  rw [mateEquiv_bigEtaleRestrictionPullbackSquare, mateEquiv_bigEtaleRestrictionPullbackSquare]
  refine TwoSquare.ext _ _ fun H => ?_
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
  rw [SmallEtale.ts_whiskerLeft_app, SmallEtale.ts_whiskerRight_app, SmallEtale.ts_vComp_app,
    SmallEtale.ts_vComp_app]
  refine id_id_comp_eq _ _ _ _ _ _ _ rfl rfl ?_
  rw [SmallEtale.boundedBaseChangeMate_app_hom_app]
  refine presheaf_map_three_eq_two H.obj
    (smallEtaleToBigEtaleFunctor B ((Over.pullback f).obj U).left T
      ((Over.pullback f).obj U).hom) _ _ _ _ _ _ ?_
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
  · exact fst_chain _ _ _ _ _ _ _ _ _ _ _ _ (by simp [etaleCounit])
      (SmallEtale.factoredCompIso_inv_app_fst B _ _ _ rfl V.unop)
      (smallEtaleBaseChange_factoredCompIso_hom_app_fst B _ _ _ _ _ _ pullback.condition V.unop)
      (smallEtaleCartesianIndexIso_hom_app_left_fst B _ _ _ _ _ _)
      (by
        simp only [op_obj, comp_obj, ObjectProperty.ι_obj, smallEtaleBaseChange_obj_obj,
          Over.pullback_obj_left, Over.map_obj_left, Over.map_obj_hom, Over.pullback_obj_hom,
          NatTrans.op_app, Over.pullback_map_left, eqToIso.inv, eqToHom_app, etaleCounit]
        exact (pullback.lift_fst _ _ _).trans (by simp))
  · exact (Over.w _).trans (Over.w _).symm

end Cube

/-! ### The base change map is an isomorphism -/

section Main

variable (B : BigEtaleSite.{u}) (A : Type u₁) [Category.{v₁} A] {T S : B.Scheme} (f : T ⟶ S)

/-- **Sections at `U` detect isomorphisms.** A morphism of sheaves on the big étale site over
`S` is an isomorphism once its restriction to the small étale site of every object `U` is: the
sections at `U` are the sections of the restriction at the final object of `U_étale`. -/
public theorem isIso_of_forall_isIso_bigEtaleRestriction_map
    {F G : Sheaf (BigEtaleOver.topology B S.obj S.property) A} (φ : F ⟶ G)
    (h : ∀ U : BigEtaleOver B S.obj S.property, IsIso ((bigEtaleRestriction B A S U).map φ)) :
    IsIso φ := by
  have key : ∀ U : BigEtaleOver B S.obj S.property, IsIso (φ.hom.app (op U)) := fun U => by
    have := h U
    have h₁ : IsIso ((sheafToPresheaf _ _).map ((bigEtaleRestriction B A S U).map φ)) :=
      inferInstance
    have h₂ : IsIso (((bigEtaleRestriction B A S U).map φ).hom.app
        (op (SmallEtale.final B U.left.obj U.left.property))) :=
      NatIso.isIso_app_of_isIso ((sheafToPresheaf _ _).map ((bigEtaleRestriction B A S U).map φ)) _
    let e : (smallEtaleToBigEtaleFunctor B U.left S U.hom).obj
        (SmallEtale.final B U.left.obj U.left.property) ≅ U :=
      Over.isoMk (Iso.refl _) (by simp [SmallEtale.final])
    exact (NatTrans.isIso_app_iff_of_iso φ.hom e.op).2 h₂
  have : IsIso ((sheafToPresheaf _ _).map φ) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ ((sheafToPresheaf _ _).map φ) fun X => key X.unop
  exact isIso_of_reflects_iso φ (sheafToPresheaf _ _)

/-- **The base change map of the big and small étale sites is an isomorphism once the small-site
base change maps of the fibre squares are**, at any coefficients `A`. If, for every object
`g : U ⟶ S` of the big étale site over `S`, the base change map `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of the
fibre square `U ×_S T` — the mate of `AlgebraicGeometry.SmallEtale.boundedBaseChangeMate` along
the inverse-image/direct-image adjunctions of the size-bounded small étale sites — is an
isomorphism, then `π_S⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_T⁻¹` is an isomorphism, whatever the
chosen adjunctions `π⁻¹ ⊣ π_*`. -/
public theorem isIso_bigSmallEtaleBaseChange_of_forall_isIso_mateEquiv
    [∀ {X Y : B.Scheme} (k : X ⟶ Y), ((smallEtaleBaseChange B k).sheafPushforwardContinuous A
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)).IsRightAdjoint]
    [∀ (X Y : B.Scheme) (k : X ⟶ Y) (F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A),
      (smallEtaleToBigEtaleFunctor B X Y k).op.HasPointwiseRightKanExtension F]
    {LT : Sheaf (SmallEtale.topology B T.obj T.property) A ⥤
      Sheaf (BigEtaleOver.topology B T.obj T.property) A}
    {LS : Sheaf (SmallEtale.topology B S.obj S.property) A ⥤
      Sheaf (BigEtaleOver.topology B S.obj S.property) A}
    (adjT : LT ⊣ bigEtaleProjectionPushforward B A T)
    (adjS : LS ⊣ bigEtaleProjectionPushforward B A S)
    (hbc : ∀ U : BigEtaleOver B S.obj S.property,
      IsIso ((mateEquiv (B.smallPullbackAdjunction ((Over.pullback f).obj U).hom A)
        (B.smallPullbackAdjunction U.hom A)).symm
          (SmallEtale.boundedBaseChangeMate B A f U.hom ((Over.pullback f).obj U).hom
            (bigEtaleFibreFst B f U) (((Over.pullback f).obj U).hom ≫ f) rfl
            pullback.condition)).natTrans) :
    IsIso (bigSmallEtaleBaseChange B A f adjT adjS) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun c => ?_
  refine isIso_of_forall_isIso_bigEtaleRestriction_map B A _ fun U => ?_
  have := hbc U
  exact Stacks.CategoryTheory.isIso_map_mateEquiv_symm_app_of_isIso adjT adjS
    (B.smallPullbackAdjunction ((Over.pullback f).obj U).hom A)
    (B.smallPullbackAdjunction U.hom A)
    (bigEtaleRestrictionPullbackSquare B A T ((Over.pullback f).obj U) adjT)
    (bigEtaleRestrictionPullbackSquare B A S U adjS)
    ((Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv)
    (bigEtaleRestrictionDirectImageSquare B A f U)
    (bigSmallEtaleDirectImageSquare B A f)
    (SmallEtale.boundedBaseChangeMate B A f U.hom ((Over.pullback f).obj U).hom
      (bigEtaleFibreFst B f U) (((Over.pullback f).obj U).hom ≫ f) rfl pullback.condition)
    (bigSmallEtale_cube_eq B A f U adjT adjS) c

/-- **The base change map of the big and small étale sites is an isomorphism once the small-site
base change maps of the fibre squares are**, for sheaves of sets. If, for every object
`g : U ⟶ S` of the big étale site over `S`, the base change map `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of the
fibre square `U ×_S T` is an isomorphism of functors on sheaves of sets on the size-bounded small
étale sites, then `π_S⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_T⁻¹` is an isomorphism. -/
public theorem isIso_bigSmallEtaleBaseChange_of_forall_isIso
    (hbc : ∀ U : BigEtaleOver B S.obj S.property,
      IsIso (smallEtaleBaseChangeNatTrans.{u} B ((Over.pullback f).obj U).hom
        (bigEtaleFibreFst B f U) f U.hom pullback.condition.symm)) :
    IsIso (bigSmallEtaleBaseChange B (Type (u + 1)) f (bigEtaleProjectionAdjunction B T)
      (bigEtaleProjectionAdjunction B S)) := by
  refine isIso_bigSmallEtaleBaseChange_of_forall_isIso_mateEquiv B (Type (u + 1)) f _ _
    fun U => ?_
  have hb := hbc U
  rw [smallEtaleBaseChangeNatTrans_eq_mateEquiv_symm,
    SmallEtale.smallEtaleBaseChangeMate_eq_boundedBaseChangeMate B f U.hom
      ((Over.pullback f).obj U).hom (bigEtaleFibreFst B f U) pullback.condition.symm
      (((Over.pullback f).obj U).hom ≫ f) rfl pullback.condition] at hb
  exact hb

/-- **The base change map of the big and small étale sites is an isomorphism, granted the
conclusion of Stacks 0A3U for `f`.** If, for every cartesian square of schemes

```
X' --g'--> T
|f'        |f
v          v
Y' --g---> S
```

the base change map `Stacks.EtaleCohomology.smallEtaleSetBaseChange` `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of
sheaves of sets on the small étale sites is an isomorphism — for `f` proper this is proper base
change, Stacks 0A3U — then `π_S⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_T⁻¹` is an isomorphism. -/
public theorem isIso_bigSmallEtaleBaseChange_of_isIso_smallEtaleSetBaseChange
    (hbc : ∀ ⦃X' Y' : Scheme.{u}⦄ (g : Y' ⟶ S.obj) (g' : X' ⟶ T.obj) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' (B.inclusion.map f) g),
      IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' (B.inclusion.map f) g
        sq.w)) :
    IsIso (bigSmallEtaleBaseChange B (Type (u + 1)) f (bigEtaleProjectionAdjunction B T)
      (bigEtaleProjectionAdjunction B S)) :=
  isIso_bigSmallEtaleBaseChange_of_forall_isIso B f fun U =>
    SmallEtale.isIso_smallEtaleBaseChangeNatTrans_of_isIso_smallEtaleSetBaseChange B f U.hom
      ((Over.pullback f).obj U).hom (bigEtaleFibreFst B f U) pullback.condition.symm
      (hbc _ _ _ ((bigEtaleFibreSquare_isPullback B f U).map B.inclusion))

/-- **Stacks 0DDJ (1), granted the conclusion of Stacks 0A3U for `f`.** Under the hypothesis of
`AlgebraicGeometry.isIso_bigSmallEtaleBaseChange_of_isIso_smallEtaleSetBaseChange`,
`π_S⁻¹ ∘ f_{small,*} ≅ f_{big,*} ∘ π_T⁻¹` as functors from sheaves of sets on `T_étale` to sheaves
of sets on `(Sch/S)_étale`, `f_big` being the morphism of big étale topoi
`AlgebraicGeometry.bigEtaleMorphism`. The isomorphism is the canonical base change map
`AlgebraicGeometry.bigSmallEtaleBaseChange`. -/
public def bigSmallEtaleDirectImageIsoOfIsIso
    (hbc : ∀ ⦃X' Y' : Scheme.{u}⦄ (g : Y' ⟶ S.obj) (g' : X' ⟶ T.obj) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' (B.inclusion.map f) g),
      IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' (B.inclusion.map f) g
        sq.w)) :
    B.smallPushforward f (Type (u + 1)) ⋙
        (bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage ≅
      (bigEtaleToSmallEtaleMorphism B T.obj T.property).inverseImage ⋙
        (bigEtaleMorphism B T S f).pushforward :=
  haveI := isIso_bigSmallEtaleBaseChange_of_isIso_smallEtaleSetBaseChange B f hbc
  asIso (bigSmallEtaleBaseChange B (Type (u + 1)) f (bigEtaleProjectionAdjunction B T)
      (bigEtaleProjectionAdjunction B S)) ≪≫
    Functor.isoWhiskerLeft _ (bigEtaleMorphismPushforwardIso B T S f).symm

/-- **The degree-zero case of Stacks 0DDJ (4): for `f` finite the base change map of the big and
small étale sites is an isomorphism, unconditionally.** The small-site base change maps of the
fibre squares are invertible by Stacks 0959,
`AlgebraicGeometry.isIso_smallEtaleBaseChangeNatTrans`. This is the input "this case follows
from part (1)" of the source's proof of part (4); the derived statement of part (4) is not proved
here. -/
public theorem isIso_bigSmallEtaleBaseChange_of_isFinite [IsFinite (B.inclusion.map f)] :
    IsIso (bigSmallEtaleBaseChange B (Type (u + 1)) f (bigEtaleProjectionAdjunction B T)
      (bigEtaleProjectionAdjunction B S)) :=
  isIso_bigSmallEtaleBaseChange_of_forall_isIso B f fun U =>
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun F =>
      isIso_smallEtaleBaseChangeNatTrans.{u} B ((Over.pullback f).obj U).hom
        (bigEtaleFibreFst B f U) f U.hom
        ((bigEtaleFibreSquare_isPullback B f U).map B.inclusion) pullback.condition.symm F

/-- **Stacks 0DDJ (1), granted Stacks 0A3U.** If the base change map
`Stacks.EtaleCohomology.smallEtaleSetBaseChange` of every cartesian square of schemes with proper
right side is an isomorphism — the conclusion of Stacks 0A3U — then for `f` proper the base change
map `π_S⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_T⁻¹` is an isomorphism. -/
public theorem isIso_bigSmallEtaleBaseChange_of_properBaseChange [IsProper (B.inclusion.map f)]
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w)) :
    IsIso (bigSmallEtaleBaseChange B (Type (u + 1)) f (bigEtaleProjectionAdjunction B T)
      (bigEtaleProjectionAdjunction B S)) :=
  isIso_bigSmallEtaleBaseChange_of_isIso_smallEtaleSetBaseChange B f
    fun _ _ g g' f' sq => h0A3U _ g g' f' sq inferInstance

end Main

end AlgebraicGeometry

end
