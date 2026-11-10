module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedImmersionsPushforward.StalkInside
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedImmersionsPushforward.StalkOutside
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Coefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion

/-!
# Direct image of abelian sheaves along a closed immersion

Let `i : Z ⟶ X` be a closed immersion in a big étale site. Base change along `i` exhibits the
small étale site of `Z` as a cover-dense and locally full site over the small étale site of
`X`, so direct image along `i` is fully faithful on abelian sheaves and inverse image along `i`
is a left inverse to it. The essential image consists of the abelian sheaves on `X_étale` whose
support is contained in `Z`.

## Main definitions

* `AlgebraicGeometry.etaleStalkFunctorAbelian` — the stalk at a geometric point, as a functor
  on abelian sheaves of the small étale site.

## Main results

* `AlgebraicGeometry.smallEtaleBaseChange_isCoverDense` — every étale scheme over `Z` is
  covered by base changes of étale schemes over `X`.
* `AlgebraicGeometry.smallEtaleBaseChange_isLocallyFull` — a morphism between two such base
  changes agrees, locally on the source, with the base change of a morphism over `X`.
* `CategoryTheory.Functor.IsCoverDense.full_sheafPushforwardContinuous` and
  `CategoryTheory.Functor.IsCoverDense.faithful_sheafPushforwardContinuous`, Mathlib's instances
  fed by the two above — direct image of abelian sheaves along `i` is fully faithful. They receive
  the tag of [Stacks, Tag 04CA] part (2) here by `add_to_stacks`.
* `AlgebraicGeometry.smallEtaleAdjunction_counit_isIso_abelian` and
  `AlgebraicGeometry.smallEtalePushforwardCompPullbackIso` — the counit of the inverse
  image/direct image adjunction is an isomorphism, so inverse image is a left inverse to
  direct image.
* `AlgebraicGeometry.smallEtalePullbackStalkIsoAbelian` — the abelian form of Stacks 03Q1: the
  stalk of an inverse image is the stalk at the image geometric point.
* `AlgebraicGeometry.smallEtalePushforward_stalk_isZero_of_not_mem_range` — the abelian form of
  the outside half of Stacks 04FX: a direct image from a closed subscheme has vanishing stalk
  away from that subscheme.
* `AlgebraicGeometry.exists_geometricPoint_map_eq_of_mem_range` — a geometric point of `X`
  whose image lies in `Z` comes from a geometric point of `Z`.
* `AlgebraicGeometry.smallEtalePushforward_essImage_iff_abelian` — the description of the
  essential image, in both directions.

## Implementation notes

Both site-theoretic conditions are checked at the level of points, using that a jointly
surjective sieve of the small étale site is a covering sieve. The geometric input is the
initiality of base change on pointed étale neighbourhoods of a geometric point of `Z`: the
nonemptiness half dominates an étale neighbourhood by a base change, which is cover density,
and cofilteredness of the comma category — the form initiality takes over a cofiltered
category — equalizes a morphism against an identity, which is local fullness.

The essential image is identified at the level of stalks at geometric points, which jointly
reflect isomorphisms of abelian sheaves. Since direct image is a fully faithful right adjoint,
membership in the essential image is the assertion that the unit is an isomorphism, and that is
checked stalkwise. At a geometric point of `X` whose image misses `Z` both stalks vanish, so
any map between them is invertible; the vanishing of the stalk of a direct image is read off
from the set-valued computation, because the forgetful functor of abelian groups preserves the
filtered colimit defining the stalk, so the underlying set of that stalk is the stalk of the
underlying sheaf of sets, which is a singleton. At a geometric point lying over `Z` the point
is the image of a geometric point of `Z`, inverse image along `i` already carries the unit to
an isomorphism by the triangle identity, and the stalk of an inverse image is the stalk at the
image point; being an isomorphism transports along that natural isomorphism of functors.

The abelian form of the inverse-image stalk comparison is proved exactly as the set-valued one
in `AlgebraicGeometry.smallEtalePullbackStalkIso`; the only coefficient-dependent ingredient is
the invariance of a colimit over a category of elements under an isomorphism of the indexing
functor, which is
`CategoryTheory.CategoryOfElements.presheafColimIsoOfNatIsoOfCoefficients`.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
* [Stacks Project, Tag 04FX](https://stacks.math.columbia.edu/tag/04FX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- A point of an étale neighbourhood whose composite with a morphism `g` is the tautological lift
of `y` is carried by `g` to `y`. -/
private theorem geometricPointOfEtalePointLift_base_of_comp_eq {S : Scheme.{u}}
    (hS : B.Contains S) {U W : SmallEtale B S hS} (y : (SmallEtale.toScheme B S hS).obj U)
    (g : W ⟶ U)
    (r : (geometricPointOfEtalePoint B S hS U y).source ⟶ (SmallEtale.toScheme B S hS).obj W)
    (h : r ≫ (SmallEtale.toScheme B S hS).map g = (geometricPointOfEtalePointLift B S hS U y).1) :
    ((SmallEtale.toScheme B S hS).map g).base (r.base default) = y := by
  have hbase := congrArg (fun k : Scheme.Hom _ _ => k.base default) h
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at hbase
  exact hbase.trans (geometricPointOfEtalePointLift_base B S hS U y)

/-- Base change along a closed immersion is cover dense: every étale scheme over the closed
subscheme is covered by base changes of étale schemes over the ambient scheme. -/
public instance smallEtaleBaseChange_isCoverDense {Z X : B.Scheme} (i : Z ⟶ X)
    [IsClosedImmersion (B.inclusion.map i)] :
    (smallEtaleBaseChange B i).IsCoverDense (SmallEtale.topology B Z.1 Z.property) := by
  refine ⟨fun U => ?_⟩
  apply SmallEtale.mem_topology_of_jointlySurjective
  intro y
  set s := geometricPointOfEtalePoint B Z.1 Z.property U y
  set p := geometricPointOfEtalePointLift B Z.1 Z.property U y
  obtain ⟨A⟩ := ((pullbackNeighborhoodFunctor_initial B i s).out
    ((geometricPointFiber B Z.1 Z.property s).elementsMk U p)).is_nonempty
  refine ⟨(smallEtaleBaseChange B i).obj A.left.obj, A.hom.hom,
    ⟨⟨A.left.obj, 𝟙 _, A.hom.hom, Category.id_comp _⟩⟩, ?_⟩
  have hfac : ((pullbackNeighborhoodFunctor B i s).obj A.left).val.1 ≫
      (SmallEtale.toScheme B Z.1 Z.property).map A.hom.hom = p.1 :=
    congrArg Subtype.val A.hom.map_val
  exact ⟨(((pullbackNeighborhoodFunctor B i s).obj A.left).val.1).base default,
    geometricPointOfEtalePointLift_base_of_comp_eq B Z.property y A.hom.hom _ hfac⟩

section LocallyFull

variable {Z X : B.Scheme} (i : Z ⟶ X) (s : GeometricPoint Z.1)

/-- A lift of a geometric point of `Z` to the base change of an étale scheme `W` over `X`
determines a lift of its image to `W`, namely its composite with the first projection. -/
private def liftAlongBaseChange (W : SmallEtale B X.1 X.property)
    (q : s.source ⟶ (SmallEtale.toScheme B Z.1 Z.property).obj
      ((smallEtaleBaseChange B i).obj W))
    (hq : q ≫ B.inclusion.map (pullback.snd W.obj.hom i) = s.hom) :
    (geometricPointFiber B X.1 X.property (s.map (B.inclusion.map i))).Elements :=
  (geometricPointFiber B X.1 X.property (s.map (B.inclusion.map i))).elementsMk W
    ⟨q ≫ B.inclusion.map (pullback.fst W.obj.hom i), by
    have h : B.inclusion.map (pullback.fst W.obj.hom i) ≫ B.inclusion.map W.obj.hom =
        B.inclusion.map (pullback.snd W.obj.hom i) ≫ B.inclusion.map i := by
      rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]
    exact (Category.assoc _ _ _).trans ((congrArg (q ≫ ·) h).trans ((reassoc_of% hq) _))⟩

/-- Base change of the lift produced by `AlgebraicGeometry.liftAlongBaseChange` recovers the
original lift. -/
private lemma liftAlongBaseChange_baseChange (W : SmallEtale B X.1 X.property)
    (q : s.source ⟶ (SmallEtale.toScheme B Z.1 Z.property).obj
      ((smallEtaleBaseChange B i).obj W))
    (hq : q ≫ B.inclusion.map (pullback.snd W.obj.hom i) = s.hom) :
    ((pullbackNeighborhoodFunctor B i s).obj (liftAlongBaseChange B i s W q hq)).val.1 = q := by
  have hobj : ((pullbackNeighborhoodFunctor B i s).obj
      (liftAlongBaseChange B i s W q hq)).val =
      geometricPointFiberBaseChangeEquiv B i s W (liftAlongBaseChange B i s W q hq).val := rfl
  rw [hobj]
  exact ((IsPullback.of_hasPullback W.obj.hom i).map B.inclusion).hom_ext
    (geometricPointFiberBaseChangeEquiv_val_fst B i s W (liftAlongBaseChange B i s W q hq).val)
    ((geometricPointFiberBaseChangeEquiv_val_snd B i s W
      (liftAlongBaseChange B i s W q hq).val).trans hq.symm)

/-- Cofilteredness of the comma categories of the initial functor `pullbackNeighborhoodFunctor`:
a morphism between two base changes of pointed étale neighbourhoods becomes the base change of a
morphism after restricting along a common pointed étale neighbourhood. -/
private theorem pullbackNeighborhoodFunctor_exists_map_comp_eq
    [IsClosedImmersion (B.inclusion.map i)]
    {U V : (geometricPointFiber B X.1 X.property (s.map (B.inclusion.map i))).Elements}
    (f : (pullbackNeighborhoodFunctor B i s).obj U ⟶ (pullbackNeighborhoodFunctor B i s).obj V) :
    ∃ (W : (geometricPointFiber B X.1 X.property (s.map (B.inclusion.map i))).Elements)
      (a : W ⟶ U) (b : W ⟶ V),
      (pullbackNeighborhoodFunctor B i s).map a ≫ f =
        (pullbackNeighborhoodFunctor B i s).map b := by
  have := (Functor.initial_iff_isCofiltered_costructuredArrow _).1
    (pullbackNeighborhoodFunctor_initial B i s) ((pullbackNeighborhoodFunctor B i s).obj V)
  let A₁ : CostructuredArrow (pullbackNeighborhoodFunctor B i s)
      ((pullbackNeighborhoodFunctor B i s).obj V) :=
    CostructuredArrow.mk (𝟙 ((pullbackNeighborhoodFunctor B i s).obj V))
  let A₂ : CostructuredArrow (pullbackNeighborhoodFunctor B i s)
      ((pullbackNeighborhoodFunctor B i s).obj V) := CostructuredArrow.mk f
  let u₁ := IsCofiltered.minToLeft A₁ A₂
  let u₂ := IsCofiltered.minToRight A₁ A₂
  have h : (pullbackNeighborhoodFunctor B i s).map u₂.left ≫ f =
      (pullbackNeighborhoodFunctor B i s).map u₁.left ≫
        𝟙 ((pullbackNeighborhoodFunctor B i s).obj V) :=
    (CostructuredArrow.w u₂).trans (CostructuredArrow.w u₁).symm
  exact ⟨_, u₂.left, u₁.left, h.trans (Category.comp_id _)⟩

/-- Base change along a closed immersion is locally full: a morphism over `Z` between the base
changes of two étale schemes over `X` agrees, on a covering of its source, with the base change
of a morphism over `X`. -/
public instance smallEtaleBaseChange_isLocallyFull [IsClosedImmersion (B.inclusion.map i)] :
    (smallEtaleBaseChange B i).IsLocallyFull (SmallEtale.topology B Z.1 Z.property) := by
  refine ⟨fun {U V} f => ?_⟩
  apply SmallEtale.mem_topology_of_jointlySurjective
  intro y
  set t := geometricPointOfEtalePoint B Z.1 Z.property
    ((smallEtaleBaseChange B i).obj U) y
  set p := geometricPointOfEtalePointLift B Z.1 Z.property
    ((smallEtaleBaseChange B i).obj U) y
  have hpU : p.1 ≫ B.inclusion.map (pullback.snd U.obj.hom i) = t.hom := p.2
  have hfw : (SmallEtale.toScheme B Z.1 Z.property).map f ≫
      B.inclusion.map (pullback.snd V.obj.hom i) =
      B.inclusion.map (pullback.snd U.obj.hom i) :=
    (B.inclusion.map_comp f.hom.left (pullback.snd V.obj.hom i)).symm.trans
      (congrArg B.inclusion.map (Over.w f.hom))
  have hpV : (p.1 ≫ (SmallEtale.toScheme B Z.1 Z.property).map f) ≫
      B.inclusion.map (pullback.snd V.obj.hom i) = t.hom := by
    rwa [Category.assoc, hfw]
  set Ua := liftAlongBaseChange B i t U p.1 hpU
  set Va := liftAlongBaseChange B i t V
    (p.1 ≫ (SmallEtale.toScheme B Z.1 Z.property).map f) hpV
  have hU2 : ((pullbackNeighborhoodFunctor B i t).obj Ua).val.1 = p.1 :=
    liftAlongBaseChange_baseChange B i t U p.1 hpU
  have hV2 : ((pullbackNeighborhoodFunctor B i t).obj Va).val.1 =
      p.1 ≫ (SmallEtale.toScheme B Z.1 Z.property).map f :=
    liftAlongBaseChange_baseChange B i t V _ hpV
  let f' : (pullbackNeighborhoodFunctor B i t).obj Ua ⟶
      (pullbackNeighborhoodFunctor B i t).obj Va := ⟨f, by
    apply Subtype.ext
    change ((pullbackNeighborhoodFunctor B i t).obj Ua).val.1 ≫
      (SmallEtale.toScheme B Z.1 Z.property).map f =
      ((pullbackNeighborhoodFunctor B i t).obj Va).val.1
    rw [hU2, hV2]
    rfl⟩
  obtain ⟨W, a, b, hab⟩ := pullbackNeighborhoodFunctor_exists_map_comp_eq B i t f'
  have hlift : (smallEtaleBaseChange B i).map a.hom ≫ f = (smallEtaleBaseChange B i).map b.hom :=
    congrArg Functor.Elements.Hom.hom hab
  refine ⟨(smallEtaleBaseChange B i).obj W.obj, (smallEtaleBaseChange B i).map a.hom,
    ⟨W.obj, a.hom, 𝟙 _, ⟨b.hom, hlift.symm⟩, (Category.id_comp _).symm⟩, ?_⟩
  have hfac : ((pullbackNeighborhoodFunctor B i t).obj W).val.1 ≫
      (SmallEtale.toScheme B Z.1 Z.property).map ((smallEtaleBaseChange B i).map a.hom) =
      ((pullbackNeighborhoodFunctor B i t).obj Ua).val.1 :=
    congrArg Subtype.val ((pullbackNeighborhoodFunctor B i t).map a).map_val
  exact ⟨(((pullbackNeighborhoodFunctor B i t).obj W).val.1).base default,
    geometricPointOfEtalePointLift_base_of_comp_eq B Z.property y _ _ (hfac.trans hU2)⟩

end LocallyFull

section FullyFaithful

variable {Z X : B.Scheme} (i : Z ⟶ X) [IsClosedImmersion (B.inclusion.map i)]

/- **Stacks 04CA, part (2).** Direct image of abelian sheaves along a closed immersion is full and
faithful by Mathlib's instances for a cover-dense, locally full functor, fed by
`smallEtaleBaseChange_isCoverDense` and `smallEtaleBaseChange_isLocallyFull`. -/
add_to_stacks 04CA "part (2): fully faithful"
  CategoryTheory.Functor.IsCoverDense.full_sheafPushforwardContinuous
add_to_sga "4 III 4.1" "i) ⇒ ii)"
  CategoryTheory.Functor.IsCoverDense.full_sheafPushforwardContinuous
add_to_stacks 04CA "part (2): fully faithful"
  CategoryTheory.Functor.IsCoverDense.faithful_sheafPushforwardContinuous

/-- **Stacks 04CA.** The counit of the inverse image/direct image adjunction along a closed
immersion is an isomorphism on every abelian sheaf. -/
@[stacks 04CA "left inverse, abelian sheaves"]
public theorem smallEtaleAdjunction_counit_isIso_abelian
    (F : Sheaf (SmallEtale.topology B Z.1 Z.property) AddCommGrpCat.{u + 1}) :
    IsIso (((smallEtaleBaseChange B i).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.1 X.property)
      (SmallEtale.topology B Z.1 Z.property)).counit.app F) :=
  inferInstance

/-- **Stacks 04CA.** Inverse image along a closed immersion is a left inverse to direct image
on abelian sheaves: the counit of the adjunction is a natural isomorphism. -/
@[stacks 04CA "left inverse, abelian sheaves"]
public def smallEtalePushforwardCompPullbackIso :
    (smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.1 X.property)
        (SmallEtale.topology B Z.1 Z.property) ⋙
      (smallEtaleBaseChange B i).sheafPullback AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.1 X.property)
        (SmallEtale.topology B Z.1 Z.property) ≅
      𝟭 (Sheaf (SmallEtale.topology B Z.1 Z.property) AddCommGrpCat.{u + 1}) :=
  asIso (((smallEtaleBaseChange B i).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B X.1 X.property)
    (SmallEtale.topology B Z.1 Z.property)).counit)

end FullyFaithful

/-! ### Stalks and the essential image -/

/-- The stalk at a geometric point, as a functor on the abelian sheaves of the small étale
site: a sheaf is restricted along the projection from the category of pointed étale
neighbourhoods and the colimit is taken there. -/
public abbrev etaleStalkFunctorAbelian (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S) :
    Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  sheafToPresheaf _ _ ⋙ etaleStalkPresheafFunctor B S hS s AddCommGrpCat.{u + 1}

/-- **Stacks 03Q1 for abelian sheaves.** Inverse image of abelian sheaves on small étale sites
commutes with taking stalks at a geometric point: the stalk at `x` of the inverse image along
`f` is the stalk of the original sheaf at the image geometric point, naturally in the sheaf. -/
public def smallEtalePullbackStalkIsoAbelian {S T : B.Scheme} (f : T ⟶ S)
    (x : GeometricPoint T.1) :
    (smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{u + 1}
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property) ⋙
      etaleStalkFunctorAbelian B T.1 T.property x ≅
    etaleStalkFunctorAbelian B S.1 S.property (x.map (B.inclusion.map f)) := by
  let J := SmallEtale.topology B S.1 S.property
  let K := SmallEtale.topology B T.1 T.property
  let u := smallEtaleBaseChange B f
  let p := geometricPointSitePoint B S.1 S.property (x.map (B.inclusion.map f))
  let q := geometricPointSitePoint B T.1 T.property x
  haveI : PreservesLimitsOfShape (Discrete PEmpty.{1}) u :=
    Functor.preservesLimitsOfShape_pempty_of_isTerminal u
      (SmallEtale.finalIsTerminal B S.1 S.property)
      ((SmallEtale.finalIsTerminal B S.1 S.property).isTerminalObj u)
  letI : HasFiniteLimits (SmallEtale B S.1 S.property) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  letI : PreservesFiniteLimits u := preservesFiniteLimits_of_preservesTerminal_and_pullbacks u
  letI : RepresentablyFlat u := flat_of_preservesFiniteLimits u
  let hcover : CoverPreserving J K u := CoverPreserving.of_isContinuous u J K
  let eFiber : geometricPointFiber B S.1 S.property (x.map (B.inclusion.map f)) ≅
      u ⋙ geometricPointFiber B T.1 T.property x :=
    geometricPointFiberBaseChangeIso B f x
  let eElements := CategoryOfElements.equivalenceOfNatIso
    (C := SmallEtale B S.1 S.property)
    (P := geometricPointFiber B S.1 S.property (x.map (B.inclusion.map f)))
    (Q := u ⋙ geometricPointFiber B T.1 T.property x) eFiber
  haveI : InitiallySmall.{u} (u ⋙ geometricPointFiber B T.1 T.property x).Elements :=
    ⟨_, inferInstance, fromInitialModel.{u} p.fiber.Elements ⋙ eElements.functor,
      @Functor.initial_comp_equivalence _ _ _ _ _ _
        (fromInitialModel.{u} p.fiber.Elements) eElements.functor inferInstance
        eElements.isEquivalence_functor⟩
  haveI : InitiallySmall.{u} (u ⋙ q.fiber).Elements :=
    inferInstanceAs (InitiallySmall.{u} (u ⋙ geometricPointFiber B T.1 T.property x).Elements)
  letI : HasColimitsOfShape p.fiber.Elementsᵒᵖ AddCommGrpCat.{u + 1} :=
    hasColimitsOfShape_geometricPointFiber B S.1 S.property (x.map (B.inclusion.map f))
  letI : HasColimitsOfShape
      (u ⋙ geometricPointFiber B T.1 T.property x).Elementsᵒᵖ AddCommGrpCat.{u + 1} :=
    hasColimitsOfShape_of_finallySmall _ _
  let eStalk := Functor.isoWhiskerLeft (sheafToPresheaf J AddCommGrpCat.{u + 1})
    (CategoryOfElements.presheafColimIsoOfNatIsoOfCoefficients
      (A := AddCommGrpCat.{u + 1}) eFiber)
  let eComap := q.sheafFiberComapIso u hcover AddCommGrpCat.{u + 1}
  change (u.sheafPullback AddCommGrpCat.{u + 1} J K ⋙ q.sheafFiber) ≅ p.sheafFiber
  exact eComap.symm ≪≫ eStalk.symm

/-- A point of a scheme with values in a field lifts through a closed immersion as soon as its
image lies in the range of that immersion: the base change of the immersion along the point is
a surjective closed immersion onto the spectrum of the field, hence an isomorphism. -/
private lemma exists_lift_of_isClosedImmersion {Ω : Type u} [Field Ω] {W Y : Scheme.{u}}
    (f : W ⟶ Y) [IsClosedImmersion f] (a : Spec (.of Ω) ⟶ Y)
    (ha : a (IsLocalRing.closedPoint Ω) ∈ Set.range f) :
    ∃ b : Spec (.of Ω) ⟶ W, b ≫ f = a := by
  let q := pullback.snd f a
  have : Surjective q := ⟨fun z => by
    have hz : a z ∈ Set.range f := (Subsingleton.elim z (IsLocalRing.closedPoint Ω)) ▸ ha
    change z ∈ Set.range q
    rw [Scheme.Pullback.range_snd f a]
    exact hz⟩
  have : IsIso q := isIso_of_isClosedImmersion_of_surjective q
  refine ⟨inv q ≫ pullback.fst f a, ?_⟩
  rw [Category.assoc, pullback.condition]
  exact IsIso.inv_hom_id_assoc q a

section EssentialImage

variable {Z X : B.Scheme} (i : Z ⟶ X) [IsClosedImmersion (B.inclusion.map i)]

/-- **Stacks 04FX, the half away from the closed subscheme, for abelian sheaves.** The direct
image along a closed immersion of an abelian sheaf on the small étale site of the closed
subscheme has vanishing stalk at every geometric point of the ambient scheme whose image misses
that subscheme.

The forgetful functor of abelian groups preserves the filtered colimit defining the stalk, so
the underlying set of the stalk is the stalk of the underlying sheaf of sets, and that is a
singleton by the set-valued computation. -/
public theorem smallEtalePushforward_stalk_isZero_of_not_mem_range
    (G : Sheaf (SmallEtale.topology B Z.1 Z.property) AddCommGrpCat.{u + 1})
    (s : GeometricPoint X.1)
    (hs : s.hom default ∉ Set.range (B.inclusion.map i).base) :
    IsZero (etaleStalk B X.1 X.property s
      (((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.1 X.property)
        (SmallEtale.topology B Z.1 Z.property)).obj G).obj) := by
  have hunique := smallEtalePushforward_stalk_unique_of_not_mem_range.{u, u + 1} B i
    ((sheafCompose (SmallEtale.topology B Z.1 Z.property)
      (forget AddCommGrpCat.{u + 1})).obj G) s hs
  set D := SmallEtale.etaleStalkDiagram B X.1 X.property s
    (((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.1 X.property)
      (SmallEtale.topology B Z.1 Z.property)).obj G).obj
  have : Subsingleton (colimit (D ⋙ forget AddCommGrpCat.{u + 1})) :=
    ⟨fun a b => hunique.unique trivial trivial⟩
  have : Subsingleton ↑(colimit D) :=
    (preservesColimitIso (forget AddCommGrpCat.{u + 1}) D).toEquiv.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton (colimit D)

/-- A geometric point of the ambient scheme whose image lies in the closed subscheme is the
image of a geometric point of that subscheme, with the same residue field. -/
public theorem exists_geometricPoint_map_eq_of_mem_range (s : GeometricPoint X.1)
    (hs : s.hom default ∈ Set.range (B.inclusion.map i).base) :
    ∃ t : GeometricPoint Z.1, t.map (B.inclusion.map i) = s := by
  obtain ⟨z, hz⟩ := hs
  obtain ⟨b, hb⟩ := exists_lift_of_isClosedImmersion (B.inclusion.map i) s.hom
    ⟨z, hz.trans (congrArg s.hom.base (Subsingleton.elim _ _))⟩
  exact ⟨⟨s.residueField, b⟩,
    show (⟨s.residueField, b ≫ B.inclusion.map i⟩ : GeometricPoint X.1) = s by rw [hb]⟩

/-- The support of an abelian sheaf in the essential image of direct image along a closed
immersion is contained in the closed subscheme. -/
private theorem smallEtalePushforward_support_subset_of_mem_essImage
    (F : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})
    (hF : ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.1 X.property)
      (SmallEtale.topology B Z.1 Z.property)).essImage F) :
    SmallEtale.supportSheaf B X.1 X.property F ⊆ Set.range (B.inclusion.map i).base := by
  obtain ⟨G, ⟨e⟩⟩ := hF
  rintro x ⟨s, hlies, hnonzero⟩
  by_contra hxrange
  refine hnonzero (IsZero.of_iso
    (smallEtalePushforward_stalk_isZero_of_not_mem_range B i G s ?_)
    ((etaleStalkFunctorAbelian B X.1 X.property s).mapIso e.symm))
  rwa [hlies]

/-- **Stacks 04CA, part (2).** An abelian sheaf on the small étale site of `X` lies in the
essential image of direct image along a closed immersion `i : Z ⟶ X` exactly when its support
is contained in `Z`, that is, exactly when its stalk vanishes at every geometric point of `X`
whose image misses `Z`. -/
@[stacks 04CA "part (2): essential image"]
public theorem smallEtalePushforward_essImage_iff_abelian
    (F : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1}) :
    ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.1 X.property)
        (SmallEtale.topology B Z.1 Z.property)).essImage F ↔
      SmallEtale.supportSheaf B X.1 X.property F ⊆
        Set.range (B.inclusion.map i).base := by
  refine ⟨smallEtalePushforward_support_subset_of_mem_essImage B i F, fun hsupport => ?_⟩
  set pf := (smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B X.1 X.property) (SmallEtale.topology B Z.1 Z.property)
  set pb := (smallEtaleBaseChange B i).sheafPullback AddCommGrpCat.{u + 1}
    (SmallEtale.topology B X.1 X.property) (SmallEtale.topology B Z.1 Z.property)
  set adj := (smallEtaleBaseChange B i).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B X.1 X.property) (SmallEtale.topology B Z.1 Z.property)
  have hunit : IsIso (adj.unit.app F) := by
    refine isIso_of_isIso_etaleStalkMap B X.1 X.property (adj.unit.app F) fun s => ?_
    by_cases hs : s.hom default ∈ Set.range (B.inclusion.map i).base
    · obtain ⟨t, rfl⟩ := exists_geometricPoint_map_eq_of_mem_range B i s hs
      have hcounit : IsIso (adj.counit.app (pb.obj F)) :=
        smallEtaleAdjunction_counit_isIso_abelian B i _
      have htriangle : pb.map (adj.unit.app F) ≫ adj.counit.app (pb.obj F) = 𝟙 _ :=
        adj.left_triangle_components F
      have hcomp : IsIso (pb.map (adj.unit.app F) ≫ adj.counit.app (pb.obj F)) := by
        rw [htriangle]
        infer_instance
      have hpullback : IsIso (pb.map (adj.unit.app F)) :=
        IsIso.of_isIso_comp_right _ (adj.counit.app (pb.obj F))
      exact (NatIso.isIso_map_iff (smallEtalePullbackStalkIsoAbelian B i t) (adj.unit.app F)).mp
        (Functor.map_isIso (etaleStalkFunctorAbelian B Z.1 Z.property t) (pb.map (adj.unit.app F)))
    · have hsource : IsZero (etaleStalk B X.1 X.property s F.obj) :=
        of_not_not fun h => hs (hsupport ⟨s, rfl, h⟩)
      have htarget : IsZero (etaleStalk B X.1 X.property s (pf.obj (pb.obj F)).obj) :=
        smallEtalePushforward_stalk_isZero_of_not_mem_range B i (pb.obj F) s hs
      have hmap : (etaleStalkPresheafFunctor B X.1 X.property s AddCommGrpCat.{u + 1}).map
          (adj.unit.app F).hom = (hsource.iso htarget).hom :=
        hsource.eq_of_src _ _
      rw [hmap]
      exact inferInstanceAs (IsIso (hsource.iso htarget).hom)
  exact adj.mem_essImage_of_unit_isIso F

end EssentialImage

end AlgebraicGeometry

end
