module

public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.GroupoidRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteLocalSurjectivity
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Continuous

/-!
# Quotient sheaves of a groupoid restricted along a map with open saturation

Let `G` be a groupoid scheme over `S` with scheme of objects `U` and scheme of arrows `R`,
and let `g : U' ⟶ U` be a morphism of `S`-schemes. The *saturation* of `g` is the image of
the reach map `U' ×_{g, U, t} R ⟶ U`, which reads off the source of an arrow whose target
lifts along `g`. When that image is an open subscheme `W ⊂ U` and the reach map factors
through `W` by a morphism inducing a surjection of fppf sheaves, the map of quotient
sheaves `U'/R' ⟶ U/R` induced by the restriction of `G` along `g` is a representable open
immersion of sheaves on the big fppf site of `S`.

## Main results

* `AlgebraicGeometry.GroupoidScheme.isOpenImmersion_restrictionQuotientMap_of_open_image`:
  **Stacks 046M**, the open immersion of quotient sheaves.

## Implementation notes

The saturation is presented by an open immersion `i : W ⟶ U` of `S`-schemes together with
the equality of its range with the range of
`AlgebraicGeometry.GroupoidScheme.restrictionReachMap`; the factorization is a morphism `k`
with `k ≫ i` the reach map, and fppf-surjectivity is local surjectivity of the map of
sheafified functors of points induced by `k`. The conclusion is
`AlgebraicGeometry.Space.IsOpenImmersion`, which includes representability.

The subsheaf of `U/R` cut out by `W` is obtained by classifying points: a point of `U` over
a test object is sent to the open subset of that object where it lands in `W`, which is a
continuous map to the Sierpiński space, so the functor of points of `U` maps to the
restriction of `AlgebraicGeometry.continuousMapPresheaf Prop`. The range of `i` is invariant
under the groupoid, because the relation induced on points by the pre-relation underlying a
groupoid scheme is an equivalence relation (Stacks 022Q), so this classifying map descends
to the quotient sheaf. The subfunctor where the descended classifier is identically true is
a sheaf, the map from `U'/R'` factors through it, and the factorization is an isomorphism:
it is injective because `U'/R' ⟶ U/R` is (Stacks 02VH), and surjective because a local
section of `U/R` landing in `W` lifts through the open immersion `i`, whose own
factorization through the subfunctor is locally surjective by the hypothesis on `k`.

That the inclusion of the subfunctor is a representable open immersion is checked on a
single test object: the classifier of a point of `U/R` over an object `A` of the site is a
continuous `Prop`-valued map on `A`, hence an open subscheme of `A`, which is again an
object of the site because an open subscheme does not exceed the size of its ambient
scheme; the inclusion of that open subscheme is the required base change.

The restriction of `AlgebraicGeometry.continuousMapPresheaf Prop` to the big fppf site of
`S` is a sheaf because the presheaf is an fpqc sheaf, hence an fppf sheaf, and the functor
from the big fppf site of `S` to schemes is continuous for the fppf topology by
`AlgebraicGeometry.BigFppfSite.isContinuous_inclusion`.

## References

* [Stacks Project, Tag 046M](https://stacks.math.columbia.edu/tag/046M)
* [Stacks Project, Tag 02VH](https://stacks.math.columbia.edu/tag/02VH)
* [Stacks Project, Tag 022Q](https://stacks.math.columbia.edu/tag/022Q)
* [Stacks Project, Tag 02WU](https://stacks.math.columbia.edu/tag/02WU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u v w

namespace AlgebraicGeometry

/-- The characteristic function of an open subscheme of the target of a morphism of schemes,
as a continuous map to the Sierpiński space. -/
private noncomputable def openCharacteristicMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) : C(X, Prop) :=
  ⟨fun x => f.base x ∈ V, continuous_Prop.mpr (V.2.preimage f.continuous)⟩

/-- The classifying map of an open subscheme `V` of an `S`-scheme `U`: a point of `U` over a
test object of the site is sent to the open subset of that object on which it lands in
`V`. -/
private noncomputable def openCharacteristicNatTrans
    {S : Scheme.{u}} {C : Type v} [Category.{w} C]
    (F : C ⥤ Over S) (U : Over S) (V : U.left.Opens) :
    points F U ⟶ F.op ⋙ (Over.forget S).op ⋙ continuousMapPresheaf Prop := by
  refine ⟨fun X => ↾fun a => openCharacteristicMap a.left V, ?_⟩
  intro X Y f
  ext a
  rfl

/-- The restriction of the presheaf of continuous `Prop`-valued maps along a functor which is
continuous for the fppf topology is a sheaf. -/
private theorem isSheaf_op_comp_continuousMapPresheaf
    {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) (F : C ⥤ Scheme.{u})
    [Functor.IsContinuous F J Scheme.fppfTopology] :
    Presheaf.IsSheaf J (F.op ⋙ continuousMapPresheaf Prop) := by
  apply (isSheaf_iff_isSheaf_of_type J _).2
  exact F.op_comp_isSheaf_of_types J Scheme.fppfTopology
    ⟨continuousMapPresheaf Prop,
      (isSheaf_fpqcTopology_continuousMapPresheaf Prop).of_le
        Scheme.fppfTopology_le_fpqcTopology⟩

/-- The functor from the big fppf site of `S` to schemes, factored through `S`-schemes, is
continuous for the fppf topology. -/
private theorem isContinuous_post_inclusion_comp_forget (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    Functor.IsContinuous (Over.post (X := B.obj hS) B.inclusion ⋙ Over.forget S)
      (BigFppfOver.topology B S hS) Scheme.fppfTopology := by
  have hF : Over.post (X := B.obj hS) B.inclusion ⋙ Over.forget S =
      BigFppfOver.toScheme B S hS := by
    dsimp [BigFppfOver.toScheme, BigFppfOver.forget]
    exact Over.post_forget_eq_forget_comp B.inclusion (B.obj hS)
  rw [hF]
  exact Functor.isContinuous_comp (Over.forget (B.obj hS)) B.inclusion
    (B.topology.over (B.obj hS)) B.topology Scheme.fppfTopology

/-- The presheaf of continuous `Prop`-valued maps, restricted to the big fppf site of `S`, is
a sheaf. -/
private theorem isSheaf_continuousMapPresheaf_prop (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      ((Over.post (X := B.obj hS) B.inclusion).op ⋙ (Over.forget S).op ⋙
        continuousMapPresheaf Prop) := by
  let F := Over.post (X := B.obj hS) B.inclusion ⋙ Over.forget S
  let _ : Functor.IsContinuous F (BigFppfOver.topology B S hS) Scheme.fppfTopology :=
    isContinuous_post_inclusion_comp_forget B S hS
  exact isSheaf_op_comp_continuousMapPresheaf (BigFppfOver.topology B S hS) F

namespace GroupoidScheme

/-- The identity arrow gives a section of the reach map over `g`. -/
private theorem exists_comp_restrictionReachMap_eq
    {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects) :
    ∃ e : U' ⟶ pullback g G.target, e ≫ restrictionReachMap G g = g :=
  ⟨pullback.lift (𝟙 U') (g ≫ G.identity) (by simp [G.target_identity]), by
    change _ ≫ pullback.snd g G.target ≫ G.source = g
    rw [← Category.assoc, pullback.lift_snd, Category.assoc, G.source_identity,
      Category.comp_id]⟩

/-- The restricting map factors through the reach map, through the identity arrow. -/
private theorem range_le_restrictionReachMap
    {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects) :
    Set.range g.left.base ⊆ Set.range (restrictionReachMap G g).left.base := by
  obtain ⟨e, he⟩ := exists_comp_restrictionReachMap_eq G g
  rintro x ⟨y, rfl⟩
  exact ⟨e.left.base y, congrArg (fun f : U' ⟶ G.objects => f.left.base y) he⟩

/-- The range of the second projection of a fibre product of `S`-schemes is the preimage of
the range of the other map. -/
private theorem range_snd_over
    {S : Scheme.{u}} {A B C : Over S} (f : A ⟶ C) (g : B ⟶ C) :
    Set.range (pullback.snd f g).left.base =
      g.left.base ⁻¹' Set.range f.left.base := by
  let e := PreservesPullback.iso (Over.forget S) f g
  have hs : e.hom ≫ pullback.snd f.left g.left =
      (Over.forget S).map (pullback.snd f g) :=
    PreservesPullback.iso_hom_snd (Over.forget S) f g
  change Set.range (((Over.forget S).map (pullback.snd f g)).base) = _
  rw [← hs]
  change Set.range ((pullback.snd f.left g.left).base ∘ e.hom.base) = _
  rw [Set.range_comp]
  have hbij := ConcreteCategory.bijective_of_isIso e.hom.base
  rw [Set.range_eq_univ.mpr hbij.2, Set.image_univ, Scheme.Pullback.range_snd]

/-- The saturation of `g`: the range of the reach map is the set of sources of arrows whose
target lifts along `g`. -/
private theorem range_restrictionReachMap_eq
    {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects) :
    Set.range (restrictionReachMap G g).left.base =
      G.source.left.base '' (G.target.left.base ⁻¹' Set.range g.left.base) := by
  change Set.range
      (G.source.left.base ∘ (pullback.snd g G.target).left.base) = _
  rw [Set.range_comp, range_snd_over]

/-- The inverse of an arrow has the target of the arrow as its source. -/
private theorem source_inverse_apply {S : Scheme.{u}} (G : GroupoidScheme S) (r : G.arrows.left) :
    G.source.left.base (G.inverse.left.base r) = G.target.left.base r := by
  simpa [Scheme.Hom.comp_apply] using
    congrArg (fun f : Scheme.Hom G.arrows.left G.objects.left => f.base r)
      (congrArg (fun f : G.arrows ⟶ G.objects => f.left) G.source_inverse)

/-- The inverse of an arrow has the source of the arrow as its target. -/
private theorem target_inverse_apply {S : Scheme.{u}} (G : GroupoidScheme S) (r : G.arrows.left) :
    G.target.left.base (G.inverse.left.base r) = G.source.left.base r := by
  simpa [Scheme.Hom.comp_apply] using
    congrArg (fun f : Scheme.Hom G.arrows.left G.objects.left => f.base r)
      (congrArg (fun f : G.arrows ⟶ G.objects => f.left) G.target_inverse)

/-- The saturation of `g` is invariant under the groupoid: the relation induced on points by
the pre-relation underlying a groupoid scheme is an equivalence relation. -/
private theorem range_restrictionReachMap_invariant
    {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects) :
    ∀ r : G.arrows.left,
      G.source.left.base r ∈ Set.range (restrictionReachMap G g).left.base →
      G.target.left.base r ∈ Set.range (restrictionReachMap G g).left.base := by
  rw [range_restrictionReachMap_eq]
  intro r hr
  rcases hr with ⟨a, ha, has⟩
  have hE : Equivalence
      (Function.SourceTargetRel G.source.left.base G.target.left.base) := by
    simpa [groupoidPreRelation, PreRelation.target, PreRelation.source] using
      AlgebraicGeometry.PreRelation.equivalence_sourceTargetRel (groupoidPreRelation G)
        (groupoidPreRelation_isPreEquivalenceRelation G)
  have hrel₁ : Function.SourceTargetRel G.source.left.base G.target.left.base
      (G.target.left.base a) (G.source.left.base a) := ⟨a, rfl, rfl⟩
  have hrel₂ : Function.SourceTargetRel G.source.left.base G.target.left.base
      (G.source.left.base a) (G.target.left.base r) := by
    refine ⟨G.inverse.left.base r, ?_, ?_⟩
    · exact (target_inverse_apply G r).trans has.symm
    · exact source_inverse_apply G r
  rcases hE.trans hrel₁ hrel₂ with ⟨b, hb₁, hb₂⟩
  exact ⟨b, by simpa [hb₁] using ha, hb₂⟩

/-- An open subscheme whose range is the saturation of `g` is an invariant open. -/
private theorem openImage_invariant
    {S : Scheme.{u}} (G : GroupoidScheme S) {U' W : Over S}
    (g : U' ⟶ G.objects) (i : W ⟶ G.objects)
    [IsOpenImmersion i.left]
    (himage : Set.range i.left.base =
      Set.range (restrictionReachMap G g).left.base) :
    IsInvariantOpen G i.left.opensRange := by
  change ∀ r : G.arrows.left,
    G.source.left.base r ∈ Set.range i.left.base →
      G.target.left.base r ∈ Set.range i.left.base
  rw [himage]
  intro r hr
  exact range_restrictionReachMap_invariant G g r hr

/-- For an invariant subset of the object scheme the source and the target maps have the same
preimage: the inverse of an arrow starting outside carries the witness back. -/
private theorem invariantSet_source_preimage_eq_target
    {S : Scheme.{u}} (G : GroupoidScheme S)
    (W : Set G.objects.left) (hW : IsInvariantSet G W) :
    G.source.left.base ⁻¹' W = G.target.left.base ⁻¹' W := by
  refine Set.Subset.antisymm (hW ·) fun r hr => ?_
  change G.source.left.base r ∈ W
  rw [← target_inverse_apply G r]
  exact hW _ (by rw [source_inverse_apply]; exact hr)

/-- The classifying map of an invariant open identifies related points, hence descends to the
quotient sheaf. -/
private theorem openCharacteristicNatTrans_groupoid_compatible
    {S : Scheme.{u}} {C : Type v} [Category.{w} C]
    (F : C ⥤ Over S) (G : GroupoidScheme S)
    (W : G.objects.left.Opens) (hW : IsInvariantOpen G W) :
    sourceMap F (groupoidPreRelation G) ≫ openCharacteristicNatTrans F G.objects W =
      targetMap F (groupoidPreRelation G) ≫ openCharacteristicNatTrans F G.objects W := by
  ext X r
  apply ContinuousMap.ext; intro x
  have hEq := invariantSet_source_preimage_eq_target G W hW
  dsimp [sourceMap, targetMap, groupoidPreRelation, PreRelation.source, PreRelation.target,
    openCharacteristicNatTrans]
  simp only [prod.lift_snd, prod.lift_fst, ConcreteCategory.hom_ofHom]
  change (openCharacteristicMap (r ≫ G.source).left W) x =
    (openCharacteristicMap (r ≫ G.target).left W) x
  change ((r ≫ G.source).left x ∈ W) =
    ((r ≫ G.target).left x ∈ W)
  have hpoint := congrArg (fun A : Set G.arrows.left => A (r.left x)) hEq
  change (G.source.left.base (r.left.base x) ∈ W) =
    (G.target.left.base (r.left.base x) ∈ W) at hpoint
  simpa only [Over.comp_left, Scheme.Hom.comp_apply] using hpoint

/-- A morphism of `S`-schemes whose range is contained in the range of an open immersion
factors through it. -/
private noncomputable def factorThroughOpenSubset
    {S : Scheme.{u}} {U' W V : Over S} (g : U' ⟶ V)
    (i : W ⟶ V) [IsOpenImmersion i.left]
    (hsubset : Set.range g.left.base ⊆ Set.range i.left.base) : U' ⟶ W := by
  have hsubset' : Set.range g.left ⊆ Set.range i.left := by simpa using hsubset
  let l : U'.left ⟶ W.left := IsOpenImmersion.lift i.left g.left hsubset'
  have hl : l ≫ i.left = g.left := IsOpenImmersion.lift_fac i.left g.left _
  exact Over.homMk l (by
    calc
      l ≫ W.hom = (l ≫ i.left) ≫ V.hom := by
        rw [← i.w, Category.assoc]
      _ = g.left ≫ V.hom := by rw [hl]
      _ = U'.hom := g.w)

/-- The factorization through an open immersion is a factorization. -/
private theorem factorThroughOpenSubset_fac
    {S : Scheme.{u}} {U' W V : Over S} (g : U' ⟶ V)
    (i : W ⟶ V) [IsOpenImmersion i.left]
    (hsubset : Set.range g.left.base ⊆ Set.range i.left.base) :
    factorThroughOpenSubset g i hsubset ≫ i = g := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac i.left g.left _

/-- The subfunctor on which a classifying map into the presheaf of continuous `Prop`-valued
maps is identically true. -/
private def classifierTrueSubfunctor
    {S : Scheme.{u}} {C : Type v} [Category.{w} C]
    (F : C ⥤ Over S) (Q : Cᵒᵖ ⥤ Type u)
    (c : Q ⟶ F.op ⋙ (Over.forget S).op ⋙ continuousMapPresheaf Prop) :
    Subfunctor Q where
  obj X := {x | ∀ z : (F.obj X.unop).left, (c.app X x).toFun z}
  map {X Y} f := by
    change ∀ x, (∀ z : (F.obj X.unop).left, (c.app X x).toFun z) →
      ∀ z : (F.obj Y.unop).left, (c.app Y (Q.map f x)).toFun z
    intro x hx z
    have hn := c.naturality_apply f x
    have hev := congrArg (fun p : C((F.obj Y.unop).left, Prop) => p.toFun z) hn
    have hev' : (c.app Y (Q.map f x)).toFun z ↔
        (c.app X x).toFun ((F.map f.unop).left.base z) := by
      change (c.app Y (Q.map f x)).toFun z ↔
        ((c.app X x).comp ((F.map f.unop).left.base.hom)) z
      exact Iff.of_eq hev
    exact hev'.mpr (hx ((F.map f.unop).left.base.hom z))

/-- The classifying map which is constantly true. -/
private def constantTrueNatTrans
    {S : Scheme.{u}} {C : Type v} [Category.{w} C]
    (F : C ⥤ Over S) (Q : Cᵒᵖ ⥤ Type u) :
    Q ⟶ F.op ⋙ (Over.forget S).op ⋙ continuousMapPresheaf Prop where
  app X := ↾fun (_ : Q.obj X) => ContinuousMap.const ((F.obj X.unop).left) True
  naturality := by
    intro X Y f
    ext x
    apply ContinuousMap.ext
    intro z
    rfl

/-- The subfunctor on which a classifying map is identically true is a sheaf whenever its
source and target are. -/
private theorem classifierTrueSubfunctor_isSheaf
    {S : Scheme.{u}} {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type u)]
    (F : C ⥤ Over S) (Q : Cᵒᵖ ⥤ Type u)
    (c : Q ⟶ F.op ⋙ (Over.forget S).op ⋙ continuousMapPresheaf Prop)
    (hQ : Presieve.IsSheaf J Q)
    (hC : Presieve.IsSheaf J
      (F.op ⋙ (Over.forget S).op ⋙ continuousMapPresheaf Prop)) :
    Presieve.IsSheaf J (classifierTrueSubfunctor F Q c).toFunctor := by
  rw [(classifierTrueSubfunctor F Q c).isSheaf_iff hQ]
  intro X x hx
  let cTrue := constantTrueNatTrans F Q
  have heq : c.app X x = cTrue.app X x := by
    apply (hC.isSeparated
      ((classifierTrueSubfunctor F Q c).sieveOfSection x) hx).ext
    intro Y f hf
    have hmem : Q.map f.op x ∈ (classifierTrueSubfunctor F Q c).obj (Opposite.op Y) := hf
    have hn := c.naturality_apply f.op x
    have hnt := cTrue.naturality_apply f.op x
    change ∀ z, (c.app (Opposite.op Y) (Q.map f.op x)).toFun z at hmem
    change ((F.op ⋙ (Over.forget S).op ⋙ continuousMapPresheaf Prop).map f.op)
        (c.app X x) =
      ((F.op ⋙ (Over.forget S).op ⋙ continuousMapPresheaf Prop).map f.op)
        (cTrue.app X x)
    rw [← hn, ← hnt]
    apply ContinuousMap.ext
    intro z
    apply propext
    change (c.app (Opposite.op Y) (Q.map f.op x)).toFun z ↔ True
    exact ⟨fun _ => trivial, fun _ => hmem z⟩
  intro z
  rw [heq]
  trivial

/-- The map from the sheafified functor of points of `U` to the quotient sheaf of a
pre-relation on `U`. -/
private noncomputable def quotientPointMap
    {S : Scheme.{u}} {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type u)]
    (F : C ⥤ Over S) {R U : Over S} (j : PreRelation R U) :
    (presheafToSheaf J (Type u)).obj (points F U) ⟶ quotientSheaf J F j :=
  ⟨sheafifyLift J (toQuotientSheaf J F j) (quotientSheaf J F j).property⟩

/-- The map from the sheafified functor of points agrees with the canonical projection. -/
private theorem toSheafify_comp_quotientPointMap
    {S : Scheme.{u}} {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type u)]
    (F : C ⥤ Over S) {R U : Over S} (j : PreRelation R U) :
    toSheafify J (points F U) ≫ (quotientPointMap J F j).hom = toQuotientSheaf J F j :=
  toSheafify_sheafifyLift J (toQuotientSheaf J F j) (quotientSheaf J F j).property

/-- **Stacks 046M.** Let `G` be a groupoid scheme over `S` and let `g : U' ⟶ U` be a morphism
to its scheme of objects whose saturation is the range of an open immersion `i : W ⟶ U`. If
the reach map factors as `k ≫ i` with `k` inducing a surjection of fppf sheaves, then the map
of quotient sheaves `U'/R' ⟶ U/R` induced by the restriction of `G` along `g` is a
representable open immersion. -/
@[stacks 046M]
theorem isOpenImmersion_restrictionQuotientMap_of_open_image
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (G : GroupoidScheme S) {U' W : Over S}
    (g : U' ⟶ G.objects) (i : W ⟶ G.objects)
    [IsOpenImmersion i.left]
    (k : pullback g G.target ⟶ W)
    (hk : k ≫ i = restrictionReachMap G g)
    (himage : Set.range i.left.base =
      Set.range (restrictionReachMap G g).left.base)
    (hsurj : Sheaf.IsLocallySurjective
      ((presheafToSheaf (BigFppfOver.topology B S hS) (Type u)).map
        ((Over.post B.inclusion).op.whiskerLeft (yoneda.map k)))) :
    Space.IsOpenImmersion B S hS
      (restrictionQuotientMap (BigFppfOver.topology B S hS) (Over.post B.inclusion) G g
        (restrict G g)).1 := by
  let J := BigFppfOver.topology B S hS
  let F : BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  let jG := groupoidPreRelation G
  let A : Sheaf J (Type u) :=
    ⟨F.op ⋙ (Over.forget S).op ⋙ continuousMapPresheaf Prop,
      isSheaf_continuousMapPresheaf_prop B S hS⟩
  let χ := openCharacteristicNatTrans F G.objects i.left.opensRange
  have hχ : sourceMap F jG ≫ χ = targetMap F jG ≫ χ := by
    exact openCharacteristicNatTrans_groupoid_compatible F G i.left.opensRange
      (openImage_invariant G g i himage)
  let cG := quotientSheafDesc J F jG A χ hχ
  have hcG : toQuotientSheaf J F jG ≫ cG.hom = χ := by
    exact toQuotientSheaf_quotientSheafDesc J F jG A χ hχ
  let H := restrict G g
  let jH := groupoidPreRelation H.groupoid
  let q := restrictionQuotientMap J F G g H
  let χH := openCharacteristicNatTrans F H.groupoid.objects ⊤
  have hχH : sourceMap F jH ≫ χH = targetMap F jH ≫ χH := by
    exact openCharacteristicNatTrans_groupoid_compatible F H.groupoid ⊤ (by
      intro r hr
      simp)
  let cH := quotientSheafDesc J F jH A χH hχH
  have hcH : toQuotientSheaf J F jH ≫ cH.hom = χH := by
    exact toQuotientSheaf_quotientSheafDesc J F jH A χH hχH
  let cTrue : quotientSheaf J F jH ⟶ A :=
    ⟨constantTrueNatTrans F (quotientSheaf J F jH).obj⟩
  have hcTrue : toQuotientSheaf J F jH ≫ cTrue.hom = χH := by
    ext X a; apply ContinuousMap.ext; intro x; rfl
  have hcHTrue : cH = cTrue := by
    symm; exact quotientSheafDesc_unique J F jH A χH hχH cTrue hcTrue
  have hmapχ :
      F.op.whiskerLeft (yoneda.map H.hom.mapObjects) ≫ χ = χH := by
    ext X a; apply ContinuousMap.ext; intro x
    change ((a ≫ H.hom.mapObjects).left.base x ∈ i.left.opensRange) = True
    have hfactor : H.hom.mapObjects.left =
        (eqToHom H.objects_eq ≫ g).left := congrArg Over.Hom.left H.mapObjects_eq
    have hpoint : (a ≫ H.hom.mapObjects).left.base x ∈
        Set.range g.left.base := by
      refine ⟨(eqToHom H.objects_eq).left.base (a.left.base x), ?_⟩
      change g.left.base ((eqToHom H.objects_eq).left.base (a.left.base x)) =
        H.hom.mapObjects.left.base (a.left.base x)
      have hf := congrArg
        (fun m : Scheme.Hom H.groupoid.objects.left G.objects.left =>
          m.base (a.left.base x)) hfactor
      simpa [Scheme.Hom.comp_apply] using hf.symm
    have hrange : Set.range g.left.base ⊆ Set.range i.left.base := by
      rw [himage]
      exact range_le_restrictionReachMap G g
    have hmem := hrange hpoint
    change (a ≫ H.hom.mapObjects).left.base x ∈ Set.range i.left.base at hmem
    simpa [openCharacteristicNatTrans, openCharacteristicMap,
      Scheme.Hom.opensRange] using hmem
  have hqproj : toQuotientSheaf J F jH ≫ q.hom =
      F.op.whiskerLeft (yoneda.map H.hom.mapObjects) ≫ toQuotientSheaf J F jG := by
    change toQuotientSheaf J F jH ≫
      (quotientSheafMap J F jH jG H.hom.mapArrows H.hom.mapObjects _ _).hom = _
    exact toQuotientSheaf_comp_quotientSheafMap J F jH jG
      H.hom.mapArrows H.hom.mapObjects _ _
  have hdesc : q ≫ cG = cH := by
    exact quotientSheafDesc_unique J F jH A χH hχH (q ≫ cG) (by
      change (toQuotientSheaf J F jH ≫ q.hom) ≫ cG.hom = χH
      calc
        (toQuotientSheaf J F jH ≫ q.hom) ≫ cG.hom =
            (F.op.whiskerLeft (yoneda.map H.hom.mapObjects) ≫
              toQuotientSheaf J F jG) ≫ cG.hom := by rw [hqproj]
        _ = F.op.whiskerLeft (yoneda.map H.hom.mapObjects) ≫ χ := by
              rw [Category.assoc, hcG]
        _ = χH := hmapχ)
  let QG := quotientSheaf J F jG
  let TTrue := classifierTrueSubfunctor F QG.obj cG.hom
  have hTTrue : Presieve.IsSheaf J TTrue.toFunctor :=
    classifierTrueSubfunctor_isSheaf J F QG.obj cG.hom
      ((isSheaf_iff_isSheaf_of_type J _).mp QG.property)
      ((isSheaf_iff_isSheaf_of_type J _).mp A.property)
  have hqrange : Subfunctor.range q.hom ≤ TTrue := by
    intro X y hy
    rcases hy with ⟨x, rfl⟩
    intro z
    have h₁ : cG.hom.app X (q.hom.app X x) = cH.hom.app X x :=
      congrArg (fun f : quotientSheaf J F jH ⟶ A => f.hom.app X x) hdesc
    have h₂ : cH.hom.app X x = cTrue.hom.app X x :=
      congrArg (fun f : quotientSheaf J F jH ⟶ A => f.hom.app X x) hcHTrue
    change (cG.hom.app X (q.hom.app X x)).toFun z
    rw [h₁, h₂]
    trivial
  let qT := Subfunctor.lift q.hom hqrange
  have hqfactor : qT ≫ TTrue.ι = q.hom := Subfunctor.lift_ι q.hom hqrange
  have hqTmono : Mono qT := by
    have hqmono : Mono q.hom := by
      have : Mono q := mono_restrictionQuotientMap J F G g H
      infer_instance
    let _ : Mono q.hom := hqmono
    exact mono_of_mono_fac hqfactor
  let mapW := F.op.whiskerLeft (yoneda.map i)
  have hWrange : Subfunctor.range (mapW ≫ toQuotientSheaf J F jG) ≤ TTrue := by
    intro X y hy
    rcases hy with ⟨a, rfl⟩
    intro z
    have hχ : cG.hom.app X ((toQuotientSheaf J F jG).app X (mapW.app X a)) =
        χ.app X (mapW.app X a) := by
      have h := congrArg (fun n => n.app X (mapW.app X a)) hcG
      simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using h
    have hχ' : cG.hom.app X ((mapW ≫ toQuotientSheaf J F jG).app X a) =
        χ.app X (mapW.app X a) := by
      simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using hχ
    change (cG.hom.app X ((mapW ≫ toQuotientSheaf J F jG).app X a)).toFun z
    rw [hχ']
    change ((mapW.app X a).left.base z ∈ i.left.opensRange)
    have hmem : (mapW.app X a).left.base z ∈ Set.range i.left.base :=
      ⟨a.left.base z, rfl⟩
    simpa [Scheme.Hom.opensRange] using hmem
  let uW : points F W ⟶ TTrue.toFunctor :=
    Subfunctor.lift (mapW ≫ toQuotientSheaf J F jG) hWrange
  have hTTrueP : Presheaf.IsSheaf J TTrue.toFunctor :=
    (isSheaf_iff_isSheaf_of_type J _).mpr hTTrue
  let QT : Sheaf J (Type u) := ⟨TTrue.toFunctor, hTTrueP⟩
  let ψW : (presheafToSheaf J (Type u)).obj (points F W) ⟶ QT :=
    ⟨sheafifyLift J uW hTTrueP⟩
  have hψW : Sheaf.IsLocallySurjective ψW := by
    change Presheaf.IsLocallySurjective J ψW.hom
    constructor
    intro X t
    let hqpt := toQuotientSheaf_isLocallySurjective J F jG
    have hI : Presheaf.imageSieve (toQuotientSheaf J F jG) t.val ∈ J X :=
      hqpt.imageSieve_mem t.val
    apply J.superset_covering ?_ hI
    intro Y f hf
    rcases hf with ⟨a, ha⟩
    have hmem : (QG.obj.map f.op t.val) ∈ TTrue.obj (Opposite.op Y) :=
      TTrue.map f.op t.property
    have htrueRep : ∀ z : (F.obj Y).left,
        (cG.hom.app (Opposite.op Y)
          ((toQuotientSheaf J F jG).app (Opposite.op Y) a)).toFun z := by
      intro z
      have heq := congrArg (fun y => cG.hom.app (Opposite.op Y) y) ha
      rw [heq]
      change ∀ z, (cG.hom.app (Opposite.op Y) (QG.obj.map f.op t.val)).toFun z at hmem
      exact hmem z
    have hχrep : cG.hom.app (Opposite.op Y)
        ((toQuotientSheaf J F jG).app (Opposite.op Y) a) =
        χ.app (Opposite.op Y) a := by
      have h := congrArg (fun n => n.app (Opposite.op Y) a) hcG
      simpa [NatTrans.comp_app, ConcreteCategory.comp_apply] using h
    have hχtrue : ∀ z : (F.obj Y).left, (χ.app (Opposite.op Y) a).toFun z := by
      intro z
      rw [← hχrep]
      exact htrueRep z
    have hsubset : Set.range a.left.base ⊆ Set.range i.left.base := by
      rintro _ ⟨z, rfl⟩
      have hz := hχtrue z
      change a.left.base z ∈ i.left.opensRange at hz
      simpa [Scheme.Hom.opensRange] using hz
    let aW := factorThroughOpenSubset a i hsubset
    refine ⟨(toSheafify J (points F W)).app (Opposite.op Y) aW, ?_⟩
    apply Subtype.ext
    have heqW : aW ≫ i = a := factorThroughOpenSubset_fac a i hsubset
    have hunit := toSheafify_sheafifyLift J uW hTTrueP
    have happ : (ψW.hom.app (Opposite.op Y)
        ((toSheafify J (points F W)).app (Opposite.op Y) aW)) =
      uW.app (Opposite.op Y) aW := by
      change (sheafifyLift J uW hTTrueP).app (Opposite.op Y)
          ((toSheafify J (points F W)).app (Opposite.op Y) aW) = _
      have h := congrArg (fun n => n.app (Opposite.op Y) aW) hunit
      simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using h
    change (ψW.hom.app (Opposite.op Y)
        ((toSheafify J (points F W)).app (Opposite.op Y) aW)).val =
      (TTrue.toFunctor.map f.op t).val
    rw [congrArg Subtype.val happ]
    change (toQuotientSheaf J F jG).app (Opposite.op Y)
        (mapW.app (Opposite.op Y) aW) = QG.obj.map f.op t.val
    change (toQuotientSheaf J F jG).app (Opposite.op Y)
        (aW ≫ i) = QG.obj.map f.op t.val
    rw [heqW, ha]
  let pb := pullback g G.target
  let fstH := pullback.fst g G.target ≫ eqToHom H.objects_eq.symm
  let mapPBH := F.op.whiskerLeft (yoneda.map fstH)
  let mapK := F.op.whiskerLeft (yoneda.map k)
  let α : (presheafToSheaf J (Type u)).obj (points F pb) ⟶ quotientSheaf J F jH :=
    (presheafToSheaf J (Type u)).map mapPBH ≫ quotientPointMap J F jH
  let κ := (presheafToSheaf J (Type u)).map mapK
  let qTS : quotientSheaf J F jH ⟶ QT := Sheaf.homEquiv.symm qT
  let mapReach := restrictionReachMap G g
  have hrelation :
      (F.op.whiskerLeft (yoneda.map mapReach)) ≫ toQuotientSheaf J F jG =
        (F.op.whiskerLeft (yoneda.map (pullback.fst g G.target ≫ g))) ≫
          toQuotientSheaf J F jG := by
    let t := pullback.fst g G.target
    let a := pullback.snd g G.target
    have h := congrArg
      (fun p => (F.op.whiskerLeft (yoneda.map a)) ≫ p)
      (sourceMap_toQuotientSheaf J F jG)
    simp only [sourceMap, targetMap, jG, groupoidPreRelation, PreRelation.source,
      PreRelation.target, prod.lift_snd, prod.lift_fst] at h
    change (F.op.whiskerLeft (yoneda.map a) ≫
        F.op.whiskerLeft (yoneda.map G.source)) ≫ toQuotientSheaf J F jG =
      (F.op.whiskerLeft (yoneda.map a) ≫
        F.op.whiskerLeft (yoneda.map G.target)) ≫ toQuotientSheaf J F jG at h
    rw [← Functor.whiskerLeft_comp, ← Functor.map_comp] at h
    simpa [mapReach, restrictionReachMap, t, a, Category.assoc, pullback.condition] using h
  have hrel : mapK ≫ mapW ≫ toQuotientSheaf J F jG =
      mapPBH ≫ (F.op.whiskerLeft (yoneda.map H.hom.mapObjects)) ≫
        toQuotientSheaf J F jG := by
    change (mapK ≫ mapW) ≫ toQuotientSheaf J F jG =
      (mapPBH ≫ (F.op.whiskerLeft (yoneda.map H.hom.mapObjects))) ≫
        toQuotientSheaf J F jG
    have h1 : mapK ≫ mapW = F.op.whiskerLeft (yoneda.map (k ≫ i)) := by
      ext X a; simp [mapK, mapW, Category.assoc]
    have h2 : mapPBH ≫ F.op.whiskerLeft (yoneda.map H.hom.mapObjects) =
        F.op.whiskerLeft (yoneda.map (pullback.fst g G.target ≫ g)) := by
      ext X a; simp [mapPBH, fstH, H.mapObjects_eq, Category.assoc]
    rw [h1, h2, hk, hrelation]
  have hfactor : α ≫ qTS = κ ≫ ψW := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (hQ := hTTrueP)
    change toSheafify J (points F pb) ≫ (α.hom ≫ qTS.hom) =
      toSheafify J (points F pb) ≫ (κ.hom ≫ ψW.hom)
    ext X x
    apply Subtype.ext
    have hunitA : toSheafify J (points F pb) ≫ α.hom =
        mapPBH ≫ toQuotientSheaf J F jH := by
      change toSheafify J (points F pb) ≫
          sheafifyMap J mapPBH ≫ (quotientPointMap J F jH).hom = _
      calc
        _ = (mapPBH ≫ toSheafify J (points F H.groupoid.objects)) ≫
            (quotientPointMap J F jH).hom := by
          exact congrArg (fun f => f ≫ (quotientPointMap J F jH).hom)
            (toSheafify_naturality J mapPBH).symm
        _ = mapPBH ≫ toQuotientSheaf J F jH := by
          rw [Category.assoc, toSheafify_comp_quotientPointMap]
    have hunitK : toSheafify J (points F pb) ≫ κ.hom ≫
        ψW.hom ≫ TTrue.ι = mapK ≫ uW ≫ TTrue.ι := by
      change toSheafify J (points F pb) ≫
          sheafifyMap J mapK ≫ sheafifyLift J uW hTTrueP ≫ TTrue.ι = _
      calc
        _ = (mapK ≫ toSheafify J (points F W)) ≫
            sheafifyLift J uW hTTrueP ≫ TTrue.ι := by
          exact congrArg
            (fun f => f ≫ sheafifyLift J uW hTTrueP ≫ TTrue.ι)
            (toSheafify_naturality J mapK).symm
        _ = mapK ≫ uW ≫ TTrue.ι := by
          calc
            _ = mapK ≫
                (toSheafify J (points F W) ≫ sheafifyLift J uW hTTrueP) ≫
                  TTrue.ι := by simp only [Category.assoc]
            _ = mapK ≫ uW ≫ TTrue.ι := by
              rw [toSheafify_sheafifyLift]
    have hqTSfac : qTS.hom ≫ TTrue.ι = q.hom := by
      change qT ≫ TTrue.ι = q.hom
      exact hqfactor
    have hleft : toSheafify J (points F pb) ≫ α.hom ≫ qTS.hom ≫ TTrue.ι =
      toSheafify J (points F pb) ≫ κ.hom ≫ ψW.hom ≫ TTrue.ι := by
      calc
        _ = (toSheafify J (points F pb) ≫ α.hom) ≫
            qTS.hom ≫ TTrue.ι := by simp only [Category.assoc]
        _ = (mapPBH ≫ toQuotientSheaf J F jH) ≫
            qTS.hom ≫ TTrue.ι := by rw [hunitA]
        _ = mapPBH ≫
            (toQuotientSheaf J F jH ≫ (qTS.hom ≫ TTrue.ι)) := by
          simp only [Category.assoc]
        _ = mapPBH ≫ (toQuotientSheaf J F jH ≫ q.hom) := by rw [hqTSfac]
        _ = mapPBH ≫
            (F.op.whiskerLeft (yoneda.map H.hom.mapObjects) ≫
              toQuotientSheaf J F jG) := by rw [hqproj]
        _ = mapK ≫ mapW ≫ toQuotientSheaf J F jG := by
          simpa only [Category.assoc] using hrel.symm
        _ = mapK ≫ (uW ≫ TTrue.ι) := by rw [Subfunctor.lift_ι]
        _ = mapK ≫ uW ≫ TTrue.ι := by rfl
        _ = _ := hunitK.symm
    exact congrArg (fun f => f.app X x) hleft
  have : Sheaf.IsLocallySurjective κ := hsurj
  have : Sheaf.IsLocallySurjective ψW := hψW
  have hloccomp : Sheaf.IsLocallySurjective (α ≫ qTS) := by
    change Presheaf.IsLocallySurjective J ((α ≫ qTS).hom)
    rw [hfactor]
    change Sheaf.IsLocallySurjective (κ ≫ ψW)
    infer_instance
  let _ : Presheaf.IsLocallySurjective J (α.hom ≫ qTS.hom) := hloccomp
  have hqTlocal : Presheaf.IsLocallySurjective J qTS.hom := by
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
      (f₁ := α.hom) (f₂ := qTS.hom) (f₃ := α.hom ≫ qTS.hom) rfl
  have : Epi qTS := (Sheaf.isLocallySurjective_iff_epi qTS).mp hqTlocal
  have : Mono qTS := by
    have : Mono qTS.hom := by
      change Mono qT
      exact hqTmono
    exact Sheaf.Hom.mono_of_presheaf_mono J (Type u) qTS
  have hqTiso : IsIso qTS := isIso_of_mono_of_epi qTS
  let T := BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) T
  have hOpen : P.presheaf TTrue.ι := by
    apply MorphismProperty.relative.of_exists
    intro A f
    let D := F.op ⋙ (Over.forget S).op ⋙ continuousMapPresheaf Prop
    let c : yoneda.obj A ⟶ D := f ≫ cG.hom
    let e := c.app (Opposite.op A) (𝟙 A)
    let V : (F.obj A).left.Opens :=
      ⟨{x | e.toFun x}, continuous_Prop.mp e.continuous⟩
    let hV : B.Contains V :=
      (Scheme.size_coe_opens_le (F.obj A).left V).trans_lt A.left.property
    let VO := B.obj hV
    let inc : VO ⟶ A.left := ObjectProperty.homMk V.ι
    let Aopen : BigFppfOver B S hS := Over.mk (inc ≫ A.hom)
    let snd : Aopen ⟶ A := Over.homMk inc (by rfl)
    have hinc : IsOpenImmersion (T.map snd) := by
      change IsOpenImmersion V.ι
      infer_instance
    have hpre (X : BigFppfOver B S hS) (a : X ⟶ Aopen) :
        (f.app (Opposite.op X) (a ≫ snd)) ∈ TTrue.obj (Opposite.op X) := by
      change ∀ z : (F.obj X).left,
        (cG.hom.app (Opposite.op X)
          (f.app (Opposite.op X) (a ≫ snd))).toFun z
      intro z
      have hn := c.naturality_apply (a ≫ snd).op (𝟙 A)
      have heval := congrArg (fun p : C((F.obj X).left, Prop) => p.toFun z) hn
      have heval' : (c.app (Opposite.op X) (a ≫ snd)).toFun z ↔
          e.toFun ((T.map (a ≫ snd)).base z) := by
        have hevalD : (c.app (Opposite.op X) (a ≫ snd)).toFun z ↔
            (D.map (a ≫ snd).op e).toFun z := by
          simpa [c, e] using heval
        have hmapEval : (D.map (a ≫ snd).op e).toFun z =
            e.toFun ((T.map (a ≫ snd)).base z) := by
          rfl
        exact hevalD.trans (Iff.of_eq hmapEval)
      have hpoint : (T.map (a ≫ snd)).base z ∈ V := by
        change V.ι ((T.map a).base z) ∈ V
        exact ((T.map a).base z).property
      exact heval'.mpr hpoint
    let p := yoneda.map snd ≫ f
    have hp : Subfunctor.range p ≤ TTrue := by
      intro X y hy
      rcases hy with ⟨a, rfl⟩
      exact hpre X.unop a
    let liftp : yoneda.obj Aopen ⟶ TTrue.toFunctor := Subfunctor.lift p hp
    let fst : yoneda.obj Aopen ⟶ TTrue.toFunctor := liftp
    have hcomm : fst ≫ TTrue.ι = yoneda.map snd ≫ f := by
      exact Subfunctor.lift_ι p hp
    refine ⟨Aopen, fst, snd, ?_, ?_⟩
    · apply IsPullback.of_forall_isPullback_app
      intro X
      cases X with
      | op X =>
        rw [Types.isPullback_iff]
        refine ⟨?_, ?_, ?_⟩
        · exact congrArg (fun m => m.app (Opposite.op X)) hcomm
        · intro x y hxy
          have : Mono (F.map snd).left := by
            change Mono (T.map snd)
            let _ : IsOpenImmersion (T.map snd) := hinc
            infer_instance
          have hsndMono : Mono snd := by
            have : Mono inc := by
              apply (Functor.reflectsMonomorphisms_of_faithful B.inclusion).reflects
              change Mono V.ι
              infer_instance
            exact (Functor.reflectsMonomorphisms_of_faithful
              (Over.forget (B.obj hS))).reflects snd (by
                change Mono inc
                infer_instance)
          let _ : Mono snd := hsndMono
          exact (cancel_mono snd).1 hxy.2
        · intro y x hxy
          have hxT : f.app (Opposite.op X) x ∈ TTrue.obj (Opposite.op X) := by
            rw [← hxy]
            exact y.property
          have hcx : ∀ z : (F.obj X).left,
              (cG.hom.app (Opposite.op X) (f.app (Opposite.op X) x)).toFun z := hxT
          have hsubset : Set.range (F.map x).left.base ⊆
              Set.range (F.map snd).left.base := by
            rintro _ ⟨z, rfl⟩
            have hn := c.naturality_apply x.op (𝟙 A)
            have heval := congrArg (fun m : C((F.obj X).left, Prop) => m.toFun z) hn
            have hz := hcx z
            have heval' : (cG.hom.app (Opposite.op X)
                (f.app (Opposite.op X) x)).toFun z ↔
                  e.toFun ((T.map x).base z) := by
              have hmap : (F.map x).left.base = (T.map x).base := rfl
              have hevalD : (cG.hom.app (Opposite.op X)
                  (f.app (Opposite.op X) x)).toFun z ↔
                  (D.map x.op e).toFun z := by
                simpa [c, e] using heval
              have hmapEval : (D.map x.op e).toFun z =
                  e.toFun ((T.map x).base z) := by
                rfl
              exact hevalD.trans (Iff.of_eq hmapEval)
            have hz' : e.toFun ((F.map x).left.base.hom z) := by
              exact heval'.mp hz
            refine ⟨⟨(T.map x).base z, hz'⟩, ?_⟩
            change V.ι ⟨(T.map x).base z, hz'⟩ = (F.map x).left.base z
            rfl
          have : IsOpenImmersion (F.map snd).left := by
            change IsOpenImmersion (T.map snd)
            exact hinc
          let xopen := factorThroughOpenSubset (F.map x) (F.map snd) hsubset
          let xopenLeft : B.inclusion.obj X.left ⟶ B.inclusion.obj Aopen.left := xopen.left
          let zleft : X.left ⟶ Aopen.left := B.inclusion.preimage xopenLeft
          let z : X ⟶ Aopen := Over.homMk zleft (by
            apply B.inclusion.map_injective
            change B.inclusion.map zleft ≫ B.inclusion.map Aopen.hom =
              B.inclusion.map X.hom
            change B.inclusion.map (B.inclusion.preimage xopenLeft) ≫
              B.inclusion.map Aopen.hom = B.inclusion.map X.hom
            rw [Functor.map_preimage]
            exact xopen.w)
          have hz : F.map z = xopen := by
            apply Over.OverMorphism.ext
            change B.inclusion.map zleft = xopen.left
            exact Functor.map_preimage B.inclusion xopenLeft
          have hzfac : z ≫ snd = x := by
            apply Over.OverMorphism.ext
            apply B.inclusion.map_injective
            change B.inclusion.map (z.left ≫ snd.left) = B.inclusion.map x.left
            rw [B.inclusion.map_comp]
            rw [show B.inclusion.map z.left = xopen.left from
              congrArg Over.Hom.left hz]
            exact congrArg Over.Hom.left
              (factorThroughOpenSubset_fac (F.map x) (F.map snd) hsubset)
          refine ⟨z, ?_, ?_⟩
          · apply Subtype.ext
            have htop : (fst.app (Opposite.op X) z).val =
                f.app (Opposite.op X) (z ≫ snd) := by
              rfl
            change y.val = f.app (Opposite.op X) x at hxy
            calc
              (fst.app (Opposite.op X) z).val =
                  f.app (Opposite.op X) (z ≫ snd) := htop
              _ = f.app (Opposite.op X) x := by rw [hzfac]
              _ = y.val := hxy.symm
          · simpa using hzfac
    · change IsOpenImmersion (T.map snd)
      exact hinc
  change P.presheaf q.hom
  rw [show q.hom = qTS.hom ≫ TTrue.ι from hqfactor.symm]
  let _ : MorphismProperty.RespectsIso (P.presheaf) := inferInstance
  exact MorphismProperty.RespectsIso.precomp (P.presheaf) qTS.hom TTrue.ι hOpen

/-! ### Restriction to an invariant open -/

/-- A morphism of schemes over the base whose underlying map is an open immersion is a
monomorphism. -/
private theorem mono_of_isOpenImmersion_left {S : Scheme.{u}} {W V : Over S} (i : W ⟶ V)
    [IsOpenImmersion i.left] : Mono i := by
  refine ⟨fun {T} a b hab => ?_⟩
  apply Over.OverMorphism.ext
  have _ : Mono i.left := inferInstance
  refine (cancel_mono i.left).mp ?_
  have h := congrArg Over.Hom.left hab
  rw [Over.comp_left, Over.comp_left] at h
  exact h

/-- **The saturation of an invariant open is that open itself.** If the range of `i` is
invariant under the arrows of `G`, then the arrows whose target lifts along `i` are exactly
those whose source does, so reading off the source of such an arrow sweeps out precisely the
range of `i`. -/
theorem range_restrictionReachMap_eq_of_isInvariantSet {S : Scheme.{u}} (G : GroupoidScheme S)
    {W : Over S} (i : W ⟶ G.objects)
    (hi : IsInvariantSet G (Set.range i.left.base)) :
    Set.range (restrictionReachMap G i).left.base = Set.range i.left.base := by
  refine Set.Subset.antisymm ?_ (range_le_restrictionReachMap G i)
  rw [range_restrictionReachMap_eq]
  rintro x ⟨r, hr, rfl⟩
  have hmem : r ∈ G.target.left.base ⁻¹' Set.range i.left.base := hr
  rw [← invariantSet_source_preimage_eq_target G _ hi] at hmem
  exact hmem

/-- The reach map of an open immersion with invariant range factors through it. -/
private noncomputable def invariantReachFactor {S : Scheme.{u}} (G : GroupoidScheme S)
    {W : Over S} (i : W ⟶ G.objects) [IsOpenImmersion i.left]
    (hi : IsInvariantSet G (Set.range i.left.base)) :
    pullback i G.target ⟶ W :=
  factorThroughOpenSubset (restrictionReachMap G i) i
    (le_of_eq (range_restrictionReachMap_eq_of_isInvariantSet G i hi))

private theorem invariantReachFactor_fac {S : Scheme.{u}} (G : GroupoidScheme S)
    {W : Over S} (i : W ⟶ G.objects) [IsOpenImmersion i.left]
    (hi : IsInvariantSet G (Set.range i.left.base)) :
    invariantReachFactor G i hi ≫ i = restrictionReachMap G i :=
  factorThroughOpenSubset_fac _ _ _

/-- The factorization of the reach map through an invariant open is a split epimorphism: the
identity arrow at a point of the open is a section of it. -/
private theorem isSplitEpi_invariantReachFactor {S : Scheme.{u}} (G : GroupoidScheme S)
    {W : Over S} (i : W ⟶ G.objects) [IsOpenImmersion i.left]
    (hi : IsInvariantSet G (Set.range i.left.base)) :
    IsSplitEpi (invariantReachFactor G i hi) := by
  obtain ⟨e, he⟩ := exists_comp_restrictionReachMap_eq G i
  have _ : Mono i := mono_of_isOpenImmersion_left i
  refine IsSplitEpi.mk' ⟨e, ?_⟩
  refine (cancel_mono i).mp ?_
  rw [Category.assoc, invariantReachFactor_fac G i hi, he, Category.id_comp]

/-- **The invariant-open case of Stacks 02WU.** Let `(U, R, s, t, c)` be a groupoid scheme
over `S` and let `i : V ⟶ U` be an open immersion of schemes over `S` whose range is invariant
under the arrows of the groupoid.  Then the map of fppf quotient sheaves `V/R|_V ⟶ U/R` induced
by the restriction of the groupoid along `i` is representable, and is an open immersion; so
`V/R|_V` is an open subspace of `U/R`.

This is only the special case of Stacks 02WU in which `g : U' → U` is already an open immersion
onto an invariant open: the saturation is then the given open itself and the covering of it by
the reach map is split by the identity arrow of the groupoid, so no flatness is needed of
anything.  The lemma as stated in the source, for an equivalence relation with `s, t`
surjective, flat and locally of finite presentation and an arbitrary flat, locally finitely
presented `g`, is `AlgebraicGeometry.Space.isOpenImmersion_restrictedQuotientMap`. -/
theorem isOpenImmersion_restrictionQuotientMap_of_isInvariantSet
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (G : GroupoidScheme S) {W : Over S} (i : W ⟶ G.objects) [IsOpenImmersion i.left]
    (hi : IsInvariantSet G (Set.range i.left.base)) :
    Space.IsOpenImmersion B S hS
      (restrictionQuotientMap (BigFppfOver.topology B S hS) (Over.post B.inclusion) G i
        (restrict G i)).1 := by
  let J := BigFppfOver.topology B S hS
  let F : BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  let k := invariantReachFactor G i hi
  refine isOpenImmersion_restrictionQuotientMap_of_open_image B S hS G i i k
    (invariantReachFactor_fac G i hi)
    (range_restrictionReachMap_eq_of_isInvariantSet G i hi).symm ?_
  obtain ⟨sec⟩ := (isSplitEpi_invariantReachFactor G i hi).exists_splitEpi
  have hsec : sec.section_ ≫ k = 𝟙 _ := sec.id
  have hfac : F.op.whiskerLeft (yoneda.map sec.section_) ≫
      F.op.whiskerLeft (yoneda.map k) = 𝟙 _ := by
    rw [← Functor.whiskerLeft_comp, ← CategoryTheory.Functor.map_comp, hsec,
      CategoryTheory.Functor.map_id, Functor.whiskerLeft_id']
  have _ : IsSplitEpi ((presheafToSheaf J (Type u)).map
      (F.op.whiskerLeft (yoneda.map k))) :=
    IsSplitEpi.mk' ⟨(presheafToSheaf J (Type u)).map
      (F.op.whiskerLeft (yoneda.map sec.section_)), by
        rw [← CategoryTheory.Functor.map_comp, hfac, CategoryTheory.Functor.map_id]⟩
  exact (Sheaf.isLocallySurjective_iff_epi _).mpr inferInstance

end GroupoidScheme

end AlgebraicGeometry

end
