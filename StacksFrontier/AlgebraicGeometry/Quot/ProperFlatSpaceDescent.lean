module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatFibreSections
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatIsomPresheaf
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatLimitPreservingReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineSiteLimitCone
public import StacksFrontier.AlgebraicGeometry.Spaces.PrestackBaseChange

/-!
# Stage descent for the proper flat families, read on the underlying algebraic spaces

`StacksFrontier.AlgebraicGeometry.Quot.ProperFlatLimitPreservingReduction` reduces **Stacks 0D1I** to
three descent conditions for the projection `AlgebraicGeometry.cartesianProperFlatProjection` of
Stacks 0D1E at an affine cofiltered cone whose cone of underlying schemes is a limit. Those three
conditions are phrased in the language of fibred categories: objects of a fibre, vertical
morphisms, and morphisms lying over a transition of the diagram. This file translates them into
statements about algebraic spaces over the site and their structure morphisms, so that nothing of
the fibred-category plumbing is left in the geometric input.

The translation rests on **Stacks 04U9**: a morphism of the comma category of Stacks 04U8 is
strongly cartesian exactly when its square of structure morphisms is cartesian
(`AlgebraicGeometry.spacesProjection_isStronglyCartesian_iff`, and in the form used here
`AlgebraicGeometry.isStronglyCartesian_of_isPullback`). So a morphism of the fibred category over
a transition of the diagram *is* a cartesian square of structure morphisms, and the geometric
input can speak only of spaces, structure morphisms and cartesian squares.

## Main definitions

* `AlgebraicGeometry.ProperFlatFamilyDescendsAlongAffineLimit`: the geometric input for descent of
  objects. Along an affine cofiltered limit, a finitely presented, flat and proper family over the
  vertex is the base change of such a family over a stage.
* `AlgebraicGeometry.ProperFlatFamilyIsomorphismDescendsAlongAffineLimit`: the geometric input for
  descent of vertical morphisms. An isomorphism over the vertex between the base changes of two
  stage families comes from one between their base changes to a later stage.
* `AlgebraicGeometry.ProperFlatMorphismEqualityDescendsAlongAffineLimit`: the geometric input for
  descent of equalities. Two morphisms of stage families whose base changes to the vertex agree
  have equal base changes to a later stage.
* `AlgebraicGeometry.coneBaseRestrict`: the comparison of the base change of a stage family to the
  vertex with its base change to a later stage, along which the last two conditions compare a
  morphism at a stage with one over the vertex.

## Main results

* `AlgebraicGeometry.descentObj_cartesianProperFlat`,
  `AlgebraicGeometry.descentHom_cartesianProperFlat` and
  `AlgebraicGeometry.descentEq_cartesianProperFlat`: the three inputs give the three conditions
  `Deformation.Artin.DescentObj`, `Deformation.Artin.DescentHom` and
  `Deformation.Artin.DescentEq` for the proper flat families, which is exactly what
  `AlgebraicGeometry.isLimitPreserving_cartesianProperFlatFiberedCategory_of_stageDescent`
  consumes.
* `AlgebraicGeometry.ProperFlatFibre.exists_homLift_of_isPullback`: the translation in the
  direction that builds fibred-category data, a cartesian square of structure morphisms being
  turned into a morphism of the fibred category lying over the given morphism of bases.
* `AlgebraicGeometry.ProperFlatFibre.str_properties`,
  `AlgebraicGeometry.ProperFlatFibre.isAlgebraicSpace_space` and
  `AlgebraicGeometry.ProperFlatFibre.map_str_id`: the translation in the direction that reads
  geometry off fibred-category data.
* `AlgebraicGeometry.ProperFlatFibre.map_injective_of_isHomLift`: a morphism of the fibred
  category lying over a prescribed morphism of bases is determined by its morphism of spaces, so
  an equation of such morphisms is an equation of morphisms of algebraic spaces.

## Implementation notes

An object `x` of the fibre over `U` carries two separate pieces of data about its base: the base
`x.val.obj.obj.right` of the underlying comma object, and the identification `x.property` of that
base with `U`. The structure morphism `AlgebraicGeometry.ProperFlatFibre.str` composes the comma
object's own structure morphism with the Yoneda image of that identification, so a statement about
`str x` is not literally a statement about the comma object until the identification is removed.
Both translation lemmas therefore destructure `x` and `subst` its identification first; this is
possible precisely because they are stated with the base of the fibre a free variable.

*Which base changes the conditions speak of.* The condition on objects is stated with an abstract
cartesian square, because what it must produce is a family at a stage of which the given family
over the vertex *is* a base change; demanding that the given family be literally the chosen fibre
product would be a stronger requirement. The two conditions on morphisms are stated at the chosen
fibre products instead, since there the base change is an input rather than something to be
produced, and the stage objects their conclusions ask for can then be the chosen pullbacks of the
fibred category, whose spaces `AlgebraicGeometry.ProperFlatFibre.pullIso` identifies with those
fibre products.

*Why the condition on morphisms is about isomorphisms.* The morphisms of the category of Stacks
0D1E are the cartesian ones, so a morphism of one of its fibres is automatically an isomorphism,
and `Deformation.Artin.DescentHom` therefore asks for one. See the docstring of
`AlgebraicGeometry.ProperFlatFamilyIsomorphismDescendsAlongAffineLimit` for how that condition
follows from the fullness half of Stacks 07SK read on arbitrary morphisms together with
`AlgebraicGeometry.ProperFlatMorphismEqualityDescendsAlongAffineLimit`.

## References

* [Stacks Project, Tag 0D1I](https://stacks.math.columbia.edu/tag/0D1I)
* [Stacks Project, Tag 0D1E](https://stacks.math.columbia.edu/tag/0D1E)
* [Stacks Project, Tag 04U8](https://stacks.math.columbia.edu/tag/04U8)
* [Stacks Project, Tag 04U9](https://stacks.math.columbia.edu/tag/04U9)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v w

namespace ProperFlatFibre

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local implicit_reducible] Functor.Fiber

/-- The structure morphism of an object of the fibre over the base of its own comma object is that
comma object's structure morphism: the identification of the two bases is the identity. -/
private theorem str_mk_rfl (xv : CartesianProperFlatSpaces B S hS) :
    str (⟨xv, rfl⟩ : (cartesianProperFlatProjection B S hS).Fiber
        ((cartesianProperFlatProjection B S hS).obj xv)) =
      ((comma B S hS).obj xv).hom :=
  Eq.trans
    (congrArg (fun t => ((comma B S hS).obj xv).hom ≫ t)
      (yoneda.map_id ((cartesianProperFlatProjection B S hS).obj xv)))
    (Category.comp_id _)

/-- **A cartesian square of structure morphisms is a morphism of the proper flat families lying
over the morphism of bases.** Given an object `x` of the fibre over `U`, a morphism `π : U ⟶ V` of
the site and a finitely presented, flat and proper algebraic space `fi : Zi ⟶ h_V` whose base
change along `π` is the structure morphism of `x`, the space `Zi` is an object of the fibre over
`V` and the comparison morphism is a morphism of the fibred category lying over `π`.

This is the converse half of Stacks 04U9 applied to the proper flat families, and is the step that
lets a purely geometric descent statement produce the data `Deformation.Artin.DescentObj` asks
for. `AlgebraicGeometry.ProperFlatFibre.isPullback_map` is the other direction. -/
theorem exists_homLift_of_isPullback {U V : BigFppfOver B S hS}
    (x : (cartesianProperFlatProjection B S hS).Fiber U) (π : U ⟶ V)
    {Zi : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZi : IsAlgebraicSpace B S hS Zi)
    {fi : Zi ⟶ yoneda.obj V} (hfp : Space.IsFinitePresentation B S hS fi)
    (hfl : Space.IsFlat B S hS fi) (hpr : Space.IsProper B S hS fi)
    {g : space x ⟶ Zi} (hsq : IsPullback g (str x) fi (yoneda.map π)) :
    ∃ (xi : (cartesianProperFlatProjection B S hS).Fiber V) (δ : x.val ⟶ xi.val),
      (cartesianProperFlatProjection B S hS).IsHomLift π δ := by
  obtain ⟨xv, hx⟩ := x
  subst hx
  rw [str_mk_rfl] at hsq
  let Ci : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    ⟨⟨Zi, hZi⟩, V, fi⟩
  let m : xv.obj.obj ⟶ Ci := { left := ObjectProperty.homMk g, right := π, w := hsq.w }
  refine ⟨⟨⟨⟨Ci, ⟨hfp, hfl, hpr⟩⟩⟩, rfl⟩, ⟨ObjectProperty.homMk m, ?_⟩, ?_⟩
  · exact isStronglyCartesian_of_isPullback B S hS m hsq.flip
  · exact IsHomLift.of_fac' _ π _ rfl rfl
      (by exact ((Category.id_comp (π ≫ 𝟙 V)).trans (Category.comp_id π)).symm)

/-- A vertical morphism of the proper flat families commutes with the structure morphisms of its
source and target. This is `AlgebraicGeometry.ProperFlatFibre.map_str` over the identity, with the
Yoneda image of the identity removed. -/
theorem map_str_id {V : BigFppfOver B S hS}
    {x y : (cartesianProperFlatProjection B S hS).Fiber V} (f : x.val ⟶ y.val)
    [(cartesianProperFlatProjection B S hS).IsHomLift (𝟙 V) f] :
    map f ≫ str y = str x :=
  Eq.trans (map_str f (𝟙 V))
    (Eq.trans (congrArg (fun t => str x ≫ t) (yoneda.map_id V)) (Category.comp_id _))

/-- **A morphism of the proper flat families lying over a prescribed morphism of bases is
determined by the morphism of algebraic spaces carrying it.** The morphism of base schemes is
recovered from the lifting datum, and the morphism of total spaces is the hypothesis; this
generalises `AlgebraicGeometry.ProperFlatFibre.map_injective` from the fibre over one object to
arbitrary morphisms with a prescribed lift. -/
theorem map_injective_of_isHomLift {U V : BigFppfOver B S hS} (g : U ⟶ V)
    {a b : CartesianProperFlatSpaces B S hS} {f f' : a ⟶ b}
    [(cartesianProperFlatProjection B S hS).IsHomLift g f]
    [(cartesianProperFlatProjection B S hS).IsHomLift g f']
    (h : (underlying B S hS).map f = (underlying B S hS).map f') : f = f' := by
  apply (comma B S hS).map_injective
  apply Comma.hom_ext
  · apply ObjectProperty.hom_ext
    exact h
  · show (cartesianProperFlatProjection B S hS).map f =
      (cartesianProperFlatProjection B S hS).map f'
    rw [IsHomLift.fac' (cartesianProperFlatProjection B S hS) g f,
      IsHomLift.fac' (cartesianProperFlatProjection B S hS) g f']

/-- The comparison from the chosen pullback of a fibre object along `q` lies over `q`. -/
private theorem isHomLift_pullMap_mk {V W : BigFppfOver B S hS}
    (x : (cartesianProperFlatProjection B S hS).Fiber V) (q : W ⟶ V) :
    (cartesianProperFlatProjection B S hS).IsHomLift q (pullMap x (Over.mk q)) := by
  have := isFibered B S hS
  exact (Functor.IsPreFibered.pullbackMap.IsCartesian x.property q).toIsHomLift

end ProperFlatFibre

section BaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The comparison of two base changes of one family along a factorisation of the base
morphism.** For `f : X ⟶ h_V` and a factorisation `r = p ≫ q` of `r : U ⟶ V` through
`q : W ⟶ V`, the base change of `f` along `r` maps to its base change along `q`, over `p`. -/
def pullbackBaseRestrict {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U W V : BigFppfOver B S hS}
    (f : X ⟶ yoneda.obj V) {p : U ⟶ W} {q : W ⟶ V} {r : U ⟶ V} (h : p ≫ q = r) :
    pullback (yoneda.map r) f ⟶ pullback (yoneda.map q) f :=
  pullback.lift (pullback.fst (yoneda.map r) f ≫ yoneda.map p)
    (pullback.snd (yoneda.map r) f)
    (by rw [Category.assoc, ← Functor.map_comp, h]; exact pullback.condition)

/-- The comparison `pullbackBaseRestrict f h` followed by the first projection is the first
projection followed by `p`. -/
@[reassoc (attr := simp)]
theorem pullbackBaseRestrict_fst {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U W V : BigFppfOver B S hS} (f : X ⟶ yoneda.obj V) {p : U ⟶ W} {q : W ⟶ V} {r : U ⟶ V}
    (h : p ≫ q = r) :
    pullbackBaseRestrict f h ≫ pullback.fst (yoneda.map q) f =
      pullback.fst (yoneda.map r) f ≫ yoneda.map p :=
  pullback.lift_fst _ _ _

/-- The comparison `pullbackBaseRestrict f h` commutes with the second projections to `X`. -/
@[reassoc (attr := simp)]
theorem pullbackBaseRestrict_snd {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U W V : BigFppfOver B S hS} (f : X ⟶ yoneda.obj V) {p : U ⟶ W} {q : W ⟶ V} {r : U ⟶ V}
    (h : p ≫ q = r) :
    pullbackBaseRestrict f h ≫ pullback.snd (yoneda.map q) f =
      pullback.snd (yoneda.map r) f :=
  pullback.lift_snd _ _ _

/-- **The comparison of the base change of a stage family to the vertex of the cone with its base
change to a later stage.** For `f : X ⟶ h_{D i}` and `s : k ⟶ i`, the base change of `f` along the
cone leg `c.π.app i` maps to its base change along `D.map s`, over the cone leg `c.π.app k`. -/
def coneBaseRestrict {I : Type v} [Category.{w} I] {D : I ⥤ BigAffineFppf B S hS} (c : Cone D)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {i k : I} (s : k ⟶ i)
    (f : X ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) :
    pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) f ⟶
      pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) f :=
  pullbackBaseRestrict f (p := (BigAffineFppf.inclusion B S hS).map (c.π.app k))
    (by rw [← Functor.map_comp, c.w s])

/-- The comparison `coneBaseRestrict c s f` followed by the first projection is the first
projection followed by the cone leg `c.π.app k`. -/
@[reassoc (attr := simp)]
theorem coneBaseRestrict_fst {I : Type v} [Category.{w} I] {D : I ⥤ BigAffineFppf B S hS}
    (c : Cone D) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {i k : I} (s : k ⟶ i)
    (f : X ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) :
    coneBaseRestrict c s f ≫
        pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) f =
      pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) f ≫
        yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app k)) :=
  pullbackBaseRestrict_fst _ _

/-- The comparison `coneBaseRestrict c s f` commutes with the second projections to `X`. -/
@[reassoc (attr := simp)]
theorem coneBaseRestrict_snd {I : Type v} [Category.{w} I] {D : I ⥤ BigAffineFppf B S hS}
    (c : Cone D) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {i k : I} (s : k ⟶ i)
    (f : X ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) :
    coneBaseRestrict c s f ≫
        pullback.snd (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) f =
      pullback.snd (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) f :=
  pullbackBaseRestrict_snd _ _

end BaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent of finitely presented, flat and proper families along an affine cofiltered limit.**
Let `T = lim Tᵢ` be a cofiltered inverse system of affine schemes of the big fppf site of `S`
whose cone of underlying schemes is a limit. The condition says that every finitely presented,
flat and proper algebraic space over `h_T` is the base change of a finitely presented, flat and
proper algebraic space over `h_{Tᵢ}` for some stage `i`.

This is the geometric content of the essential-surjectivity half of **Stacks 0D1I**: nothing of
the category fibred in groupoids of Stacks 0D1E appears, only algebraic spaces over the site,
their structure morphisms, and cartesian squares. -/
def ProperFlatFamilyDescendsAlongAffineLimit : Prop :=
  ∀ (I : Type v) [Category.{w} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) (c : Cone D),
    IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
    ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Z →
    ∀ (f : Z ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj c.pt)),
      Space.IsFinitePresentation B S hS f → Space.IsFlat B S hS f →
      Space.IsProper B S hS f →
      ∃ (i : I) (Zi : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Zi)
        (fi : Zi ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) (g : Z ⟶ Zi),
        Space.IsFinitePresentation B S hS fi ∧ Space.IsFlat B S hS fi ∧
          Space.IsProper B S hS fi ∧
          IsPullback g f fi
            (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i)))

/-- **Descent of objects for the proper flat families, from descent of the underlying algebraic
spaces.** The condition `Deformation.Artin.DescentObj` of Stacks 07XL for the projection of
Stacks 0D1E at an affine cofiltered cone follows from
`AlgebraicGeometry.ProperFlatFamilyDescendsAlongAffineLimit`.

An object of the fibre over the vertex is its underlying algebraic space together with its
structure morphism, which is of finite presentation, flat and proper; descending that datum to a
stage gives a family over the stage and a cartesian square, and a cartesian square is exactly a
morphism of the fibred category lying over the cone projection, by Stacks 04U9. -/
theorem descentObj_cartesianProperFlat
    (h : ProperFlatFamilyDescendsAlongAffineLimit.{u, v, w} B S hS)
    {I : Type v} [Category.{w} I] [IsCofiltered I] (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    Deformation.Artin.DescentObj (cartesianProperFlatProjection B S hS)
      (D ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone c) := by
  intro x
  obtain ⟨hfp, hfl, hpr⟩ := ProperFlatFibre.str_properties x
  obtain ⟨i, Zi, hZi, fi, g, hfpi, hfli, hpri, hsq⟩ :=
    h I D c hc (ProperFlatFibre.space x) (ProperFlatFibre.isAlgebraicSpace_space x)
      (ProperFlatFibre.str x) hfp hfl hpr
  obtain ⟨xi, δ, hδ⟩ := ProperFlatFibre.exists_homLift_of_isPullback x
    ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) hZi hfpi hfli hpri hsq
  exact ⟨i, xi, δ, hδ⟩

/-- **Descent of equalities of morphisms of finitely presented, flat and proper families along an
affine cofiltered limit.** Let `T = lim Tᵢ` be a cofiltered inverse system of affine schemes of
the big fppf site of `S` whose cone of underlying schemes is a limit, and let `X ⟶ h_{Tᵢ}` and
`Y ⟶ h_{Tᵢ}` be finitely presented, flat and proper algebraic spaces over a stage. The condition
says that two morphisms `X ⟶ Y` over `h_{Tᵢ}` whose base changes to `h_T` agree already have
equal base changes to `h_{T_k}` for some later stage `k`.

The base changes are taken at the chosen fibre products: the base change of `a : X ⟶ Y` along
`h_{T_k} ⟶ h_{Tᵢ}` agrees with that of `a'` exactly when the two composites of the second
projection of `h_{T_k} ×_{h_{Tᵢ}} X` with `a` and with `a'` agree, since the first components of
the two base changes agree automatically.

This is the faithfulness half of **Stacks 07SK** in the affine-base setting, and the geometric
content of the faithfulness half of **Stacks 0D1I**. -/
def ProperFlatMorphismEqualityDescendsAlongAffineLimit : Prop :=
  ∀ (I : Type v) [Category.{w} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) (c : Cone D),
    IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
    ∀ (i : I) (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
      IsAlgebraicSpace B S hS X → IsAlgebraicSpace B S hS Y →
    ∀ (f : X ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
      (g : Y ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i))),
      Space.IsFinitePresentation B S hS f → Space.IsFlat B S hS f → Space.IsProper B S hS f →
      Space.IsFinitePresentation B S hS g → Space.IsFlat B S hS g → Space.IsProper B S hS g →
    ∀ a a' : X ⟶ Y, a ≫ g = f → a' ≫ g = f →
      pullback.snd (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) f ≫ a =
          pullback.snd (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) f ≫ a' →
      ∃ (k : I) (s : k ⟶ i),
        pullback.snd (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) f ≫ a =
          pullback.snd (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) f ≫ a'

attribute [local instance] ProperFlatFibre.isFibered

/-- **Descent of equalities of vertical morphisms for the proper flat families, from descent of
equalities of morphisms of the underlying algebraic spaces.** The condition
`Deformation.Artin.DescentEq` of Stacks 07XL for the projection of Stacks 0D1E at an affine
cofiltered cone follows from
`AlgebraicGeometry.ProperFlatMorphismEqualityDescendsAlongAffineLimit`.

A vertical morphism of the fibre over a stage is a morphism of the underlying algebraic spaces
over the base, by `AlgebraicGeometry.ProperFlatFibre.map_str_id`; a morphism of the fibred
category over the cone projection exhibits the space over the vertex as the base change of the
space over the stage, by Stacks 04U9, so the hypothesis becomes an equality of the base changes to
the vertex; and the stage object the conclusion asks for is the chosen pullback along the
transition, whose space is the chosen fibre product by
`AlgebraicGeometry.ProperFlatFibre.pullIso`. -/
theorem descentEq_cartesianProperFlat
    (h : ProperFlatMorphismEqualityDescendsAlongAffineLimit.{u, v, w} B S hS)
    {I : Type v} [Category.{w} I] [IsCofiltered I] (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    Deformation.Artin.DescentEq (cartesianProperFlatProjection B S hS)
      (D ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone c) := by
  intro i xi yi x δ hδ ψ ψ' hψ hψ' hδψ
  have hδ' : (cartesianProperFlatProjection B S hS).IsHomLift
    ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) δ := hδ
  have hψ₀ : (cartesianProperFlatProjection B S hS).IsHomLift
    (𝟙 ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) ψ := hψ
  have hψ₀' : (cartesianProperFlatProjection B S hS).IsHomLift
    (𝟙 ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) ψ' := hψ'
  obtain ⟨hfp, hfl, hpr⟩ := ProperFlatFibre.str_properties xi
  obtain ⟨hgp, hgl, hgr⟩ := ProperFlatFibre.str_properties yi
  have hd : IsPullback (ProperFlatFibre.str x) (ProperFlatFibre.map δ)
      (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i)))
      (ProperFlatFibre.str xi) :=
    ProperFlatFibre.isPullback_map δ ((BigAffineFppf.inclusion B S hS).map (c.π.app i))
  have hmapeq : ProperFlatFibre.map δ ≫ ProperFlatFibre.map ψ =
      ProperFlatFibre.map δ ≫ ProperFlatFibre.map ψ' :=
    Eq.trans ((ProperFlatFibre.underlying B S hS).map_comp δ ψ).symm
      (Eq.trans (congrArg (ProperFlatFibre.underlying B S hS).map hδψ)
        ((ProperFlatFibre.underlying B S hS).map_comp δ ψ'))
  have hvertex : pullback.snd (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i)))
        (ProperFlatFibre.str xi) ≫ ProperFlatFibre.map ψ =
      pullback.snd (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i)))
        (ProperFlatFibre.str xi) ≫ ProperFlatFibre.map ψ' := by
    rw [← hd.isoPullback_inv_snd, Category.assoc, Category.assoc, hmapeq]
  obtain ⟨k, s, hk⟩ := h I D c hc i _ _ (ProperFlatFibre.isAlgebraicSpace_space xi)
    (ProperFlatFibre.isAlgebraicSpace_space yi) (ProperFlatFibre.str xi) (ProperFlatFibre.str yi)
    hfp hfl hpr hgp hgl hgr (ProperFlatFibre.map ψ) (ProperFlatFibre.map ψ')
    (ProperFlatFibre.map_str_id ψ) (ProperFlatFibre.map_str_id ψ') hvertex
  have hdx := ProperFlatFibre.isHomLift_pullMap_mk xi
    ((BigAffineFppf.inclusion B S hS).map (D.map s))
  refine ⟨k, s, ProperFlatFibre.pull xi (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s))),
    ProperFlatFibre.pullMap xi (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s))),
    hdx, ?_⟩
  refine ProperFlatFibre.map_injective_of_isHomLift
    ((BigAffineFppf.inclusion B S hS).map (D.map s)) ?_
  rw [(ProperFlatFibre.underlying B S hS).map_comp, (ProperFlatFibre.underlying B S hS).map_comp]
  refine (cancel_epi (ProperFlatFibre.pullIso xi
    (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))).inv).mp ?_
  rw [← Category.assoc, ← Category.assoc, ProperFlatFibre.pullIso_inv_snd]
  exact hk

/-- **Descent of isomorphisms of finitely presented, flat and proper families along an affine
cofiltered limit.** Let `T = lim Tᵢ` be a cofiltered inverse system of affine schemes of the big
fppf site of `S` whose cone of underlying schemes is a limit, and let `X ⟶ h_{Tᵢ}` and
`Y ⟶ h_{Tᵢ}` be finitely presented, flat and proper algebraic spaces over a stage. The condition
says that an isomorphism over `h_T` between their base changes to the vertex comes from an
isomorphism between their base changes to a later stage, compatibly with the restriction map
`AlgebraicGeometry.coneBaseRestrict`.

*Why isomorphisms.* The morphisms of the category of Stacks 0D1E are the cartesian ones, so a
morphism of one of its fibres is automatically an isomorphism, and
`Deformation.Artin.DescentHom` therefore asks for an isomorphism at the later stage. This
condition is the fullness half of **Stacks 07SK** in the affine-base setting, read on
isomorphisms — equivalently, limit preservation of the isomorphism functor of Stacks 02ZB. It
follows from the fullness half read on arbitrary morphisms together with
`AlgebraicGeometry.ProperFlatMorphismEqualityDescendsAlongAffineLimit`: descend the isomorphism
and its inverse to two stages, pass to a common stage, and use descent of equalities twice to see
that the two descended morphisms are mutually inverse at a further stage. That derivation is not
carried out here. -/
def ProperFlatFamilyIsomorphismDescendsAlongAffineLimit : Prop :=
  ∀ (I : Type v) [Category.{w} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) (c : Cone D),
    IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
    ∀ (i : I) (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
      IsAlgebraicSpace B S hS X → IsAlgebraicSpace B S hS Y →
    ∀ (f : X ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
      (g : Y ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i))),
      Space.IsFinitePresentation B S hS f → Space.IsFlat B S hS f → Space.IsProper B S hS f →
      Space.IsFinitePresentation B S hS g → Space.IsFlat B S hS g → Space.IsProper B S hS g →
    ∀ u : pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) f ⟶
        pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) g,
      IsIso u →
      u ≫ pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) g =
        pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) f →
      ∃ (k : I) (s : k ⟶ i)
        (v : pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) f ⟶
          pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) g),
        IsIso v ∧
        v ≫ pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) g =
          pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) f ∧
        coneBaseRestrict c s f ≫ v = u ≫ coneBaseRestrict c s g

section HomDescent

attribute [local implicit_reducible] Functor.Fiber

/-- **Descent of vertical morphisms for the proper flat families, from descent of isomorphisms of
the underlying algebraic spaces.** The condition `Deformation.Artin.DescentHom` of Stacks 07XL for
the projection of Stacks 0D1E at an affine cofiltered cone follows from
`AlgebraicGeometry.ProperFlatFamilyIsomorphismDescendsAlongAffineLimit`.

The vertical morphism `φ` over the vertex is an isomorphism, because the projection is fibred in
groupoids; the two morphisms `δ` and `ε` over the cone projection exhibit the spaces over the
vertex as base changes of the stage spaces, by Stacks 04U9, so `φ` becomes an isomorphism of the
two chosen base changes to the vertex. The stage objects the conclusion asks for are the chosen
pullbacks along the transition, whose spaces are the chosen fibre products by
`AlgebraicGeometry.ProperFlatFibre.pullIso`; the isomorphism the input returns is therefore an
isomorphism of their spaces over the base, hence an isomorphism of the fibre by
`AlgebraicGeometry.ProperFlatFibre.isoOfUnderlying`, and that is the vertical morphism `ψ`. The
comparison `δk` is the universal property of the chosen cartesian lift. -/
theorem descentHom_cartesianProperFlat
    (h : ProperFlatFamilyIsomorphismDescendsAlongAffineLimit.{u, v, w} B S hS)
    {I : Type v} [Category.{w} I] [IsCofiltered I] (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    Deformation.Artin.DescentHom (cartesianProperFlatProjection B S hS)
      (D ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone c) := by
  intro i xi yi x y δ ε hδ hε φ hφ
  have hδ' : (cartesianProperFlatProjection B S hS).IsHomLift
    ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) δ := hδ
  have hε' : (cartesianProperFlatProjection B S hS).IsHomLift
    ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) ε := hε
  have hφ' : (cartesianProperFlatProjection B S hS).IsHomLift
    (𝟙 ((BigAffineFppf.inclusion B S hS).obj c.pt)) φ := hφ
  have : (cartesianProperFlatProjection B S hS).IsStronglyCartesian
      (𝟙 ((BigAffineFppf.inclusion B S hS).obj c.pt)) φ :=
    (cartesianProperFlatProjection_isFiberedInGroupoids B S hS).isStronglyCartesian_homLift _ φ
  have : IsIso φ :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso (cartesianProperFlatProjection B S hS)
      (𝟙 ((BigAffineFppf.inclusion B S hS).obj c.pt)) φ
  have : IsIso (ProperFlatFibre.map φ) :=
    Functor.map_isIso (ProperFlatFibre.underlying B S hS) φ
  have hd := ProperFlatFibre.isPullback_map δ
    ((BigAffineFppf.inclusion B S hS).map (c.π.app i))
  have he := ProperFlatFibre.isPullback_map ε
    ((BigAffineFppf.inclusion B S hS).map (c.π.app i))
  have hu : (hd.isoPullback.inv ≫ ProperFlatFibre.map φ ≫ he.isoPullback.hom) ≫
      pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i)))
        (ProperFlatFibre.str yi) =
      pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i)))
        (ProperFlatFibre.str xi) := by
    simp only [Category.assoc, IsPullback.isoPullback_hom_fst]
    rw [ProperFlatFibre.map_str_id φ, hd.isoPullback_inv_fst]
  obtain ⟨hfp, hfl, hpr⟩ := ProperFlatFibre.str_properties xi
  obtain ⟨hgp, hgl, hgr⟩ := ProperFlatFibre.str_properties yi
  obtain ⟨k, s, v, hviso, hvfst, hvcompat⟩ := h I D c hc i _ _
    (ProperFlatFibre.isAlgebraicSpace_space xi) (ProperFlatFibre.isAlgebraicSpace_space yi)
    (ProperFlatFibre.str xi) (ProperFlatFibre.str yi) hfp hfl hpr hgp hgl hgr
    (hd.isoPullback.inv ≫ ProperFlatFibre.map φ ≫ he.isoPullback.hom) inferInstance hu
  have := hviso
  have hfac : (BigAffineFppf.inclusion B S hS).map (c.π.app i) =
      (BigAffineFppf.inclusion B S hS).map (c.π.app k) ≫
        (BigAffineFppf.inclusion B S hS).map (D.map s) := by
    rw [← Functor.map_comp, c.w s]
  have hdx := ProperFlatFibre.isHomLift_pullMap_mk xi
    ((BigAffineFppf.inclusion B S hS).map (D.map s))
  have hdy := ProperFlatFibre.isHomLift_pullMap_mk yi
    ((BigAffineFppf.inclusion B S hS).map (D.map s))
  have hcx : (cartesianProperFlatProjection B S hS).IsStronglyCartesian
      ((BigAffineFppf.inclusion B S hS).map (D.map s))
      (ProperFlatFibre.pullMap xi
        (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))) :=
    (cartesianProperFlatProjection_isFiberedInGroupoids B S hS).isStronglyCartesian_homLift _ _
  have px_fst : (ProperFlatFibre.pullIso xi
        (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))).hom ≫
      pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s)))
        (ProperFlatFibre.str xi) =
      ProperFlatFibre.str (ProperFlatFibre.pull xi
        (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))) :=
    ProperFlatFibre.pullIso_hom_fst xi _
  have px_snd : (ProperFlatFibre.pullIso xi
        (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))).hom ≫
      pullback.snd (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s)))
        (ProperFlatFibre.str xi) =
      ProperFlatFibre.map (ProperFlatFibre.pullMap xi
        (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))) :=
    ProperFlatFibre.pullIso_hom_snd xi _
  have py_fst : (ProperFlatFibre.pullIso yi
        (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))).inv ≫
      ProperFlatFibre.str (ProperFlatFibre.pull yi
        (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))) =
      pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s)))
        (ProperFlatFibre.str yi) :=
    ProperFlatFibre.pullIso_inv_fst yi _
  have py_snd : (ProperFlatFibre.pullIso yi
        (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))).inv ≫
      ProperFlatFibre.map (ProperFlatFibre.pullMap yi
        (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))) =
      pullback.snd (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s)))
        (ProperFlatFibre.str yi) :=
    ProperFlatFibre.pullIso_inv_snd yi _
  have hee : (ProperFlatFibre.pullIso xi
        (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s))) ≪≫ asIso v ≪≫
        (ProperFlatFibre.pullIso yi
          (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))).symm).hom ≫
      ProperFlatFibre.str (ProperFlatFibre.pull yi
        (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))) =
      ProperFlatFibre.str (ProperFlatFibre.pull xi
        (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))) := by
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
    rw [py_fst, hvfst, px_fst]
  obtain ⟨δk, hδk, hδkfac⟩ : ∃ δk : x.val ⟶ (ProperFlatFibre.pull xi
        (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))).val,
      (cartesianProperFlatProjection B S hS).IsHomLift
          ((BigAffineFppf.inclusion B S hS).map (c.π.app k)) δk ∧
        δk ≫ ProperFlatFibre.pullMap xi
          (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s))) = δ :=
    ⟨Functor.IsStronglyCartesian.map (cartesianProperFlatProjection B S hS) _ _ hfac δ,
      inferInstance,
      Functor.IsStronglyCartesian.fac (cartesianProperFlatProjection B S hS) _ _ hfac δ⟩
  have := hδk
  obtain ⟨ψ, hψlift, hψmap⟩ : ∃ ψ : (ProperFlatFibre.pull xi
        (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))).val ⟶
      (ProperFlatFibre.pull yi
        (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))).val,
      (cartesianProperFlatProjection B S hS).IsHomLift
          (𝟙 ((BigAffineFppf.inclusion B S hS).obj (D.obj k))) ψ ∧
        ProperFlatFibre.map ψ =
          (ProperFlatFibre.pullIso xi
            (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))).hom ≫ v ≫
            (ProperFlatFibre.pullIso yi
              (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))).inv :=
    ⟨(ProperFlatFibre.isoOfUnderlying _ _ _ hee).hom.val,
      (ProperFlatFibre.isoOfUnderlying _ _ _ hee).hom.property, by
        rw [ProperFlatFibre.isoOfUnderlying_hom]
        simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom]⟩
  have := hψlift
  refine ⟨k, s,
    ProperFlatFibre.pull xi (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s))),
    ProperFlatFibre.pull yi (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s))),
    ProperFlatFibre.pullMap xi (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s))),
    ProperFlatFibre.pullMap yi (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s))),
    δk, ψ, hdx, hdy, hδk, hψlift, hδkfac, ?_⟩
  have : (cartesianProperFlatProjection B S hS).IsHomLift
      ((BigAffineFppf.inclusion B S hS).map (c.π.app i))
      (δk ≫ ψ ≫ ProperFlatFibre.pullMap yi
        (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))) := by
    rw [hfac]; infer_instance
  have : (cartesianProperFlatProjection B S hS).IsHomLift
      ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) (φ ≫ ε) :=
    IsHomLift.comp_lift_id_left' (cartesianProperFlatProjection B S hS)
      ((BigAffineFppf.inclusion B S hS).obj c.pt) φ
      ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) ε
  refine ProperFlatFibre.map_injective_of_isHomLift
    ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) ?_
  have key : ProperFlatFibre.map δk ≫ (ProperFlatFibre.pullIso xi
        (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))).hom =
      hd.isoPullback.hom ≫ coneBaseRestrict c s (ProperFlatFibre.str xi) := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Over.mk_hom]
      rw [Category.assoc, Category.assoc, px_fst, coneBaseRestrict_fst,
        ProperFlatFibre.map_str δk ((BigAffineFppf.inclusion B S hS).map (c.π.app k)),
        IsPullback.isoPullback_hom_fst_assoc]
    · simp only [Over.mk_hom]
      rw [Category.assoc, Category.assoc, px_snd, coneBaseRestrict_snd,
        IsPullback.isoPullback_hom_snd]
      exact Eq.trans ((ProperFlatFibre.underlying B S hS).map_comp δk _).symm
        (congrArg (ProperFlatFibre.underlying B S hS).map hδkfac)
  calc (ProperFlatFibre.underlying B S hS).map
        (δk ≫ ψ ≫ ProperFlatFibre.pullMap yi
          (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s))))
      = ProperFlatFibre.map δk ≫ ProperFlatFibre.map ψ ≫
          ProperFlatFibre.map (ProperFlatFibre.pullMap yi
            (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))) := by
        rw [Functor.map_comp, Functor.map_comp]
    _ = (ProperFlatFibre.map δk ≫ (ProperFlatFibre.pullIso xi
            (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))).hom) ≫ v ≫
          ((ProperFlatFibre.pullIso yi
            (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s)))).inv ≫
            ProperFlatFibre.map (ProperFlatFibre.pullMap yi
              (Over.mk ((BigAffineFppf.inclusion B S hS).map (D.map s))))) := by
        rw [hψmap]; simp only [Category.assoc]
    _ = hd.isoPullback.hom ≫ (coneBaseRestrict c s (ProperFlatFibre.str xi) ≫ v) ≫
          pullback.snd (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s)))
            (ProperFlatFibre.str yi) := by
        rw [key, py_snd]; simp only [Category.assoc]
    _ = hd.isoPullback.hom ≫ ((hd.isoPullback.inv ≫ ProperFlatFibre.map φ ≫
            he.isoPullback.hom) ≫ coneBaseRestrict c s (ProperFlatFibre.str yi)) ≫
          pullback.snd (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s)))
            (ProperFlatFibre.str yi) := by
        rw [hvcompat]
    _ = (ProperFlatFibre.underlying B S hS).map (φ ≫ ε) := by
        rw [Functor.map_comp]
        simp only [Category.assoc, coneBaseRestrict_snd, IsPullback.isoPullback_hom_snd,
          Iso.hom_inv_id_assoc]

end HomDescent

end AlgebraicGeometry

end
