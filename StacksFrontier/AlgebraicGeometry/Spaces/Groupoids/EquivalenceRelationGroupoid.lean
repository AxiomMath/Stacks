module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces

/-!
# Equivalence relations extend uniquely to groupoids in algebraic spaces

Let `B` be an algebraic space over a scheme `S` of a big fppf site and let `U` and `R` be
algebraic spaces over `B`. An equivalence relation `j : R ⟶ U ×_B U` over `B` carries exactly
the data of a groupoid in algebraic spaces over `B`: the source and the target of the groupoid
are the two components of `j`, and the composition law is then forced, because an arrow of such
a groupoid is determined by its source and its target. This is **Stacks 043Y**.

## Main definitions

* `AlgebraicGeometry.Space.ExtendsRelation`: the assertion that a groupoid in algebraic spaces
  has the object space, the arrow space, the two morphisms to the base, and the source and
  target morphisms prescribed by a pre-relation.
* `AlgebraicGeometry.Space.groupoidOfIsEquivalenceRelation`: the groupoid in algebraic spaces
  extending an equivalence relation.
* `AlgebraicGeometry.Space.PreRelation.SectionRel`: the relation induced by a pre-relation on the
  sections of the object space over a test scheme, and
  `AlgebraicGeometry.Space.PreRelation.pointwiseOfEquivalence`, the groupoid it gives there.
* `AlgebraicGeometry.Space.PreRelation.transitiveComp`: the composition morphism of the extending
  groupoid, the transitivity morphism of the internal relation read on the space of composable
  pairs `AlgebraicGeometry.Space.PreRelation.composablePairs`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_groupoid_of_isEquivalenceRelation`: **Stacks 043Y**, an
  equivalence relation of algebraic spaces over `B` extends to a groupoid in algebraic spaces
  over `B` in exactly one way.
* `AlgebraicGeometry.Space.groupoidOfIsEquivalenceRelation_extendsRelation`: the groupoid
  constructed here is such an extension.
* `AlgebraicGeometry.Space.source_comp_section` and
  `AlgebraicGeometry.Space.target_comp_section`: in any groupoid in algebraic spaces the
  composite of a composable pair of arrows has the source of the second arrow and the target of
  the first.

## Implementation notes

The pre-relation is taken, as in **Stacks 043C** and as for
`AlgebraicGeometry.Space.groupoidPreRelation`, in the slice of *presheaves* over the underlying
presheaf of the base: by **Stacks 02X2** the fibre product of algebraic spaces is the presheaf
one, so for algebraic `U` and `R` this is the pre-relation of the source, and the statement is
literally about the pre-relation that **Stacks 043X** attaches to a groupoid.

The object and arrow spaces of a bundled groupoid in algebraic spaces are data, so "this
groupoid extends this relation" is recorded by `ExtendsRelation`, whose morphism conditions are
transported along the equalities of spaces by `CategoryTheory.eqToHom`. Uniqueness is therefore
uniqueness of the whole bundle, composition included, which is the content of the lemma.

Over a test scheme the groupoid is the thin groupoid of the induced equivalence relation on the
sections of the object space, an arrow from `x` to `y` being the mere existence of a section of
the arrow space with source `x` and target `y`; the identification of its arrows with sections
of `R` chooses such a section, and this is a bijection because `j` is a monomorphism
(`AlgebraicGeometry.Space.PreRelation.testPoint_eq_of_mono`). The composition morphism of
algebraic spaces is the transitivity morphism of the internal equivalence relation, taken on
the fibre product `R ×_{s, U, t} R`; monicity is again what forces it to be the only possible
one, since `AlgebraicGeometry.Space.source_comp_section` and
`AlgebraicGeometry.Space.target_comp_section` already pin down the two endpoints of a composite
in *any* extending groupoid.

The pointwise characterization
`AlgebraicGeometry.Space.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation` is what
converts the internal hypothesis into the monomorphism and the equivalence relations on test
points that both halves of the proof use.

The auxiliary notions attached to a pre-relation live in the `AlgebraicGeometry.Space.PreRelation`
namespace, beside `AlgebraicGeometry.Space.PreRelation.testPoint_eq_of_mono`. They are not
private, because the construction of the extending groupoid uses them in its *body* and the
equalities `AlgebraicGeometry.Space.groupoidOfIsEquivalenceRelation_extendsRelation` reads that
body off.

## References

* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 043X](https://stacks.math.columbia.edu/tag/043X)
* [Stacks Project, Tag 043Y](https://stacks.math.columbia.edu/tag/043Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B U R : AlgebraicSpaces C S hS} {qU : U ⟶ B} {qR : R ⟶ B}

/-! ### Sections of the space of composable pairs -/

/-- The first projection of the image of a composable pair in the presheaf fibre product is the
first member of the pair. -/
private theorem composableToPullback_app_fst
    {F G : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (s t : G ⟶ F)
    (T : (BigFppfOver C S hS)ᵒᵖ) (p : (Deformation.composableArrows F G s t).obj T) :
    (pullback.fst s t).app T ((composableToPullback s t).app T p) = p.1.1 := by
  change (composableToPullback s t ≫ pullback.fst s t).app T p = p.1.1
  rw [composableToPullback, pullback.lift_fst]
  rfl

/-- The second projection of the image of a composable pair in the presheaf fibre product is the
second member of the pair. -/
private theorem composableToPullback_app_snd
    {F G : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (s t : G ⟶ F)
    (T : (BigFppfOver C S hS)ᵒᵖ) (p : (Deformation.composableArrows F G s t).obj T) :
    (pullback.snd s t).app T ((composableToPullback s t).app T p) = p.1.2 := by
  change (composableToPullback s t ≫ pullback.snd s t).app T p = p.1.2
  rw [composableToPullback, pullback.lift_snd]
  rfl

/-- Two sections of a fibre product of algebraic spaces over a test object agree as soon as
their two projections do, fibre products of presheaves being computed pointwise. -/
private theorem fibreProduct_section_ext {X Y Z : AlgebraicSpaces C S hS}
    (f : X ⟶ Z) (g : Y ⟶ Z) (T : (BigFppfOver C S hS)ᵒᵖ)
    {p q : (AlgebraicSpaces.fiberProduct C S hS f g).obj.obj T}
    (hfst : (pullback.fst f.hom g.hom).app T p = (pullback.fst f.hom g.hom).app T q)
    (hsnd : (pullback.snd f.hom g.hom).app T p = (pullback.snd f.hom g.hom).app T q) : p = q := by
  apply (fiberProductAtEquiv f g T).injective
  apply Subtype.ext
  apply Prod.ext
  · rw [fiberProductAtEquiv_fst, fiberProductAtEquiv_fst, hfst]
  · rw [fiberProductAtEquiv_snd, fiberProductAtEquiv_snd, hsnd]

/-- Every section of the fibre product `R ×_{s, U, t} R` over a test object comes from a
composable pair whose members are its two projections. -/
private theorem exists_composablePair_eq
    {X Y : AlgebraicSpaces C S hS} (f g : X ⟶ Y) (T : (BigFppfOver C S hS)ᵒᵖ)
    (p : (AlgebraicSpaces.fiberProduct C S hS f g).obj.obj T) :
    ∃ q : (Deformation.composableArrows _ _ f.hom g.hom).obj T,
      (composableToPullback f.hom g.hom).app T q = p ∧
        q.1.1 = (pullback.fst f.hom g.hom).app T p ∧ q.1.2 = (pullback.snd f.hom g.hom).app T p :=
  ⟨fiberProductAtEquiv f g T p,
    fibreProduct_section_ext f g T
      ((composableToPullback_app_fst _ _ T _).trans (fiberProductAtEquiv_fst f g T p))
      ((composableToPullback_app_snd _ _ T _).trans (fiberProductAtEquiv_snd f g T p)),
    fiberProductAtEquiv_fst f g T p, fiberProductAtEquiv_snd f g T p⟩

/-! ### The endpoints of a composite in a groupoid in algebraic spaces -/

/-- **Stacks 043W.** The composite of a composable pair of arrows of a groupoid in algebraic
spaces has the source of the second arrow: this holds for the composition morphism carried by
the structure, evaluated at any section of the fibre product `R ×_{s, U, t} R`. -/
theorem source_comp_section (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (p : (AlgebraicSpaces.fiberProduct C S hS G.source G.target).obj.obj T) :
    G.source.hom.app T (G.comp.hom.app T p) =
      G.source.hom.app T ((pullback.snd G.source.hom G.target.hom).app T p) := by
  obtain ⟨q, hq, -, hsnd⟩ := exists_composablePair_eq G.source G.target T p
  rw [← hsnd, ← hq]
  exact (Classical.choice (G.pointwiseGroupoid T)).source_comp q.1.1 q.1.2 q.2

/-- **Stacks 043W.** The composite of a composable pair of arrows of a groupoid in algebraic
spaces has the target of the first arrow: this holds for the composition morphism carried by
the structure, evaluated at any section of the fibre product `R ×_{s, U, t} R`. -/
theorem target_comp_section (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (p : (AlgebraicSpaces.fiberProduct C S hS G.source G.target).obj.obj T) :
    G.target.hom.app T (G.comp.hom.app T p) =
      G.target.hom.app T ((pullback.fst G.source.hom G.target.hom).app T p) := by
  obtain ⟨q, hq, hfst, -⟩ := exists_composablePair_eq G.source G.target T p
  rw [← hfst, ← hq]
  exact (Classical.choice (G.pointwiseGroupoid T)).target_comp q.1.1 q.1.2 q.2

/-! ### Sections of the arrow space -/

/-- The base point of the image of a section under a morphism over the base is the base point of
the section. -/
private theorem yonedaEquiv_symm_app_comp (f : Over.mk qR.hom ⟶ Over.mk qU.hom)
    (T : BigFppfOver C S hS) (a : R.obj.obj (op T)) :
    yonedaEquiv.symm (f.left.app (op T) a) ≫ qU.hom = yonedaEquiv.symm a ≫ qR.hom := by
  rw [← yonedaEquiv_symm_naturality_right T f.left a, Category.assoc]
  exact congrArg _ (Over.w f)

namespace PreRelation

/-- A section of the arrow space of a *relation* is determined by its source and its target. -/
theorem section_eq_of_endpoints (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    (hj : Mono j) {T : BigFppfOver C S hS} {a b : R.obj.obj (op T)}
    (hs : j.source.left.app (op T) a = j.source.left.app (op T) b)
    (ht : j.target.left.app (op T) a = j.target.left.app (op T) b) : a = b := by
  have hsa := yonedaEquiv_symm_app_comp j.source T a
  have hsb := yonedaEquiv_symm_app_comp j.source T b
  have hta := yonedaEquiv_symm_app_comp j.target T a
  have hbase : yonedaEquiv.symm b ≫ qR.hom = yonedaEquiv.symm a ≫ qR.hom := by
    rw [← hsa, ← hsb, hs]
  have h := PreRelation.testPoint_eq_of_mono j
    (b := yonedaEquiv.symm a ≫ qR.hom)
    (x := ⟨yonedaEquiv.symm (j.target.left.app (op T) a), hta⟩)
    (y := ⟨yonedaEquiv.symm (j.source.left.app (op T) a), hsa⟩)
    (r := ⟨yonedaEquiv.symm a, rfl⟩)
    (s := ⟨yonedaEquiv.symm b, hbase⟩)
    (yonedaEquiv_symm_naturality_right T j.target.left a)
    (yonedaEquiv_symm_naturality_right T j.source.left a)
    (by rw [yonedaEquiv_symm_naturality_right T j.target.left b, ← ht])
    (by rw [yonedaEquiv_symm_naturality_right T j.source.left b, ← hs])
  exact yonedaEquiv.symm.injective h

/-- Two sections of the object space over a test scheme are *related* when some section of the
arrow space has them as its source and as its target. -/
def SectionRel (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    (T : BigFppfOver C S hS) (x y : U.obj.obj (op T)) : Prop :=
  ∃ a : R.obj.obj (op T), j.source.left.app (op T) a = x ∧ j.target.left.app (op T) a = y

/-- A chosen section of the arrow space joining a related pair of sections of the object
space. -/
def sectionRelArrow (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    {T : BigFppfOver C S hS} {x y : U.obj.obj (op T)} (h : SectionRel j T x y) :
    {a : R.obj.obj (op T) //
      j.source.left.app (op T) a = x ∧ j.target.left.app (op T) a = y} :=
  ⟨Classical.choose h, Classical.choose_spec h⟩

/-- Related sections of the object space lie over the same point of the base. -/
private theorem base_eq_of_sectionRel (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    {T : BigFppfOver C S hS} {x y : U.obj.obj (op T)} (h : SectionRel j T x y) :
    yonedaEquiv.symm y ≫ qU.hom = yonedaEquiv.symm x ≫ qU.hom := by
  obtain ⟨a, hsa, hta⟩ := h
  rw [← hsa, ← hta, yonedaEquiv_symm_app_comp j.source T a, yonedaEquiv_symm_app_comp j.target T a]

/-- A related pair of sections of the object space is a related pair of test points. -/
private theorem rel_of_sectionRel (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    {T : BigFppfOver C S hS} {x y : U.obj.obj (op T)} (h : SectionRel j T x y)
    (b : yoneda.obj T ⟶ B.obj) (hx : yonedaEquiv.symm x ≫ qU.hom = b)
    (hy : yonedaEquiv.symm y ≫ qU.hom = b) :
    j.Rel b ⟨yonedaEquiv.symm y, hy⟩ ⟨yonedaEquiv.symm x, hx⟩ := by
  obtain ⟨a, hsa, hta⟩ := h
  refine ⟨⟨yonedaEquiv.symm a, ?_⟩, ?_, ?_⟩
  · change yonedaEquiv.symm a ≫ qR.hom = b
    rw [← yonedaEquiv_symm_app_comp j.source T a, hsa, hx]
  · rw [yonedaEquiv_symm_naturality_right T j.target.left a, hta]
  · rw [yonedaEquiv_symm_naturality_right T j.source.left a, hsa]

/-- A related pair of test points is a related pair of sections of the object space. -/
private theorem sectionRel_of_rel (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    {T : BigFppfOver C S hS} {b : yoneda.obj T ⟶ B.obj}
    {x y : TestPoint T b (Over.mk qU.hom)} (h : j.Rel b x y) :
    SectionRel j T (yonedaEquiv y.1) (yonedaEquiv x.1) := by
  obtain ⟨r, ht, hs⟩ := h
  refine ⟨yonedaEquiv r.1, ?_, ?_⟩
  · rw [← yonedaEquiv_comp r.1 j.source.left, hs]
  · rw [← yonedaEquiv_comp r.1 j.target.left, ht]

/-- The relation induced on the sections of the object space over a test scheme by a
pre-equivalence relation is an equivalence relation. -/
theorem sectionRel_equivalence (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    (he : IsPreEquivalenceRelation j) (T : BigFppfOver C S hS) :
    Equivalence (SectionRel j T) where
  refl x := by
    have h := (he T (yonedaEquiv.symm x ≫ qU.hom)).refl
      (⟨yonedaEquiv.symm x, rfl⟩ : TestPoint T _ (Over.mk qU.hom))
    simpa using sectionRel_of_rel j h
  symm {x y} h := by
    have hb := base_eq_of_sectionRel j h
    have hrel := rel_of_sectionRel j h (yonedaEquiv.symm x ≫ qU.hom) rfl hb
    simpa using sectionRel_of_rel j ((he T (yonedaEquiv.symm x ≫ qU.hom)).symm hrel)
  trans {x y z} h₁ h₂ := by
    have hby := base_eq_of_sectionRel j h₁
    have hbz := base_eq_of_sectionRel j h₂
    have hrel₁ := rel_of_sectionRel j h₁ (yonedaEquiv.symm x ≫ qU.hom) rfl hby
    have hrel₂ := rel_of_sectionRel j h₂ (yonedaEquiv.symm x ≫ qU.hom) hby (hbz.trans hby)
    simpa using
      sectionRel_of_rel j ((he T (yonedaEquiv.symm x ≫ qU.hom)).trans hrel₂ hrel₁)

/-- The thin groupoid of the induced equivalence relation on the sections of the object space
over a test scheme, for any composition map with the expected endpoints. -/
def pointwiseOfEquivalence (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    (hj : Mono j) (he : IsPreEquivalenceRelation j) (T : BigFppfOver C S hS)
    (cmp : {p : R.obj.obj (op T) × R.obj.obj (op T) //
        j.source.left.app (op T) p.1 = j.target.left.app (op T) p.2} → R.obj.obj (op T))
    (hcs : ∀ p, j.source.left.app (op T) (cmp p) = j.source.left.app (op T) p.1.2)
    (hct : ∀ p, j.target.left.app (op T) (cmp p) = j.target.left.app (op T) p.1.1) :
    Deformation.PointwiseGroupoid
      (j.source.left.app (op T)) (j.target.left.app (op T)) cmp := by
  classical
  letI : Category.{u, u} (U.obj.obj (op T)) :=
    { Hom x y := ULift.{u, 0} (PLift (SectionRel j T x y))
      id x := ULift.up (PLift.up ((sectionRel_equivalence j he T).refl x))
      comp f g :=
        ULift.up (PLift.up ((sectionRel_equivalence j he T).trans f.down.down g.down.down))
      id_comp _ := rfl
      comp_id _ := rfl
      assoc _ _ _ := rfl }
  letI grp : Groupoid.{u} (U.obj.obj (op T)) :=
    { inv f := ULift.up (PLift.up ((sectionRel_equivalence j he T).symm f.down.down))
      inv_comp _ := rfl
      comp_inv _ := rfl }
  let ae : ∀ x y : U.obj.obj (op T), (x ⟶ y) ≃
      {a : R.obj.obj (op T) //
        j.source.left.app (op T) a = x ∧ j.target.left.app (op T) a = y} := fun x y =>
    { toFun f := sectionRelArrow j f.down.down
      invFun a := ULift.up (PLift.up ⟨a.1, a.2.1, a.2.2⟩)
      left_inv _ := rfl
      right_inv a := by
        refine Subtype.ext (section_eq_of_endpoints j hj ?_ ?_)
        · exact (sectionRelArrow j _).2.1.trans a.2.1.symm
        · exact (sectionRelArrow j _).2.2.trans a.2.2.symm }
  refine ⟨grp, ae, fun {x y z} g f => ?_⟩
  have hpair : j.source.left.app (op T) (ae y z f).1 =
      j.target.left.app (op T) (ae x y g).1 := ((ae y z f).2.1).trans ((ae x y g).2.2).symm
  refine section_eq_of_endpoints j hj ?_ ?_
  · rw [hcs ⟨((ae y z f).1, (ae x y g).1), hpair⟩]
    exact ((ae x z (g ≫ f)).2.1).trans ((ae x y g).2.1).symm
  · rw [hct ⟨((ae y z f).1, (ae x y g).1), hpair⟩]
    exact ((ae x z (g ≫ f)).2.2).trans ((ae y z f).2.2).symm

/-! ### The extension of an equivalence relation -/

/-- A chosen internal equivalence relation structure on the two components of an equivalence
relation. -/
def chosenRelation (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    [IsEquivalenceRelation j.target j.source] : EquivalenceRelation j.target j.source :=
  Classical.choice IsEquivalenceRelation.nonempty_equivalenceRelation

/-- The space of composable pairs of arrows, as an object over the base. -/
@[sga "3 V 1.2" "special case"]
abbrev composablePairs (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom)) :
    Over B.obj :=
  Over.mk (pullback.fst j.source.left j.target.left ≫ qR.hom)

/-- The first arrow of a composable pair. -/
def firstArrow (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom)) :
    composablePairs j ⟶ Over.mk qR.hom :=
  Over.homMk (pullback.fst j.source.left j.target.left)

/-- The second arrow of a composable pair. -/
def secondArrow (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom)) :
    composablePairs j ⟶ Over.mk qR.hom :=
  Over.homMk (pullback.snd j.source.left j.target.left) (by
    have hws : j.source.left ≫ qU.hom = qR.hom := Over.w j.source
    have hwt : j.target.left ≫ qU.hom = qR.hom := Over.w j.target
    change pullback.snd j.source.left j.target.left ≫ qR.hom =
      pullback.fst j.source.left j.target.left ≫ qR.hom
    calc pullback.snd j.source.left j.target.left ≫ qR.hom
        = pullback.snd j.source.left j.target.left ≫ j.target.left ≫ qU.hom := by
          rw [hwt]
      _ = (pullback.snd j.source.left j.target.left ≫ j.target.left) ≫ qU.hom :=
          (Category.assoc _ _ _).symm
      _ = (pullback.fst j.source.left j.target.left ≫ j.source.left) ≫ qU.hom := by
          rw [pullback.condition]
      _ = pullback.fst j.source.left j.target.left ≫ qR.hom := by
          rw [Category.assoc, hws])

/-- The two arrows of a composable pair are composable. -/
theorem firstArrow_comp_source (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom)) :
    firstArrow j ≫ j.source = secondArrow j ≫ j.target := by
  apply CategoryTheory.Over.OverMorphism.ext
  change pullback.fst j.source.left j.target.left ≫ j.source.left =
    pullback.snd j.source.left j.target.left ≫ j.target.left
  exact pullback.condition

/-- The composition morphism of the extending groupoid: the transitivity morphism of the
internal relation, read on the space of composable pairs. -/
def transitiveComp (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    (e : TransitiveRelation j.target j.source) :
    AlgebraicSpaces.fiberProduct C S hS
        (ObjectProperty.homMk j.source.left : R ⟶ U)
        (ObjectProperty.homMk j.target.left : R ⟶ U) ⟶ R :=
  ObjectProperty.homMk
    (PullbackCone.IsLimit.lift e.isLimit (firstArrow j) (secondArrow j)
      (firstArrow_comp_source j) ≫ e.t).left

/-- The composition morphism is a morphism over the base. -/
theorem transitiveComp_comp_base (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    (e : TransitiveRelation j.target j.source) :
    (transitiveComp j e).hom ≫ qR.hom =
      pullback.fst j.source.left j.target.left ≫ qR.hom :=
  Over.w (PullbackCone.IsLimit.lift e.isLimit (firstArrow j) (secondArrow j)
    (firstArrow_comp_source j) ≫ e.t)

/-- The composite of a composable pair has the target of its first arrow. -/
private theorem transitiveComp_comp_target (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    (e : TransitiveRelation j.target j.source) :
    (transitiveComp j e).hom ≫ j.target.left =
      pullback.fst j.source.left j.target.left ≫ j.target.left := by
  have h : (PullbackCone.IsLimit.lift e.isLimit (firstArrow j) (secondArrow j)
      (firstArrow_comp_source j) ≫ e.t) ≫ j.target = firstArrow j ≫ j.target := by
    rw [Category.assoc, e.transitivity₁, ← Category.assoc,
      PullbackCone.IsLimit.lift_fst]
  exact congrArg (fun k : composablePairs j ⟶ Over.mk qU.hom => k.left) h

/-- The composite of a composable pair has the source of its second arrow. -/
private theorem transitiveComp_comp_source (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    (e : TransitiveRelation j.target j.source) :
    (transitiveComp j e).hom ≫ j.source.left =
      pullback.snd j.source.left j.target.left ≫ j.source.left := by
  have h : (PullbackCone.IsLimit.lift e.isLimit (firstArrow j) (secondArrow j)
      (firstArrow_comp_source j) ≫ e.t) ≫ j.source = secondArrow j ≫ j.source := by
    rw [Category.assoc, e.transitivity₂, ← Category.assoc,
      PullbackCone.IsLimit.lift_snd]
  exact congrArg (fun k : composablePairs j ⟶ Over.mk qU.hom => k.left) h

/-- Evaluating a composite `a ≫ c` of presheaf morphisms, followed by `f`, only depends on
`c ≫ f`. -/
private theorem app_comp_comp_eq {X Y Z W : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (a : X ⟶ Y) (c : Y ⟶ Z) (f : Z ⟶ W) (g : Y ⟶ W) (h : c ≫ f = g)
    (T : (BigFppfOver C S hS)ᵒᵖ) (p : X.obj T) :
    f.app T ((a ≫ c).app T p) = g.app T (a.app T p) := by
  rw [← h]
  rfl

/-- The source of the composite of a composable pair of sections. -/
theorem transitiveComp_section_source
    (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    (e : TransitiveRelation j.target j.source) (T : BigFppfOver C S hS)
    (p : (Deformation.composableArrows U.obj R.obj j.source.left j.target.left).obj (op T)) :
    j.source.left.app (op T)
        ((composableToPullback j.source.left j.target.left ≫
          (transitiveComp j e).hom).app (op T) p) =
      j.source.left.app (op T) p.1.2 :=
  (app_comp_comp_eq _ _ _ _ (transitiveComp_comp_source j e) _ p).trans
    (congrArg (j.source.left.app (op T)) (composableToPullback_app_snd _ _ (op T) p))

/-- The target of the composite of a composable pair of sections. -/
theorem transitiveComp_section_target
    (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    (e : TransitiveRelation j.target j.source) (T : BigFppfOver C S hS)
    (p : (Deformation.composableArrows U.obj R.obj j.source.left j.target.left).obj (op T)) :
    j.target.left.app (op T)
        ((composableToPullback j.source.left j.target.left ≫
          (transitiveComp j e).hom).app (op T) p) =
      j.target.left.app (op T) p.1.1 :=
  (app_comp_comp_eq _ _ _ _ (transitiveComp_comp_target j e) _ p).trans
    (congrArg (j.target.left.app (op T)) (composableToPullback_app_fst _ _ (op T) p))

end PreRelation

/-- A groupoid in algebraic spaces over `B` *extends* a pre-relation `j` when its object and
arrow spaces are those of `j`, their structure morphisms to `B` are those of `j`, and its
source and target morphisms are the two components of `j`. -/
structure ExtendsRelation (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    (G : GroupoidInAlgebraicSpaces C S hS B) : Prop where
  /-- The space of objects is `U`. -/
  objects_eq : G.objects = U
  /-- The space of arrows is `R`. -/
  arrows_eq : G.arrows = R
  /-- The space of objects lies over `B` through the structure morphism of `U`. -/
  objectsToBase_eq : eqToHom objects_eq.symm ≫ G.objectsToBase = qU
  /-- The space of arrows lies over `B` through the structure morphism of `R`. -/
  arrowsToBase_eq : eqToHom arrows_eq.symm ≫ G.arrowsToBase = qR
  /-- The source morphism is the source of the relation. -/
  source_eq : eqToHom arrows_eq.symm ≫ G.source ≫ eqToHom objects_eq =
    ObjectProperty.homMk j.source.left
  /-- The target morphism is the target of the relation. -/
  target_eq : eqToHom arrows_eq.symm ≫ G.target ≫ eqToHom objects_eq =
    ObjectProperty.homMk j.target.left

/-- **Stacks 043Y.** The groupoid in algebraic spaces over `B` extending an equivalence relation
`j : R ⟶ U ×_B U` over `B`: its object and arrow spaces are `U` and `R`, its source and target
are the two components of `j`, and its composition is the transitivity morphism of `j`. -/
def groupoidOfIsEquivalenceRelation (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    [IsEquivalenceRelation j.target j.source] : GroupoidInAlgebraicSpaces C S hS B where
  objects := U
  arrows := R
  objectsToBase := qU
  arrowsToBase := qR
  source := ObjectProperty.homMk j.source.left
  target := ObjectProperty.homMk j.target.left
  source_over := ObjectProperty.hom_ext _ (Over.w j.source)
  target_over := ObjectProperty.hom_ext _ (Over.w j.target)
  comp := j.transitiveComp j.chosenRelation.toTransitiveRelation
  comp_over :=
    ObjectProperty.hom_ext _
      (j.transitiveComp_comp_base j.chosenRelation.toTransitiveRelation)
  pointwiseGroupoid := by
    intro T
    have hj := (isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).mp inferInstance
    refine ⟨j.pointwiseOfEquivalence hj.1 hj.2 T.unop _ ?_ ?_⟩
    · exact j.transitiveComp_section_source j.chosenRelation.toTransitiveRelation T.unop
    · exact j.transitiveComp_section_target j.chosenRelation.toTransitiveRelation T.unop

/-- The groupoid of **Stacks 043Y** does extend the given equivalence relation. -/
theorem groupoidOfIsEquivalenceRelation_extendsRelation
    (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    [IsEquivalenceRelation j.target j.source] :
    ExtendsRelation j (groupoidOfIsEquivalenceRelation j) where
  objects_eq := rfl
  arrows_eq := rfl
  objectsToBase_eq := by
    change 𝟙 U ≫ qU = qU
    simp
  arrowsToBase_eq := by
    change 𝟙 R ≫ qR = qR
    simp
  source_eq := by
    change 𝟙 R ≫ ObjectProperty.homMk j.source.left ≫ 𝟙 U = ObjectProperty.homMk j.source.left
    simp
  target_eq := by
    change 𝟙 R ≫ ObjectProperty.homMk j.target.left ≫ 𝟙 U = ObjectProperty.homMk j.target.left
    simp

/-- A groupoid in algebraic spaces over `B` whose object and arrow spaces are `U` and `R` over
the base and whose source and target are the two components of an equivalence relation `j` is
the groupoid `AlgebraicGeometry.Space.groupoidOfIsEquivalenceRelation j`: its composition is
forced, an arrow of such a groupoid being determined by its source and its target.

The two morphisms are given as `s` and `t` together with the equalities identifying them, and
the three remaining fields of the groupoid are quantified inside the statement, so that `s` and
`t` can be rewritten before those fields, whose types depend on them, are in scope. -/
private theorem mk_eq_groupoidOfIsEquivalenceRelation
    (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    [IsEquivalenceRelation j.target j.source] {s t : R ⟶ U}
    (hs : s = ObjectProperty.homMk j.source.left)
    (ht : t = ObjectProperty.homMk j.target.left) :
    ∀ (hso : s ≫ qU = qR) (hto : t ≫ qU = qR)
      (c : AlgebraicSpaces.fiberProduct C S hS s t ⟶ R)
      (hco : c ≫ qR = (ObjectProperty.homMk (pullback.fst s.hom t.hom) :
          AlgebraicSpaces.fiberProduct C S hS s t ⟶ R) ≫ qR)
      (hpw : ∀ T, Nonempty (Deformation.PointwiseGroupoid (s.hom.app T) (t.hom.app T)
        (fun p => (composableToPullback s.hom t.hom ≫ c.hom).app T p))),
      GroupoidInAlgebraicSpaces.mk U R qU qR s t hso hto c hco hpw =
        groupoidOfIsEquivalenceRelation j := by
  subst hs ht
  intro hso hto c hco hpw
  have hcomp : c = (groupoidOfIsEquivalenceRelation j).comp := by
    let G : GroupoidInAlgebraicSpaces C S hS B :=
      { objects := U
        arrows := R
        objectsToBase := qU
        arrowsToBase := qR
        source := ObjectProperty.homMk j.source.left
        target := ObjectProperty.homMk j.target.left
        source_over := hso
        target_over := hto
        comp := c
        comp_over := hco
        pointwiseGroupoid := hpw }
    apply ObjectProperty.hom_ext
    ext T p
    refine j.section_eq_of_endpoints
      ((isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).mp inferInstance).1 ?_ ?_
    · exact (source_comp_section G T p).trans
        (source_comp_section (groupoidOfIsEquivalenceRelation j) T p).symm
    · exact (target_comp_section G T p).trans
        (target_comp_section (groupoidOfIsEquivalenceRelation j) T p).symm
  subst hcomp
  rfl

/-- **Stacks 043Y.** An equivalence relation `j : R ⟶ U ×_B U` of algebraic spaces over an
algebraic space `B` extends to a groupoid in algebraic spaces over `B`, and in exactly one way:
the source and the target of the groupoid are the two components of `j`, and its composition
law is then forced, an arrow being determined by its source and its target. -/
@[stacks 043Y]
theorem existsUnique_groupoid_of_isEquivalenceRelation
    (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    [IsEquivalenceRelation j.target j.source] :
    ∃! G : GroupoidInAlgebraicSpaces C S hS B, ExtendsRelation j G := by
  refine ⟨groupoidOfIsEquivalenceRelation j,
    groupoidOfIsEquivalenceRelation_extendsRelation j, ?_⟩
  intro G hG
  obtain ⟨ho, ha, hob, hab, hs, ht⟩ := hG
  obtain ⟨objects, arrows, objectsToBase, arrowsToBase, source, target,
    source_over, target_over, comp, comp_over, pointwiseGroupoid⟩ := G
  cases ho
  cases ha
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hob hab hs ht
  subst hob hab
  exact mk_eq_groupoidOfIsEquivalenceRelation j hs ht source_over target_over comp comp_over
    pointwiseGroupoid

end AlgebraicGeometry.Space

end
