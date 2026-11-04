module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctor

/-!
# The points of the Hilbert functor with values in an algebraic space (Stacks 0D3W)

In Situation 0CZY a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` of a big fppf site
is given and `Hilb_{X/Y}` is read, by Stacks 0CZY, as a presheaf on the big fppf site of `S`
whose value at a scheme `V` of the site is the set of pairs `(h, Z)` consisting of a morphism
`h : V ⟶ Y` and a closed subspace `Z` of `X_V = X ×_{Y, h} V` which is of finite presentation,
flat and proper over `V`.  Stacks 0D3W extends the description of those pairs from the schemes of
the site to an arbitrary algebraic space `T`:

`Mor_{Sh((Sch/S)_fppf)}(T, Hilb_{X/Y}) = {(h, Z) : h : T ⟶ Y, Z ⊆ X_T closed with Z ⟶ T of`
`finite presentation, flat and proper}`

with `X_T = X ×_{Y, h} T`.  This file supplies the right-hand side over an arbitrary algebraic
space `T` and proves the identification *in both directions*, as a bijection.

## Main definitions

* `AlgebraicGeometry.Space.hilbertChartMap`: the transition morphism `X_{T'} ⟶ X_T` of base
  changes of `f` induced by a morphism `T' ⟶ T` over `Y`.
* `AlgebraicGeometry.Space.SpaceHilbertFamily`: **the right-hand side of the displayed
  identification of Stacks 0D3W**, a morphism `h : T ⟶ Y` bundled with such a closed subspace of
  `X_T`.
* `AlgebraicGeometry.Space.SpaceHilbertFamily.toMor`: the morphism of sheaves determined by such a
  pair — the inverse image of `Z` in every chart of `T`.
* `AlgebraicGeometry.Space.hilbertMorBase` and
  `AlgebraicGeometry.Space.hilbertMorSubfunctor`: the morphism `T ⟶ Y` and the closed subspace of
  `X_T` read off a morphism of sheaves into the Hilbert presheaf.
* `AlgebraicGeometry.Space.IsHilbertLocalOnBase`: the descent input, that the four conditions on a
  subfunctor of `X_T` may be tested in the charts of `T`.

## Main results

* `AlgebraicGeometry.Space.hilbertMorSubfunctor_preimage`: the subspace glued from a morphism of
  sheaves restricts, in every chart of `T`, to the subspace that morphism gives there.
* `AlgebraicGeometry.Space.subfunctor_ext_of_charts`: a subfunctor of `X_T` is determined by its
  inverse images in the charts of `T`.
* `AlgebraicGeometry.Space.morEquivSpaceHilbertFamily`: **Stacks 0D3W**, the displayed
  identification as a bijection, for an arbitrary algebraic space `T`, conditional on the descent
  input.
* `AlgebraicGeometry.Space.morEquivSpaceHilbertFamilyOfScheme`: **Stacks 0D3W for a scheme of the
  site**, unconditionally.

## Implementation notes

**Why the identification is a bijection and not an equality.**  The source writes `=` between a
set of morphisms of sheaves and a set of pairs.  Those are two different types here — a type of
natural transformations on one side, a structure with six fields on the other — so a
propositional equality between them is not even well typed.  It is therefore given as an `Equiv`,
that is as data, and the data is *constructed*: both maps are written down and no object is
chosen from an existence statement.  This is also the form the analogous Stacks 0D3V takes in
`StacksFrontier/AlgebraicGeometry/Quot/QuotFunctorPoints.lean`, which keeps the two tags comparable.

**What is proved for a general algebraic space, and what is carried.**  Everything except the
descent of the four conditions is proved here, for an arbitrary algebraic space `T`.  A closed
subspace of `X_T` is a *subfunctor*, that is a subset of the sections over every scheme of the
site, and the Hilbert functor restricts along a transition map by the inverse image
`CategoryTheory.Subfunctor.preimage`, whose functor laws hold on the nose.  So the pair-to-
transformation direction is the inverse image of `Z` in each chart, and the transformation-to-
pair direction glues: every section of `X_T` over `V` lies in the chart `V ⟶ T` given by its own
second projection, which is `AlgebraicGeometry.Space.hilbertChartMap_app_diagSection`, and the
subspace of that chart decides its membership.  What this gluing does *not* give is that the
glued subfunctor is a closed subspace, of finite presentation, flat and proper over `T`: those
four conditions are only known in the charts, and passing from the charts to `T` is descent.
That step is carried, as the named hypothesis `hloc : IsHilbertLocalOnBase f T` of
`AlgebraicGeometry.Space.morEquivSpaceHilbertFamily` — in the source it is the choice of a scheme
`U` with a surjective étale morphism `U ⟶ T` followed by descent along it, for which this
development has the faithfulness clause of quasi-coherent descent and none of the effectivity
(see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Quot/QuotFunctorPoints.lean`).  The hypothesis is not a
restriction on `T`: it is discharged, by
`AlgebraicGeometry.Space.isHilbertLocalOnBase_yoneda`, whenever `T` is a scheme of the site,
which gives the unconditional
`AlgebraicGeometry.Space.morEquivSpaceHilbertFamilyOfScheme`.

**Hilb as a Quot functor is not available here.**  The source deduces Stacks 0D3W from the
analogous Stacks 0D3V for the Quot functor through the identification
`Hilb_{X/B} = Quot_{𝒪_X/X/B}` of Stacks 0D00.  That identification is not in this development:
`StacksFrontier/AlgebraicGeometry/Quot/HilbertFamilyStructureSheafDictionary.lean` proves two
entries of the dictionary underlying it and
`StacksFrontier/AlgebraicGeometry/Quot/HilbertFunctorAlgebraicSpace.lean` carries the identification
itself as a hypothesis.  So the description is proved here directly for the Hilbert functor,
which is in any case the shorter route: the Quot side has to conjugate a quotient by a comparison
of inverse images of modules, whereas inverse images of subfunctors are functorial on the nose.

**The universe of the identification.**  An algebraic space is a presheaf of `Type u` on the big
fppf site, whereas `Hilb_{X/Y}` takes values in `Type (u + 1)`, its sections being recorded by
subfunctors of a presheaf.  As for Stacks 0D3V the left-hand side is therefore read with the
sheaf of the algebraic space lifted; the lift is an isomorphism onto its image at every object of
the site, so no morphism is added or lost.

## References

* [Stacks Project, Tag 0D3W](https://stacks.math.columbia.edu/tag/0D3W)
* [Stacks Project, Tag 0CZY](https://stacks.math.columbia.edu/tag/0CZY)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 0D3V](https://stacks.math.columbia.edu/tag/0D3V)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 05VY](https://stacks.math.columbia.edu/tag/05VY)
* [Stacks Project, Tag 060V](https://stacks.math.columbia.edu/tag/060V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The Yoneda bijection, read at the identity: the section of a presheaf corresponding to a
morphism out of a representable is recovered by evaluating that morphism at the identity. -/
theorem yonedaEquiv_symm_app_id {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W : (BigFppfOver B S hS)ᵒᵖ} (t : F.obj W) :
    (yonedaEquiv.symm t).app W (𝟙 W.unop) = t :=
  Equiv.apply_symm_apply yonedaEquiv t

section PullbackSections

variable {P Q R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : P ⟶ R) (b : Q ⟶ R)

/-- A section of a fibre product of presheaves is determined by its two projections: the two
projections are jointly monic, so the morphisms out of a representable they correspond to agree. -/
theorem presheafPullbackSection_ext {W : (BigFppfOver B S hS)ᵒᵖ} {p q : (pullback a b).obj W}
    (hfst : (pullback.fst a b).app W p = (pullback.fst a b).app W q)
    (hsnd : (pullback.snd a b).app W p = (pullback.snd a b).app W q) : p = q := by
  apply (yonedaEquiv (X := W.unop) (F := pullback a b)).symm.injective
  apply pullback.hom_ext <;> apply yonedaEquiv.injective <;>
    rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exacts [hfst, hsnd]

/-- The defining condition of a fibre product of presheaves, read on a section. -/
theorem presheafPullback_condition_app {W : (BigFppfOver B S hS)ᵒᵖ} (p : (pullback a b).obj W) :
    a.app W ((pullback.fst a b).app W p) = b.app W ((pullback.snd a b).app W p) := by
  simpa using types_congr_hom (congr_app (pullback.condition (f := a) (g := b)) W) p

/-- The section of a fibre product of presheaves determined by two compatible sections of the
two factors. -/
def presheafPullbackSection {W : (BigFppfOver B S hS)ᵒᵖ} (x : P.obj W) (y : Q.obj W)
    (w : a.app W x = b.app W y) : (pullback a b).obj W :=
  yonedaEquiv (pullback.lift (yonedaEquiv.symm x) (yonedaEquiv.symm y)
    (by
      apply yonedaEquiv.injective
      rwa [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]))

/-- The first projection of `presheafPullbackSection a b x y w` is `x`. -/
@[simp]
theorem presheafPullbackSection_fst {W : (BigFppfOver B S hS)ᵒᵖ} (x : P.obj W) (y : Q.obj W)
    (w : a.app W x = b.app W y) :
    (pullback.fst a b).app W (presheafPullbackSection a b x y w) = x := by
  rw [presheafPullbackSection, ← yonedaEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]

/-- The second projection of `presheafPullbackSection a b x y w` is `y`. -/
@[simp]
theorem presheafPullbackSection_snd {W : (BigFppfOver B S hS)ᵒᵖ} (x : P.obj W) (y : Q.obj W)
    (w : a.app W x = b.app W y) :
    (pullback.snd a b).app W (presheafPullbackSection a b x y w) = y := by
  rw [presheafPullbackSection, ← yonedaEquiv_comp, pullback.lift_snd, Equiv.apply_symm_apply]

end PullbackSections

section Chart

variable {X Y : AlgebraicSpaces B S hS}

/-- The morphism `X_{T'} ⟶ X_T` of base changes of `f : X ⟶ Y` induced by a morphism `k : T' ⟶ T`
of presheaves over `Y`, where the structure morphism `c' : T' ⟶ Y` is presented as `k ≫ c`.

Carrying the identification `hk : k ≫ c = c'` as a hypothesis rather than taking `c'` to be
`k ≫ c` on the nose is what lets the construction be applied when the two are only
propositionally equal, which is the case for the structure morphisms read off a morphism of
sheaves into the Hilbert presheaf. -/
def hilbertChartMap (f : X ⟶ Y) {G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {c : G ⟶ Y.obj}
    {c' : G' ⟶ Y.obj} (k : G' ⟶ G) (hk : k ≫ c = c') :
    pullback f.hom c' ⟶ pullback f.hom c :=
  pullback.lift (pullback.fst f.hom c') (pullback.snd f.hom c' ≫ k)
    (by rw [Category.assoc, hk]; exact pullback.condition)

/-- `hilbertChartMap f k hk` commutes with the first projections to `X`. -/
@[reassoc (attr := simp)]
theorem hilbertChartMap_fst (f : X ⟶ Y) {G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {c : G ⟶ Y.obj} {c' : G' ⟶ Y.obj} (k : G' ⟶ G) (hk : k ≫ c = c') :
    hilbertChartMap f k hk ≫ pullback.fst f.hom c = pullback.fst f.hom c' :=
  pullback.lift_fst _ _ _

/-- The second projection of `hilbertChartMap f k hk` is the second projection followed by `k`. -/
@[reassoc (attr := simp)]
theorem hilbertChartMap_snd (f : X ⟶ Y) {G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {c : G ⟶ Y.obj} {c' : G' ⟶ Y.obj} (k : G' ⟶ G) (hk : k ≫ c = c') :
    hilbertChartMap f k hk ≫ pullback.snd f.hom c = pullback.snd f.hom c' ≫ k :=
  pullback.lift_snd _ _ _

/-- On sections, `hilbertChartMap f k hk` preserves the first projection to `X`. -/
@[simp]
theorem hilbertChartMap_app_fst (f : X ⟶ Y) {G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {c : G ⟶ Y.obj} {c' : G' ⟶ Y.obj} (k : G' ⟶ G) (hk : k ≫ c = c')
    {W : (BigFppfOver B S hS)ᵒᵖ} (q : (pullback f.hom c').obj W) :
    (pullback.fst f.hom c).app W ((hilbertChartMap f k hk).app W q) =
      (pullback.fst f.hom c').app W q :=
  types_congr_hom (congr_app (hilbertChartMap_fst f k hk) W) q

/-- On sections, the second projection of the image under `hilbertChartMap f k hk` is the image
under `k` of the second projection. -/
@[simp]
theorem hilbertChartMap_app_snd (f : X ⟶ Y) {G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {c : G ⟶ Y.obj} {c' : G' ⟶ Y.obj} (k : G' ⟶ G) (hk : k ≫ c = c')
    {W : (BigFppfOver B S hS)ᵒᵖ} (q : (pullback f.hom c').obj W) :
    (pullback.snd f.hom c).app W ((hilbertChartMap f k hk).app W q) =
      k.app W ((pullback.snd f.hom c').app W q) :=
  types_congr_hom (congr_app (hilbertChartMap_snd f k hk) W) q

/-- The square comparing two base changes of `f` is cartesian: `X_{T'}` is the base change of
`X_T` along `k`. -/
theorem isPullback_hilbertChartMap (f : X ⟶ Y) {G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {c : G ⟶ Y.obj} {c' : G' ⟶ Y.obj} (k : G' ⟶ G) (hk : k ≫ c = c') :
    IsPullback (hilbertChartMap f k hk) (pullback.snd f.hom c') (pullback.snd f.hom c) k := by
  have hleft : IsPullback (pullback.fst f.hom c') (pullback.snd f.hom c') f.hom (k ≫ c) := by
    rw [hk]
    exact IsPullback.of_hasPullback _ _
  have hright := IsPullback.of_hasPullback f.hom c
  convert IsPullback.of_right' hleft hright using 1
  apply pullback.hom_ext
  · simp only [hilbertChartMap, pullback.lift_fst, hright.lift_fst]
  · simp only [hilbertChartMap, pullback.lift_snd, hright.lift_snd]

/-- The morphisms of base changes compose: this is the functoriality of `X_{(-)}` in the base. -/
theorem hilbertChartMap_comp (f : X ⟶ Y) {G G' G'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {c : G ⟶ Y.obj} {c' : G' ⟶ Y.obj} {c'' : G'' ⟶ Y.obj} (k : G' ⟶ G) (hk : k ≫ c = c')
    (k' : G'' ⟶ G') (hk' : k' ≫ c' = c'') :
    hilbertChartMap f k' hk' ≫ hilbertChartMap f k hk =
      hilbertChartMap f (k' ≫ k) (by rw [Category.assoc, hk, hk']) := by
  apply pullback.hom_ext <;> simp

/-- The transition map of base changes used by the Hilbert functor of Stacks 0CZY is the
transition map along the induced morphism of representables. -/
theorem schemeBaseChangeMap_restrict (f : X ⟶ Y) {V V' : BigFppfOver B S hS} (g : V' ⟶ V)
    (c : yoneda.obj V ⟶ Y.obj) :
    schemeBaseChangeMap f (HilbertFamilyOver.restrict g c) =
      hilbertChartMap f (yoneda.map g) (rfl : yoneda.map g ≫ c = yoneda.map g ≫ c) :=
  rfl

/-- The two projections of a section of `X_T` are compatible over `Y` after the second one is
read as a morphism out of a representable and evaluated at the identity. -/
theorem fst_app_eq_comp_app_id (f : X ⟶ Y) {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : G ⟶ Y.obj)
    {W : (BigFppfOver B S hS)ᵒᵖ} (p : (pullback f.hom c).obj W) :
    f.hom.app W ((pullback.fst f.hom c).app W p) =
      (yonedaEquiv.symm ((pullback.snd f.hom c).app W p) ≫ c).app W (𝟙 W.unop) := by
  rw [presheafPullback_condition_app f.hom c p]
  exact congrArg (fun y ↦ c.app W y) (yonedaEquiv_symm_app_id _).symm

/-- **Every section of `X_T` comes from the chart it determines.** A section `p` of `X_T` over `V`
is the image, under the transition map of the chart `V ⟶ T` given by its second projection, of
the section of `X_V` with the same first projection and second projection the identity. -/
theorem hilbertChartMap_app_diagSection (f : X ⟶ Y)
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : G ⟶ Y.obj)
    {W : (BigFppfOver B S hS)ᵒᵖ} (p : (pullback f.hom c).obj W) :
    (hilbertChartMap f (yonedaEquiv.symm ((pullback.snd f.hom c).app W p))
          (rfl : yonedaEquiv.symm ((pullback.snd f.hom c).app W p) ≫ c = _)).app W
        (presheafPullbackSection f.hom _ ((pullback.fst f.hom c).app W p) (𝟙 W.unop)
          (fst_app_eq_comp_app_id f c p)) = p := by
  refine presheafPullbackSection_ext f.hom c ?_ ?_
  · rw [hilbertChartMap_app_fst, presheafPullbackSection_fst]
  · rw [hilbertChartMap_app_snd, presheafPullbackSection_snd]
    exact yonedaEquiv_symm_app_id _

/-- **A subfunctor of `X_T` is determined by its inverse images in the charts of `T`.** Two
subfunctors of `X_T` with the same inverse image along the transition map of every morphism from
a scheme of the site to `T` are equal. -/
theorem subfunctor_ext_of_charts (f : X ⟶ Y) {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (c : G ⟶ Y.obj) {Z₁ Z₂ : Subfunctor (pullback f.hom c)}
    (h : ∀ (V : BigFppfOver B S hS) (k : yoneda.obj V ⟶ G),
      Z₁.preimage (hilbertChartMap f k (rfl : k ≫ c = k ≫ c)) =
        Z₂.preimage (hilbertChartMap f k (rfl : k ≫ c = k ≫ c))) :
    Z₁ = Z₂ := by
  refine Subfunctor.ext (funext fun W ↦ Set.ext fun p ↦ ?_)
  have hp := hilbertChartMap_app_diagSection f c p
  have key (Z : Subfunctor (pullback f.hom c)) : p ∈ Z.obj W ↔
      presheafPullbackSection f.hom _ ((pullback.fst f.hom c).app W p) (𝟙 W.unop)
        (fst_app_eq_comp_app_id f c p) ∈
        (Z.preimage (hilbertChartMap f
          (yonedaEquiv.symm ((pullback.snd f.hom c).app W p)) rfl)).obj W := by
    rw [Subfunctor.preimage_obj, Set.mem_preimage, hp]
  rw [key Z₁, key Z₂, h W.unop (yonedaEquiv.symm ((pullback.snd f.hom c).app W p))]

/-- **The right-hand side of the displayed identification of Stacks 0D3W.** A pair `(h, Z)`
consisting of a morphism `h : T ⟶ Y` out of an algebraic space and a closed subspace `Z` of the
base change `X_T = X ×_{Y, h} T` which is of finite presentation, flat and proper over `T`.

For `T` a scheme of the site over `Y` this is `AlgebraicGeometry.Space.HilbertFamilyOver`, the
families classified by the Hilbert functor of Stacks 0CZY; the fibre product is the same
construction at a different second argument. -/
structure SpaceHilbertFamily (f : X ⟶ Y) (T : AlgebraicSpaces B S hS) where
  /-- The morphism `T ⟶ Y` along which `X` is based changed. -/
  hom : T ⟶ Y
  /-- The closed subspace of `X_T`, recorded as a subfunctor. -/
  Z : Subfunctor (pullback f.hom hom.hom)
  /-- It is a closed subspace (Stacks 02YU). -/
  closed : IsClosedSubspace B S hS Z
  /-- It is of finite presentation over `T` (Stacks 03XP). -/
  finitePresentation : IsFinitePresentation B S hS (Z.ι ≫ pullback.snd f.hom hom.hom)
  /-- It is flat over `T` (Stacks 03ML). -/
  flat : IsFlat B S hS (Z.ι ≫ pullback.snd f.hom hom.hom)
  /-- It is proper over `T` (Stacks 03ZM). -/
  proper : IsProper B S hS (Z.ι ≫ pullback.snd f.hom hom.hom)

/-- The square exhibiting the inverse image of a closed subspace of `X_T` in `X_{T'}` as its base
change along `T' ⟶ T`, as a square of algebraic spaces over `T'` and `T`. This is what carries
finite presentation, flatness and properness over the base to the inverse image. -/
theorem isPullback_preimage_chart (f : X ⟶ Y) {G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {c : G ⟶ Y.obj} {c' : G' ⟶ Y.obj} (hG : IsAlgebraicSpace B S hS G)
    (hG' : IsAlgebraicSpace B S hS G') (k : G' ⟶ G) (hk : k ≫ c = c')
    (Z : Subfunctor (pullback f.hom c)) (hZ : IsClosedSubspace B S hS Z)
    (hXc : IsAlgebraicSpace B S hS (pullback f.hom c))
    (hXc' : IsAlgebraicSpace B S hS (pullback f.hom c'))
    (hpre : IsClosedSubspace B S hS (Z.preimage (hilbertChartMap f k hk))) :
    IsPullback
      (ObjectProperty.homMk (Z.fromPreimage (hilbertChartMap f k hk)) :
        (⟨(Z.preimage (hilbertChartMap f k hk)).toFunctor, hpre.1⟩ :
          AlgebraicSpaces B S hS) ⟶ ⟨Z.toFunctor, hZ.1⟩)
      ((ObjectProperty.homMk (Z.preimage (hilbertChartMap f k hk)).ι :
        (⟨(Z.preimage (hilbertChartMap f k hk)).toFunctor, hpre.1⟩ :
          AlgebraicSpaces B S hS) ⟶ ⟨pullback f.hom c', hXc'⟩) ≫
        ObjectProperty.homMk (pullback.snd f.hom c'))
      ((ObjectProperty.homMk Z.ι :
        (⟨Z.toFunctor, hZ.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨pullback f.hom c, hXc⟩) ≫
        ObjectProperty.homMk (pullback.snd f.hom c))
      (ObjectProperty.homMk k :
        (⟨G', hG'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩) := by
  have hinner : IsPullback
      (ObjectProperty.homMk (Z.fromPreimage (hilbertChartMap f k hk)) :
        (⟨(Z.preimage (hilbertChartMap f k hk)).toFunctor, hpre.1⟩ :
          AlgebraicSpaces B S hS) ⟶ ⟨Z.toFunctor, hZ.1⟩)
      (ObjectProperty.homMk (Z.preimage (hilbertChartMap f k hk)).ι :
        (⟨(Z.preimage (hilbertChartMap f k hk)).toFunctor, hpre.1⟩ :
          AlgebraicSpaces B S hS) ⟶ ⟨pullback f.hom c', hXc'⟩)
      (ObjectProperty.homMk Z.ι :
        (⟨Z.toFunctor, hZ.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨pullback f.hom c, hXc⟩)
      (ObjectProperty.homMk (hilbertChartMap f k hk) :
        (⟨pullback f.hom c', hXc'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨pullback f.hom c, hXc⟩) :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
      (Subfunctor.isPullback_preimage (hilbertChartMap f k hk) Z)
  have houter : IsPullback
      (ObjectProperty.homMk (hilbertChartMap f k hk) :
        (⟨pullback f.hom c', hXc'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨pullback f.hom c, hXc⟩)
      (ObjectProperty.homMk (pullback.snd f.hom c') :
        (⟨pullback f.hom c', hXc'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G', hG'⟩)
      (ObjectProperty.homMk (pullback.snd f.hom c) :
        (⟨pullback f.hom c, hXc⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
      (ObjectProperty.homMk k : (⟨G', hG'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩) :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
      (isPullback_hilbertChartMap f k hk)
  exact hinner.paste_vert houter

/-- The transition map `X_V ⟶ X_T` for a morphism `V ⟶ T` from a scheme of the site. -/
abbrev SpaceHilbertFamily.chartMap {f : X ⟶ Y} {T : AlgebraicSpaces B S hS}
    (x : SpaceHilbertFamily f T) {V : BigFppfOver B S hS} (k : yoneda.obj V ⟶ T.obj) :
    pullback f.hom (k ≫ x.hom.hom) ⟶ pullback f.hom x.hom.hom :=
  hilbertChartMap f k rfl

/-- **The restriction of a pair of Stacks 0D3W to a chart.** For a morphism `k : V ⟶ T` from a
scheme of the big fppf site, the inverse image of `Z` in `X_V` is a family classified by the
Hilbert functor of Stacks 0CZY over `V`: it is a closed subspace by Stacks 083Q, and it is of
finite presentation, flat and proper over `V` because all three properties are stable under base
change (Stacks 03XR, 03MO, 04WP) and the square of the previous lemma is cartesian. -/
def SpaceHilbertFamily.chartFamily {f : X ⟶ Y} {T : AlgebraicSpaces B S hS}
    (x : SpaceHilbertFamily f T) {V : BigFppfOver B S hS} (k : yoneda.obj V ⟶ T.obj) :
    HilbertFamily f (CostructuredArrow.mk (k ≫ x.hom.hom)) := by
  have hXT : IsAlgebraicSpace B S hS (pullback f.hom x.hom.hom) :=
    isAlgebraicSpace_pullback B S hS f.hom x.hom.hom X.2 T.2 Y.2
  have hXV : IsAlgebraicSpace B S hS (pullback f.hom (k ≫ x.hom.hom)) :=
    isAlgebraicSpace_pullback B S hS f.hom (k ≫ x.hom.hom) X.2
      (isAlgebraicSpace_yoneda B S hS V) Y.2
  have hpre : IsClosedSubspace B S hS (x.Z.preimage (x.chartMap k)) :=
    isClosedSubspace_preimage B S hS (x.chartMap k) x.Z hXT hXV x.closed
  have hpb := isPullback_preimage_chart f T.2 (isAlgebraicSpace_yoneda B S hS V) k rfl x.Z
    x.closed hXT hXV hpre
  have := Space.isFinitePresentation_isStableUnderBaseChange B S hS
  have := Space.isFlat_isStableUnderBaseChange B S hS
  have := Space.isProper_isStableUnderBaseChange B S hS
  refine ⟨x.Z.preimage (x.chartMap k), hpre, ?_, ?_, ?_⟩
  · simpa using MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {F G : AlgebraicSpaces B S hS} (q : F ⟶ G) => IsFinitePresentation B S hS q.hom)
      hpb (by simpa using x.finitePresentation)
  · simpa using MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {F G : AlgebraicSpaces B S hS} (q : F ⟶ G) => IsFlat B S hS q.hom)
      hpb (by simpa using x.flat)
  · simpa using MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {F G : AlgebraicSpaces B S hS} (q : F ⟶ G) => IsProper B S hS q.hom)
      hpb (by simpa using x.proper)

/-- The closed subspace of `x.chartFamily k` is the inverse image of `x.Z` under `x.chartMap k`. -/
@[simp]
theorem SpaceHilbertFamily.chartFamily_Z {f : X ⟶ Y} {T : AlgebraicSpaces B S hS}
    (x : SpaceHilbertFamily f T) {V : BigFppfOver B S hS} (k : yoneda.obj V ⟶ T.obj) :
    (x.chartFamily k).Z = x.Z.preimage (x.chartMap k) := rfl

/-- **The morphism of sheaves determined by a pair of Stacks 0D3W.** The transformation whose
value at a section `t` of `T` over a scheme `V` of the site is the pair consisting of the induced
morphism `V ⟶ Y` and the inverse image of `Z` in `X_V`.

Naturality holds because the Hilbert presheaf restricts by taking inverse images of subfunctors,
which is functorial on the nose, and because the two chart maps compose. -/
def SpaceHilbertFamily.toMor {f : X ⟶ Y} {T : AlgebraicSpaces B S hS}
    (x : SpaceHilbertFamily f T) : T.obj ⋙ uliftFunctor.{u + 1, u} ⟶ hilbertPresheaf f where
  app W := TypeCat.ofHom fun t ↦
    (⟨yonedaEquiv.symm t.down ≫ x.hom.hom, x.chartFamily (yonedaEquiv.symm t.down)⟩ :
      HilbertFamilyOver f W.unop)
  naturality := by
    intro W W' g
    ext t
    obtain ⟨t⟩ := t
    have hk : yonedaEquiv.symm (T.obj.map g t) = yoneda.map g.unop ≫ yonedaEquiv.symm t :=
      yonedaEquiv_symm_map g t
    change (⟨yonedaEquiv.symm (T.obj.map g t) ≫ x.hom.hom,
        x.chartFamily (yonedaEquiv.symm (T.obj.map g t))⟩ : HilbertFamilyOver f W'.unop) =
      HilbertFamilyOver.baseChange g.unop
        ⟨yonedaEquiv.symm t ≫ x.hom.hom, x.chartFamily (yonedaEquiv.symm t)⟩
    refine HilbertFamilyOver.ext ?_ ?_
    · rw [hk]
      exact Category.assoc _ _ _
    · rw [hk]
      refine heq_of_eq ?_
      change x.Z.preimage (hilbertChartMap f (yoneda.map g.unop ≫ yonedaEquiv.symm t) rfl)
        = (x.Z.preimage (hilbertChartMap f (yonedaEquiv.symm t) rfl)).preimage
            (schemeBaseChangeMap f
              (HilbertFamilyOver.restrict g.unop (yonedaEquiv.symm t ≫ x.hom.hom)))
      rw [schemeBaseChangeMap_restrict, ← Subfunctor.preimage_comp, hilbertChartMap_comp]

section Mor

variable {f : X ⟶ Y} {T : AlgebraicSpaces B S hS}
  (α : T.obj ⋙ uliftFunctor.{u + 1, u} ⟶ hilbertPresheaf f)

/-- **The morphism `T ⟶ Y` underlying a morphism of sheaves into the Hilbert presheaf.** Its
value at a section `t` of `T` is the morphism to `Y` that the family at `t` lies over, read as a
section of `Y` by the Yoneda bijection; this is the composition with the canonical morphism
`AlgebraicGeometry.Space.hilbertPresheafToBase` of Stacks 0CZY, read one universe down. -/
def hilbertMorBase : T ⟶ Y :=
  ObjectProperty.homMk
    { app := fun W ↦ TypeCat.ofHom fun t ↦ yonedaEquiv ((α.app W (ULift.up t)).toBase)
      naturality := by
        intro W W' g
        ext t
        have hnat : α.app W' (ULift.up (T.obj.map g t)) =
            HilbertFamilyOver.baseChange g.unop (α.app W (ULift.up t)) :=
          types_congr_hom (α.naturality g) (ULift.up t)
        change yonedaEquiv ((α.app W' (ULift.up (T.obj.map g t))).toBase) =
          Y.obj.map g (yonedaEquiv ((α.app W (ULift.up t)).toBase))
        rw [hnat]
        exact (yonedaEquiv_naturality _ g.unop).symm }

/-- The value of `hilbertMorBase α` at a section `t` is the morphism to `Y` underlying the family
`α.app W (ULift.up t)`, read as a section of `Y`. -/
@[simp]
theorem hilbertMorBase_hom_app (W : (BigFppfOver B S hS)ᵒᵖ) (t : T.obj.obj W) :
    (hilbertMorBase α).hom.app W t = yonedaEquiv ((α.app W (ULift.up t)).toBase) := rfl

/-- The family at a section `t` of `T` lies over the morphism `V ⟶ Y` obtained from `t` and the
underlying morphism `T ⟶ Y`. -/
theorem hilbertMor_toBase_eq (W : (BigFppfOver B S hS)ᵒᵖ) (t : T.obj.obj W) :
    yonedaEquiv.symm t ≫ (hilbertMorBase α).hom = (α.app W (ULift.up t)).toBase := by
  rw [yonedaEquiv_symm_naturality_right, hilbertMorBase_hom_app, Equiv.symm_apply_apply]

/-- Naturality of a morphism of sheaves into the Hilbert presheaf, read on sections: the family
at a restricted section is the base change of the family. -/
theorem hilbertMor_app_map {V V' : BigFppfOver B S hS} (w : V' ⟶ V) (t : T.obj.obj (op V)) :
    α.app (op V') (ULift.up (T.obj.map w.op t)) =
      HilbertFamilyOver.baseChange w (α.app (op V) (ULift.up t)) :=
  types_congr_hom (α.naturality w.op) (ULift.up t)

/-- The morphisms to `Y` that the families of a morphism of sheaves lie over are compatible with
restriction. -/
theorem hilbertMor_toBase_map {V : BigFppfOver B S hS} (t : T.obj.obj (op V))
    {W : (BigFppfOver B S hS)ᵒᵖ} (s : W.unop ⟶ V) :
    yoneda.map s ≫ (α.app (op V) (ULift.up t)).toBase =
      (α.app W (ULift.up (T.obj.map s.op t))).toBase :=
  (congrArg HilbertFamilyOver.toBase (hilbertMor_app_map α s t)).symm

/-- The inverse image of a subfunctor of `X_T` along a transition map does not depend on which
identification of the structure morphism of the chart is used. -/
theorem preimage_hilbertChartMap_heq {G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {c : G ⟶ Y.obj} {c₁ c₂ : G' ⟶ Y.obj} (k : G' ⟶ G) (hk₁ : k ≫ c = c₁) (hk₂ : k ≫ c = c₂)
    (Z : Subfunctor (pullback f.hom c)) :
    Z.preimage (hilbertChartMap f k hk₁) ≍ Z.preimage (hilbertChartMap f k hk₂) := by
  cases hk₁.symm.trans hk₂
  rfl

/-- **The closed subspaces of a morphism of sheaves into the Hilbert presheaf are compatible with
restriction:** the subspace at a restricted section is the inverse image of the subspace. -/
theorem hilbertMor_family_Z_map {V : BigFppfOver B S hS} (t : T.obj.obj (op V))
    {W : (BigFppfOver B S hS)ᵒᵖ} (s : W.unop ⟶ V) :
    (α.app W (ULift.up (T.obj.map s.op t))).family.Z =
      (α.app (op V) (ULift.up t)).family.Z.preimage
        (hilbertChartMap f (yoneda.map s) (hilbertMor_toBase_map α t s)) :=
  eq_of_heq ((HilbertFamilyOver.family_Z_heq (hilbertMor_app_map α s t)).trans
    (preimage_hilbertChartMap_heq (yoneda.map s) rfl (hilbertMor_toBase_map α t s) _))

/-- The two projections of a section of `X_T`, for `T ⟶ Y` the morphism underlying a morphism of
sheaves into the Hilbert presheaf, are compatible over `Y` with the family at its second
projection. -/
theorem fst_app_eq_toBase_app_id {W : (BigFppfOver B S hS)ᵒᵖ}
    (p : (pullback f.hom (hilbertMorBase α).hom).obj W) :
    f.hom.app W ((pullback.fst f.hom (hilbertMorBase α).hom).app W p) =
      (α.app W (ULift.up ((pullback.snd f.hom (hilbertMorBase α).hom).app W p))).toBase.app W
        (𝟙 W.unop) := by
  rw [← hilbertMor_toBase_eq α W]
  exact fst_app_eq_comp_app_id f (hilbertMorBase α).hom p

/-- **The membership condition defining the glued closed subspace.** A section `x` of `X` over
`W` lying over a section `u` of `T` belongs to the glued subspace when the corresponding section
of `X_W`, the one whose second projection is the identity, lies in the closed subspace of the
family of the morphism of sheaves at `u`. -/
def hilbertMorMem (W : (BigFppfOver B S hS)ᵒᵖ) (u : T.obj.obj W) (x : X.obj.obj W)
    (hx : f.hom.app W x = (α.app W (ULift.up u)).toBase.app W (𝟙 W.unop)) : Prop :=
  presheafPullbackSection f.hom (α.app W (ULift.up u)).toBase x (𝟙 W.unop) hx ∈
    (α.app W (ULift.up u)).family.Z.obj W

/-- The membership condition depends only on the two sections, not on the compatibility proof. -/
theorem hilbertMorMem_congr {W : (BigFppfOver B S hS)ᵒᵖ} {u u' : T.obj.obj W} {x x' : X.obj.obj W}
    (hu : u = u') (hx : x = x')
    (h : f.hom.app W x = (α.app W (ULift.up u)).toBase.app W (𝟙 W.unop))
    (h' : f.hom.app W x' = (α.app W (ULift.up u')).toBase.app W (𝟙 W.unop)) :
    hilbertMorMem α W u x h ↔ hilbertMorMem α W u' x' h' := by
  subst hu hx
  rfl

/-- **The membership condition read in a chart.** For a section `t` of `T` over `V` and a morphism
`s : W ⟶ V`, the membership condition at the restricted section is membership in the closed
subspace of the family at `t`, tested on any section of `X_V` over `W` with the given
projections. This is the compatibility of the families with restriction, read on sections. -/
theorem hilbertMorMem_iff {V : BigFppfOver B S hS} (t : T.obj.obj (op V))
    {W : (BigFppfOver B S hS)ᵒᵖ} (s : W.unop ⟶ V) (x : X.obj.obj W)
    (h : f.hom.app W x = (α.app W (ULift.up (T.obj.map s.op t))).toBase.app W (𝟙 W.unop))
    (q : (pullback f.hom (α.app (op V) (ULift.up t)).toBase).obj W)
    (hq₁ : (pullback.fst f.hom (α.app (op V) (ULift.up t)).toBase).app W q = x)
    (hq₂ : (pullback.snd f.hom (α.app (op V) (ULift.up t)).toBase).app W q = s) :
    hilbertMorMem α W (T.obj.map s.op t) x h ↔ q ∈ (α.app (op V) (ULift.up t)).family.Z.obj W := by
  have hpt : (hilbertChartMap f (yoneda.map s) (hilbertMor_toBase_map α t s)).app W
      (presheafPullbackSection f.hom (α.app W (ULift.up (T.obj.map s.op t))).toBase x
        (𝟙 W.unop) h) = q := by
    refine presheafPullbackSection_ext f.hom _ ?_ ?_
    · rw [hilbertChartMap_app_fst, presheafPullbackSection_fst, hq₁]
    · rw [hilbertChartMap_app_snd, presheafPullbackSection_snd, hq₂]
      simp
  show presheafPullbackSection f.hom (α.app W (ULift.up (T.obj.map s.op t))).toBase x
      (𝟙 W.unop) h ∈ (α.app W (ULift.up (T.obj.map s.op t))).family.Z.obj W ↔ _
  rw [hilbertMor_family_Z_map α t s]
  simp only [Subfunctor.preimage_obj, Set.mem_preimage, hpt]

/-- **The closed subspace of `X_T` glued from a morphism of sheaves into the Hilbert presheaf.**
A section of `X_T` lies in it when the membership condition holds for its two projections; the
stability under restriction is the compatibility of the families with restriction. -/
def hilbertMorSubfunctor : Subfunctor (pullback f.hom (hilbertMorBase α).hom) where
  obj W := {p | hilbertMorMem α W ((pullback.snd f.hom (hilbertMorBase α).hom).app W p)
    ((pullback.fst f.hom (hilbertMorBase α).hom).app W p) (fst_app_eq_toBase_app_id α p)}
  map := by
    intro W W' i p hp
    have hu : (pullback.snd f.hom (hilbertMorBase α).hom).app W'
        ((pullback f.hom (hilbertMorBase α).hom).map i p) =
          T.obj.map i ((pullback.snd f.hom (hilbertMorBase α).hom).app W p) :=
      NatTrans.naturality_apply (pullback.snd f.hom (hilbertMorBase α).hom) i p
    have hx : (pullback.fst f.hom (hilbertMorBase α).hom).app W'
        ((pullback f.hom (hilbertMorBase α).hom).map i p) =
          X.obj.map i ((pullback.fst f.hom (hilbertMorBase α).hom).app W p) :=
      NatTrans.naturality_apply (pullback.fst f.hom (hilbertMorBase α).hom) i p
    refine (hilbertMorMem_congr α hu hx _ ?_).2 ?_
    · rw [← hu, ← hx]
      exact fst_app_eq_toBase_app_id α _
    · set u := (pullback.snd f.hom (hilbertMorBase α).hom).app W p
      refine (hilbertMorMem_iff α u i.unop _ _
        ((pullback f.hom (α.app W (ULift.up u)).toBase).map i
          (presheafPullbackSection f.hom _ _ (𝟙 W.unop)
            (fst_app_eq_toBase_app_id α p))) ?_ ?_).2 ?_
      · rw [NatTrans.naturality_apply (pullback.fst f.hom _) i, presheafPullbackSection_fst]
      · rw [NatTrans.naturality_apply (pullback.snd f.hom _) i, presheafPullbackSection_snd]
        simp
      · exact (α.app W (ULift.up u)).family.Z.map i hp

/-- **The glued subspace restricts to the given subspaces in every chart.** Its inverse image in
`X_V` along the chart determined by a section `t` of `T` over `V` is the closed subspace of the
family at `t`. This is the whole content of the gluing; both directions of the displayed
identification of Stacks 0D3W are read off it. -/
theorem hilbertMorSubfunctor_preimage {V : BigFppfOver B S hS} (t : T.obj.obj (op V)) :
    (hilbertMorSubfunctor α).preimage
        (hilbertChartMap f (yonedaEquiv.symm t) (hilbertMor_toBase_eq α (op V) t)) =
      (α.app (op V) (ULift.up t)).family.Z := by
  refine Subfunctor.ext (funext fun W ↦ Set.ext fun q ↦ ?_)
  simp only [Subfunctor.preimage_obj, Set.mem_preimage]
  have hu : (pullback.snd f.hom (hilbertMorBase α).hom).app W
      ((hilbertChartMap f (yonedaEquiv.symm t) (hilbertMor_toBase_eq α (op V) t)).app W q) =
      T.obj.map ((pullback.snd f.hom (α.app (op V) (ULift.up t)).toBase).app W q).op t := by
    rw [hilbertChartMap_app_snd]
    rfl
  have hx : (pullback.fst f.hom (hilbertMorBase α).hom).app W
      ((hilbertChartMap f (yonedaEquiv.symm t) (hilbertMor_toBase_eq α (op V) t)).app W q) =
      (pullback.fst f.hom (α.app (op V) (ULift.up t)).toBase).app W q :=
    hilbertChartMap_app_fst f _ _ q
  have h₁ : f.hom.app W ((pullback.fst f.hom (α.app (op V) (ULift.up t)).toBase).app W q) =
      (α.app W (ULift.up (T.obj.map ((pullback.snd f.hom
        (α.app (op V) (ULift.up t)).toBase).app W q).op t))).toBase.app W (𝟙 W.unop) := by
    rw [← hu, ← hx]
    exact fst_app_eq_toBase_app_id α _
  exact (hilbertMorMem_congr α hu hx _ h₁).trans (hilbertMorMem_iff α t _ _ h₁ q rfl rfl)

/-- The inverse image of the glued subspace in a chart, taken along the chart map with the trivial
identification of the structure morphism, is heterogeneously the subspace of the family there. -/
private theorem hilbertMorSubfunctor_preimage_heq {V : BigFppfOver B S hS} (t : T.obj.obj (op V)) :
    (hilbertMorSubfunctor α).preimage (hilbertChartMap f (yonedaEquiv.symm t) rfl) ≍
      (α.app (op V) (ULift.up t)).family.Z :=
  (preimage_hilbertChartMap_heq (yonedaEquiv.symm t) rfl (hilbertMor_toBase_eq α (op V) t)
    (hilbertMorSubfunctor α)).trans (heq_of_eq (hilbertMorSubfunctor_preimage α t))

/-- **The descent input of Stacks 0D3W.** Being a closed subspace of `X_T` which is of finite
presentation, flat and proper over `T` is local on the base for the family of all morphisms to
`T` from the schemes of the big fppf site: if the inverse image of a subfunctor `Z` of `X_T` in
every such chart satisfies the four conditions, then so does `Z`.

For `T` a scheme of the site this holds, by `AlgebraicGeometry.Space.isHilbertLocalOnBase_yoneda`,
because the identity is such a chart. For a general algebraic space it is the descent step of the
source's proof, which chooses a scheme `U` with a surjective étale morphism `U ⟶ T` and descends
the closed subspace obtained over `U` along it; that descent is the effectivity of descent for
closed subspaces together with the fpqc descent of Stacks 05VY and 060V for flatness and finite
presentation, none of which this development carries. -/
def IsHilbertLocalOnBase (f : X ⟶ Y) (T : AlgebraicSpaces B S hS) : Prop :=
  ∀ (h : T ⟶ Y) (Z : Subfunctor (pullback f.hom h.hom)),
    (∀ (V : BigFppfOver B S hS) (c' : yoneda.obj V ⟶ Y.obj) (k : yoneda.obj V ⟶ T.obj)
        (hk : k ≫ h.hom = c'),
      IsClosedSubspace B S hS (Z.preimage (hilbertChartMap f k hk)) ∧
        IsFinitePresentation B S hS
            ((Z.preimage (hilbertChartMap f k hk)).ι ≫ pullback.snd f.hom c') ∧
          IsFlat B S hS ((Z.preimage (hilbertChartMap f k hk)).ι ≫ pullback.snd f.hom c') ∧
            IsProper B S hS
              ((Z.preimage (hilbertChartMap f k hk)).ι ≫ pullback.snd f.hom c')) →
    IsClosedSubspace B S hS Z ∧
      IsFinitePresentation B S hS (Z.ι ≫ pullback.snd f.hom h.hom) ∧
        IsFlat B S hS (Z.ι ≫ pullback.snd f.hom h.hom) ∧
          IsProper B S hS (Z.ι ≫ pullback.snd f.hom h.hom)

/-- **The pair of Stacks 0D3W determined by a morphism of sheaves into the Hilbert presheaf.**
The morphism `T ⟶ Y` is the one underlying the transformation and the closed subspace is the
glued one; the four conditions on it come from the four conditions in every chart through the
descent input. -/
def hilbertMorFamily (hloc : IsHilbertLocalOnBase f T) : SpaceHilbertFamily f T :=
  have hc := hloc (hilbertMorBase α) (hilbertMorSubfunctor α) (by
    intro V c' k hk
    obtain ⟨t, rfl⟩ := yonedaEquiv.symm.surjective k
    obtain rfl : c' = (α.app (op V) (ULift.up t)).toBase :=
      hk.symm.trans (hilbertMor_toBase_eq α (op V) t)
    have hZ : (hilbertMorSubfunctor α).preimage (hilbertChartMap f (yonedaEquiv.symm t) hk) =
        (α.app (op V) (ULift.up t)).family.Z := hilbertMorSubfunctor_preimage α t
    rw [hZ]
    exact ⟨(α.app (op V) (ULift.up t)).family.closed,
      (α.app (op V) (ULift.up t)).family.finitePresentation,
      (α.app (op V) (ULift.up t)).family.flat,
      (α.app (op V) (ULift.up t)).family.proper⟩)
  ⟨hilbertMorBase α, hilbertMorSubfunctor α, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩

/-- The morphism `T ⟶ Y` of `hilbertMorFamily α hloc` is `hilbertMorBase α`. -/
@[simp]
theorem hilbertMorFamily_hom (hloc : IsHilbertLocalOnBase f T) :
    (hilbertMorFamily α hloc).hom = hilbertMorBase α := rfl

/-- The closed subspace of `hilbertMorFamily α hloc` is `hilbertMorSubfunctor α`. -/
@[simp]
theorem hilbertMorFamily_Z (hloc : IsHilbertLocalOnBase f T) :
    (hilbertMorFamily α hloc).Z = hilbertMorSubfunctor α := rfl

end Mor

section Equivalence

variable {f : X ⟶ Y} {T : AlgebraicSpaces B S hS}

/-- Two pairs of Stacks 0D3W agree as soon as their morphisms to `Y` agree and their closed
subspaces agree over that. The subspace is typed through the morphism to `Y`, so its equality is
heterogeneous. -/
theorem SpaceHilbertFamily.ext {a b : SpaceHilbertFamily f T} (hhom : a.hom = b.hom)
    (hZ : a.Z ≍ b.Z) : a = b := by
  obtain ⟨ah, aZ, acl, afp, afl, apr⟩ := a
  obtain ⟨bh, bZ, bcl, bfp, bfl, bpr⟩ := b
  subst hhom
  cases eq_of_heq hZ
  rfl

/-- Two subfunctors of the base changes along two equal morphisms `T ⟶ Y` agree, heterogeneously,
as soon as their inverse images in every chart of `T` agree. -/
theorem subfunctor_heq_of_charts {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {c₁ c₂ : G ⟶ Y.obj}
    (hc : c₁ = c₂) {Z₁ : Subfunctor (pullback f.hom c₁)} {Z₂ : Subfunctor (pullback f.hom c₂)}
    (h : ∀ (V : BigFppfOver B S hS) (k : yoneda.obj V ⟶ G),
      Z₁.preimage (hilbertChartMap f k (rfl : k ≫ c₁ = k ≫ c₁)) ≍
        Z₂.preimage (hilbertChartMap f k (rfl : k ≫ c₂ = k ≫ c₂))) :
    Z₁ ≍ Z₂ := by
  subst hc
  exact heq_of_eq (subfunctor_ext_of_charts f c₁ fun V k ↦ eq_of_heq (h V k))

/-- The morphism `T ⟶ Y` underlying the transformation of a pair of Stacks 0D3W is the morphism
of that pair. -/
theorem hilbertMorBase_toMor (x : SpaceHilbertFamily f T) : hilbertMorBase x.toMor = x.hom := by
  apply ObjectProperty.hom_ext
  refine hom_ext_yoneda fun V p ↦ ?_
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_comp, hilbertMorBase_hom_app]
  show yonedaEquiv (yonedaEquiv.symm (yonedaEquiv p) ≫ x.hom.hom) = _
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- **The pair recovered from the transformation of a pair is that pair.** The morphisms to `Y`
agree, and the closed subspaces agree because they have the same inverse image in every chart of
`T`, which is what `AlgebraicGeometry.Space.hilbertMorSubfunctor_preimage` says. -/
theorem hilbertMorFamily_toMor (hloc : IsHilbertLocalOnBase f T) (x : SpaceHilbertFamily f T) :
    hilbertMorFamily x.toMor hloc = x := by
  refine SpaceHilbertFamily.ext (hilbertMorBase_toMor x) ?_
  refine subfunctor_heq_of_charts (congrArg (fun q ↦ q.hom) (hilbertMorBase_toMor x)) fun V k ↦ ?_
  obtain ⟨t, rfl⟩ := yonedaEquiv.symm.surjective k
  exact hilbertMorSubfunctor_preimage_heq x.toMor t

/-- **The transformation of the pair recovered from a morphism of sheaves is that morphism.** At
every section the two agree in their morphism to `Y` and in their closed subspace, again by
`AlgebraicGeometry.Space.hilbertMorSubfunctor_preimage`. -/
theorem toMor_hilbertMorFamily (hloc : IsHilbertLocalOnBase f T)
    (α : T.obj ⋙ uliftFunctor.{u + 1, u} ⟶ hilbertPresheaf f) :
    (hilbertMorFamily α hloc).toMor = α := by
  ext W t
  obtain ⟨t⟩ := t
  refine HilbertFamilyOver.ext (hilbertMor_toBase_eq α W t) ?_
  exact hilbertMorSubfunctor_preimage_heq α t

/-- **Stacks 0D3W.** For an algebraic space `T` over `S` the morphisms of sheaves on the big fppf
site of `S` from `T` into the Hilbert presheaf `Hilb_{X/Y}` of Stacks 0CZY are the pairs `(h, Z)`
consisting of a morphism `h : T ⟶ Y` of algebraic spaces and a closed subspace `Z` of
`X_T = X ×_{Y, h} T` which is of finite presentation, flat and proper over `T`.

The source writes `=` between a set of morphisms of sheaves and a set of pairs; those are two
different types here, so the honest reading is a bijection, and it is given as an `Equiv`, that
is as data. Both directions are constructed: the forward map is
`AlgebraicGeometry.Space.hilbertMorFamily`, which reads the morphism `h` off the canonical
morphism to `Y` and glues the closed subspaces of the charts, and the inverse is
`AlgebraicGeometry.Space.SpaceHilbertFamily.toMor`, which restricts a pair to every chart;
nothing is chosen from an existence statement.

The hypothesis `hloc` is the descent input `AlgebraicGeometry.Space.IsHilbertLocalOnBase`, which
is all that the general case needs beyond the gluing proved here; it holds unconditionally when
`T` is a scheme of the site. -/
@[stacks 0D3W "the identification as a bijection, for an arbitrary algebraic space"]
def morEquivSpaceHilbertFamily (f : X ⟶ Y) (T : AlgebraicSpaces B S hS)
    (hloc : IsHilbertLocalOnBase f T) :
    (T.obj ⋙ uliftFunctor.{u + 1, u} ⟶ hilbertPresheaf f) ≃ SpaceHilbertFamily f T where
  toFun α := hilbertMorFamily α hloc
  invFun x := x.toMor
  left_inv := toMor_hilbertMorFamily hloc
  right_inv := hilbertMorFamily_toMor hloc

/-- For a scheme of the big fppf site the descent input of Stacks 0D3W holds: the identity is one
of the charts, and the inverse image along it is the subfunctor itself. -/
theorem isHilbertLocalOnBase_yoneda (f : X ⟶ Y) (U : BigFppfOver B S hS) :
    IsHilbertLocalOnBase f ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ := by
  intro h Z hcharts
  have hid : hilbertChartMap f (𝟙 (yoneda.obj U)) (Category.id_comp h.hom) =
      𝟙 (pullback f.hom h.hom) := by
    apply pullback.hom_ext <;> simp
  have hU := hcharts U h.hom (𝟙 (yoneda.obj U)) (Category.id_comp h.hom)
  rwa [hid, Subfunctor.preimage_id] at hU

/-- **Stacks 0D3W for a scheme of the big fppf site.** The morphisms of sheaves from a scheme `U`
of the site into the Hilbert presheaf `Hilb_{X/Y}` of Stacks 0CZY are the pairs `(h, Z)`
consisting of a morphism `h : U ⟶ Y` of algebraic spaces and a closed subspace `Z` of
`X_U = X ×_{Y, h} U` which is of finite presentation, flat and proper over `U`.

This is `AlgebraicGeometry.Space.morEquivSpaceHilbertFamily` at the algebraic space of `U`, where
the descent input is discharged by the identity chart, so nothing is assumed. -/
@[stacks 0D3W "the identification for a scheme of the big fppf site, unconditionally"]
def morEquivSpaceHilbertFamilyOfScheme (f : X ⟶ Y) (U : BigFppfOver B S hS) :
    (uliftYoneda.{u + 1}.obj U ⟶ hilbertPresheaf f) ≃
      SpaceHilbertFamily f ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :=
  morEquivSpaceHilbertFamily f _ (isHilbertLocalOnBase_yoneda f U)

end Equivalence

end Chart

end AlgebraicGeometry.Space

end
