module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteSheafification
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.IdealPresentationGlobal

/-!
# Sheafification commutes with restriction to the slice over a presentation

Let `(𝒞, 𝒪)` be a ringed site, let `ℐ ⊂ 𝒪` be a sheaf of ideals of finite type and let `P` be a
local presentation of `ℐ`, i.e. an object `U = P.obj` of `𝒞` together with a finite family
`f_1, …, f_r` of sections of `𝒪` over `U` generating `ℐ|_U`. The proof of [Stacks, Tag 099E]
builds the complex `K^•` of [Stacks, Tag 099D] on the presentation site of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.IdealPresentationSite`,
sheafifies it there, and then asserts that its restriction to the slice site `𝒞/U` is the
sheafification *on `𝒞/U`* of the restricted presheaf complex `K^•_{U, I}`. That interchange is
what this file proves:

`a_{IdealPres}(K^•)|_{𝒞/U} ≅ a_{𝒞/U}(K^•|_{𝒞/U})`,

degreewise for the complex and compatibly with the two augmentations onto the structure sheaf.

The mathematics is that `AlgebraicGeometry.RingedSite.idealPresOver P : 𝒞/U ⥤ IdealPres ℐ` is a
**continuous and cocontinuous** functor of sites. Cocontinuity is what makes a locally bijective
morphism of presheaves stay locally bijective after restriction, hence what makes the comparison
invertible; continuity is what makes the restriction of a sheaf a sheaf, so that there is a
restriction functor on sheaves of modules at all. Granted those two, the comparison is
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyNatIso`, which is exactly
this statement for an arbitrary continuous and cocontinuous functor; nothing about sheafification
is reproved here.

Both conditions are proved by hand, because `idealPresOver P` is neither full nor
representably flat:

* **cover-preservation** is free: the image in `𝒞` of a sieve of `𝒞/U` under
  `idealPresOver P ⋙ idealPresForget ℐ = Over.forget U` is its image under `Over.forget U`, which
  covers by the definition of `CategoryTheory.GrothendieckTopology.over`;
* **cocontinuity** needs the lifting lemma `idealPresOverLift`: a morphism `Q ⟶ P|_V` of
  presentations and an arrow `i` of `𝒞` into `Q.obj` together lift to a morphism
  `P|_{V'} ⟶ Q` over `i`, because the span of `P`'s generators at an arrow factors through the
  base. So a sieve covering `P|_V` in the presentation site pulls back to a sieve of `𝒞/U` whose
  image contains the image of the original one;
* **compatible-preservation** needs the same lifting lemma in its invertible case,
  `idealPresOverIso`: a morphism `W ⟶ P|_V` of presentations exhibits `W` as *isomorphic* to the
  restriction of `P` along the composite `W.obj ⟶ V.left ⟶ U`. This is the substitute for the
  fullness that `CategoryTheory.compatiblePreservingOfDownwardsClosed` asks for and
  `idealPresOver P` does not have.

## Main definitions

* `AlgebraicGeometry.RingedSite.idealPresOverLift`: a morphism of presentations over the base of
  `P`, lifted to a restriction of `P`.
* `AlgebraicGeometry.RingedSite.idealPresOverIso`: a presentation mapping to a restriction of
  `P` is isomorphic to a restriction of `P`.
* `AlgebraicGeometry.RingedSite.presSliceRingSheaf`, `presSlicePresheafRestriction`,
  `presSliceSheafRestriction` and `presSliceSheafification`: the structure sheaf of rings of the
  slice site read as the restriction along `idealPresOver P`, the two restriction functors it
  indexes, and the sheafification functor on the slice site.
* `AlgebraicGeometry.RingedSite.presSliceCechAugmentation`: the augmentation of the sheafified
  restricted complex on the slice site.

## Main results

* `AlgebraicGeometry.RingedSite.coverPreserving_idealPresOver`,
  `AlgebraicGeometry.RingedSite.compatiblePreserving_idealPresOver` and
  `AlgebraicGeometry.RingedSite.isContinuous_idealPresOver`: **`idealPresOver P` is a continuous
  functor of sites**, with no hypothesis on `ℐ`.
* `AlgebraicGeometry.RingedSite.isCocontinuous_idealPresOver`: **`idealPresOver P` is
  cocontinuous**, given that the forgetful functor from the presentation site is cover dense;
  `isCocontinuous_idealPresOver_of_isFiniteType` supplies that from
  `SheafOfModules.IsFiniteType`.
* `AlgebraicGeometry.RingedSite.presSliceSheafifyNatIso`: **sheafification of presheaves of
  modules commutes with restriction to the slice over a presentation**, as an isomorphism of
  functors.
* `AlgebraicGeometry.RingedSite.presSliceSheafComplexIso`: **the same degreewise for a complex**
  — the restriction to `𝒞/U` of the sheafified `K^•` is the sheafification on `𝒞/U` of the
  restricted `K^•`.
* `AlgebraicGeometry.RingedSite.presSliceSheafComplexIso_inv_f_zero_comp`: **the degreewise
  comparison is compatible with the augmentations** — in degree `0` it carries the slice
  augmentation to the restriction of the augmentation of the sheafified `K^•`.

## Implementation notes

**Where the universes collapse, and where they do not.** The site-theoretic statements — the
lifting lemmas, cover-preservation, compatible-preservation, continuity and cocontinuity — are at
`AlgebraicGeometry.RingedSite.{u, v, w}` with all three parameters free. The sheafification
statements are at `{u, u, u}`, inherited from
`StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.IdealPresentationGlobal`:
`AlgebraicGeometry.RingedSite.presRingSheaf` is defined there through the Comparison Lemma, whose
`HasLimitsOfShape (StructuredArrow Y G.op) AddCommGrpCat.{w}` hypothesis forces the coefficient
universe to contain the objects and the arrows of `𝒞`. At `{u, u, u}` the sheafification
hypotheses on the slice topology and on the presentation topology are found by instance search
with no hypothesis, so nothing is threaded.

**`idealPresOver P` is a slice inclusion only up to equivalence, and the equivalence is not
built.** `idealPresOverIso` and `idealPresOverLift` together say that `𝒞/U` is equivalent, as a
site, to the slice of the presentation site over `P`; one could build that equivalence and then
quote Mathlib's instances for `CategoryTheory.Over.forget`. The direct route is taken instead
because the equivalence would still need both cover-preservation statements — the topology
comparison in both directions — which is the entire content, plus the bookkeeping of the
equivalence on top.

**`rw` is unusable in the span-of-generators goals.** `AlgebraicGeometry.RingedSite.IdealPres.Hom`
states its condition over `⟶` of `X.C`, and inside the structure field that hom-type is spelled
through a different `Quiver` instance than the one the ambient category produces. A `rw` in such
a goal fails with "the target expression is not type-correct under `implicit` transparency" while
the pattern is plainly visible. The three equalities of arrows of `𝒞` that the lifting lemmas
need — `over_lift_comp_hom`, `comp_id_comp_assoc`, `over_hom_eq_of_base_eq` — are therefore
stated as separate lemmas whose variables live in `X.C` only, where `rw` works, and are applied
rather than rewritten with.

## References

* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 00XB](https://stacks.math.columbia.edu/tag/00XB) — the localized site
  `𝒞/U`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.PushforwardSheafification

universe u v w w'

namespace AlgebraicGeometry.RingedSite

section SliceSite

variable {X : RingedSite.{u, v, w}}
  {𝓘 : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}

/-- An arrow of `𝒞` that factors an arrow of the slice over `U` composes with the structure map
of its target to the structure map of its source. -/
theorem over_lift_comp_hom {U : X.C} {V V' : Over U} (φ : V' ⟶ V) {T : X.C}
    (i : V'.left ⟶ T) (b : T ⟶ V.left) (hi : i ≫ b = φ.left) {Z : X.C} (p : Z ⟶ V'.left)
    {q : Z ⟶ T} (hq : p ≫ i = q) : p ≫ V'.hom = (q ≫ b) ≫ V.hom := by
  subst hq
  rw [Category.assoc p i b, hi, Category.assoc, Over.w φ]

/-- Reassociation past an identity, in the form the span condition of a morphism of
presentations produces. -/
theorem comp_id_comp_assoc {T₁ T₂ T₃ T₄ : X.C} {p q : T₁ ⟶ T₂} (hq : p ≫ 𝟙 T₂ = q)
    (b : T₂ ⟶ T₃) (c : T₃ ⟶ T₄) : (p ≫ b) ≫ c = q ≫ b ≫ c := by
  rw [← hq, Category.comp_id, Category.assoc]

/-- Two arrows of `𝒞` into the bases of two objects of the slice over `U` that agree after
composing into a third object already agree after composing to `U`. -/
theorem over_hom_eq_of_base_eq {U : X.C} {Y₁ Y₂ Z : Over U} (g₁ : Y₁ ⟶ Z) (g₂ : Y₂ ⟶ Z)
    {W : X.C} (b₁ : W ⟶ Y₁.left) (b₂ : W ⟶ Y₂.left) (hb : b₁ ≫ g₁.left = b₂ ≫ g₂.left) :
    b₂ ≫ Y₂.hom = b₁ ≫ Y₁.hom := by
  rw [← Over.w g₂, ← Category.assoc, ← hb, Category.assoc, Over.w g₁]

/-- **A morphism of presentations lifts to a restriction of `P`.** Given a morphism
`g : Q ⟶ P|_V` of presentations over the base of `P` and an arrow `i` of `𝒞` into `Q.obj`
factoring the underlying arrow of some `φ : V' ⟶ V` of the slice, this is the morphism
`P|_{V'} ⟶ Q` over `i`.

The span condition holds because the span of `P`'s generators at an arrow into `V'.left` is
their span at the composite into `P.obj`, and that composite is computed by `g`'s own span
condition. -/
def idealPresOverLift (P : IdealPres 𝓘) {V V' : Over P.obj} (φ : V' ⟶ V) {Q : IdealPres 𝓘}
    (g : Q ⟶ (idealPresOver P).obj V) (i : V'.left ⟶ Q.obj) (hi : i ≫ g.base = φ.left) :
    (idealPresOver P).obj V' ⟶ Q where
  base := i
  spanAt_eq {_} p q hq :=
    ((P.spanAt_restrict V'.hom p).trans
      (congrArg (spanAt P.gen) (over_lift_comp_hom φ i g.base hi p hq))).trans
      ((P.spanAt_restrict V.hom (q ≫ g.base)).symm.trans
        (g.spanAt_eq q (q ≫ g.base) rfl).symm)

/-- An arrow of the slice over `P.obj` whose underlying arrow factors through a morphism of a
sieve of the presentation site lies in the pullback of that sieve. -/
theorem arrows_functorPullback_idealPresOver (P : IdealPres 𝓘) {V : Over P.obj}
    (S : Sieve ((idealPresOver P).obj V)) {Q : IdealPres 𝓘} {g : Q ⟶ (idealPresOver P).obj V}
    (hg : S.arrows g) {V' : Over P.obj} (φ : V' ⟶ V) (i : V'.left ⟶ Q.obj)
    (hi : i ≫ g.base = φ.left) :
    (Sieve.functorPullback (idealPresOver P) S).arrows φ := by
  have e : (idealPresOver P).map φ = idealPresOverLift P φ g i hi ≫ g :=
    IdealPres.Hom.ext' hi.symm
  show S.arrows ((idealPresOver P).map φ)
  rw [e]
  exact S.downward_closed hg _

/-- **`idealPresOver P` preserves covers.** Its composite with the forgetful functor to `𝒞` is
`CategoryTheory.Over.forget`, so the image in `𝒞` of a covering sieve of the slice site is the
covering sieve it came from. -/
theorem coverPreserving_idealPresOver (P : IdealPres 𝓘) :
    CoverPreserving (X.J.over P.obj) ((idealPresForget 𝓘).restrictedTopology X.J)
      (idealPresOver P) where
  cover_preserve {V S} hS :=
    Functor.mem_restrictedTopology_of_functorPushforward_mem
      (by rwa [← Sieve.functorPushforward_comp])

/-- **`idealPresOver P` is cocontinuous.** A sieve covering the restricted presentation `P|_V`
pulls back to a sieve of `𝒞/V` whose image in `𝒞` contains the image of the original sieve: an
arrow `i ≫ g.base` of that image is the underlying arrow of an arrow of the slice over which
`idealPresOverLift` lifts `g`.

Cover-density of the forgetful functor is used only to read membership in the restricted
topology as covering of the image sieve. -/
theorem isCocontinuous_idealPresOver [(idealPresForget 𝓘).IsCoverDense X.J]
    (P : IdealPres 𝓘) :
    (idealPresOver P).IsCocontinuous (X.J.over P.obj)
      ((idealPresForget 𝓘).restrictedTopology X.J) where
  cover_lift {V S} hS := by
    let := isLocallyFull_idealPresForget 𝓘
    refine X.J.superset_covering (fun W b hb ↦ ?_)
      (Functor.mem_restrictedTopology_iff.1 hS)
    obtain ⟨Q, g, i, hg, rfl⟩ := hb
    exact (Sieve.overEquiv_iff _ _).2
      (arrows_functorPullback_idealPresOver P S hg _ i rfl)

/-- **A presentation mapping to a restriction of `P` is isomorphic to a restriction of `P`.**
Both morphisms are the identity on the common base object `W.obj`, and both span conditions are
`f`'s own.

This is the substitute for the fullness hypothesis of
`CategoryTheory.compatiblePreservingOfDownwardsClosed`, which `idealPresOver P` does not
satisfy. -/
def idealPresOverIso (P : IdealPres 𝓘) {V : Over P.obj} {W : IdealPres 𝓘}
    (f : W ⟶ (idealPresOver P).obj V) :
    (idealPresOver P).obj (Over.mk (f.base ≫ V.hom)) ≅ W where
  hom := idealPresOverLift P (Over.homMk f.base) f (𝟙 W.obj) (Category.id_comp _)
  inv :=
    { base := 𝟙 W.obj
      spanAt_eq := fun {_} p q hq ↦
        ((f.spanAt_eq p (p ≫ f.base) rfl).trans
            (P.spanAt_restrict V.hom (p ≫ f.base))).trans
          ((congrArg (spanAt P.gen) (comp_id_comp_assoc hq f.base V.hom)).trans
            (P.spanAt_restrict (f.base ≫ V.hom) q).symm) }
  hom_inv_id := IdealPres.Hom.ext' (Category.id_comp (𝟙 W.obj))
  inv_hom_id := IdealPres.Hom.ext' (Category.id_comp (𝟙 W.obj))

/-- **`idealPresOver P` preserves compatible families.** The two arrows of the presentation site
out of `W` both factor, through `idealPresOverIso`, as `idealPresOver P` applied to arrows of the
slice out of one object; compatibility of the family at those two arrows of the slice, pushed
along the isomorphism, is the assertion. -/
theorem compatiblePreserving_idealPresOver (P : IdealPres 𝓘) :
    CompatiblePreserving.{w'} ((idealPresForget 𝓘).restrictedTopology X.J)
      (idealPresOver P) := by
  refine ⟨fun ℱ {Z T x} hx {Y₁ Y₂ W} f₁ f₂ {g₁ g₂} hg₁ hg₂ he ↦ ?_⟩
  have hb : f₁.base ≫ g₁.left = f₂.base ≫ g₂.left := congrArg IdealPres.Hom.base he
  let φ₁ : Over.mk (f₁.base ≫ Y₁.hom) ⟶ Y₁ := Over.homMk f₁.base
  let φ₂ : Over.mk (f₁.base ≫ Y₁.hom) ⟶ Y₂ :=
    Over.homMk f₂.base (over_hom_eq_of_base_eq g₁ g₂ f₁.base f₂.base hb)
  have h1 : (idealPresOver P).map φ₁ = (idealPresOverIso P f₁).hom ≫ f₁ :=
    IdealPres.Hom.ext' (Category.id_comp f₁.base).symm
  have h2 : (idealPresOver P).map φ₂ = (idealPresOverIso P f₁).hom ≫ f₂ :=
    IdealPres.Hom.ext' (Category.id_comp f₂.base).symm
  refine (ℱ.obj.mapIso (idealPresOverIso P f₁).op).toEquiv.injective ?_
  have key := hx φ₁ φ₂ hg₁ hg₂ (Over.OverMorphism.ext hb)
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, h1, h2, op_comp,
    Functor.map_comp, types_comp_apply] at key
  simpa only [Iso.op_hom, Iso.toEquiv_fun, Functor.mapIso_hom] using key

/-- **`idealPresOver P` is a continuous functor of sites**, with no hypothesis on `ℐ`: it
preserves covers and preserves compatible families. So restriction of sections along it carries
sheaves on the presentation site to sheaves on the slice site. -/
instance isContinuous_idealPresOver (P : IdealPres 𝓘) :
    (idealPresOver P).IsContinuous (X.J.over P.obj)
      ((idealPresForget 𝓘).restrictedTopology X.J) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving_idealPresOver P)
    (coverPreserving_idealPresOver P)

end SliceSite

section SliceSheafification

variable (X : RingedSite.{u, u, u})
  (𝓘 : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
  (h : 𝓘.toSheafOfModules.IsFiniteType) (P : IdealPres 𝓘)

/-- **The structure sheaf of rings of the slice site over the base of a presentation**, read as
the restriction of the structure sheaf of the presentation site along `idealPresOver P`. -/
abbrev presSliceRingSheaf : Sheaf (X.J.over P.obj) RingCat.{u} :=
  pushforwardRingSheaf (X.J.over P.obj) (idealPresOver P) (presRingSheaf X 𝓘 h)

/-- The restricted sheaf of rings **is** the structure sheaf of the localized ringed site, on
the nose: both are the structure presheaf of `𝒞` read along `Over.forget P.obj`, the composite
`idealPresOver P ⋙ idealPresForget ℐ` being `Over.forget P.obj` by
`AlgebraicGeometry.RingedSite.idealPresOver_comp_forget`. -/
theorem presSliceRingSheaf_eq :
    presSliceRingSheaf X 𝓘 h P = (Stacks.SheafOfModules.Tensor.ringSheaf (X.over P.obj).O) := rfl

/-- Restriction of presheaves of modules from the presentation site to the slice site over the
base of a presentation. -/
abbrev presSlicePresheafRestriction :
    PresheafOfModules.{u} (presRingSheaf X 𝓘 h).obj ⥤
      PresheafOfModules.{u} (presSliceRingSheaf X 𝓘 h P).obj :=
  presheafPushforwardFunctor.{u} (X.J.over P.obj) (idealPresOver P) (presRingSheaf X 𝓘 h)

/-- Restriction of sheaves of modules from the presentation site to the slice site over the base
of a presentation. -/
abbrev presSliceSheafRestriction :
    SheafOfModules.{u} (presRingSheaf X 𝓘 h) ⥤
      SheafOfModules.{u} (presSliceRingSheaf X 𝓘 h P) :=
  sheafPushforwardFunctor.{u} (X.J.over P.obj) (idealPresOver P) (presRingSheaf X 𝓘 h)

/-- **The sheafification functor for presheaves of modules on the slice site over the base of a
presentation.** -/
abbrev presSliceSheafification :
    PresheafOfModules.{u} (presSliceRingSheaf X 𝓘 h P).obj ⥤
      SheafOfModules.{u} (presSliceRingSheaf X 𝓘 h P) :=
  PresheafOfModules.sheafification.{u} (𝟙 (presSliceRingSheaf X 𝓘 h P).obj)

/-- The sheafification functor `presSliceSheafification` on the slice site is additive. -/
instance additive_presSliceSheafification : (presSliceSheafification X 𝓘 h P).Additive :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (presSliceRingSheaf X 𝓘 h P).obj)).left_adjoint_additive

/-- The restriction functor `presSlicePresheafRestriction` on presheaves of modules preserves zero
morphisms. -/
instance preservesZeroMorphisms_presSlicePresheafRestriction :
    (presSlicePresheafRestriction X 𝓘 h P).PreservesZeroMorphisms where
  map_zero _ _ := PresheafOfModules.hom_ext fun _ ↦ rfl

/-- The restriction functor `presSliceSheafRestriction` on sheaves of modules preserves zero
morphisms. -/
instance preservesZeroMorphisms_presSliceSheafRestriction :
    (presSliceSheafRestriction X 𝓘 h P).PreservesZeroMorphisms where
  map_zero _ _ := SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ ↦ rfl)

/-- **The restriction of the structure sheaf of the presentation site, as a sheaf of modules over
itself, is the structure sheaf of the slice site.** -/
theorem presSliceSheafRestriction_obj_unit :
    (presSliceSheafRestriction X 𝓘 h P).obj (SheafOfModules.unit (presRingSheaf X 𝓘 h)) =
      SheafOfModules.unit (presSliceRingSheaf X 𝓘 h P) := rfl

include h

/-- **`idealPresOver P` is cocontinuous at a finite-type sheaf of ideals**: the cover-density
hypothesis of `AlgebraicGeometry.RingedSite.isCocontinuous_idealPresOver` is supplied by
`AlgebraicGeometry.RingedSite.isCoverDense_idealPresForget_of_isFiniteType`. -/
theorem isCocontinuous_idealPresOver_of_isFiniteType :
    (idealPresOver P).IsCocontinuous (X.J.over P.obj) (presTopology X 𝓘) :=
  let := isCoverDense_idealPresForget_of_isFiniteType X 𝓘 h
  isCocontinuous_idealPresOver P

/-- **Sheafification of presheaves of modules commutes with restriction to the slice over a
presentation**, as an isomorphism of functors:

`a_{𝒞/U}(M|_{𝒞/U}) ≅ a_{IdealPres}(M)|_{𝒞/U}`.

This is the instance at `idealPresOver P` of
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyNatIso`, the two inputs being
`AlgebraicGeometry.RingedSite.isContinuous_idealPresOver` and
`isCocontinuous_idealPresOver_of_isFiniteType`. -/
def presSliceSheafifyNatIso :
    presSlicePresheafRestriction X 𝓘 h P ⋙ presSliceSheafification X 𝓘 h P ≅
      presSheafification X 𝓘 h ⋙ presSliceSheafRestriction X 𝓘 h P :=
  let := isCocontinuous_idealPresOver_of_isFiniteType X 𝓘 h P
  pushforwardSheafifyNatIso.{u} (X.J.over P.obj) (idealPresOver P) (presRingSheaf X 𝓘 h)

/-- **The restriction to `𝒞/U` of the sheafified `K^•` is the sheafification on `𝒞/U` of the
restricted `K^•`**, degreewise and compatibly with the differentials.

This is the interchange [Stacks, Tag 099E] needs in order to compute the restriction of its
global complex on a slice where `ℐ` is generated by finitely many sections: the right-hand side
is a sheafification performed on `𝒞/U` of a complex of presheaves of modules on `𝒞/U`, which is
where the extended alternating Čech complex of `f_1, …, f_r` lives. -/
def presSliceSheafComplexIso :
    ((presSliceSheafRestriction X 𝓘 h P).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (presSheafComplex X 𝓘 h) ≅
      ((presSliceSheafification X 𝓘 h P).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (((presSlicePresheafRestriction X 𝓘 h P).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (presCechComplex 𝓘)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ((presSliceSheafifyNatIso X 𝓘 h P).app ((presCechComplex 𝓘).X n)).symm)
    fun i j _ ↦ ((presSliceSheafifyNatIso X 𝓘 h P).inv.naturality
      ((presCechComplex 𝓘).d i j)).symm

/-- **The augmentation of the sheafified restricted complex on the slice site**: the
sheafification on `𝒞/U` of the restriction of
`AlgebraicGeometry.RingedSite.presCechAugmentation`. -/
def presSliceCechAugmentation :
    (((presSliceSheafification X 𝓘 h P).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (((presSlicePresheafRestriction X 𝓘 h P).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (presCechComplex 𝓘))).X 0 ⟶
      (presSliceSheafRestriction X 𝓘 h P).obj (SheafOfModules.unit (presRingSheaf X 𝓘 h)) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (presSliceRingSheaf X 𝓘 h P).obj)).symm
    (pushforwardForgetHom.{u} (X.J.over P.obj) (idealPresOver P) (presRingSheaf X 𝓘 h)
      (presCechAugmentation 𝓘))

/-- The inverse of the degreewise comparison is, in each degree, the comparison morphism
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyHom`. -/
theorem presSliceSheafComplexIso_inv_f (n : ℕ) :
    (presSliceSheafComplexIso X 𝓘 h P).inv.f n =
      pushforwardSheafifyHom.{u} (X.J.over P.obj) (idealPresOver P) (presRingSheaf X 𝓘 h)
        ((presCechComplex 𝓘).X n) := rfl

/-- **The degreewise comparison is compatible with the augmentations.** In degree `0` the
comparison of `presSliceSheafComplexIso` carries the augmentation of the sheafified restricted
complex to the restriction of the augmentation of the sheafified `K^•`.

Both are adjoint transposes of the restriction of
`AlgebraicGeometry.RingedSite.presCechAugmentation`, which is
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyHom_comp_map`. -/
theorem presSliceSheafComplexIso_inv_f_zero_comp :
    (presSliceSheafComplexIso X 𝓘 h P).inv.f 0 ≫
        (presSliceSheafRestriction X 𝓘 h P).map (presSheafAugmentation X 𝓘 h) =
      presSliceCechAugmentation X 𝓘 h P :=
  let := isCocontinuous_idealPresOver_of_isFiniteType X 𝓘 h P
  (congrArg (fun x ↦ x ≫ (presSliceSheafRestriction X 𝓘 h P).map
        (presSheafAugmentation X 𝓘 h))
      (presSliceSheafComplexIso_inv_f X 𝓘 h P 0)).trans
    (pushforwardSheafifyHom_comp_map.{u} (X.J.over P.obj) (idealPresOver P)
      (presRingSheaf X 𝓘 h) (P := (presCechComplex 𝓘).X 0)
      (T := SheafOfModules.unit (presRingSheaf X 𝓘 h)) (presCechAugmentation 𝓘))

end SliceSheafification

end AlgebraicGeometry.RingedSite

end
