module

public import Mathlib.CategoryTheory.Localization.Bifunctor
public import Mathlib.CategoryTheory.Shift.CommShiftTwo
public import StacksFrontier.CategoryTheory.Shift.LiftNatTransCommShift

/-!
# Lifting a transformation of bifunctors through localizations respects the shifts

Let `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` be localization functors for morphism properties `W₁`,
`W₂`, let `F₁, F₂ : C₁ ⥤ C₂ ⥤ E` be bifunctors factoring through `L₁` and `L₂` as
`F₁', F₂' : D₁ ⥤ D₂ ⥤ E`, and let `τ : F₁ ⟶ F₂`. Mathlib descends `τ` to
`CategoryTheory.Localization.lift₂NatTrans L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' τ : F₁' ⟶ F₂'`. This file
proves that the descended transformation is compatible with the shifts in each variable
separately — `CategoryTheory.NatTrans.CommShift₂` — as soon as `τ` is.

This is the two-variable analogue of
`CategoryTheory.Localization.liftNatTrans_commShift`, and it is what supplies a shift
compatibility for a comparison isomorphism of *bifunctors* produced by
`CategoryTheory.Localization.lift₂NatIso`, which carries none by construction.

## Main results

* `CategoryTheory.Localization.Lifting₂.curryProd`: a functor on `D₁ × D₂` lifting one on
  `C₁ × C₂` along `L₁.prod L₂` curries to a bifunctor lifting the curried one, the converse of
  `CategoryTheory.Localization.Lifting₂.uncurry`.
* `CategoryTheory.Localization.curry_map_liftNatTrans`: the one-variable descent along a product
  localization, curried, is the two-variable descent. Together with `Lifting₂.curryProd` this
  brings a comparison built by the one-variable `liftNatIso` over a product localization — the
  shape [Stacks, Tag 079U] is built in — into the scope of the results below.
* `CategoryTheory.Localization.lift₂NatTrans_app_eq_liftNatTrans`: at an object `L₁.obj X₁` in
  the image of the first localization, the component of the descended transformation is
  *literally* the one-variable descent along `L₂` of the component `τ.app X₁`. This is the
  reduction that makes the two-variable statement a corollary of the one-variable one.
* `CategoryTheory.Localization.lift₂NatTrans_flipApp_eq_liftNatTrans`: the same in the other
  variable.
* `CategoryTheory.Localization.commShift_app_of_isLocalization`: a transformation of bifunctors
  whose components over the image of a localization functor commute with the shift has *all* its
  components commute with the shift.
* `CategoryTheory.Localization.lift₂NatTrans_commShift_app` and
  `lift₂NatTrans_commShift_flipApp`: the two halves of the conclusion, at an arbitrary object of
  the localization.
* `CategoryTheory.Localization.lift₂NatTrans_commShift₂` and
  `lift₂NatIso_hom_commShift₂`: the conclusion, as a
  `CategoryTheory.NatTrans.CommShift₂`.

## Implementation notes

**The two-variable case is a corollary of the one-variable case, twice.** Mathlib's
`CategoryTheory.NatTrans.CommShift₂` has exactly two fields, `commShift_app` and
`commShift_flipApp`, each a family of one-variable `CategoryTheory.NatTrans.CommShift`
statements; no two-variable argument and no sign coherence is involved in proving it. Two things
have to be supplied beyond the one-variable lemma:

* *The identification.* `CategoryTheory.Localization.lift₂NatTrans` is defined by uncurrying and
  descending along `L₁.prod L₂`, so its component at `L₁.obj X₁` is not by construction a
  one-variable descent along `L₂`. It is one: both sides agree at every `L₂.obj X₂` by
  `lift₂NatTrans_app_app` and `liftNatTrans_app`, and `natTrans_ext` promotes that to equality.
  The `CategoryTheory.Localization.Lifting` datum for the component is
  `CategoryTheory.Localization.Lifting₂.fst`, whose isomorphism is the evaluation of the
  `Lifting₂` isomorphism, so the two agree by `rfl`.
* *Essential surjectivity.* `NatTrans.CommShift₂` asks for `commShift_app` at every object of
  `D₁`, not only at those of the form `L₁.obj X₁`. A localization functor is essentially
  surjective (`CategoryTheory.Localization.essSurj`), and a component at an isomorphic object is
  conjugate to the given one by `F₁'.map` and `F₂'.map` of that isomorphism, both of which commute
  with the shift because `F₁'` and `F₂'` do (the `commShift_map` field of
  `CategoryTheory.Functor.CommShift₂`). That is `commShift_app_of_isLocalization`.

**Why the lifting isomorphisms are hypotheses and not instances.** The hypotheses `hι₁`, `hι₂`
are the shift compatibility of the two `CategoryTheory.Localization.Lifting₂` isomorphisms,
evaluated in the first variable; they are exactly what the one-variable lemma consumes. They are
stated through `CategoryTheory.Localization.Lifting₂.fst`, introduced by `letI`, rather than as
`NatTrans.CommShift ((Lifting₂.iso …).hom.app X₁) M`: the latter is the same proposition, but its
source bifunctor is `(((whiskeringLeft₂ E).obj L₁).obj L₂).obj F₁'`, and instance resolution does
not see through `CategoryTheory.whiskeringLeft₂` to the `L₂ ⋙ F₁'.obj (L₁.obj X₁)` whose
`CategoryTheory.Functor.CommShift` is available, so the statement does not elaborate. For the
same reason `CategoryTheory.Functor.CommShift₂.precomp₁` and `precomp₂` do not combine into a
`CommShift₂` for that whiskered bifunctor, which is why the hypotheses are not packaged as a
single `NatTrans.CommShift₂` of the `Lifting₂` isomorphism. When the lifting is tautological, as
it is for [Stacks, Tag 079U], these isomorphisms are identities and the hypotheses are discharged
by `CategoryTheory.NatTrans.CommShift.id` after rewriting with `Lifting₂.curryProd_iso_hom_app_app`
or the corresponding `Iso.refl` computation.

**What this does and does not do for [Stacks, Tag 079U].** The comparison of Tag 079U,
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso` in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/PullbackTensorComparison.lean`, is built
as a one-variable `CategoryTheory.Localization.liftNatIso` along
`kFlatQPair = kFlatQY.prod kFlatQY` between the two *uncurried* bifunctors on
`D(𝒪_Y) × D(𝒪_Y)`. `Lifting₂.curryProd` turns that datum into the `Lifting₂` this file is
stated over, and `curry_map_liftNatTrans` identifies the uncurried descent with
`lift₂NatTrans`, so the results here do apply to it in principle. What is *not* available in this
development, and is what still blocks a shift compatibility for Tag 079U, is the input:

* the K-flat models category `(CochainComplex.KFlatBifunctor.kFlatObjects _).FullSubcategory`
  carries no shift. Mathlib supplies one, `CategoryTheory.ObjectProperty.hasShift`, from
  `CategoryTheory.ObjectProperty.IsStableUnderShift` — "a shift of a K-flat complex with flat
  terms is again one" — which is not recorded anywhere in this development;
* with that, `CategoryTheory.ObjectProperty.commShiftι` would give `kFlatQY.CommShift ℤ`;
* the four bifunctors would need `CategoryTheory.Functor.CommShift₂Int` instances; for the
  derived tensor product the per-variable halves are the `commShift_left`/`commShift_right` data
  of [Stacks, Tag 06YU], but the sign coherence between them is not recorded;
* and `modelsComparison` — the degreewise comparison `f^*(K^p ⊗ L^q) ≅ f^*K^p ⊗ f^*L^q` of
  [Stacks, Tag 01CD] assembled on total tensor complexes — would need a
  `NatTrans.CommShift₂`, which is a Koszul sign computation on total complexes.

None of those four is a localization-theoretic fact, and none is weakened or assumed here.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public section

namespace CategoryTheory.Localization

open CategoryTheory.Functor

variable {C₁ C₂ D₁ D₂ E : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  [Category* E]

/-! ### A lifting along a product localization, curried -/

section CurryProd

variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  (F F' : C₁ × C₂ ⥤ E)

/-- **A functor on `D₁ × D₂` lifting one on `C₁ × C₂` along `L₁.prod L₂` curries to a bifunctor
lifting the curried one in the sense of `CategoryTheory.Localization.Lifting₂`.**  This is the
converse of `CategoryTheory.Localization.Lifting₂.uncurry`, and it is what brings a comparison
built by the one-variable `liftNatIso` over a product localization — the shape
[Stacks, Tag 079U] is built in — into the two-variable vocabulary. -/
@[instance_reducible]
noncomputable def Lifting₂.curryProd (F : C₁ × C₂ ⥤ E) (F' : D₁ × D₂ ⥤ E)
    [Lifting (L₁.prod L₂) (W₁.prod W₂) F F'] :
    Lifting₂ L₁ L₂ W₁ W₂ (Functor.curry.obj F) (Functor.curry.obj F') where
  iso := (Functor.curryObjProdComp L₁ L₂ F').symm ≪≫
    Functor.curry.mapIso (Lifting.iso (L₁.prod L₂) (W₁.prod W₂) F F')

variable {L₁ L₂ W₁ W₂}

/-- The isomorphism of `Lifting₂.curryProd` has the components of the isomorphism it is built
from. -/
theorem Lifting₂.curryProd_iso_hom_app_app (F : C₁ × C₂ ⥤ E) (F' : D₁ × D₂ ⥤ E)
    [Lifting (L₁.prod L₂) (W₁.prod W₂) F F'] (X₁ : C₁) (X₂ : C₂) :
    letI := Lifting₂.curryProd L₁ L₂ W₁ W₂ F F'
    ((Lifting₂.iso L₁ L₂ W₁ W₂ (Functor.curry.obj F) (Functor.curry.obj F')).hom.app X₁).app X₂ =
      (Lifting.iso (L₁.prod L₂) (W₁.prod W₂) F F').hom.app (X₁, X₂) := by
  change ((((Functor.curryObjProdComp L₁ L₂ F').symm ≪≫
    Functor.curry.mapIso (Lifting.iso (L₁.prod L₂) (W₁.prod W₂) F F')).hom.app X₁).app X₂) = _
  simp

/-- The inverse of the isomorphism of `Lifting₂.curryProd` has the components of the inverse of
the isomorphism it is built from. -/
theorem Lifting₂.curryProd_iso_inv_app_app (F : C₁ × C₂ ⥤ E) (F' : D₁ × D₂ ⥤ E)
    [Lifting (L₁.prod L₂) (W₁.prod W₂) F F'] (X₁ : C₁) (X₂ : C₂) :
    letI := Lifting₂.curryProd L₁ L₂ W₁ W₂ F F'
    ((Lifting₂.iso L₁ L₂ W₁ W₂ (Functor.curry.obj F) (Functor.curry.obj F')).inv.app X₁).app X₂ =
      (Lifting.iso (L₁.prod L₂) (W₁.prod W₂) F F').inv.app (X₁, X₂) := by
  change ((((Functor.curryObjProdComp L₁ L₂ F').symm ≪≫
    Functor.curry.mapIso (Lifting.iso (L₁.prod L₂) (W₁.prod W₂) F F')).inv.app X₁).app X₂) = _
  simp

variable (L₁ L₂ W₁ W₂) [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities]

/-- **The one-variable descent along a product localization, curried, is the two-variable
descent.**  Both sides agree at every pair in the image of the two localizations, and
`CategoryTheory.Localization.natTrans₂_ext` promotes that to equality. -/
theorem curry_map_liftNatTrans (F₁ F₂ : C₁ × C₂ ⥤ E) (F₁' F₂' : D₁ × D₂ ⥤ E)
    [Lifting (L₁.prod L₂) (W₁.prod W₂) F₁ F₁'] [Lifting (L₁.prod L₂) (W₁.prod W₂) F₂ F₂']
    (τ : F₁ ⟶ F₂) :
    letI := Lifting₂.curryProd L₁ L₂ W₁ W₂ F₁ F₁'
    letI := Lifting₂.curryProd L₁ L₂ W₁ W₂ F₂ F₂'
    Functor.curry.map (liftNatTrans (L₁.prod L₂) (W₁.prod W₂) F₁ F₂ F₁' F₂' τ) =
      lift₂NatTrans L₁ L₂ W₁ W₂ (Functor.curry.obj F₁) (Functor.curry.obj F₂)
        (Functor.curry.obj F₁') (Functor.curry.obj F₂') (Functor.curry.map τ) := by
  let _ := Lifting₂.curryProd L₁ L₂ W₁ W₂ F₁ F₁'
  let _ := Lifting₂.curryProd L₁ L₂ W₁ W₂ F₂ F₂'
  refine natTrans₂_ext L₁ L₂ W₁ W₂ fun X₁ X₂ => ?_
  rw [lift₂NatTrans_app_app, Lifting₂.curryProd_iso_hom_app_app,
    Lifting₂.curryProd_iso_inv_app_app]
  exact liftNatTrans_app (L₁.prod L₂) (W₁.prod W₂) F₁ F₂ F₁' F₂' τ (X₁, X₂)

end CurryProd

/-! ### The component of a two-variable descent is a one-variable descent -/

section Components

variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities]
  (F₁ F₂ : C₁ ⥤ C₂ ⥤ E) (F₁' F₂' : D₁ ⥤ D₂ ⥤ E)
  [Lifting₂ L₁ L₂ W₁ W₂ F₁ F₁'] [Lifting₂ L₁ L₂ W₁ W₂ F₂ F₂'] (τ : F₁ ⟶ F₂)

/-- **At an object in the image of the first localization, the component of a two-variable
descent is the one-variable descent of the corresponding component.** Both sides agree at every
object in the image of the second localization, which determines a transformation of functors on
`D₂`. -/
theorem lift₂NatTrans_app_eq_liftNatTrans (X₁ : C₁) :
    letI := Lifting₂.fst L₁ L₂ W₁ W₂ F₁ F₁' X₁
    letI := Lifting₂.fst L₁ L₂ W₁ W₂ F₂ F₂' X₁
    (lift₂NatTrans L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' τ).app (L₁.obj X₁) =
      liftNatTrans L₂ W₂ (F₁.obj X₁) (F₂.obj X₁) (F₁'.obj (L₁.obj X₁)) (F₂'.obj (L₁.obj X₁))
        (τ.app X₁) := by
  refine natTrans_ext L₂ W₂ fun X₂ => ?_
  rw [liftNatTrans_app, lift₂NatTrans_app_app]
  rfl

/-- **At an object in the image of the second localization, the flipped component of a
two-variable descent is the one-variable descent along the first localization of the
corresponding flipped component.** -/
theorem lift₂NatTrans_flipApp_eq_liftNatTrans (X₂ : C₂) :
    letI := Lifting₂.snd L₁ L₂ W₁ W₂ F₁ F₁' X₂
    letI := Lifting₂.snd L₁ L₂ W₁ W₂ F₂ F₂' X₂
    (lift₂NatTrans L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' τ).flipApp (L₂.obj X₂) =
      liftNatTrans L₁ W₁ (F₁.flip.obj X₂) (F₂.flip.obj X₂) (F₁'.flip.obj (L₂.obj X₂))
        (F₂'.flip.obj (L₂.obj X₂)) (τ.flipApp X₂) := by
  refine natTrans_ext L₁ W₁ fun X₁ => ?_
  rw [liftNatTrans_app]
  exact lift₂NatTrans_app_app L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' τ X₁ X₂

end Components

/-! ### Spreading a componentwise shift compatibility over the whole localization -/

section EssSurj

variable {M : Type*} [AddMonoid M] [HasShift D₂ M] [HasShift E M]
  (L₁ : C₁ ⥤ D₁) (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁]
  (F₁' F₂' : D₁ ⥤ D₂ ⥤ E) [∀ Y₁ : D₁, (F₁'.obj Y₁).CommShift M]
  [∀ Y₁ : D₁, (F₂'.obj Y₁).CommShift M]
  [∀ {Y₁ Z₁ : D₁} (g : Y₁ ⟶ Z₁), NatTrans.CommShift (F₁'.map g) M]
  [∀ {Y₁ Z₁ : D₁} (g : Y₁ ⟶ Z₁), NatTrans.CommShift (F₂'.map g) M]

include W₁ in
/-- **A transformation of bifunctors whose components over the image of a localization functor
commute with the shift has all its components commute with the shift.** A localization functor is
essentially surjective, and the component at an isomorphic object is conjugate to the given one by
the images of that isomorphism under the two bifunctors, which commute with the shift because the
bifunctors do. -/
theorem commShift_app_of_isLocalization (σ : F₁' ⟶ F₂')
    (hσ : ∀ X₁ : C₁, NatTrans.CommShift (σ.app (L₁.obj X₁)) M) (Y₁ : D₁) :
    NatTrans.CommShift (σ.app Y₁) M := by
  have := Localization.essSurj L₁ W₁
  let e := L₁.objObjPreimageIso Y₁
  let _ := hσ (L₁.objPreimage Y₁)
  have hdec : F₁'.map e.inv ≫ σ.app (L₁.obj (L₁.objPreimage Y₁)) ≫ F₂'.map e.hom =
      σ.app Y₁ := by
    rw [← Category.assoc, σ.naturality e.inv, Category.assoc, ← Functor.map_comp]
    simp
  rw [← hdec]
  infer_instance

end EssSurj

/-! ### The two-variable descent commutes with the shifts -/

section CommShift

variable {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D₁ M]
  [HasShift D₂ M] [HasShift E M]
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities] [L₁.CommShift M] [L₂.CommShift M]
  (F₁ F₂ : C₁ ⥤ C₂ ⥤ E) (F₁' F₂' : D₁ ⥤ D₂ ⥤ E)
  [Lifting₂ L₁ L₂ W₁ W₂ F₁ F₁'] [Lifting₂ L₁ L₂ W₁ W₂ F₂ F₂']
  {h : CommShift₂Setup E M}
  [F₁.CommShift₂ h] [F₂.CommShift₂ h] [F₁'.CommShift₂ h] [F₂'.CommShift₂ h]
  (τ : F₁ ⟶ F₂) [NatTrans.CommShift₂ τ h]

omit [L₁.CommShift M] in
/-- **The two-variable descent commutes with the shift in the second variable.** At an object in
the image of `L₁` this is `lift₂NatTrans_app_eq_liftNatTrans` followed by the one-variable
`CategoryTheory.Localization.liftNatTrans_commShift` along `L₂`, and it spreads to every object
of `D₁` by `commShift_app_of_isLocalization`.

The hypotheses `hι₁`, `hι₂` are the shift compatibility of the two lifting isomorphisms in the
first variable, which is what the one-variable lemma consumes. -/
theorem lift₂NatTrans_commShift_app
    (hι₁ : ∀ X₁ : C₁, letI := Lifting₂.fst L₁ L₂ W₁ W₂ F₁ F₁' X₁
      NatTrans.CommShift (Lifting.iso L₂ W₂ (F₁.obj X₁) (F₁'.obj (L₁.obj X₁))).hom M)
    (hι₂ : ∀ X₁ : C₁, letI := Lifting₂.fst L₁ L₂ W₁ W₂ F₂ F₂' X₁
      NatTrans.CommShift (Lifting.iso L₂ W₂ (F₂.obj X₁) (F₂'.obj (L₁.obj X₁))).hom M)
    (Y₁ : D₁) :
    NatTrans.CommShift ((lift₂NatTrans L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' τ).app Y₁) M := by
  refine commShift_app_of_isLocalization L₁ W₁ F₁' F₂' _ (fun X₁ => ?_) Y₁
  let _ := Lifting₂.fst L₁ L₂ W₁ W₂ F₁ F₁' X₁
  let _ := Lifting₂.fst L₁ L₂ W₁ W₂ F₂ F₂' X₁
  let _ := hι₁ X₁
  let _ := hι₂ X₁
  rw [lift₂NatTrans_app_eq_liftNatTrans L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' τ X₁]
  exact liftNatTrans_commShift L₂ W₂ _ _ _ _ (τ.app X₁)

omit [L₂.CommShift M] in
/-- **The two-variable descent commutes with the shift in the first variable.** The mirror image
of `lift₂NatTrans_commShift_app`, through `lift₂NatTrans_flipApp_eq_liftNatTrans` and the
one-variable lemma along `L₁`. -/
theorem lift₂NatTrans_commShift_flipApp
    (hι₁ : ∀ X₂ : C₂, letI := Lifting₂.snd L₁ L₂ W₁ W₂ F₁ F₁' X₂
      NatTrans.CommShift
        (Lifting.iso L₁ W₁ (F₁.flip.obj X₂) (F₁'.flip.obj (L₂.obj X₂))).hom M)
    (hι₂ : ∀ X₂ : C₂, letI := Lifting₂.snd L₁ L₂ W₁ W₂ F₂ F₂' X₂
      NatTrans.CommShift
        (Lifting.iso L₁ W₁ (F₂.flip.obj X₂) (F₂'.flip.obj (L₂.obj X₂))).hom M)
    (Y₂ : D₂) :
    NatTrans.CommShift ((lift₂NatTrans L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' τ).flipApp Y₂) M := by
  refine commShift_app_of_isLocalization L₂ W₂ F₁'.flip F₂'.flip _ (fun X₂ => ?_) Y₂
  let _ := Lifting₂.snd L₁ L₂ W₁ W₂ F₁ F₁' X₂
  let _ := Lifting₂.snd L₁ L₂ W₁ W₂ F₂ F₂' X₂
  let _ := hι₁ X₂
  let _ := hι₂ X₂
  change NatTrans.CommShift
    ((lift₂NatTrans L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' τ).flipApp (L₂.obj X₂)) M
  rw [lift₂NatTrans_flipApp_eq_liftNatTrans L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' τ X₂]
  exact liftNatTrans_commShift L₁ W₁ _ _ _ _ (τ.flipApp X₂)

/-- **A transformation of bifunctors lifted through two localization functors commutes with the
shifts in both variables as soon as the transformation it is lifted from does.** This is the
two-variable analogue of `CategoryTheory.Localization.liftNatTrans_commShift`. -/
theorem lift₂NatTrans_commShift₂
    (hι₁ : ∀ X₁ : C₁, letI := Lifting₂.fst L₁ L₂ W₁ W₂ F₁ F₁' X₁
      NatTrans.CommShift (Lifting.iso L₂ W₂ (F₁.obj X₁) (F₁'.obj (L₁.obj X₁))).hom M)
    (hι₂ : ∀ X₁ : C₁, letI := Lifting₂.fst L₁ L₂ W₁ W₂ F₂ F₂' X₁
      NatTrans.CommShift (Lifting.iso L₂ W₂ (F₂.obj X₁) (F₂'.obj (L₁.obj X₁))).hom M)
    (hκ₁ : ∀ X₂ : C₂, letI := Lifting₂.snd L₁ L₂ W₁ W₂ F₁ F₁' X₂
      NatTrans.CommShift
        (Lifting.iso L₁ W₁ (F₁.flip.obj X₂) (F₁'.flip.obj (L₂.obj X₂))).hom M)
    (hκ₂ : ∀ X₂ : C₂, letI := Lifting₂.snd L₁ L₂ W₁ W₂ F₂ F₂' X₂
      NatTrans.CommShift
        (Lifting.iso L₁ W₁ (F₂.flip.obj X₂) (F₂'.flip.obj (L₂.obj X₂))).hom M) :
    NatTrans.CommShift₂ (lift₂NatTrans L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' τ) h where
  commShift_app Y₁ :=
    lift₂NatTrans_commShift_app L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' τ hι₁ hι₂ Y₁
  commShift_flipApp Y₂ :=
    lift₂NatTrans_commShift_flipApp L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' τ hκ₁ hκ₂ Y₂

end CommShift

/-! ### The isomorphism version -/

section Iso

variable {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D₁ M]
  [HasShift D₂ M] [HasShift E M]
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities] [L₁.CommShift M] [L₂.CommShift M]
  (F₁ F₂ : C₁ ⥤ C₂ ⥤ E) (F₁' F₂' : D₁ ⥤ D₂ ⥤ E)
  [Lifting₂ L₁ L₂ W₁ W₂ F₁ F₁'] [Lifting₂ L₁ L₂ W₁ W₂ F₂ F₂']
  {h : CommShift₂Setup E M}
  [F₁.CommShift₂ h] [F₂.CommShift₂ h] [F₁'.CommShift₂ h] [F₂'.CommShift₂ h]

/-- **An isomorphism of bifunctors lifted through two localization functors commutes with the
shifts in both variables as soon as the isomorphism it is lifted from does.** This is the form a
comparison isomorphism of bifunctors built by `CategoryTheory.Localization.lift₂NatIso` is
consumed in: the lifted isomorphism carries no compatibility with the shifts by construction, and
this supplies it. -/
theorem lift₂NatIso_hom_commShift₂ (e : F₁ ≅ F₂) [NatTrans.CommShift₂ e.hom h]
    (hι₁ : ∀ X₁ : C₁, letI := Lifting₂.fst L₁ L₂ W₁ W₂ F₁ F₁' X₁
      NatTrans.CommShift (Lifting.iso L₂ W₂ (F₁.obj X₁) (F₁'.obj (L₁.obj X₁))).hom M)
    (hι₂ : ∀ X₁ : C₁, letI := Lifting₂.fst L₁ L₂ W₁ W₂ F₂ F₂' X₁
      NatTrans.CommShift (Lifting.iso L₂ W₂ (F₂.obj X₁) (F₂'.obj (L₁.obj X₁))).hom M)
    (hκ₁ : ∀ X₂ : C₂, letI := Lifting₂.snd L₁ L₂ W₁ W₂ F₁ F₁' X₂
      NatTrans.CommShift
        (Lifting.iso L₁ W₁ (F₁.flip.obj X₂) (F₁'.flip.obj (L₂.obj X₂))).hom M)
    (hκ₂ : ∀ X₂ : C₂, letI := Lifting₂.snd L₁ L₂ W₁ W₂ F₂ F₂' X₂
      NatTrans.CommShift
        (Lifting.iso L₁ W₁ (F₂.flip.obj X₂) (F₂'.flip.obj (L₂.obj X₂))).hom M) :
    NatTrans.CommShift₂ (lift₂NatIso L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' e).hom h :=
  lift₂NatTrans_commShift₂ L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' e.hom hι₁ hι₂ hκ₁ hκ₂

end Iso

end CategoryTheory.Localization

end
