module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackCategory
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPinnedMorphisms
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStack
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackProjection
public import StacksFrontier.AlgebraicGeometry.Quot.QuotToCoherentStack

/-!
# The 1-morphism `Quot_{F/X/B} ⟶ Coh_{X/B}` (Stacks 0DP6)

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation and let `F` be a
quasi-coherent `𝒪_X`-module.  Remark 0DP6 of the Stacks project recalls the morphism

`Quot_{F/X/B} ⟶ Coh_{X/B}`

which sends an element `F_T ⟶ 𝒬` of `Quot_{F/X/B}(T)` to the object `𝒬` of `Coh_{X/B}` over `T`.
Regarding the Quot functor as a category fibred in sets over the big fppf site — its category of
elements — this is a functor over the site.  Its object part is
`AlgebraicGeometry.Space.QuotSituation.cohObject`, and a morphism `h : T' ⟶ T` of test schemes
along which a quotient pulls back to a second one goes to the morphism of `Coh_{X/B}` whose base
map is `h` and whose module comparison identifies the inverse image `(X_h)^*𝒬` with the pulled
back quotient.

This file proves that the two assignments form a functor, so that the morphism of the source is a
1-morphism of categories over the big fppf site.  The two functor laws are the unit and the
associativity coherence of the comparisons of inverse images of Stacks 03LU: a morphism of
`Coh_{X/B}` into the object attached to a quotient `F_T/K` is determined by its base map and by
its module comparison read against the projection of `F_T` onto `F_T/K`, an epimorphism, and the
identities and composites of `Coh_{X/B}` read in this way are the coherences of Stacks 03LU
(`StacksFrontier/AlgebraicGeometry/Quot/CoherentStackPinnedMorphisms.lean`).

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.cohHomOfEq`: the morphism of `Coh_{X/B}` attached to a
  morphism of test schemes along which one quotient pulls back to another.
* `AlgebraicGeometry.Space.QuotSituation.quotBasedCategory`: the category fibred in sets attached
  to `Quot_{F/X/B}`, as a category over the big fppf site.
* `AlgebraicGeometry.Space.QuotSituation.quotToCoherent`: **Stacks 0DP6**, the 1-morphism
  `Quot_{F/X/B} ⟶ Coh_{X/B}` of categories over the big fppf site.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.isPinned_cohFibreOfEq`: the module comparison of the
  morphism attached to a morphism of test schemes is pinned by the projections onto the
  quotients.
* `AlgebraicGeometry.Space.QuotSituation.cohHomOfEq_id` and
  `AlgebraicGeometry.Space.QuotSituation.cohHomOfEq_comp`: the unit and composition laws, at the
  level of the morphisms of `Coh_{X/B}`.
* `AlgebraicGeometry.Space.QuotSituation.quotToCoherent_obj` and
  `AlgebraicGeometry.Space.QuotSituation.quotToCoherent_map`: the 1-morphism sends a quotient to
  the object of `Coh_{X/B}` attached to it, and a morphism of test schemes to the morphism of
  `Coh_{X/B}` attached to it.

## Implementation notes

The object of `Coh_{X/B}` attached to a quotient is used in the written-out form
`AlgebraicGeometry.Space.QuotSituation.quotientCoherentObject`, an abbreviation equal to
`AlgebraicGeometry.Space.QuotSituation.cohObject`, so that its test scheme and its module are read
off without unfolding a definition; the identifications of the two functor laws are otherwise
found by the elaborator only after unfolding the categories of modules.

The category fibred in sets attached to the Quot functor is Mathlib's category of elements of
`AlgebraicGeometry.Space.QuotSituation.quotFunctor`, with its morphisms reversed so that it lies
over the test schemes rather than their opposite, and with its hom-sets raised to the universe of
the hom-sets of `Coh_{X/B}` by `CategoryTheory.ULiftHom`, as for the category `𝒮_B` of
`AlgebraicGeometry.Space.baseBasedCategory`.

## References

* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-! ### The morphism of `Coh_{X/B}` attached to a morphism of test schemes -/

/-- **The object of `Coh_{X/B}` attached to a member of `Quot_{F/X/B}(T)`**, written out: the test
scheme `T` with the quotient `F_T/K`.  It is `AlgebraicGeometry.Space.QuotSituation.cohObject`, by
`AlgebraicGeometry.Space.QuotSituation.quotientCoherentObject_eq`; it is an abbreviation, so that
its test scheme and its module are read off without unfolding a definition. -/
abbrev quotientCoherentObject {T : SchemesOver D.Y} (K : Subobject (D.baseChangeModule T))
    (hK : K ∈ D.properlySupportedQuotients T) : CoherentObject D.toCoherentSituation where
  T := T
  F := D.quotientModule T K
  quasicoherent := hK.1.1.1
  finitePresentation := hK.1.2
  flat := hK.1.1.2
  properSupport := ⟨D.isLocallyOfFiniteType_projection T, hK.2.1, hK.2.2⟩

/-- The written-out object attached to a quotient is the one of
`AlgebraicGeometry.Space.QuotSituation.cohObject`. -/
theorem quotientCoherentObject_eq {T : SchemesOver D.Y} (K : Subobject (D.baseChangeModule T))
    (hK : K ∈ D.properlySupportedQuotients T) :
    D.quotientCoherentObject K hK = D.cohObject T K hK :=
  rfl

/-- The module comparison of the morphism of `Coh_{X/B}` attached to a morphism `h : T' ⟶ T` of
test schemes pulling the member `K` of `Quot_{F/X/B}(T)` back to `K'`: the identification of the
inverse image of `F_T/K` along `X_h` with `F_{T'}/K'`. -/
def cohFibreOfEq {T' T : SchemesOver D.Y} (h : T' ⟶ T) {K : Subobject (D.baseChangeModule T)}
    {K' : Subobject (D.baseChangeModule T')} (e : D.quotientPullback h K = K') :
    (modulePullback B S hS (D.toCoherentSituation.relativeMap h)).obj (D.quotientModule T K) ⟶
      D.quotientModule T' K' :=
  (D.quotientPullbackCokernelIso h K).inv ≫ eqToHom (congrArg (D.quotientModule T') e)

/-- The module comparison `AlgebraicGeometry.Space.QuotSituation.cohFibreOfEq` is an
isomorphism. -/
instance isIso_cohFibreOfEq {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {K : Subobject (D.baseChangeModule T)} {K' : Subobject (D.baseChangeModule T')}
    (e : D.quotientPullback h K = K') : IsIso (D.cohFibreOfEq h e) := by
  subst e
  exact inferInstanceAs (IsIso ((D.quotientPullbackCokernelIso h K).inv ≫ 𝟙 _))

/-- **The morphism of `Coh_{X/B}` attached to a morphism of test schemes.**  If a morphism
`h : T' ⟶ T` of test schemes pulls the member `K` of `Quot_{F/X/B}(T)` back to the member `K'`
of `Quot_{F/X/B}(T')`, there is a morphism of `Coh_{X/B}` from the object attached to `K'` to the
object attached to `K`: its base map is `h`, and its module comparison identifies the inverse
image of `F_T/K` with `F_{T'}/K'`. -/
def cohHomOfEq {T' T : SchemesOver D.Y} (h : T' ⟶ T) {K : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.properlySupportedQuotients T) {K' : Subobject (D.baseChangeModule T')}
    (hK' : K' ∈ D.properlySupportedQuotients T') (e : D.quotientPullback h K = K') :
    CoherentHom (D.quotientCoherentObject K' hK') (D.quotientCoherentObject K hK) where
  base := h
  fibre := D.cohFibreOfEq h e
  isIso_fibre := D.isIso_cohFibreOfEq h e

/-- The base map of the morphism attached to a morphism of test schemes is that morphism. -/
@[simp]
theorem cohHomOfEq_base {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {K : Subobject (D.baseChangeModule T)} (hK : K ∈ D.properlySupportedQuotients T)
    {K' : Subobject (D.baseChangeModule T')} (hK' : K' ∈ D.properlySupportedQuotients T')
    (e : D.quotientPullback h K = K') : (D.cohHomOfEq h hK hK' e).base = h :=
  rfl

/-- The projection `F_T ⟶ F_T/K` onto the quotient of a member `K` of `Quot_{F/X/B}(T)`, as a
presentation of the module of the object of `Coh_{X/B}` attached to it. -/
def presentation (T : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)) :
    (modulePullback B S hS (baseChangeProjection D.toCoherentSituation.f T)).obj D.F ⟶
      D.quotientModule T K :=
  D.quotientProjection T K

/-- The presentation of the module of the object attached to a quotient is an epimorphism. -/
theorem epi_presentation (T : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)) :
    Epi (D.presentation T K) :=
  QuotientSituation.epi_quotientProjection D.toQuotientSituation T K

/-- **The module comparison is pinned by the two projections onto the quotients.**  It carries
the projection of `F_{T'}` onto `(X_h)^*(F_T/K)` to the projection of `F_{T'}` onto
`F_{T'}/K'`. -/
theorem isPinned_cohFibreOfEq {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {K : Subobject (D.baseChangeModule T)} {K' : Subobject (D.baseChangeModule T')}
    (e : D.quotientPullback h K = K') :
    Functor.IsPinned (D.toCoherentSituation.presentationComparison h) (D.cohFibreOfEq h e)
      (D.presentation T K) (D.presentation T' K') := by
  have key : Functor.IsPinned (D.baseChangeComparison h)
      ((D.quotientPullbackCokernelIso h K).inv ≫ eqToHom (congrArg (D.quotientModule T') e))
      (D.quotientProjection T K) (D.quotientProjection T' K') := by
    subst e
    show D.quotientPullbackProjection h K ≫ ((D.quotientPullbackCokernelIso h K).inv ≫ 𝟙 _) = _
    rw [Category.comp_id]
    exact (Iso.comp_inv_eq (D.quotientPullbackCokernelIso h K)).2
      (D.quotientProjection_comp_quotientPullbackCokernelIso_hom h K).symm
  exact key

/-! ### The functor laws -/

/-- A morphism of `Coh_{X/B}` with base map `h` whose module comparison is pinned by the
projections agrees with the one attached to `h`. -/
private theorem cohHomOfEq_eq_mk {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {K : Subobject (D.baseChangeModule T)} (hK : K ∈ D.properlySupportedQuotients T)
    {K' : Subobject (D.baseChangeModule T')} (hK' : K' ∈ D.properlySupportedQuotients T')
    (e : D.quotientPullback h K = K') {φ : (modulePullback B S hS
      (D.toCoherentSituation.relativeMap h)).obj (D.quotientModule T K) ⟶ D.quotientModule T' K'}
    (hφ : IsIso φ) (hpin : Functor.IsPinned (D.toCoherentSituation.presentationComparison h) φ
      (D.presentation T K) (D.presentation T' K')) :
    D.cohHomOfEq h hK hK' e =
      (CoherentHom.mk h φ hφ : CoherentHom (D.quotientCoherentObject K' hK')
        (D.quotientCoherentObject K hK)) :=
  CoherentSituation.mk_eq_mk_of_isPinned (D := D.toCoherentSituation) D.F
    (A' := D.quotientCoherentObject K' hK') (A := D.quotientCoherentObject K hK) h
    (D.isIso_cohFibreOfEq h e) hφ (D.epi_presentation T K) (D.isPinned_cohFibreOfEq h e) hpin

/-- **The unit law.**  The morphism of `Coh_{X/B}` attached to the identity of a test scheme is
the identity of the object attached to the quotient. -/
theorem cohHomOfEq_id (T : SchemesOver D.Y) {K : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.properlySupportedQuotients T) (e : D.quotientPullback (𝟙 T) K = K) :
    D.cohHomOfEq (𝟙 T) hK hK e =
      CoherentHom.id (modulePushforwardCoherence B S hS) (D.quotientCoherentObject K hK) := by
  have h3 := D.cohHomOfEq_eq_mk (𝟙 T) hK hK e
    (Iso.isIso_hom ((D.toCoherentSituation.idComparison (modulePushforwardCoherence B S hS)
      (D.quotientCoherentObject K hK).T).app (D.quotientCoherentObject K hK).F))
    (CoherentSituation.isPinned_idComparison (D := D.toCoherentSituation) D.F
      (D.quotientCoherentObject K hK).T (Q := (D.quotientCoherentObject K hK).F)
      (D.presentation T K))
  exact h3.trans (CoherentSituation.coherentHom_id_eq_mk (D.quotientCoherentObject K hK)).symm

/-- **The composition law.**  The composite of the morphisms of `Coh_{X/B}` attached to two
composable morphisms of test schemes is the morphism attached to their composite. -/
theorem cohHomOfEq_comp {T'' T' T : SchemesOver D.Y} (h : T'' ⟶ T') (k : T' ⟶ T)
    {K : Subobject (D.baseChangeModule T)} (hK : K ∈ D.properlySupportedQuotients T)
    {K' : Subobject (D.baseChangeModule T')} (hK' : K' ∈ D.properlySupportedQuotients T')
    {K'' : Subobject (D.baseChangeModule T'')} (hK'' : K'' ∈ D.properlySupportedQuotients T'')
    (e₁ : D.quotientPullback k K = K') (e₂ : D.quotientPullback h K' = K'')
    (e : D.quotientPullback (h ≫ k) K = K'') :
    (D.cohHomOfEq h hK' hK'' e₂).comp (D.cohHomOfEq k hK hK' e₁) =
      D.cohHomOfEq (h ≫ k) hK hK'' e := by
  have hpin := CoherentSituation.isPinned_fibreComp (D := D.toCoherentSituation)
    (D.isPinned_cohFibreOfEq h e₂) (D.isPinned_cohFibreOfEq k e₁)
  have hiso := @Functor.isIso_fibreComp _ _ _ _ _ _ _ _ _
    (D.toCoherentSituation.compComparison h k) _ _ _
    (D.cohFibreOfEq h e₂) (D.cohFibreOfEq k e₁) (D.isIso_cohFibreOfEq h e₂)
    (D.isIso_cohFibreOfEq k e₁)
  exact (CoherentSituation.coherentHom_mk_comp_mk (D := D.toCoherentSituation)
    (A'' := D.quotientCoherentObject K'' hK'') (A' := D.quotientCoherentObject K' hK')
    (A := D.quotientCoherentObject K hK) h k (D.cohFibreOfEq h e₂) (D.isIso_cohFibreOfEq h e₂)
    (D.cohFibreOfEq k e₁) (D.isIso_cohFibreOfEq k e₁) hiso).trans
    (D.cohHomOfEq_eq_mk (h ≫ k) hK hK'' e hiso hpin).symm

/-! ### The category fibred in sets attached to the Quot functor -/

/-- The objects of the category fibred in sets attached to `Quot_{F/X/B}`: the elements of the
Quot functor, that is, the pairs of a test scheme over `B` and a member of `Quot_{F/X/B}(T)`.  The
morphisms are reversed so that they lie over the test schemes, and their hom-sets are raised to
the universe of the hom-sets of `Coh_{X/B}`. -/
abbrev QuotObjects : Type (u + 1) :=
  ULiftHom.{u + 1} (D.quotFunctor.Elements)ᵒᵖ

/-- The test scheme of an element of the Quot functor. -/
abbrev QuotObjects.T {D : QuotSituation B S hS} (x : D.QuotObjects) : SchemesOver D.Y :=
  (ULiftHom.objDown x).unop.1.unop

/-- The kernel of the quotient of an element of the Quot functor. -/
abbrev QuotObjects.K {D : QuotSituation B S hS} (x : D.QuotObjects) :
    Subobject (D.baseChangeModule x.T) :=
  (ULiftHom.objDown x).unop.2.1

/-- The kernel of the quotient of an element of the Quot functor is a member of
`Quot_{F/X/B}(T)`. -/
theorem QuotObjects.mem {D : QuotSituation B S hS} (x : D.QuotObjects) :
    x.K ∈ D.properlySupportedQuotients x.T :=
  (ULiftHom.objDown x).unop.2.2

/-- The morphism of test schemes underlying a morphism of elements of the Quot functor. -/
abbrev QuotObjects.base {D : QuotSituation B S hS} {x y : D.QuotObjects} (m : x ⟶ y) :
    x.T ⟶ y.T :=
  m.down.unop.1.unop

/-- A morphism of elements of the Quot functor pulls the quotient of its target back to the
quotient of its source. -/
theorem QuotObjects.quotientPullback_base {D : QuotSituation B S hS} {x y : D.QuotObjects}
    (m : x ⟶ y) : D.quotientPullback (QuotObjects.base m) y.K = x.K :=
  congrArg Subtype.val m.down.unop.2

/-- **The category fibred in sets attached to `Quot_{F/X/B}`, as a category over the big fppf
site.**  An object is a test scheme `T` over `B` together with a member of `Quot_{F/X/B}(T)`, a
morphism is a morphism of test schemes along which the quotient of the target pulls back to the
quotient of the source, and the projection forgets the quotient and the morphism to `B`. -/
def quotBasedCategory : BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS) where
  obj := D.QuotObjects
  p := ULiftHom.down ⋙ (CategoryOfElements.π D.quotFunctor).leftOp ⋙
    CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y

/-! ### The 1-morphism `Quot_{F/X/B} ⟶ Coh_{X/B}` -/

/-- The functor underlying the 1-morphism `Quot_{F/X/B} ⟶ Coh_{X/B}`. -/
def quotToCoherentFunctor :
    letI : Category.{u + 1} (CoherentObject D.toCoherentSituation) :=
      D.toCoherentSituation.categoryData.category
    D.QuotObjects ⥤ CoherentObject D.toCoherentSituation :=
  letI : Category.{u + 1} (CoherentObject D.toCoherentSituation) :=
    D.toCoherentSituation.categoryData.category
  { obj := fun x => D.cohObject x.T x.K x.mem
    map := fun {x y} m => D.cohHomOfEq (QuotObjects.base m) y.mem x.mem
      (QuotObjects.quotientPullback_base m)
    map_id := fun x => D.cohHomOfEq_id x.T x.mem _
    map_comp := fun {x y z} m n => (D.cohHomOfEq_comp (QuotObjects.base m)
      (QuotObjects.base n) z.mem y.mem x.mem _ _ _).symm }

/-- **Stacks 0DP6, the morphism `Quot_{F/X/B} ⟶ Coh_{X/B}`.**  The rule sending an element
`F_T ⟶ 𝒬` of `Quot_{F/X/B}(T)` to the object `𝒬` of `Coh_{X/B}` over `T`, and a morphism of test
schemes along which one quotient pulls back to another to the morphism of `Coh_{X/B}` with that
base map identifying the inverse image of the one quotient with the other, is a 1-morphism of
categories over the big fppf site: it respects identities and composition, by the coherences of
the comparisons of inverse images of Stacks 03LU, and it does not change the underlying test
scheme. -/
@[stacks 0DP6 "the morphism Quot_{F/X/B} ⟶ Coh_{X/B} sending F_T ⟶ Q to the object Q over T, as \
a 1-morphism of categories over the big fppf site (functor laws included)"]
def quotToCoherent :
    D.quotBasedCategory ⥤ᵇ coherentBasedCategory D.toCoherentSituation.categoryData where
  toFunctor := D.quotToCoherentFunctor
  w := rfl

/-- The 1-morphism `Quot_{F/X/B} ⟶ Coh_{X/B}` sends an element of the Quot functor to the object
of `Coh_{X/B}` attached to its quotient. -/
theorem quotToCoherent_obj (x : D.QuotObjects) :
    D.quotToCoherent.obj x = D.cohObject x.T x.K x.mem :=
  rfl

/-- The 1-morphism `Quot_{F/X/B} ⟶ Coh_{X/B}` sends a morphism of elements of the Quot functor
to the morphism of `Coh_{X/B}` attached to its underlying morphism of test schemes. -/
theorem quotToCoherent_map {x y : D.QuotObjects} (m : x ⟶ y) :
    D.quotToCoherent.map m =
      D.cohHomOfEq (QuotObjects.base m) y.mem x.mem (QuotObjects.quotientPullback_base m) :=
  rfl

end QuotSituation

end AlgebraicGeometry.Space

end
