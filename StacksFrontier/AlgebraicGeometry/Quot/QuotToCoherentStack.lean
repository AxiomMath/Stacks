module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStack
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctor
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPresheaf
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorPullback

/-!
# The morphism `Quot_{F/X/B} ⟶ Coh_{X/B}` (Stacks 0DP6)

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
of finite presentation and let `F` be a quasi-coherent `𝒪_X`-module — the standing data
`AlgebraicGeometry.Space.QuotSituation` of Stacks 09TR.  The same morphism is the standing data
`AlgebraicGeometry.Space.CoherentSituation` of Stacks 08KB, over which the category `Coh_{X/B}`
of quasi-coherent `𝒪_{X_T}`-modules of finite presentation, flat over `T` and with support
proper over `T`, is formed.

Stacks 0DP6 records that there is a morphism

`Quot_{F/X/B} ⟶ Coh_{X/B}`

sending a `T`-point `F_T ⟶ 𝒬` of the Quot functor to the object `𝒬` of `Coh_{X/B}` over `T`,
and then forms `Quot^P_{F/X/B}` as the fibre product `Quot_{F/X/B} ×_{Coh_{X/B}} Coh^P_{X/B}`.
This file constructs the morphism, on objects and on morphisms: a quotient of `F_T` lying in
`Quot_{F/X/B}(T)` satisfies, by the very definition of that set, each of the four conditions an
object of `Coh_{X/B}` over `T` is required to satisfy, and the inverse image of a quotient along
a morphism `h : T' ⟶ T` of test schemes is, by
`AlgebraicGeometry.Space.QuotientSituation.quotientPullbackCokernelIso`, isomorphic to the
inverse image of the quotient — which is exactly the module comparison a morphism of `Coh_{X/B}`
consists of.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.toCoherentSituation`: the standing data of Stacks 08KB
  underlying the standing data of Stacks 09TR — the same finitely presented morphism of
  algebraic spaces, which is all either situation records besides the module `F`.
* `AlgebraicGeometry.Space.QuotSituation.cohObject`: **Stacks 0DP6**, the object part of the
  morphism: the object `(T, 𝒬)` of `Coh_{X/B}` attached to a member of `Quot_{F/X/B}(T)`.
* `AlgebraicGeometry.Space.QuotSituation.cohHom`: **Stacks 0DP6**, the part of the morphism
  acting on morphisms of test schemes.
* `CategoryTheory.Functor.conjSubobjectCokernelIso_id` and
  `CategoryTheory.Functor.conjSubobjectCokernelIso_comp`: the unit and composition laws for
  `CategoryTheory.Functor.conjSubobjectCokernelIso`, the comparison of a conjugated quotient
  with the image of the quotient.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.isProperlySupportedOver_quotientPullback`: the
  proper-support half, Stacks 0CZJ, of the statement that the inverse image of a member of
  `Quot_{F/X/B}(T)` is a member of `Quot_{F/X/B}(T')` -- which is what makes the source of
  `cohHom` an object attached by `cohObject` at all.  The whole four-condition statement is
  `AlgebraicGeometry.Space.QuotSituation.quotientPullback_mem_properlySupportedQuotients` in
  `StacksFrontier/AlgebraicGeometry/Quot/QuotFunctorPresheaf.lean`; the other three conditions are
  the preservation theorems of
  `StacksFrontier/AlgebraicGeometry/Quot/QuotientFunctorPullback.lean`.
* `AlgebraicGeometry.Space.QuotSituation.cohObject_T` and
  `AlgebraicGeometry.Space.QuotSituation.cohObject_F`: the object attached to a quotient has
  the given test scheme as its test scheme and the quotient `F_T/K` as its module.  This is the
  rule "`F_T ⟶ 𝒬` goes to `𝒬` over `T`" of the source.
* `AlgebraicGeometry.Space.QuotSituation.cohHom_base` and
  `AlgebraicGeometry.Space.QuotSituation.cohHom_fibre`: the morphism attached to `h : T' ⟶ T`
  has `h` as its base map — so the morphism of this file lies over the identity of the schemes
  over `B` — and the comparison of the two base changes as its module comparison.
* `AlgebraicGeometry.Space.QuotSituation.quotientPullbackProjection_comp_cohHom_fibre`: the
  module comparison carries the projection of `F_{T'}` onto the inverse image of `F_T/K` to the
  projection of `F_{T'}` onto its quotient by the pulled-back kernel.  Since the former is an
  epimorphism this *pins* the module comparison: it is the unique morphism of its type with
  that property, so `cohHom` is not an unconstrained choice.
* `AlgebraicGeometry.Space.QuotSituation.cohObject_congr`: the object attached to a quotient
  depends only on the kernel, not on the proof that it lies in `Quot_{F/X/B}(T)`.
* `AlgebraicGeometry.Space.QuotSituation.cohObject_quotientPullback_id` and
  `AlgebraicGeometry.Space.QuotSituation.cohObject_quotientPullback_comp`: **the functoriality
  of the object part of the morphism** — the object attached to the inverse image of a quotient
  along an identity is the object attached to the quotient, and the object attached to the
  inverse image along a composite is the one attached to the iterated inverse image.  These are
  `AlgebraicGeometry.Space.QuotientSituation.quotientPullback_id` and
  `AlgebraicGeometry.Space.QuotientSituation.quotientPullback_comp`, hence the
  pseudofunctoriality of the inverse images of Stacks 03LU, supplied by
  `AlgebraicGeometry.Space.modulePushforwardCoherence`.

## Scope

Stacks 0DP6 has two assertions: the morphism `Quot_{F/X/B} ⟶ Coh_{X/B}`, and the fibre product
`Quot^P_{F/X/B} = Quot_{F/X/B} ×_{Coh_{X/B}} Coh^P_{X/B}`. This file treats the first.

Its object part and its action on morphisms of test schemes are constructed here.  The functor
laws hold for the *object* part — that is `cohObject_quotientPullback_id` and
`cohObject_quotientPullback_comp` below — and the morphism part is shown to lie over the
identity of the schemes over `B`, by `cohHom_base`.  The functor laws for the module
comparisons are `AlgebraicGeometry.Space.QuotSituation.quotientPullbackCokernelIso_hom_id` and
`AlgebraicGeometry.Space.QuotSituation.quotientPullbackCokernelIso_hom_comp` in
`StacksFrontier/AlgebraicGeometry/Quot/QuotToCoherentStackFunctorLaws.lean`.  The category
structure on `Coh_{X/B}`, whose composition is associative and unital exactly because the inverse
images of Stacks 03LU are pseudofunctorial, is
`AlgebraicGeometry.Space.CoherentSituation.categoryData`.
`CategoryTheory.Functor.conjSubobjectCokernelIso_id` and
`CategoryTheory.Functor.conjSubobjectCokernelIso_comp` below are the two laws for an arbitrary
comparison of inverse images.

The preservation statements under inverse image used by
`AlgebraicGeometry.Space.QuotSituation.cohHom` are these: preservation of finite
presentation (Properties of Spaces, Section 05VR, through Stacks 03DO) is
`AlgebraicGeometry.Space.QuotientSituation.pullbackPreservesFinitePresentation`, flatness over
the base (Stacks 05VW) is
`AlgebraicGeometry.Space.QuotientSituation.pullbackPreservesFlatOver`, and quasi-coherence
(Stacks 03GA) holds at an arbitrary morphism of algebraic spaces by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`.

## Implementation notes

The object part takes the kernel and the proof of membership in `Quot_{F/X/B}(T)` as separate
arguments rather than an element of the subtype, so that `cohObject_congr` can be stated and the
object attached to a pulled-back quotient can be named without naming the proof; this is the
shape `AlgebraicGeometry.Space.QuotientSituation.quotientsFunctor` uses as well.

Closedness of the support and the locally-finite-type hypothesis on the projection `X_T ⟶ T`,
both of which `AlgebraicGeometry.Space.CoherentObject` existentially quantifies, come from the
proper-support condition of `Quot_{F/X/B}(T)` and from
`AlgebraicGeometry.Space.QuotSituation.isLocallyOfFiniteType_projection`; the latter is proved,
not assumed, which is the reason Stacks 09TR adds finite presentation of `f` to the situation of
Stacks 082M.

The module comparison of the morphism is the *inverse* of
`AlgebraicGeometry.Space.QuotientSituation.quotientPullbackCokernelIso`, because
`AlgebraicGeometry.Space.CoherentHom` records a morphism from the inverse image of the module of
the target to the module of the source while that isomorphism goes the other way.

## References

* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- **Transporting the projection onto a quotient along an equality of subobjects.**  The
projection onto the quotient by `K`, followed by the identification of the two quotients that an
equality `K = K'` induces, is the projection onto the quotient by `K'`. -/
theorem Limits.cokernel_π_arrow_eqToHom {C : Type*} [Category* C] [Abelian C] {A : C}
    {K K' : Subobject A} (e : K = K') :
    Limits.cokernel.π K.arrow ≫
        eqToHom (congrArg (fun J : Subobject A => Limits.cokernel J.arrow) e) =
      Limits.cokernel.π K'.arrow := by
  subst e; simp

namespace Functor

variable {C : Type*} {D₀ : Type*} {D₁ : Type*} {D₂ : Type*}
  [Category* C] [Category* D₀] [Category* D₁] [Category* D₂]
  [Abelian D₀] [Abelian D₁] [Abelian D₂]

/-- The comparison of a conjugated quotient is `eqToHom` of an equality of subobjects followed by
`g` as soon as `g` carries the projection onto the quotient by the new subobject to the
projection `conjQuotientProjection`. -/
private theorem conjSubobjectCokernelIso_hom_eq_eqToHom_comp {P : C ⥤ D₁} {P₀ : C ⥤ D₀}
    {L : D₀ ⥤ D₁} [L.PreservesEpimorphisms] (c : P ≅ P₀ ⋙ L) {M : C} (K : Subobject (P₀.obj M))
    {K' : Subobject (P.obj M)} (e : conjSubobject c K = K')
    (g : Limits.cokernel K'.arrow ⟶ L.obj (Limits.cokernel K.arrow))
    (hg : Limits.cokernel.π K'.arrow ≫ g = conjQuotientProjection c K) :
    (conjSubobjectCokernelIso c K).hom =
      eqToHom (congrArg (fun J : Subobject (P.obj M) => Limits.cokernel J.arrow) e) ≫ g := by
  rw [← cancel_epi (Limits.cokernel.π _), cokernel_π_comp_conjSubobjectCokernelIso_hom c K,
    ← Category.assoc, Limits.cokernel_π_arrow_eqToHom e, hg]

/-- **The unit law for the comparison of a conjugated quotient with the image of the
quotient.**  Conjugating by a comparison which is whiskering `P` with an isomorphism `𝟭 ≅ L`
leaves the subobject unchanged, by `CategoryTheory.Functor.conjSubobject_id`; this says that
under that identification of the two quotients the comparison of
`CategoryTheory.Functor.conjSubobjectCokernelIso` is the component of `𝟭 ≅ L`.

Both sides are determined by their composites with the projection onto the quotient by the
conjugated subobject, which is an epimorphism, and those composites agree by the naturality of
`𝟭 ≅ L`. -/
theorem conjSubobjectCokernelIso_id {P : C ⥤ D₁} {L : D₁ ⥤ D₁} [L.PreservesEpimorphisms]
    (γ : 𝟭 D₁ ≅ L) (e : P ≅ P ⋙ L)
    (hfac : e = (rightUnitor P).symm ≪≫ isoWhiskerLeft P γ) {M : C}
    (K : Subobject (P.obj M)) :
    (conjSubobjectCokernelIso e K).hom =
      eqToHom (congrArg (fun J : Subobject (P.obj M) => Limits.cokernel J.arrow)
          (conjSubobject_id γ e hfac K)) ≫
        γ.hom.app (Limits.cokernel K.arrow) := by
  refine conjSubobjectCokernelIso_hom_eq_eqToHom_comp e K (conjSubobject_id γ e hfac K) _ ?_
  subst hfac
  simp only [conjQuotientProjection, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app, rightUnitor_inv_app, Category.id_comp]
  exact γ.hom.naturality (Limits.cokernel.π K.arrow)

/-- **The composition law for the comparison of a conjugated quotient with the image of the
quotient.**  Under the identification of `CategoryTheory.Functor.conjSubobject_comp`, the
comparison for a composite comparison is the comparison for the second factor followed by the
image under `L₂` of the comparison for the first and the identification `L ≅ L₁ ⋙ L₂`.

As for the unit law, both sides are determined by their composites with the projection onto the
quotient by the conjugated subobject, and those composites agree by the characterization of the
two inner comparisons and the naturality of `L ≅ L₁ ⋙ L₂`. -/
theorem conjSubobjectCokernelIso_comp {P₀ : C ⥤ D₀} {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂}
    {L₁ : D₀ ⥤ D₁} {L₂ : D₁ ⥤ D₂} {L : D₀ ⥤ D₂} [L₁.PreservesEpimorphisms]
    [L₂.PreservesEpimorphisms] [L.PreservesEpimorphisms]
    (c₁ : P₁ ≅ P₀ ⋙ L₁) (c₂ : P₂ ≅ P₁ ⋙ L₂) (c : P₂ ≅ P₀ ⋙ L) (τ : L ≅ L₁ ⋙ L₂)
    (hfac : c = (c₂ ≪≫ isoWhiskerRight c₁ L₂ ≪≫ associator P₀ L₁ L₂) ≪≫
      (isoWhiskerLeft P₀ τ).symm)
    {M : C} (K : Subobject (P₀.obj M)) :
    (conjSubobjectCokernelIso c K).hom =
      eqToHom (congrArg (fun J : Subobject (P₂.obj M) => Limits.cokernel J.arrow)
          (conjSubobject_comp c₁ c₂ c τ hfac K)) ≫
        (conjSubobjectCokernelIso c₂ (conjSubobject c₁ K)).hom ≫
          L₂.map (conjSubobjectCokernelIso c₁ K).hom ≫
            τ.inv.app (Limits.cokernel K.arrow) := by
  refine conjSubobjectCokernelIso_hom_eq_eqToHom_comp c K
    (conjSubobject_comp c₁ c₂ c τ hfac K) _ ?_
  rw [← Category.assoc, cokernel_π_comp_conjSubobjectCokernelIso_hom c₂ (conjSubobject c₁ K)]
  subst hfac
  simp only [conjQuotientProjection, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app, isoWhiskerLeft_inv, whiskerLeft_app,
    associator_hom_app, Category.id_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, cokernel_π_comp_conjSubobjectCokernelIso_hom c₁ K]
  simp only [conjQuotientProjection, Functor.map_comp, Category.assoc]
  have hnat := τ.inv.naturality (Limits.cokernel.π K.arrow)
  simp only [Functor.comp_map] at hnat
  rw [hnat]

end Functor

end CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The standing data of Stacks 08KB underlying the standing data of Stacks 09TR.**  A
quotient situation records a finitely presented morphism `f : X ⟶ B` of algebraic spaces
together with a quasi-coherent `𝒪_X`-module; forgetting the module leaves exactly the data over
which `Coh_{X/B}` is formed. -/
def QuotSituation.toCoherentSituation (D : QuotSituation B S hS) : CoherentSituation B S hS where
  X := D.X
  Y := D.Y
  f := D.f
  finitePresentation := D.finitePresentation

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-- **The inverse image of a quotient with support proper over the test scheme again has
support proper over the test scheme**, in the spelling that names the pulled-back kernel.

This is Stacks 0CZJ in the form
`AlgebraicGeometry.Space.QuotSituation.isProperlySupportedOver_modulePullback_quotientModule`,
transported along the identification
`AlgebraicGeometry.Space.QuotientSituation.quotientPullbackCokernelIso` of the quotient by the
pulled-back kernel with the inverse image of the quotient: an isomorphism of modules does not
change the support (Stacks 04KB), and the condition then transports by Stacks 0CZE. -/
theorem isProperlySupportedOver_quotientPullback {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {K : Subobject (D.baseChangeModule T)} (hK : K ∈ D.properlySupportedQuotients T) :
    D.IsProperlySupportedOver T' (D.quotientModule T' (D.quotientPullback h K)) := by
  obtain ⟨hcl, hproper⟩ := D.isProperlySupportedOver_modulePullback_quotientModule h hK
  have heq := supportOfSheaf_eq_of_iso B S hS (D.space T') (D.quotientPullbackCokernelIso h K)
  exact hasProperSupport_of_subset B S hS (D.space T').2 _ (D.projection T').hom
    (D.isLocallyOfFiniteType_projection T') (heq ▸ hcl) heq.subset ⟨hcl, hproper⟩

/-- **Stacks 0DP6, the object part of the morphism `Quot_{F/X/B} ⟶ Coh_{X/B}`.**  A `T`-point
`F_T ⟶ 𝒬` of the Quot functor, recorded by its kernel `K`, goes to the object `(T, F_T/K)` of
`Coh_{X/B}`: the four conditions an object of `Coh_{X/B}` over `T` satisfies — quasi-coherence,
finite presentation, flatness over `T` and proper support over `T` — are the four conditions
cutting `Quot_{F/X/B}(T)` out of the subobjects of `F_T`. -/
@[stacks 0DP6 "the object part of the morphism Quot_{F/X/B} ⟶ Coh_{X/B}: a quotient F_T ⟶ Q in \
Quot_{F/X/B}(T) goes to the object Q of Coh_{X/B} over T. The action on morphisms of test \
schemes is `AlgebraicGeometry.Space.QuotSituation.cohHom`. The functor laws hold for the \
OBJECT part (`cohObject_quotientPullback_id`, `cohObject_quotientPullback_comp`) but are NOT \
established for the module comparisons, Coh_{X/B} not being a category in this development; \
and the fibre product Quot^P = Quot ×_{Coh} Coh^P of the remark is NOT formed: \
Coh^P_{X/B} is not constructed anywhere in this development, only the standing data of \
Situation 0DNC. See the module \
docstring for the full accounting"]
def cohObject (T : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T))
    (hK : K ∈ D.properlySupportedQuotients T) : CoherentObject D.toCoherentSituation where
  T := T
  F := D.quotientModule T K
  quasicoherent := hK.1.1.1
  finitePresentation := hK.1.2
  flat := hK.1.1.2
  properSupport := ⟨D.isLocallyOfFiniteType_projection T, hK.2.1, hK.2.2⟩

/-- **Stacks 0DP6, the action of the morphism `Quot_{F/X/B} ⟶ Coh_{X/B}` on morphisms of test
schemes.**  A morphism `h : T' ⟶ T` of test schemes over `B` and a member `K` of
`Quot_{F/X/B}(T)` give a morphism of `Coh_{X/B}` from the object attached to the inverse image
of `K` to the object attached to `K`: its base map is `h` itself, and its module comparison is
the identification of the inverse image of `F_T/K` with the quotient of `F_{T'}` by the
pulled-back kernel. -/
@[stacks 0DP6 "the action of the morphism Quot_{F/X/B} ⟶ Coh_{X/B} on morphisms of test \
schemes, whose object part is `AlgebraicGeometry.Space.QuotSituation.cohObject`: the base map \
is h itself, so the morphism lies over the identity of the schemes over B, and the module \
comparison is the one of Tag 03LU identifying the inverse image of F_T/K with the quotient of \
F_{T'} by the pulled-back kernel. No hypothesis is carried: the preservation under inverse \
image of finite presentation (Properties of Spaces, Section 05VR) is the theorem \
`AlgebraicGeometry.Space.QuotientSituation.pullbackPreservesFinitePresentation`. \
The functor laws for the module comparisons are NOT established and the fibre product Quot^P \
of the remark is NOT formed; see the module docstring"]
def cohHom {T' T : SchemesOver D.Y}
    (h : T' ⟶ T)
    {K : Subobject (D.baseChangeModule T)} (hK : K ∈ D.properlySupportedQuotients T) :
    CoherentHom
      (D.cohObject T' (D.quotientPullback h K)
        (D.quotientPullback_mem_properlySupportedQuotients h K hK))
      (D.cohObject T K hK) where
  base := h
  fibre := (D.quotientPullbackCokernelIso h K).inv
  isIso_fibre := Iso.isIso_inv _

/-- The test scheme of the object attached to a quotient is the given test scheme. -/
theorem cohObject_T (T : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T))
    (hK : K ∈ D.properlySupportedQuotients T) : (D.cohObject T K hK).T = T := rfl

/-- **The module of the object attached to a quotient is the quotient.**  This is the rule
"`F_T ⟶ 𝒬` goes to `𝒬` over `T`" of Stacks 0DP6. -/
theorem cohObject_F (T : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T))
    (hK : K ∈ D.properlySupportedQuotients T) :
    (D.cohObject T K hK).F = D.quotientModule T K := rfl

/-- **The morphism attached to a morphism of test schemes has that morphism as its base
map.**  So the morphism `Quot_{F/X/B} ⟶ Coh_{X/B}` lies over the identity of the schemes
over `B`. -/
theorem cohHom_base
    {T' T : SchemesOver D.Y} (h : T' ⟶ T) {K : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.properlySupportedQuotients T) :
    (D.cohHom h hK).base = h := rfl

/-- The module comparison of the morphism attached to a morphism of test schemes is the
identification of the inverse image of the quotient with the quotient by the pulled-back
kernel. -/
theorem cohHom_fibre
    {T' T : SchemesOver D.Y} (h : T' ⟶ T) {K : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.properlySupportedQuotients T) :
    (D.cohHom h hK).fibre = (D.quotientPullbackCokernelIso h K).inv := rfl

/-- **The module comparison of the morphism is pinned by the two projections.**  It carries the
projection of `F_{T'}` onto the inverse image of `F_T/K` to the projection of `F_{T'}` onto its
quotient by the pulled-back kernel.  The former projection is an epimorphism, so this property
determines the comparison: the module comparison of
`AlgebraicGeometry.Space.QuotSituation.cohHom` is not an unconstrained morphism of its type. -/
theorem quotientPullbackProjection_comp_cohHom_fibre
    {T' T : SchemesOver D.Y} (h : T' ⟶ T) {K : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.properlySupportedQuotients T) :
    D.quotientPullbackProjection h K ≫ (D.cohHom h hK).fibre =
      D.quotientProjection T' (D.quotientPullback h K) :=
  (Iso.comp_inv_eq (D.quotientPullbackCokernelIso h K)).2
    (D.quotientProjection_comp_quotientPullbackCokernelIso_hom h K).symm

/-- **The object attached to a quotient depends only on the kernel.**  Together with
`AlgebraicGeometry.Space.QuotientSituation.quotientPullback_id` and
`AlgebraicGeometry.Space.QuotientSituation.quotientPullback_comp` this is the functoriality of
the object part of the morphism `Quot_{F/X/B} ⟶ Coh_{X/B}`. -/
theorem cohObject_congr {T : SchemesOver D.Y} {K K' : Subobject (D.baseChangeModule T)}
    (e : K = K') (hK : K ∈ D.properlySupportedQuotients T)
    (hK' : K' ∈ D.properlySupportedQuotients T) :
    D.cohObject T K hK = D.cohObject T K' hK' := by subst e; rfl

/-- **The object part of the morphism takes the identity of a test scheme to the identity.**
The inverse image of a quotient along the identity is the quotient itself, by the unit law of
the pseudofunctoriality of the inverse images of Stacks 03LU, so the two objects of `Coh_{X/B}`
agree. -/
theorem cohObject_quotientPullback_id
    (T : SchemesOver D.Y) {K : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.properlySupportedQuotients T)
    (hK' : D.quotientPullback (𝟙 T) K ∈ D.properlySupportedQuotients T) :
    D.cohObject T (D.quotientPullback (𝟙 T) K) hK' = D.cohObject T K hK :=
  D.cohObject_congr (D.quotientPullback_id (modulePushforwardCoherence B S hS) T K) hK' hK

/-- **The object part of the morphism is compatible with composition of morphisms of test
schemes.**  The inverse image of a quotient along a composite is the iterated inverse image, by
the associativity coherence of the pseudofunctoriality of the inverse images of Stacks 03LU, so
the two objects of `Coh_{X/B}` agree. -/
theorem cohObject_quotientPullback_comp
    {T'' T' T : SchemesOver D.Y} (h : T'' ⟶ T') (k : T' ⟶ T)
    {K : Subobject (D.baseChangeModule T)}
    (hK₁ : D.quotientPullback (h ≫ k) K ∈ D.properlySupportedQuotients T'')
    (hK₂ : D.quotientPullback h (D.quotientPullback k K) ∈
      D.properlySupportedQuotients T'') :
    D.cohObject T'' (D.quotientPullback (h ≫ k) K) hK₁ =
      D.cohObject T'' (D.quotientPullback h (D.quotientPullback k K)) hK₂ :=
  D.cohObject_congr (D.quotientPullback_comp (modulePushforwardCoherence B S hS) h k K)
    hK₁ hK₂

end QuotSituation

end AlgebraicGeometry.Space

end
