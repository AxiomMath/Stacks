module

public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubstackCharts
public import StacksFrontier.AlgebraicGeometry.Stacks.SubstackFactorizationPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InvariantClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.PresentationFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.ProjectionTwoArrow
import all StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionDescent

/-!
# Substacks of a presented algebraic stack and invariant subspaces (Stacks 0507)

Let `[U/R] ⟶ 𝒳` be a presentation of an algebraic stack `𝒳` over `S`: a smooth groupoid
`G = (U, R, s, t, c)` in algebraic spaces over `S` together with an equivalence `E` over the big
fppf site from its quotient stack to `𝒳`. Write `π : U ⟶ 𝒳` for the composite of the canonical
projection of Stacks 044R with `E`. Stacks 0507 asserts that `𝒵 ↦ U ×_𝒳 𝒵` is a bijection from
the locally closed substacks of `𝒳` to the `R`-invariant locally closed subspaces of `U`, that a
1-morphism `𝒴 ⟶ 𝒳` factors through `𝒵` exactly when `𝒴 ×_𝒳 U ⟶ U` factors through `U ×_𝒳 𝒵`,
and the same for closed and for open substacks.

## Main definitions

* `AlgebraicGeometry.Stack.presentationSubfunctor`: the subfunctor of a presheaf `F` cut out by a
  property `P` of the objects of `𝒳` along a 1-morphism `v` from the category attached to `F`;
  along the presentation it is `U ×_𝒳 𝒵` for the full subcategory `𝒵` of `P`.
* `AlgebraicGeometry.Stack.presentationProperty`: conversely, the property of the objects of `𝒳`
  cut out by a subfunctor `Z` of `F` along `v`: an object has it when every object of `F` mapping
  to it lies in `Z`.
* `AlgebraicGeometry.Stack.substackWithEquiv`: the bijection, at an arbitrary property `Q` of
  morphisms of schemes which descends effectively along covering sieves.

## Main results

* `AlgebraicGeometry.Stack.exists_equiv_isInvariantLocallyClosed_presentation`: **Stacks 0507**,
  locally closed substacks.
* `AlgebraicGeometry.Stack.exists_equiv_isInvariantClosed_presentation`: **Stacks 0507**, closed
  substacks.
* `AlgebraicGeometry.Stack.exists_equiv_isInvariantOpen_presentation`: **Stacks 0507**, open
  substacks.

## The proof

The source deduces the bijection from Stacks 0505 and Stacks 04YN, which in this library rest on
the representability of `[Z/R_Z] ⟶ [U/R]` (Stacks 04ZP). The route here avoids them, and with
them the bootstrap theorem; it uses only full faithfulness of the presentation and fppf descent of
the three kinds of immersion along covering sieves.

*From substacks to subspaces.* For a `Q`-substack `𝒵` cut out by `P`, the subfunctor
`U ×_𝒳 𝒵 = {u | P (π u)}` has as inverse image along a section `u` of `U` over `T` the subfunctor
of `yoneda T` cut out by `P` at `π u`, which is a `Q`-subspace because `𝒵` is a `Q`-substack
(`AlgebraicGeometry.Stack.isSubspaceWith_objSubfunctor`); so it is a `Q`-subspace of `U`. It is
invariant because an arrow `r` of `R` gives a morphism `π (s r) ⟶ π (t r)` lying over an identity,
which is an isomorphism (Stacks 044S).

*From subspaces to substacks.* For an invariant subspace `Z`, let `P_Z` hold at `x` when every
object `π u ⟶ x` of the presentation mapping to `x` has `u ∈ Z`. Then `U ×_𝒳 𝒵_{P_Z} = Z`: a
morphism `π u' ⟶ π u` comes from an arrow of the pointwise groupoid, because the presentation is
fully faithful (Stacks 044X, part (2), with Stacks 003Z), and that arrow is an arrow of `R`
joining `u'` to a restriction of `u`, so invariance applies. The property `P_Z` is local on the
site because `Z` is a sheaf, and at an object `y` of `𝒳` over `T` its subfunctor of `yoneda T` is
locally, over the covering of Stacks 044X part (1), the inverse image of `Z` along a section of
`U`; so it is a `Q`-subspace by descent along covering sieves
(`AlgebraicGeometry.Stack.isSubspaceWith_objSubfunctor_of_covering`), and `P_Z` cuts out a
`Q`-substack.

*The two composites.* `U ×_𝒳 𝒵_{P_Z} = Z` is the computation above. For a substack `P`, the
property `P_{U ×_𝒳 𝒵_P}` is `P`: one inclusion is that `P` is inherited along morphisms, the
other is the descent step `AlgebraicGeometry.Stack.forall_prop_of_forall_twoFibreProduct` of the
factorization criterion, which is where membership of a substack being local on the site enters.

*The factorization criterion* is the pointwise reading of the descent step: `f` factors through
`𝒵_P` when `P` holds on its image, and the comparison isomorphisms of `𝒴 ×_𝒳 U` carry that to
membership in `U ×_𝒳 𝒵_P` of the `U`-component of each of its objects.

Smoothness of the groupoid is not used; it is part of the hypotheses because the source states
the lemma for a presentation.

## Implementation notes

The subspace `U ×_𝒳 𝒵` is a subfunctor of `U`. Each of the three statements records that it is
the image of the first projection of the 2-fibre product `U ×_𝒳 𝒵` of Stacks 02X2, which is the
sense in which the bijection sends `𝒵` to `U ×_𝒳 𝒵`; the projection is a monomorphism because
the inclusion of `𝒵` is fully faithful. "`𝒴 ×_𝒳 U ⟶ U` factors through `Z`" is stated as: the
`U`-component of every object of the 2-fibre product lies in `Z`, which is what a factorization
of a 1-morphism into the category attached to `U` through the category attached to `Z` amounts
to.

## References

* [Stacks Project, Tag 0507](https://stacks.math.columbia.edu/tag/0507)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.GroupoidInAlgebraicSpaces

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section PresentationSubfunctor

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The morphism of the category attached to a presheaf from the restriction of a section along a
morphism of the site to that section. -/
def fibredCategoryRestrictHom {T T' : BigFppfOver B S hS} (t : T' ⟶ T) (x : F.obj (op T)) :
    (⟨T', Discrete.mk (F.map t.op x)⟩ : (fibredCategory B S hS F).val.obj) ⟶
      ⟨T, Discrete.mk x⟩ :=
  { base := t
    fiber := Discrete.eqToHom rfl }

/-- The image of `AlgebraicGeometry.Stack.fibredCategoryRestrictHom` under a 1-morphism over the
site lies over the morphism of the site it restricts along. -/
instance isHomLift_map_fibredCategoryRestrictHom
    (v : (fibredCategory B S hS F).val ⥤ᵇ 𝒳.val.val) {T T' : BigFppfOver B S hS}
    (t : T' ⟶ T) (x : F.obj (op T)) :
    𝒳.val.val.p.IsHomLift t (v.map (fibredCategoryRestrictHom t x)) := by
  have : (fibredCategory B S hS F).val.p.IsHomLift t (fibredCategoryRestrictHom t x) :=
    IsHomLift.of_fac _ t _ rfl rfl (by simp; rfl)
  exact Functor.isHomLift_map_of_comp_eq v.w t (fibredCategoryRestrictHom t x)

variable {P : ObjectProperty 𝒳.val.val.obj} (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a)
  (v : (fibredCategory B S hS F).val ⥤ᵇ 𝒳.val.val)

/-- The subfunctor of `F` cut out by a property `P` of the objects of `𝒳` inherited along
morphisms, along a 1-morphism `v` from the category attached to `F`: its sections over `T` are
the sections `x` of `F` with `P (v (T, x))`. Along a presentation of `𝒳` this is the subspace
`U ×_𝒳 𝒵` of `U`, for `𝒵` the full subcategory of `P`. -/
def presentationSubfunctor : Subfunctor F where
  obj T := {x | P (v.obj ⟨T.unop, Discrete.mk x⟩)}
  map {_ _} i x hx := hP (v.map (fibredCategoryRestrictHom i.unop x)) hx

/-- A section `x` of `F` over `T` lies in `presentationSubfunctor hP v` exactly when `P` holds
at the image of `(T, x)` under `v`. -/
theorem mem_presentationSubfunctor_iff {T : BigFppfOver B S hS} (x : F.obj (op T)) :
    x ∈ (presentationSubfunctor hP v).obj (op T) ↔ P (v.obj ⟨T, Discrete.mk x⟩) :=
  Iff.rfl

/-- The inverse image of `AlgebraicGeometry.Stack.presentationSubfunctor` along a section `x` of
`F` over `T` is `objSubfunctor` at the image of `(T, x)`. -/
theorem presentationSubfunctor_preimage {T : BigFppfOver B S hS} (x : F.obj (op T)) :
    (presentationSubfunctor hP v).preimage (yonedaEquiv.symm x) =
      objSubfunctor hP ⟨v.obj ⟨T, Discrete.mk x⟩, v.w_obj _⟩ := by
  ext T' t
  show P (v.obj ⟨T'.unop, Discrete.mk (F.map t.op x)⟩) ↔ _
  exact (mem_objSubfunctor_iff hP _ t (v.map (fibredCategoryRestrictHom t x))).symm

/-- **From `Q`-substacks to `Q`-subspaces.** If `P` cuts out a `Q`-substack of `𝒳` and `F` is
an algebraic space, then `AlgebraicGeometry.Stack.presentationSubfunctor` is a `Q`-subspace of
`F`: its inverse images along sections of `F` are the subfunctors cut out by `P` at objects of
`𝒳`, which are `Q`-subspaces by `AlgebraicGeometry.Stack.isSubspaceWith_objSubfunctor`. -/
theorem isSubspaceWith_presentationSubfunctor {Q : MorphismProperty Scheme.{u}} [Q.RespectsIso]
    (hPQ : IsSubstackWith Q 𝒳 P) (hF : IsAlgebraicSpace B S hS F) :
    Space.IsSubspaceWith B S hS Q (presentationSubfunctor hP v) := by
  have hQ : (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      (presentationSubfunctor hP v).ι :=
    Space.presheaf_ι_of_forall_preimage _ fun a g => by
      rw [← yonedaEquiv.symm_apply_apply g, presentationSubfunctor_preimage]
      exact (isSubspaceWith_objSubfunctor hP hPQ _).2
  exact ⟨isAlgebraicSpace_of_relativelyRepresentable B S hS _ hQ.rep hF, hQ⟩

/-- **The subspace `U ×_𝒳 𝒵` is the image of the projection of the 2-fibre product.** For `P`
closed under isomorphism, a section `x` of `F` over `T` lies in
`AlgebraicGeometry.Stack.presentationSubfunctor` exactly when `(T, x)` is the first component of
an object of the 2-fibre product of `v` with the inclusion of the full subcategory of `P`. -/
theorem mem_presentationSubfunctor_iff_exists_twoFibreProduct [P.IsClosedUnderIsomorphisms]
    {T : BigFppfOver B S hS} (x : F.obj (op T)) :
    x ∈ (presentationSubfunctor hP v).obj (op T) ↔
      ∃ d : TwoFibreProductOver (fibredCategory B S hS F).val.p (fullSubcategoryBased 𝒳 P).p
          𝒳.val.val.p v.toFunctor (fullSubcategoryBasedInclusion 𝒳 P).toFunctor,
        d.x = ⟨T, Discrete.mk x⟩ := by
  refine ⟨fun hx => ⟨{ base := T
                       x := ⟨T, Discrete.mk x⟩
                       y := ⟨v.obj ⟨T, Discrete.mk x⟩, hx⟩
                       hx := rfl
                       hy := v.w_obj _
                       iso := Iso.refl _
                       vertical := IsHomLift.id (v.w_obj _) }, rfl⟩, ?_⟩
  rintro ⟨d, hd⟩
  have h : P (v.obj d.x) := P.prop_of_iso d.iso.symm d.y.property
  rwa [hd] at h

/-- The property of the objects of `𝒳` cut out by a subfunctor `Z` of `F` along a 1-morphism `v`
from the category attached to `F`: an object `x` has it when every object `(T, u)` of the
category attached to `F` with a morphism `v (T, u) ⟶ x` has `u ∈ Z`. -/
def presentationProperty (Z : Subfunctor F) : ObjectProperty 𝒳.val.val.obj :=
  fun x => ∀ (y : (fibredCategory B S hS F).val.obj), (v.obj y ⟶ x) →
    y.fiber.as ∈ Z.obj (op y.base)

omit hP in
/-- `AlgebraicGeometry.Stack.presentationProperty` is inherited along morphisms. -/
theorem presentationProperty_of_hom (Z : Subfunctor F) {a b : 𝒳.val.val.obj} (φ : a ⟶ b)
    (hb : presentationProperty v Z b) : presentationProperty v Z a :=
  fun y ζ => hb y (ζ ≫ φ)

omit hP in
/-- **`AlgebraicGeometry.Stack.presentationProperty` is local on the site** when `Z` is a sheaf
in a sheaf `F`: if it holds at the restrictions of an object `y` along the arrows of a covering
sieve, then it holds at `y`. A morphism `v (T, u) ⟶ y` restricts along the pull-back of the
sieve to morphisms into restrictions of `y`, so the restrictions of `u` lie in `Z`. -/
theorem presentationProperty_of_covering (Z : Subfunctor F)
    (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F)
    (hZ : Presieve.IsSheaf (BigFppfOver.topology B S hS) Z.toFunctor)
    ⦃U : BigFppfOver B S hS⦄ (y : 𝒳.val.val.p.Fiber U) ⦃R : Sieve U⦄
    (hR : R ∈ BigFppfOver.topology B S hS U)
    (hall : ∀ ⦃V : BigFppfOver B S hS⦄ (k : V ⟶ U), R k →
      k ∈ (objSubfunctor (presentationProperty_of_hom v Z) y).obj (op V)) :
    presentationProperty v Z y.1 := by
  rintro ⟨Tx, ⟨u⟩⟩ ζ
  have hd : 𝒳.val.val.p.obj (v.obj ⟨Tx, ⟨u⟩⟩) = Tx := v.w_obj _
  let m : Tx ⟶ U := eqToHom hd.symm ≫ 𝒳.val.val.p.map ζ ≫ eqToHom y.2
  have hm : 𝒳.val.val.p.IsHomLift m ζ := IsHomLift.of_fac _ m ζ hd y.2 (by simp [m])
  refine (Subfunctor.isSheaf_iff Z hF).1 hZ (op Tx) u
    ((BigFppfOver.topology B S hS).superset_covering ?_
      ((BigFppfOver.topology B S hS).pullback_stable m hR))
  intro W n hn
  exact (mem_objSubfunctor_iff _ y (n ≫ m) (v.map (fibredCategoryRestrictHom n u) ≫ ζ)).1
    (hall (n ≫ m) hn) ⟨W, ⟨F.map n.op u⟩⟩ (𝟙 _)

end PresentationSubfunctor

section Presentation

variable {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (G : GroupoidInAlgebraicSpaces B S hS (baseSpace B S hS))
  (E : (quotientStack G).obj ⥤ 𝒳.val.val.obj) [E.IsEquivalence]
  (hE : E ⋙ 𝒳.val.val.p = (quotientStack G).p)

/-- The 1-morphism `π : U ⟶ 𝒳` of a presentation: the canonical projection of Stacks 044R
followed by the equivalence `[U/R] ⟶ 𝒳`. -/
noncomputable abbrev presentationProjection :
    (fibredCategory B S hS G.objects.obj).val ⥤ᵇ 𝒳.val.val :=
  (quotientStackProjection G).comp (⟨E, hE⟩ : quotientStack G ⥤ᵇ 𝒳.val.val)

omit [E.IsEquivalence] in
/-- **`U ×_𝒳 𝒵` is invariant.** For `P` closed under isomorphism and inherited along morphisms,
the inverse images of `AlgebraicGeometry.Stack.presentationSubfunctor` under the source and the
target maps agree: an arrow `r` gives a morphism `π (s r) ⟶ π (t r)` lying over an identity
(Stacks 044S), which is an isomorphism because `𝒳` is fibred in groupoids. -/
theorem presentationSubfunctor_preimage_target {P : ObjectProperty 𝒳.val.val.obj}
    [P.IsClosedUnderIsomorphisms] (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a) :
    (presentationSubfunctor hP (presentationProjection G E hE)).preimage G.target.hom =
      (presentationSubfunctor hP (presentationProjection G E hE)).preimage G.source.hom := by
  ext T r
  obtain ⟨g, hg, -, -⟩ := quotientStackTwoArrow_app G ⟨T.unop, Discrete.mk r⟩
  set ζ := E.map ((pointwiseToQuotientStack G).map g)
  have hg' : (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p.IsHomLift
      (𝟙 T.unop) g :=
    hg ▸ IsHomLift.map _ g
  have h1 : (quotientStack G).p.IsHomLift (𝟙 T.unop) ((pointwiseToQuotientStack G).map g) :=
    Functor.isHomLift_map_of_comp_eq (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq
      (𝟙 T.unop) g
  have h2 : 𝒳.val.val.p.IsHomLift (𝟙 T.unop) ζ :=
    Functor.isHomLift_map_of_comp_eq hE (𝟙 T.unop) ((pointwiseToQuotientStack G).map g)
  have := 𝒳.val.property.isStronglyCartesian_homLift (𝟙 T.unop) ζ
  have : IsIso ζ := Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.val.p (𝟙 T.unop) ζ
  show P (E.obj ((pointwiseToQuotientStack G).obj ⟨T.unop, G.target.hom.app T r⟩)) ↔
    P (E.obj ((pointwiseToQuotientStack G).obj ⟨T.unop, G.source.hom.app T r⟩))
  exact ⟨hP ζ, P.prop_of_iso (asIso ζ)⟩

/-- **`U ×_𝒳 𝒵_{P_Z} = Z`.** For a subfunctor `Z` of `U` whose inverse image under the source
map is contained in its inverse image under the target map, the subfunctor of `U` cut out by
`AlgebraicGeometry.Stack.presentationProperty` is `Z` itself.

A morphism `π u' ⟶ π u` in `𝒳` comes, through the equivalence and the full faithfulness of the
pointwise groupoid fibration in the quotient stack (Stacks 044X), from an arrow of the pointwise
groupoid fibration; its fibre component, inverted, is an arrow of `R` with source a restriction
of `u` and target `u'`. -/
theorem presentationSubfunctor_presentationProperty (Z : Subfunctor G.objects.obj)
    (hZ : Z.preimage G.source.hom ≤ Z.preimage G.target.hom) :
    presentationSubfunctor (presentationProperty_of_hom (presentationProjection G E hE) Z)
      (presentationProjection G E hE) = Z := by
  ext T x
  refine ⟨fun hx => hx ⟨T.unop, Discrete.mk x⟩ (𝟙 _), fun hx y ζ => ?_⟩
  let ψ := (fullyFaithfulPointwiseToQuotientStack G).preimage (E.preimage ζ)
  obtain ⟨r, hs, ht⟩ := G.toGroupoidInFunctors.evaluationArrowEquiv (op y.base) _ _
    (Groupoid.inv ψ.fiber)
  have hs' : G.source.hom.app (op y.base) r = G.objects.obj.map ψ.base.op x := hs
  have ht' : G.target.hom.app (op y.base) r = y.fiber.as := ht
  have h₁ : r ∈ (Z.preimage G.source.hom).obj (op y.base) := by
    show G.source.hom.app _ r ∈ Z.obj _
    rw [hs']
    exact Z.map ψ.base.op hx
  rw [← ht']
  exact hZ _ h₁

/-- **`P_{U ×_𝒳 𝒵_P} = P`.** For a property `P` closed under isomorphism and inherited along
morphisms whose full subcategory is an algebraic stack, the property cut out by its subfunctor of
`U` is `P` itself, as soon as the full subcategory of the latter property is an algebraic stack
too. One inclusion is inheritance along morphisms; the other is the descent step
`AlgebraicGeometry.Stack.forall_prop_of_forall_twoFibreProduct` of the factorization criterion,
applied to the inclusion of the full subcategory of the latter property. -/
theorem presentationProperty_presentationSubfunctor {P : ObjectProperty 𝒳.val.val.obj}
    [P.IsClosedUnderIsomorphisms] (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a)
    (hPalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hPZalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳
      (presentationProperty (presentationProjection G E hE)
        (presentationSubfunctor hP (presentationProjection G E hE))))) :
    presentationProperty (presentationProjection G E hE)
      (presentationSubfunctor hP (presentationProjection G E hE)) = P := by
  funext x
  exact propext ⟨fun hx => forall_prop_of_forall_twoFibreProduct
      (𝒴 := fullSubcategoryAlgebraicStack 𝒳 _ hPZalg) G E hE hPalg
      (fullSubcategoryBasedInclusion 𝒳 _)
      (fun d => P.prop_of_iso d.iso (d.y.property d.x d.iso.hom)) ⟨x, hx⟩,
    fun hx _ ζ => hP ζ hx⟩

/-- **From invariant `Q`-subspaces to `Q`-substacks.** For a `Q`-subspace `Z` of `U` whose
inverse image under the source map is contained in its inverse image under the target map,
`AlgebraicGeometry.Stack.presentationProperty` cuts out a `Q`-substack of `𝒳`, as soon as
morphisms with `Q` descend effectively along covering sieves.

At an object `y` of `𝒳` over `T`, the presentation supplies a covering sieve of `T` over each
arrow `k` of which a morphism `π u ⟶ y` lies (Stacks 044X, part (1)); the inverse image along `k`
of the subfunctor of `yoneda T` cut out at `y` is then the inverse image of `Z` along `u`, a
`Q`-subspace, and the property is local on the site, so descent along the covering sieve
applies. -/
theorem isSubstackWith_presentationProperty {Q : MorphismProperty Scheme.{u}} [Q.RespectsIso]
    (hdesc : Space.IsEffectiveDescentAlongCoveringSieve B S hS Q)
    (Z : Subfunctor G.objects.obj) (hZQ : Space.IsSubspaceWith B S hS Q Z)
    (hZ : Z.preimage G.source.hom ≤ Z.preimage G.target.hom) :
    IsSubstackWith Q 𝒳 (presentationProperty (presentationProjection G E hE) Z) := by
  have hinh : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) →
      presentationProperty (presentationProjection G E hE) Z b →
        presentationProperty (presentationProjection G E hE) Z a :=
    presentationProperty_of_hom (presentationProjection G E hE) Z
  refine isSubstackWith_of_forall_isSubspaceWith_objSubfunctor hinh fun U y => ?_
  obtain ⟨R, hR, hloc⟩ := exists_local_hom_from_presentation G E hE U y
  refine isSubspaceWith_objSubfunctor_of_covering hinh hdesc y
    (isSheaf_objSubfunctor hinh
      (presentationProperty_of_covering (presentationProjection G E hE) Z
        ((isSheaf_iff_isSheaf_of_type _ _).1 G.objects.property.isSheaf)
        ((isSheaf_iff_isSheaf_of_type _ _).1 hZQ.1.isSheaf)) y) hR ?_
  intro V k hk
  obtain ⟨⟨Tb, ⟨u⟩⟩, ζ, hζ⟩ := hloc hk
  have := hζ
  have hd := IsHomLift.domain_eq 𝒳.val.val.p k ζ
  have hV : Tb = V :=
    ((presentationProjection G E hE).w_obj ⟨Tb, ⟨u⟩⟩).symm.trans hd
  subst hV
  have key : Space.IsSubspaceWith B S hS Q (objSubfunctor hinh
      ⟨(presentationProjection G E hE).obj ⟨Tb, ⟨u⟩⟩,
        (presentationProjection G E hE).w_obj ⟨Tb, ⟨u⟩⟩⟩) := by
    rw [← presentationSubfunctor_preimage, presentationSubfunctor_presentationProperty G E hE Z hZ]
    exact Space.isSubspaceWith_preimage _ Z G.objects.property (isAlgebraicSpace_yoneda _ _ _ _)
      hZQ
  exact objSubfunctor_preimage hinh y
    ⟨_, (presentationProjection G E hE).w_obj ⟨Tb, ⟨u⟩⟩⟩ k ζ hζ ▸ key

/-- **The factorization criterion along a presentation, pointwise.** For `P` closed under
isomorphism and inherited along morphisms whose full subcategory is an algebraic stack, a
1-morphism `f : 𝒴 ⟶ 𝒳` factors through the full subcategory of `P` exactly when the
`U`-component of every object of `𝒴 ×_𝒳 U` lies in `U ×_𝒳 𝒵_P`. -/
theorem factorsThrough_iff_forall_mem_presentationSubfunctor {P : ObjectProperty 𝒳.val.val.obj}
    [P.IsClosedUnderIsomorphisms] (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a)
    (hPalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    {𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒴 ⟶ 𝒳) :
    (∃ g : 𝒴.val.val ⥤ᵇ fullSubcategoryBased 𝒳 P,
        Nonempty (g.comp (fullSubcategoryBasedInclusion 𝒳 P) ≅ f.hom.hom)) ↔
      ∀ d : TwoFibreProductOver (fibredCategory B S hS G.objects.obj).val.p 𝒴.val.val.p
          𝒳.val.val.p (presentationProjection G E hE).toFunctor f.hom.hom.toFunctor,
        d.x.fiber.as ∈
          (presentationSubfunctor hP (presentationProjection G E hE)).obj (op d.x.base) :=
  (exists_based_factorization_iff f.hom.hom).trans
    ⟨fun h d => P.prop_of_iso d.iso.symm (h d.y), fun h =>
      forall_prop_of_forall_twoFibreProduct G E hE hPalg f.hom.hom
        fun d => P.prop_of_iso d.iso (h d)⟩

/-- **Stacks 0507 at a property `Q` of morphisms of schemes.** If morphisms with `Q` descend
effectively along covering sieves, then `𝒵 ↦ U ×_𝒳 𝒵` is a bijection from the `Q`-substacks of
`𝒳` to the `R`-invariant `Q`-subspaces of `U`. -/
noncomputable def substackWithEquiv {Q : MorphismProperty Scheme.{u}} [Q.RespectsIso]
    (hdesc : Space.IsEffectiveDescentAlongCoveringSieve B S hS Q) :
    {P : ObjectProperty 𝒳.val.val.obj // IsSubstackWith Q 𝒳 P} ≃
      {Z : Subfunctor G.objects.obj // Space.IsSubspaceWith B S hS Q Z ∧
        Z.preimage G.target.hom = Z.preimage G.source.hom} where
  toFun P :=
    have := P.2.1
    ⟨presentationSubfunctor (fun {_ _} φ hb => P.2.prop_of_hom φ hb)
        (presentationProjection G E hE),
      isSubspaceWith_presentationSubfunctor (fun {_ _} φ hb => P.2.prop_of_hom φ hb)
        (presentationProjection G E hE) P.2 G.objects.property,
      presentationSubfunctor_preimage_target G E hE (fun {_ _} φ hb => P.2.prop_of_hom φ hb)⟩
  invFun Z := ⟨presentationProperty (presentationProjection G E hE) Z.1,
    isSubstackWith_presentationProperty G E hE hdesc Z.1 Z.2.1 Z.2.2.symm.le⟩
  left_inv P := by
    have := P.2.1
    exact Subtype.ext (presentationProperty_presentationSubfunctor G E hE _ P.2.2.choose
      (isSubstackWith_presentationProperty G E hE hdesc _
        (isSubspaceWith_presentationSubfunctor (fun {_ _} φ hb => P.2.prop_of_hom φ hb)
          (presentationProjection G E hE) P.2 G.objects.property)
        (presentationSubfunctor_preimage_target G E hE
          (fun {_ _} φ hb => P.2.prop_of_hom φ hb)).symm.le).2.choose)
  right_inv Z := Subtype.ext (presentationSubfunctor_presentationProperty G E hE Z.1 Z.2.2.symm.le)

/-- The subfunctor attached by `substackWithEquiv` to a substack property `P` is
`presentationSubfunctor` of `P` along `presentationProjection`. -/
theorem substackWithEquiv_apply_coe {Q : MorphismProperty Scheme.{u}} [Q.RespectsIso]
    (hdesc : Space.IsEffectiveDescentAlongCoveringSieve B S hS Q)
    (P : {P : ObjectProperty 𝒳.val.val.obj // IsSubstackWith Q 𝒳 P}) :
    (substackWithEquiv G E hE hdesc P).1 =
      presentationSubfunctor (fun {_ _} φ hb => P.2.prop_of_hom φ hb)
        (presentationProjection G E hE) :=
  rfl

include E hE in
/-- For a subfunctor of `U`, containment of its inverse image under the source map in its inverse
image under the target map forces equality: such a subfunctor is `U ×_𝒳 𝒵` for the property
`AlgebraicGeometry.Stack.presentationProperty` it cuts out
(`AlgebraicGeometry.Stack.presentationSubfunctor_presentationProperty`), and subfunctors of that
form are invariant (`AlgebraicGeometry.Stack.presentationSubfunctor_preimage_target`). -/
theorem preimage_target_eq_of_preimage_source_le (Z : Subfunctor G.objects.obj)
    (hZ : Z.preimage G.source.hom ≤ Z.preimage G.target.hom) :
    Z.preimage G.target.hom = Z.preimage G.source.hom := by
  have : (presentationProperty (presentationProjection G E hE) Z).IsClosedUnderIsomorphisms :=
    ⟨fun e => presentationProperty_of_hom (presentationProjection G E hE) Z e.inv⟩
  have h := presentationSubfunctor_preimage_target G E hE
    (presentationProperty_of_hom (presentationProjection G E hE) Z)
  rwa [presentationSubfunctor_presentationProperty G E hE Z hZ] at h

end Presentation

section Correspondence

variable (𝒳 : AlgebraicStacks.{u, w} B S hS) (Pr : GroupoidPresentation B S hS 𝒳.val.val)

/-- **Stacks 0507 at a property `Q` of morphisms of schemes.** Let `[U/R] ⟶ 𝒳` be a presentation
of an algebraic stack and let morphisms with `Q` descend effectively along covering sieves. There
is a bijection from the `Q`-substacks `𝒵` of `𝒳` to the `R`-invariant `Q`-subspaces of `U`,
sending `𝒵` to the image of the projection `U ×_𝒳 𝒵 ⟶ U`; and a 1-morphism `f : 𝒴 ⟶ 𝒳`
factors through `𝒵` exactly when `𝒴 ×_𝒳 U ⟶ U` factors through `U ×_𝒳 𝒵`, that is, exactly when
the `U`-component of every object of `𝒴 ×_𝒳 U` lies in the image of `𝒵`. -/
theorem exists_equiv_substackWith_presentation {Q : MorphismProperty Scheme.{u}} [Q.RespectsIso]
    (hdesc : Space.IsEffectiveDescentAlongCoveringSieve B S hS Q) :
    ∃ e : {P : ObjectProperty 𝒳.val.val.obj // IsSubstackWith Q 𝒳 P} ≃
        {Z : Subfunctor Pr.groupoid.objects.obj // Space.IsSubspaceWith B S hS Q Z ∧
          Z.preimage Pr.groupoid.target.hom = Z.preimage Pr.groupoid.source.hom},
      ∀ P : {P : ObjectProperty 𝒳.val.val.obj // IsSubstackWith Q 𝒳 P},
        (∀ (T : BigFppfOver B S hS) (u : Pr.groupoid.objects.obj.obj (op T)),
          u ∈ (e P).1.obj (op T) ↔
            ∃ d : TwoFibreProductOver (fibredCategory B S hS Pr.groupoid.objects.obj).val.p
                (fullSubcategoryBased 𝒳 P.1).p 𝒳.val.val.p
                (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                  Pr.basedFunctor.w).toFunctor
                (fullSubcategoryBasedInclusion 𝒳 P.1).toFunctor,
              d.x = ⟨T, Discrete.mk u⟩) ∧
        ∀ (𝒴 : AlgebraicStacks.{u, w} B S hS) (f : 𝒴 ⟶ 𝒳),
          ((∃ g : 𝒴.val.val ⥤ᵇ fullSubcategoryBased 𝒳 P.1,
              Nonempty (g.comp (fullSubcategoryBasedInclusion 𝒳 P.1) ≅ f.hom.hom)) ↔
            ∃ g : BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor
                  (fibredCategory B S hS Pr.groupoid.objects.obj).val.p 𝒴.val.val.p 𝒳.val.val.p
                  (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                    Pr.basedFunctor.w).toFunctor f.hom.hom.toFunctor) ⥤ᵇ
                BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor
                  (fibredCategory B S hS Pr.groupoid.objects.obj).val.p
                  (fullSubcategoryBased 𝒳 P.1).p 𝒳.val.val.p
                  (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                    Pr.basedFunctor.w).toFunctor
                  (fullSubcategoryBasedInclusion 𝒳 P.1).toFunctor),
              Nonempty (g.comp (TwoFibreProductOver.fstBased (fullSubcategoryBased 𝒳 P.1).p
                  𝒳.val.val.p (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                    Pr.basedFunctor.w).toFunctor
                  (fullSubcategoryBasedInclusion 𝒳 P.1).toFunctor) ≅
                TwoFibreProductOver.fstBased 𝒴.val.val.p 𝒳.val.val.p
                  (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                    Pr.basedFunctor.w).toFunctor f.hom.hom.toFunctor)) ∧
          ((∃ g : 𝒴.val.val ⥤ᵇ fullSubcategoryBased 𝒳 P.1,
              Nonempty (g.comp (fullSubcategoryBasedInclusion 𝒳 P.1) ≅ f.hom.hom)) ↔
            ∀ d : TwoFibreProductOver (fibredCategory B S hS Pr.groupoid.objects.obj).val.p
                𝒴.val.val.p 𝒳.val.val.p
                (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                  Pr.basedFunctor.w).toFunctor f.hom.hom.toFunctor,
              d.x.fiber.as ∈ (e P).1.obj (op d.x.base)) := by
  refine ⟨substackWithEquiv Pr.groupoid Pr.basedFunctor.toFunctor Pr.basedFunctor.w hdesc,
    fun P => ?_⟩
  have := P.2.1
  exact ⟨fun T u => mem_presentationSubfunctor_iff_exists_twoFibreProduct
      P.2.prop_of_hom _ u,
    fun 𝒴 f => ⟨factorsThroughSubstack_iff_presentation_of_isAlgebraicStack 𝒳 𝒴 Pr.groupoid
      Pr.smooth Pr.basedFunctor.toFunctor Pr.basedFunctor.w P.1 P.2.2.choose f,
      factorsThrough_iff_forall_mem_presentationSubfunctor Pr.groupoid
      Pr.basedFunctor.toFunctor Pr.basedFunctor.w P.2.prop_of_hom
      P.2.2.choose f⟩⟩

/-- **Stacks 0507**, locally closed substacks. Let `[U/R] ⟶ 𝒳` be a presentation of an algebraic
stack. There is a canonical bijection from the locally closed substacks `𝒵` of `𝒳` to the
`R`-invariant locally closed subspaces of `U`, sending `𝒵` to `U ×_𝒳 𝒵`. Moreover, a 1-morphism
`f : 𝒴 ⟶ 𝒳` of algebraic stacks factors through `𝒵` if and only if `𝒴 ×_𝒳 U ⟶ U` factors through
`U ×_𝒳 𝒵`.

Here `[U/R] ⟶ 𝒳` is a presentation of the algebraic stack `𝒳` (Stacks 04TI), and `π : U ⟶ 𝒳`
is the canonical projection followed by the equivalence. The bijection `e` sends `𝒵` to the
subspace of `U` that is the image of the projection `U ×_𝒳 𝒵 ⟶ U` from the 2-fibre product
(first conjunct). For every 1-morphism `f : 𝒴 ⟶ 𝒳` of algebraic stacks, `f` factors through `𝒵`
over the site and up to a 2-isomorphism exactly when the projection `𝒴 ×_𝒳 U ⟶ U` factors
through `U ×_𝒳 𝒵` (second conjunct), and exactly when the `U`-component of every object of
`𝒴 ×_𝒳 U` lies in `e 𝒵` (third conjunct), which is to say that `𝒴 ×_𝒳 U ⟶ U` factors through
the subspace `e 𝒵`. -/
@[stacks 0507 "locally closed"]
theorem exists_equiv_isInvariantLocallyClosed_presentation :
    ∃ e : {P : ObjectProperty 𝒳.val.val.obj // IsLocallyClosedSubstack 𝒳 P} ≃
        {Z : Subfunctor Pr.groupoid.objects.obj // IsInvariantLocallyClosed Pr.groupoid Z},
      ∀ P : {P : ObjectProperty 𝒳.val.val.obj // IsLocallyClosedSubstack 𝒳 P},
        (∀ (T : BigFppfOver B S hS) (u : Pr.groupoid.objects.obj.obj (op T)),
          u ∈ (e P).1.obj (op T) ↔
            ∃ d : TwoFibreProductOver (fibredCategory B S hS Pr.groupoid.objects.obj).val.p
                (fullSubcategoryBased 𝒳 P.1).p 𝒳.val.val.p
                (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                  Pr.basedFunctor.w).toFunctor
                (fullSubcategoryBasedInclusion 𝒳 P.1).toFunctor,
              d.x = ⟨T, Discrete.mk u⟩) ∧
        ∀ (𝒴 : AlgebraicStacks.{u, w} B S hS) (f : 𝒴 ⟶ 𝒳),
          ((∃ g : 𝒴.val.val ⥤ᵇ fullSubcategoryBased 𝒳 P.1,
              Nonempty (g.comp (fullSubcategoryBasedInclusion 𝒳 P.1) ≅ f.hom.hom)) ↔
            ∃ g : BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor
                  (fibredCategory B S hS Pr.groupoid.objects.obj).val.p 𝒴.val.val.p 𝒳.val.val.p
                  (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                    Pr.basedFunctor.w).toFunctor f.hom.hom.toFunctor) ⥤ᵇ
                BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor
                  (fibredCategory B S hS Pr.groupoid.objects.obj).val.p
                  (fullSubcategoryBased 𝒳 P.1).p 𝒳.val.val.p
                  (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                    Pr.basedFunctor.w).toFunctor
                  (fullSubcategoryBasedInclusion 𝒳 P.1).toFunctor),
              Nonempty (g.comp (TwoFibreProductOver.fstBased (fullSubcategoryBased 𝒳 P.1).p
                  𝒳.val.val.p (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                    Pr.basedFunctor.w).toFunctor
                  (fullSubcategoryBasedInclusion 𝒳 P.1).toFunctor) ≅
                TwoFibreProductOver.fstBased 𝒴.val.val.p 𝒳.val.val.p
                  (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                    Pr.basedFunctor.w).toFunctor f.hom.hom.toFunctor)) ∧
          ((∃ g : 𝒴.val.val ⥤ᵇ fullSubcategoryBased 𝒳 P.1,
              Nonempty (g.comp (fullSubcategoryBasedInclusion 𝒳 P.1) ≅ f.hom.hom)) ↔
            ∀ d : TwoFibreProductOver (fibredCategory B S hS Pr.groupoid.objects.obj).val.p
                𝒴.val.val.p 𝒳.val.val.p
                (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                  Pr.basedFunctor.w).toFunctor f.hom.hom.toFunctor,
              d.x.fiber.as ∈ (e P).1.obj (op d.x.base)) :=
  have : MorphismProperty.RespectsIso (@AlgebraicGeometry.IsImmersion.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exists_equiv_substackWith_presentation 𝒳 Pr
    (Space.isEffectiveDescentAlongCoveringSieve_isImmersion B S hS)

/-- **Stacks 0507**, closed substacks. Let `[U/R] ⟶ 𝒳` be a presentation of an algebraic stack.
There is a canonical bijection from the closed substacks `𝒵` of `𝒳` to the `R`-invariant closed
subspaces of `U`, sending `𝒵` to `U ×_𝒳 𝒵`. Moreover, a 1-morphism `f : 𝒴 ⟶ 𝒳` of algebraic
stacks factors through `𝒵` if and only if `𝒴 ×_𝒳 U ⟶ U` factors through `U ×_𝒳 𝒵`.

Here `[U/R] ⟶ 𝒳` is a presentation of the algebraic stack `𝒳` (Stacks 04TI), and `π : U ⟶ 𝒳`
is the canonical projection followed by the equivalence. The bijection `e` sends `𝒵` to the
subspace of `U` that is the image of the projection `U ×_𝒳 𝒵 ⟶ U` from the 2-fibre product
(first conjunct). For every 1-morphism `f : 𝒴 ⟶ 𝒳` of algebraic stacks, `f` factors through `𝒵`
over the site and up to a 2-isomorphism exactly when the projection `𝒴 ×_𝒳 U ⟶ U` factors
through `U ×_𝒳 𝒵` (second conjunct), and exactly when the `U`-component of every object of
`𝒴 ×_𝒳 U` lies in `e 𝒵` (third conjunct), which is to say that `𝒴 ×_𝒳 U ⟶ U` factors through
the subspace `e 𝒵`. -/
@[stacks 0507 "closed"]
theorem exists_equiv_isInvariantClosed_presentation :
    ∃ e : {P : ObjectProperty 𝒳.val.val.obj // IsClosedSubstack 𝒳 P} ≃
        {Z : Subfunctor Pr.groupoid.objects.obj // IsInvariantClosed Pr.groupoid Z},
      ∀ P : {P : ObjectProperty 𝒳.val.val.obj // IsClosedSubstack 𝒳 P},
        (∀ (T : BigFppfOver B S hS) (u : Pr.groupoid.objects.obj.obj (op T)),
          u ∈ (e P).1.obj (op T) ↔
            ∃ d : TwoFibreProductOver (fibredCategory B S hS Pr.groupoid.objects.obj).val.p
                (fullSubcategoryBased 𝒳 P.1).p 𝒳.val.val.p
                (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                  Pr.basedFunctor.w).toFunctor
                (fullSubcategoryBasedInclusion 𝒳 P.1).toFunctor,
              d.x = ⟨T, Discrete.mk u⟩) ∧
        ∀ (𝒴 : AlgebraicStacks.{u, w} B S hS) (f : 𝒴 ⟶ 𝒳),
          ((∃ g : 𝒴.val.val ⥤ᵇ fullSubcategoryBased 𝒳 P.1,
              Nonempty (g.comp (fullSubcategoryBasedInclusion 𝒳 P.1) ≅ f.hom.hom)) ↔
            ∃ g : BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor
                  (fibredCategory B S hS Pr.groupoid.objects.obj).val.p 𝒴.val.val.p 𝒳.val.val.p
                  (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                    Pr.basedFunctor.w).toFunctor f.hom.hom.toFunctor) ⥤ᵇ
                BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor
                  (fibredCategory B S hS Pr.groupoid.objects.obj).val.p
                  (fullSubcategoryBased 𝒳 P.1).p 𝒳.val.val.p
                  (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                    Pr.basedFunctor.w).toFunctor
                  (fullSubcategoryBasedInclusion 𝒳 P.1).toFunctor),
              Nonempty (g.comp (TwoFibreProductOver.fstBased (fullSubcategoryBased 𝒳 P.1).p
                  𝒳.val.val.p (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                    Pr.basedFunctor.w).toFunctor
                  (fullSubcategoryBasedInclusion 𝒳 P.1).toFunctor) ≅
                TwoFibreProductOver.fstBased 𝒴.val.val.p 𝒳.val.val.p
                  (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                    Pr.basedFunctor.w).toFunctor f.hom.hom.toFunctor)) ∧
          ((∃ g : 𝒴.val.val ⥤ᵇ fullSubcategoryBased 𝒳 P.1,
              Nonempty (g.comp (fullSubcategoryBasedInclusion 𝒳 P.1) ≅ f.hom.hom)) ↔
            ∀ d : TwoFibreProductOver (fibredCategory B S hS Pr.groupoid.objects.obj).val.p
                𝒴.val.val.p 𝒳.val.val.p
                (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                  Pr.basedFunctor.w).toFunctor f.hom.hom.toFunctor,
              d.x.fiber.as ∈ (e P).1.obj (op d.x.base)) :=
  exists_equiv_substackWith_presentation 𝒳 Pr
    (FormalSpace.isEffectiveDescentAlongCoveringSieve_isClosedImmersion B S hS)

/-- An open substack of `𝒳` is the same thing as a property of its objects cutting out a
`Q`-substack at the open immersions. -/
def OpenSubstack.equivIsSubstackWith :
    OpenSubstack 𝒳 ≃ {P : ObjectProperty 𝒳.val.val.obj //
      IsSubstackWith (@AlgebraicGeometry.IsOpenImmersion.{u}) 𝒳 P} where
  toFun V := ⟨V.property, V.strictlyFull, V.isAlgebraic, V.isOpenImmersion⟩
  invFun P := ⟨P.1, P.2.1, P.2.2.choose, P.2.2.choose_spec⟩
  left_inv _ := OpenSubstack.ext rfl
  right_inv _ := rfl

/-- **Stacks 0507**, open substacks. Let `[U/R] ⟶ 𝒳` be a presentation of an algebraic stack.
There is a canonical bijection from the open substacks `𝒵` of `𝒳` to the `R`-invariant open
subspaces of `U`, sending `𝒵` to `U ×_𝒳 𝒵`. Moreover, a 1-morphism `f : 𝒴 ⟶ 𝒳` of algebraic
stacks factors through `𝒵` if and only if `𝒴 ×_𝒳 U ⟶ U` factors through `U ×_𝒳 𝒵`.

Here `[U/R] ⟶ 𝒳` is a presentation of the algebraic stack `𝒳` (Stacks 04TI), and `π : U ⟶ 𝒳`
is the canonical projection followed by the equivalence. The bijection `e` sends `𝒵` to the
subspace of `U` that is the image of the projection `U ×_𝒳 𝒵 ⟶ U` from the 2-fibre product
(first conjunct). For every 1-morphism `f : 𝒴 ⟶ 𝒳` of algebraic stacks, `f` factors through `𝒵`
over the site and up to a 2-isomorphism exactly when the projection `𝒴 ×_𝒳 U ⟶ U` factors
through `U ×_𝒳 𝒵` (second conjunct), and exactly when the `U`-component of every object of
`𝒴 ×_𝒳 U` lies in `e 𝒵` (third conjunct), which is to say that `𝒴 ×_𝒳 U ⟶ U` factors through
the subspace `e 𝒵`. An `R`-invariant open subspace is one whose inverse image under the source
map is contained in its inverse image under the target map (Stacks 044F, part (1)). -/
@[stacks 0507 "open"]
theorem exists_equiv_isInvariantOpen_presentation :
    ∃ e : OpenSubstack 𝒳 ≃
        {Z : Subfunctor Pr.groupoid.objects.obj // IsInvariantOpen Pr.groupoid Z},
      ∀ P : OpenSubstack 𝒳,
        (∀ (T : BigFppfOver B S hS) (u : Pr.groupoid.objects.obj.obj (op T)),
          u ∈ (e P).1.obj (op T) ↔
            ∃ d : TwoFibreProductOver (fibredCategory B S hS Pr.groupoid.objects.obj).val.p
                (fullSubcategoryBased 𝒳 P.property).p 𝒳.val.val.p
                (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                  Pr.basedFunctor.w).toFunctor
                (fullSubcategoryBasedInclusion 𝒳 P.property).toFunctor,
              d.x = ⟨T, Discrete.mk u⟩) ∧
        ∀ (𝒴 : AlgebraicStacks.{u, w} B S hS) (f : 𝒴 ⟶ 𝒳),
          ((∃ g : 𝒴.val.val ⥤ᵇ fullSubcategoryBased 𝒳 P.property,
              Nonempty (g.comp (fullSubcategoryBasedInclusion 𝒳 P.property) ≅ f.hom.hom)) ↔
            ∃ g : BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor
                  (fibredCategory B S hS Pr.groupoid.objects.obj).val.p 𝒴.val.val.p 𝒳.val.val.p
                  (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                    Pr.basedFunctor.w).toFunctor f.hom.hom.toFunctor) ⥤ᵇ
                BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor
                  (fibredCategory B S hS Pr.groupoid.objects.obj).val.p
                  (fullSubcategoryBased 𝒳 P.property).p 𝒳.val.val.p
                  (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                    Pr.basedFunctor.w).toFunctor
                  (fullSubcategoryBasedInclusion 𝒳 P.property).toFunctor),
              Nonempty (g.comp (TwoFibreProductOver.fstBased (fullSubcategoryBased 𝒳 P.property).p
                  𝒳.val.val.p (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                    Pr.basedFunctor.w).toFunctor
                  (fullSubcategoryBasedInclusion 𝒳 P.property).toFunctor) ≅
                TwoFibreProductOver.fstBased 𝒴.val.val.p 𝒳.val.val.p
                  (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                    Pr.basedFunctor.w).toFunctor f.hom.hom.toFunctor)) ∧
          ((∃ g : 𝒴.val.val ⥤ᵇ fullSubcategoryBased 𝒳 P.property,
              Nonempty (g.comp (fullSubcategoryBasedInclusion 𝒳 P.property) ≅ f.hom.hom)) ↔
            ∀ d : TwoFibreProductOver (fibredCategory B S hS Pr.groupoid.objects.obj).val.p
                𝒴.val.val.p 𝒳.val.val.p
                (presentationProjection Pr.groupoid Pr.basedFunctor.toFunctor
                  Pr.basedFunctor.w).toFunctor f.hom.hom.toFunctor,
              d.x.fiber.as ∈ (e P).1.obj (op d.x.base)) := by
  obtain ⟨e, he⟩ := exists_equiv_substackWith_presentation 𝒳 Pr
    (Space.isEffectiveDescentAlongCoveringSieve_isOpenImmersion B S hS)
  refine ⟨(OpenSubstack.equivIsSubstackWith 𝒳).trans (e.trans (Equiv.subtypeEquivRight
    fun Z => ⟨fun h => ⟨h.1, h.2.symm.le⟩, fun h => ⟨h.1,
      preimage_target_eq_of_preimage_source_le Pr.groupoid Pr.basedFunctor.toFunctor
        Pr.basedFunctor.w Z h.2⟩⟩)), fun V => he ((OpenSubstack.equivIsSubstackWith 𝒳) V)⟩

end Correspondence

end AlgebraicGeometry.Stack

end
