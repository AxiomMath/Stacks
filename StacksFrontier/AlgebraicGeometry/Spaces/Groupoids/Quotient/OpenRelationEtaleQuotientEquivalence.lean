module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.OpenRelationEtaleQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.CoveringMap
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategoryStack
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackEquivalence
public import StacksFrontier.CategoryTheory.Sites.Stackification.Uniqueness
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyUniqueness

/-!
# The comparison `[U/R] ⟶ U/R` of an open relation is an equivalence (Stacks 0DU1)

Let `Y` be an algebraic space over a scheme `S` of a big fppf site, and let `(U, R, s, t, c)` be a
groupoid in algebraic spaces over `Y` whose object space is flat and locally of finite
presentation over `Y` and whose pre-relation `(t, s) : R ⟶ U ×_Y U` is an open immersion.
**Stacks 0DU1** asserts `X = [U/R] = U/R`; the comparison 1-morphism `[U/R] ⟶ U/R` is
`AlgebraicGeometry.Stack.quotientStackToQuotientSheaf`, built in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/Quotient/OpenRelationEtaleQuotient.lean`.  This
file proves that comparison is an **equivalence**, which is the remaining half of the assertion.

Algebraicity of `U/R` is what the comparison itself needs in order to exist, and it is supplied
by `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_isOpenImmersion` from the
hypotheses of Stacks 0DU1; that is the only place where Stacks 04S6, flatness and local finite
presentation of the object space enter.

## The argument

The quotient stack is the stackification of the pointwise groupoid fibration
`AlgebraicGeometry.Stack.quotientPrestack` of Stacks 044Q, and the comparison is, by
construction, the extension of the quotient map along that stackification
(`AlgebraicGeometry.Stack.liftedQuotientStackOfInvariant`).  So the triangle

`quotientPrestack ⟶ [U/R] ⟶ U/R`

is a stackification followed by a 1-morphism into a stack, and the comparison is an equivalence
as soon as the *composite* is fully faithful and locally essentially surjective on fibres:

* **Full faithfulness of the composite.**  The composite is 2-isomorphic to
  `AlgebraicGeometry.Stack.prestackOfInvariant`, that is to the invariant morphism read on the
  pointwise groupoid fibration, and that functor is fully faithful exactly because the arrow
  space is the fibre square of the quotient map, `R = U ×_{U/R} U`.  That square is Stacks 06PG,
  `AlgebraicGeometry.Space.isPullback_toQuotientSheaf`, and the open immersion hypothesis is what
  makes the pre-relation an equivalence relation so that it applies.  Fullness reads a section of
  the fibre square as an arrow of the groupoid; faithfulness is the monomorphism half of the same
  square.
* **Local essential surjectivity on fibres.**  A section of `U/R` over a test object lifts to the
  object space along a covering sieve, because the quotient map `U ⟶ U/R` is locally surjective
  (`AlgebraicGeometry.Space.isLocallySurjective_toQuotientSheaf`), and the fibres of the fibred
  category of `U/R` are discrete, so the lift is an equality of objects rather than merely an
  isomorphism.

Both inputs are then fed to the universal property of the stackification, Stacks 0435/04W9: the
restriction functor along a stackification is fully faithful on morphism categories, so the
extension of the composite is a two-sided quasi-inverse of the comparison.

## Main results

* `AlgebraicGeometry.Stack.isEquivalence_quotientStackToQuotientSheaf`: the comparison
  `[U/R] ⟶ U/R` is an equivalence of categories.
* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_quotientStackToQuotientSheaf`:
  the comparison is an equivalence *over the big fppf site* — it has a
  quasi-inverse which is again strictly a 1-morphism over the site, with unit and counit
  vertical.  This is Stacks 003Z (2) applied to the previous result.
* `AlgebraicGeometry.Stack.isAlgebraicSpace_and_equivalenceOver_and_isEtale_of_isOpenImmersion`:
  **Stacks 0DU1** in full — `U/R` is an algebraic space, the comparison is an equivalence over the
  site, and `U/R ⟶ Y` is étale.

## Implementation notes

The universes are forced.  A stackification raises the morphism universe of its presentation, so
the quotient stack has morphisms in `u + 1` while the fibred category of an algebraic space has
morphisms in `u`.  The argument therefore runs on
`AlgebraicGeometry.Stack.liftedFibredCategory`, the fibred category of `U/R` with its morphisms
raised, which is exactly the shape in which the library already builds the comparison; the
comparison itself is that functor composed with
`AlgebraicGeometry.Stack.liftedFibredCategoryDown`, an equivalence, so being an equivalence
transfers between the two readings for free.

## References

* [Stacks Project, Tag 0DU1](https://stacks.math.columbia.edu/tag/0DU1)
* [Stacks Project, Tag 0435](https://stacks.math.columbia.edu/tag/0435)
* [Stacks Project, Tag 04W9](https://stacks.math.columbia.edu/tag/04W9)
* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u

section Stackification

universe vb vh va va' va'' vd

/-- **A 1-morphism out of a stackification is an equivalence once the composite with the
stackification is fully faithful and locally essentially surjective on fibres.**

Let `L : 𝒜 ⥤ ℬ` exhibit the stack `q` as the stackification of `p` (clauses `hmor` and `hobj` of
Stacks 02ZN) and let `H : ℬ ⥤ ℰ` be a 1-morphism of fibred categories into a stack `r`.  If
`L ⋙ H` is fully faithful and every object of a fibre of `r` is, along a covering sieve, in the
essential image of `L ⋙ H`, then `H` is an equivalence of categories.

This is the determinacy clause of Stacks 02ZN and 02ZP,
`CategoryTheory.Functor.Stackification.nonempty_isEquivalenceOver_of_locally_fullyFaithful`,
specialised to a *fully faithful* composite: full faithfulness makes the comparison of morphism
presheaves an isomorphism, hence locally bijective, which is the clause (1) that result asks of
the composite.  Only the conclusion is weakened, from an equivalence over the base to an
equivalence of the underlying categories, which is all this file consumes. -/
private theorem isEquivalence_of_stackification_composite
    {D : Type vd} [Category.{vb} D]
    {A : Type va} [Category.{vh} A] {B : Type va'} [Category.{vh} B]
    {E : Type va''} [Category.{vh} E]
    {p : A ⥤ D} {q : B ⥤ D} {r : E ⥤ D}
    [p.IsFibered] [q.IsFibered] [r.IsFibered]
    {J : GrothendieckTopology D} {L : A ⥤ B} {H : B ⥤ E}
    (hL : p.IsFibredOneMorphism q L) (hH : q.IsFibredOneMorphism r H)
    (hq : q.IsStack J) (hr : r.IsStack J)
    (hmor : ∀ (U : D) (x y : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hL.morPresheafMap x y) ∧
        Presheaf.IsLocallySurjective (J.over U) (hL.morPresheafMap x y))
    (hobj : ∀ (U : D) (x : q.Fiber U), ∃ R ∈ J U, ∀ ⦃V : D⦄ ⦃f : V ⟶ U⦄,
      R.arrows f → (Functor.fiberFunctorOfCompEq hL.comp_eq V).essImage
        (Functor.pullbackFiber q x f))
    [(L ⋙ H).Full] [(L ⋙ H).Faithful]
    (hcompobj : ∀ (U : D) (x : r.Fiber U), ∃ R ∈ J U, ∀ ⦃V : D⦄ ⦃f : V ⟶ U⦄,
      R.arrows f → (Functor.fiberFunctorOfCompEq (hL.comp hH).comp_eq V).essImage
        (Functor.pullbackFiber r x f)) : H.IsEquivalence := by
  have hFmor (U : D) (x y : p.Fiber U) :
      Presheaf.IsLocallyInjective (J.over U) ((hL.comp hH).morPresheafMap x y) ∧
        Presheaf.IsLocallySurjective (J.over U) ((hL.comp hH).morPresheafMap x y) := by
    have := Comma.isIso_morPresheafMap_of_fullyFaithful (hL.comp hH) (U := U) x y
    exact ⟨inferInstance, inferInstance⟩
  obtain ⟨e⟩ := Functor.Stackification.nonempty_isEquivalenceOver_of_locally_fullyFaithful
    hL hH J hmor hobj hFmor hcompobj hq hr
  exact (CategoryTheory.Equivalence.mk H e.inv e.unitIso.symm e.counitIso).isEquivalence_functor

end Stackification

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-! ### Full faithfulness of an invariant morphism whose relation is its own fibre square -/

/-- **An invariant morphism whose relation is its own fibre square is fully faithful on the
pointwise groupoid fibration.**  Let `φ : U ⟶ F` identify the source and the target of a groupoid
in algebraic spaces, and suppose the square cut out by the source and the target of the groupoid
is the fibre square of `φ` with itself, `R = U ×_F U`.  Then
`AlgebraicGeometry.Stack.pointwiseOfInvariant` is full and faithful.

Fullness: a morphism of the fibred category of `F` between the images of two objects `x`, `y` of
the pointwise groupoid over a test object `T` is a morphism `T' ⟶ T` of the site together with the
equality `φ(x) = φ(y|_{T'})` of sections of `F`; the fibre square turns that equality into a
section of the arrow space with source `x` and target `y|_{T'}`, which is an arrow of the
evaluated groupoid by Stacks 044P.  Faithfulness: two arrows with the same source and the same
target are named by two sections of the arrow space agreeing after the source and the target
maps, hence are equal because the comparison into the fibre square is a monomorphism. -/
private theorem fullyFaithful_pointwiseOfInvariant
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (φ : G.objects.obj ⟶ F)
    (hφ : G.target.hom ≫ φ = G.source.hom ≫ φ)
    (hpb : IsPullback G.source.hom G.target.hom φ φ) :
    (pointwiseOfInvariant G φ hφ).toFunctor.Full ∧
      (pointwiseOfInvariant G φ hφ).toFunctor.Faithful := by
  let K := G.toGroupoidInFunctors
  have hval {T : BigFppfOver C S hS} {a b : G.arrows.obj.obj (op T)}
      (hs : G.source.hom.app (op T) a = G.source.hom.app (op T) b)
      (ht : G.target.hom.app (op T) a = G.target.hom.app (op T) b) : a = b := by
    apply yonedaEquiv.symm.injective
    apply hpb.hom_ext
    · apply yonedaEquiv.injective
      simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using hs
    · apply yonedaEquiv.injective
      simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using ht
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · intro x y η
    let a : yoneda.obj x.base ⟶ G.objects.obj := yonedaEquiv.symm x.fiber
    let b : yoneda.obj x.base ⟶ G.objects.obj :=
      yonedaEquiv.symm (G.objects.obj.map η.base.op y.fiber)
    have hya : yonedaEquiv a = x.fiber := Equiv.apply_symm_apply _ _
    have hyb : yonedaEquiv b = G.objects.obj.map η.base.op y.fiber :=
      Equiv.apply_symm_apply _ _
    have hab : a ≫ φ = b ≫ φ := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp, hya, hyb]
      have he := Discrete.eq_of_hom η.fiber
      change φ.app (op x.base) x.fiber =
        F.map η.base.op (φ.app (op y.base) y.fiber) at he
      exact he.trans (φ.naturality_apply η.base.op y.fiber).symm
    let r := yonedaEquiv (hpb.lift a b hab)
    have hs : K.source.app (op x.base) r = x.fiber := by
      have h := congrArg yonedaEquiv (hpb.lift_fst a b hab)
      rwa [yonedaEquiv_comp, hya] at h
    have ht : K.target.app (op x.base) r = K.objects.map η.base.op y.fiber := by
      have h := congrArg yonedaEquiv (hpb.lift_snd a b hab)
      rwa [yonedaEquiv_comp, hyb] at h
    let ψ : x ⟶ y := ⟨η.base,
      (K.evaluationArrowEquiv (op x.base) _ _).symm ⟨r, hs, ht⟩⟩
    refine ⟨ψ, ?_⟩
    apply Pseudofunctor.CoGrothendieck.Hom.ext
      (F := ((F ⋙ CategoryTheory.typeToGrpd) ⋙ Grpd.forgetToCat).toPseudofunctor')
      ((pointwiseOfInvariant G φ hφ).toFunctor.map ψ) η rfl
    exact Discrete.hom_eq
  · intro x y α β h
    have hbase : α.base = β.base := congrArg (fun η => η.base) h
    rcases α with ⟨a, α⟩
    rcases β with ⟨b, β⟩
    obtain rfl : a = b := hbase
    obtain rfl : α = β := by
      apply (K.evaluationArrowEquiv (op x.base) _ _).injective
      apply Subtype.ext
      apply hval
      · exact (K.evaluationArrowEquiv _ _ _ α).property.1.trans
          (K.evaluationArrowEquiv _ _ _ β).property.1.symm
      · exact (K.evaluationArrowEquiv _ _ _ α).property.2.trans
          (K.evaluationArrowEquiv _ _ _ β).property.2.symm
    rfl

/-! ### The fibres of the universe-enlarged fibred category of an algebraic space -/

/-- The universe-enlarged fibred category of an algebraic space is a fibred category: raising the
morphism universe preserves being fibred in groupoids. -/
private instance isFibered_liftedFibredCategory (X : AlgebraicSpaces C S hS) :
    (liftedFibredCategory X).p.IsFibered :=
  (isFiberedInGroupoids_uliftHom _ (fibredCategory C S hS X.obj).property).isFibered

/-- The fibre of the universe-enlarged fibred category of an algebraic space `X` over a test
object `U` is `X(U)`: raising the morphism universe leaves the objects, hence the fibres, alone. -/
private def liftedFiberEquiv (X : AlgebraicSpaces C S hS) (U : BigFppfOver C S hS) :
    (liftedFibredCategory X).p.Fiber U ≃ X.obj.obj (op U) :=
  (show (liftedFibredCategory X).p.Fiber U ≃
      (PresheafOfCategories.discreteProjection X.obj).Fiber U from Equiv.refl _).trans
    (PresheafOfCategories.discreteFiberEquiv X.obj U)

/-- The section of `X` named by an object of a fibre is compatible with restriction: the chosen
pullback of an object of the fibre over `U` along `f : V ⟶ U` names the restriction along `f` of
the section it named. -/
private theorem liftedFiberEquiv_pullbackFiber (X : AlgebraicSpaces C S hS)
    {U V : BigFppfOver C S hS} (f : V ⟶ U) (x : (liftedFibredCategory X).p.Fiber U) :
    liftedFiberEquiv X V (Functor.pullbackFiber (liftedFibredCategory X).p x f) =
      X.obj.map f.op (liftedFiberEquiv X U x) := by
  let pp := PresheafOfCategories.discreteProjection X.obj
  let r := (liftedFibredCategory X).p
  let ψ := Functor.IsPreFibered.pullbackMap (p := r) x.2 f
  have hlift : pp.IsHomLift f ψ.down :=
    IsHomLift.of_fac' pp f ψ.down (IsHomLift.domain_eq r f ψ)
      (IsHomLift.codomain_eq r f ψ) (IsHomLift.fac' r f ψ)
  exact PresheafOfCategories.discreteFiberEquiv_eq_map_of_isHomLift X.obj f
    (show pp.Fiber U from x) (show pp.Fiber V from Functor.pullbackFiber r x f) ψ.down hlift

/-! ### Stacks 0DU1: the canonical comparison is an equivalence -/

section Comparison

variable {Y : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS Y)
  (hflat : Space.IsFlat C S hS G.objectsToBase.hom)
  (hlfp : Space.IsLocallyOfFinitePresentation C S hS G.objectsToBase.hom)
  (hopen : Space.IsOpenImmersion C S hS (Space.groupoidPreRelation G).left)

/-- **The canonical comparison `[U/R] ⟶ U/R` is an equivalence of categories.**  Let
`(U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `Y` whose object space
is flat and locally of finite presentation over `Y` and whose pre-relation
`(t, s) : R ⟶ U ×_Y U` is an open immersion, so that the quotient sheaf `U/R` is an algebraic
space by `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_isOpenImmersion`.  Then the
comparison `AlgebraicGeometry.Stack.quotientStackToQuotientSheaf` of
Stacks 0DU1 is an equivalence.

See the module documentation for the shape of the argument. -/
theorem isEquivalence_quotientStackToQuotientSheaf :
    (quotientStackToQuotientSheaf G hflat hlfp hopen).toFunctor.IsEquivalence := by
  set X := quotientSheafSpace G hflat hlfp hopen
  set φ := quotientSheafProjection G hflat hlfp hopen
  have hφ : G.target ≫ φ = G.source ≫ φ :=
    target_comp_quotientSheafProjection G hflat hlfp hopen
  have hφ' : G.target.hom ≫ φ.hom = G.source.hom ≫ φ.hom :=
    hom_comp_eq_of_invariant G hφ
  -- The relation is the fibre square of the quotient map, Stacks 06PG.
  have hpb : IsPullback G.source.hom G.target.hom φ.hom φ.hom := by
    have h := Space.isPullback_toQuotientSheaf (Space.groupoidPreRelation G)
      (Space.isEquivalenceRelation_groupoidPreRelation_of_isOpenImmersion hopen)
      G.arrows.property.isSheaf G.objects.property.isSheaf
    rwa [groupoidPreRelation_source_left G, groupoidPreRelation_target_left G] at h
  -- The three functors of the triangle.
  let p := (quotientPrestack G).p
  let q := (quotientStack G).p
  let r := (liftedFibredCategory X).p
  let L := toQuotientStack G
  let H := liftedQuotientStackOfInvariant G φ hφ
  have hL : p.IsFibredOneMorphism q L := isFibredOneMorphism_toQuotientStack G
  have hH : q.IsFibredOneMorphism r H :=
    Functor.Stackification.extendGroupoid_isFibredOneMorphism
      (isFiberedInGroupoids_quotientPrestack G)
      (isFiberedInGroupoids_quotientStack G)
      (isStack_quotientStack G)
      (isFiberedInGroupoids_uliftHom _ (fibredCategory C S hS X.obj).property)
      (liftedFibredCategory_isStack X)
      (isFibredOneMorphism_toQuotientStack G).comp_eq
      (prestackOfInvariant G φ hφ).w
      (isLocallyBijective_toQuotientStack G)
      (essImage_toQuotientStack G)
  -- `L ⋙ H` is fully faithful: it is 2-isomorphic to the invariant morphism on the
  -- presentation, which is fully faithful because the relation is the fibre square.
  obtain ⟨_, _⟩ := fullyFaithful_pointwiseOfInvariant G φ.hom hφ' hpb
  have : (quotientPrestackDown G).toFunctor.IsEquivalence :=
    (quotientPrestackEquivalence G).isEquivalence_inverse
  let e : (fibredCategory C S hS X.obj).val.obj ≌
      ULiftHom.{u + 1} (fibredCategory C S hS X.obj).val.obj := ULiftHom.equiv
  have : (liftedFibredCategoryUp X).toFunctor.IsEquivalence := e.isEquivalence_functor
  have : (liftedFibredCategoryDown X).toFunctor.IsEquivalence := e.isEquivalence_inverse
  have hpf : (prestackOfInvariant G φ hφ).toFunctor =
      (quotientPrestackDown G).toFunctor ⋙
        (pointwiseOfInvariant G φ.hom hφ').toFunctor ⋙
          (liftedFibredCategoryUp X).toFunctor := rfl
  have : (prestackOfInvariant G φ hφ).toFunctor.Full := by rw [hpf]; infer_instance
  have : (prestackOfInvariant G φ hφ).toFunctor.Faithful := by rw [hpf]; infer_instance
  have : (L ⋙ H).Full := Functor.Full.of_iso (quotientStackOfInvariantUnit G φ hφ).symm
  have : (L ⋙ H).Faithful := Functor.Faithful.of_iso (quotientStackOfInvariantUnit G φ hφ).symm
  -- Every object of a fibre of the quotient sheaf comes, along a covering sieve, from the
  -- object space: the quotient map is locally surjective.
  have : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS) φ.hom :=
    Space.isLocallySurjective_toQuotientSheaf (Space.groupoidPreRelation G)
  have hcompobj : ∀ (U : BigFppfOver C S hS) (x : r.Fiber U),
      ∃ R ∈ BigFppfOver.topology C S hS U, ∀ ⦃V : BigFppfOver C S hS⦄ ⦃f : V ⟶ U⦄,
        R.arrows f → (Functor.fiberFunctorOfCompEq (hL.comp hH).comp_eq V).essImage
          (Functor.pullbackFiber r x f) := by
    intro U x
    let v := liftedFiberEquiv X U x
    refine ⟨Presheaf.imageSieve φ.hom v, Presheaf.imageSieve_mem _ φ.hom v, ?_⟩
    rintro V f ⟨t, ht⟩
    let z : p.Fiber V := ⟨(quotientPrestackEquivalence G).functor.obj ⟨V, t⟩, rfl⟩
    refine ⟨z, ⟨eqToIso ?_⟩⟩
    apply (liftedFiberEquiv X V).injective
    rwa [liftedFiberEquiv_pullbackFiber X f x,
      show (Functor.fiberFunctorOfCompEq (hL.comp hH).comp_eq V).obj z =
        (⟨⟨V, Discrete.mk (φ.hom.app (op V) t)⟩, rfl⟩ : r.Fiber V) from
      Subtype.ext (quotientStackOfInvariant_obj_toQuotientStack G φ hφ z.1)]
  -- The comparison, read in the enlarged universe, is an equivalence.
  have : H.IsEquivalence :=
    isEquivalence_of_stackification_composite hL hH (isStack_quotientStack G)
      (liftedFibredCategory_isStack X) (isLocallyBijective_toQuotientStack G)
      (essImage_toQuotientStack G) hcompobj
  exact Functor.isEquivalence_trans H (liftedFibredCategoryDown X).toFunctor

/-- **Stacks 0DU1, the canonical comparison is an equivalence over the site.**  Let
`(U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `Y` whose object space
is flat and locally of finite presentation over `Y` and whose pre-relation
`(t, s) : R ⟶ U ×_Y U` is an open immersion, so that the quotient sheaf `U/R` is an algebraic
space by `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_isOpenImmersion`, the first
clause of the tag.  Then the canonical comparison
`AlgebraicGeometry.Stack.quotientStackToQuotientSheaf` is an equivalence in the 2-category of
categories fibred in groupoids over the big fppf site: it admits a quasi-inverse which is again
strictly a 1-morphism over the site, and the unit and counit are vertical.

This is the remaining half of the assertion `X = [U/R] = U/R` of the source.  The equivalence is
asserted of the comparison already constructed, the subtype pinning its forward 1-morphism to be
that comparison; it is not a second, independently chosen 1-morphism.  Being an equivalence over
the site rather than merely an equivalence of categories is Stacks 003Z (2),
`CategoryTheory.Functor.IsFiberedInGroupoids.isEquivalence_over`, applied to
`AlgebraicGeometry.Stack.isEquivalence_quotientStackToQuotientSheaf`. -/
theorem nonempty_equivalenceOver_quotientStackToQuotientSheaf :
    Nonempty { e : StacksRepresentableCFG.EquivalenceOver (quotientStack G).p
        (fibredCategory C S hS (quotientSheafSpace G hflat hlfp hopen).obj).val.p //
      e.hom.functor = (quotientStackToQuotientSheaf G hflat hlfp hopen).toFunctor } := by
  -- Stacks 003Z (2): an equivalence of categories over the site has a quasi-inverse over it.
  obtain ⟨g, hg, η, ε, hη, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over (quotientStack G).p
      (fibredCategory C S hS (quotientSheafSpace G hflat hlfp hopen).obj).val.p
      (isFiberedInGroupoids_quotientStack G)
      (fibredCategory C S hS (quotientSheafSpace G hflat hlfp hopen).obj).property
      (quotientStackToQuotientSheaf G hflat hlfp hopen).toFunctor
      (quotientStackToQuotientSheaf G hflat hlfp hopen).w
      (isEquivalence_quotientStackToQuotientSheaf G hflat hlfp hopen)
  refine ⟨⟨{ hom := ⟨(quotientStackToQuotientSheaf G hflat hlfp hopen).toFunctor,
               (quotientStackToQuotientSheaf G hflat hlfp hopen).w⟩
             inv := ⟨g, hg⟩
             unitIso := η.symm
             counitIso := ε
             unit_over := ?_
             counit_over := ?_ }, rfl⟩⟩
  · refine NatTrans.ext ?_
    funext a
    have h1 : (quotientStack G).p.IsHomLift (𝟙 ((quotientStack G).p.obj a))
        (η.app a).hom := by simpa using hη a
    have : (quotientStack G).p.IsHomLift (𝟙 ((quotientStack G).p.obj a)) (η.inv.app a) :=
      IsHomLift.lift_id_inv (quotientStack G).p ((quotientStack G).p.obj a) (η.app a)
    simpa using IsHomLift.fac' (quotientStack G).p (𝟙 ((quotientStack G).p.obj a)) (η.inv.app a)
  · refine NatTrans.ext ?_
    funext a
    have := hε a
    simpa using IsHomLift.fac'
      (fibredCategory C S hS (quotientSheafSpace G hflat hlfp hopen).obj).val.p
      (𝟙 ((fibredCategory C S hS (quotientSheafSpace G hflat hlfp hopen).obj).val.p.obj a))
      (ε.hom.app a)

/-- **Stacks 0DU1.** Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic
space `Y` whose object space `U` is flat and locally of finite presentation over `Y` and whose
pre-relation `(t, s) : R ⟶ U ×_Y U` is an open immersion.  Then `X = [U/R] = U/R` is an algebraic
space and `X ⟶ Y` is étale: the quotient sheaf `U/R` of Stacks 044J is an algebraic space, the
canonical comparison `AlgebraicGeometry.Stack.quotientStackToQuotientSheaf` from the quotient
stack `[U/R]` to it is an equivalence over the big fppf site, and the structural morphism
`U/R ⟶ Y` is étale.

The three clauses are `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_isOpenImmersion`,
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_quotientStackToQuotientSheaf` and
`AlgebraicGeometry.Space.isEtale_quotientSheafToBase_of_isOpenImmersion`. -/
@[stacks 0DU1]
theorem isAlgebraicSpace_and_equivalenceOver_and_isEtale_of_isOpenImmersion :
    IsAlgebraicSpace C S hS (Space.quotientSheaf (Space.groupoidPreRelation G)).obj ∧
      Nonempty { e : StacksRepresentableCFG.EquivalenceOver (quotientStack G).p
          (fibredCategory C S hS (quotientSheafSpace G hflat hlfp hopen).obj).val.p //
        e.hom.functor = (quotientStackToQuotientSheaf G hflat hlfp hopen).toFunctor } ∧
      Space.IsEtale C S hS
        (Space.quotientSheafToBase Y.property.isSheaf (Space.groupoidPreRelation G)).hom :=
  ⟨Space.isAlgebraicSpace_quotientSheaf_of_isOpenImmersion hflat hlfp hopen,
    nonempty_equivalenceOver_quotientStackToQuotientSheaf G hflat hlfp hopen,
    Space.isEtale_quotientSheafToBase_of_isOpenImmersion hflat hlfp hopen⟩

end Comparison

end AlgebraicGeometry.Stack

end
