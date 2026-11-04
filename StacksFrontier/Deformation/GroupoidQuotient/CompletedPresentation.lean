module

public import StacksFrontier.CategoryTheory.Grothendieck.FibrewiseHom
public import StacksFrontier.Deformation.CofiberedPresentation.Existence
public import StacksFrontier.Deformation.FormalObject.Completion
public import StacksFrontier.Deformation.Groupoid.Smooth
public import StacksFrontier.Deformation.GroupoidQuotient.Realization
public import StacksFrontier.Deformation.SchlessingerConditions.SmoothMorphisms

/-!
# The completed presentation of a smoothly presented category (Stacks 0DR3, last equivalence)

Let `P` be a representable presentation on the category `𝒞^_Λ` of Noetherian complete local
`Λ`-algebras with residue field `k`, with object algebra `A` and arrow algebra `B`, and suppose its
restriction `(A|_{𝒞_Λ}, B|_{𝒞_Λ}, s, t, c)` to `𝒞_Λ` is a smooth groupoid in functors presenting a
category `𝓕` cofibred in groupoids over `𝒞_Λ`. Remark 0DR3 asserts that then the quotient
`[A/B]` is equivalent over `𝒞^_Λ` to the completion `𝓕^` (Stacks 06H3), "see discussion in
Formal Deformation Theory, Section 06KC as to why this works". This file proves it.

## Main definitions

* `Deformation.RepresentablePresentation.completionComparison`: the functor
  `[A/B] → [A|_{𝒞_Λ}/B|_{𝒞_Λ}]^` sending a point `A ⟶ R` to the formal object of its truncations
  `A ⟶ R/𝔪_R^{n+1}`.
* `Deformation.completionEquivalence`: the completion `𝓕^ ≌ 𝓖^` of an equivalence `𝓕 ≃ 𝓖` over
  `𝒞_Λ`, built from the two-functoriality of completion (Stacks 06H9).
* `Deformation.RepresentablePresentation.completedPresentation`: the equivalence `[A/B] ≃ 𝓕^` over
  `𝒞^_Λ`.

## Main results

* The comparison functor is faithful and full: a morphism of `[A/B]` is an arrow `B ⟶ S`, and a
  morphism of complete local algebras is determined by, and can be assembled from, a compatible
  family of morphisms into the truncations of its target (Stacks 06HE).
* `Deformation.RepresentablePresentation.completionComparison_essSurj`: it is essentially
  surjective when the restriction of `P` is smooth.

## Implementation notes

Essential surjectivity is a rectification. A formal object of `[A|_{𝒞_Λ}/B|_{𝒞_Λ}]` over `R` is a
family of points `z_n : A ⟶ R/𝔪^{n+1}` together with isomorphisms `z_{n+1}|_{R/𝔪^{n+1}} ≅ z_n`,
that is arrows `B ⟶ R/𝔪^{n+1}`; it need not be a compatible family. Smoothness of the source
projection lifts, along the surjection `R/𝔪^{n+2} ⟶ R/𝔪^{n+1}`, the composite of the transition
isomorphism with the isomorphism `z_n ≅ x_n` already constructed, which yields isomorphisms
`z_n ≅ x_n` onto a compatible family `x_n`; completeness of `R` assembles the `x_n` into a point
`A ⟶ R`, and the isomorphisms into an isomorphism of formal objects (a vertical morphism of a
category cofibred in groupoids, Stacks 06H4).
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace Deformation

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A morphism of complete local algebras is determined by its composites with the adic quotient
projections of its target. -/
theorem CompleteLocalAlgCat.hom_ext_of_quotientProjection
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} {f g : R ⟶ S}
    (h : ∀ n, f ≫ quotientProjection S n = g ≫ quotientProjection S n) : f = g :=
  (representableSectionEquiv R S).injective (AdicSection.ext h)

/-- A compatible family of morphisms into the adic truncations of `S` comes from a morphism
into `S`. -/
theorem CompleteLocalAlgCat.exists_hom_of_compatible
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k}
    (z : ∀ n, R ⟶ artinianToComplete.obj (AdicTruncation.obj S n))
    (hz : ∀ n, z (n + 1) ≫ artinianToComplete.map (AdicTruncation.transition S n) = z n) :
    ∃ f : R ⟶ S, ∀ n, f ≫ quotientProjection S n = z n := by
  refine ⟨(representableSectionEquiv R S).symm ⟨z, hz⟩, fun n => ?_⟩
  exact congrArg (fun σ : AdicSection (restrictedCoyoneda R) S => σ.value n)
    ((representableSectionEquiv R S).apply_symm_apply ⟨z, hz⟩)

/-- The adic quotient projections, as a natural transformation from the identity of `𝒞^_Λ`. -/
def adicQuotientNat (n : ℕ) : 𝟭 (CompleteLocalAlgCat.{u, v, w} Λ k) ⟶
    AdicTruncation.functor n ⋙ artinianToComplete where
  app R := quotientProjection R n
  naturality R S f := (quotientProjection_naturality R S f n).symm

/-- The arrow represented by the transport of a morphism of an evaluated groupoid is the
transport of the arrow it represents. -/
theorem evaluationArrowEquiv_evaluationMap {C : Type*} [Category C]
    (G : GroupoidInFunctors C) {T S : C} (f : T ⟶ S) {x y : G.Evaluation T} (a : x ⟶ y) :
    (G.evaluationArrowEquiv S _ _ ((evaluationMap G f).map a)).1 =
      G.arrows.map f (G.evaluationArrowEquiv T x y a).1 := by
  change (G.evaluationArrowEquiv S _ _ ((G.evaluationArrowEquiv S _ _).symm _)).1 = _
  rw [Equiv.apply_symm_apply]

/-- `evaluationArrowEquiv_eqToHom_comp`, for morphisms of the fibre categories of the quotient. -/
theorem evaluationArrowEquiv_eqToHom_comp' {C : Type*} [Category C]
    (G : GroupoidInFunctors C) (T : C) {x x' y : (evaluationFunctor G).obj T} (hx : x' = x)
    (a : x ⟶ y) :
    (G.evaluationArrowEquiv T x' y (eqToHom hx ≫ a)).1 = (G.evaluationArrowEquiv T x y a).1 := by
  cases hx
  simp

/-- The arrow represented by a composite of morphisms of a fibre category of the quotient is
unchanged by a trailing `eqToHom`. -/
theorem evaluationArrowEquiv_comp_comp_eqToHom' {C : Type*} [Category C]
    (G : GroupoidInFunctors C) (T : C) {x y z z' : (evaluationFunctor G).obj T} (a : x ⟶ y)
    (b : y ⟶ z) (hz : z = z') :
    (G.evaluationArrowEquiv T x z' (a ≫ b ≫ eqToHom hz)).1 =
      (G.evaluationArrowEquiv T x z (a ≫ b)).1 := by
  cases hz
  simp

/-- The arrow represented by the transport of a morphism followed by `eqToHom`s is the transport
of the arrow it represents. -/
theorem evaluationArrowEquiv_map_comp_eqToHom_comp_eqToHom {C : Type*} [Category C]
    (G : GroupoidInFunctors C) {T S : C} (f : T ⟶ S) {x y y' : (evaluationFunctor G).obj T}
    (a : x ⟶ y) (h : y = y') {z : (evaluationFunctor G).obj S}
    (h' : ((evaluationFunctor G).map f).toFunctor.obj y' = z) :
    (G.evaluationArrowEquiv S _ z
        (((evaluationFunctor G).map f).toFunctor.map (a ≫ eqToHom h) ≫ eqToHom h')).1 =
      G.arrows.map f (G.evaluationArrowEquiv T x y a).1 := by
  subst h h'
  simp only [eqToHom_refl, Category.comp_id]
  exact evaluationArrowEquiv_evaluationMap G f a

/-- The arrow represented by the transport of a morphism of a fibre category of the quotient. -/
theorem evaluationArrowEquiv_map' {C : Type*} [Category C]
    (G : GroupoidInFunctors C) {T S : C} (f : T ⟶ S) {x y : (evaluationFunctor G).obj T}
    (a : x ⟶ y) :
    (G.evaluationArrowEquiv S _ _ (((evaluationFunctor G).map f).toFunctor.map a)).1 =
      G.arrows.map f (G.evaluationArrowEquiv T x y a).1 :=
  evaluationArrowEquiv_evaluationMap G f a

/-- The arrow represented by a transported morphism between two `eqToHom`s. -/
theorem evaluationArrowEquiv_eqToHom_comp_map_comp_eqToHom {C : Type*} [Category C]
    (G : GroupoidInFunctors C) {T S : C} (f : T ⟶ S) {x y : G.Evaluation T} (a : x ⟶ y)
    {z z' : G.Evaluation S} (h : z = ((evaluationFunctor G).map f).toFunctor.obj x)
    (h' : ((evaluationFunctor G).map f).toFunctor.obj y = z') :
    (G.evaluationArrowEquiv S z z'
        (eqToHom h ≫ ((evaluationFunctor G).map f).toFunctor.map a ≫ eqToHom h')).1 =
      G.arrows.map f (G.evaluationArrowEquiv T x y a).1 := by
  subst h h'
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact evaluationArrowEquiv_evaluationMap G f a

/-! ### Completion of an equivalence over `𝒞_Λ` -/

section CompletionEquivalence

universe uF vF uG vG

variable {F : Type uF} [Category.{vF} F] {G : Type uG} [Category.{vG} G]
  {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k} {q : G ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- The completion of an isomorphism of morphisms of categories over `𝒞_Λ`. -/
def completionIso {φ ψ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q)}
    (e : φ ≅ ψ) : completionMap φ ≅ completionMap ψ where
  hom := completionNatTrans e.hom
  inv := completionNatTrans e.inv
  hom_inv_id := by
    change BasedNatTrans.comp _ _ = _
    rw [← completionNatTrans_comp]
    change completionNatTrans (e.hom ≫ e.inv) = _
    rw [e.hom_inv_id]
    exact completionNatTrans_id φ
  inv_hom_id := by
    change BasedNatTrans.comp _ _ = _
    rw [← completionNatTrans_comp]
    change completionNatTrans (e.inv ≫ e.hom) = _
    rw [e.inv_hom_id]
    exact completionNatTrans_id ψ

/-- The forward morphism over `𝒞_Λ` of an equivalence over `𝒞_Λ`. -/
def _root_.StacksRepresentableCFG.EquivalenceOver.homBased
    (E : StacksRepresentableCFG.EquivalenceOver p q) :
    BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q) :=
  ⟨E.hom.functor, E.hom.w⟩

/-- The backward morphism over `𝒞_Λ` of an equivalence over `𝒞_Λ`. -/
def _root_.StacksRepresentableCFG.EquivalenceOver.invBased
    (E : StacksRepresentableCFG.EquivalenceOver p q) :
    BasedFunctor (BasedCategory.ofFunctor q) (BasedCategory.ofFunctor p) :=
  ⟨E.inv.functor, E.inv.w⟩

omit [Algebra Λ k] in
private theorem isHomLift_id_of_map_eq_eqToHom {X : Type*} [Category X] {C : Type*} [Category C]
    (r : X ⥤ C) {a b : X} (φ : a ⟶ b) {c : C} (ha : r.obj a = c) (hb : r.obj b = c)
    (hφ : r.map φ = eqToHom (ha.trans hb.symm)) : r.IsHomLift (𝟙 c) φ :=
  IsHomLift.of_fac' r _ φ ha hb (by simp [hφ])

/-- An isomorphism of morphisms of based categories, read on the underlying functors. -/
def _root_.CategoryTheory.BasedNatIso.toFunctorIso {𝒮 : Type*} [Category 𝒮]
    {𝒳 𝒴 : BasedCategory 𝒮} {φ ψ : BasedFunctor 𝒳 𝒴} (e : φ ≅ ψ) :
    φ.toFunctor ≅ ψ.toFunctor where
  hom := e.hom.toNatTrans
  inv := e.inv.toNatTrans
  hom_inv_id := congrArg BasedNatTrans.toNatTrans e.hom_inv_id
  inv_hom_id := congrArg BasedNatTrans.toNatTrans e.inv_hom_id

/-- The unit of an equivalence over `𝒞_Λ`, as a vertical natural isomorphism. -/
def unitBasedIso (E : StacksRepresentableCFG.EquivalenceOver p q) :
    BasedFunctor.id (BasedCategory.ofFunctor p) ≅ E.homBased.comp E.invBased :=
  BasedNatIso.mkNatIso (NatIso.ofComponents (fun a => E.unitIso.app a)
      (fun f => E.unitIso.hom.naturality f)) fun a => by
    exact isHomLift_id_of_map_eq_eqToHom p (E.unitIso.hom.app a) rfl
      (Functor.congr_obj (show (E.hom.functor ⋙ E.inv.functor) ⋙ p = p by
        rw [Functor.assoc, E.inv.w, E.hom.w]) a)
      ((NatTrans.congr_app E.unit_over a).trans (eqToHom_app _ a))

/-- The counit of an equivalence over `𝒞_Λ`, as a vertical natural isomorphism. -/
def counitBasedIso (E : StacksRepresentableCFG.EquivalenceOver p q) :
    E.invBased.comp E.homBased ≅ BasedFunctor.id (BasedCategory.ofFunctor q) :=
  BasedNatIso.mkNatIso (NatIso.ofComponents (fun a => E.counitIso.app a)
      (fun f => E.counitIso.hom.naturality f)) fun a => by
    exact isHomLift_id_of_map_eq_eqToHom q (E.counitIso.hom.app a)
      (Functor.congr_obj (show (E.inv.functor ⋙ E.hom.functor) ⋙ q = q by
        rw [Functor.assoc, E.hom.w, E.inv.w]) a) rfl
      ((NatTrans.congr_app E.counit_over a).trans (eqToHom_app _ a))

/-- **The completion of an equivalence over `𝒞_Λ` is an equivalence of categories of formal
objects.** -/
def completionEquivalence (E : StacksRepresentableCFG.EquivalenceOver p q) :
    FormalObject p ≌ FormalObject q :=
  CategoryTheory.Equivalence.mk (completionMap E.homBased).toFunctor
    (completionMap E.invBased).toFunctor
    (BasedNatIso.toFunctorIso (completionIso (unitBasedIso E)) ≪≫
      eqToIso (congrArg BasedFunctor.toFunctor (completionMap_comp E.homBased E.invBased)))
    (eqToIso (congrArg BasedFunctor.toFunctor (completionMap_comp E.invBased E.homBased)).symm ≪≫
      BasedNatIso.toFunctorIso (completionIso (counitBasedIso E)))

/-- The functor of `completionEquivalence E` is the completion of the forward morphism of `E`. -/
theorem completionEquivalence_functor (E : StacksRepresentableCFG.EquivalenceOver p q) :
    (completionEquivalence E).functor = (completionMap E.homBased).toFunctor := rfl

end CompletionEquivalence

namespace RepresentablePresentation

variable (P : RepresentablePresentation.{_, v, v} (CompleteLocalAlgCat.{u, v, w} Λ k))

/-- The `n`-th adic truncation functor of the quotient `[A/B]` over `𝒞^_Λ` of a representable
presentation into the quotient `[A|_{𝒞_Λ}/B|_{𝒞_Λ}]` of its restriction: a point `x : A ⟶ R`
goes to its composite with `R ⟶ R/𝔪_R^{n+1}`. -/
def truncationFunctor (n : ℕ) :
    Grothendieck (evaluationFunctor P.groupoidInFunctors) ⥤
      Grothendieck (evaluationFunctor
        (GroupoidInFunctors.restrict P.groupoidInFunctors artinianToComplete)) :=
  Grothendieck.map (Functor.whiskerRight (adicQuotientNat n)
      (evaluationFunctor P.groupoidInFunctors) :
      evaluationFunctor P.groupoidInFunctors ⟶
        AdicTruncation.functor n ⋙ artinianToComplete ⋙ evaluationFunctor P.groupoidInFunctors) ⋙
    Grothendieck.pre (artinianToComplete ⋙ evaluationFunctor P.groupoidInFunctors)
      (AdicTruncation.functor n)

/-- The fibre component of the `n`-th truncation of a morphism `f` is, up to an `eqToHom`, the
transport of the fibre component of `f` along `R ⟶ R/𝔪_R^{n+1}`. -/
theorem truncationFunctor_map_fiber (n : ℕ)
    {X Y : Grothendieck (evaluationFunctor P.groupoidInFunctors)} (f : X ⟶ Y) :
    ∃ h, ((P.truncationFunctor n).map f).fiber =
      eqToHom h ≫ ((evaluationFunctor P.groupoidInFunctors).map
        (quotientProjection Y.base n)).toFunctor.map f.fiber :=
  ⟨_, by
    change (eqToHom (((Functor.whiskerRight (adicQuotientNat n)
      (evaluationFunctor P.groupoidInFunctors)).naturality f.base).symm)).toNatTrans.app X.fiber ≫
      (evaluationMap P.groupoidInFunctors (quotientProjection Y.base n)).map f.fiber = _
    rw [Cat.eqToHom_app]
    rfl⟩

/-- Two morphisms of a quotient category with equal base components are equal as soon as the
arrows representing their fibre components agree. -/
theorem _root_.Deformation.grothendieck_hom_ext_of_arrow {C : Type*} [Category C]
    {G : GroupoidInFunctors C} {X Y : Grothendieck (evaluationFunctor G)} (f g : X ⟶ Y)
    (hb : f.base = g.base)
    (he : (G.evaluationArrowEquiv _ _ _ f.fiber).1 = (G.evaluationArrowEquiv _ _ _ g.fiber).1) :
    f = g := by
  refine Grothendieck.ext f g hb ((G.evaluationArrowEquiv _ _ _).injective (Subtype.ext ?_))
  rwa [evaluationArrowEquiv_eqToHom_comp']

/-- The arrow represented by the fibre component of the truncation of a morphism is the
truncation of the arrow represented by its fibre component. -/
theorem truncationFunctor_map_fiber_arrow (n : ℕ)
    {X Y : Grothendieck (evaluationFunctor P.groupoidInFunctors)} (f : X ⟶ Y) :
    ((GroupoidInFunctors.restrict P.groupoidInFunctors artinianToComplete).evaluationArrowEquiv
        _ _ _ ((P.truncationFunctor n).map f).fiber).1 =
      P.groupoidInFunctors.arrows.map (quotientProjection Y.base n)
        (P.groupoidInFunctors.evaluationArrowEquiv _ _ _ f.fiber).1 := by
  obtain ⟨h, hf⟩ := P.truncationFunctor_map_fiber n f
  rw [hf]
  exact (evaluationArrowEquiv_eqToHom_comp' P.groupoidInFunctors
    (artinianToComplete.obj (AdicTruncation.obj Y.base n)) h _).trans
    (evaluationArrowEquiv_map' _ _ _)

/-- Transporting the `(n+1)`-st truncation of a point along `R/𝔪_R^{n+2} ⟶ R/𝔪_R^{n+1}` gives its
`n`-th truncation. -/
theorem truncationTransition_fiber_eq (n : ℕ)
    (X : Grothendieck (evaluationFunctor P.groupoidInFunctors)) :
    ((evaluationFunctor (GroupoidInFunctors.restrict P.groupoidInFunctors artinianToComplete)).map
        (AdicTruncation.transition X.base n)).toFunctor.obj
          ((P.truncationFunctor (n + 1)).obj X).fiber =
      ((P.truncationFunctor n).obj X).fiber := by
  change ULift.up ((X.fiber.down ≫ quotientProjection X.base (n + 1)) ≫
    artinianToComplete.map (AdicTruncation.transition X.base n)) =
    ULift.up (X.fiber.down ≫ quotientProjection X.base n)
  rw [Category.assoc, quotientProjection_transition]

/-- The transition from the `(n+1)`-st to the `n`-th truncation of a point. -/
def truncationTransition (n : ℕ) (X : Grothendieck (evaluationFunctor P.groupoidInFunctors)) :
    (P.truncationFunctor (n + 1)).obj X ⟶ (P.truncationFunctor n).obj X :=
  ⟨AdicTruncation.transition X.base n, eqToHom (P.truncationTransition_fiber_eq n X)⟩

/-- A morphism of a Grothendieck construction whose base component is `f` up to the
identifications of its endpoints lifts `f`. -/
theorem _root_.Deformation.grothendieck_isHomLift_of_base {C : Type*} [Category C]
    {F : C ⥤ Cat} {X Y : Grothendieck F} {R S : C} (f : R ⟶ S) (φ : X ⟶ Y) (hX : X.base = R)
    (hY : Y.base = S) (h : φ.base = eqToHom hX ≫ f ≫ eqToHom hY.symm) :
    (Grothendieck.forget F).IsHomLift f φ := by
  subst hX hY
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  subst h
  exact IsHomLift.map _ φ

/-- A morphism of a Grothendieck construction lifting `f` has base component `f`. -/
theorem _root_.Deformation.grothendieck_base_eq_of_isHomLift {C : Type*} [Category C]
    {F : C ⥤ Cat} {X Y : Grothendieck F} (φ : X ⟶ Y) (f : X.base ⟶ Y.base)
    (h : (Grothendieck.forget F).IsHomLift f φ) : φ.base = f :=
  (@IsHomLift.eq_of_isHomLift _ _ _ _ (Grothendieck.forget F) X Y f φ h).symm

/-- The arrow represented by the fibre component of a morphism of the quotient of a groupoid in
functors. -/
def _root_.Deformation.fiberArrow {C : Type*} [Category C] {G : GroupoidInFunctors C}
    {X Y : Grothendieck (evaluationFunctor G)} (φ : X ⟶ Y) : G.arrows.obj Y.base :=
  (G.evaluationArrowEquiv _ _ _ φ.fiber).1

/-- Precomposing with a morphism whose fibre component is an `eqToHom` does not change the
represented arrow. -/
theorem _root_.Deformation.fiberArrow_comp_of_eqToHom_left {C : Type*} [Category C]
    {G : GroupoidInFunctors C} {X Y Z : Grothendieck (evaluationFunctor G)} (φ : X ⟶ Y)
    (ψ : Y ⟶ Z) (h : ((evaluationFunctor G).map φ.base).toFunctor.obj X.fiber = Y.fiber)
    (hφ : φ.fiber = eqToHom h) : fiberArrow (φ ≫ ψ) = fiberArrow ψ := by
  simp only [fiberArrow, Grothendieck.comp_fiber, hφ, eqToHom_map, eqToHom_trans_assoc]
  exact evaluationArrowEquiv_eqToHom_comp' G _ _ _

/-- Postcomposing with a morphism whose fibre component is an `eqToHom` transports the represented
arrow along its base component. -/
theorem _root_.Deformation.fiberArrow_comp_of_eqToHom_right {C : Type*} [Category C]
    {G : GroupoidInFunctors C} {X Y Z : Grothendieck (evaluationFunctor G)} (φ : X ⟶ Y)
    (ψ : Y ⟶ Z) (h : ((evaluationFunctor G).map ψ.base).toFunctor.obj Y.fiber = Z.fiber)
    (hψ : ψ.fiber = eqToHom h) :
    fiberArrow (φ ≫ ψ) = G.arrows.map ψ.base (fiberArrow φ) := by
  simp only [fiberArrow, Grothendieck.comp_fiber, hψ]
  exact evaluationArrowEquiv_eqToHom_comp_map_comp_eqToHom G _ _ _ _

/-- The arrow represented by the `n`-th truncation of a morphism `f` is the arrow of `f` composed
with `R ⟶ R/𝔪_R^{n+1}`. -/
theorem fiberArrow_truncationFunctor_map (n : ℕ)
    {X Y : Grothendieck (evaluationFunctor P.groupoidInFunctors)} (f : X ⟶ Y) :
    fiberArrow ((P.truncationFunctor n).map f) =
      ULift.up ((fiberArrow f).down ≫ quotientProjection Y.base n) :=
  P.truncationFunctor_map_fiber_arrow n f

/-- Precomposing with a truncation transition does not change the represented arrow. -/
theorem fiberArrow_truncationTransition_comp (n : ℕ)
    {X : Grothendieck (evaluationFunctor P.groupoidInFunctors)}
    {Z : Grothendieck (evaluationFunctor
      (GroupoidInFunctors.restrict P.groupoidInFunctors artinianToComplete))}
    (ψ : (P.truncationFunctor n).obj X ⟶ Z) :
    fiberArrow (P.truncationTransition n X ≫ ψ) = fiberArrow ψ :=
  fiberArrow_comp_of_eqToHom_left _ _ (P.truncationTransition_fiber_eq n X) rfl

/-- Postcomposing with a truncation transition composes the represented arrow with
`R/𝔪_R^{n+2} ⟶ R/𝔪_R^{n+1}`. -/
theorem fiberArrow_comp_truncationTransition (n : ℕ)
    {Y : Grothendieck (evaluationFunctor P.groupoidInFunctors)}
    {Z : Grothendieck (evaluationFunctor
      (GroupoidInFunctors.restrict P.groupoidInFunctors artinianToComplete))}
    (φ : Z ⟶ (P.truncationFunctor (n + 1)).obj Y) :
    fiberArrow (φ ≫ P.truncationTransition n Y) =
      ULift.up ((fiberArrow φ).down ≫
        artinianToComplete.map (AdicTruncation.transition Y.base n)) :=
  fiberArrow_comp_of_eqToHom_right _ _ (P.truncationTransition_fiber_eq n Y) rfl

/-- The truncation transition as an explicit morphism of the Grothendieck construction. -/
theorem truncationTransition_eq (n : ℕ)
    (X : Grothendieck (evaluationFunctor P.groupoidInFunctors)) :
    P.truncationTransition n X = Grothendieck.Hom.mk (X := (P.truncationFunctor (n + 1)).obj X)
      (Y := (P.truncationFunctor n).obj X) (AdicTruncation.transition X.base n)
      (eqToHom (P.truncationTransition_fiber_eq n X)) := rfl

/-- The truncation transitions are natural in the point. -/
theorem truncationTransition_naturality (n : ℕ)
    {X Y : Grothendieck (evaluationFunctor P.groupoidInFunctors)} (f : X ⟶ Y) :
    P.truncationTransition n X ≫ (P.truncationFunctor n).map f =
      (P.truncationFunctor (n + 1)).map f ≫ P.truncationTransition n Y := by
  refine grothendieck_hom_ext_of_arrow _ _
    ((AdicTruncation.transitionNat n).naturality f.base).symm ?_
  change fiberArrow _ = fiberArrow _
  rw [fiberArrow_truncationTransition_comp, fiberArrow_comp_truncationTransition,
    fiberArrow_truncationFunctor_map, fiberArrow_truncationFunctor_map]
  exact ULift.ext _ _ ((Category.assoc _ _ _).trans
    (congrArg _ (quotientProjection_transition Y.base n))).symm

/-- The comparison functor `[A/B] → [A|_{𝒞_Λ}/B|_{𝒞_Λ}]^` over `𝒞^_Λ`: a point `x : A ⟶ R` goes
to the formal object of its truncations `A ⟶ R/𝔪_R^{n+1}`, a morphism to the formal object
morphism of its truncations. -/
def completionComparison :
    Grothendieck (evaluationFunctor P.groupoidInFunctors) ⥤
      FormalObject (Grothendieck.forget (evaluationFunctor
        (GroupoidInFunctors.restrict P.groupoidInFunctors artinianToComplete))) where
  obj X :=
    { base := X.base
      level := fun n => (P.truncationFunctor n).obj X
      level_eq := fun _ => rfl
      transition := fun n => P.truncationTransition n X
      transition_lift := fun n => IsHomLift.map _ (P.truncationTransition n X) }
  map f :=
    { base := f.base
      app := fun n => (P.truncationFunctor n).map f
      app_lift := fun n => IsHomLift.map _ ((P.truncationFunctor n).map f)
      naturality := fun n => P.truncationTransition_naturality n f }
  map_id X := FormalObject.Hom.ext rfl (fun n => (P.truncationFunctor n).map_id X)
  map_comp f g := FormalObject.Hom.ext rfl (fun n => (P.truncationFunctor n).map_comp f g)

/-- The comparison functor lies over `𝒞^_Λ`: composed with the projection of formal objects it is
the projection of `[A/B]`. -/
theorem completionComparison_comp_projection :
    P.completionComparison ⋙ FormalObject.projection =
      Grothendieck.forget (evaluationFunctor P.groupoidInFunctors) := rfl

/-- The comparison functor is faithful. -/
instance : P.completionComparison.Faithful where
  map_injective {X Y} f g hfg := by
    refine grothendieck_hom_ext_of_arrow f g (congrArg FormalObject.Hom.base hfg) ?_
    change fiberArrow f = fiberArrow g
    refine ULift.ext _ _ (CompleteLocalAlgCat.hom_ext_of_quotientProjection fun n => ?_)
    have h := congrArg fiberArrow (congrArg (fun h => FormalObject.Hom.app h n) hfg)
    change fiberArrow ((P.truncationFunctor n).map f) = fiberArrow ((P.truncationFunctor n).map g)
      at h
    rw [fiberArrow_truncationFunctor_map, fiberArrow_truncationFunctor_map] at h
    exact congrArg ULift.down h

/-- The comparison functor is full. -/
instance : P.completionComparison.Full where
  map_surjective {X Y} h := by
    let b : X.base ⟶ Y.base := h.base
    have hbase : ∀ n, (h.app n).base = AdicTruncation.map b n := fun n =>
      grothendieck_base_eq_of_isHomLift (h.app n) _ (h.app_lift n)
    let β : ∀ n, P.arrows ⟶ artinianToComplete.obj (AdicTruncation.obj Y.base n) :=
      fun n => (fiberArrow (h.app n)).down
    have hβ : ∀ n, β (n + 1) ≫ artinianToComplete.map (AdicTruncation.transition Y.base n) =
        β n := fun n => by
      have hn := congrArg fiberArrow (h.naturality n)
      rw [show fiberArrow ((P.completionComparison.obj X).transition n ≫ h.app n) =
          fiberArrow (h.app n) from P.fiberArrow_truncationTransition_comp n (h.app n),
        show fiberArrow (h.app (n + 1) ≫ (P.completionComparison.obj Y).transition n) =
          _ from P.fiberArrow_comp_truncationTransition n (h.app (n + 1))] at hn
      exact (congrArg ULift.down hn).symm
    obtain ⟨βc, hβc⟩ := CompleteLocalAlgCat.exists_hom_of_compatible β hβ
    have hsrc : P.source ≫ βc = X.fiber.down ≫ b := by
      refine CompleteLocalAlgCat.hom_ext_of_quotientProjection fun n => ?_
      have h1 := congrArg ULift.down
        (P.groupoidInFunctors.evaluationArrowEquiv _ _ _ (h.app n).fiber).2.1
      change P.source ≫ β n = (X.fiber.down ≫ quotientProjection X.base n) ≫
        artinianToComplete.map (h.app n).base at h1
      rw [Category.assoc, hβc, h1, hbase n, Category.assoc, Category.assoc]
      exact congrArg (X.fiber.down ≫ ·) (quotientProjection_naturality _ _ b n)
    have htgt : P.target ≫ βc = Y.fiber.down :=
      CompleteLocalAlgCat.hom_ext_of_quotientProjection fun n => by
        rw [Category.assoc, hβc]
        exact congrArg ULift.down
          (P.groupoidInFunctors.evaluationArrowEquiv _ _ _ (h.app n).fiber).2.2
    let φ : ((evaluationFunctor P.groupoidInFunctors).map b).toFunctor.obj X.fiber ⟶ Y.fiber :=
      (P.groupoidInFunctors.evaluationArrowEquiv _ _ _).symm
        ⟨ULift.up βc, congrArg ULift.up hsrc, congrArg ULift.up htgt⟩
    refine ⟨⟨b, φ⟩, FormalObject.Hom.ext rfl (fun n => ?_)⟩
    apply grothendieck_hom_ext_of_arrow _ _ (hbase n).symm
    change fiberArrow ((P.truncationFunctor n).map ⟨b, φ⟩) = fiberArrow (h.app n)
    rw [fiberArrow_truncationFunctor_map]
    apply ULift.ext
    change ((P.groupoidInFunctors.evaluationArrowEquiv _ _ _
      ((P.groupoidInFunctors.evaluationArrowEquiv _ _ _).symm _)).1.down ≫ _) = _
    rw [Equiv.apply_symm_apply]
    exact hβc n

section EssSurj

variable {P}
variable (hK : GroupoidInFunctors.IsSmooth
  (GroupoidInFunctors.restrict P.groupoidInFunctors artinianToComplete))
variable (ξ : FormalObject (Grothendieck.forget (evaluationFunctor
  (GroupoidInFunctors.restrict P.groupoidInFunctors artinianToComplete))))

local notation "𝒦" => GroupoidInFunctors.restrict P.groupoidInFunctors artinianToComplete

/-- The `n`-th level of a formal object lies over `R/𝔪_R^{n+1}`. -/
theorem level_base_eq (n : ℕ) : (ξ.level n).base = AdicTruncation.obj ξ.base n :=
  ξ.level_eq n

/-- The `n`-th level of a formal object of `[A|_{𝒞_Λ}/B|_{𝒞_Λ}]`, transported to lie over
`R/𝔪_R^{n+1}` on the nose. -/
def levelTransport (n : ℕ) : Grothendieck (evaluationFunctor 𝒦) :=
  (ξ.level n).transport (eqToHom (level_base_eq ξ n))

/-- The comparison of a level with its transport. -/
def levelIso (n : ℕ) : ξ.level n ≅ levelTransport ξ n :=
  ((ξ.level n).transportIso (eqToIso (level_base_eq ξ n))).symm

/-- The transition of a formal object, between the transported levels. -/
def levelTransition (n : ℕ) : levelTransport ξ (n + 1) ⟶ levelTransport ξ n :=
  (levelIso ξ (n + 1)).inv ≫ ξ.transition n ≫ (levelIso ξ n).hom

omit [Algebra Λ k] in
private theorem conj_eqToHom_eq {C : Type*} [Category C] {A A' B B' : C} (t : A ⟶ B)
    (g : A' ⟶ B') (p : A' = A) (q : B = B') (hg : g = eqToHom p ≫ t ≫ eqToHom q)
    (p' : A = A') (q' : B' = B) : eqToHom p' ≫ g ≫ eqToHom q' = t := by
  subst p q
  simp [hg]

/-- The base component of the transported transition is `R/𝔪_R^{n+2} ⟶ R/𝔪_R^{n+1}`. -/
theorem levelTransition_base (n : ℕ) :
    (levelTransition ξ n).base = AdicTruncation.transition ξ.base n := by
  have := ξ.transition_lift n
  exact conj_eqToHom_eq _ _ _ _ (IsHomLift.fac' (Grothendieck.forget (evaluationFunctor 𝒦))
    ((AdicTruncation.transitionNat n).app ξ.base) (ξ.transition n))
    (level_base_eq ξ (n + 1)).symm (level_base_eq ξ n)

/-- The fibre component of the transported transition, as a morphism of the fibre over
`R/𝔪_R^{n+1}`. -/
def levelTransitionFiber (n : ℕ) :
    ((evaluationFunctor 𝒦).map (AdicTruncation.transition ξ.base n)).toFunctor.obj
        (levelTransport ξ (n + 1)).fiber ⟶ (levelTransport ξ n).fiber :=
  Grothendieck.baseHom (levelTransition ξ n) (levelTransition_base ξ n)

include hK in
/-- Given a morphism `θ` out of the transported `n`-th level, there is an arrow over
`R/𝔪_R^{n+2}` with source the transported `(n+1)`-st level whose restriction to `R/𝔪_R^{n+1}` is
the arrow of the transported transition followed by `θ`. -/
theorem exists_rectifyLift (n : ℕ)
    (θ : Σ x : (evaluationFunctor 𝒦).obj (AdicTruncation.obj ξ.base n),
      (levelTransport ξ n).fiber ⟶ x) :
    ∃ e : (𝒦).arrows.obj (AdicTruncation.obj ξ.base (n + 1)),
      (𝒦).arrows.map (AdicTruncation.transition ξ.base n) e =
          ((𝒦).evaluationArrowEquiv _ _ _ (levelTransitionFiber ξ n ≫ θ.2)).1 ∧
        (𝒦).source.app _ e = (levelTransport ξ (n + 1)).fiber :=
  (isSmooth_elementsBasedFunctor_iff (𝒦).source).1 hK.1
    (AdicTruncation.transition ξ.base n)
    (surjective_adicTruncation_transition_hom ξ.base n) _ (levelTransport ξ (n + 1)).fiber
    ((𝒦).evaluationArrowEquiv _ _ _ (levelTransitionFiber ξ n ≫ θ.2)).2.1

/-- One step of the rectification of a formal object: from an isomorphism `θ : z_n ⟶ x` out of
the transported `n`-th level, smoothness of the source projection lifts
`z_{n+1}|_{R/𝔪^{n+1}} ⟶ z_n ⟶ x` to an isomorphism out of `z_{n+1}`. -/
def rectifyStep (n : ℕ)
    (θ : Σ x : (evaluationFunctor 𝒦).obj (AdicTruncation.obj ξ.base n),
      (levelTransport ξ n).fiber ⟶ x) :
    Σ x : (evaluationFunctor 𝒦).obj (AdicTruncation.obj ξ.base (n + 1)),
      (levelTransport ξ (n + 1)).fiber ⟶ x :=
  ⟨(𝒦).target.app _ (Classical.choose (exists_rectifyLift hK ξ n θ)),
    ((𝒦).evaluationArrowEquiv _ _ _).symm
      ⟨Classical.choose (exists_rectifyLift hK ξ n θ),
        (Classical.choose_spec (exists_rectifyLift hK ξ n θ)).2, rfl⟩⟩

/-- The rectified tower: isomorphisms `θ_n : z_n ⟶ x_n` out of the transported levels whose
targets form a compatible family. -/
def rectify : (n : ℕ) → Σ x : (evaluationFunctor 𝒦).obj (AdicTruncation.obj ξ.base n),
    (levelTransport ξ n).fiber ⟶ x
  | 0 => ⟨(levelTransport ξ 0).fiber, 𝟙 _⟩
  | n + 1 => rectifyStep hK ξ n (rectify n)

/-- The `(n+1)`-st stage of the rectified tower is the rectification step applied to the `n`-th. -/
theorem rectify_succ (n : ℕ) : rectify hK ξ (n + 1) = rectifyStep hK ξ n (rectify hK ξ n) := rfl

/-- The targets of the rectified tower form a compatible family. -/
theorem rectify_compatible (n : ℕ) :
    (𝒦).objects.map (AdicTruncation.transition ξ.base n) (rectify hK ξ (n + 1)).1 =
      (rectify hK ξ n).1 := by
  rw [rectify_succ]
  change (𝒦).objects.map _ ((𝒦).target.app _ (Classical.choose (exists_rectifyLift hK ξ n _))) = _
  rw [← NatTrans.naturality_apply, (Classical.choose_spec (exists_rectifyLift hK ξ n _)).1]
  exact ((𝒦).evaluationArrowEquiv _ _ _ _).2.2

/-- The restriction of the arrow of the `(n+1)`-st rectified morphism is the arrow of the
transported transition followed by the `n`-th rectified morphism. -/
theorem rectify_arrow (n : ℕ) :
    (𝒦).arrows.map (AdicTruncation.transition ξ.base n)
        ((𝒦).evaluationArrowEquiv _ _ _ (rectify hK ξ (n + 1)).2).1 =
      ((𝒦).evaluationArrowEquiv _ _ _ (levelTransitionFiber ξ n ≫ (rectify hK ξ n).2)).1 := by
  rw [rectify_succ]
  have h := Classical.choose_spec (exists_rectifyLift hK ξ n (rectify hK ξ n))
  change (𝒦).arrows.map _ ((𝒦).evaluationArrowEquiv _ _ _ (((𝒦).evaluationArrowEquiv _ _ _).symm
    ⟨Classical.choose (exists_rectifyLift hK ξ n (rectify hK ξ n)), h.2, rfl⟩)).1 = _
  rw [Equiv.apply_symm_apply]
  exact h.1

/-- The point `A ⟶ R` assembled from the rectified tower. -/
theorem exists_rectifiedPoint : ∃ x : P.objects ⟶ ξ.base,
    ∀ n, x ≫ quotientProjection ξ.base n = ((rectify hK ξ n).1 : ULift.{v} _).down :=
  CompleteLocalAlgCat.exists_hom_of_compatible _ (fun n =>
    congrArg ULift.down (rectify_compatible hK ξ n))

/-- The object of `[A/B]` over `R` that the rectified tower determines. -/
def rectifiedObject : Grothendieck (evaluationFunctor P.groupoidInFunctors) :=
  ⟨ξ.base, ULift.up (Classical.choose (exists_rectifiedPoint hK ξ))⟩

/-- The `n`-th target of the rectified tower is the `n`-th truncation of the rectified object. -/
theorem rectify_fst_eq (n : ℕ) :
    (rectify hK ξ n).1 = ((P.truncationFunctor n).obj (rectifiedObject hK ξ)).fiber :=
  ULift.ext _ _ (Classical.choose_spec (exists_rectifiedPoint hK ξ) n).symm

/-- The comparison of the transported `n`-th level with the `n`-th truncation of the rectified
object. -/
def rectifiedLevelHom (n : ℕ) :
    levelTransport ξ n ⟶ (P.truncationFunctor n).obj (rectifiedObject hK ξ) :=
  Grothendieck.ofFibreHom ((rectify hK ξ n).2 ≫ eqToHom (rectify_fst_eq hK ξ n))

/-- The comparisons `rectifiedLevelHom` commute with the transitions. -/
theorem levelTransition_comp_rectifiedLevelHom (n : ℕ) :
    levelTransition ξ n ≫ rectifiedLevelHom hK ξ n =
      rectifiedLevelHom hK ξ (n + 1) ≫ P.truncationTransition n (rectifiedObject hK ξ) := by
  rw [← Grothendieck.mk_baseHom (levelTransition ξ n) (levelTransition_base ξ n),
    truncationTransition_eq]
  refine (Grothendieck.mk_comp_ofFibreHom (F := evaluationFunctor 𝒦)
    (AdicTruncation.transition ξ.base n) (levelTransitionFiber ξ n)
      ((rectify hK ξ n).2 ≫ eqToHom (rectify_fst_eq hK ξ n))).trans
    (Eq.trans ?_ (Grothendieck.ofFibreHom_comp_mk (F := evaluationFunctor 𝒦)
      ((rectify hK ξ (n + 1)).2 ≫ eqToHom (rectify_fst_eq hK ξ (n + 1)))
      (AdicTruncation.transition ξ.base n)
        (eqToHom (P.truncationTransition_fiber_eq n (rectifiedObject hK ξ)))).symm)
  congr 1
  refine ((𝒦).evaluationArrowEquiv _ _ _).injective (Subtype.ext ?_)
  refine (evaluationArrowEquiv_comp_comp_eqToHom' _ _ _ _ _).trans ?_
  refine Eq.trans ?_ (evaluationArrowEquiv_map_comp_eqToHom_comp_eqToHom _ _ _ _ _).symm
  exact (rectify_arrow hK ξ n).symm

omit [Algebra Λ k] in
private theorem eqToHom_comp_id_eq_conj {C : Type*} [Category C] {X A : C} (p : X = A)
    (q : X = A) (r : A = A) (g : A ⟶ A) (hg : g = 𝟙 A) :
    eqToHom p ≫ 𝟙 A = eqToHom q ≫ g ≫ eqToHom r := by
  subst p hg
  simp

/-- The comparison of a formal object with the comparison image of its rectified object. -/
def rectifiedHom : ξ ⟶ P.completionComparison.obj (rectifiedObject hK ξ) where
  base := 𝟙 ξ.base
  app n := (levelIso ξ n).hom ≫ rectifiedLevelHom hK ξ n
  app_lift n := by
    refine grothendieck_isHomLift_of_base _ _ (level_base_eq ξ n) rfl ?_
    change eqToHom (level_base_eq ξ n) ≫ 𝟙 _ = _
    exact eqToHom_comp_id_eq_conj _ _ _ _ ((AdicTruncation.functor n).map_id ξ.base)
  naturality n := by
    change ξ.transition n ≫ (levelIso ξ n).hom ≫ rectifiedLevelHom hK ξ n =
      ((levelIso ξ (n + 1)).hom ≫ rectifiedLevelHom hK ξ (n + 1)) ≫
        P.truncationTransition n (rectifiedObject hK ξ)
    rw [Category.assoc, ← levelTransition_comp_rectifiedLevelHom, levelTransition]
    simp

/-- The comparison of a formal object with the image of its rectified object is an isomorphism. -/
theorem isIso_rectifiedHom : IsIso (rectifiedHom hK ξ) :=
  isIso_of_isHomLift_id (formalObjectProjection_isCofiberedInGroupoids _
    (quotientProjection_cofibered (𝒦))) (A := ξ.base) (rectifiedHom hK ξ)
    (IsHomLift.map FormalObject.projection (rectifiedHom hK ξ))

end EssSurj

/-- **The comparison functor is essentially surjective when the restricted groupoid is smooth.**
A formal object of `[A|_{𝒞_Λ}/B|_{𝒞_Λ}]` is rectified, using smoothness of the source
projection to lift its transition isomorphisms level by level, into a compatible tower of
points, which is a point `A ⟶ R` by completeness. -/
theorem completionComparison_essSurj
    (hK : GroupoidInFunctors.IsSmooth
      (GroupoidInFunctors.restrict P.groupoidInFunctors artinianToComplete)) :
    P.completionComparison.EssSurj where
  mem_essImage ξ := by
    have := isIso_rectifiedHom hK ξ
    exact ⟨rectifiedObject hK ξ, ⟨(asIso (rectifiedHom hK ξ)).symm⟩⟩

/-- **The completed presentation.** Let `P` be a representable presentation on `𝒞^_Λ` whose
restriction to `𝒞_Λ` is a smooth groupoid in functors presenting a category `𝓕` cofibred over
`𝒞_Λ`. Then the quotient `[A/B]` of `P` is equivalent over `𝒞^_Λ` to the completion `𝓕^` of
`𝓕`. -/
def completedPresentation
    (hK : GroupoidInFunctors.IsSmooth
      (GroupoidInFunctors.restrict P.groupoidInFunctors artinianToComplete))
    {F : Type*} [Category F] {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (E : Presentation (GroupoidInFunctors.restrict P.groupoidInFunctors artinianToComplete) p) :
    Presentation P.groupoidInFunctors (FormalObject.projection (p := p)) :=
  haveI := P.completionComparison_essSurj hK
  presentationOfQuotientEquivalence P.groupoidInFunctors FormalObject.projection
    (P.completionComparison ⋙ (completionEquivalence E).functor)
    ((Functor.assoc _ _ _).trans ((congrArg (P.completionComparison ⋙ ·)
      (completionMap E.homBased).w).trans P.completionComparison_comp_projection))

end RepresentablePresentation

end Deformation
