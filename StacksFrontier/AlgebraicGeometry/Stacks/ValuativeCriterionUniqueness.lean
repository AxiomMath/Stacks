module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperInertiaWhiskerLift
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.CategoryTheory.DottedArrows.Composition
public import StacksFrontier.CategoryTheory.DottedArrows.Defs
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.LocallyGroupoid
public import StacksFrontier.CategoryTheory.FiberedInSetoids.Setoid
public import StacksFrontier.CategoryTheory.FiberedInSetoids.Transfer

/-!
# The uniqueness part of the valuative criterion for algebraic stacks

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` of a big fppf site.
A *valuative diagram* for `f` is a 2-commutative square whose left edge is the inclusion of
the generic point of the spectrum of a valuation ring, together with the 2-morphism `γ`
witnessing the 2-commutativity. The 1-morphism `f` satisfies the uniqueness part of the
valuative criterion when, for every such diagram, the category of dotted arrows is either empty
or a setoid with exactly one isomorphism class.

## Main definitions

* `AlgebraicGeometry.Stack.ValuativeDiagram`: a valuative square for a 1-morphism of
  algebraic stacks, with its witnessing 2-morphism.
* `AlgebraicGeometry.Stack.ValuativeCriterion.Uniqueness`: the uniqueness part of the
  valuative criterion.

## Main results

* `AlgebraicGeometry.Stack.valuativeCriterionUniqueness_comp`: the uniqueness part of the
  valuative criterion is preserved by composition.
* `AlgebraicGeometry.Stack.nonempty_dottedArrow_equivalence_of_forall_exists_whiskerLeft` and
  `AlgebraicGeometry.Stack.nonempty_dottedArrow_iff_exists_diagonal`: for an algebraic stack `𝒴`
  whose inertia projection `I_𝒴 ⟶ 𝒴` is proper, the category of dotted arrows of a valuative
  diagram is independent of the witnessing 2-morphism up to equivalence, and it is nonempty
  exactly when a diagonal 1-morphism exists.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

/-- A 2-commutative valuative square for a 1-morphism `f` of algebraic stacks: a valuation
ring `R`, objects of the site whose underlying schemes are the spectra of the fraction field
of `R` and of `R`, the inclusion of the generic point between them read as a 1-morphism `j`
of categories fibred in groupoids, a generic point `x` of `𝒳`, a special point `y` of `𝒴`,
and a 2-morphism `γ` witnessing the 2-commutativity. -/
structure ValuativeDiagram
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS)
    (f : 𝒳 ⟶ 𝒴) where
  /-- The valuation ring. -/
  R : Type u
  [ring : CommRing R]
  [domain : IsDomain R]
  [valuation : ValuationRing R]
  /-- The object of the site carrying the generic point. -/
  generic : BigFppfOver B S hS
  /-- The object of the site carrying the special point. -/
  whole : BigFppfOver B S hS
  /-- Its underlying scheme is the spectrum of the fraction field of `R`. -/
  generic_iso : (BigFppfOver.toScheme B S hS).obj generic ≅
    Spec (.of (FractionRing R))
  /-- Its underlying scheme is the spectrum of `R`. -/
  whole_iso : (BigFppfOver.toScheme B S hS).obj whole ≅ Spec (.of R)
  /-- The inclusion of the generic point, in the site. -/
  inclusion : generic ⟶ whole
  /-- The inclusion is the canonical map, under the two identifications. -/
  inclusion_spec : (BigFppfOver.toScheme B S hS).map inclusion =
    generic_iso.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ whole_iso.inv
  /-- The left edge of the square, as a 1-morphism of categories fibred in groupoids. -/
  j : schemeFibredCategory B S hS generic ⟶
    schemeFibredCategory B S hS whole
  /-- The left edge is the one induced by the inclusion. -/
  j_canonical : j.hom.toFunctor = Over.map inclusion
  /-- The generic point of `𝒳`. -/
  x : schemeFibredCategory B S hS generic ⟶ 𝒳.1
  /-- The special point of `𝒴`. -/
  y : schemeFibredCategory B S hS whole ⟶ 𝒴.1
  /-- The 2-morphism witnessing the 2-commutativity of the square. -/
  γ : (j ≫ y) ⟶ (x ≫ f.hom)

namespace ValuativeCriterion

/-- A 1-morphism of algebraic stacks satisfies the *uniqueness part of the
valuative criterion* when, for every valuative diagram for it, the category of dotted arrows
is either empty or a setoid with exactly one isomorphism class. -/
@[stacks 0CLG]
abbrev Uniqueness
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ D : ValuativeDiagram B S hS 𝒳 𝒴 f,
    IsSetoidCategory (CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ) ∧
      ∀ a b : CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ, Nonempty (a ≅ b)

end ValuativeCriterion

/-! ### Composition -/

/-- The composition of two 1-morphisms of algebraic stacks satisfying the
uniqueness part of the valuative criterion satisfies it as well. -/
@[stacks 0CLI]
theorem valuativeCriterionUniqueness_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : ValuativeCriterion.Uniqueness B S hS f)
    (hg : ValuativeCriterion.Uniqueness B S hS g) :
    ValuativeCriterion.Uniqueness B S hS (f ≫ g) := by
  intro D
  let lower : ValuativeDiagram B S hS 𝒴 𝒵 g :=
    { D with x := D.x ≫ f.hom, γ := D.γ ≫ (α_ D.x f.hom g.hom).inv }
  let upper : CategoryTheory.DottedArrow (D.x ≫ f.hom) D.j g.hom D.y
      (D.γ ≫ (α_ D.x f.hom g.hom).inv) → ValuativeDiagram B S hS 𝒳 𝒴 f :=
    fun q => { D with y := q.a, γ := q.α }
  let p := CategoryTheory.DottedArrow.compose D.x D.j f.hom g.hom D.y D.γ
  have hp : p.IsFiberedInGroupoids :=
    CategoryTheory.DottedArrow.compose_isFiberedInGroupoids D.x D.j f.hom g.hom D.y D.γ
  have hfibre : ∀ q : CategoryTheory.DottedArrow (D.x ≫ f.hom) D.j g.hom D.y
      (D.γ ≫ (α_ D.x f.hom g.hom).inv),
      IsSetoidCategory (p.Fiber q) ∧ ∀ a b : p.Fiber q, Nonempty (a ≅ b) := by
    intro q
    obtain ⟨E⟩ := CategoryTheory.DottedArrow.fiber_categoryIso D.x D.j f.hom g.hom D.y D.γ q
    have hupper := hf (upper q)
    have hinv : ∀ a : p.Fiber q, E.inverse.obj (E.functor.obj a) = a := fun a => by
      simpa using congrArg (fun F : p.Fiber q ⥤ p.Fiber q => F.obj a) E.functor_inverse
    have hcomp : (E.functor ⋙ E.inverse).Faithful := by
      rw [E.functor_inverse]; infer_instance
    have hfaith : E.functor.Faithful := Functor.Faithful.of_comp E.functor E.inverse
    refine ⟨IsSetoidCategory.of_faithful E.functor hfaith (hp.fiber_isGroupoid q) hupper.1, ?_⟩
    intro a b
    obtain ⟨e⟩ := hupper.2 (E.functor.obj a) (E.functor.obj b)
    exact ⟨(eqToIso (hinv a)).symm ≪≫ E.inverse.mapIso e ≪≫ eqToIso (hinv b)⟩
  have hW : (CategoryTheory.DottedArrow.toWithFactorization
      D.x D.j f.hom g.hom D.y D.γ).IsEquivalence :=
    CategoryTheory.DottedArrow.toWithFactorization_isEquivalence D.x D.j f.hom g.hom D.y D.γ
  have hgpd : IsGroupoid (CategoryTheory.DottedArrow D.x D.j (f.hom ≫ g.hom) D.y D.γ) :=
    inferInstance
  exact ⟨IsSetoidCategory.of_faithful
      (CategoryTheory.DottedArrow.toWithFactorization D.x D.j f.hom g.hom D.y D.γ)
      hW.faithful hgpd
      (IsSetoidCategory.of_isFiberedInGroupoids p hp (hg lower).1 fun q => (hfibre q).1),
    nonempty_iso_of_isEquivalence
      (CategoryTheory.DottedArrow.toWithFactorization D.x D.j f.hom g.hom D.y D.γ) hW
      (nonempty_iso_of_isFiberedInGroupoids p hp (hg lower).2 fun q => (hfibre q).2)⟩

/-! ### Proper inertia -/

/-- **Every 2-endomorphism of `y ∘ j` is the restriction of one of `y`**, for the left edge `j`
of a valuative diagram, when the inertia of `𝒴` is proper. -/
theorem exists_whiskerLeft_of_isProper_inertiaProjection_valuativeDiagram
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hI : IsProper B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒴).hom)
    (D : ValuativeDiagram B S hS 𝒳 𝒴 f)
    (τ : (D.j ≫ D.y) ⟶ (D.j ≫ D.y)) :
    ∃ δ : D.y ⟶ D.y, D.j ◁ δ = τ :=
  let := D.ring
  let := D.domain
  let := D.valuation
  exists_whiskerLeft_of_isProper_inertiaProjection B S hS hI D.inclusion D.R D.whole_iso
    D.generic_iso D.inclusion_spec D.j_canonical D.y τ

/-- When the inertia `I_𝒴 ⟶ 𝒴` is proper, the category of
dotted arrows of a valuative diagram is independent, up to a noncanonical equivalence, of the
2-morphism witnessing the 2-commutativity. -/
@[stacks 0CLD "1 of 2: independence of the witness"]
theorem nonempty_dottedArrow_equivalence_of_forall_exists_whiskerLeft
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hI : IsProper B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒴).hom)
    (D : ValuativeDiagram B S hS 𝒳 𝒴 f)
    (γ γ' : (D.j ≫ D.y) ⟶ (D.x ≫ f.hom)) :
    Nonempty (CategoryTheory.DottedArrow D.x D.j f.hom D.y γ ≌
      CategoryTheory.DottedArrow D.x D.j f.hom D.y γ') :=
  CategoryTheory.DottedArrow.nonempty_equivalence_congrWitness
    (exists_whiskerLeft_of_isProper_inertiaProjection_valuativeDiagram B S hS f hI D) γ γ'

/-- When the inertia `I_𝒴 ⟶ 𝒴` is proper, a dotted arrow of a valuative diagram exists — for
one and hence for every witnessing 2-morphism — exactly when there is a diagonal 1-morphism
`a : Spec R ⟶ 𝒳` with 2-morphisms `a ∘ j ⟶ x` and `y ⟶ f ∘ a`, with no condition relating
them to the witness. -/
@[stacks 0CLD "2 of 2: existence for some and hence every witness"]
theorem nonempty_dottedArrow_iff_exists_diagonal
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hI : IsProper B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒴).hom)
    (D : ValuativeDiagram B S hS 𝒳 𝒴 f)
    (γ : (D.j ≫ D.y) ⟶ (D.x ≫ f.hom)) :
    Nonempty (CategoryTheory.DottedArrow D.x D.j f.hom D.y γ) ↔
      ∃ a : schemeFibredCategory B S hS D.whole ⟶ 𝒳.1,
        Nonempty ((D.j ≫ a) ⟶ D.x) ∧ Nonempty (D.y ⟶ (a ≫ f.hom)) :=
  CategoryTheory.DottedArrow.nonempty_iff_exists_diagonal γ
    (exists_whiskerLeft_of_isProper_inertiaProjection_valuativeDiagram B S hS f hI D)

end AlgebraicGeometry.Stack

end
