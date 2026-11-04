module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PolynomialTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingTerminalSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackHomAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageAdjunction
public import StacksFrontier.RingTheory.Etale.StandardPresentationSolutions

/-!
# Polynomial systems in the generalized elements of a sheaf of rings

Let `(C, J)` be a site, `R` a sheaf of rings on it with commuting sections, and `Z` a sheaf of
sets.  The generalized elements `Z ⟶ ringSheaf R` form a commutative ring
(`CategoryTheory.Sheaf.homCommRing`), whose operations are the ring-operation *morphisms of
sheaves* `CategoryTheory.Sheaf.ringAddHom` and `ringMulHom` of a sheaf of rings
(`CategoryTheory.Sheaf.hom_add_eq`, `hom_mul_eq`, `hom_one_eq`, `hom_ringZero_eq`).  So for a
system `P` of polynomials with coefficients in a ring `Λ`, a coefficient map
`γ : Λ →+* (Z ⟶ ringSheaf R)` and a tuple `a : Fin n → (Z ⟶ ringSheaf R)` of generalized
elements, `MvPolynomial.eval₂ γ a (P j)` **is** the evaluation of `Pⱼ` at `a` as a morphism of
sheaves `Z ⟶ ringSheaf R`, built out of those operation morphisms, and
`MvPolynomial.IsSolution P γ a` says that each of the `n` evaluations is the zero morphism
(`MvPolynomial.isSolution_iff_forall_eval₂`).  No recursion over the polynomial is needed to
construct it: Mathlib's `MvPolynomial.eval₂` does that once and for all, in any commutative ring.

What this file adds is that the solution condition **transports**, in the four directions a
first-order condition on sections has to travel:

* *down to sections*: a system solved by generalized elements of shape `Z` is solved by the
  values of those elements on any section of `Z` over any object of the site;
* *along an inverse image*: a system solved by generalized elements of shape `Z` is solved by
  their inverse images along any finite-product-preserving functor `Φ` between categories of
  sheaves of sets, as generalized elements of the inverse-image sheaf of rings of Stacks 03D2;
* *along a morphism of sheaves of rings*: a system solved in `R` is solved in `R'`, which is how
  the condition crosses the structure map of a morphism of ringed topoi;
* *along a precomposition*: the evaluation morphism is natural in `Z`.

Each is one application of `MvPolynomial.isSolution_comp` — the image of a solution under a ring
homomorphism is a solution of the transported system — to one of the four ring homomorphisms
`CategoryTheory.Sheaf.sectionsEvalRingHom`,
`Stacks.Sheaves.ToposPullback.inverseImageRingEltRingHom`,
`CategoryTheory.Sheaf.postcompRingHomOfSheaf` and `CategoryTheory.Sheaf.compRingHom`.  That those
four maps are ring homomorphisms and not merely additive ones is the whole content; it is what
makes a *polynomial* condition survive where a linear one would survive anyway.

Beyond those transports, the first of them is **reversible**:
`CategoryTheory.Sheaf.isSolution_of_forall_sectionsEval_eval₂` says a tuple of generalized
elements solves a system as morphisms of sheaves as soon as the evaluation of each `Pⱼ` at it
vanishes on every section, because a generalized element of a sheaf of rings vanishes exactly when
all of its sections do (`CategoryTheory.Sheaf.hom_eq_zero_iff_forall_sectionsEval`); and
`CategoryTheory.Sheaf.sectionsEvalRingHom_eval₂` identifies that hypothesis with the chartwise
solution condition, so the two conditions are equivalent.  That converse is what makes the
condition *establishable* rather than merely transportable, and with it the coefficients' own
reading as constant generalized elements, `CategoryTheory.Sheaf.constRingHom`.

## Why this is wanted

This is the transport of equations needed by step (3) of the proof of [Stacks Project, Tag 04I6].
There `Φ = g⁻¹` is the inverse image of a morphism of ringed topoi, `h_V` is a representable
sheaf on the small étale site of `Y` presented as the solutions of an étale system
(`AlgebraicGeometry.SolutionPresentation`), and the comparison morphism
`g⁻¹h_V ⟶ h_{X ×_Y V}` is produced by
`AlgebraicGeometry.SolutionPresentation.homOfIsSolution` from the `n` coordinates of `h_V`
pulled back along `g⁻¹` and followed by the structure map.  The hypothesis that constructor
needs is precisely that those `n` morphisms *solve* the twisted system over every chart of
`X_étale` — and a chart of `X_étale` names a *section* of `g⁻¹h_V`, about which nothing can be
assumed, `g⁻¹` being an abstract left adjoint.  The route out is to establish the solution
condition once as an identity of **morphisms of sheaves** out of `h_V`, where the coordinates are
visible, and then to transport it and evaluate it on each section: establishing it is
`CategoryTheory.Sheaf.isSolution_of_forall_sectionsEval_eval₂`, which turns the chartwise
condition on `Y_étale` — where `AlgebraicGeometry.SolutionPresentation` supplies it outright —
into the equation of morphisms, and transporting and evaluating it is
`Stacks.Sheaves.ToposPullback.isSolution_sections_postcomp_inverseImageRingHom` below, which
composes all three of the inverse image, the structure map and the evaluation on a section.

The coefficient half of the same step — that the structure map carries a global function `b` of
`𝒪_Y` to `φ b` — is a separate statement, and is proved as
`AlgebraicGeometry.RingedToposHom.terminalObjHomEquiv_globalSectionsMap`.  Nothing here is
specific to the étale site, to a morphism of topoi, or to étale systems; the statements below are
about an arbitrary site, an arbitrary sheaf of rings with commuting sections and an arbitrary
polynomial system.  Supplying the étale instance of them — identifying the sheaf of rings with
the small étale structure sheaf and `m` with the structure map of `g` — is what remains of step
(3), and is not done here.

## Main definitions

* `CategoryTheory.Sheaf.postcompRingHomOfSheaf`: postcomposition with a morphism of sheaves of
  rings, as a ring homomorphism of generalized elements.
* `CategoryTheory.Sheaf.constElt` and `CategoryTheory.Sheaf.constRingHom`: a section of a sheaf of
  rings over a terminal object of the site, read as a constant generalized element of any shape,
  and that reading as a ring homomorphism — the map along which the *coefficients* of a system
  become generalized elements.

## Main results

* `CategoryTheory.Sheaf.isSolution_sectionsEvalRingHom`: a system solved by generalized elements
  is solved by their values on sections.
* `CategoryTheory.Sheaf.hom_eq_zero_iff_forall_sectionsEval`: a generalized element of a sheaf of
  rings vanishes exactly when all of its sections do.
* `CategoryTheory.Sheaf.isSolution_of_forall_sectionsEval_eval₂` and
  `CategoryTheory.Sheaf.sectionsEvalRingHom_eval₂`: the converse of the first result, and the
  computation which identifies its hypothesis with the sectionwise condition.  Together with the
  first result they say that the solution condition on generalized elements *is* the sectionwise
  condition, so it may be established where sections are visible and then transported where they
  are not.
* `CategoryTheory.Sheaf.sectionsEvalRingHom_constRingHom`: evaluating a constant generalized
  element on a section is restriction of the global function.
* `CategoryTheory.Sheaf.eval₂_hom_comp`: polynomial evaluation of generalized elements is natural
  in the shape — restricting the evaluated morphism along `g : Z' ⟶ Z` evaluates the restricted
  coefficients and coordinates.
* `CategoryTheory.Sheaf.isSolution_postcompRingHom`: a system solved by generalized elements of
  `R` is solved by their images in `R'`.
* `Stacks.Sheaves.ToposPullback.isSolution_inverseImageRingHom`: a system solved by generalized
  elements is solved by their inverse images, over the inverse-image sheaf of rings.
* `Stacks.Sheaves.ToposPullback.isSolution_sections_inverseImageRingHom` and
  `isSolution_sections_postcomp_inverseImageRingHom`: the composites, the second of which is the
  form step (3) of the proof of Stacks 04I6 consumes.

## Implementation notes

**Commutativity is a hypothesis, supplied by `letI`.**  `ringSheaf` is the underlying sheaf of
sets of a sheaf of possibly non-commutative rings, so `CategoryTheory.Sheaf.homRing` is only a
`Ring`, while `MvPolynomial.eval₂` and `MvPolynomial.IsSolution` ask for a `CommRing`.  Both
`CategoryTheory.Sheaf.homCommRing` and `ringSectionsCommRing` are therefore `def`s taking
commutativity of the sections as an argument, as `CategoryTheory.Sheaf.hom_mul_comm` records, and
every statement below opens with the corresponding `letI`.  On the inverse-image side the
hypothesis is discharged, not assumed again: `CategoryTheory.Sheaf.pullback_sections_mul_comm`
derives commutativity of the sections of `pullbackRingSheaf J Φ R` from that of `R`.

**No `MvPolynomial` lemma is proved here.**  Every proof is `MvPolynomial.isSolution_comp` or
`MvPolynomial.eval₂_comp_left` at one of the four ring homomorphisms.  The file is short because
the work was done by bundling those maps as `RingHom`s — three in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackHomAlgebra`, where the four axioms of
each were already proved separately but only the additive two were packaged, and
`postcompRingHomOfSheaf` here out of `CategoryTheory.Sheaf.ringObjMap`.

**`ringSheaf` is spelled `Sheaf.ringSheaf` in the `Stacks.Sheaves.ToposPullback` section.**
`Stacks.ringSheaf`, the underlying sheaf of rings of a sheaf of *commutative* rings, is in scope
there through the import of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageAdjunction` and wins the
namespace-prefix resolution against the opened `CategoryTheory.Sheaf.ringSheaf`.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] {R : Sheaf J RingCat.{w}}
  {Z Z' : Sheaf J (Type w)}
  (hc : ∀ (X : Cᵒᵖ) (x y : (sectionsFunctor J X).obj (ringSheaf R)), x * y = y * x)
  {Λ : Type*} [CommRing Λ] {n : ℕ} {P : Fin n → MvPolynomial (Fin n) Λ}

/-- **A polynomial system solved by generalized elements is solved by their sections.**

If the tuple `a` of generalized elements of `R` of shape `Z` solves the system `P` with
coefficients pushed along `γ`, then for every object `X` of the site and every section `z` of `Z`
over `X` the tuple of values `(aᵢ)_X(z)` solves `P` with coefficients pushed along `γ` followed
by evaluation at `z`.

This is the step that makes the solution condition checkable on a sheaf about whose sections
nothing is known: the condition is established as an identity of morphisms of sheaves and then
read off on each section. -/
theorem isSolution_sectionsEvalRingHom (X : Cᵒᵖ) (z : (sectionsFunctor J X).obj Z) :
    letI := homCommRing hc Z
    letI := ringSectionsCommRing hc X
    ∀ (γ : Λ →+* (Z ⟶ ringSheaf R)) {a : Fin n → (Z ⟶ ringSheaf R)},
      MvPolynomial.IsSolution P γ a →
        MvPolynomial.IsSolution P ((sectionsEvalRingHom X z).comp γ)
          (fun i => (a i).hom.app X z) := by
  let := homCommRing hc Z
  let := ringSectionsCommRing hc X
  exact fun γ _ ha => MvPolynomial.isSolution_comp γ (sectionsEvalRingHom X z) ha

/-- **Polynomial evaluation of generalized elements is natural in the shape.**

The evaluation `MvPolynomial.eval₂ γ a p : Z ⟶ ringSheaf R` is a morphism of sheaves, built from
the ring-operation morphisms of `R`; restricting it along `g : Z' ⟶ Z` is the evaluation of the
restricted coefficients and coordinates.  This is what lets the evaluation be treated as a
morphism of sheaves rather than as a family of maps on sections. -/
theorem eval₂_hom_comp (g : Z' ⟶ Z) (p : MvPolynomial (Fin n) Λ) :
    letI := homCommRing hc Z
    letI := homCommRing hc Z'
    ∀ (γ : Λ →+* (Z ⟶ ringSheaf R)) (a : Fin n → (Z ⟶ ringSheaf R)),
      g ≫ MvPolynomial.eval₂ γ a p =
        MvPolynomial.eval₂ ((compRingHom g).comp γ) (fun i => g ≫ a i) p := by
  let := homCommRing hc Z
  let := homCommRing hc Z'
  exact fun γ a => MvPolynomial.eval₂_comp_left (compRingHom g) γ a p

/-! ### Establishing the solution condition as an equation of morphisms of sheaves

The statements above *transport* a solution condition already known.  What makes the condition
**establishable** on a sheaf whose sections admit no description is the converse of
`CategoryTheory.Sheaf.isSolution_sectionsEvalRingHom`: the condition on generalized elements is
*equivalent* to the sectionwise condition, because a generalized element vanishes exactly when all
of its sections do, so `MvPolynomial.eval₂ γ a (Pⱼ) = 0` is a single equation between morphisms of
sheaves which may be checked wherever sections happen to be visible.

The coefficients need a home of their own in that equation: a global function has to be read as a
*constant* generalized element, and the reading has to be a ring homomorphism, which is
`CategoryTheory.Sheaf.constRingHom` below. -/

section Morphisms

variable {T : C}

/-- A generalized element of a sheaf of rings vanishes exactly when all of its sections do.

This is what makes the solution condition a condition on *morphisms of sheaves*: the equation
`MvPolynomial.eval₂ γ a (Pⱼ) = 0` may be checked on sections over any objects of the site at all,
and conversely holds as an equation of morphisms once it holds on sections. -/
lemma hom_eq_zero_iff_forall_sectionsEval (a : Z ⟶ ringSheaf R) :
    a = 0 ↔ ∀ (X : Cᵒᵖ) (z : (sectionsFunctor J X).obj Z), sectionsEvalRingHom X z a = 0 := by
  refine ⟨fun h X z => ?_, fun h => hom_ext_sections fun X z => ?_⟩
  · exact h ▸ sectionsFunctor_map_hom_ringZero X z
  · exact (h X z).trans (sectionsFunctor_map_hom_ringZero X z).symm

/-- The constant generalized element of shape `Z` named by a section of a sheaf of rings over a
terminal object of the site: the morphism `Z ⟶ ⊤ ⟶ R` whose value on any section is the
restriction of the given global one. -/
def constElt (hT : IsTerminal T) (Z : Sheaf J (Type w))
    (x : (sectionsFunctor J (op T)).obj (ringSheaf R)) : Z ⟶ ringSheaf R :=
  Limits.terminal.from Z ≫ terminalObjHomEquiv hT (ringSheaf R) x

/-- The value of `CategoryTheory.Sheaf.constElt hT Z x` on any section of `Z` over `X` is the
restriction of `x` along the unique morphism `X ⟶ T`. -/
@[simp]
lemma sectionsFunctor_map_constElt (hT : IsTerminal T) (Z : Sheaf J (Type w))
    (x : (sectionsFunctor J (op T)).obj (ringSheaf R)) (X : Cᵒᵖ)
    (z : (sectionsFunctor J X).obj Z) :
    (sectionsFunctor J X).map (constElt hT Z x) z =
      (ringSheaf R).obj.map (hT.from X.unop).op x := by
  rw [constElt, (sectionsFunctor J X).map_comp_apply]
  exact sectionsFunctor_map_terminalObjHomEquiv (E := ringSheaf R) hT x X _

/-- **A global function of a sheaf of rings, read as a constant generalized element, is a ring
homomorphism.**

This is the map along which the *coefficients* of a polynomial system travel when the system is
restated as an equation between morphisms of sheaves: for `ψ : Λ →+* Γ(T, R)` the composite
`(constRingHom hT Z).comp ψ` is the coefficient homomorphism of the system read in the
generalized elements of shape `Z`, and `CategoryTheory.Sheaf.sectionsEvalRingHom` carries it back
to restriction of the global coefficients over each object of the site
(`CategoryTheory.Sheaf.sectionsEvalRingHom_constRingHom`).

Ring-homomorphism-ness is not checked by hand.  Evaluation on the unique section of the terminal
sheaf is already a ring homomorphism `(⊤ ⟶ R) →+* Γ(T, R)`
(`CategoryTheory.Sheaf.sectionsEvalRingHom`), and it is the *inverse* of
`CategoryTheory.Sheaf.terminalObjHomEquiv` on the nose, so that bijection is an isomorphism of
rings (`CategoryTheory.Sheaf.terminalSheafHomRingEquiv`); composing its inverse with
precomposition by `Z ⟶ ⊤`, which is a ring homomorphism by
`CategoryTheory.Sheaf.compRingHom`, gives this map.  Checking the four axioms directly instead
would ask the kernel to see restriction of sections as a ring homomorphism through
`CategoryTheory.sheafCompose`, which does not terminate. -/
noncomputable def terminalSheafHomRingEquiv (hT : IsTerminal T) :
    (⊤_ (Sheaf J (Type w)) ⟶ ringSheaf R) ≃+* (sectionsFunctor J (op T)).obj (ringSheaf R) :=
  { (terminalObjHomEquiv hT (ringSheaf R)).symm with
    map_mul' := fun a b => sectionsFunctor_map_hom_mul (Z := ⊤_ (Sheaf J (Type w))) (op T) a b
      (terminalSheafSection J (op T))
    map_add' := fun a b => sectionsFunctor_map_hom_add (Z := ⊤_ (Sheaf J (Type w))) (op T) a b
      (terminalSheafSection J (op T)) }

/-- **A global function of a sheaf of rings, read as a constant generalized element, is a ring
homomorphism.**  See `CategoryTheory.Sheaf.terminalSheafHomRingEquiv` for how the four axioms are
obtained. -/
noncomputable def constRingHom (hT : IsTerminal T) (Z : Sheaf J (Type w)) :
    (sectionsFunctor J (op T)).obj (ringSheaf R) →+* (Z ⟶ ringSheaf R) :=
  (compRingHom (Limits.terminal.from Z)).comp
    (terminalSheafHomRingEquiv (R := R) hT).symm.toRingHom

/-- `CategoryTheory.Sheaf.constRingHom hT Z` sends a global section `x` to the constant
generalized element `CategoryTheory.Sheaf.constElt hT Z x`. -/
@[simp]
lemma constRingHom_apply (hT : IsTerminal T) (Z : Sheaf J (Type w))
    (x : (sectionsFunctor J (op T)).obj (ringSheaf R)) :
    constRingHom hT Z x = constElt hT Z x :=
  rfl

/-- **Evaluating a constant generalized element on a section is restriction of the global
function.**  Read with `Λ` the coefficient ring of a polynomial system, this says that the
coefficient homomorphism of the system over generalized elements of shape `Z` evaluates, over
each object of the site, to the coefficient homomorphism of the system over that object. -/
lemma sectionsEvalRingHom_constRingHom (hT : IsTerminal T) (Z : Sheaf J (Type w)) (X : Cᵒᵖ)
    (z : (sectionsFunctor J X).obj Z)
    (x : (sectionsFunctor J (op T)).obj (ringSheaf R)) :
    sectionsEvalRingHom X z (constRingHom hT Z x) =
      (ringSheaf R).obj.map (hT.from X.unop).op x :=
  sectionsFunctor_map_constElt hT Z x X z

/-- **The solution condition for generalized elements follows from the sectionwise one.**

A tuple of generalized elements of a sheaf of rings solves a polynomial system *as morphisms of
sheaves* as soon as the evaluation of each `Pⱼ` at it vanishes on every section over every object
of the site.  Read through `CategoryTheory.Sheaf.sectionsEvalRingHom_eval₂`, which rewrites that
hypothesis as the chartwise solution condition, and together with
`CategoryTheory.Sheaf.isSolution_sectionsEvalRingHom`, which is the converse, this says the two
conditions are equivalent.

It is the direction that does the work.  A sheaf presented as an inverse image along an abstract
left adjoint has no accessible sections, so its own solution condition cannot be read off one
chart at a time; what can be done is to establish the condition over the *target*, where the
sections are visible, promote it there to the equation `MvPolynomial.eval₂ γ a (Pⱼ) = 0` between
morphisms of sheaves, and then transport that equation along the inverse image and the structure
map by `Stacks.Sheaves.ToposPullback.isSolution_sections_postcomp_inverseImageRingHom`. -/
theorem isSolution_of_forall_sectionsEval_eval₂ :
    letI := homCommRing hc Z
    ∀ (γ : Λ →+* (Z ⟶ ringSheaf R)) (a : Fin n → (Z ⟶ ringSheaf R)),
      (∀ (j : Fin n) (X : Cᵒᵖ) (z : (sectionsFunctor J X).obj Z),
          sectionsEvalRingHom X z (MvPolynomial.eval₂ γ a (P j)) = 0) →
        MvPolynomial.IsSolution P γ a := by
  let := homCommRing hc Z
  exact fun γ a h => (MvPolynomial.isSolution_iff_forall_eval₂ P γ a).2 fun j =>
    (hom_eq_zero_iff_forall_sectionsEval _).2 (h j)

/-- **Polynomial evaluation of generalized elements commutes with evaluation on a section.**

This is the computation that identifies the two sides of
`CategoryTheory.Sheaf.isSolution_of_forall_sectionsEval_eval₂`: the hypothesis of that theorem,
read through this, is exactly the chartwise solution condition, so the condition on generalized
elements and the sectionwise condition are equivalent — the converse implication being
`CategoryTheory.Sheaf.isSolution_sectionsEvalRingHom`. -/
lemma sectionsEvalRingHom_eval₂ (X : Cᵒᵖ) (z : (sectionsFunctor J X).obj Z)
    (p : MvPolynomial (Fin n) Λ) :
    letI := homCommRing hc Z
    letI := ringSectionsCommRing hc X
    ∀ (γ : Λ →+* (Z ⟶ ringSheaf R)) (a : Fin n → (Z ⟶ ringSheaf R)),
      sectionsEvalRingHom X z (MvPolynomial.eval₂ γ a p) =
        MvPolynomial.eval₂ ((sectionsEvalRingHom X z).comp γ)
          (fun i => sectionsEvalRingHom X z (a i)) p := by
  let := homCommRing hc Z
  let := ringSectionsCommRing hc X
  exact fun γ a => MvPolynomial.eval₂_comp_left (sectionsEvalRingHom X z) γ a p

end Morphisms

/-! ### Transport along a morphism of sheaves of rings -/

section Postcomposition

variable {R' : Sheaf J RingCat.{w}} (m : R ⟶ R')

/-- Postcomposition with a morphism of sheaves of rings, as a ring homomorphism of generalized
elements.  This is `CategoryTheory.Sheaf.ringObjMap` at `Q = coyoneda.obj (op Z)`, whose two
transported ring structures are `CategoryTheory.Sheaf.homRing` on the nose. -/
def postcompRingHomOfSheaf (T : Sheaf J (Type w)) : (T ⟶ ringSheaf R) →+* (T ⟶ ringSheaf R') :=
  ringObjMap m (coyoneda.obj (op T))

/-- `CategoryTheory.Sheaf.postcompRingHomOfSheaf m T` sends a generalized element `x` to its
composite with the morphism of underlying sheaves of sets of `m`. -/
@[simp]
lemma postcompRingHomOfSheaf_apply (T : Sheaf J (Type w)) (x : T ⟶ ringSheaf R) :
    postcompRingHomOfSheaf m T x = x ≫ (sheafCompose J (forget RingCat.{w})).map m := rfl

/-- **A polynomial system solved by generalized elements of `R` is solved by their images in
`R'`.**  The structure map of a morphism of ringed topoi is such an `m`, which is how the
solution condition crosses from the inverse-image sheaf of rings to the structure sheaf of the
source. -/
theorem isSolution_postcompRingHom
    (hc' : ∀ (X : Cᵒᵖ) (x y : (sectionsFunctor J X).obj (ringSheaf R')), x * y = y * x)
    (T : Sheaf J (Type w)) :
    letI := homCommRing hc T
    letI := homCommRing hc' T
    ∀ (γ : Λ →+* (T ⟶ ringSheaf R)) {a : Fin n → (T ⟶ ringSheaf R)},
      MvPolynomial.IsSolution P γ a →
        MvPolynomial.IsSolution P ((postcompRingHomOfSheaf m T).comp γ)
          (fun i => a i ≫ (sheafCompose J (forget RingCat.{w})).map m) := by
  let := homCommRing hc T
  let := homCommRing hc' T
  exact fun γ _ ha => MvPolynomial.isSolution_comp γ (postcompRingHomOfSheaf m T) ha

end Postcomposition

end CategoryTheory.Sheaf

/-! ## Transport along an inverse image -/

namespace Stacks.Sheaves.ToposPullback

open CategoryTheory Limits Sheaf Functor Opposite

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  {R : Sheaf K RingCat.{ww'}} {Z : Sheaf K (Type ww')} {W : Sheaf J (Type ww)}
  (hc : ∀ (Y : Dᵒᵖ) (x y : (sectionsFunctor K Y).obj (Sheaf.ringSheaf R)), x * y = y * x)
  {Λ : Type*} [CommRing Λ] {n : ℕ} {P : Fin n → MvPolynomial (Fin n) Λ}

/-- **A polynomial system solved by generalized elements is solved by their inverse images.**

If the tuple `a` of generalized elements of `R` of shape `Z` solves the system `P` with
coefficients pushed along `γ`, then the tuple of inverse images `c ≫ Φ.map (aᵢ)` solves `P` as
generalized elements of the inverse-image sheaf of rings `pullbackRingSheaf J Φ R` of
Stacks 03D2, with coefficients pushed along `γ` followed by the inverse image.

The inverse image of generalized elements is a ring homomorphism
(`Stacks.Sheaves.ToposPullback.inverseImageRingEltRingHom`), which is exactly what a polynomial
— as opposed to linear — condition needs. -/
theorem isSolution_inverseImageRingHom (c : W ⟶ Φ.obj Z) :
    letI := homCommRing hc Z
    letI := homCommRing (pullback_sections_mul_comm J Φ hc) W
    ∀ (γ : Λ →+* (Z ⟶ Sheaf.ringSheaf R)) {a : Fin n → (Z ⟶ Sheaf.ringSheaf R)},
      MvPolynomial.IsSolution P γ a →
        MvPolynomial.IsSolution P ((inverseImageRingEltRingHom J Φ c).comp γ)
          (fun i => c ≫ Φ.map (a i)) := by
  let := homCommRing hc Z
  let := homCommRing (pullback_sections_mul_comm J Φ hc) W
  exact fun γ _ ha => MvPolynomial.isSolution_comp γ (inverseImageRingEltRingHom J Φ c) ha

/-- **The form step (3) of the proof of [Stacks Project, Tag 04I6] consumes.**

A system solved by generalized elements of `R` of shape `Z` is solved, over every object `X` of
the source site and every section `z` of `W` over `X`, by the values there of the inverse images
of those elements — as sections of the inverse-image sheaf of rings.

This is the composite of `isSolution_inverseImageRingHom` with
`CategoryTheory.Sheaf.isSolution_sectionsEvalRingHom`, and it is the statement a constructor
such as `AlgebraicGeometry.SolutionPresentation.homOfIsSolution` asks for: the solution condition
over each chart, for a sheaf — an inverse image along an abstract left adjoint — whose sections
admit no description. -/
theorem isSolution_sections_inverseImageRingHom (c : W ⟶ Φ.obj Z) (X : Cᵒᵖ)
    (z : (sectionsFunctor J X).obj W) :
    letI := homCommRing hc Z
    letI := ringSectionsCommRing (pullback_sections_mul_comm J Φ hc) X
    ∀ (γ : Λ →+* (Z ⟶ Sheaf.ringSheaf R)) {a : Fin n → (Z ⟶ Sheaf.ringSheaf R)},
      MvPolynomial.IsSolution P γ a →
        MvPolynomial.IsSolution P
          (((sectionsEvalRingHom X z).comp (inverseImageRingEltRingHom J Φ c)).comp γ)
          (fun i => (c ≫ Φ.map (a i)).hom.app X z) := by
  let := homCommRing hc Z
  let := homCommRing (pullback_sections_mul_comm J Φ hc) W
  let := ringSectionsCommRing (pullback_sections_mul_comm J Φ hc) X
  exact fun γ _ ha => MvPolynomial.isSolution_comp γ
    ((sectionsEvalRingHom X z).comp (inverseImageRingEltRingHom J Φ c)) ha

/-- **The transport of equations needed by step (3) of the proof of
[Stacks Project, Tag 04I6], in full.**

Let `R` be a sheaf of rings on the target site with commuting sections, `O` a sheaf of rings on
the source site, and `m : Φ⁻¹R ⟶ O` a morphism of sheaves of rings — for `Φ = g⁻¹` the inverse
image of a morphism of ringed topoi, `m` is the inverse-image form of its structure map.  If the
tuple `a` of generalized elements of `R` of shape `Z` solves the system `P` with coefficients
pushed along `γ`, then over every object `X` of the source site and every section `z` of `W` the
values of the transported coordinates `c ≫ Φ.map (aᵢ) ≫ m` solve `P` with coefficients pushed
along the composite.

Every hypothesis is about the target site; nothing is assumed about the sections of `Φ.obj Z`,
which for `Φ` a left adjoint admit no description.  That is the point: the solution condition is
established as an identity of morphisms of sheaves and only then evaluated on sections, which is
the form `AlgebraicGeometry.SolutionPresentation.homOfIsSolution` asks for. -/
theorem isSolution_sections_postcomp_inverseImageRingHom (c : W ⟶ Φ.obj Z)
    {O : Sheaf J RingCat.{ww}} (m : pullbackRingSheaf J Φ R ⟶ O)
    (hcO : ∀ (X : Cᵒᵖ) (x y : (sectionsFunctor J X).obj (Sheaf.ringSheaf O)), x * y = y * x)
    (X : Cᵒᵖ) (z : (sectionsFunctor J X).obj W) :
    letI := homCommRing hc Z
    letI := ringSectionsCommRing hcO X
    ∀ (γ : Λ →+* (Z ⟶ Sheaf.ringSheaf R)) {a : Fin n → (Z ⟶ Sheaf.ringSheaf R)},
      MvPolynomial.IsSolution P γ a →
        MvPolynomial.IsSolution P
          (((sectionsEvalRingHom X z).comp
            ((postcompRingHomOfSheaf m W).comp (inverseImageRingEltRingHom J Φ c))).comp γ)
          (fun i => ((c ≫ Φ.map (a i)) ≫
            (sheafCompose J (forget RingCat.{ww})).map m).hom.app X z) := by
  let := homCommRing hc Z
  let := homCommRing (pullback_sections_mul_comm J Φ hc) W
  let := homCommRing hcO W
  let := ringSectionsCommRing hcO X
  exact fun γ _ ha => MvPolynomial.isSolution_comp γ
    ((sectionsEvalRingHom X z).comp
      ((postcompRingHomOfSheaf m W).comp (inverseImageRingEltRingHom J Φ c))) ha

end Stacks.Sheaves.ToposPullback

end
