module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalKernelLocalInjective
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPolynomialModel
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPresentationKernelLifting
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPresentationSquareDescent
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyBijective

/-!
# Local injectivity of the degree `-1` comparison of two polynomial presentations

Let `α₁ : E₁ ⟶ B` and `α₂ : E₂ ⟶ B` be two families of generators of a sheaf of commutative
rings `B` over `A` on a site, and let `h : E₁ ⟶ E₂` be a morphism of families with
`h ≫ α₂ = α₁`.  Writing `K₁` and `K₂` for the kernels of the two presentations `A[E₁] ⟶ B` and
`A[E₂] ⟶ B`, the induced map `Ker(K₁/K₁² ⟶ ⋯) ⟶ Ker(K₂/K₂² ⟶ ⋯)` is the degree `-1`
comparison map of the two naive cotangent complexes.  This file proves that it is locally
injective, which is the companion of the local surjectivity proved in
`StacksFrontier.CategoryTheory.Sites.Modules.ConormalPresentationKernelLifting`.

`Stacks.Sites.Conormal.isLocallyInjective_kernelMapOfFac` reduces local injectivity to a single
statement about one local section of the first conormal sheaf: if it is killed both by the first
conormal map and by the map of conormal sheaves of the factorisation, then it restricts to zero
on a covering sieve.  That statement is what this file proves, and with it local injectivity
becomes unconditional for a morphism of polynomial presentations.

The proof is local and composes four coverings.  Over a covering of the given object the
section is the conormal class of a section `x` of the kernel ideal whose universal differential
vanishes; over a second covering the image of `x` in `A[E₂]` lies in the square of the second
kernel ideal, because the map of conormal sheaves kills its class, and `x` itself comes from an
honest polynomial `q` on the polynomial model `A(-)[E₁(-)]`; over a third covering all partial
derivatives of `q` lie in the kernel of the first model and the renaming of `q` lies in the
square of the kernel of the second model; and over a fourth covering `q` itself lies in the
square of the kernel of the first model, which is
`Stacks.Sites.FreeAlgebra.exists_covering_mem_ker_sq_polynomialPresheafMap`.  A section of the
square of the kernel ideal has vanishing conormal class, so the original section restricts to
zero there.

## Main results

* `Stacks.SheafOfModules.vanishingSieve_arrows_of_mem_ker_sq`: the final step, that a polynomial
  in the square of the kernel of the model puts one single arrow in the vanishing sieve.
* `Stacks.SheafOfModules.vanishingSieve_presentationConormal_mem`: **the vanishing sieve of a
  local section killed by both maps is a covering sieve.**
* `Stacks.SheafOfModules.isLocallyInjective_presentationKernelMap`: **Stacks 08TY in degree
  `-1`, local injectivity.**  The degree `-1` comparison map of the two naive cotangent
  complexes is locally injective.

## Implementation notes

Each of the four coverings is composed with the next by
`Stacks.SheafOfModules.covers_of_forall_covers`, which is
`CategoryTheory.GrothendieckTopology.transitive` phrased for a sieve on the source of a
composite arrow; that is what keeps the nesting of the four coverings linear instead of
quadratic.  Two coverings of one and the same object are taken together with
`CategoryTheory.GrothendieckTopology.intersection_covering` rather than chained, so that only
one arrow is introduced per level.

Two spellings of the first term of a conormal sequence, as
`Stacks.Sites.Conormal.conormalSheaf` and as the first term of
`Stacks.Sites.Conormal.conormalSequence`, are definitionally equal only at default
transparency, so a goal mentioning both is not type-correct at the transparency `rw` and `simp`
check their motives at.  Every step on a conormal class is therefore composed with `Eq.trans`
and `congrArg`, and the proof is split into one named lemma per covering so that no single
declaration has to elaborate the whole chain.

The partial derivatives of a restriction of a polynomial are *not* the restrictions of its
partial derivatives — restriction renames the variables — but the ring-level descent of a square
membership reads them only over the object where the polynomial lives, so the hypothesis is
carried over one object here rather than over all further arrows as in the surjective half.

## References

* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), the independence of the
  naive cotangent complex from the presentation, whose degree `-1` local injectivity this is.
* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal sequence.
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1), part (2), the homotopy
  behind the comparison of two factorisations.
* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU), the free algebra sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w z

namespace Stacks.SheafOfModules


open Stacks.Sites.Conormal Stacks.Sites.FreeAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- For an essentially small site, sheafification of presheaves of abelian groups exists. -/
local instance [EssentiallySmall.{z} C] : HasSheafify J AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteHasSheafify (J := J)

/-- For an essentially small site, a morphism of presheaves of abelian groups becomes an
isomorphism after sheafification exactly when it is locally bijective. -/
local instance [EssentiallySmall.{z} C] : J.WEqualsLocallyBijective AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective (J := J)

variable [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)

/-! ### One presentation -/

section OnePresentation

variable (E : Functor Cᵒᵖ (Type w)) (α : E ⟶ underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom]

omit [J.WEqualsLocallyBijective CommRingCat.{w}] in
/-- **The final step: one arrow of the vanishing sieve.**  Let `q` be a polynomial over `V`
lying in the square of the kernel of the polynomial model, and let the conormal class of the
image of `q` in `A[E]` be the restriction along `n` of a section `y` of the conormal sheaf.
Then `n` belongs to the vanishing sieve of `y`.

The image in `A[E]` of a polynomial in the square of the kernel of the model lies in the square
of the kernel ideal of the presentation, because the sheafification unit is a factorisation of
the model through the presentation, and a section of the square of the kernel ideal has
vanishing conormal class. -/
theorem vanishingSieve_arrows_of_mem_ker_sq {X V : C}
    (y : (presentationConormalSequence.{v, u, w, z} J A B a E α).X₁.val.obj (op X))
    (n : V ⟶ X) (q : (polynomialPresheaf J A E).obj (op V))
    (hq : q ∈ kernelIdeal (polynomialEvaluation J A B E a α) (op V))
    (hqc : conormalClass.{v, u, w, z} J A (freeAlgebraSheaf J A E) B
        (freeAlgebraSheafCoefficientMap J A E) (presentation J A B a E α) (op V)
        ⟨(polynomialUnit J A E).app (op V) q,
          polynomialUnit_mem_kernelIdeal J A B a E α (op V) q hq⟩ =
      (presentationConormalSequence.{v, u, w, z} J A B a E α).X₁.val.map n.op y)
    (hsq : q ∈ kernelIdeal (polynomialEvaluation J A B E a α) (op V) ^ 2) :
    (vanishingSieve (presentationConormalSequence.{v, u, w, z} J A B a E α).X₁.val y).arrows n := by
  have hmem : (polynomialUnit J A E).app (op V) q ∈
      kernelIdeal (presentation J A B a E α).hom (op V) ^ 2 :=
    map_mem_ker_sq_of_fac ((polynomialEvaluation J A B E a α).app (op V))
      ((presentation J A B a E α).hom.app (op V)) ((polynomialUnit J A E).app (op V))
      (polynomialUnit_app_comp_presentation_app J A B a E α (op V)) hsq
  have hzero := conormalClass_eq_zero_of_mem_sq.{v, u, w, z} J A (freeAlgebraSheaf J A E) B
    (freeAlgebraSheafCoefficientMap J A E) (presentation J A B a E α) (op V)
    ⟨(polynomialUnit J A E).app (op V) q,
      polynomialUnit_mem_kernelIdeal J A B a E α (op V) q hq⟩ hmem
  exact hqc.symm.trans hzero

end OnePresentation

/-! ### Morphisms of presentations -/

section MorphismOfPresentations

variable (E₁ E₂ : Functor Cᵒᵖ (Type w)) (h : E₁ ⟶ E₂)
  (α₁ : E₁ ⟶ underlyingPresheaf J B) (α₂ : E₂ ⟶ underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E₁ α₁).hom]
  [Presheaf.IsLocallySurjective J (presentation J A B a E₂ α₂).hom]
  (hα : h ≫ α₂ = α₁)

include hα in
omit [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The conormal class of the image of a local section vanishes.**  If the conormal class of a
section `x` of the first kernel ideal is the restriction along `g` of a section `y` killed by
the map of conormal sheaves of the factorisation, then the conormal class of the image of `x`
in `A[E₂]` is zero: the map of conormal sheaves sends the one class to the other, and it sends
the restriction of `y` to the restriction of zero. -/
theorem conormalClass_freeAlgebraMap_eq_zero {X Y : C}
    (y : (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).X₁.val.obj (op X)) (g : Y ⟶ X)
    (x : kernelIdeal (presentation J A B a E₁ α₁).hom (op Y))
    (hxc : conormalClass.{v, u, w, z} J A (freeAlgebraSheaf J A E₁) B
        (freeAlgebraSheafCoefficientMap J A E₁) (presentation J A B a E₁ α₁) (op Y) x =
      (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).X₁.val.map g.op y)
    (hy : (conormalSheafMapOfFac.{v, u, w, z} J B (freeAlgebraSheaf J A E₁)
        (freeAlgebraSheaf J A E₂) (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
        (freeAlgebraMap J A E₁ E₂ h)
        (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα)).val.app (op X) y = 0) :
    conormalClass.{v, u, w, z} J A (freeAlgebraSheaf J A E₂) B
        (freeAlgebraSheafCoefficientMap J A E₂) (presentation J A B a E₂ α₂) (op Y)
        ⟨(freeAlgebraMap J A E₁ E₂ h).hom.app (op Y)
            (x : (freeAlgebraSheaf J A E₁).obj.obj (op Y)),
          kernelIdeal_le_comap (presentation J A B a E₁ α₁).hom
            (presentation J A B a E₂ α₂).hom (freeAlgebraMap J A E₁ E₂ h).hom
            (hom_of_comp_eq (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα))
            (op Y) x.2⟩ = 0 := by
  have hclass := conormalSheafMapOfFac_conormalClass.{v, u, w, z} J A B
    (freeAlgebraSheaf J A E₁) (freeAlgebraSheaf J A E₂)
    (freeAlgebraSheafCoefficientMap J A E₁) (freeAlgebraSheafCoefficientMap J A E₂)
    (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂) (freeAlgebraMap J A E₁ E₂ h)
    (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα) (op Y) x
  refine hclass.symm.trans ?_
  refine Eq.trans (congrArg ((conormalSheafMapOfFac.{v, u, w, z} J B
    (freeAlgebraSheaf J A E₁) (freeAlgebraSheaf J A E₂) (presentation J A B a E₁ α₁)
    (presentation J A B a E₂ α₂) (freeAlgebraMap J A E₁ E₂ h)
    (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα)).val.app (op Y)) hxc) ?_
  refine Eq.trans (PresheafOfModules.naturality_apply
    (conormalSheafMapOfFac.{v, u, w, z} J B (freeAlgebraSheaf J A E₁)
      (freeAlgebraSheaf J A E₂) (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
      (freeAlgebraMap J A E₁ E₂ h)
      (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα)).val g.op y) ?_
  refine Eq.trans (congrArg
    ((presentationConormalSequence.{v, u, w, z} J A B a E₂ α₂).X₁.val.map g.op) hy) ?_
  exact map_zero
    ((presentationConormalSequence.{v, u, w, z} J A B a E₂ α₂).X₁.val.map g.op).hom

include hα in
/-- **The fourth covering: descending the square membership.**  A polynomial `q` over `W` in the
kernel of the first model, all of whose partial derivatives lie in that kernel and whose
renaming lies in the square of the kernel of the second model, and whose conormal class is the
restriction of `y` along `n`, makes the vanishing sieve of `y` cover `n`: over a covering sieve
of `W` every restriction of `q` lies in the square of the kernel of the first model, by
`Stacks.Sites.FreeAlgebra.exists_covering_mem_ker_sq_polynomialPresheafMap`, and over every
arrow of that sieve `Stacks.SheafOfModules.vanishingSieve_arrows_of_mem_ker_sq` applies. -/
theorem covers_vanishingSieve_of_forall_pderiv_mem {X W : C}
    (y : (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).X₁.val.obj (op X))
    (n : W ⟶ X) (q : (polynomialPresheaf J A E₁).obj (op W))
    (hq : q ∈ kernelIdeal (polynomialEvaluation J A B E₁ a α₁) (op W))
    (hpd : ∀ i : E₁.obj (op W), MvPolynomial.pderiv i q ∈
      kernelIdeal (polynomialEvaluation J A B E₁ a α₁) (op W))
    (hsq : (polynomialPresheafMap J A h).app (op W) q ∈
      kernelIdeal (polynomialEvaluation J A B E₂ a α₂) (op W) ^ 2)
    (hqc : conormalClass.{v, u, w, z} J A (freeAlgebraSheaf J A E₁) B
        (freeAlgebraSheafCoefficientMap J A E₁) (presentation J A B a E₁ α₁) (op W)
        ⟨(polynomialUnit J A E₁).app (op W) q,
          polynomialUnit_mem_kernelIdeal J A B a E₁ α₁ (op W) q hq⟩ =
      (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).X₁.val.map n.op y) :
    J.Covers (vanishingSieve
      (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).X₁.val y) n := by
  obtain ⟨S, hS, hker⟩ := exists_covering_mem_ker_sq_polynomialPresheafMap J A B a E₁ E₂ h
    α₁ α₂ hα q hq hpd hsq
  refine covers_of_forall_covers J _ n S hS (fun V m hm ↦ ?_)
  refine J.arrow_max (m ≫ n) _ ?_
  exact vanishingSieve_arrows_of_mem_ker_sq.{v, u, w, z} J A B a E₁ α₁ y (m ≫ n)
    ((polynomialPresheaf J A E₁).map m.op q)
    (map_kernel (polynomialEvaluation J A B E₁ a α₁) m.op hq)
    (conormalClass_polynomialUnit_map_eq.{v, u, w, z} J A B a E₁ α₁ y n q hq hqc m)
    (hker V m hm)

include hα in
/-- **The third covering: the derivative criterion and the square on the polynomial model.**  A
polynomial `q` over `Z` in the kernel of the first model whose image in `A[E₁]` has vanishing
universal differential, whose renaming has its image in `A[E₂]` in the square of the second
kernel ideal, and whose conormal class is the restriction of `y` along `n`, makes the vanishing
sieve of `y` cover `n`.

Two coverings of `Z` are taken together: on one all partial derivatives of every restriction of
`q` lie in the kernel of the first model, by
`Stacks.Sites.FreeAlgebra.exists_covering_forall_pderiv_mem`; on the other every restriction of
the renaming of `q` lies in the square of the kernel of the second model, by
`Stacks.Sites.FreeAlgebra.exists_covering_mem_ker_sq_polynomialUnit`.  Over an arrow of the
intersection both hypotheses of
`Stacks.SheafOfModules.covers_vanishingSieve_of_forall_pderiv_mem` hold for the restricted
polynomial, the second because renaming commutes with restriction. -/
theorem covers_vanishingSieve_of_polynomialUnit_mem_ker_sq {X Z : C}
    (y : (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).X₁.val.obj (op X))
    (n : Z ⟶ X) (q : (polynomialPresheaf J A E₁).obj (op Z))
    (hq : q ∈ kernelIdeal (polynomialEvaluation J A B E₁ a α₁) (op Z))
    (hqd : tensorDifferential.{v, u, w, z} J A (freeAlgebraSheaf J A E₁) B
      (freeAlgebraSheafCoefficientMap J A E₁) (presentation J A B a E₁ α₁) (op Z)
      ((polynomialUnit J A E₁).app (op Z) q) = 0)
    (hs₂ : (polynomialUnit J A E₂).app (op Z) ((polynomialPresheafMap J A h).app (op Z) q) ∈
      kernelIdeal (presentation J A B a E₂ α₂).hom (op Z) ^ 2)
    (hqc : conormalClass.{v, u, w, z} J A (freeAlgebraSheaf J A E₁) B
        (freeAlgebraSheafCoefficientMap J A E₁) (presentation J A B a E₁ α₁) (op Z)
        ⟨(polynomialUnit J A E₁).app (op Z) q,
          polynomialUnit_mem_kernelIdeal J A B a E₁ α₁ (op Z) q hq⟩ =
      (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).X₁.val.map n.op y) :
    J.Covers (vanishingSieve
      (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).X₁.val y) n := by
  obtain ⟨S, hS, hder⟩ := exists_covering_forall_pderiv_mem.{v, u, w, z} J A B E₁ a α₁
    (op Z) ⟨q, hq⟩ hqd
  obtain ⟨T, hT, hsq⟩ := exists_covering_mem_ker_sq_polynomialUnit J A B E₂ a α₂
    ((polynomialPresheafMap J A h).app (op Z) q) hs₂
  refine covers_of_forall_covers J _ n (S ⊓ T) (J.intersection_covering hS hT)
    (fun W m hm ↦ ?_)
  have hnat := NatTrans.naturality_apply (polynomialPresheafMap J A h) m.op q
  refine covers_vanishingSieve_of_forall_pderiv_mem.{v, u, w, z} J A B a E₁ E₂ h α₁ α₂ hα y
    (m ≫ n) ((polynomialPresheaf J A E₁).map m.op q)
    (map_kernel (polynomialEvaluation J A B E₁ a α₁) m.op hq) (hder W m hm.1) ?_
    (conormalClass_polynomialUnit_map_eq.{v, u, w, z} J A B a E₁ α₁ y n q hq hqc m)
  rw [hnat]
  exact hsq W m hm.2

include hα in
/-- **The vanishing sieve of a local section killed by both maps is a covering sieve.**  This is
the local injectivity half of Stacks 08TY in degree `-1`, in the form that
`Stacks.Sites.Conormal.isLocallyInjective_kernelMapOfFac` consumes: a section of the conormal
sheaf of the first presentation killed both by the first conormal map and by the map of
conormal sheaves of the factorisation restricts to zero on a covering sieve.

The proof composes two coverings and then calls
`Stacks.SheafOfModules.covers_vanishingSieve_of_polynomialUnit_mem_ker_sq`, which supplies the
remaining two.  The second level takes together the covering on which the image in `A[E₂]` of
the representing section lies in the square of the second kernel ideal — the representing
section's conormal class is killed by the map of conormal sheaves, so
`Stacks.Sites.Conormal.exists_covering_mem_ker_sq_of_conormalClass_eq_zero` applies — and the
covering on which that section comes from an honest polynomial. -/
theorem vanishingSieve_presentationConormal_mem (X : C)
    (y : (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).X₁.val.obj (op X))
    (h₁ : (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).f.val.app (op X) y = 0)
    (h₂ : (conormalSheafMapOfFac.{v, u, w, z} J B (freeAlgebraSheaf J A E₁)
        (freeAlgebraSheaf J A E₂) (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
        (freeAlgebraMap J A E₁ E₂ h)
        (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα)).val.app (op X) y = 0) :
    vanishingSieve
      (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).X₁.val y ∈ J X := by
  obtain ⟨S, hS, hcl⟩ := exists_covering_conormalClass_eq_tensorDifferential_eq_zero.{v, u, w, z}
    J A (freeAlgebraSheaf J A E₁) B (freeAlgebraSheafCoefficientMap J A E₁)
    (presentation J A B a E₁ α₁) X y h₁
  refine J.transitive hS _ (fun Y g hgS ↦ ?_)
  obtain ⟨x, hxc, hxd⟩ := hcl Y g hgS
  obtain ⟨T, hT, hker⟩ := exists_covering_mem_ker_sq_of_conormalClass_eq_zero.{v, u, w, z}
    J A (freeAlgebraSheaf J A E₂) B (freeAlgebraSheafCoefficientMap J A E₂)
    (presentation J A B a E₂ α₂) Y _
    (conormalClass_freeAlgebraMap_eq_zero.{v, u, w, z} J A B a E₁ E₂ h α₁ α₂ hα y g x hxc h₂)
  obtain ⟨U, hU, hpol⟩ := exists_covering_polynomial_kernelIdeal_lift J A B E₁ a α₁
    (x : (freeAlgebraSheaf J A E₁).obj.obj (op Y)) x.2
  refine covers_of_forall_covers J _ g (T ⊓ U) (J.intersection_covering hT hU)
    (fun Z k hk ↦ ?_)
  obtain ⟨q, hqker, hqunit⟩ := hpol Z k hk.2
  have hu₂ : (polynomialUnit J A E₂).app (op Z) ((polynomialPresheafMap J A h).app (op Z) q) =
      (freeAlgebraMap J A E₁ E₂ h).hom.app (op Z) ((polynomialUnit J A E₁).app (op Z) q) :=
    congrArg
      (fun t : polynomialPresheaf J A E₁ ⟶ (freeAlgebraSheaf J A E₂).obj ↦ t.app (op Z) q)
      (polynomialPresheafMap_comp_polynomialUnit J A h)
  have hchain : (polynomialUnit J A E₂).app (op Z)
        ((polynomialPresheafMap J A h).app (op Z) q) =
      (freeAlgebraSheaf J A E₂).obj.map k.op ((freeAlgebraMap J A E₁ E₂ h).hom.app (op Y)
        (x : (freeAlgebraSheaf J A E₁).obj.obj (op Y))) :=
    hu₂.trans ((congrArg ((freeAlgebraMap J A E₁ E₂ h).hom.app (op Z)) hqunit).trans
      (NatTrans.naturality_apply (freeAlgebraMap J A E₁ E₂ h).hom k.op
        (x : (freeAlgebraSheaf J A E₁).obj.obj (op Y))))
  refine covers_vanishingSieve_of_polynomialUnit_mem_ker_sq.{v, u, w, z} J A B a E₁ E₂ h
    α₁ α₂ hα y (k ≫ g) q hqker
    (tensorDifferential_eq_zero_of_map.{v, u, w, z} J A B a E₁ α₁ k.op
      (x : (freeAlgebraSheaf J A E₁).obj.obj (op Y)) hxd
      ((polynomialUnit J A E₁).app (op Z) q) hqunit) ?_
    (conormalClass_polynomialUnit_eq.{v, u, w, z} J A B a E₁ α₁ y g x hxc k q hqker hqunit)
  rw [hchain]
  exact hker Z k hk.1

variable [hsh : HasSheafify J AddCommGrpCat.{max w u v z}]

include hα hsh in
/-- **Stacks 08TY in degree `-1`, local injectivity.**  The map on the kernels of the two
conormal maps induced by a morphism of polynomial presentations is locally injective.  This is
`Stacks.Sites.Conormal.isLocallyInjective_kernelMapOfFac` applied to
`Stacks.SheafOfModules.vanishingSieve_presentationConormal_mem`. -/
theorem isLocallyInjective_presentationKernelMap :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf B).val).map
        (kernelMapOfFac.{v, u, w, z} J A B (freeAlgebraSheaf J A E₁) (freeAlgebraSheaf J A E₂)
          (freeAlgebraSheafCoefficientMap J A E₁) (freeAlgebraSheafCoefficientMap J A E₂)
          (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
          (freeAlgebraMap J A E₁ E₂ h)
          (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα)
          (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A E₁ E₂ h)).val) :=
  isLocallyInjective_kernelMapOfFac.{v, u, w, z} J A B
    (freeAlgebraSheaf J A E₁) (freeAlgebraSheaf J A E₂)
    (freeAlgebraSheafCoefficientMap J A E₁) (freeAlgebraSheafCoefficientMap J A E₂)
    (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
    (freeAlgebraMap J A E₁ E₂ h)
    (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα)
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A E₁ E₂ h)
    (vanishingSieve_presentationConormal_mem.{v, u, w, z} J A B a E₁ E₂ h α₁ α₂ hα)

include hα hsh in
/-- **Stacks 08TY in degree `-1`.**  The map on the kernels of the two conormal maps induced by
a morphism of polynomial presentations is an isomorphism.  A morphism of sheaves of modules
which is locally injective and locally surjective is an isomorphism, and both halves are now
available: `Stacks.SheafOfModules.isLocallyInjective_presentationKernelMap` and
`Stacks.SheafOfModules.isLocallySurjective_presentationKernelMap`. -/
theorem isIso_presentationKernelMap :
    IsIso (kernelMapOfFac.{v, u, w, z} J A B
      (freeAlgebraSheaf J A E₁) (freeAlgebraSheaf J A E₂)
      (freeAlgebraSheafCoefficientMap J A E₁) (freeAlgebraSheafCoefficientMap J A E₂)
      (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
      (freeAlgebraMap J A E₁ E₂ h)
      (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα)
      (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A E₁ E₂ h)) := by
  have := isLocallyInjective_presentationKernelMap.{v, u, w, z} J A B a E₁ E₂ h α₁ α₂ hα
  have := isLocallySurjective_presentationKernelMap.{v, u, w, z} J A B a E₁ E₂ h α₁ α₂ hα
  exact isIso_of_isLocallyBijective _

end MorphismOfPresentations

end Stacks.SheafOfModules

end
