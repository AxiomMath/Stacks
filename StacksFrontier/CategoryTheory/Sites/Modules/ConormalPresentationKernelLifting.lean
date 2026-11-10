module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalKernelLocalSurjective
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPolynomialSubstitution
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalTensorDifferentialLocal
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangent
public import StacksFrontier.CategoryTheory.Sites.Modules.PolynomialPresheafMap
public import StacksFrontier.CategoryTheory.Sites.Modules.PolynomialPresheafSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lifting a conormal class along a morphism of polynomial presentations

Let `α₁ : E₁ ⟶ B` and `α₂ : E₂ ⟶ B` be two families of generators of a sheaf of commutative
rings `B` over `A` on a site, and let `h : E₁ ⟶ E₂` be a morphism of families with
`h ≫ α₂ = α₁`.  Writing `K₁` and `K₂` for the kernels of the two presentations `A[E₁] ⟶ B` and
`A[E₂] ⟶ B`, the induced map `Ker(K₁/K₁² ⟶ ⋯) ⟶ Ker(K₂/K₂² ⟶ ⋯)` is the degree `-1`
comparison map of the two naive cotangent complexes.  This file proves that it is locally
surjective, by showing that the lifting sieve of
`Stacks.Sites.Conormal.conormalKernelLiftSieve` is a covering sieve.

The proof is local and composes four coverings.  Over a covering of the given object the
section of the conormal sheaf of `α₂` is the conormal class of a section of the kernel ideal
whose universal differential vanishes; over a further covering that section comes from an
honest polynomial `q` on the polynomial model `A(-)[E₂(-)]`; over a third covering all partial
derivatives of `q` lie in the kernel of the model; and over a fourth covering the images in `B`
of the finitely many variables occurring in `q` lift through the first presentation.  At that
point the ring-level substitution engine
`Stacks.Sites.Conormal.exists_mem_ker_sub_mem_sq_of_vars_lift` applies and produces the
required section over the first presentation.

## Main results

* `Stacks.SheafOfModules.conormalKernelLiftSieve_arrows_of_vars_lift`: the ring-level step, that
  a polynomial representing the section, with all partial derivatives in the kernel and with its
  variables lifted, puts one single arrow in the lifting sieve.
* `Stacks.SheafOfModules.conormalKernelLiftSieve_mem`: **the lifting sieve of a morphism of
  polynomial presentations is a covering sieve.**
* `Stacks.SheafOfModules.isLocallySurjective_presentationKernelMap`: **Stacks 08TY in degree
  `-1`, local surjectivity.**  The degree `-1` comparison map of the two naive cotangent
  complexes is locally surjective.

## Implementation notes

Each of the four coverings is composed with the next by
`Stacks.SheafOfModules.covers_of_forall_covers`, which is
`CategoryTheory.GrothendieckTopology.transitive` phrased for a sieve on the source of a
composite arrow; that is what keeps the nesting of the four coverings linear instead of
quadratic.

Two spellings of the first term of a conormal sequence, as
`Stacks.Sites.Conormal.conormalSheaf` and as the first term of
`Stacks.Sites.Conormal.conormalSequence`, are definitionally equal only at default
transparency, so a goal mentioning both is not type-correct at the transparency `rw` and `simp`
check their motives at.  Every step on a conormal class is therefore composed with `Eq.trans`
and `congrArg`, and the proof is split into one named lemma per covering so that no single
declaration has to elaborate the whole chain.

The partial derivatives of a restriction of a polynomial are *not* the restrictions of its
partial derivatives — restriction renames the variables — so the hypothesis carried by
`Stacks.SheafOfModules.covers_conormalKernelLiftSieve_of_forall_pderiv_mem` quantifies over all
further arrows rather than over the one object where the polynomial lives.

## References

* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), the independence of the
  naive cotangent complex from the presentation, whose degree `-1` local surjectivity this is.
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

/-- On an essentially `z`-small site, presheaves of abelian groups in universe `z` admit a
sheafification. -/
local instance [EssentiallySmall.{z} C] : HasSheafify J AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteHasSheafify (J := J)

/-- On an essentially `z`-small site, the morphisms of presheaves of abelian groups in universe
`z` inverted by sheafification are exactly the locally bijective ones. -/
local instance [EssentiallySmall.{z} C] : J.WEqualsLocallyBijective AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective (J := J)

/-- **Chaining two coverings along a composite arrow.**  If `S` is a covering sieve of `Y` and
a sieve `T` of `X` covers `g ≫ n` for every arrow `g` of `S`, then `T` covers `n`. -/
@[sga "4 II 1.1" "more general"]
theorem covers_of_forall_covers {X Y : C} (T : Sieve X) (n : Y ⟶ X) (S : Sieve Y)
    (hS : S ∈ J Y) (hT : ∀ (Z : C) (g : Z ⟶ Y), S.arrows g → J.Covers T (g ≫ n)) :
    J.Covers T n := by
  refine J.transitive hS (T.pullback n) (fun Z g hg ↦ ?_)
  rw [← Sieve.pullback_comp]
  exact hT Z g hg

variable [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)

/-! ### One presentation -/

section OnePresentation

variable (E : Functor Cᵒᵖ (Type w)) (α : E ⟶ underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom]

omit [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom] in
omit [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The sheafification unit of the presheaf of polynomial rings is a factorisation of the
polynomial model of a presentation through the presentation itself, read on the sections over
one object of the site. -/
theorem polynomialUnit_app_comp_presentation_app (X : Cᵒᵖ) :
    (polynomialUnit J A E).app X ≫ (presentation J A B a E α).hom.app X =
      (polynomialEvaluation J A B E a α).app X :=
  NatTrans.congr_app (polynomialUnit_comp_desc J A B E a α) X

omit [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom] in
omit [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- A polynomial lying in the kernel of the polynomial model of a presentation has its image in
`A[E]` in the kernel ideal of the presentation. -/
theorem polynomialUnit_mem_kernelIdeal (X : Cᵒᵖ) (p : (polynomialPresheaf J A E).obj X)
    (hp : p ∈ kernelIdeal (polynomialEvaluation J A B E a α) X) :
    (polynomialUnit J A E).app X p ∈ kernelIdeal (presentation J A B a E α).hom X :=
  mem_ker_of_fac ((polynomialEvaluation J A B E a α).app X)
    ((presentation J A B a E α).hom.app X) ((polynomialUnit J A E).app X)
    (polynomialUnit_app_comp_presentation_app J A B a E α X) hp

omit [J.WEqualsLocallyBijective CommRingCat]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The universal differential of a restriction of a vanishing section vanishes.**  A section
of `A[E]` whose universal differential in `B ⊗[A[E]] Ω[A[E]/A]` is zero has the same property
for any section that restricts from it. -/
theorem tensorDifferential_eq_zero_of_map {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : (freeAlgebraSheaf J A E).obj.obj X)
    (hx : tensorDifferential.{v, u, w, z} J A (freeAlgebraSheaf J A E) B
      (freeAlgebraSheafCoefficientMap J A E) (presentation J A B a E α) X x = 0)
    (y : (freeAlgebraSheaf J A E).obj.obj Y)
    (hy : y = (freeAlgebraSheaf J A E).obj.map f x) :
    tensorDifferential.{v, u, w, z} J A (freeAlgebraSheaf J A E) B
      (freeAlgebraSheafCoefficientMap J A E) (presentation J A B a E α) Y y = 0 := by
  refine Eq.trans (congrArg (tensorDifferential.{v, u, w, z} J A (freeAlgebraSheaf J A E) B
    (freeAlgebraSheafCoefficientMap J A E) (presentation J A B a E α) Y) hy) ?_
  refine Eq.trans (tensorDifferential_map.{v, u, w, z} J A (freeAlgebraSheaf J A E) B
    (freeAlgebraSheafCoefficientMap J A E) (presentation J A B a E α) f x) ?_
  refine Eq.trans (congrArg
    ((presentationConormalSequence.{v, u, w, z} J A B a E α).X₂.val.map f) hx) ?_
  exact map_zero ((presentationConormalSequence.{v, u, w, z} J A B a E α).X₂.val.map f).hom

omit [J.WEqualsLocallyBijective CommRingCat]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **A polynomial lift of a restriction represents the restricted conormal class.**  If the
conormal class of a section `x` of the kernel ideal over `Y` is the restriction along `g` of a
section `c` of the conormal sheaf, and a polynomial `q` over `Z` has for image in `A[E]` the
restriction of `x` along `k`, then the conormal class of that image is the restriction of `c`
along `k ≫ g`. -/
theorem conormalClass_polynomialUnit_eq {X Y Z : C}
    (c : (presentationConormalSequence.{v, u, w, z} J A B a E α).X₁.val.obj (op X)) (g : Y ⟶ X)
    (x : kernelIdeal (presentation J A B a E α).hom (op Y))
    (hx : conormalClass.{v, u, w, z} J A (freeAlgebraSheaf J A E) B
        (freeAlgebraSheafCoefficientMap J A E) (presentation J A B a E α) (op Y) x =
      (presentationConormalSequence.{v, u, w, z} J A B a E α).X₁.val.map g.op c)
    (k : Z ⟶ Y) (q : (polynomialPresheaf J A E).obj (op Z))
    (hq : q ∈ kernelIdeal (polynomialEvaluation J A B E a α) (op Z))
    (hqu : (polynomialUnit J A E).app (op Z) q =
      (freeAlgebraSheaf J A E).obj.map k.op (x : (freeAlgebraSheaf J A E).obj.obj (op Y))) :
    conormalClass.{v, u, w, z} J A (freeAlgebraSheaf J A E) B
        (freeAlgebraSheafCoefficientMap J A E) (presentation J A B a E α) (op Z)
        ⟨(polynomialUnit J A E).app (op Z) q,
          polynomialUnit_mem_kernelIdeal J A B a E α (op Z) q hq⟩ =
      (presentationConormalSequence.{v, u, w, z} J A B a E α).X₁.val.map (k ≫ g).op c := by
  have hmem : (freeAlgebraSheaf J A E).obj.map k.op (x : (freeAlgebraSheaf J A E).obj.obj (op Y))
      ∈ kernelIdeal (presentation J A B a E α).hom (op Z) :=
    map_kernel (presentation J A B a E α).hom k.op x.2
  refine Eq.trans (congrArg (conormalClass.{v, u, w, z} J A (freeAlgebraSheaf J A E) B
    (freeAlgebraSheafCoefficientMap J A E) (presentation J A B a E α) (op Z))
    (Subtype.ext hqu :
      (⟨(polynomialUnit J A E).app (op Z) q,
          polynomialUnit_mem_kernelIdeal J A B a E α (op Z) q hq⟩ :
        kernelIdeal (presentation J A B a E α).hom (op Z)) = ⟨_, hmem⟩)) ?_
  refine Eq.trans (conormalClass_map.{u, v, w, z} J A (freeAlgebraSheaf J A E) B
    (freeAlgebraSheafCoefficientMap J A E) (presentation J A B a E α) k.op x ⟨_, hmem⟩ rfl) ?_
  refine Eq.trans (congrArg
    ((presentationConormalSequence.{v, u, w, z} J A B a E α).X₁.val.map k.op) hx) ?_
  exact ((presentationConormalSequence.{v, u, w, z} J A B a E α).X₁.val.map_comp_apply
    g.op k.op c).symm

omit [J.WEqualsLocallyBijective CommRingCat]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The class equation of a polynomial representative is stable under restriction.**  If the
conormal class of the image in `A[E]` of a polynomial `q` in the kernel over `Z` is the
restriction of `c` along `n`, then for every `m : V ⟶ Z` the conormal class of the image of the
restriction of `q` along `m` is the restriction of `c` along `m ≫ n`. -/
theorem conormalClass_polynomialUnit_map_eq {X Z V : C}
    (c : (presentationConormalSequence.{v, u, w, z} J A B a E α).X₁.val.obj (op X)) (n : Z ⟶ X)
    (q : (polynomialPresheaf J A E).obj (op Z))
    (hq : q ∈ kernelIdeal (polynomialEvaluation J A B E a α) (op Z))
    (hqc : conormalClass.{v, u, w, z} J A (freeAlgebraSheaf J A E) B
        (freeAlgebraSheafCoefficientMap J A E) (presentation J A B a E α) (op Z)
        ⟨(polynomialUnit J A E).app (op Z) q,
          polynomialUnit_mem_kernelIdeal J A B a E α (op Z) q hq⟩ =
      (presentationConormalSequence.{v, u, w, z} J A B a E α).X₁.val.map n.op c)
    (m : V ⟶ Z) :
    conormalClass.{v, u, w, z} J A (freeAlgebraSheaf J A E) B
        (freeAlgebraSheafCoefficientMap J A E) (presentation J A B a E α) (op V)
        ⟨(polynomialUnit J A E).app (op V) ((polynomialPresheaf J A E).map m.op q),
          polynomialUnit_mem_kernelIdeal J A B a E α (op V)
            ((polynomialPresheaf J A E).map m.op q)
            (map_kernel (polynomialEvaluation J A B E a α) m.op hq)⟩ =
      (presentationConormalSequence.{v, u, w, z} J A B a E α).X₁.val.map (m ≫ n).op c :=
  conormalClass_polynomialUnit_eq.{v, u, w, z} J A B a E α c n
    ⟨(polynomialUnit J A E).app (op Z) q,
      polynomialUnit_mem_kernelIdeal J A B a E α (op Z) q hq⟩ hqc m
    ((polynomialPresheaf J A E).map m.op q)
    (map_kernel (polynomialEvaluation J A B E a α) m.op hq)
    (NatTrans.naturality_apply (polynomialUnit J A E) m.op q)

end OnePresentation

/-! ### Morphisms of presentations -/

section MorphismOfPresentations

variable (E₁ E₂ : Functor Cᵒᵖ (Type w)) (h : E₁ ⟶ E₂)
  (α₁ : E₁ ⟶ underlyingPresheaf J B) (α₂ : E₂ ⟶ underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E₁ α₁).hom]
  [Presheaf.IsLocallySurjective J (presentation J A B a E₂ α₂).hom]
  (hα : h ≫ α₂ = α₁)

omit [J.WEqualsLocallyBijective CommRingCat]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The ring-level step: one arrow of the lifting sieve.**  Let `q` be a polynomial over `V`
lying in the kernel of the polynomial model of the second presentation, let all of its partial
derivatives lie there too, let the image in `B` of every variable occurring in `q` lift through
the polynomial model of the first presentation, and let the conormal class of the image of `q`
in `A[E₂]` be the restriction along `n` of a section `c`.  Then `n` belongs to the lifting
sieve of `c`. -/
theorem conormalKernelLiftSieve_arrows_of_vars_lift {X V : C}
    (c : (presentationConormalSequence.{v, u, w, z} J A B a E₂ α₂).X₁.val.obj (op X))
    (n : V ⟶ X) (q : (polynomialPresheaf J A E₂).obj (op V))
    (hq : q ∈ kernelIdeal (polynomialEvaluation J A B E₂ a α₂) (op V))
    (hpd : ∀ i : E₂.obj (op V), MvPolynomial.pderiv i q ∈
      kernelIdeal (polynomialEvaluation J A B E₂ a α₂) (op V))
    (hlift : ∀ i ∈ MvPolynomial.vars q, ∃ cc : (polynomialPresheaf J A E₁).obj (op V),
      (polynomialEvaluation J A B E₁ a α₁).app (op V) cc =
        (polynomialEvaluation J A B E₂ a α₂).app (op V) (MvPolynomial.X i))
    (hqc : conormalClass.{v, u, w, z} J A (freeAlgebraSheaf J A E₂) B
        (freeAlgebraSheafCoefficientMap J A E₂) (presentation J A B a E₂ α₂) (op V)
        ⟨(polynomialUnit J A E₂).app (op V) q,
          polynomialUnit_mem_kernelIdeal J A B a E₂ α₂ (op V) q hq⟩ =
      (presentationConormalSequence.{v, u, w, z} J A B a E₂ α₂).X₁.val.map n.op c) :
    (conormalKernelLiftSieve.{v, u, w, z} J A B (freeAlgebraSheaf J A E₁)
      (freeAlgebraSheaf J A E₂) (freeAlgebraSheafCoefficientMap J A E₁)
      (freeAlgebraSheafCoefficientMap J A E₂) (presentation J A B a E₁ α₁)
      (presentation J A B a E₂ α₂) (freeAlgebraMap J A E₁ E₂ h)
      (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα) c).arrows n := by
  obtain ⟨p, hpker, hpd0, hsub⟩ := exists_mem_ker_sub_mem_sq_of_vars_lift
    ((polynomialEvaluation J A B E₂ a α₂).app (op V))
    ((polynomialEvaluation J A B E₁ a α₁).app (op V))
    ((polynomialPresheafMap J A h).app (op V))
    ((polynomialCoefficientMap J A E₁).app (op V))
    (NatTrans.congr_app
      (polynomialPresheafMap_comp_polynomialEvaluation J A h B a α₁ α₂ hα) (op V))
    (NatTrans.congr_app (polynomialCoefficientMap_comp_polynomialPresheafMap J A h) (op V))
    q hq hpd hlift
  have hu2 : (polynomialUnit J A E₂).app (op V) ((polynomialPresheafMap J A h).app (op V) p) =
      (freeAlgebraMap J A E₁ E₂ h).hom.app (op V) ((polynomialUnit J A E₁).app (op V) p) :=
    congrArg
      (fun t : polynomialPresheaf J A E₁ ⟶ (freeAlgebraSheaf J A E₂).obj ↦ t.app (op V) p)
      (polynomialPresheafMap_comp_polynomialUnit J A h)
  have hsq := map_mem_ker_sq_of_fac ((polynomialEvaluation J A B E₂ a α₂).app (op V))
    ((presentation J A B a E₂ α₂).hom.app (op V)) ((polynomialUnit J A E₂).app (op V))
    (polynomialUnit_app_comp_presentation_app J A B a E₂ α₂ (op V)) hsub
  have hms : (polynomialUnit J A E₂).app (op V)
        ((polynomialPresheafMap J A h).app (op V) p - q) =
      (freeAlgebraMap J A E₁ E₂ h).hom.app (op V) ((polynomialUnit J A E₁).app (op V) p) -
        (polynomialUnit J A E₂).app (op V) q :=
    (map_sub ((polynomialUnit J A E₂).app (op V)).hom _ _).trans
      (congrArg (fun t : (freeAlgebraSheaf J A E₂).obj.obj (op V) ↦
        t - (polynomialUnit J A E₂).app (op V) q) hu2)
  have hsub2 : (freeAlgebraMap J A E₁ E₂ h).hom.app (op V)
        ((polynomialUnit J A E₁).app (op V) p) -
      (polynomialUnit J A E₂).app (op V) q ∈
      kernelIdeal (presentation J A B a E₂ α₂).hom (op V) ^ 2 :=
    Eq.mp (congrArg (fun t : (freeAlgebraSheaf J A E₂).obj.obj (op V) ↦
      t ∈ kernelIdeal (presentation J A B a E₂ α₂).hom (op V) ^ 2) hms) hsq
  refine ⟨⟨(polynomialUnit J A E₁).app (op V) p,
    polynomialUnit_mem_kernelIdeal J A B a E₁ α₁ (op V) p hpker⟩, ?_, ?_⟩
  · exact tensorDifferential_unit_eq_zero.{v, u, w, z} J A B E₁ a α₁ (op V) p hpd0
  · refine Eq.trans (conormalSheafMapOfFac_conormalClass.{v, u, w, z} J A B
      (freeAlgebraSheaf J A E₁) (freeAlgebraSheaf J A E₂)
      (freeAlgebraSheafCoefficientMap J A E₁) (freeAlgebraSheafCoefficientMap J A E₂)
      (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂) (freeAlgebraMap J A E₁ E₂ h)
      (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα) (op V) _) ?_
    refine Eq.trans ?_ hqc
    exact conormalClass_eq_of_sub_mem_sq.{v, u, w, z} J A (freeAlgebraSheaf J A E₂) B
      (freeAlgebraSheafCoefficientMap J A E₂) (presentation J A B a E₂ α₂) (op V) _ _ hsub2

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The fourth covering: lifting the variables.**  A polynomial `q` over `W` in the kernel of
the polynomial model of the second presentation, all of whose partial derivatives stay in that
kernel after any restriction, and whose conormal class is the restriction of `c` along `n`,
makes the lifting sieve of `c` cover `n`. -/
theorem covers_conormalKernelLiftSieve_of_forall_pderiv_mem {X W : C}
    (c : (presentationConormalSequence.{v, u, w, z} J A B a E₂ α₂).X₁.val.obj (op X))
    (n : W ⟶ X) (q : (polynomialPresheaf J A E₂).obj (op W))
    (hq : q ∈ kernelIdeal (polynomialEvaluation J A B E₂ a α₂) (op W))
    (hpd : ∀ (V : C) (m : V ⟶ W) (i : E₂.obj (op V)),
      MvPolynomial.pderiv i ((polynomialPresheaf J A E₂).map m.op q) ∈
        kernelIdeal (polynomialEvaluation J A B E₂ a α₂) (op V))
    (hqc : conormalClass.{v, u, w, z} J A (freeAlgebraSheaf J A E₂) B
        (freeAlgebraSheafCoefficientMap J A E₂) (presentation J A B a E₂ α₂) (op W)
        ⟨(polynomialUnit J A E₂).app (op W) q,
          polynomialUnit_mem_kernelIdeal J A B a E₂ α₂ (op W) q hq⟩ =
      (presentationConormalSequence.{v, u, w, z} J A B a E₂ α₂).X₁.val.map n.op c) :
    J.Covers (conormalKernelLiftSieve.{v, u, w, z} J A B (freeAlgebraSheaf J A E₁)
      (freeAlgebraSheaf J A E₂) (freeAlgebraSheafCoefficientMap J A E₁)
      (freeAlgebraSheafCoefficientMap J A E₂) (presentation J A B a E₁ α₁)
      (presentation J A B a E₂ α₂) (freeAlgebraMap J A E₁ E₂ h)
      (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα) c) n := by
  classical
  obtain ⟨S, hS, hvar⟩ := exists_covering_forall_exists_lift
    (polynomialEvaluation J A B E₁ a α₁) J
    ((MvPolynomial.vars q).image fun i ↦
      (polynomialEvaluation J A B E₂ a α₂).app (op W) (MvPolynomial.X i))
  refine covers_of_forall_covers J _ n S hS (fun V m hm ↦ ?_)
  refine J.arrow_max (m ≫ n) _ ?_
  refine conormalKernelLiftSieve_arrows_of_vars_lift.{v, u, w, z} J A B a E₁ E₂ h α₁ α₂ hα c
    (m ≫ n) ((polynomialPresheaf J A E₂).map m.op q)
    (map_kernel (polynomialEvaluation J A B E₂ a α₂) m.op hq) (hpd V m) ?_
    (conormalClass_polynomialUnit_map_eq.{v, u, w, z} J A B a E₂ α₂ c n q hq hqc m)
  intro i hi
  obtain ⟨e, he, hei⟩ := exists_vars_of_mem_vars_polynomialPresheaf_map J A E₂ m.op q hi
  obtain ⟨t, ht⟩ := hvar V m hm
    ((polynomialEvaluation J A B E₂ a α₂).app (op W) (MvPolynomial.X e))
    (Finset.mem_image_of_mem _ he)
  refine ⟨t, Eq.trans ht ?_⟩
  refine Eq.trans (congrArg ((underlyingPresheaf J B).map m.op)
    (polynomialEvaluation_app_X J A E₂ B a α₂ (op W) e)) ?_
  refine Eq.trans (NatTrans.naturality_apply α₂ m.op e).symm ?_
  refine Eq.trans (congrArg (α₂.app (op V)) hei) ?_
  exact (polynomialEvaluation_app_X J A E₂ B a α₂ (op V) i).symm

/-- **The lifting sieve of a morphism of polynomial presentations is a covering sieve.**  This
is the local surjectivity half of Stacks 08TY in degree `-1`: a section of the conormal sheaf
of the second presentation killed by its conormal map is, locally, the image of the conormal
class of a section of the kernel ideal of the first presentation whose universal differential
vanishes. -/
theorem conormalKernelLiftSieve_mem (X : C)
    (c : (presentationConormalSequence.{v, u, w, z} J A B a E₂ α₂).X₁.val.obj (op X))
    (hc : (presentationConormalSequence.{v, u, w, z} J A B a E₂ α₂).f.val.app (op X) c = 0) :
    conormalKernelLiftSieve.{v, u, w, z} J A B
        (freeAlgebraSheaf J A E₁) (freeAlgebraSheaf J A E₂)
        (freeAlgebraSheafCoefficientMap J A E₁) (freeAlgebraSheafCoefficientMap J A E₂)
        (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
        (freeAlgebraMap J A E₁ E₂ h)
        (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα) c ∈ J X := by
  obtain ⟨S, hS, hcl⟩ := exists_covering_conormalClass_eq_tensorDifferential_eq_zero.{v, u, w, z}
    J A (freeAlgebraSheaf J A E₂) B (freeAlgebraSheafCoefficientMap J A E₂)
    (presentation J A B a E₂ α₂) X c hc
  refine J.transitive hS _ (fun Y g hgS ↦ ?_)
  obtain ⟨x, hxc, hxd⟩ := hcl Y g hgS
  obtain ⟨S', hS', hpol⟩ := exists_covering_polynomial_kernelIdeal_lift J A B E₂ a α₂
    (x : (freeAlgebraSheaf J A E₂).obj.obj (op Y)) x.2
  refine covers_of_forall_covers J _ g S' hS' (fun Z k hkS' ↦ ?_)
  obtain ⟨q, hqker, hqunit⟩ := hpol Z k hkS'
  obtain ⟨S'', hS'', hder⟩ := exists_covering_forall_pderiv_mem.{v, u, w, z} J A B E₂ a α₂
    (op Z) ⟨q, hqker⟩
    (tensorDifferential_eq_zero_of_map.{v, u, w, z} J A B a E₂ α₂ k.op
      (x : (freeAlgebraSheaf J A E₂).obj.obj (op Y)) hxd
      ((polynomialUnit J A E₂).app (op Z) q) hqunit)
  refine covers_of_forall_covers J _ (k ≫ g) S'' hS'' (fun W l hlS'' ↦ ?_)
  refine covers_conormalKernelLiftSieve_of_forall_pderiv_mem.{v, u, w, z} J A B a E₁ E₂ h
    α₁ α₂ hα c (l ≫ k ≫ g) ((polynomialPresheaf J A E₂).map l.op q)
    (map_kernel (polynomialEvaluation J A B E₂ a α₂) l.op hqker) ?_
    (conormalClass_polynomialUnit_map_eq.{v, u, w, z} J A B a E₂ α₂ c (k ≫ g) q hqker
      (conormalClass_polynomialUnit_eq.{v, u, w, z} J A B a E₂ α₂ c g x hxc k q hqker hqunit) l)
  intro V m i
  have hcomp : (polynomialPresheaf J A E₂).map (m ≫ l).op q =
      (polynomialPresheaf J A E₂).map m.op ((polynomialPresheaf J A E₂).map l.op q) :=
    congrArg (fun t : (polynomialPresheaf J A E₂).obj (op Z) ⟶
      (polynomialPresheaf J A E₂).obj (op V) ↦ t q)
      ((polynomialPresheaf J A E₂).map_comp l.op m.op)
  rw [← hcomp]
  exact hder V (m ≫ l) (S''.downward_closed hlS'' m) i

/-- **Stacks 08TY in degree `-1`, local surjectivity.**  The map on the kernels of the two
conormal maps induced by a morphism of polynomial presentations is locally surjective. -/
theorem isLocallySurjective_presentationKernelMap :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf B).obj).map
        (kernelMapOfFac.{v, u, w, z} J A B (freeAlgebraSheaf J A E₁) (freeAlgebraSheaf J A E₂)
          (freeAlgebraSheafCoefficientMap J A E₁) (freeAlgebraSheafCoefficientMap J A E₂)
          (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
          (freeAlgebraMap J A E₁ E₂ h)
          (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα)
          (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A E₁ E₂ h)).val) :=
  isLocallySurjective_kernelMapOfFac.{v, u, w, z} J A B
    (freeAlgebraSheaf J A E₁) (freeAlgebraSheaf J A E₂)
    (freeAlgebraSheafCoefficientMap J A E₁) (freeAlgebraSheafCoefficientMap J A E₂)
    (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
    (freeAlgebraMap J A E₁ E₂ h)
    (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα)
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A E₁ E₂ h)
    (conormalKernelLiftSieve_mem.{v, u, w, z} J A B a E₁ E₂ h α₁ α₂ hα)

end MorphismOfPresentations

end Stacks.SheafOfModules

end
