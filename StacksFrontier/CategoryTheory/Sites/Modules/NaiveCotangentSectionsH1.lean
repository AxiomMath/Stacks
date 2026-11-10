module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPresentationKernelInjective
public import StacksFrontier.Cotangent.SheavesOfRings.NaiveComparisonArrow
public import StacksFrontier.RingTheory.NaiveCotangent.SquareMap

/-!
# The degree `-1` cohomology of `NL_{B/A}` is locally the `H₁` of the sections

Let `a : A ⟶ B` be a morphism of sheaves of commutative rings on a site.  For an object `U` the
canonical map of Stacks 0D0I on sections, `NL_{B(U)/A(U)} ⟶ NL_{B/A}(U)`
(`Stacks.SheafOfModules.sectionsNaiveCotangentComparison`), restricts to a map

`H₁(L_{B(U)/A(U)}) ⟶ Ker(NL_{B/A}^{-1}(U) ⟶ NL_{B/A}^0(U))`

from the first homology of the naive cotangent complex of the ring map `A(U) → B(U)` to the
sections over `U` of the kernel of the differential of `NL_{B/A}`, that is, of the degree `-1`
cohomology sheaf.  This file proves that this map is compatible with restriction and that it is
*locally bijective*: a local section of the kernel is, on a covering, in its image, and an
element of `H₁(L_{B(U)/A(U)})` whose image vanishes restricts to zero on a covering.

So the degree `-1` cohomology sheaf of `NL_{B/A}` is the sheaf associated to the presheaf
`U ↦ H₁(L_{B(U)/A(U)})`.  This is the site-level form of the first step of the proof of
Stacks 0D0I, with no hypothesis on the site; the stalkwise computation of the source is replaced
by the local study of the polynomial model of the canonical presentation, which is
`StacksFrontier.CategoryTheory.Sites.Modules.ConormalPolynomialModel` and
`StacksFrontier.CategoryTheory.Sites.Modules.ConormalPolynomialTensor`.

## Main definitions

* `Stacks.SheafOfModules.sectionsH1Restrict`: restriction `H₁(L_{B(U)/A(U)}) → H₁(L_{B(V)/A(V)})`
  along a morphism `V ⟶ U` of the site.
* `Stacks.SheafOfModules.sectionsH1Comparison`: the map `H₁(L_{B(U)/A(U)}) → NL_{B/A}^{-1}(U)`.

## Main results

* `Stacks.SheafOfModules.sectionsH1Comparison_d`: its image is killed by the differential.
* `Stacks.SheafOfModules.sectionsH1Comparison_smul`: it is linear over the sections of `B`.
* `Stacks.SheafOfModules.sectionsH1Comparison_restrict`: it commutes with restriction.
* `Stacks.SheafOfModules.sectionsH1LiftSieve_mem`: local surjectivity onto the kernel of the
  differential.
* `Stacks.SheafOfModules.sectionsH1VanishingSieve_mem`: local injectivity.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Algebra

universe v u w z

namespace Stacks.SheafOfModules

open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)

/-! ### The polynomial model of the canonical presentation, read as `Generators.self` -/

omit [HasWeakSheafify J CommRingCat.{w}] [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  in
/-- The kernel of the canonical presentation `A(U)[B(U)] → B(U)` of rings is the kernel of the
polynomial model of the canonical presentation of sheaves, evaluated at `U`. -/
theorem mem_selfKer_iff (U : Cᵒᵖ)
    (p : MvPolynomial (ToType (B.obj.obj U)) (ToType (A.obj.obj U))) :
    letI := algebraSections J A B a U
    p ∈ (Generators.self (ToType (A.obj.obj U)) (ToType (B.obj.obj U))).toExtension.ker ↔
      p ∈ kernelIdeal (polynomialEvaluation J A B (underlyingPresheaf J B) a (𝟙 _)) U := by
  let := algebraSections J A B a U
  change MvPolynomial.aeval _root_.id p = 0 ↔
    (MvPolynomial.eval₂Hom (a.hom.app U).hom _root_.id) p = 0
  rw [MvPolynomial.aeval_def]
  rfl

omit [HasWeakSheafify J CommRingCat.{w}] [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  in
/-- **The derivative criterion for `H₁`.**  The class of a polynomial of the kernel of the
canonical presentation of a ring map is a cycle of the naive cotangent complex exactly when all
of its partial derivatives lie in the kernel. -/
theorem cotangentComplex_mk_eq_zero_iff {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (q : (Generators.self R S).toExtension.ker) :
    (Generators.self R S).toExtension.cotangentComplex (Extension.Cotangent.mk q) = 0 ↔
      ∀ i : S, MvPolynomial.aeval (R := R) _root_.id (MvPolynomial.pderiv i q.1) = 0 := by
  have key : ∀ i : S, (Generators.self R S).cotangentSpaceBasis.repr
      ((Generators.self R S).toExtension.cotangentComplex (Extension.Cotangent.mk q)) i =
        MvPolynomial.aeval (R := R) _root_.id (MvPolynomial.pderiv i q.1) := fun i =>
    (congrArg (fun t => (Generators.self R S).cotangentSpaceBasis.repr t i)
      (Extension.cotangentComplex_mk (P := (Generators.self R S).toExtension) q)).trans
      ((Generators.self R S).cotangentSpaceBasis_repr_one_tmul q.1 i)
  refine ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · rw [← key, h, map_zero, Finsupp.zero_apply]
  · apply (Generators.self R S).cotangentSpaceBasis.repr.injective
    ext i
    rw [key, h, map_zero, Finsupp.zero_apply]

/-! ### Restriction of `H₁` of the sections -/

omit [HasWeakSheafify J CommRingCat.{w}] [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  in
/-- The square of rings attached to a morphism `f : U ⟶ V` of `Cᵒᵖ` commutes. -/
theorem sectionsSquare_comm {U V : Cᵒᵖ} (f : U ⟶ V) (r : ToType (A.obj.obj U)) :
    (B.obj.map f).hom ((a.hom.app U).hom r) = (a.hom.app V).hom ((A.obj.map f).hom r) :=
  (ConcreteCategory.congr_hom (a.hom.naturality f) r).symm

/-- **Restriction of `H₁` of the sections** along a morphism `f : U ⟶ V` of `Cᵒᵖ`: the map
`H₁(L_{B(U)/A(U)}) → H₁(L_{B(V)/A(V)})` induced by the square of restriction maps. -/
noncomputable def sectionsH1Restrict {U V : Cᵒᵖ} (f : U ⟶ V) :
    @H1Cotangent (ToType (A.obj.obj U)) (ToType (B.obj.obj U)) _ _
        (algebraSections J A B a U) →+
      @H1Cotangent (ToType (A.obj.obj V)) (ToType (B.obj.obj V)) _ _
        (algebraSections J A B a V) :=
  @NaiveCotangent.h1CotangentMapOfSquare _ _ _ _ _ _ _ _ (algebraSections J A B a U)
    (algebraSections J A B a V) (A.obj.map f).hom (B.obj.map f).hom
    (sectionsSquare_comm J A B a f)

omit [HasWeakSheafify J CommRingCat.{w}] [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  in
/-- On the class of a polynomial, restriction of `H₁` is the class of the restricted
polynomial in the polynomial model. -/
theorem sectionsH1Restrict_val {U V : Cᵒᵖ} (f : U ⟶ V)
    (z : @H1Cotangent (ToType (A.obj.obj U)) (ToType (B.obj.obj U)) _ _
      (algebraSections J A B a U))
    (g : letI := algebraSections J A B a U
      (Generators.self (ToType (A.obj.obj U)) (ToType (B.obj.obj U))).toExtension.ker)
    (hg : letI := algebraSections J A B a U
      z.1 = Extension.Cotangent.mk g) :
    letI := algebraSections J A B a U
    letI := algebraSections J A B a V
    (sectionsH1Restrict J A B a f z).1 = Extension.Cotangent.mk
      ⟨(polynomialPresheaf J A (underlyingPresheaf J B)).map f g.1,
        NaiveCotangent.selfRingHomOfSquare_mem_ker _ _ (sectionsSquare_comm J A B a f) g⟩ := by
  let := algebraSections J A B a U
  let := algebraSections J A B a V
  change NaiveCotangent.cotangentMapOfSquare _ _ (sectionsSquare_comm J A B a f) z.1 = _
  rw [hg]
  exact NaiveCotangent.cotangentMapOfSquare_mk _ _ _ g

omit [HasWeakSheafify J CommRingCat.{w}] [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  in
/-- Restriction of `H₁` of the sections is functorial. -/
theorem sectionsH1Restrict_comp {U V W : Cᵒᵖ} (f : U ⟶ V) (f' : V ⟶ W)
    (z : @H1Cotangent (ToType (A.obj.obj U)) (ToType (B.obj.obj U)) _ _
      (algebraSections J A B a U)) :
    sectionsH1Restrict J A B a (f ≫ f') z =
      sectionsH1Restrict J A B a f' (sectionsH1Restrict J A B a f z) := by
  let := algebraSections J A B a U
  let := algebraSections J A B a V
  let := algebraSections J A B a W
  obtain ⟨g, hg⟩ := Extension.Cotangent.mk_surjective z.1
  apply Subtype.ext
  have e1 := sectionsH1Restrict_val J A B a (f ≫ f') z g hg.symm
  have e2 := sectionsH1Restrict_val J A B a f' _ _ (sectionsH1Restrict_val J A B a f z g hg.symm)
  refine e1.trans (Eq.trans ?_ e2.symm)
  congr 2
  exact ((polynomialPresheaf J A (underlyingPresheaf J B)).map_comp_apply f f' g.1)

omit [HasWeakSheafify J CommRingCat.{w}] [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  in
/-- Restriction of `H₁` of the sections along an identity is the identity. -/
theorem sectionsH1Restrict_id (U : Cᵒᵖ)
    (z : @H1Cotangent (ToType (A.obj.obj U)) (ToType (B.obj.obj U)) _ _
      (algebraSections J A B a U)) :
    sectionsH1Restrict J A B a (𝟙 U) z = z := by
  let := algebraSections J A B a U
  obtain ⟨g, hg⟩ := Extension.Cotangent.mk_surjective z.1
  apply Subtype.ext
  refine (sectionsH1Restrict_val J A B a (𝟙 U) z g hg.symm).trans (Eq.trans ?_ hg)
  congr 2
  exact (polynomialPresheaf J A (underlyingPresheaf J B)).map_id_apply U g.1

/-! ### The comparison map on `H₁` -/

/-- The degree `-1` sections comparison restricted to `H₁(L_{B(U)/A(U)})`. -/
noncomputable def sectionsH1Comparison (U : Cᵒᵖ) :
    @H1Cotangent (ToType (A.obj.obj U)) (ToType (B.obj.obj U)) _ _
        (algebraSections J A B a U) →+
      ToType ((conormalSheaf.{v, u, w, z} J (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _))).val.obj U) :=
  letI := algebraSections J A B a U
  (sectionsConormalComparison.{v, u, w, z} J A B a U).toAddMonoidHom.comp
    (Extension.h1Cotangentι (P := (Generators.self (ToType (A.obj.obj U))
      (ToType (B.obj.obj U))).toExtension)).toAddMonoidHom

/-- On the class of a polynomial, the comparison is the conormal class of its image in the free
algebra sheaf. -/
theorem sectionsH1Comparison_apply (U : Cᵒᵖ)
    (z : @H1Cotangent (ToType (A.obj.obj U)) (ToType (B.obj.obj U)) _ _
      (algebraSections J A B a U))
    (g : letI := algebraSections J A B a U
      (Generators.self (ToType (A.obj.obj U)) (ToType (B.obj.obj U))).toExtension.ker)
    (hg : letI := algebraSections J A B a U
      z.1 = Extension.Cotangent.mk g) :
    sectionsH1Comparison.{v, u, w, z} J A B a U z =
      conormalClass.{v, u, w, z} J A (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _)) U
        ⟨freeAlgebraSectionsMap J A B U g.1,
          ker_le_comap_freeAlgebraSectionsMap J A B a U g.2⟩ := by
  let := algebraSections J A B a U
  change sectionsConormalComparison.{v, u, w, z} J A B a U z.1 = _
  rw [hg]
  exact sectionsConormalComparison_mk.{v, u, w, z} J A B a U g

/-- **The comparison is linear over the sections of `B`.** -/
theorem sectionsH1Comparison_smul (U : Cᵒᵖ) (b : ToType (B.obj.obj U))
    (z : @H1Cotangent (ToType (A.obj.obj U)) (ToType (B.obj.obj U)) _ _
      (algebraSections J A B a U)) :
    letI := algebraSections J A B a U
    sectionsH1Comparison.{v, u, w, z} J A B a U (b • z) =
      b • sectionsH1Comparison.{v, u, w, z} J A B a U z := by
  let := algebraSections J A B a U
  exact map_smul (sectionsConormalComparison.{v, u, w, z} J A B a U) b z.1

/-- **The image of a cycle is killed by the differential of `NL_{B/A}`.** -/
theorem sectionsH1Comparison_d (U : Cᵒᵖ)
    (z : @H1Cotangent (ToType (A.obj.obj U)) (ToType (B.obj.obj U)) _ _
      (algebraSections J A B a U)) :
    (presentationConormalSequence.{v, u, w, z} J A B a (underlyingPresheaf J B) (𝟙 _)).f.val.app U
        (sectionsH1Comparison.{v, u, w, z} J A B a U z) = 0 := by
  let := algebraSections J A B a U
  have h := LinearMap.congr_fun (sectionsComparison_comm.{v, u, w, z} J A B a U) z.1
  change sectionsDifferential.{v, u, w, z} J A B a U
    (sectionsConormalComparison.{v, u, w, z} J A B a U z.1) = 0
  refine h.trans ?_
  change sectionsTensorComparison.{v, u, w, z} J A B a U
    ((Generators.self (ToType (A.obj.obj U)) (ToType (B.obj.obj U))).toExtension.cotangentComplex
      z.1) = 0
  rw [show (Generators.self (ToType (A.obj.obj U))
      (ToType (B.obj.obj U))).toExtension.cotangentComplex z.1 = 0 from z.2, map_zero]

/-- **The comparison commutes with restriction.** -/
theorem sectionsH1Comparison_restrict {U V : Cᵒᵖ} (f : U ⟶ V)
    (z : @H1Cotangent (ToType (A.obj.obj U)) (ToType (B.obj.obj U)) _ _
      (algebraSections J A B a U)) :
    sectionsH1Comparison.{v, u, w, z} J A B a V (sectionsH1Restrict J A B a f z) =
      (conormalSheaf.{v, u, w, z} J (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _))).val.map f
        (sectionsH1Comparison.{v, u, w, z} J A B a U z) := by
  let := algebraSections J A B a U
  let := algebraSections J A B a V
  obtain ⟨g, hg⟩ := Extension.Cotangent.mk_surjective z.1
  refine (sectionsH1Comparison_apply.{v, u, w, z} J A B a V _ _
    (sectionsH1Restrict_val J A B a f z g hg.symm)).trans (Eq.trans ?_ (congrArg
      ((conormalSheaf.{v, u, w, z} J (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _))).val.map f)
      (sectionsH1Comparison_apply.{v, u, w, z} J A B a U z g hg.symm).symm))
  refine conormalClass_map.{u, v, w, z} J A (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
    (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
    (presentation J A B a (underlyingPresheaf J B) (𝟙 _)) f _ _ ?_
  exact (NatTrans.naturality_apply (polynomialUnit J A (underlyingPresheaf J B)) f g.1)

/-! ### Local surjectivity and local injectivity -/

/-- The arrows along which a local section of the conormal sheaf of `A[B] ⟶ B` restricts into
the image of the comparison map on `H₁`.  It is a sieve because the comparison commutes with
restriction. -/
def sectionsH1LiftSieve {X : C}
    (c : (conormalSheaf.{v, u, w, z} J (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
      (presentation J A B a (underlyingPresheaf J B) (𝟙 _))).val.obj (op X)) : Sieve X where
  arrows Y g := ∃ z : @H1Cotangent (ToType (A.obj.obj (op Y))) (ToType (B.obj.obj (op Y))) _ _
      (algebraSections J A B a (op Y)),
    sectionsH1Comparison.{v, u, w, z} J A B a (op Y) z =
      (conormalSheaf.{v, u, w, z} J (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _))).val.map g.op c
  downward_closed := by
    rintro Y Z g ⟨z, hz⟩ k
    refine ⟨sectionsH1Restrict J A B a k.op z, ?_⟩
    rw [sectionsH1Comparison_restrict, hz, op_comp]
    exact ((conormalSheaf.{v, u, w, z} J (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
      (presentation J A B a (underlyingPresheaf J B) (𝟙 _))).val.map_comp_apply g.op k.op c).symm

/-- The arrows along which an element of `H₁` of the sections restricts to zero. -/
def sectionsH1VanishingSieve {X : C}
    (z : @H1Cotangent (ToType (A.obj.obj (op X))) (ToType (B.obj.obj (op X))) _ _
      (algebraSections J A B a (op X))) : Sieve X where
  arrows Y g := sectionsH1Restrict J A B a g.op z = 0
  downward_closed := by
    intro Y Z g hg k
    rw [op_comp, sectionsH1Restrict_comp, hg, map_zero]

variable [J.WEqualsLocallyBijective CommRingCat.{w}]

/-- **Local surjectivity.**  A local section of the conormal sheaf of the canonical presentation
killed by the differential of `NL_{B/A}` is, on a covering sieve, the image of an element of
`H₁(L_{B(-)/A(-)})`. -/
theorem sectionsH1LiftSieve_mem {X : C}
    (c : (conormalSheaf.{v, u, w, z} J (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
      (presentation J A B a (underlyingPresheaf J B) (𝟙 _))).val.obj (op X))
    (hc : (presentationConormalSequence.{v, u, w, z} J A B a (underlyingPresheaf J B)
      (𝟙 _)).f.val.app (op X) c = 0) :
    sectionsH1LiftSieve.{v, u, w, z} J A B a c ∈ J X := by
  obtain ⟨S₁, hS₁, h₁⟩ := exists_covering_conormalClass_eq_tensorDifferential_eq_zero.{v, u, w, z}
    J A (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
    (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
    (presentation J A B a (underlyingPresheaf J B) (𝟙 _)) X c hc
  refine J.transitive hS₁ _ (fun Y g hg ↦ ?_)
  obtain ⟨x, hxc, hxd⟩ := h₁ Y g hg
  obtain ⟨S₂, hS₂, h₂⟩ := exists_covering_polynomial_kernelIdeal_lift J A B
    (underlyingPresheaf J B) a (𝟙 _) (x : (freeAlgebraSheaf J A (underlyingPresheaf J B)).obj.obj
      (op Y)) x.2
  refine J.transitive hS₂ _ (fun Z k hk ↦ ?_)
  obtain ⟨q, hq, hqu⟩ := h₂ Z k hk
  have hqd := tensorDifferential_eq_zero_of_map.{v, u, w, z} J A B a (underlyingPresheaf J B) (𝟙 _)
    k.op (x : (freeAlgebraSheaf J A (underlyingPresheaf J B)).obj.obj (op Y)) hxd _ hqu
  obtain ⟨S₃, hS₃, h₃⟩ := exists_covering_forall_pderiv_mem.{v, u, w, z} J A B
    (underlyingPresheaf J B) a (𝟙 _) (op Z) ⟨q, hq⟩ hqd
  refine J.superset_covering (fun W m hm ↦ ?_) hS₃
  let := algebraSections J A B a (op W)
  have hq' : (polynomialPresheaf J A (underlyingPresheaf J B)).map m.op q ∈
      (Generators.self (ToType (A.obj.obj (op W))) (ToType (B.obj.obj (op W)))).toExtension.ker :=
    (mem_selfKer_iff J A B a (op W) _).mpr
      (map_kernel (polynomialEvaluation J A B (underlyingPresheaf J B) a (𝟙 _)) m.op hq)
  have hcyc : (Generators.self (ToType (A.obj.obj (op W)))
      (ToType (B.obj.obj (op W)))).toExtension.cotangentComplex
        (Extension.Cotangent.mk ⟨_, hq'⟩) = 0 :=
    (cotangentComplex_mk_eq_zero_iff _).mpr fun i ↦
      (mem_selfKer_iff J A B a (op W) _).mpr (h₃ W m hm i)
  refine ⟨⟨Extension.Cotangent.mk ⟨_, hq'⟩, hcyc⟩, ?_⟩
  refine (sectionsH1Comparison_apply.{v, u, w, z} J A B a (op W) _ ⟨_, hq'⟩ rfl).trans ?_
  have hqu' : (polynomialUnit J A (underlyingPresheaf J B)).app (op W)
      ((polynomialPresheaf J A (underlyingPresheaf J B)).map m.op q) =
      (freeAlgebraSheaf J A (underlyingPresheaf J B)).obj.map (m ≫ k).op
        (x : (freeAlgebraSheaf J A (underlyingPresheaf J B)).obj.obj (op Y)) := by
    refine (NatTrans.naturality_apply (polynomialUnit J A (underlyingPresheaf J B)) m.op q).trans ?_
    rw [hqu, op_comp, Functor.map_comp_apply]
  exact conormalClass_polynomialUnit_eq.{v, u, w, z} J A B a (underlyingPresheaf J B) (𝟙 _)
    c g x hxc (m ≫ k) ((polynomialPresheaf J A (underlyingPresheaf J B)).map m.op q)
    (map_kernel (polynomialEvaluation J A B (underlyingPresheaf J B) a (𝟙 _)) m.op hq) hqu'

/-- **Local injectivity.**  An element of `H₁(L_{B(U)/A(U)})` whose image in the conormal sheaf
of the canonical presentation vanishes restricts to zero on a covering sieve. -/
theorem sectionsH1VanishingSieve_mem {X : C}
    (z : @H1Cotangent (ToType (A.obj.obj (op X))) (ToType (B.obj.obj (op X))) _ _
      (algebraSections J A B a (op X)))
    (hz : sectionsH1Comparison.{v, u, w, z} J A B a (op X) z = 0) :
    sectionsH1VanishingSieve J A B a z ∈ J X := by
  let := algebraSections J A B a (op X)
  obtain ⟨g₀, hg₀⟩ := Extension.Cotangent.mk_surjective z.1
  have h0 := (sectionsH1Comparison_apply.{v, u, w, z} J A B a (op X) z g₀ hg₀.symm).symm.trans hz
  obtain ⟨S₁, hS₁, h₁⟩ := exists_covering_mem_ker_sq_of_conormalClass_eq_zero.{v, u, w, z}
    J A (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
    (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
    (presentation J A B a (underlyingPresheaf J B) (𝟙 _)) X _ h0
  refine J.transitive hS₁ _ (fun Y g hg ↦ ?_)
  have hY := h₁ Y g hg
  have hnat : (freeAlgebraSheaf J A (underlyingPresheaf J B)).obj.map g.op
      (freeAlgebraSectionsMap J A B (op X) g₀.1) =
      (polynomialUnit J A (underlyingPresheaf J B)).app (op Y)
        ((polynomialPresheaf J A (underlyingPresheaf J B)).map g.op g₀.1) :=
    (NatTrans.naturality_apply (polynomialUnit J A (underlyingPresheaf J B)) g.op g₀.1).symm
  rw [hnat] at hY
  obtain ⟨S₂, hS₂, h₂⟩ := exists_covering_mem_ker_sq_polynomialUnit J A B
    (underlyingPresheaf J B) a (𝟙 _) _ hY
  refine J.superset_covering (fun Z k hk ↦ ?_) hS₂
  let := algebraSections J A B a (op Z)
  change sectionsH1Restrict J A B a (k ≫ g).op z = 0
  apply Subtype.ext
  rw [sectionsH1Restrict_val J A B a (k ≫ g).op z g₀ hg₀.symm]
  refine (Extension.Cotangent.mk_eq_zero_iff _).mpr ?_
  have hideal : (Generators.self (ToType (A.obj.obj (op Z)))
      (ToType (B.obj.obj (op Z)))).toExtension.ker =
      kernelIdeal (polynomialEvaluation J A B (underlyingPresheaf J B) a (𝟙 _)) (op Z) :=
    Ideal.ext fun p ↦ mem_selfKer_iff J A B a (op Z) p
  change (polynomialPresheaf J A (underlyingPresheaf J B)).map (k ≫ g).op g₀.1 ∈
    (Generators.self (ToType (A.obj.obj (op Z))) (ToType (B.obj.obj (op Z)))).toExtension.ker ^ 2
  rw [hideal]
  rw [op_comp]
  exact (polynomialPresheaf J A (underlyingPresheaf J B)).map_comp_apply g.op k.op g₀.1 ▸
    h₂ Z k hk

end Stacks.SheafOfModules

end
