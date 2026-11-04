module

public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentPresentationQuasiIso
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentInverseImage

/-!
# Stacks 08TL for the trivial presentation

Let `a : A ⟶ B` be a *locally surjective* morphism of sheaves of commutative rings on a
topological space `X`.  Then `A` itself presents `B` as a quotient of an `A`-algebra: the
**trivial presentation**.  Its conormal sequence is `I/I² ⟶ B ⊗[A] Ω[A/A] ⟶ Ω[B/A]`, and
`Ω[A/A] = 0`, so the sequence is `I/I² ⟶ 0` and the associated two-term complex `NL(a)` is
`I/I²` placed in degree `-1`.

`Stacks.SheafOfModules.quasiIso_naiveCotangentComplexComparison` of
`StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentPresentationQuasiIso` proves Stacks 08TL for
a *polynomial* presentation `A[E] ⟶ B` attached to a family of generators `α : E ⟶ B`.  The
trivial presentation is not of that form — `A` is not a free algebra sheaf over `A` — so this
file proves the same statement for it, by the same route: the comparison map is the map of the
factorisation of `a` through the canonical polynomial presentation `A[B] ⟶ B`, and at every
point the two stalk extensions of `Bₓ` over `Aₓ` admit morphisms in both directions.

This is the form of Stacks 08TL that identifies `H^{-1}(NL_{B/A})` with the conormal sheaf
`I/I²` of `a` itself.

## Main definitions

* `Stacks.SheafOfModules.structStalkSection` and
  `Stacks.SheafOfModules.structStalkBackHom`: a set-theoretic section of `Aₓ → Bₓ` and the
  induced homomorphism `(A[B])ₓ → Aₓ`.
* `Stacks.SheafOfModules.structStalkExtensionHomBack`: the morphism of stalk extensions from
  the canonical polynomial presentation to the trivial one.
* `Stacks.SheafOfModules.trivialConormalSequence` and
  `Stacks.SheafOfModules.trivialNaiveCotangentComplex`: the conormal sequence of the trivial
  presentation and the two-term complex `NL(a)` built from it.
* `Stacks.SheafOfModules.trivialNaiveCotangentComplexComparison`: the comparison chain map
  `NL(a) ⟶ NL_{B/A}`.
* `CategoryTheory.eqToHom_comm_of_naturality`: a general category-theoretic convenience.

## Main results

* `Stacks.SheafOfModules.quasiIso_trivialNaiveCotangentComplexComparison`: **Stacks 08TL for
  the trivial presentation** — the comparison map `NL(a) ⟶ NL_{B/A}` is a quasi-isomorphism.
* `Stacks.SheafOfModules.isZero_trivialConormalSequence_X₂` and
  `Stacks.SheafOfModules.trivialConormalSequence_f_eq_zero`: the middle term `B ⊗[A] Ω[A/A]` of
  the conormal sequence of the trivial presentation is a zero object and its left-hand map
  therefore vanishes.
* `Stacks.SheafOfModules.isZero_trivialNaiveCotangentComplex_X_of_ne`: `NL(a)` is concentrated
  in degree `-1`, where its term is the conormal sheaf `I/I²` of `a`.

## Implementation notes

Every stalk-level input is already available at the generality of an arbitrary pair of
presentations of `B` over a base: `Stacks.Sites.Conormal.stalkExtension`,
`Stacks.Sites.Conormal.stalkExtensionHom`,
`Stacks.Sites.Conormal.conormalSequenceStalkMapF_eq_cotangentComplex'`,
`Stacks.Sites.Conormal.conormalSheafMapOfFacStalk_eq_cotangentMap` and
`Stacks.Sites.Conormal.tensorSheafMapOfFacStalk_eq_cotangentSpaceMap`.  Only the morphism of
stalk extensions *back* from the canonical polynomial presentation had to be built, and it is
the evaluation of a polynomial over `Aₓ` at a set-theoretic section of `Aₓ → Bₓ`.

The base of the trivial presentation is `A` itself, so the conormal sequence is formed with
`R := A` and `a := 𝟙 A`; the identity of `A` is surjective on sections, whence `Ω[A/A] = 0`.

## References

* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal sequence.
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct

universe u

noncomputable section

namespace CategoryTheory

/-- A naturality square transported along equalities of the two objects of the target
complex: the shape in which `HomologicalComplex.mkHomFromDouble` asks for the commutation of a
chain map whose target has its terms given by equalities rather than by construction. -/
theorem eqToHom_comm_of_naturality {C : Type*} [Category C] {K₁ K₂ L₁ L₂ M N : C}
    (h₁ : M = L₁) (h₀ : N = L₂) (c : K₁ ⟶ L₁) (F : L₁ ⟶ L₂) (tf : K₁ ⟶ K₂) (t : K₂ ⟶ L₂)
    (hnat : tf ≫ t = c ≫ F) :
    (c ≫ eqToHom h₁.symm) ≫ eqToHom h₁ ≫ F ≫ eqToHom h₀.symm =
      tf ≫ t ≫ eqToHom h₀.symm := by
  subst h₁
  subst h₀
  simpa using hnat.symm

/-- A functor preserving zero morphisms carries a zero object to a zero object.

Module-scoped: the library carries this as `CategoryTheory.Functor.isZero_obj` in
`StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas`, which this file cannot import
without inverting the `Topology` / `AlgebraicGeometry` layering. -/
private theorem Functor.isZero_obj {C : Type*} [Category C] {D : Type*} [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D] (F : C ⥤ D)
    [F.PreservesZeroMorphisms] {M : C} (h : Limits.IsZero M) : Limits.IsZero (F.obj M) := by
  rw [Limits.IsZero.iff_id_eq_zero] at h ⊢
  rw [← F.map_id, h, F.map_zero]

end CategoryTheory

namespace Stacks.SheafOfModules

open TopCat.Presheaf Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

variable {X : TopCat.{u}} (A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (a : A ⟶ B) [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) a.hom] (x : X)

/-- The stalk of the identity of `A` is the identity of `Aₓ`. -/
theorem stalkFunctor_map_id_apply (r : ToType (stalk A.obj x)) :
    ((stalkFunctor CommRingCat.{u} x).map (𝟙 A : A ⟶ A).hom).hom r = r :=
  congrArg (fun m : stalk A.obj x ⟶ stalk A.obj x => m.hom r)
    ((stalkFunctor CommRingCat.{u} x).map_id A.obj)

/-- A set-theoretic section of the stalk of `a : A ⟶ B` on the stalk of the underlying presheaf
of sets of `B`. -/
def structStalkSection :
    stalk (C := Type u) (underlyingPresheaf (Opens.grothendieckTopology X) B) x →
      ToType (stalk A.obj x) :=
  fun t => Function.surjInv (stalkMap_surjective a.hom x)
    (presentationStalkVariable B (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _) x t)

/-- The section is a section of the stalk of `a`. -/
theorem structStalkSection_spec
    (t : stalk (C := Type u) (underlyingPresheaf (Opens.grothendieckTopology X) B) x) :
    ((stalkFunctor CommRingCat.{u} x).map a.hom).hom (structStalkSection A B a x t) =
      presentationStalkVariable B (underlyingPresheaf (Opens.grothendieckTopology X) B)
        (𝟙 _) x t :=
  Function.surjInv_eq (stalkMap_surjective a.hom x) _

/-- The homomorphism `(A[B])ₓ → Aₓ` over `Aₓ` and over `Bₓ` obtained by evaluating a polynomial
over `Aₓ` at a set-theoretic section of the stalk of `a : A ⟶ B`. -/
def structStalkBackHom :
    ToType (stalk (freeAlgebraSheaf (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B)).obj x) →+*
      ToType (stalk A.obj x) :=
  (MvPolynomial.eval₂Hom (RingHom.id (ToType (stalk A.obj x)))
      (structStalkSection A B a x)).comp
    (freeAlgebraSheafStalkRingEquiv A
      (underlyingPresheaf (Opens.grothendieckTopology X) B) x).toRingHom

/-- The homomorphism `(A[B])ₓ → Aₓ` is a homomorphism of `Aₓ`-algebras. -/
theorem structStalkBackHom_coefficientMap (r : ToType (stalk A.obj x)) :
    structStalkBackHom A B a x
        (((stalkFunctor CommRingCat.{u} x).map
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
            (underlyingPresheaf (Opens.grothendieckTopology X) B)).hom).hom r) =
      ((stalkFunctor CommRingCat.{u} x).map (𝟙 A : A ⟶ A).hom).hom r := by
  refine Eq.trans (congrArg (MvPolynomial.eval₂Hom (RingHom.id (ToType (stalk A.obj x)))
      (structStalkSection A B a x))
    (freeAlgebraSheafStalkRingEquiv_coefficientMap A
      (underlyingPresheaf (Opens.grothendieckTopology X) B) x r)) ?_
  exact (MvPolynomial.eval₂Hom_C _ _ r).trans (stalkFunctor_map_id_apply A x r).symm

/-- The homomorphism `(A[B])ₓ → Aₓ` is compatible with the two presentations of `Bₓ`. -/
theorem stalkMap_structStalkBackHom
    (y : ToType (stalk (freeAlgebraSheaf (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B)).obj x)) :
    ((stalkFunctor CommRingCat.{u} x).map a.hom).hom (structStalkBackHom A B a x y) =
      ((stalkFunctor CommRingCat.{u} x).map
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).hom).hom y := by
  refine Eq.trans ?_ (stalkFunctor_map_presentation_apply A B a
    (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _) x y).symm
  refine Eq.trans (RingHom.congr_fun (MvPolynomial.comp_eval₂Hom
      (RingHom.id (ToType (stalk A.obj x))) (structStalkSection A B a x)
      ((stalkFunctor CommRingCat.{u} x).map a.hom).hom)
    (freeAlgebraSheafStalkRingEquiv A
      (underlyingPresheaf (Opens.grothendieckTopology X) B) x y)) ?_
  exact congrArg (fun ψ : MvPolynomial
      (stalk (C := Type u) (underlyingPresheaf (Opens.grothendieckTopology X) B) x)
      (ToType (stalk A.obj x)) →+* ToType (stalk B.obj x) => ψ
      (freeAlgebraSheafStalkRingEquiv A
        (underlyingPresheaf (Opens.grothendieckTopology X) B) x y))
    (congrArg₂ MvPolynomial.eval₂Hom
      (RingHom.comp_id ((stalkFunctor CommRingCat.{u} x).map a.hom).hom)
      (funext (structStalkSection_spec A B a x)))


/-! ### The naive cotangent complex of the trivial presentation -/

/-- The conormal sequence of the *trivial* presentation of `B` over `A`, that is of `a : A ⟶ B`
itself regarded as a presentation of `B` as a quotient of the `A`-algebra `A`.  Its three terms
are `I/I²`, `B ⊗[A] Ω[A/A]` and `Ω[B/A]`. -/
abbrev trivialConormalSequence :=
  Stacks.Sites.Conormal.conormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) A A B
    (𝟙 A) a

/-- The naive cotangent complex `NL(a)` of the trivial presentation `a : A ⟶ B`, with `I/I²` in
degree `-1` and `B ⊗[A] Ω[A/A]` in degree `0`. -/
def trivialNaiveCotangentComplex :
    CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X) B)) ℤ := by
  have : HasZeroObject (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X) B)) :=
    hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.double (trivialConormalSequence A B a).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)

/-- The conormal sheaf `I/I²` of `a` is the degree `-1` term of `NL(a)`. -/
@[simp] theorem trivialNaiveCotangentComplex_X_negOne :
    (trivialNaiveCotangentComplex A B a).X (-1) = (trivialConormalSequence A B a).X₁ := by
  simp [trivialNaiveCotangentComplex, HomologicalComplex.double]

/-- `B ⊗[A] Ω[A/A]` is the degree `0` term of `NL(a)`. -/
@[simp] theorem trivialNaiveCotangentComplex_X_zero :
    (trivialNaiveCotangentComplex A B a).X 0 = (trivialConormalSequence A B a).X₂ := by
  simp [trivialNaiveCotangentComplex, HomologicalComplex.double]

/-- `NL(a)` has no terms outside degrees `-1` and `0`. -/
theorem trivialNaiveCotangentComplex_isZero_X (i : ℤ) (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero ((trivialNaiveCotangentComplex A B a).X i) := by
  have : HasZeroObject (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X) B)) :=
    hasZeroObject_of_hasTerminal_object
  change IsZero ((HomologicalComplex.double (trivialConormalSequence A B a).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).X i)
  exact HomologicalComplex.isZero_double_X _ _ i hneg hzero

/-- The first structure isomorphism of the double complex of `f` is an `eqToHom`. -/
private theorem doubleXIso₀_hom_eq_eqToHom [HasZeroObject (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology X) B))] :
    (HomologicalComplex.doubleXIso₀ (trivialConormalSequence A B a).f
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).hom =
      eqToHom (trivialNaiveCotangentComplex_X_negOne A B a) := by
  simp only [HomologicalComplex.doubleXIso₀]
  congr 1

/-- The second structure isomorphism of the double complex of `f` is an `eqToHom`. -/
private theorem doubleXIso₁_hom_eq_eqToHom [HasZeroObject (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology X) B))] :
    (HomologicalComplex.doubleXIso₁ (trivialConormalSequence A B a).f
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)).hom =
      eqToHom (trivialNaiveCotangentComplex_X_zero A B a) := by
  simp only [HomologicalComplex.doubleXIso₁]
  congr 1

/-- The inverse of the second structure isomorphism of the double complex of `f` is an
`eqToHom`. -/
private theorem doubleXIso₁_inv_eq_eqToHom [HasZeroObject (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology X) B))] :
    (HomologicalComplex.doubleXIso₁ (trivialConormalSequence A B a).f
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)).inv =
      eqToHom (trivialNaiveCotangentComplex_X_zero A B a).symm := by
  simp only [HomologicalComplex.doubleXIso₁]
  congr 1

/-- The only nonzero differential of `NL(a)` is the conormal map. -/
theorem trivialNaiveCotangentComplex_d_negOne_zero :
    (trivialNaiveCotangentComplex A B a).d (-1) 0 =
      eqToHom (trivialNaiveCotangentComplex_X_negOne A B a) ≫
        (trivialConormalSequence A B a).f ≫
        eqToHom (trivialNaiveCotangentComplex_X_zero A B a).symm := by
  have : HasZeroObject (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X) B)) :=
    hasZeroObject_of_hasTerminal_object
  change (HomologicalComplex.double (trivialConormalSequence A B a).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).d (-1) 0 = _
  rw [HomologicalComplex.double_d _ _ (by decide)]
  rw [doubleXIso₀_hom_eq_eqToHom, doubleXIso₁_inv_eq_eqToHom]
  rfl


/-! ### The comparison map of the trivial presentation -/

omit [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) a.hom] in
/-- The factorisation of the trivial presentation `a : A ⟶ B` through the canonical polynomial
presentation `A[B] ⟶ B`: the coefficient inclusion `A ⟶ A[B]` followed by `A[B] ⟶ B` is `a`. -/
theorem freeAlgebraSheafCoefficientMap_comp_presentation_id :
    freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B) ≫
        presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _) =
      a :=
  freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology X) A B
    (underlyingPresheaf (Opens.grothendieckTopology X) B) a (𝟙 _)

/-- The map `I/I² ⟶ J/J²` of conormal sheaves induced by the factorisation of the trivial
presentation through the canonical polynomial one. -/
abbrev trivialConormalMap :=
  Stacks.Sites.Conormal.conormalSheafMapOfFac.{u, u, u, u} (Opens.grothendieckTopology X) B A
    (freeAlgebraSheaf (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B))
    a
    (presentation (Opens.grothendieckTopology X) A B a
      (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B))
    (freeAlgebraSheafCoefficientMap_comp_presentation_id A B a)

/-- The map `B ⊗[A] Ω[A/A] ⟶ B ⊗[A[B]] Ω[A[B]/A]` induced by the factorisation of the trivial
presentation through the canonical polynomial one. -/
abbrev trivialTensorMap :=
  Stacks.Sites.Conormal.tensorSheafMapOfFac.{u, u, u, u} (Opens.grothendieckTopology X) A B A
    (freeAlgebraSheaf (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B))
    (𝟙 A)
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B))
    a
    (presentation (Opens.grothendieckTopology X) A B a
      (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B))
    (freeAlgebraSheafCoefficientMap_comp_presentation_id A B a)
    (Category.id_comp _)



/-- The square expressing that the two induced maps commute with the differentials of `NL(a)`
and `NL_{B/A}`. -/
theorem trivialConormalMap_comm :
    (trivialConormalMap A B a ≫ eqToHom
          (naiveCotangentComplex_X_negOne (Opens.grothendieckTopology X) A B a).symm) ≫
        (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X) A B a).d (-1) 0 =
      (trivialConormalSequence A B a).f ≫
        (trivialTensorMap A B a ≫ eqToHom
          (naiveCotangentComplex_X_zero (Opens.grothendieckTopology X) A B a).symm) := by
  rw [naiveCotangentComplex_d_negOne_zero]
  exact CategoryTheory.eqToHom_comm_of_naturality
    (naiveCotangentComplex_X_negOne (Opens.grothendieckTopology X) A B a)
    (naiveCotangentComplex_X_zero (Opens.grothendieckTopology X) A B a) _ _ _ _
    (Stacks.Sites.Conormal.conormalSequence_f_naturality.{u, u, u, u}
      (Opens.grothendieckTopology X) A B A
      (freeAlgebraSheaf (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B))
      (𝟙 A)
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B))
      a
      (presentation (Opens.grothendieckTopology X) A B a
        (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B))
      (freeAlgebraSheafCoefficientMap_comp_presentation_id A B a)
      (Category.id_comp _))

/-- The degree `0` component of the comparison is killed by every differential out of degree
`0`, since `NL_{B/A}` has none. -/
theorem trivialTensorMap_comp_d (k : ℤ) :
    (trivialTensorMap A B a ≫ eqToHom
          (naiveCotangentComplex_X_zero (Opens.grothendieckTopology X) A B a).symm) ≫
        (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X) A B a).d 0 k = 0 := by
  rw [naiveCotangentComplex_d_zero, Limits.comp_zero]

/-- **The comparison chain map `NL(a) ⟶ NL_{B/A}` of the trivial presentation.**  It is the map
of the factorisation of `a : A ⟶ B` through the canonical polynomial presentation `A[B] ⟶ B`. -/
def trivialNaiveCotangentComplexComparison :
    trivialNaiveCotangentComplex A B a ⟶
      naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X) A B a := by
  have : HasZeroObject (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X) B)) :=
    hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.mkHomFromDouble
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)
    (trivialConormalMap A B a ≫ eqToHom
      (naiveCotangentComplex_X_negOne (Opens.grothendieckTopology X) A B a).symm)
    (trivialTensorMap A B a ≫ eqToHom
      (naiveCotangentComplex_X_zero (Opens.grothendieckTopology X) A B a).symm)
    (trivialConormalMap_comm A B a)
    (fun k _ ↦ trivialTensorMap_comp_d A B a k)

/-- In degree `-1` the comparison is the map of conormal sheaves. -/
theorem trivialNaiveCotangentComplexComparison_f_negOne :
    (trivialNaiveCotangentComplexComparison A B a).f (-1) =
      eqToHom (trivialNaiveCotangentComplex_X_negOne A B a) ≫
        trivialConormalMap A B a ≫ eqToHom
          (naiveCotangentComplex_X_negOne (Opens.grothendieckTopology X) A B a).symm := by
  have : HasZeroObject (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X) B)) :=
    hasZeroObject_of_hasTerminal_object
  rw [← doubleXIso₀_hom_eq_eqToHom]
  exact HomologicalComplex.mkHomFromDouble_f₀
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide) _ _
    (trivialConormalMap_comm A B a) (fun k _ ↦ trivialTensorMap_comp_d A B a k)

/-- In degree `0` the comparison is the map on the scalar extensions of the differentials. -/
theorem trivialNaiveCotangentComplexComparison_f_zero :
    (trivialNaiveCotangentComplexComparison A B a).f 0 =
      eqToHom (trivialNaiveCotangentComplex_X_zero A B a) ≫
        trivialTensorMap A B a ≫ eqToHom
          (naiveCotangentComplex_X_zero (Opens.grothendieckTopology X) A B a).symm := by
  have : HasZeroObject (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X) B)) :=
    hasZeroObject_of_hasTerminal_object
  rw [← doubleXIso₁_hom_eq_eqToHom]
  exact HomologicalComplex.mkHomFromDouble_f₁
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide) _ _
    (trivialConormalMap_comm A B a) (fun k _ ↦ trivialTensorMap_comp_d A B a k)


/-! ### A morphism of stalk extensions back from the canonical presentation -/

/-- **The stalk extension of the trivial presentation receives a morphism from the stalk
extension of the canonical polynomial one.**  Together with the morphism in the other direction
induced by the coefficient inclusion `A ⟶ A[B]`, this is what makes the comparison map of the
trivial presentation a quasi-isomorphism on stalks. -/
def structStalkExtensionHomBack :
    letI := stalkAlgebraBase A B a x
    (stalkExtension A (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B))
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) a x
        (freeAlgebraSheafCoefficientMap_comp_presentation_id A B a)).Hom
      (stalkExtension A A B (𝟙 A) a a x (Category.id_comp a)) :=
  letI := stalkAlgebraBase A B a x
  { toRingHom := structStalkBackHom A B a x
    toRingHom_algebraMap := structStalkBackHom_coefficientMap A B a x
    algebraMap_toRingHom := stalkMap_structStalkBackHom A B a x }

/-! ### The comparison map of the trivial presentation is a quasi-isomorphism -/

/-- **Stacks 08TL for the trivial presentation.**  For a locally surjective morphism
`a : A ⟶ B` of sheaves of commutative rings on a topological space, the comparison map
`NL(a) ⟶ NL_{B/A}` from the naive cotangent complex of the trivial presentation of `B` over `A`
— that is, of `a` itself, presenting `B` as a quotient of the `A`-algebra `A` — to the naive
cotangent complex of the canonical polynomial presentation is a quasi-isomorphism.

Quasi-isomorphy is a stalkwise condition, and at every point `x` the two stalk complexes are
the naive cotangent complexes of two extensions of `Bₓ` over `Aₓ` between which morphisms exist
in both directions: the stalk of the coefficient inclusion `A ⟶ A[B]` one way, and evaluation
of a polynomial at a set-theoretic section of `Aₓ → Bₓ` the other way.  So the comparison is a
homotopy equivalence on stalks. -/
@[stacks 08TL "NL(α) ⟶ NL_{B/A} for the trivial presentation α = a : A ⟶ B of B over A"]
theorem quasiIso_trivialNaiveCotangentComplexComparison :
    QuasiIso (trivialNaiveCotangentComplexComparison A B a) := by
  refine (AlgebraicGeometry.SheafOfModules.quasiIso_iff_forall_stalk_quasiIso _ _).mpr fun x => ?_
  -- `Tensor.ringSheaf` is a reducible `abbrev` whose body is a `Sheaf` literal, so computing the
  -- discrimination-tree key of `(Tensor.ringSheaf B).obj` unfolds it and iota-reduces the
  -- projection; the key no longer matches the one at which `stalkFunctor_additive` is stated,
  -- which is `𝒪.obj` for an opaque `𝒪`, and the instance is never offered.  Naming it as a term
  -- seats it, and `PreservesZeroMorphisms` then follows for the rest of the proof.
  let : (AlgebraicGeometry.SheafOfModules.stalkFunctor (Tensor.ringSheaf B) x).Additive :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_additive (Tensor.ringSheaf.{u, u, u} B) x
  let : (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Tensor.ringSheaf B) x).PreservesZeroMorphisms :=
    CategoryTheory.Functor.preservesZeroMorphisms_of_additive _
  let _ : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
  let := stalkAlgebraBase A B a x
  let u₁ := (conormalSheafStalkLinearEquiv A B a x).toAddEquiv
  let u₀ := (cotangentSpaceStalkLinearEquiv A A B (𝟙 A) a x).toAddEquiv
  let v₁ := (conormalSheafStalkLinearEquiv (freeAlgebraSheaf (Opens.grothendieckTopology X) A
    (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
    (presentation (Opens.grothendieckTopology X) A B a
      (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x).toAddEquiv
  let v₀ := (cotangentSpaceStalkLinearEquiv A (freeAlgebraSheaf (Opens.grothendieckTopology X) A
    (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B))
    (presentation (Opens.grothendieckTopology X) A B a
      (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x).toAddEquiv
  have hc₁ : (𝟙 A : A ⟶ A) ≫ a = a := Category.id_comp a
  have hc₂ := freeAlgebraSheafCoefficientMap_comp_presentation_id A B a
  have ha : (𝟙 A : A ⟶ A) ≫ freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B) =
      freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B) := Category.id_comp _
  have hqi := NaiveCotangent.nlExtensionMap_isQuasiIso
    (stalkExtensionHom A A (freeAlgebraSheaf (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B)) B (𝟙 A)
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B))
      a
      (presentation (Opens.grothendieckTopology X) A B a
        (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) a
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B)) x hc₁ hc₂ ha hc₂)
    (structStalkExtensionHomBack A B a x)
  have hdK := conormalSequenceStalkMapF_eq_cotangentComplex' A A B (𝟙 A) a x a hc₁
  have hdL := conormalSequenceStalkMapF_eq_cotangentComplex' A
    (freeAlgebraSheaf (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B))
    (presentation (Opens.grothendieckTopology X) A B a
      (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x a hc₂
  have hpc := conormalSheafMapOfFacStalk_eq_cotangentMap A A
    (freeAlgebraSheaf (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B)) B (𝟙 A)
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B))
    a
    (presentation (Opens.grothendieckTopology X) A B a
      (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B)) x hc₂ ha a hc₁ hc₂
  have hpt := tensorSheafMapOfFacStalk_eq_cotangentSpaceMap A A
    (freeAlgebraSheaf (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B)) B (𝟙 A)
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B))
    a
    (presentation (Opens.grothendieckTopology X) A B a
      (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B)) x hc₂ ha a hc₁ hc₂
  refine CochainComplex.quasiIso_of_isZero_X_of_eqToHom _ ?_ ?_
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map (trivialConormalSequence A B a).f)
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map
      (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) A B a).f)
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map (trivialConormalMap A B a))
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map (trivialTensorMap A B a))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i h1 h2
    rw [Functor.mapHomologicalComplex_obj_X]
    exact AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj _ x _
      (trivialNaiveCotangentComplex_isZero_X A B a i h1 h2)
  · intro i h1 h2
    rw [Functor.mapHomologicalComplex_obj_X]
    exact AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj _ x _
      (naiveCotangentComplex_isZero_X (Opens.grothendieckTopology X) A B a i h1 h2)
  · exact congrArg (AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).obj
      (trivialNaiveCotangentComplex_X_negOne A B a)
  · exact congrArg (AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).obj
      (trivialNaiveCotangentComplex_X_zero A B a)
  · exact congrArg (AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).obj
      (naiveCotangentComplex_X_negOne (Opens.grothendieckTopology X) A B a)
  · exact congrArg (AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).obj
      (naiveCotangentComplex_X_zero (Opens.grothendieckTopology X) A B a)
  · refine (Functor.mapHomologicalComplex_obj_d _ _ _ _ _).trans
      ((congrArg (AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map
        (trivialNaiveCotangentComplex_d_negOne_zero A B a)).trans
      (Functor.map_eqToHom_comp_comp_eqToHom _
        (trivialNaiveCotangentComplex_X_negOne A B a) _
        (trivialNaiveCotangentComplex_X_zero A B a)))
  · refine (Functor.mapHomologicalComplex_obj_d _ _ _ _ _).trans
      ((congrArg (AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map
        (naiveCotangentComplex_d_negOne_zero (Opens.grothendieckTopology X) A B a)).trans
      (Functor.map_eqToHom_comp_comp_eqToHom _
        (naiveCotangentComplex_X_negOne (Opens.grothendieckTopology X) A B a) _
        (naiveCotangentComplex_X_zero (Opens.grothendieckTopology X) A B a)))
  · refine (Functor.mapHomologicalComplex_map_f _ _ _ _).trans
      ((congrArg (AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map
        (trivialNaiveCotangentComplexComparison_f_negOne A B a)).trans
      (Functor.map_eqToHom_comp_comp_eqToHom _
        (trivialNaiveCotangentComplex_X_negOne A B a) _
        (naiveCotangentComplex_X_negOne (Opens.grothendieckTopology X) A B a)))
  · refine (Functor.mapHomologicalComplex_map_f _ _ _ _).trans
      ((congrArg (AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map
        (trivialNaiveCotangentComplexComparison_f_zero A B a)).trans
      (Functor.map_eqToHom_comp_comp_eqToHom _
        (trivialNaiveCotangentComplex_X_zero A B a) _
        (naiveCotangentComplex_X_zero (Opens.grothendieckTopology X) A B a)))
  · exact CochainComplex.eq_zero_of_d_eq_zero_of_addEquiv (u₁ := u₁) (u₀ := u₀) (v₁ := v₁)
      hdK hpc hqi.eq_zero_of_d_eq_zero
  · exact CochainComplex.exists_of_d_eq_zero_of_addEquiv (u₁ := u₁) (u₀ := u₀) (v₁ := v₁)
      (v₀ := v₀) hdK hdL hpc hqi.exists_of_d_eq_zero
  · exact CochainComplex.exists_d_eq_of_addEquiv (u₁ := u₁) (u₀ := u₀) (v₁ := v₁) (v₀ := v₀)
      hdK hdL hpt hqi.exists_d_eq
  · exact CochainComplex.exists_add_d_eq_of_addEquiv (u₀ := u₀) (v₁ := v₁) (v₀ := v₀)
      hdL hpt hqi.exists_add_d_eq


/-! ### The conormal sequence of the trivial presentation is `I/I² ⟶ 0` -/

omit [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) a.hom] in
/-- **`Ω[A(U)/A(U)] = 0`.**  The identity of `A(U)` is surjective, and the differentials of a
surjective ring map vanish. -/
theorem subsingleton_differentialsPresheaf_id (U : (Opens X)ᵒᵖ) :
    Subsingleton (ToType ((differentialsPresheaf (𝟙 A : A ⟶ A).hom).obj U)) := by
  let := ((𝟙 A : A ⟶ A).hom.app U).hom.toAlgebra
  exact KaehlerDifferential.subsingleton_of_surjective
    (R := ToType (A.obj.obj U)) (S := ToType (A.obj.obj U)) (fun r => ⟨r, rfl⟩)

omit [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) a.hom] in
/-- **`(A/I) ⊗[A] Ω[A/A] = 0` on every open.**  A tensor product one factor of which is a
subsingleton is a subsingleton. -/
theorem subsingleton_tensorObj_id (U : (Opens X)ᵒᵖ) :
    Subsingleton (ToType (tensorObj a.hom (𝟙 A : A ⟶ A).hom U)) := by
  have h := subsingleton_differentialsPresheaf_id A U
  change Subsingleton (TensorProduct (ToType (A.obj.obj U)) _ _)
  infer_instance

omit [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) a.hom] in
/-- **The middle presheaf of the conormal sequence of the trivial presentation is zero.** -/
theorem isZero_tensorPresheaf_id :
    IsZero (tensorPresheaf a.hom (𝟙 A : A ⟶ A).hom) := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact @Subsingleton.elim _ (subsingleton_tensorObj_id A B a U) _ _

/-- **The middle term `B ⊗[A] Ω[A/A]` of the conormal sequence of the trivial presentation
vanishes.**  It is the associated sheaf of a zero presheaf of modules, and both the universe
lift and sheafification preserve zero objects. -/
theorem isZero_trivialConormalSequence_X₂ :
    IsZero (trivialConormalSequence A B a).X₂ :=
  Functor.isZero_obj (PresheafOfModules.sheafification.{u}
      (quotientToRingSheaf (Opens.grothendieckTopology X) A B a))
    (Functor.isZero_obj (liftModules.{u, u, u, u} _) (isZero_tensorPresheaf_id A B a))

/-- **The conormal sequence of the trivial presentation is `I/I² ⟶ 0`:** its left-hand map
vanishes, its target being a zero object. -/
theorem trivialConormalSequence_f_eq_zero : (trivialConormalSequence A B a).f = 0 :=
  (isZero_trivialConormalSequence_X₂ A B a).eq_of_tgt _ _

/-- **`NL(a)` is concentrated in degree `-1`.**  Outside degrees `-1` and `0` a `double`
vanishes, and in degree `0` the term is `B ⊗[A] Ω[A/A] = 0`. -/
theorem isZero_trivialNaiveCotangentComplex_X_of_ne (i : ℤ) (h : i ≠ -1) :
    IsZero ((trivialNaiveCotangentComplex A B a).X i) := by
  by_cases h0 : i = 0
  · subst h0
    exact IsZero.of_iso (isZero_trivialConormalSequence_X₂ A B a)
      (eqToIso (trivialNaiveCotangentComplex_X_zero A B a))
  · exact trivialNaiveCotangentComplex_isZero_X A B a i h h0

end Stacks.SheafOfModules

end

end
