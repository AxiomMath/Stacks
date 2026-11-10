module

public import StacksFrontier.AlgebraicGeometry.Simplicial.Degeneracies.DegreeOne
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Coskeletal
public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.FreeAlgebra

/-!
# The second degree of a polynomial simplicial resolution

For a polynomial presentation with relations `fₜ`, the degree-two polynomial algebra has
variables for two copies of each relation, for syzygies among the relations, and for the
products `xₜxₜ' - fₜxₜ'`. Its three face maps cover every compatible triple of degree-one
elements.

## Main definitions

* `Algebra.PolynomialPresentationWithKernelGenerators.DegreeTwo.Rel` is the module of finite
  relations among the `fₜ`.
* `Algebra.PolynomialPresentationWithKernelGenerators.DegreeTwo.P2` is the degree-two
  polynomial algebra, and `faceZero`, `faceOne` and `faceTwo` are its faces.
* `Algebra.PolynomialPresentationWithKernelGenerators.DegreeTwo.MatchingTriple` is the explicit
  degree-two matching condition.
* `Algebra.PolynomialPresentationWithKernelGenerators.DegreeTwo.matchingEquiv` identifies the
  actual degree-two coskeleton algebra with the matching triples.
* `Algebra.PolynomialPresentationWithKernelGenerators.DegreeTwo.coskeletonFace` is an actual
  face of that coskeleton, transported to the degree-one polynomial algebra.
* `Algebra.PolynomialPresentationWithKernelGenerators.DegreeTwo.degreeTwoToCoskeleton` is the
  algebra map defined by the three displayed faces.

## Main results

* `Algebra.PolynomialPresentationWithKernelGenerators.DegreeTwo.faces_matching` says the three
  faces form a matching triple.
* `Algebra.PolynomialPresentationWithKernelGenerators.DegreeTwo.degreeTwoToCoskeleton_surjective`
  states surjectivity onto the actual degree-two coskeleton algebra.

## Implementation notes

The degree-two object of the one-coskeleton is represented by triples `(g₀,g₁,g₂)` satisfying
the three face equations in `MatchingTriple`. The matching equivalence identifies the actual
coskeleton object with the explicit triples of its actual faces, via `matchingEquiv_faces`. The
other tagged equation identifies the algebra map with the displayed three polynomial face maps,
and surjectivity concerns this actual algebra map. The formulas for its generators are built
into the face maps.

Comparing two maps out of the degree-one algebra is done through the free algebra on one
generator: `freeOneEval_comp_eq` reduces such a comparison to a single equation between
elements, and the three face comparisons are instances of it. Stating that reduction once,
rather than repeating the elaboration of the comparison for each face, is what keeps the three
face lemmas inside the default elaboration budget.

## References

* [Stacks Project, Tag 09D4](https://stacks.math.columbia.edu/tag/09D4)
-/

@[expose] public section

open Algebra MvPolynomial CategoryTheory Opposite Limits
open scoped Simplicial

universe u v w x

namespace Algebra.PolynomialPresentationWithKernelGenerators.DegreeTwo

variable (p : PolynomialPresentationWithKernelGenerators.{u, v, w, x})
/-- Finite linear relations among the defining relations of the presentation. -/
def Rel : Type (max u w x) :=
  letI : Algebra p.A p.B := p.algebraMap.toAlgebra
  {r : p.relationIndex →₀ p.P0 //
    r.sum (fun t a => a * p.presentation.relation t) = 0}

/-- Variables for the degree-two polynomial algebra. -/
inductive DegreeTwoVariable : Type (max u w x) where
  | base (i : p.variableIndex)
  | y (t : p.relationIndex)
  | z (t : p.relationIndex)
  | v (r : Rel p)
  | w (t t' : p.relationIndex)

/-- The degree-two polynomial algebra `A[uᵢ,yₜ,zₜ,vᵣ,wₜₜ']`. -/
abbrev P2 := MvPolynomial (DegreeTwoVariable p) p.A

/-- The first face sends `yₜ` to `xₜ` and the other new variables to zero. -/
noncomputable def faceZero : P2 p →ₐ[p.A] DegreeOne.P1 p :=
  MvPolynomial.aeval fun
    | .base i => MvPolynomial.X (Sum.inl i)
    | .y t => MvPolynomial.X (Sum.inr t)
    | .z _ => 0
    | .v _ => 0
    | .w _ _ => 0

/-- The middle face sends both `yₜ` and `zₜ` to `xₜ`. -/
noncomputable def faceOne : P2 p →ₐ[p.A] DegreeOne.P1 p :=
  MvPolynomial.aeval fun
    | .base i => MvPolynomial.X (Sum.inl i)
    | .y t => MvPolynomial.X (Sum.inr t)
    | .z t => MvPolynomial.X (Sum.inr t)
    | .v _ => 0
    | .w _ _ => 0

/-- The last face has values `fₜ`, `xₜ`, `∑ rₜxₜ`, and
`xₜxₜ' - fₜxₜ'` on the four respective families of new variables. -/
noncomputable def faceTwo : P2 p →ₐ[p.A] DegreeOne.P1 p := by
  letI : Algebra p.A p.B := p.algebraMap.toAlgebra
  exact MvPolynomial.aeval fun
    | .base i => MvPolynomial.X (Sum.inl i)
    | .y t => DegreeOne.degeneracyZero p (p.presentation.relation t)
    | .z t => MvPolynomial.X (Sum.inr t)
    | .v r => r.val.sum (fun t a =>
        DegreeOne.degeneracyZero p a * MvPolynomial.X (Sum.inr t))
    | .w t t' =>
        MvPolynomial.X (Sum.inr t) * MvPolynomial.X (Sum.inr t') -
          DegreeOne.degeneracyZero p (p.presentation.relation t) *
            MvPolynomial.X (Sum.inr t')

/-- The three boundary compatibility equations for the degree-two object
of the one-coskeleton. -/
def MatchingTriple (g₀ g₁ g₂ : DegreeOne.P1 p) : Prop :=
  DegreeOne.faceZero p g₀ = DegreeOne.faceZero p g₁ ∧
  DegreeOne.faceOne p g₀ = DegreeOne.faceZero p g₂ ∧
  DegreeOne.faceOne p g₁ = DegreeOne.faceOne p g₂

private theorem faceZero_degeneracyZero_apply (a : p.P0) :
    DegreeOne.faceZero p (DegreeOne.degeneracyZero p a) = a := by
  have h : (DegreeOne.faceZero p).comp
      (DegreeOne.degeneracyZero p) = AlgHom.id p.A _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [DegreeOne.faceZero, DegreeOne.degeneracyZero,
      MvPolynomial.aeval_X]
  exact AlgHom.congr_fun h a

private theorem faceOne_degeneracyZero_apply (a : p.P0) :
    DegreeOne.faceOne p (DegreeOne.degeneracyZero p a) = a := by
  have h : (DegreeOne.faceOne p).comp
      (DegreeOne.degeneracyZero p) = AlgHom.id p.A _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [DegreeOne.faceOne, DegreeOne.degeneracyZero,
      MvPolynomial.aeval_X]
  exact AlgHom.congr_fun h a

private theorem faceZero_relationVariable (t : p.relationIndex) :
    DegreeOne.faceZero p (MvPolynomial.X (Sum.inr t)) = 0 := by
  simp [DegreeOne.faceZero]

private theorem faceOne_relationVariable (t : p.relationIndex) :
    letI : Algebra p.A p.B := p.algebraMap.toAlgebra
    DegreeOne.faceOne p (MvPolynomial.X (Sum.inr t)) =
      p.presentation.relation t := by
  let : Algebra p.A p.B := p.algebraMap.toAlgebra
  simp [DegreeOne.faceOne]

private theorem aeval_sub_algHom_mem_span_X_sub_algHom
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {σ : Type*} (f : σ → S)
    (s : S →ₐ[R] MvPolynomial σ R) (q : MvPolynomial σ R) :
    q - s ((MvPolynomial.aeval f) q) ∈
      Ideal.span (Set.range fun i : σ =>
        MvPolynomial.X i - s (f i)) := by
  let I : Ideal (MvPolynomial σ R) :=
    Ideal.span (Set.range fun i : σ => MvPolynomial.X i - s (f i))
  change q - s ((MvPolynomial.aeval f) q) ∈ I
  induction q using MvPolynomial.induction_on with
  | C a => simp [I]
  | add q r hq hr =>
      have heq : q + r - s ((MvPolynomial.aeval f) (q + r)) =
          (q - s ((MvPolynomial.aeval f) q)) +
            (r - s ((MvPolynomial.aeval f) r)) := by
        simp only [map_add]
        ring
      rw [heq]
      exact I.add_mem hq hr
  | mul_X q i hq =>
      have hgen : MvPolynomial.X i - s (f i) ∈ I :=
        Ideal.subset_span ⟨i, rfl⟩
      have heq : q * MvPolynomial.X i -
          s ((MvPolynomial.aeval f) (q * MvPolynomial.X i)) =
          (q - s ((MvPolynomial.aeval f) q)) * MvPolynomial.X i +
            s ((MvPolynomial.aeval f) q) *
              (MvPolynomial.X i - s (f i)) := by
        simp only [map_mul, MvPolynomial.aeval_X]
        ring
      rw [heq]
      exact I.add_mem (I.mul_mem_right _ hq) (I.mul_mem_left _ hgen)

/-- The three displayed face maps define a map to the degree-two matching object. -/
@[stacks 09D4 "degree_two"]
theorem faces_matching (q : P2 p) :
    MatchingTriple p (faceZero p q) (faceOne p q) (faceTwo p q) :=
  let : Algebra p.A p.B := p.algebraMap.toAlgebra
  show DegreeOne.faceZero p (faceZero p q) =
      DegreeOne.faceZero p (faceOne p q) ∧ _ ∧ _ from by
    constructor
    · have h : (DegreeOne.faceZero p).comp (faceZero p) =
          (DegreeOne.faceZero p).comp (faceOne p) := by
        apply MvPolynomial.algHom_ext
        intro i
        cases i <;> simp [faceZero, faceOne, DegreeOne.faceZero]
      exact AlgHom.congr_fun h q
    constructor
    · have h : (DegreeOne.faceOne p).comp (faceZero p) =
          (DegreeOne.faceZero p).comp (faceTwo p) := by
        apply MvPolynomial.algHom_ext
        intro i
        simp only [AlgHom.comp_apply]
        cases i with
        | base j => simp [faceZero, faceTwo, DegreeOne.faceZero,
            DegreeOne.faceOne]
        | y t =>
            simp only [faceZero, faceTwo, MvPolynomial.aeval_X]
            rw [faceZero_degeneracyZero_apply]
            simp [DegreeOne.faceOne]
        | z t => simp [faceZero, faceTwo, DegreeOne.faceZero]
        | v r =>
            simp only [faceZero, faceTwo, MvPolynomial.aeval_X]
            change DegreeOne.faceOne p 0 =
              DegreeOne.faceZero p
              (r.val.sum (fun t a => DegreeOne.degeneracyZero p a *
                MvPolynomial.X (Sum.inr t)))
            simp only [map_zero]
            rw [_root_.map_finsuppSum]
            simp only [map_mul, faceZero_relationVariable, mul_zero]
            simp [Finsupp.sum]
        | w t t' =>
            simp [faceZero, faceTwo, DegreeOne.faceZero,
              DegreeOne.degeneracyZero]
      exact AlgHom.congr_fun h q
    · have h : (DegreeOne.faceOne p).comp (faceOne p) =
          (DegreeOne.faceOne p).comp (faceTwo p) := by
        apply MvPolynomial.algHom_ext
        intro i
        simp only [AlgHom.comp_apply]
        cases i with
        | base j => simp [faceOne, faceTwo, DegreeOne.faceOne]
        | y t =>
            simp only [faceOne, faceTwo, MvPolynomial.aeval_X]
            rw [faceOne_degeneracyZero_apply]
            simp [DegreeOne.faceOne]
        | z t => simp [faceOne, faceTwo, DegreeOne.faceOne]
        | v r =>
            simp only [faceOne, faceTwo, MvPolynomial.aeval_X]
            change DegreeOne.faceOne p 0 =
              DegreeOne.faceOne p
              (r.val.sum (fun t a => DegreeOne.degeneracyZero p a *
                MvPolynomial.X (Sum.inr t)))
            simp only [map_zero]
            rw [_root_.map_finsuppSum]
            simp only [map_mul, faceOne_degeneracyZero_apply, faceOne_relationVariable]
            change 0 = r.val.sum (fun t a => a * p.presentation.relation t)
            exact r.property.symm
        | w t t' =>
            simp only [faceOne, faceTwo, MvPolynomial.aeval_X]
            change DegreeOne.faceOne p 0 = DegreeOne.faceOne p
              (MvPolynomial.X (Sum.inr t) * MvPolynomial.X (Sum.inr t') -
                DegreeOne.degeneracyZero p (p.presentation.relation t) *
                  MvPolynomial.X (Sum.inr t'))
            simp only [map_zero, map_sub, map_mul, faceOne_relationVariable,
              faceOne_degeneracyZero_apply]
            ring_nf
      exact AlgHom.congr_fun h q

/-- A face of the actual degree-two coskeleton, transported through its
degree-one polynomial-algebra identification. -/
noncomputable def coskeletonFace (i : Fin 3)
    (a : (DegreeOne.degreeOneCoskeleton p).simplicial _⦋2⦌) :
    DegreeOne.P1 p :=
  ULift.down
    (((DegreeOne.degreeOneCoskeleton p).simplicial.δ i ≫
      (DegreeOne.degreeOneCoskeleton p).oneIso.hom) a)

/-- The three actual faces of an element of the degree-two coskeleton form a matching triple. -/
theorem actual_faces_matching
    (a : (DegreeOne.degreeOneCoskeleton p).simplicial _⦋2⦌) :
    MatchingTriple p (coskeletonFace p 0 a) (coskeletonFace p 1 a)
      (coskeletonFace p 2 a) := by
  let d := DegreeOne.degreeOneCoskeleton p
  have h00 :
      (d.simplicial.δ 0 ≫ d.oneIso.hom) ≫
          AlgCat.ofHom (DegreeOne.faceZeroLift p) =
        (d.simplicial.δ 1 ≫ d.oneIso.hom) ≫
          AlgCat.ofHom (DegreeOne.faceZeroLift p) := by
    rw [← d.faceZero_eq]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have hδ : d.simplicial.δ 0 ≫ d.simplicial.δ 0 =
        d.simplicial.δ 1 ≫ d.simplicial.δ 0 :=
      (d.simplicial.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2)) (by decide)).symm
    simpa [Category.assoc] using congrArg
      (fun f : d.simplicial _⦋2⦌ ⟶ d.simplicial _⦋0⦌ => f ≫ d.zeroIso.hom) hδ
  have h01 :
      (d.simplicial.δ 0 ≫ d.oneIso.hom) ≫
          AlgCat.ofHom (DegreeOne.faceOneLift p) =
        (d.simplicial.δ 2 ≫ d.oneIso.hom) ≫
          AlgCat.ofHom (DegreeOne.faceZeroLift p) := by
    rw [← d.faceOne_eq, ← d.faceZero_eq]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have hδ : d.simplicial.δ 0 ≫ d.simplicial.δ 1 =
        d.simplicial.δ 2 ≫ d.simplicial.δ 0 :=
      (d.simplicial.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)).symm
    simpa [Category.assoc] using congrArg
      (fun f : d.simplicial _⦋2⦌ ⟶ d.simplicial _⦋0⦌ => f ≫ d.zeroIso.hom) hδ
  have h12 :
      (d.simplicial.δ 1 ≫ d.oneIso.hom) ≫
          AlgCat.ofHom (DegreeOne.faceOneLift p) =
        (d.simplicial.δ 2 ≫ d.oneIso.hom) ≫
          AlgCat.ofHom (DegreeOne.faceOneLift p) := by
    rw [← d.faceOne_eq]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have hδ : d.simplicial.δ 1 ≫ d.simplicial.δ 1 =
        d.simplicial.δ 2 ≫ d.simplicial.δ 1 :=
      (d.simplicial.δ_comp_δ (i := (1 : Fin 2)) (j := (1 : Fin 2)) (by decide)).symm
    simpa [Category.assoc] using congrArg
      (fun f : d.simplicial _⦋2⦌ ⟶ d.simplicial _⦋0⦌ => f ≫ d.zeroIso.hom) hδ
  constructor
  · have h := congrArg (fun f => f a) h00
    simpa [coskeletonFace, DegreeOne.faceZeroLift, AlgCat.comp_apply] using
      congrArg ULift.down h
  constructor
  · have h := congrArg (fun f => f a) h01
    simpa [coskeletonFace, DegreeOne.faceZeroLift,
      DegreeOne.faceOneLift, AlgCat.comp_apply] using
      congrArg ULift.down h
  · have h := congrArg (fun f => f a) h12
    simpa [coskeletonFace, DegreeOne.faceOneLift, AlgCat.comp_apply] using
      congrArg ULift.down h

/-- The degree-two object of the coskeleton `d` is the limit of its one-truncation over the
maps `⦋m⦌ ⟶ ⦋2⦌` with `m ≤ 1`. -/
noncomputable def degreeTwoCoskeletonLimitIso
    (d : DegreeOne.DegreeOneCoskeleton p) :
    d.simplicial _⦋2⦌ ≅
      limit (StructuredArrow.proj (op ⦋2⦌)
        (SimplexCategory.Truncated.inclusion 1).op ⋙
        d.truncated) := by
  rw [d.isCoskeleton]
  exact (SimplexCategory.Truncated.inclusion 1).op.ranObjObjIsoLimit
    d.truncated (op ⦋2⦌)

/-- The degree-one object of the one-truncation, identified with the degree-one polynomial
algebra. -/
noncomputable def degreeOneTruncatedTopIso
    (d : DegreeOne.DegreeOneCoskeleton p) :
    d.truncated.obj
      (op (⟨⦋1⦌, by decide⟩ : SimplexCategory.Truncated 1)) ≅
      DegreeOne.algP1 p := by
  let L := (SimplexCategory.Truncated.inclusion 1).op
  let X : (SimplexCategory.Truncated 1)ᵒᵖ :=
    op (⟨⦋1⦌, by decide⟩ : SimplexCategory.Truncated 1)
  have hc : IsIso ((L.ranCounit.app d.truncated).app X) := by
    infer_instance
  have e : (L.ran.obj d.truncated).obj (L.obj X) ≅ d.truncated.obj X :=
    asIso ((L.ranCounit.app d.truncated).app X)
  have h : (L.ran.obj d.truncated).obj (L.obj X) = d.simplicial _⦋1⦌ := by
    simpa [SimplicialObject.Truncated.cosk, L] using
      congrArg (fun F : SimplicialObject (AlgCat.{max u v w x} p.A) => F _⦋1⦌)
        d.isCoskeleton.symm
  exact e.symm.trans ((eqToIso h).trans d.oneIso)

/-- An object of the one-truncation equal to the degree-one object, identified with the
degree-one polynomial algebra. -/
noncomputable def degreeOneTruncatedObjIso
    (d : DegreeOne.DegreeOneCoskeleton p)
    (Y : (SimplexCategory.Truncated 1)ᵒᵖ)
    (hY : Y = op (⟨⦋1⦌, by decide⟩ : SimplexCategory.Truncated 1)) :
    d.truncated.obj Y ≅ DegreeOne.algP1 p :=
  (eqToIso (congrArg d.truncated.obj hY)).trans (degreeOneTruncatedTopIso p d)

private noncomputable def degreeZeroTruncatedTopIso
    (d : DegreeOne.DegreeOneCoskeleton p) :
    d.truncated.obj
      (op (⟨⦋0⦌, by decide⟩ : SimplexCategory.Truncated 1)) ≅
      DegreeOne.algP0 p := by
  let L := (SimplexCategory.Truncated.inclusion 1).op
  let X : (SimplexCategory.Truncated 1)ᵒᵖ :=
    op (⟨⦋0⦌, by decide⟩ : SimplexCategory.Truncated 1)
  have hc : IsIso ((L.ranCounit.app d.truncated).app X) := by
    infer_instance
  have e : (L.ran.obj d.truncated).obj (L.obj X) ≅ d.truncated.obj X :=
    asIso ((L.ranCounit.app d.truncated).app X)
  have h : (L.ran.obj d.truncated).obj (L.obj X) = d.simplicial _⦋0⦌ := by
    simpa [SimplicialObject.Truncated.cosk, L] using
      congrArg (fun F : SimplicialObject (AlgCat.{max u v w x} p.A) => F _⦋0⦌)
        d.isCoskeleton.symm
  exact e.symm.trans ((eqToIso h).trans d.zeroIso)

private theorem truncated_faceZero_compat
    (d : DegreeOne.DegreeOneCoskeleton p) :
    (degreeOneTruncatedTopIso p d).inv ≫
      d.truncated.map
        (SimplexCategory.Truncated.δ 1 0 (by decide) (by decide)).op ≫
      (degreeZeroTruncatedTopIso p d).hom =
        AlgCat.ofHom (DegreeOne.faceZeroLift p) := by
  cases d with
  | mk truncated simplicial hcosk augmentation zeroIso oneIso faceZero_eq faceOne_eq
      degeneracyZero_eq augmentation_eq =>
    cases hcosk
    let L := (SimplexCategory.Truncated.inclusion 1).op
    let X1 : (SimplexCategory.Truncated 1)ᵒᵖ :=
      op (⟨⦋1⦌, by decide⟩ : SimplexCategory.Truncated 1)
    let X0 : (SimplexCategory.Truncated 1)ᵒᵖ :=
      op (⟨⦋0⦌, by decide⟩ : SimplexCategory.Truncated 1)
    let f : X1 ⟶ X0 := (SimplexCategory.Truncated.δ 1 0 (by decide) (by decide)).op
    have hnat := (L.ranCounit.app truncated).naturality f
    simpa [degreeOneTruncatedTopIso, degreeZeroTruncatedTopIso,
      SimplicialObject.Truncated.cosk, SimplicialObject.δ, L, X1, X0, f, hnat]
      using faceZero_eq

private theorem truncated_faceOne_compat
    (d : DegreeOne.DegreeOneCoskeleton p) :
    (degreeOneTruncatedTopIso p d).inv ≫
      d.truncated.map
        (SimplexCategory.Truncated.δ 1 1 (by decide) (by decide)).op ≫
      (degreeZeroTruncatedTopIso p d).hom =
        AlgCat.ofHom (DegreeOne.faceOneLift p) := by
  cases d with
  | mk truncated simplicial hcosk augmentation zeroIso oneIso faceZero_eq faceOne_eq
      degeneracyZero_eq augmentation_eq =>
    cases hcosk
    let L := (SimplexCategory.Truncated.inclusion 1).op
    let X1 : (SimplexCategory.Truncated 1)ᵒᵖ :=
      op (⟨⦋1⦌, by decide⟩ : SimplexCategory.Truncated 1)
    let X0 : (SimplexCategory.Truncated 1)ᵒᵖ :=
      op (⟨⦋0⦌, by decide⟩ : SimplexCategory.Truncated 1)
    let f : X1 ⟶ X0 := (SimplexCategory.Truncated.δ 1 1 (by decide) (by decide)).op
    have hnat := (L.ranCounit.app truncated).naturality f
    simpa [degreeOneTruncatedTopIso, degreeZeroTruncatedTopIso,
      SimplicialObject.Truncated.cosk, SimplicialObject.δ, L, X1, X0, f, hnat]
      using faceOne_eq

private theorem truncated_faceZero_pre
    (d : DegreeOne.DegreeOneCoskeleton p) :
    (degreeOneTruncatedTopIso p d).inv ≫
      d.truncated.map
        (SimplexCategory.Truncated.δ 1 0 (by decide) (by decide)).op =
      AlgCat.ofHom (DegreeOne.faceZeroLift p) ≫
        (degreeZeroTruncatedTopIso p d).inv := by
  have h := truncated_faceZero_compat p d
  calc
    _ = ((degreeOneTruncatedTopIso p d).inv ≫
          d.truncated.map
            (SimplexCategory.Truncated.δ 1 0 (by decide) (by decide)).op ≫
          (degreeZeroTruncatedTopIso p d).hom) ≫
          (degreeZeroTruncatedTopIso p d).inv := by simp [Category.assoc]
    _ = _ := by rw [h]

private theorem truncated_faceOne_pre
    (d : DegreeOne.DegreeOneCoskeleton p) :
    (degreeOneTruncatedTopIso p d).inv ≫
      d.truncated.map
        (SimplexCategory.Truncated.δ 1 1 (by decide) (by decide)).op =
      AlgCat.ofHom (DegreeOne.faceOneLift p) ≫
        (degreeZeroTruncatedTopIso p d).inv := by
  have h := truncated_faceOne_compat p d
  calc
    _ = ((degreeOneTruncatedTopIso p d).inv ≫
          d.truncated.map
            (SimplexCategory.Truncated.δ 1 1 (by decide) (by decide)).op ≫
          (degreeZeroTruncatedTopIso p d).hom) ≫
          (degreeZeroTruncatedTopIso p d).inv := by simp [Category.assoc]
    _ = _ := by rw [h]

private noncomputable abbrev algFreeOne : AlgCat.{max u v w x} p.A :=
  AlgCat.of p.A (ULift.{max (max (max u v) w) x, max u} (FreeAlgebra p.A Unit))

private noncomputable def freeOneEval {T : AlgCat.{max u v w x} p.A} (a : T) :
    algFreeOne p ⟶ T := by
  letI : Algebra p.A T := T.isAlgebra
  exact AlgCat.ofHom ((FreeAlgebra.lift p.A (fun _ : Unit => a)).comp
    ((ULift.algEquiv (R := p.A) :
      ULift.{max (max (max u v) w) x} (FreeAlgebra p.A Unit) ≃ₐ[p.A]
        FreeAlgebra p.A Unit).toAlgHom))

private theorem freeOneEval_generator {T : AlgCat.{max u v w x} p.A} (a : T) :
    (freeOneEval p a).hom (ULift.up (FreeAlgebra.ι p.A ())) = a := by
  simp [freeOneEval, FreeAlgebra.lift_ι_apply]

private theorem freeOne_hom_ext {T : AlgCat.{max u v w x} p.A}
    (f g : algFreeOne p ⟶ T)
    (h : f.hom (ULift.up (FreeAlgebra.ι p.A ())) =
      g.hom (ULift.up (FreeAlgebra.ι p.A ()))) : f = g := by
  apply AlgCat.hom_ext
  apply AlgHom.ext
  intro x
  cases x with
  | up x =>
    let e := (ULift.algEquiv (R := p.A) :
      ULift.{max (max (max u v) w) x} (FreeAlgebra p.A Unit) ≃ₐ[p.A]
        FreeAlgebra p.A Unit).symm.toAlgHom
    have hc : f.hom.comp e = g.hom.comp e := by
      apply FreeAlgebra.hom_ext
      funext i
      cases i
      change f.hom (ULift.up (FreeAlgebra.ι p.A ())) =
        g.hom (ULift.up (FreeAlgebra.ι p.A ()))
      exact h
    exact congrArg (fun k : FreeAlgebra p.A Unit →ₐ[p.A] T => k x) hc

private theorem freeOne_faceZero_eq (a b : DegreeOne.P1 p)
    (h : DegreeOne.faceZero p a =
      DegreeOne.faceZero p b) :
    freeOneEval p (ULift.up a) ≫
        AlgCat.ofHom (DegreeOne.faceZeroLift p) =
      freeOneEval p (ULift.up b) ≫
        AlgCat.ofHom (DegreeOne.faceZeroLift p) := by
  apply freeOne_hom_ext
  change DegreeOne.faceZeroLift p
      ((freeOneEval p (show DegreeOne.algP1 p from ULift.up a)).hom
        (ULift.up (FreeAlgebra.ι p.A ()))) =
    DegreeOne.faceZeroLift p
      ((freeOneEval p (show DegreeOne.algP1 p from ULift.up b)).hom
        (ULift.up (FreeAlgebra.ι p.A ())))
  rw [freeOneEval_generator, freeOneEval_generator]
  simpa [DegreeOne.faceZeroLift] using
    congrArg (ULift.up.{max u v w x, max u w}) h

private theorem freeOne_faceOne_eq (a b : DegreeOne.P1 p)
    (h : DegreeOne.faceOne p a =
      DegreeOne.faceOne p b) :
    freeOneEval p (ULift.up a) ≫
        AlgCat.ofHom (DegreeOne.faceOneLift p) =
      freeOneEval p (ULift.up b) ≫
        AlgCat.ofHom (DegreeOne.faceOneLift p) := by
  apply freeOne_hom_ext
  change DegreeOne.faceOneLift p
      ((freeOneEval p (show DegreeOne.algP1 p from ULift.up a)).hom
        (ULift.up (FreeAlgebra.ι p.A ()))) =
    DegreeOne.faceOneLift p
      ((freeOneEval p (show DegreeOne.algP1 p from ULift.up b)).hom
        (ULift.up (FreeAlgebra.ι p.A ())))
  rw [freeOneEval_generator, freeOneEval_generator]
  simpa [DegreeOne.faceOneLift] using
    congrArg (ULift.up.{max u v w x, max u w}) h

private theorem freeOne_faceOneZero_eq (a b : DegreeOne.P1 p)
    (h : DegreeOne.faceOne p a =
      DegreeOne.faceZero p b) :
    freeOneEval p (ULift.up a) ≫
        AlgCat.ofHom (DegreeOne.faceOneLift p) =
      freeOneEval p (ULift.up b) ≫
        AlgCat.ofHom (DegreeOne.faceZeroLift p) := by
  apply freeOne_hom_ext
  change DegreeOne.faceOneLift p
      ((freeOneEval p (show DegreeOne.algP1 p from ULift.up a)).hom
        (ULift.up (FreeAlgebra.ι p.A ()))) =
    DegreeOne.faceZeroLift p
      ((freeOneEval p (show DegreeOne.algP1 p from ULift.up b)).hom
        (ULift.up (FreeAlgebra.ι p.A ())))
  rw [freeOneEval_generator, freeOneEval_generator]
  simpa [DegreeOne.faceOneLift,
    DegreeOne.faceZeroLift] using
    congrArg (ULift.up.{max u v w x, max u w}) h

private noncomputable def matchingFamily
    (d : DegreeOne.DegreeOneCoskeleton p)
    (g : DegreeOne.P1 p ×
      DegreeOne.P1 p × DegreeOne.P1 p) :
    Fin 3 → (algFreeOne p ⟶ d.truncated.obj
      (op (⟨⦋1⦌, by decide⟩ : SimplexCategory.Truncated 1))) :=
  fun i : Fin 3 => freeOneEval p (show DegreeOne.algP1 p from ULift.up
      (if i = 0 then g.1 else if i = 1 then g.2.1 else g.2.2)) ≫
    (degreeOneTruncatedTopIso p d).inv

private theorem matchingFamily_compatible
    (d : DegreeOne.DegreeOneCoskeleton p)
    (g : DegreeOne.P1 p ×
      DegreeOne.P1 p × DegreeOne.P1 p)
    (hg : MatchingTriple p g.1 g.2.1 g.2.2) :
    ∀ i j : Fin 2, i ≤ j →
      matchingFamily p d g i.castSucc ≫ d.truncated.map
        (SimplexCategory.Truncated.δ 1 j (by decide) (by decide)).op =
      matchingFamily p d g j.succ ≫ d.truncated.map
        (SimplexCategory.Truncated.δ 1 i (by decide) (by decide)).op := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · have h := freeOne_faceZero_eq p g.1 g.2.1 hg.1
    simpa [matchingFamily, Category.assoc, truncated_faceZero_pre] using
      congrArg (fun f => f ≫ (degreeZeroTruncatedTopIso p d).inv) h
  · have h := freeOne_faceOneZero_eq p g.1 g.2.2 hg.2.1
    simpa [matchingFamily, Category.assoc, truncated_faceOne_pre,
      truncated_faceZero_pre] using
      congrArg (fun f => f ≫ (degreeZeroTruncatedTopIso p d).inv) h
  · norm_num at hij
  · have h := freeOne_faceOne_eq p g.2.1 g.2.2 hg.2.2
    simpa [matchingFamily, Category.assoc, truncated_faceOne_pre] using
      congrArg (fun f => f ≫ (degreeZeroTruncatedTopIso p d).inv) h

/-- The diagram whose limit is the degree-two object of the coskeleton `d`: its one-truncation
over the maps `⦋m⦌ ⟶ ⦋2⦌` with `m ≤ 1`. -/
noncomputable abbrev degreeTwoSlice
    (d : DegreeOne.DegreeOneCoskeleton p) :=
  StructuredArrow.proj (op ⦋2⦌)
      (SimplexCategory.Truncated.inclusion 1).op ⋙ d.truncated

/-- The `i`-th face `⦋1⦌ ⟶ ⦋2⦌`, as an object of the indexing category of `degreeTwoSlice`. -/
noncomputable def degreeTwoFaceArrow (i : Fin 3) :
    StructuredArrow (op ⦋2⦌) (SimplexCategory.Truncated.inclusion 1).op :=
  StructuredArrow.mk (Y := op (⟨⦋1⦌, by decide⟩ : SimplexCategory.Truncated 1))
    (SimplexCategory.δ i).op

/-- The `i`-th face of a degree-two element of the coskeleton `d`, read in the degree-one
polynomial algebra. -/
noncomputable def coskeletonFaceOf
    (d : DegreeOne.DegreeOneCoskeleton p) (i : Fin 3)
    (a : d.simplicial _⦋2⦌) : DegreeOne.P1 p :=
  ULift.down ((d.simplicial.δ i ≫ d.oneIso.hom) a)

/-- The limit projection of `degreeTwoCoskeletonLimitIso` at the `i`-th face arrow is the `i`-th
face map, read in the degree-one polynomial algebra. -/
theorem degreeTwoCoskeletonLimitIso_face
    (d : DegreeOne.DegreeOneCoskeleton p) (i : Fin 3) :
    (degreeTwoCoskeletonLimitIso p d).hom ≫
        limit.π (degreeTwoSlice p d) (degreeTwoFaceArrow i) ≫
        (degreeOneTruncatedObjIso p d (degreeTwoFaceArrow i).right rfl).hom =
      d.simplicial.δ i ≫ d.oneIso.hom := by
  cases d with
  | mk truncated simplicial hcosk augmentation zeroIso oneIso faceZero_eq faceOne_eq
      degeneracyZero_eq augmentation_eq =>
    cases hcosk
    let d' : DegreeOne.DegreeOneCoskeleton p :=
      ⟨truncated, (SimplicialObject.Truncated.cosk 1).obj truncated, rfl,
        augmentation, zeroIso, oneIso, faceZero_eq, faceOne_eq,
        degeneracyZero_eq, augmentation_eq⟩
    let L := (SimplexCategory.Truncated.inclusion 1).op
    let X : SimplexCategoryᵒᵖ := op ⦋2⦌
    let f := degreeTwoFaceArrow i
    have h := L.ranObjObjIsoLimit_hom_π truncated X f
    have hlim : (degreeTwoCoskeletonLimitIso p d').hom ≫
        limit.π (degreeTwoSlice p d') f =
        ((SimplicialObject.Truncated.cosk 1).obj truncated).map f.hom ≫
          (L.ranCounit.app truncated).app f.right := by
      change (L.ranObjObjIsoLimit truncated X).hom ≫
          limit.π (StructuredArrow.proj X L ⋙ truncated) f =
        (L.ran.obj truncated).map f.hom ≫ (L.ranCounit.app truncated).app f.right
      exact h
    calc
      (degreeTwoCoskeletonLimitIso p d').hom ≫
          limit.π (degreeTwoSlice p d') f ≫
          (degreeOneTruncatedObjIso p d' f.right rfl).hom =
        ((SimplicialObject.Truncated.cosk 1).obj truncated).map f.hom ≫
          (L.ranCounit.app truncated).app f.right ≫
          (degreeOneTruncatedObjIso p d' f.right
            (by simp [f, degreeTwoFaceArrow])).hom := by
              have hpost := congrArg
                (fun k => k ≫ (degreeOneTruncatedObjIso p d' f.right rfl).hom) hlim
              simpa [Category.assoc] using hpost
      _ = ((SimplicialObject.Truncated.cosk 1).obj truncated).map f.hom ≫ oneIso.hom := by
        fin_cases i
        all_goals
          dsimp [f, degreeTwoFaceArrow] at *
          simp [degreeOneTruncatedObjIso, degreeOneTruncatedTopIso, d', L]
      _ = d'.simplicial.δ i ≫ oneIso.hom := by rfl

/-- Every matching triple is the triple of faces of some degree-two element of the
coskeleton. -/
theorem matchingTriple_exists
    (d : DegreeOne.DegreeOneCoskeleton p)
    (g : DegreeOne.P1 p ×
      DegreeOne.P1 p × DegreeOne.P1 p)
    (hg : MatchingTriple p g.1 g.2.1 g.2.2) :
    ∃ a : d.simplicial _⦋2⦌,
      (coskeletonFaceOf p d 0 a, coskeletonFaceOf p d 1 a,
        coskeletonFaceOf p d 2 a) = g := by
  let fam := matchingFamily p d g
  have he := (SimplicialObject.Truncated.existsUnique_cone_app_δ_eq_iff
    (n := 0) d.truncated (algFreeOne p) fam).2
      (matchingFamily_compatible p d g hg)
  let π := Classical.choose he
  have hπ := (Classical.choose_spec he).1
  let c : Cone (degreeTwoSlice p d) := ⟨algFreeOne p, π⟩
  let m := (limit.isLimit (degreeTwoSlice p d)).lift c
  let φ := m ≫ (degreeTwoCoskeletonLimitIso p d).inv
  refine ⟨φ.hom (ULift.up.{max (max (max u v) w) x, max u}
      (FreeAlgebra.ι p.A ())), ?_⟩
  have key : ∀ (i : Fin 3) (x : DegreeOne.P1 p),
      fam i = freeOneEval p (ULift.up x) ≫ (degreeOneTruncatedTopIso p d).inv →
      coskeletonFaceOf p d i (φ.hom (ULift.up.{max (max (max u v) w) x, max u}
        (FreeAlgebra.ι p.A ()))) = x := by
    intro i x hfam
    have hformula := degreeTwoCoskeletonLimitIso_face p d i
    have hY : (degreeTwoFaceArrow i).right =
        op (⟨⦋1⦌, by decide⟩ : SimplexCategory.Truncated 1) := by
      simp [degreeTwoFaceArrow]
    have hcomp : φ ≫ d.simplicial.δ i ≫ d.oneIso.hom =
        freeOneEval p (ULift.up x) := by
      calc
        φ ≫ d.simplicial.δ i ≫ d.oneIso.hom =
            m ≫ (degreeTwoCoskeletonLimitIso p d).inv ≫
              d.simplicial.δ i ≫ d.oneIso.hom := by simp [φ, Category.assoc]
        _ = m ≫ (degreeTwoCoskeletonLimitIso p d).inv ≫
              ((degreeTwoCoskeletonLimitIso p d).hom ≫
                limit.π (degreeTwoSlice p d) (degreeTwoFaceArrow i) ≫
                (degreeOneTruncatedObjIso p d (degreeTwoFaceArrow i).right hY).hom) := by
              rw [hformula]
        _ = m ≫ limit.π (degreeTwoSlice p d) (degreeTwoFaceArrow i) ≫
              (degreeOneTruncatedObjIso p d (degreeTwoFaceArrow i).right hY).hom := by
              simp
        _ = c.π.app (degreeTwoFaceArrow i) ≫
              (degreeOneTruncatedObjIso p d (degreeTwoFaceArrow i).right hY).hom := by
              have hface' : m ≫ limit.π (degreeTwoSlice p d) (degreeTwoFaceArrow i) =
                  c.π.app (degreeTwoFaceArrow i) := by simp [m]
              have hface'' := congrArg
                (fun k => k ≫ (degreeOneTruncatedObjIso p d
                  (degreeTwoFaceArrow i).right hY).hom) hface'
              simpa [Category.assoc] using hface''
        _ = freeOneEval p (ULift.up x) := by
              have hleg : c.π.app (degreeTwoFaceArrow i) = fam i := by
                simpa [degreeTwoFaceArrow] using hπ i
              rw [hleg, hfam]
              dsimp [degreeOneTruncatedObjIso]
              have hcast : eqToHom (congrArg d.truncated.obj hY) = 𝟙 _ := by
                cases hY
                rfl
              rw [hcast]
              change (freeOneEval p (ULift.up x) ≫
                (degreeOneTruncatedTopIso p d).inv) ≫ 𝟙 _ ≫
                  (degreeOneTruncatedTopIso p d).hom = _
              calc
                _ = freeOneEval p (ULift.up x) ≫
                      ((degreeOneTruncatedTopIso p d).inv ≫
                        (degreeOneTruncatedTopIso p d).hom) := by
                    simp [Category.assoc]
                _ = freeOneEval p (ULift.up x) := by simp
    let gen : algFreeOne p := ULift.up.{max (max (max u v) w) x, max u}
      (FreeAlgebra.ι p.A ())
    have hval := congrArg (fun f : algFreeOne p ⟶ DegreeOne.algP1 p =>
        f.hom gen) hcomp
    change ULift.down.{max (max (max u v) w) x, max (max u w) x}
      ((d.simplicial.δ i ≫ d.oneIso.hom) (φ.hom gen)) = x
    have hval' :
        (d.simplicial.δ i ≫ d.oneIso.hom).hom (φ.hom gen) =
          ULift.up.{max (max (max u v) w) x, max (max u w) x} x := by
      calc
        _ = (freeOneEval p (ULift.up x)).hom gen := hval
        _ = _ := by
          simpa [gen] using freeOneEval_generator p
            (T := DegreeOne.algP1 p) (ULift.up x)
    rw [hval']
  exact Prod.ext (key 0 _ (by simp [fam, matchingFamily]))
    (Prod.ext (key 1 _ (by simp [fam, matchingFamily]))
      (key 2 _ (by simp [fam, matchingFamily])))

private noncomputable abbrev degreeTwoConeOf
    (d : DegreeOne.DegreeOneCoskeleton p)
    (a : d.simplicial _⦋2⦌) : Cone (degreeTwoSlice p d) := by
  let e := freeOneEval p a ≫ (degreeTwoCoskeletonLimitIso p d).hom
  refine Cone.mk (algFreeOne p) ?_
  exact
    { app := fun X => e ≫ limit.π (degreeTwoSlice p d) X
      naturality := by
        intro X Y f
        simpa [e, Category.assoc] using
          congrArg (fun k => e ≫ k) (limit.w (degreeTwoSlice p d) f).symm }

private lemma degreeTwoSlice_arrow_factors
    (X : StructuredArrow (op ⦋2⦌) (SimplexCategory.Truncated.inclusion 1).op) :
    ∃ (i : Fin 3) (ψ : X.right.unop.obj ⟶ ⦋1⦌),
      ψ ≫ SimplexCategory.δ i = X.hom.unop := by
  have hlen : X.right.unop.obj.len ≤ 1 := X.right.unop.property
  have hmiss : ∃ i : Fin 3, ∀ x, X.hom.unop.toOrderHom x ≠ i := by
    by_contra h
    simp only [not_exists, not_forall, not_not] at h
    have hc := Fintype.card_le_of_surjective X.hom.unop.toOrderHom h
    simp only [Fintype.card_fin, SimplexCategory.len_mk,
      ] at hc
    have hsource : (unop ((SimplexCategory.Truncated.inclusion 1).op.obj
        X.right)).len ≤ 1 := by
      simpa using hlen
    omega
  obtain ⟨i, hi⟩ := hmiss
  obtain ⟨ψ, hψ⟩ := SimplexCategory.eq_comp_δ_of_not_surjective' X.hom.unop i hi
  exact ⟨i, ψ, hψ.symm⟩

private theorem degreeTwoConeOf_face
    (d : DegreeOne.DegreeOneCoskeleton p)
    (a : d.simplicial _⦋2⦌) (i : Fin 3) :
    (degreeTwoConeOf p d a).π.app (degreeTwoFaceArrow i) ≫
        (degreeOneTruncatedObjIso p d (degreeTwoFaceArrow i).right rfl).hom =
      freeOneEval p (ULift.up (coskeletonFaceOf p d i a)) := by
  change freeOneEval p a ≫ (degreeTwoCoskeletonLimitIso p d).hom ≫
      limit.π (degreeTwoSlice p d) (degreeTwoFaceArrow i) ≫
        (degreeOneTruncatedObjIso p d (degreeTwoFaceArrow i).right rfl).hom = _
  calc
    _ = freeOneEval p a ≫ ((degreeTwoCoskeletonLimitIso p d).hom ≫
        limit.π (degreeTwoSlice p d) (degreeTwoFaceArrow i) ≫
          (degreeOneTruncatedObjIso p d (degreeTwoFaceArrow i).right rfl).hom) := by
      simp
    _ = freeOneEval p a ≫ (d.simplicial.δ i ≫ d.oneIso.hom) := by
      rw [degreeTwoCoskeletonLimitIso_face p d i]
    _ = _ := by
      apply freeOne_hom_ext
      let gen : algFreeOne p := ULift.up.{max (max (max u v) w) x, max u}
        (FreeAlgebra.ι p.A ())
      change (d.oneIso.hom).hom ((d.simplicial.δ i).hom
          ((freeOneEval p a).hom gen)) =
        (freeOneEval p (ULift.up (coskeletonFaceOf p d i a))).hom gen
      have hl := freeOneEval_generator p a
      have hr := freeOneEval_generator p
        (T := DegreeOne.algP1 p) (ULift.up (coskeletonFaceOf p d i a))
      rw [hl, hr]
      simp [coskeletonFaceOf]

/-- A degree-two element of the coskeleton is determined by its three faces. -/
theorem matchingFace_injective
    (a b : (DegreeOne.degreeOneCoskeleton p).simplicial _⦋2⦌)
    (h : (coskeletonFace p 0 a, coskeletonFace p 1 a, coskeletonFace p 2 a) =
      (coskeletonFace p 0 b, coskeletonFace p 1 b, coskeletonFace p 2 b)) :
    a = b := by
  let d := DegreeOne.degreeOneCoskeleton p
  let ca := degreeTwoConeOf p d a
  let cb := degreeTwoConeOf p d b
  have h0 : coskeletonFace p 0 a = coskeletonFace p 0 b := congrArg Prod.fst h
  have h12 : (coskeletonFace p 1 a, coskeletonFace p 2 a) =
      (coskeletonFace p 1 b, coskeletonFace p 2 b) := congrArg Prod.snd h
  have h1 : coskeletonFace p 1 a = coskeletonFace p 1 b := congrArg Prod.fst h12
  have h2 : coskeletonFace p 2 a = coskeletonFace p 2 b := congrArg Prod.snd h12
  have hfaces : ∀ i : Fin 3,
      ca.π.app (degreeTwoFaceArrow i) = cb.π.app (degreeTwoFaceArrow i) := by
    intro i
    have hi : coskeletonFace p i a = coskeletonFace p i b := by
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    have hfa := degreeTwoConeOf_face p d a i
    have hfb := degreeTwoConeOf_face p d b i
    have hvalue : freeOneEval p (T := DegreeOne.algP1 p)
          (ULift.up (coskeletonFaceOf p d i a)) =
        freeOneEval p (T := DegreeOne.algP1 p)
          (ULift.up (coskeletonFaceOf p d i b)) := by
      simpa [coskeletonFaceOf, coskeletonFace, d] using congrArg
        (fun z : DegreeOne.P1 p =>
          freeOneEval p (T := DegreeOne.algP1 p) (ULift.up z)) hi
    exact (cancel_mono
      (degreeOneTruncatedObjIso p d (degreeTwoFaceArrow i).right rfl).hom).1
        (hfa.trans (hvalue.trans hfb.symm))
  have hmaps : freeOneEval p a ≫ (degreeTwoCoskeletonLimitIso p d).hom =
      freeOneEval p b ≫ (degreeTwoCoskeletonLimitIso p d).hom := by
    apply (limit.isLimit (degreeTwoSlice p d)).hom_ext
    intro X
    obtain ⟨i, ψ, hfactor⟩ := degreeTwoSlice_arrow_factors X
    let Y := degreeTwoFaceArrow i
    have hY : Y.right = op (⟨⦋1⦌, by decide⟩ : SimplexCategory.Truncated 1) := by
      simp [Y, degreeTwoFaceArrow]
    let ψ' : Y.right ⟶ X.right := by
      dsimp [Y, degreeTwoFaceArrow]
      exact (ObjectProperty.homMk ψ).op
    have hcompose : (SimplexCategory.δ i).op ≫ ψ.op = X.hom := by
      rw [← op_comp]
      exact congrArg Quiver.Hom.op hfactor
    let f : Y ⟶ X := StructuredArrow.homMk ψ' (by
      change Y.hom ≫ (SimplexCategory.Truncated.inclusion 1).op.map ψ' = X.hom
      simpa [Y, degreeTwoFaceArrow, ψ', hY, ObjectProperty.ι_map] using hcompose)
    have hca : ca.π.app X = ca.π.app Y ≫ (degreeTwoSlice p d).map f := by
      simpa using ca.π.naturality f
    have hcb : cb.π.app X = cb.π.app Y ≫ (degreeTwoSlice p d).map f := by
      simpa using cb.π.naturality f
    have hlegs : ca.π.app X = cb.π.app X := by
      have hface : ca.π.app Y = cb.π.app Y := by
        simpa [Y] using hfaces i
      exact hca.trans ((congrArg (fun k => k ≫ (degreeTwoSlice p d).map f) hface).trans hcb.symm)
    simpa [ca, cb, degreeTwoConeOf, Category.assoc] using hlegs
  have hEval : freeOneEval p a = freeOneEval p b :=
    (cancel_mono (degreeTwoCoskeletonLimitIso p d).hom).mp hmaps
  let gen : algFreeOne p := ULift.up.{max (max (max u v) w) x, max u}
    (FreeAlgebra.ι p.A ())
  have hgen := congrArg (fun f : algFreeOne p ⟶ d.simplicial _⦋2⦌ => f.hom gen) hEval
  have ha : (freeOneEval p a).hom gen = a := by
    simpa [gen] using freeOneEval_generator p a
  have hb : (freeOneEval p b).hom gen = b := by
    simpa [gen] using freeOneEval_generator p b
  exact ha.symm.trans (hgen.trans hb)

/-- The actual second degree of the one-coskeleton is canonically the algebra
of compatible triples of degree-one elements. -/
@[stacks 09D4 "degree_two"]
noncomputable def matchingEquiv :
    ((DegreeOne.degreeOneCoskeleton p).simplicial _⦋2⦌) ≃
      {g : (DegreeOne.P1 p ×
          DegreeOne.P1 p × DegreeOne.P1 p) //
        MatchingTriple p g.1 g.2.1 g.2.2} :=
  by
    classical
    let F : ((DegreeOne.degreeOneCoskeleton p).simplicial _⦋2⦌) →
        {g : (DegreeOne.P1 p ×
          DegreeOne.P1 p × DegreeOne.P1 p) //
          MatchingTriple p g.1 g.2.1 g.2.2} := fun a =>
      ⟨(coskeletonFace p 0 a, coskeletonFace p 1 a, coskeletonFace p 2 a),
        actual_faces_matching p a⟩
    apply Equiv.ofBijective F
    constructor
    · intro a b hab
      exact matchingFace_injective p a b (congrArg Subtype.val hab)
    · intro g
      obtain ⟨a, ha⟩ := matchingTriple_exists p
        (DegreeOne.degreeOneCoskeleton p) g.1 g.2
      refine ⟨a, ?_⟩
      apply Subtype.ext
      simpa [F, coskeletonFace, coskeletonFaceOf] using ha

/-- The canonical matching equivalence records exactly the three actual faces
of a degree-two simplex. -/
@[stacks 09D4 "degree_two"]
theorem matchingEquiv_faces
    (a : (DegreeOne.degreeOneCoskeleton p).simplicial _⦋2⦌) :
    (matchingEquiv p a).val =
      (coskeletonFace p 0 a, coskeletonFace p 1 a, coskeletonFace p 2 a) :=
  by
    classical
    unfold matchingEquiv
    dsimp [Equiv.ofBijective]

/-- The degree-two polynomial algebra, lifted to the universe of the algebraic
coskeleton. -/
noncomputable abbrev algP2 : AlgCat.{max u v w x} p.A :=
  AlgCat.of p.A
    (ULift.{max u v w x, max u w x} (P2 p))

/-- The face `faceZero`, between the universe-lifted polynomial algebras. -/
noncomputable def faceZeroLiftP2 :
    ULift.{max u v w x, max u w x} (P2 p) →ₐ[p.A]
      ULift.{max u v w x, max u w x} (DegreeOne.P1 p) :=
  (ULift.algEquiv (R := p.A)).symm.toAlgHom.comp
    ((faceZero p).comp (ULift.algEquiv (R := p.A)).toAlgHom)

/-- The face `faceOne`, between the universe-lifted polynomial algebras. -/
noncomputable def faceOneLiftP2 :
    ULift.{max u v w x, max u w x} (P2 p) →ₐ[p.A]
      ULift.{max u v w x, max u w x} (DegreeOne.P1 p) :=
  (ULift.algEquiv (R := p.A)).symm.toAlgHom.comp
    ((faceOne p).comp (ULift.algEquiv (R := p.A)).toAlgHom)

/-- The face `faceTwo`, between the universe-lifted polynomial algebras. -/
noncomputable def faceTwoLiftP2 :
    ULift.{max u v w x, max u w x} (P2 p) →ₐ[p.A]
      ULift.{max u v w x, max u w x} (DegreeOne.P1 p) :=
  (ULift.algEquiv (R := p.A)).symm.toAlgHom.comp
    ((faceTwo p).comp (ULift.algEquiv (R := p.A)).toAlgHom)

/-- The first face equation of the matching condition, for the lifted faces. -/
theorem lifted_faces_compatible_zero (q : P2 p) :
    (DegreeOne.faceZeroLift p).comp (faceZeroLiftP2 p)
      (ULift.up q) =
    (DegreeOne.faceZeroLift p).comp (faceOneLiftP2 p)
      (ULift.up q) := by
  let : Algebra p.A p.B := p.algebraMap.toAlgebra
  have h := (faces_matching p q).1
  simpa [faceZeroLiftP2, faceOneLiftP2,
    DegreeOne.faceZeroLift, AlgHom.comp_apply] using congrArg
      (ULift.up.{max u v w x, max u w}) h

/-- The second face equation of the matching condition, for the lifted faces. -/
theorem lifted_faces_compatible_one (q : P2 p) :
    (DegreeOne.faceOneLift p).comp (faceZeroLiftP2 p)
      (ULift.up q) =
    (DegreeOne.faceZeroLift p).comp (faceTwoLiftP2 p)
      (ULift.up q) := by
  let : Algebra p.A p.B := p.algebraMap.toAlgebra
  have h := (faces_matching p q).2.1
  simpa [faceZeroLiftP2, faceTwoLiftP2,
    DegreeOne.faceZeroLift, DegreeOne.faceOneLift,
    AlgHom.comp_apply] using congrArg
      (ULift.up.{max u v w x, max u w}) h

/-- The third face equation of the matching condition, for the lifted faces. -/
theorem lifted_faces_compatible_two (q : P2 p) :
    (DegreeOne.faceOneLift p).comp (faceOneLiftP2 p)
      (ULift.up q) =
    (DegreeOne.faceOneLift p).comp (faceTwoLiftP2 p)
      (ULift.up q) := by
  let : Algebra p.A p.B := p.algebraMap.toAlgebra
  have h := (faces_matching p q).2.2
  simpa [faceOneLiftP2, faceTwoLiftP2,
    DegreeOne.faceOneLift, AlgHom.comp_apply] using congrArg
      (ULift.up.{max u v w x, max u w}) h

/-- The three lifted faces of the degree-two polynomial algebra, as maps to the degree-one
object of the one-truncation. -/
noncomputable def polynomialMatchingFamily
    (d : DegreeOne.DegreeOneCoskeleton p) :
    Fin 3 → (algP2 p ⟶ d.truncated.obj
      (op (⟨⦋1⦌, by decide⟩ : SimplexCategory.Truncated 1)) ) :=
  fun i =>
    (AlgCat.ofHom (if i = 0 then faceZeroLiftP2 p else
      if i = 1 then faceOneLiftP2 p else faceTwoLiftP2 p)) ≫
      (degreeOneTruncatedTopIso p d).inv

/-- The defining equation of `polynomialMatchingFamily`, as a named lemma. Letting the
elaborator rediscover it inside the comparison of `degreeTwoToCoskeleton` with the three
displayed faces is what made that comparison exceed the default elaboration budget. -/
theorem polynomialMatchingFamily_apply (d : DegreeOne.DegreeOneCoskeleton p) (i : Fin 3) :
    polynomialMatchingFamily p d i =
      AlgCat.ofHom (if i = 0 then faceZeroLiftP2 p else
        if i = 1 then faceOneLiftP2 p else faceTwoLiftP2 p) ≫
        (degreeOneTruncatedTopIso p d).inv := rfl

/-- The three lifted faces satisfy the compatibilities of the simplicial identities in
degree one. -/
theorem polynomialMatchingFamily_compatible
    (d : DegreeOne.DegreeOneCoskeleton p) :
    ∀ i j : Fin 2, i ≤ j →
      polynomialMatchingFamily p d i.castSucc ≫ d.truncated.map
        (SimplexCategory.Truncated.δ 1 j (by decide) (by decide)).op =
      polynomialMatchingFamily p d j.succ ≫ d.truncated.map
        (SimplexCategory.Truncated.δ 1 i (by decide) (by decide)).op := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · apply AlgCat.hom_ext
    apply AlgHom.ext
    intro q
    cases q with
    | up q =>
      simpa [polynomialMatchingFamily, Category.assoc,
        truncated_faceZero_pre] using congrArg
          (fun z => (degreeZeroTruncatedTopIso p d).inv.hom z)
          (lifted_faces_compatible_zero p q)
  · apply AlgCat.hom_ext
    apply AlgHom.ext
    intro q
    cases q with
    | up q =>
      simpa [polynomialMatchingFamily, Category.assoc,
        truncated_faceZero_pre, truncated_faceOne_pre] using congrArg
          (fun z => (degreeZeroTruncatedTopIso p d).inv.hom z)
          (lifted_faces_compatible_one p q)
  · norm_num at hij
  · apply AlgCat.hom_ext
    apply AlgHom.ext
    intro q
    cases q with
    | up q =>
      simpa [polynomialMatchingFamily, Category.assoc,
        truncated_faceOne_pre] using congrArg
          (fun z => (degreeZeroTruncatedTopIso p d).inv.hom z)
          (lifted_faces_compatible_two p q)

/-- The cone over `degreeTwoSlice` with apex the degree-two polynomial algebra, determined by
the three lifted faces. -/
noncomputable abbrev degreeTwoPolynomialCone
    (d : DegreeOne.DegreeOneCoskeleton p) :
    Cone (degreeTwoSlice p d) := by
  let fam := polynomialMatchingFamily p d
  have hc := (SimplicialObject.Truncated.existsUnique_cone_app_δ_eq_iff
    (n := 0) d.truncated (algP2 p) fam).2
      (polynomialMatchingFamily_compatible p d)
  let π := Classical.choose hc
  exact ⟨algP2 p, π⟩

/-- The algebra map from the displayed polynomial degree two to the actual
degree-two object of the one-coskeleton. -/
@[stacks 09D4 "degree_two"]
noncomputable def degreeTwoToCoskeleton :
    algP2 p ⟶ (DegreeOne.degreeOneCoskeleton p).simplicial _⦋2⦌ :=
  (limit.isLimit (degreeTwoSlice p
      (DegreeOne.degreeOneCoskeleton p))).lift
      (degreeTwoPolynomialCone p
        (DegreeOne.degreeOneCoskeleton p)) ≫
    (degreeTwoCoskeletonLimitIso p
      (DegreeOne.degreeOneCoskeleton p)).inv

/-- The leg of `degreeTwoPolynomialCone` at the `i`-th face arrow is the `i`-th lifted face. -/
theorem degreeTwoPolynomialCone_face
    (d : DegreeOne.DegreeOneCoskeleton p) (i : Fin 3) :
    (degreeTwoPolynomialCone p d).π.app (degreeTwoFaceArrow i) =
      polynomialMatchingFamily p d i := by
  classical
  let fam := polynomialMatchingFamily p d
  have he := (SimplicialObject.Truncated.existsUnique_cone_app_δ_eq_iff
    (n := 0) d.truncated (algP2 p) fam).2
      (polynomialMatchingFamily_compatible p d)
  have hπ := (Classical.choose_spec he).1
  simpa [degreeTwoPolynomialCone, fam, degreeTwoFaceArrow] using hπ i

private theorem degreeTwoToCoskeleton_hom_face (i : Fin 3) :
    degreeTwoToCoskeleton p ≫
      (DegreeOne.degreeOneCoskeleton p).simplicial.δ i ≫
      (DegreeOne.degreeOneCoskeleton p).oneIso.hom =
      AlgCat.ofHom (if i = 0 then faceZeroLiftP2 p else
        if i = 1 then faceOneLiftP2 p else faceTwoLiftP2 p) := by
  let d := DegreeOne.degreeOneCoskeleton p
  let f := degreeTwoFaceArrow i
  let c := degreeTwoPolynomialCone p d
  let m := (limit.isLimit (degreeTwoSlice p d)).lift c
  have hY : f.right =
      op (⟨⦋1⦌, by decide⟩ : SimplexCategory.Truncated 1) := by
    simp [f, degreeTwoFaceArrow]
  let e := degreeOneTruncatedObjIso p d f.right hY
  have hform := degreeTwoCoskeletonLimitIso_face p d i
  have hform' : (degreeTwoCoskeletonLimitIso p d).inv ≫
      d.simplicial.δ i ≫ d.oneIso.hom =
        limit.π (degreeTwoSlice p d) f ≫ e.hom := by
    calc
      _ = (degreeTwoCoskeletonLimitIso p d).inv ≫
          ((degreeTwoCoskeletonLimitIso p d).hom ≫
            limit.π (degreeTwoSlice p d) f ≫
              e.hom) := by rw [hform]
      _ = _ := by simp
  have hfac : m ≫ limit.π (degreeTwoSlice p d) f = c.π.app f := by
    simp [m, c]
  have hcone : c.π.app f = polynomialMatchingFamily p d i := by
    simpa [c, f] using degreeTwoPolynomialCone_face p d i
  have heq : e = degreeOneTruncatedTopIso p d := by
    dsimp [e, degreeOneTruncatedObjIso]
    cases hY
    rfl
  change m ≫ (degreeTwoCoskeletonLimitIso p d).inv ≫
    d.simplicial.δ i ≫ d.oneIso.hom =
      AlgCat.ofHom (if i = 0 then faceZeroLiftP2 p else
        if i = 1 then faceOneLiftP2 p else faceTwoLiftP2 p)
  have hkey : polynomialMatchingFamily p d i ≫ e.hom =
      AlgCat.ofHom (if i = 0 then faceZeroLiftP2 p else
        if i = 1 then faceOneLiftP2 p else faceTwoLiftP2 p) := by
    rw [heq, polynomialMatchingFamily_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hform', ← Category.assoc, hfac, hcone]
  exact hkey

private theorem degreeTwoToCoskeleton_face_apply (q : P2 p) (i : Fin 3) :
    coskeletonFace p i (degreeTwoToCoskeleton p (ULift.up q)) =
      (if i = 0 then faceZero p q else
        if i = 1 then faceOne p q else faceTwo p q) := by
  have h := degreeTwoToCoskeleton_hom_face p i
  have hval := congrArg
    (fun f : algP2 p ⟶ DegreeOne.algP1 p => f.hom (ULift.up q)) h
  have hdown := congrArg ULift.down hval
  fin_cases i <;>
    simpa [coskeletonFace,
      faceZeroLiftP2, faceOneLiftP2, faceTwoLiftP2,
      DegreeOne.faceZeroLift,
      DegreeOne.faceOneLift,
      AlgCat.comp_apply] using hdown

/-- Under the canonical matching equivalence, the algebra map has the three
displayed face maps as its components. -/
@[stacks 09D4 "degree_two"]
theorem matchingEquiv_degreeTwoToCoskeleton (q : P2 p) :
    matchingEquiv p (degreeTwoToCoskeleton p (ULift.up q)) =
      ⟨(faceZero p q, faceOne p q, faceTwo p q), faces_matching p q⟩ := by
  apply Subtype.ext
  rw [matchingEquiv_faces]
  apply Prod.ext
  · simpa using degreeTwoToCoskeleton_face_apply p q 0
  · apply Prod.ext
    · simpa using degreeTwoToCoskeleton_face_apply p q 1
    · simpa using degreeTwoToCoskeleton_face_apply p q 2

private noncomputable def relationVariable (t : p.relationIndex) :
    DegreeOne.P1 p := MvPolynomial.X (Sum.inr t)

private noncomputable def relationVariableIdeal : Ideal (DegreeOne.P1 p) :=
  Ideal.span (Set.range (relationVariable p))

private theorem faceZero_kernel_mem_relationVariableIdeal
    (q : DegreeOne.P1 p)
    (hq : DegreeOne.faceZero p q = 0) :
    q ∈ relationVariableIdeal p := by
  let f : p.variableIndex ⊕ p.relationIndex → p.P0 :=
    Sum.elim (fun i => MvPolynomial.X i) (fun _ => 0)
  have hspan := aeval_sub_algHom_mem_span_X_sub_algHom f
    (DegreeOne.degeneracyZero p) q
  have heval : MvPolynomial.aeval f q = 0 := by
    simpa [f, DegreeOne.faceZero] using hq
  have hle : Ideal.span (Set.range fun i : p.variableIndex ⊕ p.relationIndex =>
      MvPolynomial.X i - DegreeOne.degeneracyZero p (f i)) ≤
      relationVariableIdeal p := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    cases i with
    | inl i => simp [f, DegreeOne.degeneracyZero, MvPolynomial.aeval_X]
    | inr t =>
        exact Ideal.subset_span ⟨t, by simp [f, relationVariable]⟩
  have hq' := hle hspan
  simpa [heval, relationVariableIdeal] using hq'

private theorem relationVariableIdeal_induction
    (q : DegreeOne.P1 p)
    (hq : q ∈ relationVariableIdeal p) :
    ∃ c : p.relationIndex →₀ DegreeOne.P1 p,
      q = c.sum (fun t a => a * relationVariable p t) := by
  classical
  induction hq using Submodule.span_induction with
  | mem q hq =>
      rcases hq with ⟨t, rfl⟩
      refine ⟨Finsupp.single t 1, ?_⟩
      simp [relationVariable, Finsupp.sum_single_index]
  | zero =>
      exact ⟨0, by simp⟩
  | add q r hq hr ihq ihr =>
      obtain ⟨cq, hcq⟩ := ihq
      obtain ⟨cr, hcr⟩ := ihr
      refine ⟨cq + cr, ?_⟩
      have hs : (cq + cr).sum (fun t a => a * relationVariable p t) =
          cq.sum (fun t a => a * relationVariable p t) +
            cr.sum (fun t a => a * relationVariable p t) := by
        apply Finsupp.sum_add_index
        · intro t ht
          simp
        · intro t ht a b
          simp [add_mul]
      rw [hs, hcq, hcr]
  | smul a q hq ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨a • c, ?_⟩
      have hs : (a • c).sum (fun t b => b * relationVariable p t) =
          a * c.sum (fun t b => b * relationVariable p t) := by
        calc
          _ = c.sum (fun t b => (a * b) * relationVariable p t) := by
            apply Finsupp.sum_smul_index
            intro t
            simp
          _ = c.sum (fun t b => a * (b * relationVariable p t)) := by
            congr 1
            funext t b
            ring
          _ = _ := by
            simp only [Finsupp.sum, Finset.mul_sum]
      rw [hs, hc]
      rfl

private noncomputable def liftBoth :
    DegreeOne.P1 p →ₐ[p.A] P2 p :=
  MvPolynomial.aeval fun
    | Sum.inl i => MvPolynomial.X (.base i)
    | Sum.inr t => MvPolynomial.X (.y t)

private noncomputable def liftLast :
    DegreeOne.P1 p →ₐ[p.A] P2 p :=
  MvPolynomial.aeval fun
    | Sum.inl i => MvPolynomial.X (.base i)
    | Sum.inr t => MvPolynomial.X (.z t)

private theorem faceZero_liftBoth (q : DegreeOne.P1 p) :
    faceZero p (liftBoth p q) = q := by
  have h : (faceZero p).comp (liftBoth p) = AlgHom.id p.A _ := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i <;> simp [faceZero, liftBoth]
  exact AlgHom.congr_fun h q

private theorem faceOne_liftBoth (q : DegreeOne.P1 p) :
    faceOne p (liftBoth p q) = q := by
  have h : (faceOne p).comp (liftBoth p) = AlgHom.id p.A _ := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i <;> simp [faceOne, liftBoth]
  exact AlgHom.congr_fun h q

private theorem faceTwo_liftLast (q : DegreeOne.P1 p) :
    faceTwo p (liftLast p q) = q := by
  let : Algebra p.A p.B := p.algebraMap.toAlgebra
  have h : (faceTwo p).comp (liftLast p) = AlgHom.id p.A _ := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i <;> simp [faceTwo, liftLast]
  exact AlgHom.congr_fun h q

/-- The `A`-algebra structure on `B` given by the ring homomorphism of the presentation. -/
local instance degreeTwoPresentationAlgebra : Algebra p.A p.B :=
  p.algebraMap.toAlgebra

private theorem faceOne_kernel_mem_relationDifferenceIdeal
    (q : DegreeOne.P1 p)
    (hq : DegreeOne.faceOne p q = 0) :
    q ∈ Ideal.span (Set.range fun t : p.relationIndex =>
      relationVariable p t - DegreeOne.degeneracyZero p
        (p.presentation.relation t)) := by
  let : Algebra p.A p.B := p.algebraMap.toAlgebra
  let f : p.variableIndex ⊕ p.relationIndex → p.P0 :=
    Sum.elim (fun i => MvPolynomial.X i) p.presentation.relation
  have hspan := aeval_sub_algHom_mem_span_X_sub_algHom f
    (DegreeOne.degeneracyZero p) q
  have heval : MvPolynomial.aeval f q = 0 := by
    simpa [f, DegreeOne.faceOne] using hq
  have hle : Ideal.span (Set.range fun i : p.variableIndex ⊕ p.relationIndex =>
      MvPolynomial.X i - DegreeOne.degeneracyZero p (f i)) ≤
      Ideal.span (Set.range fun t : p.relationIndex =>
        relationVariable p t - DegreeOne.degeneracyZero p
          (p.presentation.relation t)) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    cases i with
    | inl i => simp [f, DegreeOne.degeneracyZero, MvPolynomial.aeval_X]
    | inr t =>
        exact Ideal.subset_span ⟨t, by simp [f, relationVariable,
          DegreeOne.degeneracyZero]⟩
  have hq' := hle hspan
  simpa [heval] using hq'

private noncomputable def commonKernelGenerator
    (i : Rel p ⊕ (p.relationIndex × p.relationIndex)) :
    DegreeOne.P1 p := by
  letI : Algebra p.A p.B := p.algebraMap.toAlgebra
  exact match i with
    | Sum.inl r => r.val.sum (fun t a =>
        DegreeOne.degeneracyZero p a * relationVariable p t)
    | Sum.inr (t, t') =>
        relationVariable p t * relationVariable p t' -
          DegreeOne.degeneracyZero p (p.presentation.relation t) *
            relationVariable p t'

private noncomputable def commonKernelIdeal :
    Ideal (DegreeOne.P1 p) :=
  Ideal.span (Set.range (commonKernelGenerator p))

private theorem relationDifference_mul_mem_commonKernelIdeal
    (a : DegreeOne.P1 p)
    (ha : a ∈ Ideal.span (Set.range fun s : p.relationIndex =>
      relationVariable p s - DegreeOne.degeneracyZero p
        (p.presentation.relation s))) (t : p.relationIndex) :
    a * relationVariable p t ∈ commonKernelIdeal p := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
      rcases ha with ⟨s, rfl⟩
      exact Ideal.subset_span ⟨Sum.inr (s, t), by
        simp [commonKernelGenerator, relationVariable, mul_sub,
          mul_comm]⟩
  | zero => simp
  | add a b ha hb iha ihb =>
      simpa [add_mul] using (commonKernelIdeal p).add_mem iha ihb
  | smul r a ha iha =>
      simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
        (commonKernelIdeal p).mul_mem_left r iha

private theorem finsupp_sum_add_pointwise
    {ι M N : Type*} [Zero M] [AddCommMonoid N]
    (c : ι →₀ M) (f g : ι → M → N) :
    c.sum (fun i a => f i a + g i a) = c.sum f + c.sum g := by
  classical
  simp only [Finsupp.sum, Finset.sum_add_distrib]

private theorem commonKernel_mem
    (q : DegreeOne.P1 p)
    (h0 : DegreeOne.faceZero p q = 0)
    (h1 : DegreeOne.faceOne p q = 0) :
    q ∈ commonKernelIdeal p := by
  classical
  let : Algebra p.A p.B := p.algebraMap.toAlgebra
  obtain ⟨c, hc⟩ := relationVariableIdeal_induction p q
    (faceZero_kernel_mem_relationVariableIdeal p q h0)
  let r0 : p.relationIndex →₀ p.P0 :=
    c.mapRange (DegreeOne.faceOne p) (map_zero _)
  have hsum : c.sum (fun t a =>
      DegreeOne.faceOne p a * p.presentation.relation t) = 0 := by
    have hmap : DegreeOne.faceOne p q =
        c.sum (fun t a =>
          DegreeOne.faceOne p a * p.presentation.relation t) := by
      rw [hc]
      rw [_root_.map_finsuppSum]
      simp [relationVariable, faceOne_relationVariable, map_mul]
    rw [← hmap]
    exact h1
  have hr : r0.sum (fun t a => a * p.presentation.relation t) = 0 := by
    simpa [r0, Finsupp.sum_mapRange_index] using hsum
  let r : Rel p := ⟨r0, hr⟩
  have hr_apply (t : p.relationIndex) : r.val t =
      DegreeOne.faceOne p (c t) := by
    simp [r, r0, Finsupp.mapRange_apply]
  have hdelta (t : p.relationIndex) :
      DegreeOne.faceOne p
        (c t - DegreeOne.degeneracyZero p
          (DegreeOne.faceOne p (c t))) = 0 := by
    simp [map_sub, faceOne_degeneracyZero_apply]
  have hdelta_mem (t : p.relationIndex) :
      (c t - DegreeOne.degeneracyZero p
        (DegreeOne.faceOne p (c t))) * relationVariable p t ∈
        commonKernelIdeal p :=
    relationDifference_mul_mem_commonKernelIdeal p _
      (faceOne_kernel_mem_relationDifferenceIdeal p _ (hdelta t)) t
  have hsum_delta : c.sum (fun t a =>
      (a - DegreeOne.degeneracyZero p
        (DegreeOne.faceOne p a)) * relationVariable p t) ∈
      commonKernelIdeal p := by
    change (∑ t ∈ c.support, (c t -
      DegreeOne.degeneracyZero p
        (DegreeOne.faceOne p (c t))) * relationVariable p t) ∈ _
    exact (commonKernelIdeal p).sum_mem fun t _ ↦ hdelta_mem t
  have hsum_syzygy : r.val.sum (fun t a =>
      DegreeOne.degeneracyZero p a * relationVariable p t) ∈
      commonKernelIdeal p :=
    Ideal.subset_span ⟨Sum.inl r, rfl⟩
  have hmap : r.val.sum (fun t a =>
      DegreeOne.degeneracyZero p a * relationVariable p t) =
      c.sum (fun t a => DegreeOne.degeneracyZero p
        (DegreeOne.faceOne p a) * relationVariable p t) := by
    change r0.sum (fun t a =>
      DegreeOne.degeneracyZero p a * relationVariable p t) = _
    dsimp [r0]
    exact Finsupp.sum_mapRange_index
      (f := DegreeOne.faceOne p) (hf := map_zero _)
      (g := c)
      (h := fun t a => DegreeOne.degeneracyZero p a *
        relationVariable p t)
      (by intro t; simp)
  have hgen : commonKernelGenerator p (Sum.inl r) = r.val.sum (fun t a =>
      DegreeOne.degeneracyZero p a * relationVariable p t) := rfl
  have hsplit : q =
      commonKernelGenerator p (Sum.inl r) +
      c.sum (fun t a =>
          (a - DegreeOne.degeneracyZero p
            (DegreeOne.faceOne p a)) * relationVariable p t) := by
    calc
      _ = c.sum (fun t a => a * relationVariable p t) := hc
      _ = c.sum (fun t a =>
          DegreeOne.degeneracyZero p
              (DegreeOne.faceOne p a) * relationVariable p t) +
          c.sum (fun t a =>
            (a - DegreeOne.degeneracyZero p
              (DegreeOne.faceOne p a)) * relationVariable p t) := by
            calc
              _ = c.sum (fun t a =>
                    DegreeOne.degeneracyZero p
                        (DegreeOne.faceOne p a) * relationVariable p t +
                      (a - DegreeOne.degeneracyZero p
                        (DegreeOne.faceOne p a)) * relationVariable p t) := by
                    apply Finsupp.sum_congr
                    intro t ht
                    ring
              _ = _ := finsupp_sum_add_pointwise c _ _
      _ = _ := by rw [← hmap, ← hgen]
  rw [hsplit]
  exact (commonKernelIdeal p).add_mem hsum_syzygy hsum_delta

private theorem commonKernel_has_lift
    (q : DegreeOne.P1 p) (hq : q ∈ commonKernelIdeal p) :
    ∃ d : P2 p,
      faceZero p d = 0 ∧ faceOne p d = 0 ∧ faceTwo p d = q := by
  classical
  let : Algebra p.A p.B := p.algebraMap.toAlgebra
  induction hq using Submodule.span_induction with
  | mem q hq =>
      rcases hq with ⟨i, rfl⟩
      cases i with
      | inl r =>
          refine ⟨MvPolynomial.X (.v r), ?_, ?_, ?_⟩
          · simp [faceZero]
          · simp [faceOne]
          · simp [faceTwo, commonKernelGenerator, relationVariable]
      | inr pair =>
          rcases pair with ⟨t, t'⟩
          refine ⟨MvPolynomial.X (.w t t'), ?_, ?_, ?_⟩
          · simp [faceZero]
          · simp [faceOne]
          · simp [faceTwo, commonKernelGenerator, relationVariable]
  | zero => exact ⟨0, by simp [faceZero], by simp [faceOne], by simp [faceTwo]⟩
  | add q r hq hr ihq ihr =>
      obtain ⟨dq, hq0, hq1, hq2⟩ := ihq
      obtain ⟨dr, hr0, hr1, hr2⟩ := ihr
      refine ⟨dq + dr, ?_, ?_, ?_⟩ <;> simp [map_add, hq0, hq1, hq2, hr0, hr1, hr2]
  | smul a q hq ih =>
      obtain ⟨d, h0, h1, h2⟩ := ih
      refine ⟨liftLast p a * d, ?_, ?_, ?_⟩
      · simp [map_mul, h0]
      · simp [map_mul, h1]
      · simp [map_mul, faceTwo_liftLast, h2, smul_eq_mul]

private noncomputable def zCorrection
    (c : p.relationIndex →₀ DegreeOne.P1 p) : P2 p :=
  c.sum (fun t a => liftBoth p a * MvPolynomial.X (.z t))

private theorem faceZero_zCorrection
    (c : p.relationIndex →₀ DegreeOne.P1 p) :
    faceZero p (zCorrection p c) = 0 := by
  let : Algebra p.A p.B := p.algebraMap.toAlgebra
  rw [zCorrection, _root_.map_finsuppSum]
  simp only [map_mul, faceZero, MvPolynomial.aeval_X, mul_zero]
  simp

private theorem faceOne_zCorrection
    (c : p.relationIndex →₀ DegreeOne.P1 p) :
    faceOne p (zCorrection p c) =
      c.sum (fun t a => a * relationVariable p t) := by
  rw [zCorrection, _root_.map_finsuppSum]
  simp only [map_mul]
  simp_rw [faceOne_liftBoth]
  simp [faceOne, relationVariable]

private theorem polynomial_preimage_matchingTriple
    (g₀ g₁ g₂ : DegreeOne.P1 p)
    (hg : MatchingTriple p g₀ g₁ g₂) :
    ∃ q : P2 p,
      faceZero p q = g₀ ∧ faceOne p q = g₁ ∧ faceTwo p q = g₂ := by
  let : Algebra p.A p.B := p.algebraMap.toAlgebra
  have hd : DegreeOne.faceZero p (g₁ - g₀) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hg.1.symm
  obtain ⟨c, hc⟩ := relationVariableIdeal_induction p (g₁ - g₀)
    (faceZero_kernel_mem_relationVariableIdeal p _ hd)
  let q₀ := liftBoth p g₀ + zCorrection p c
  have hq₀ : faceZero p q₀ = g₀ := by
    simp [q₀, faceZero_liftBoth, faceZero_zCorrection]
  have hq₁ : faceOne p q₀ = g₁ := by
    dsimp [q₀]
    rw [map_add, faceOne_liftBoth, faceOne_zCorrection, ← hc]
    ring
  let e := g₂ - faceTwo p q₀
  have he0 : DegreeOne.faceZero p e = 0 := by
    rw [map_sub]
    have hface := (faces_matching p q₀).2.1
    rw [hq₀] at hface
    exact sub_eq_zero.mpr (hg.2.1.symm.trans hface)
  have he1 : DegreeOne.faceOne p e = 0 := by
    rw [map_sub]
    have hface := (faces_matching p q₀).2.2
    rw [hq₁] at hface
    exact sub_eq_zero.mpr (hg.2.2.symm.trans hface)
  obtain ⟨d, hd0, hd1, hd2⟩ :=
    commonKernel_has_lift p e (commonKernel_mem p e he0 he1)
  refine ⟨q₀ + d, ?_, ?_, ?_⟩
  · simp [map_add, hq₀, hd0]
  · simp [map_add, hq₁, hd1]
  · rw [map_add, hd2]
    dsimp [e]
    ring

/-- The displayed algebra map onto the actual second coskeleton degree is
surjective. -/
@[stacks 09D4 "degree_two"]
theorem degreeTwoToCoskeleton_surjective :
    Function.Surjective (degreeTwoToCoskeleton p) :=
  by
    intro a
    let g := (matchingEquiv p a).val
    obtain ⟨q, h0, h1, h2⟩ :=
      polynomial_preimage_matchingTriple p g.1 g.2.1 g.2.2
        (matchingEquiv p a).property
    refine ⟨ULift.up q, ?_⟩
    apply (matchingEquiv p).injective
    rw [matchingEquiv_degreeTwoToCoskeleton]
    exact Subtype.ext (Prod.ext h0 (Prod.ext h1 h2))

end Algebra.PolynomialPresentationWithKernelGenerators.DegreeTwo

end
