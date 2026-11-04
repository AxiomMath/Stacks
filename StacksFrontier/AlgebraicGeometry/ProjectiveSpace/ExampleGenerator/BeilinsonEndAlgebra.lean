module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.BeilinsonEquivalence

/-!
# The endomorphism algebra of Beilinson's equivalence

Let `A` be a ring, `X = P^n_A` and `P = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)`. The differential graded
algebra `Hom_{Comp^dg(𝒪_X)}(P, P)` of `P` placed in degree zero is concentrated in degree zero,
has zero differential, and its degree-zero part is the ring `R = Hom_{𝒪_X}(P, P)` of
[Stacks, Tag 0CS9].

## Main results

* `Stacks.AlgebraicGeometry.Beilinson.endAlgebra_grading_eq_bot`: no nonzero homogeneous
  elements outside degree zero.
* `Stacks.AlgebraicGeometry.Beilinson.endAlgebra_mem_grading_zero`: every element has degree zero.
* `Stacks.AlgebraicGeometry.Beilinson.endAlgebra_d_eq_zero`: the differential vanishes.
* `Stacks.AlgebraicGeometry.Beilinson.endAlgebraRingEquiv`: the underlying ring is
  `End P = Hom_{𝒪_X}(P, P)`, with multiplication the composition `f * g = f ∘ g`.

## References

* [Stacks Project, Tag 0BQU](https://stacks.math.columbia.edu/tag/0BQU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex.HomComplex
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)
open Stacks.AlgebraicGeometry.ExampleGenerator (twistSumModule)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace Stacks.AlgebraicGeometry.Beilinson

variable (A : Type u) [CommRing A] (n : ℕ)

/-- `P` in degree zero, lifted to the ambient universe of Tag 09LX: the object whose
endomorphisms form `endAlgebra`. -/
abbrev liftedGenerator : CochainComplex (RingedSite.TensorModO.{u, u, u, u, u} (site A n)) ℤ :=
  RingedSite.liftComplex.{u, u, u, u, u} (site A n) (generator A n)

/-- The degree-`p` term of `liftedGenerator` is zero for `p ≠ 0`. -/
theorem isZero_liftedGenerator_X {p : ℤ} (hp : p ≠ 0) : IsZero ((liftedGenerator A n).X p) :=
  (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (twistSumModule A n) p hp).of_iso
    ((HomologicalComplex.eval _ _ p).mapIso
      (RingedSite.liftComplexSelfIso (site A n) (generator A n)))

/-- `P`, as an object of the ambient category of Tag 09LX. -/
def generatorModule : RingedSite.TensorModO.{u, u, u, u, u} (site A n) := twistSumModule A n

/-- The identification of `P` with the degree-zero term of `liftedGenerator`. -/
def liftedGeneratorXZeroIso :
    generatorModule A n ≅
      (liftedGenerator A n).X 0 :=
  Iso.trans (Y := (generator A n).X 0)
    (HomologicalComplex.singleObjXSelf (V := RingedSite.TensorModO.{u, u, u, u, u} (site A n))
      (ComplexShape.up ℤ) 0 (generatorModule A n)).symm
    (by
      exact (HomologicalComplex.eval _ _ 0).mapIso
        (RingedSite.liftComplexSelfIso (site A n) (generator A n)).symm)

/-- Cochains of nonzero degree from `liftedGenerator` to itself vanish. -/
theorem subsingleton_cochain {m : ℤ} (hm : m ≠ 0) :
    Subsingleton (Cochain (liftedGenerator A n) (liftedGenerator A n) m) := by
  refine ⟨fun z₁ z₂ => Cochain.ext _ _ fun p q hpq => ?_⟩
  by_cases hp : p = 0
  · exact (isZero_liftedGenerator_X A n (show q ≠ 0 by omega)).eq_of_tgt _ _
  · exact (isZero_liftedGenerator_X A n hp).eq_of_src _ _

/-- A cochain of degree zero from `liftedGenerator` to itself is determined by its component in
degree zero. -/
theorem cochain_zero_ext (z₁ z₂ : Cochain (liftedGenerator A n) (liftedGenerator A n) 0)
    (h : z₁.v 0 0 (add_zero 0) = z₂.v 0 0 (add_zero 0)) : z₁ = z₂ := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  by_cases hp : p = 0
  · subst hp
    obtain rfl : q = 0 := by omega
    exact h
  · exact (isZero_liftedGenerator_X A n hp).eq_of_src _ _

/-- **`Hom^dg(P, P)` has no nonzero homogeneous elements outside degree zero.** -/
theorem endAlgebra_grading_eq_bot {m : ℤ} (hm : m ≠ 0) : (endAlgebra A n).grading m = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  let f := (RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).algebraHom m
  exact (Submodule.mem_bot ℤ).2 (show (⟨a, ha⟩ : (endAlgebra A n).grading m).1 = 0 from
    congrArg Subtype.val
      (f.injective (@Subsingleton.elim _ (subsingleton_cochain A n hm) (f ⟨a, ha⟩) (f 0))))

/-- **Every element of `Hom^dg(P, P)` has degree zero.** -/
theorem endAlgebra_mem_grading_zero (a : (endAlgebra A n).A) : a ∈ (endAlgebra A n).grading 0 := by
  refine DirectSum.Decomposition.inductionOn (endAlgebra A n).grading (zero_mem _)
    (fun {i} x => ?_) (fun _ _ => add_mem) a
  by_cases hi : i = 0
  · subst hi
    exact x.2
  · rw [(Submodule.eq_bot_iff _).1 (endAlgebra_grading_eq_bot A n hi) x x.2]
    exact zero_mem _

/-- **The differential of `Hom^dg(P, P)` vanishes.** -/
theorem endAlgebra_d_eq_zero : (endAlgebra A n).d = 0 := by
  ext a
  have h := (endAlgebra A n).d_mem 0 a (endAlgebra_mem_grading_zero A n a)
  rw [zero_add, endAlgebra_grading_eq_bot A n one_ne_zero] at h
  exact (Submodule.mem_bot ℤ).1 h

/-- The degree-zero endomorphism of `P` underlying an element of `Hom^dg(P, P)`. -/
def endAlgebraToEnd (a : (endAlgebra A n).A) :
    End (generatorModule A n) :=
  (liftedGeneratorXZeroIso A n).hom ≫
    (((RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).algebraHom 0)
      ⟨a, endAlgebra_mem_grading_zero A n a⟩ :
        Cochain (liftedGenerator A n) (liftedGenerator A n) 0).v 0 0 (add_zero 0) ≫
    (liftedGeneratorXZeroIso A n).inv

/-- `endAlgebraToEnd a` only depends on `a` as an element of the degree-zero part. -/
private theorem endAlgebraToEnd_eq_of_val_eq (a : (endAlgebra A n).A)
    (c : (endAlgebra A n).grading 0) (hc : c.1 = a) :
    endAlgebraToEnd A n a = (liftedGeneratorXZeroIso A n).hom ≫
      (((RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).algebraHom 0) c :
        Cochain (liftedGenerator A n) (liftedGenerator A n) 0).v 0 0 (add_zero 0) ≫
      (liftedGeneratorXZeroIso A n).inv := by
  subst hc
  rfl

/-- `endAlgebraToEnd` sends the unit of `Hom^dg(P, P)` to the identity of `P`. -/
theorem endAlgebraToEnd_one : endAlgebraToEnd A n 1 = 1 := by
  obtain ⟨e, he1, he⟩ :=
    (RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).algebra_one
  rw [endAlgebraToEnd_eq_of_val_eq A n 1 e he1, he]
  show _ ≫ (Cochain.ofHom (𝟙 (liftedGenerator A n))).v 0 0 (add_zero 0) ≫ _ = 𝟙 _
  rw [Cochain.ofHom_v, HomologicalComplex.id_f, Category.id_comp]
  exact (liftedGeneratorXZeroIso A n).hom_inv_id

/-- `endAlgebraToEnd` sends a product `a * b` to the composite of `endAlgebraToEnd a` after
`endAlgebraToEnd b`. -/
theorem endAlgebraToEnd_mul (a b : (endAlgebra A n).A) :
    endAlgebraToEnd A n (a * b) = endAlgebraToEnd A n a * endAlgebraToEnd A n b := by
  obtain ⟨c, hc1, hc⟩ := (RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ
    (generator A n)).algebra_mul 0 0 0 (add_zero 0) ⟨a, endAlgebra_mem_grading_zero A n a⟩
      ⟨b, endAlgebra_mem_grading_zero A n b⟩
  rw [endAlgebraToEnd_eq_of_val_eq A n _ c hc1, hc, End.mul_def, endAlgebraToEnd, endAlgebraToEnd]
  show _ ≫ (Cochain.comp
    (((RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).algebraHom 0)
      ⟨b, endAlgebra_mem_grading_zero A n b⟩ :
        Cochain (liftedGenerator A n) (liftedGenerator A n) 0)
    (((RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).algebraHom 0)
      ⟨a, endAlgebra_mem_grading_zero A n a⟩ :
        Cochain (liftedGenerator A n) (liftedGenerator A n) 0)
    (add_zero 0)).v 0 0 (add_zero 0) ≫ _ = _
  rw [Cochain.comp_zero_cochain_v]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- `endAlgebraToEnd` is additive. -/
theorem endAlgebraToEnd_add (a b : (endAlgebra A n).A) :
    endAlgebraToEnd A n (a + b) = endAlgebraToEnd A n a + endAlgebraToEnd A n b := by
  have h : (⟨a + b, endAlgebra_mem_grading_zero A n (a + b)⟩ : (endAlgebra A n).grading 0) =
      ⟨a, endAlgebra_mem_grading_zero A n a⟩ + ⟨b, endAlgebra_mem_grading_zero A n b⟩ := rfl
  rw [endAlgebraToEnd, h, map_add, Cochain.add_v, Preadditive.add_comp, Preadditive.comp_add]
  rfl

/-- `endAlgebraToEnd` is a bijection from `Hom^dg(P, P)` onto the endomorphisms of `P`. -/
theorem endAlgebraToEnd_bijective : Function.Bijective (endAlgebraToEnd A n) := by
  let ι := liftedGeneratorXZeroIso A n
  let α := (RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).algebraHom 0
  refine ⟨fun a b hab => ?_, fun f => ?_⟩
  · have h1 := congrArg (fun f : End (generatorModule A n) => ι.inv ≫ f ≫ ι.hom) hab
    simp only [endAlgebraToEnd, Category.assoc] at h1
    exact congrArg Subtype.val (α.injective (cochain_zero_ext A n _ _ h1))
  · let z : Cochain (liftedGenerator A n) (liftedGenerator A n) 0 :=
      Cochain.single (p := 0) (q := 0) (ι.inv ≫ f ≫ ι.hom) 0
    refine ⟨(α.symm z).1, ?_⟩
    have h : (⟨(α.symm z).1, endAlgebra_mem_grading_zero A n _⟩ : (endAlgebra A n).grading 0) =
      α.symm z := rfl
    rw [endAlgebraToEnd, h, LinearEquiv.apply_symm_apply]
    show ι.hom ≫ z.v 0 0 (add_zero 0) ≫ ι.inv = f
    rw [show z.v 0 0 (add_zero 0) = ι.inv ≫ f ≫ ι.hom from Cochain.single_v _ _ _]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- `endAlgebraToEnd` as a ring homomorphism. -/
def endAlgebraToEndRingHom : (endAlgebra A n).A →+* End (generatorModule A n) where
  toFun := endAlgebraToEnd A n
  map_one' := endAlgebraToEnd_one A n
  map_mul' := endAlgebraToEnd_mul A n
  map_zero' := by
    have h := endAlgebraToEnd_add A n 0 0
    rw [add_zero] at h
    exact left_eq_add.1 h
  map_add' := endAlgebraToEnd_add A n

/-- The underlying ring of `Hom^dg(P, P)` is the endomorphism ring of `P` in the ambient category
of Tag 09LX. -/
def endAlgebraRingEquivTensorModO :
    (endAlgebra A n).A ≃+* End (generatorModule A n) :=
  RingEquiv.ofBijective (R := (endAlgebra A n).A) (S := End (generatorModule A n))
    (endAlgebraToEndRingHom A n) (endAlgebraToEnd_bijective A n)

/-- The endomorphism ring of `P` does not depend on the spelling of the category of
`𝒪_X`-modules. -/
def endModulesRingEquiv :
    End (generatorModule A n) ≃+*
      End (twistSumModule A n) where
  toEquiv := Equiv.refl _
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- **The underlying ring of `Hom^dg(P, P)` is `R = Hom_{𝒪_X}(P, P)`** (Tag 0CS9): the
degree-zero component identifies it with the endomorphism ring of `P`, multiplication being
composition, `f * g = f ∘ g`. -/
def endAlgebraRingEquiv : (endAlgebra A n).A ≃+* End (twistSumModule A n) :=
  (endAlgebraRingEquivTensorModO A n).trans (endModulesRingEquiv A n)

end Stacks.AlgebraicGeometry.Beilinson

end
