module

public import StacksFrontier.Homology.HomComplex.DerivedAdjunction

/-!
# Shifting the target of a Hom complex

Let `R` be a ring, let `C` be an `R`-linear preadditive category and let `M` and `K` be cochain
complexes in `C`. Shifting the target of the Hom complex is the same as shifting the Hom complex
itself: a degree-`n` cochain `M ⟶ K⟦a⟧` is a degree-`n + a` cochain `M ⟶ K` read through the
canonical identification of the terms of a shifted complex, and the two differentials agree
because the differential of a shifted complex carries the sign `(-1)^a`, which is exactly the
sign that Mathlib's `CochainComplex.HomComplex.Cochain.rightShift` introduces.

Unlike the general shift identification of [stacks 0FNN], which shifts source and target
independently and therefore carries the degree-dependent Koszul sign `(-1)^(n b)`, this is the
special case `b = 0`, where no such sign appears and the source complex is untouched. That is
what makes the identification natural in the source complex: precomposition with a chain map
acts only on the source index, so it commutes with the reindexing of the target on the nose.

## Main definitions

* `StacksDraft.DerivedHom.HomShift.homComplexTargetShiftIso` — the identification
  `Hom^•(M, K)⟦a⟧ ≅ Hom^•(M, K⟦a⟧)`.
* `StacksDraft.DerivedHom.HomShift.homComplexInto` — the Hom complex into a fixed target as a
  contravariant functor of the source complex.
* `StacksDraft.DerivedHom.HomShift.homComplexIntoShiftIso` — the identification above as an
  isomorphism of functors of the source complex.

## References

* [Stacks Project, Tag 0FNN](https://stacks.math.columbia.edu/tag/0FNN)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex CochainComplex.HomComplex

namespace StacksDraft.DerivedHom.HomShift

universe u

section Cochain

variable (R : Type*) [Ring R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]

/-- **Shifting the target of a Hom complex shifts the Hom complex.** The degree-`n` component is
`CochainComplex.HomComplex.Cochain.rightShift`, which reindexes the target of a cochain of
degree `n + a` by `a`; the differentials match because shifting a complex multiplies its
differential by `(-1)^a`, and `Cochain.δ_rightShift` produces exactly that sign. -/
def homComplexTargetShiftIso (M K : CochainComplex C ℤ) (a : ℤ) :
    (HomComplexR R M K)⟦a⟧ ≅ HomComplexR R M (K⟦a⟧) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (Cochain.rightShiftLinearEquiv R M K (n + a) a n rfl).toModuleIso) (by
      intro i j hij
      obtain rfl : j = i + 1 := by simpa using hij.symm
      ext z
      change Cochain M K (i + a) at z
      change δ i (i + 1) (z.rightShift a i rfl) =
        (a.negOnePow • δ (i + a) (i + 1 + a) z).rightShift a (i + 1) rfl
      rw [Cochain.rightShift_units_smul,
        Cochain.δ_rightShift z a i (i + 1) rfl (i + 1 + a) rfl])

/-- The identification of `Cochain.rightShift` with the evident reindexing of homogeneous
components: it leaves the source index alone. -/
theorem homComplexTargetShiftIso_hom_apply (M K : CochainComplex C ℤ) (a n : ℤ)
    (z : Cochain M K (n + a)) :
    ((homComplexTargetShiftIso R M K a).hom.f n).hom z = z.rightShift a n rfl := rfl

end Cochain

section Functorial

variable (R : Type u) [CommRing R]

/-- The Hom complex into a fixed target, as a contravariant functor of the source complex.
This is `StacksDraft.DerivedHom.Model.homComplexFunctor` with its covariant variable fixed. -/
abbrev homComplexInto (I : Model.Complex R) : (Model.Complex R)ᵒᵖ ⥤ Model.Complex R :=
  (Functor.curry.obj (Model.homComplexFunctor R)).flip.obj I

/-- **Precomposition commutes with shifting the target.** A chain map acts on a cochain by
composition on the source side, which the target reindexing does not touch. -/
theorem homComplexTargetShiftIso_naturality {M M' : Model.Complex R} (f : M' ⟶ M)
    (K : Model.Complex R) (a : ℤ) :
    (Stacks.HomComplex.TensorHomMap.precomp R M' M K f)⟦a⟧' ≫ (homComplexTargetShiftIso R M' K
      a).hom =
      (homComplexTargetShiftIso R M K a).hom ≫ Stacks.HomComplex.TensorHomMap.precomp R M' M (K⟦a⟧)
        f := by
  ext n z
  change Cochain M K (n + a) at z
  show (((Cochain.ofHom f).comp z (zero_add (n + a))).rightShift a n rfl) =
    (Cochain.ofHom f).comp (z.rightShift a n rfl) (zero_add n)
  ext p q hpq
  rw [Cochain.rightShift_v _ a n rfl p q hpq (p + (n + a)) rfl,
    Cochain.zero_cochain_comp_v, Cochain.zero_cochain_comp_v,
    Cochain.rightShift_v z a n rfl p q hpq (p + (n + a)) rfl, Category.assoc]

/-- **Shifting the target of a Hom complex, as an isomorphism of functors of the source
complex.** -/
def homComplexIntoShiftIso (K : Model.Complex R) (a : ℤ) :
    homComplexInto R K ⋙ CategoryTheory.shiftFunctor (Model.Complex R) a ≅
      homComplexInto R (K⟦a⟧) :=
  NatIso.ofComponents (fun M ↦ homComplexTargetShiftIso R M.unop K a) (by
    intro M M' f
    dsimp [homComplexInto, Model.homComplexFunctor]
    simp only [Stacks.HomComplex.TensorHomMap.postcomp_id, Category.comp_id]
    exact homComplexTargetShiftIso_naturality R f.unop K a)

end Functorial

end StacksDraft.DerivedHom.HomShift

end
