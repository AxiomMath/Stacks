module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulDerivedCompletion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCompositionUnitShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualTriangulated
public import StacksFrontier.Algebra.Homology.DerivedCategory.StupidTruncationTriangle

/-!
# Clause 3 of Tag 08JJ at the Koszul complexes

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪` and let `K` be an
object of `D(𝒪)`. [Stacks, Tag 08JD] supplies the canonical map

`Φ_L : K ⊗^𝐋_𝒪 L^∨ ⟶ R𝑆heafHom_𝒪(L, K)`,

`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom`, and clause 3 of
[Stacks, Tag 08JJ] asserts that it is invertible for perfect `L`. This file proves that
assertion at the Koszul complexes `K(𝒪, f_1^{n+1}, …, f_r^{n+1})` of
`AlgebraicGeometry.RingedSite.koszulPowerComplex`, which is the last of the three inputs of the
formula of [Stacks, Tag 0A0E]: it is the hypothesis `hdual` of
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem`, and with
it supplied that formula is
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorKoszulComplex_completionFunctor` of
`KoszulCompletionFormula.lean`.

The dévissage is the one of [Stacks, Tag 08JJ], run as the induction on the stupid filtration of
a bounded complex,
`Stacks.DerivedCategory.BoundedInduction.property_of_bounded_complex_of_distTriang`.
The Koszul complex is concentrated in degrees `0, …, r` and its term in degree `p` is a finite
product of copies of `𝒪`, so the induction reduces the statement to the structure sheaf placed
in a single degree, which is a shift of the base case
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_structureSheaf`.

## Main results

* `AlgebraicGeometry.RingedSite.finite_support_koszulPowerComplex`: the Koszul complex is
  bounded, its non-zero terms lying in degrees `0, …, r`.
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_shift_obj₂_of_distTriang`:
  the closure of the class `{L | ∀ n, IsIso (Φ_{L⟦n⟧})}` under the *second* vertex of a
  distinguished triangle, which is the orientation the stupid-filtration induction consumes.
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_singleFunctor_unit`: `Φ` is
  invertible at the structure sheaf placed in an arbitrary degree.
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_singleFunctor_pi_unit`: `Φ` is
  invertible at a finite product of copies of the structure sheaf placed in an arbitrary degree.
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_koszulPowerComplex` and
  `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_koszulPowerSystem`:
  **`Φ` is invertible at the Koszul complexes**, in the second case in exactly the form the
  input `hdual` of
  `AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem` is
  discharged in.

## Implementation notes

*Nothing below is conditional.* Everything here is proved with no instance hypotheses beyond
the standing ones on the site and its tensor product; in particular
`CategoryTheory.NatTrans.CommShift (derivedTensorDualNatTrans X T M) ℤ` — the compatibility of
`Φ` with the shift, which does not follow from the fields of the derived tensor product datum of
Stacks 06YU as they stand (see the section "What this file does not contain" of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomSourceCommShift`) — is not
used, and neither is the
dévissage step that needs it,
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_shift`. Two things make that
possible. The triangle step
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_distTriang` does not need it,
and its four instance hypotheses are all in the library:
`AlgebraicGeometry.RingedSite.derivedSheafHomFlipCommShift` and
`AlgebraicGeometry.RingedSite.derivedSheafHomFlipIsTriangulated` for the target, and for the
source those composed with the `commShift_right` and `exact_right` fields of Stacks 06YU — the
composite being `AlgebraicGeometry.RingedSite.isTriangulated_tensorDualSourceFunctor`. And the
shifts the induction needs are needed **only at the structure sheaf**, where
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_shiftedStructureSheaf` supplies
them directly, the shift being absorbed by the source complex rather than by `Φ`.

What is new here is the mathematics between the base case `L = 𝒪` and the Koszul complexes,
which the implementation notes of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulCechHomotopyColimit`
identified as the missing step — "the Koszul complexes are not retracts of finite direct sums of
copies of `𝒪`, and reaching them needs the closure of that class under the shift and under
distinguished triangles".

*The induction is run on the shift-closed predicate.* The property fed to the
stupid-filtration induction is not `IsIso (Φ_A)` but `∀ n, IsIso (Φ_{A⟦n⟧})`. That costs nothing
at the terms — a shift of the structure sheaf placed in a degree is the structure sheaf placed in
another degree — and it buys the `⟦-1⟧` hypotheses of the triangle step for free, so the closure
of the class under the shift, `isIso_derivedTensorDualToSheafHom_of_shift`, is **not used**. The
shift by `n` in the extension step is paid for by shifting the *triangle*, which is again
distinguished by `CategoryTheory.Pretriangulated.Triangle.shift_distinguished`, rather than by
shifting `Φ`.

*The orientation of the extension step.* `isIso_derivedTensorDualToSheafHom_of_distTriang`
concludes at the *first* vertex of a distinguished triangle, while the stupid-filtration
induction supplies the first and third and asks for the second. The two are interchanged by one
rotation, `CategoryTheory.Pretriangulated.rot_of_distTriang`.

*The terms are products, not biproducts.* The degree-`p` term of the Koszul complex is the
categorical product `∏ 𝒪` over `CategoryTheory.AlternatingCech.Idx r p`, the subsets of
`Fin r` of cardinality `p`, which is a finite type; the comparison with the biproduct is
`CategoryTheory.Limits.biproduct.isoProduct`, after which the decomposition of the identity of
the biproduct feeds
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_sum_id` through the additive
single functor. No `CategoryTheory.Limits.HasBiproduct` in the derived category is needed: the
decomposition of the identity is transported as a sum of morphisms, not as a universal property.

*No `@[stacks]` attribute is attached.* What is proved is one clause of [Stacks, Tag 08JJ] at
particular complexes, not the tag; the perfect case in general, and the tag, are not proved.

## References

* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

section Bounded

variable (X : RingedSite.{u, u, u}) {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **The Koszul complex is bounded.** Its index type in degree `p` is the subsets of `Fin r`
of cardinality `p`, which is empty unless `0 ≤ p ≤ r`; so its non-zero terms lie in `[0, r]`.
This is the hypothesis `hK` of the stupid-filtration induction. -/
theorem finite_support_koszulPowerComplex (n : ℕ) :
    {i : ℤ | ¬ IsZero ((koszulPowerComplex X f n).X i)}.Finite := by
  refine (Set.finite_Icc (0 : ℤ) r).subset fun i hi ↦ ?_
  simp only [Set.mem_ofPred_eq] at hi
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · by_contra hlt
    exact hi (isZero_koszulPowerComplex_X_of_neg X f n (by omega))
  · by_contra hlt
    exact hi (isZero_koszulPowerComplex_X_of_lt X f n (by omega))

end Bounded

section Devissage

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : Stacks.SheafOfModules.DerivedTensorProduct X)
  (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- **Invertibility of `Φ` is transported along the identification `L⟦a⟧⟦b⟧ ≅ L⟦a + b⟧`.**  This
is the only reindexing the shift-closed dévissage below needs, and it is `Mathlib`'s
`CategoryTheory.shiftFunctorAdd` fed to the closure under isomorphism. -/
theorem isIso_derivedTensorDualToSheafHom_shift_shift
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (a b : ℤ)
    (h : IsIso (derivedTensorDualToSheafHom X T (L⟦a + b⟧) M)) :
    IsIso (derivedTensorDualToSheafHom X T ((L⟦a⟧)⟦b⟧) M) :=
  isIso_derivedTensorDualToSheafHom_of_iso X T
    ((CategoryTheory.shiftFunctorAdd _ a b).app L).symm M h

/-- **The dévissage step of Stacks 08JJ at the second vertex of a distinguished triangle, for
the shift-closed class.**  Given a distinguished triangle `L₁ ⟶ L₂ ⟶ L₃ ⟶ L₁⟦1⟧` of `D(𝒪)` and
the invertibility of `Φ` at **every shift** of `L₁` and of `L₃`, the canonical map is invertible
at every shift of `L₂`.

This is the form of the two-out-of-three closure that makes
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_shift` — and hence
`CategoryTheory.NatTrans.CommShift` for the canonical map of Stacks 08JD — **unnecessary**.  The
triangle step of `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_distTriang`
needs the invertibility of `Φ` at the shifts by `-1` of its second and third vertices as well as
at the vertices themselves, and in the unstrengthened form those shifts could only come from the
closure under the shift; here they are instances of the hypotheses.  The shift by `n` is paid for
by shifting the *triangle*, which is again distinguished by
`CategoryTheory.Pretriangulated.Triangle.shift_distinguished`, and not by shifting `Φ`.

The orientation is the one the induction on the stupid filtration of a bounded complex consumes:
it supplies the first and third vertices and asks for the second, which is the first vertex of
one rotation, `CategoryTheory.Pretriangulated.rot_of_distTriang`. -/
theorem isIso_derivedTensorDualToSheafHom_shift_obj₂_of_distTriang
    (Tri : Triangle
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hTri : Tri ∈ distTriang
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (h₁ : ∀ n : ℤ, IsIso (derivedTensorDualToSheafHom X T (Tri.obj₁⟦n⟧) M))
    (h₃ : ∀ n : ℤ, IsIso (derivedTensorDualToSheafHom X T (Tri.obj₃⟦n⟧) M)) (n : ℤ) :
    IsIso (derivedTensorDualToSheafHom X T (Tri.obj₂⟦n⟧) M) :=
  isIso_derivedTensorDualToSheafHom_of_distTriang X T M
    ((CategoryTheory.shiftFunctor
      (Triangle (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
        n).obj Tri).rotate
    (rot_of_distTriang _ (Triangle.shift_distinguished Tri hTri n))
    (h₃ n)
    (isIso_derivedTensorDualToSheafHom_shift_shift X T M Tri.obj₁ n 1 (h₁ (n + 1)))
    (isIso_derivedTensorDualToSheafHom_shift_shift X T M Tri.obj₃ n (-1) (h₃ (n + -1)))
    (isIso_derivedTensorDualToSheafHom_of_iso X T
      ((CategoryTheory.shiftFunctorCompIsoId _ (1 : ℤ) (-1 : ℤ) (by omega)).app
        (Tri.obj₁⟦n⟧)) M (h₁ n))

/-- **The canonical map of Stacks 08JD is invertible at the structure sheaf placed in an
arbitrary degree.** The structure sheaf in degree `p` is the shift by `-p` of the structure
sheaf in degree `0`, by the shift isomorphism of the family of single functors, so this is
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_shiftedStructureSheaf`.

That statement is proved *directly*, with the shift absorbed by the source complex rather than
by `Φ`; it is what replaces the closure of the class under the shift here, and hence what makes
everything below free of `CategoryTheory.NatTrans.CommShift (derivedTensorDualNatTrans X T M) ℤ`
— an instance which does not follow from the fields of the derived tensor product datum of
Stacks 06YU as they stand. -/
theorem isIso_derivedTensorDualToSheafHom_singleFunctor_unit (p : ℤ) :
    IsIso (derivedTensorDualToSheafHom X T
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) p).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) M) :=
  isIso_derivedTensorDualToSheafHom_of_iso X T
    (((DerivedCategory.singleFunctors
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).shiftIso
      (-p) p 0 (by omega)).app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).symm M
    (isIso_derivedTensorDualToSheafHom_shiftedStructureSheaf X T M (-p))

/-- **The canonical map of Stacks 08JD is invertible at a finite product of copies of the
structure sheaf placed in an arbitrary degree.** This is the term step of the dévissage at the
Koszul complexes, whose degree-`p` term is such a product.

A finite product in the sheaves of `𝒪`-modules is a finite biproduct, and the single functor is
additive, so the decomposition `∑ k, π k ≫ ι k = 𝟙` of the identity of the biproduct is carried
to a decomposition of the identity of its image; that is exactly the hypothesis of
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_sum_id`, whose terms are
handled by `isIso_derivedTensorDualToSheafHom_singleFunctor_unit`. -/
theorem isIso_derivedTensorDualToSheafHom_singleFunctor_pi_unit {ι : Type} [Finite ι] (p : ℤ) :
    IsIso (derivedTensorDualToSheafHom X T
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) p).obj
        (∏ᶜ fun _ : ι ↦ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) M) := by
  let : HasFiniteBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let := Fintype.ofFinite ι
  let F := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) p
  let U : ι → SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
    fun _ ↦ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  refine isIso_derivedTensorDualToSheafHom_of_iso X T (F.mapIso (biproduct.isoProduct U).symm) M ?_
  refine isIso_derivedTensorDualToSheafHom_of_sum_id X T Finset.univ
    (fun k ↦ F.map (biproduct.ι U k)) (fun k ↦ F.map (biproduct.π U k)) ?_ M
    (fun _ ↦ isIso_derivedTensorDualToSheafHom_singleFunctor_unit X T M p)
  simp only [← F.map_comp, ← F.map_sum, biproduct.total, F.map_id]

/-- **The canonical map of Stacks 08JD is invertible at every shift of a finite product of
copies of the structure sheaf placed in an arbitrary degree.**  A shift of the structure sheaf
placed in a degree is the structure sheaf placed in another degree, by the shift isomorphism of
the family of single functors, so this is
`isIso_derivedTensorDualToSheafHom_singleFunctor_pi_unit` at the shifted degree.  It is the term
step of the shift-closed dévissage. -/
theorem isIso_derivedTensorDualToSheafHom_shift_singleFunctor_pi_unit
    {ι : Type} [Finite ι] (p n : ℤ) :
    IsIso (derivedTensorDualToSheafHom X T
      (((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) p).obj
        (∏ᶜ fun _ : ι ↦ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))⟦n⟧) M) :=
  isIso_derivedTensorDualToSheafHom_of_iso X T
    (((DerivedCategory.singleFunctors
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).shiftIso n (p - n) p
      (by omega)).app
      (∏ᶜ fun _ : ι ↦ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) M
    (isIso_derivedTensorDualToSheafHom_singleFunctor_pi_unit X T M (p - n))

variable {r : ℕ} (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **Clause 3 of [Stacks, Tag 08JJ] at the Koszul complexes**: the canonical map
`K ⊗^𝐋_𝒪 L^∨ ⟶ R𝑆heafHom_𝒪(L, K)` of [Stacks, Tag 08JD] is invertible at
`L = K(𝒪, f_1^{n+1}, …, f_r^{n+1})`.

The Koszul complex is bounded, by
`AlgebraicGeometry.RingedSite.finite_support_koszulPowerComplex`, and its term in degree `p` is
the product of copies of `𝒪` indexed by the subsets of `Fin r` of cardinality `p`; so the
induction on its stupid filtration reduces the statement to
`isIso_derivedTensorDualToSheafHom_singleFunctor_pi_unit`, the extension step being
`isIso_derivedTensorDualToSheafHom_obj₂_of_distTriang` and the invariance under isomorphism and
the vanishing case being the unconditional dévissage steps of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualDevissage`. -/
theorem isIso_derivedTensorDualToSheafHom_koszulPowerComplex (n : ℕ) :
    IsIso (derivedTensorDualToSheafHom X T
      (DerivedCategory.Q.obj (koszulPowerComplex X f n)) M) := by
  have key : ∀ m : ℤ, IsIso (derivedTensorDualToSheafHom X T
      ((DerivedCategory.Q.obj (koszulPowerComplex X f n))⟦m⟧) M) := by
    refine Stacks.DerivedCategory.BoundedInduction.property_of_bounded_complex_of_distTriang
      (fun A ↦ ∀ m : ℤ, IsIso (derivedTensorDualToSheafHom X T (A⟦m⟧) M))
      (fun e h m ↦ isIso_derivedTensorDualToSheafHom_of_iso X T
        ((CategoryTheory.shiftFunctor _ m).mapIso e).symm M (h m))
      (fun _ hA m ↦ isIso_derivedTensorDualToSheafHom_of_isZero X T
        (Functor.map_isZero (CategoryTheory.shiftFunctor _ m) hA) M)
      (fun Tri hTri h₁ h₃ ↦
        isIso_derivedTensorDualToSheafHom_shift_obj₂_of_distTriang X T M Tri hTri h₁ h₃)
      (koszulPowerComplex X f n) (finite_support_koszulPowerComplex X f n) fun p m ↦ ?_
    exact isIso_derivedTensorDualToSheafHom_shift_singleFunctor_pi_unit X T M
      (ι := AlternatingCech.Idx r p) p m
  exact isIso_derivedTensorDualToSheafHom_of_iso X T
    ((CategoryTheory.shiftFunctorZero _ ℤ).app
      (DerivedCategory.Q.obj (koszulPowerComplex X f n))).symm M (key 0)

/-- **The input `hdual` of the formula of [Stacks, Tag 0A0E] for the Koszul system.** The
canonical map of [Stacks, Tag 08JD] is invertible at every member of the sequential diagram
`AlgebraicGeometry.RingedSite.koszulPowerSystem` of Koszul complexes, read in `D(𝒪)`.

This is `isIso_derivedTensorDualToSheafHom_koszulPowerComplex` at each index, the member of the
diagram at `n` being the Koszul complex on the `(n+1)`-st powers. It is the hypothesis `hdual`
of `AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem`, which
is how it enters the formula of [Stacks, Tag 0A0E]. -/
theorem isIso_derivedTensorDualToSheafHom_koszulPowerSystem (n : ℕ) :
    IsIso (derivedTensorDualToSheafHom X T
      ((koszulPowerSystem X f ⋙ DerivedCategory.Q).obj n) M) :=
  isIso_derivedTensorDualToSheafHom_koszulPowerComplex X T M f n

end Devissage

end AlgebraicGeometry.RingedSite

end
