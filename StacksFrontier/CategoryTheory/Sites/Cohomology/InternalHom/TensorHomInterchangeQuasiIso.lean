module

public import StacksFrontier.Algebra.Homology.ReindexCochainComplex
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.InternalHomUnitSource
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.Bifunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DiagonalMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomQuasiIso

/-!
# Towards the invertibility of the interchange morphism of Stacks 0BYR

Let `X` be a ringed site and let `A`, `I`, `N` be complexes of `O`-modules. The interchange
morphism of Stacks 0BYR

`Tot(A ⊗_O SheafHom(N, I)) ⟶ SheafHom(N, Tot(A ⊗_O I))`

is expected to be a quasi-isomorphism as soon as one of `A` and `N` is strictly perfect —
bounded, with every term a direct summand of a finite free `O`-module. That is the formal
content of the step the source of Stacks 0ATN calls clear, and the module constructing the
interchange morphism proves nothing about its invertibility.

This file is the first part of that argument, in the variable `N`: the structural lemmas which
let the strictly perfect case be reached by the same induction that
`AlgebraicGeometry.RingedSite.homMap_quasiIso_of_isFiniteFreeSummand` uses for the induced map
of internal Hom complexes. The interchange morphism is contravariantly functorial in `N`, so it
is an object of the arrow category depending functorially on `N`, and quasi-isomorphy then
passes to retracts of `N` for free.

Along the way the functoriality of `tensorTotalMap` in both arguments at once is recorded. It
was available on a ringed space (`Stacks.SheafOfModules.tensorTotalMap_comp`) but not on a
ringed site, and `Mathlib`'s `HomologicalComplex.mapBifunctorMap`, which `tensorTotalMap`
unfolds to, carries only its characterisation on the summand inclusions and no composition
lemma.

## Main definitions

* `AlgebraicGeometry.RingedSite.interchangeArrowFunctor`: the interchange morphism of
  Stacks 0BYR as a functor from the opposite category of complexes — the source of the internal
  Hom — to the arrow category.
* `AlgebraicGeometry.RingedSite.homUnitReindexIso`: the internal Hom complex out of a source
  concentrated in one degree `k` and trivialised there is the target reindexed by `k`, as an
  isomorphism of complexes.

## Main results

* `AlgebraicGeometry.RingedSite.tensorTotalMap_comp`: the total tensor-product morphism is
  functorial in both arguments at once.
* `AlgebraicGeometry.RingedSite.tensorHomInterchange_quasiIso_of_retract`: if the interchange
  morphism is a quasi-isomorphism at `N'` then it is one at any retract of `N'`.
* `AlgebraicGeometry.RingedSite.isIso_tensorTotalMap`: the total tensor-product morphism of two
  isomorphisms is an isomorphism.
* `AlgebraicGeometry.RingedSite.tensorTotal_isZero_of_isZero_right`: the total tensor product
  with a zero factor vanishes.
* `AlgebraicGeometry.RingedSite.tensorHomInterchange_quasiIso_of_isZero`: the interchange
  morphism is a quasi-isomorphism when the source of the internal Hom vanishes — the base case
  of the induction.
* `AlgebraicGeometry.RingedSite.exists_retract_single_of_isFiniteFreeSummand` and
  `AlgebraicGeometry.RingedSite.tensorHomInterchange_quasiIso_single_of_isFiniteFreeSummand`:
  the single-degree finite-free-summand case reduced to the single-degree finite free case.

## What this file does not contain

**The strictly perfect case itself.** What remains, following
`StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomQuasiIso` step
for step, is:

* the single-degree case, `N` concentrated in one degree and isomorphic there to a power of the
  structure sheaf. The reduction of a finite-free *summand* to a finite free one is done above;
  what is missing is the finite free case itself. The complex-level identification it needs is
  `homUnitReindexIso` above, so applying it to both complexes of the interchange — on the source
  through `isIso_tensorTotalMap` — presents the interchange as conjugate to a morphism
  `Tot(A ⊗_O reindexBy I k) ⟶ reindexBy (Tot(A ⊗_O I)) k`. Two things are then left: the
  canonical isomorphism between those two complexes, which is a **sign-free reindexing
  compatibility of the total complex in its second variable** — both sides are the same
  coproduct, indexed by `p + q = n` on the left and `p + q' = k + n` on the right, so the
  comparison is a reindexing of the summands along `q' = k + q`, for which
  `StacksDraft.TotalComplexQuasiIso.ιTotal_congr₂` is the kind of tool required; and the check
  on sections that the conjugated interchange is that isomorphism, for which
  `tensorHomInterchange_applyHomSectionOver` pins the interchange and
  `homUnitEvaluation` must be unfolded, which is possible only because its file is `@[expose]`
  and states no section formula of its own;
* a degreewise splitting of the short complex `Tot(A ⊗_O SheafHom(-, I))` obtained from a
  degreewise split short complex in `N`. This is the one step with no counterpart in the model
  file: there the corresponding row is a *product* over the degrees of the Hom source and its
  splitting is `internalHomTermwiseSplitting`, whereas here it is the total complex, whose
  degree `n` is a coproduct over `p + q = n`, so the splitting has to be assembled from the
  summands as `StacksDraft.TotalComplexQuasiIso.totalBottomSplitting` does for its own case;
* the two-out-of-three step, which given that splitting is
  `StacksDraft.TotalComplexQuasiIso.quasiIso_τ₂` — stated for an arbitrary abelian category, so
  reusable as it stands — applied to that row and to
  `AlgebraicGeometry.RingedSite.internalHomShortComplex X S (tensorTotal X A I)`, the two being
  joined by `tensorHomInterchange_natural_source`;
* the induction on the number of nonzero terms, as in `homMap_quasiIso_of_bounded`.

## References

* [Stacks Project, Lemma 20.49.10 (Tag 0BYR)](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Lemma 20.49.11 (Tag 0BYT)](https://stacks.math.columbia.edu/tag/0BYT)
* [Stacks Project, Lemma 20.49.5 (Tag 08JH)](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Lemma 36.10.11 (Tag 0ATN)](https://stacks.math.columbia.edu/tag/0ATN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

/-- **The total tensor-product morphism is functorial in both arguments at once.** Both sides
agree on every homogeneous local pure tensor, which determines a morphism out of a total tensor
product. -/
theorem tensorTotalMap_comp
    {A A' A'' B B' B'' :
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : A ⟶ A') (f' : A' ⟶ A'') (g : B ⟶ B') (g' : B' ⟶ B'') :
    tensorTotalMap X f g ≫ tensorTotalMap X f' g' =
      tensorTotalMap X (f ≫ f') (g ≫ g') := by
  refine tensorTotal_hom_ext X fun U t r a b ↦ ?_
  rw [HomologicalComplex.comp_f, comp_val_app_apply', tensorTotalMap_tensorTotalSection,
    tensorTotalMap_tensorTotalSection, tensorTotalMap_tensorTotalSection]
  rfl

/-- **The interchange morphism of Stacks 0BYR as a functor to the arrow category**, in the
source of the internal Hom. The functoriality is the contravariance of Stacks 0BYT in that
variable. -/
def interchangeArrowFunctor
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ ⥤
      Arrow
        (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) where
  obj N := Arrow.mk (tensorHomInterchange X A I N.unop)
  map g := Arrow.homMk
    (tensorTotalMap X (𝟙 A) (homMap X g.unop (𝟙 I)))
    (homMap X g.unop (𝟙 (tensorTotal X A I)))
    ((tensorHomInterchange_natural_source X A I g.unop).symm)
  map_id N := by
    apply Arrow.hom_ext <;>
      simp only [Arrow.homMk_left, Arrow.homMk_right, Arrow.id_left, Arrow.id_right,
        unop_id, homMap_id, tensorTotalMap_id] <;> rfl
  map_comp g h := by
    apply Arrow.hom_ext <;>
      simp only [Arrow.homMk_left, Arrow.homMk_right, Arrow.comp_left, Arrow.comp_right,
        unop_comp, tensorTotalMap_comp, homMap_comp, Category.comp_id]

/-- **The interchange morphism of Stacks 0BYR passes to retracts of the source of the internal
Hom.** This is what reduces a term which is a direct summand of a finite free module to a finite
free one. -/
theorem tensorHomInterchange_quasiIso_of_retract
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {N N' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (ρ : Retract N N') [QuasiIso (tensorHomInterchange X A I N')] :
    QuasiIso (tensorHomInterchange X A I N) :=
  quasiIso_of_retractArrow (ρ.op.map (interchangeArrowFunctor X A I))

/-- **The total tensor-product morphism of two isomorphisms is an isomorphism.** Its inverse is
the total tensor-product morphism of the two inverses, by functoriality. -/
theorem isIso_tensorTotalMap
    {A A' B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : A ⟶ A') (g : B ⟶ B') [IsIso f] [IsIso g] :
    IsIso (tensorTotalMap X f g) := by
  refine ⟨tensorTotalMap X (inv f) (inv g), ?_, ?_⟩ <;>
    simp only [tensorTotalMap_comp, IsIso.hom_inv_id, IsIso.inv_hom_id, tensorTotalMap_id]

/-! ### The vanishing case -/

/-- The homogeneous local pure tensor with the zero section of the second factor vanishes. This
is `tensorTotalSectionAt_zero_right` read in the degree `t + r`. -/
lemma tensorTotalSection_zero_right
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (t r : ℤ)
    (a : (A.X t).val.obj (op U)) :
    tensorTotalSection X A B U t r a 0 = 0 :=
  (tensorTotalSectionAt_self X A B U t r a 0).symm.trans
    (tensorTotalSectionAt_zero_right X U t r (t + r) rfl a)

/-- **The total tensor product with a zero factor vanishes.** The identity of the total complex
is the total tensor-product morphism of the two identities, and the identity of a zero complex
is zero, so the identity vanishes on every homogeneous local pure tensor and therefore
altogether. -/
theorem tensorTotal_isZero_of_isZero_right
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {Z : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hZ : IsZero Z) :
    IsZero (tensorTotal X A Z) := by
  have hid : (𝟙 Z) = (0 : Z ⟶ Z) := hZ.eq_of_src _ _
  rw [IsZero.iff_id_eq_zero, ← tensorTotalMap_id X A Z, hid]
  refine tensorTotal_hom_ext X fun U t r a b ↦ ?_
  rw [tensorTotalMap_tensorTotalSection]
  have hz : ∀ {W W' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
      (x : W.val.obj (op U)),
      (ConcreteCategory.hom ((SheafOfModules.Hom.val (0 : W ⟶ W')).app (op U))) x = 0 :=
    fun x ↦ rfl
  simp only [HomologicalComplex.zero_f, hz, tensorTotalSection_zero_right]

/-- **A zero source of the internal Hom makes the interchange morphism a quasi-isomorphism**, for
trivial reasons: both of its complexes vanish. This is the base case of the induction on the
number of nonzero terms. -/
theorem tensorHomInterchange_quasiIso_of_isZero
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hN : IsZero N) :
    QuasiIso (tensorHomInterchange X A I N) := by
  have h := StacksDraft.TotalComplexQuasiIso.isIso_of_isZero_of_isZero
    (tensorHomInterchange X A I N)
    (tensorTotal_isZero_of_isZero_right X A (sheafHomComplex_isZero_of_isZero X hN I))
    (sheafHomComplex_isZero_of_isZero X hN (tensorTotal X A I))
  infer_instance

/-! ### The internal Hom complex out of a trivialised single-degree source -/

/-- **The internal Hom complex out of a source concentrated in one degree and trivialised there
is the target, reindexed.** The degreewise isomorphisms are
`AlgebraicGeometry.RingedSite.homUnitEvaluationIso`, and they commute with the differentials by
`AlgebraicGeometry.RingedSite.homUnitEvaluation_d`.

That compatibility has no sign in it, which is why the target here is the sign-free reindexing
`CochainComplex.reindexBy F k` and not the shift `F⟦k⟧`. The unit-source development states only
the degreewise isomorphisms; this assembles them into an isomorphism of complexes, which is what
a comparison of two complexes built out of `F` needs. -/
noncomputable def homUnitReindexIso
    {E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : ℤ)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hE : ∀ p, p ≠ k → IsZero (E.X p)) :
    (sheafHomComplex X E F).obj ≅ CochainComplex.reindexBy F k :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => homUnitEvaluationIso X k n e hE)
    (fun i j hij => (homUnitEvaluation_d X k i j (by simpa using hij) e
      ((hE (k + 1) (by omega)).eq_of_tgt _ _)).symm)

/-! ### Reducing a single-degree finite-free summand to a single-degree finite free -/

/-- **A complex concentrated in one degree at a direct summand of a finite free module is a
retract of the one at that finite free module.** A retract is carried to a retract by any
functor, here by the single-degree embedding. -/
theorem exists_retract_single_of_isFiniteFreeSummand (k : ℤ)
    {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hM : IsFiniteFreeSummand X M) :
    ∃ r : ℕ, Nonempty (Retract
      ((HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) k).obj M)
      ((HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) k).obj (unitPower X r))) := by
  obtain ⟨r, ⟨ρ⟩⟩ := hM
  exact ⟨r, ⟨ρ.map (HomologicalComplex.single
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k)⟩⟩

/-- **The single-degree finite-free-summand case follows from the single-degree finite free
case**, by the retract lemma above. The finite free case itself — the interchange morphism at a
source concentrated in one degree and isomorphic there to a power of the structure sheaf — is
taken as a hypothesis, because it is not yet proved; see the section on what this file does not
contain. -/
theorem tensorHomInterchange_quasiIso_single_of_isFiniteFreeSummand
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (k : ℤ) {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hM : IsFiniteFreeSummand X M)
    (h : ∀ r : ℕ, QuasiIso (tensorHomInterchange X A I
      ((HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) k).obj (unitPower X r)))) :
    QuasiIso (tensorHomInterchange X A I
      ((HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) k).obj M)) := by
  obtain ⟨r, ⟨ρ⟩⟩ := exists_retract_single_of_isFiniteFreeSummand X k hM
  have := h r
  exact tensorHomInterchange_quasiIso_of_retract X A I ρ

end AlgebraicGeometry.RingedSite

end
