module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomTriangulated
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSheafHomContravariantCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomFiniteFree
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory

/-!
# The derived internal Hom out of a strictly perfect complex preserves `D_B`

Let `(C, O)` be a ringed site, `B` a weak Serre subcategory of the category of `O`-modules
(Stacks 02MO) and `L` an object of `D(O)` all of whose cohomology sheaves lie in `B`.  For a
strictly perfect complex `P` (Stacks 08FL) every cohomology sheaf of `RSheafHom(P, L)` lies in
`B` again.

The proof is the stupid filtration of `P`, as in Stacks 08JH: a degreewise split short exact
sequence of complexes gives a distinguished triangle of derived internal Homs (Stacks 08JC in
the contravariant variable), and the objects of `D(O)` with cohomology in `B` form a
triangulated subcategory (Stacks 06UQ), stable under retracts; a complex concentrated in one
degree with value a direct summand of a finite free module is a retract of one with value
`O^{⊕r}`, which is an extension of copies of `O`; and `RSheafHom(O[-k], L) = L[k]`.

This is the local input of the coherence of `RSheafHom(K, L)` for `K` perfect and `L` with
coherent cohomology, used in the proof of Stacks 0D0T.

## Main results

* `AlgebraicGeometry.RingedSite.derivedCategoryB_derivedSheafHom_of_bounded`: the statement for a
  complex vanishing outside a window, with terms direct summands of finite free modules.
* `AlgebraicGeometry.RingedSite.derivedCategoryB_derivedSheafHom_of_isStrictlyPerfect`: the
  statement for a strictly perfect complex.

## References

* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0D0S](https://stacks.math.columbia.edu/tag/0D0S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u}) [HasSheafify X.J AddCommGrpCat.{u}]
  (Bp : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  (hB : WeakSerre.IsWeakSerre Bp)
  (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- The class of complexes `E` such that `RSheafHom(E, L)` has its cohomology in `B`. -/
abbrev DerivedHomInB
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    Prop :=
  DerivedCategoryB.derivedCategoryB Bp
    (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj E))).obj L)

omit [HasSheafify X.J AddCommGrpCat.{u}] in
include hB in
/-- A zero complex is in the class. -/
theorem derivedHomInB_of_isZero
    {E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hE : IsZero E) : DerivedHomInB X Bp L E := fun n =>
  DerivedCategoryB.zero_mem_of_isWeakSerre Bp hB _
    ((DerivedCategory.homologyFunctor _ n).map_isZero
      (((derivedSheafHomBifunctor X).flip.obj L).map_isZero
        (DerivedCategory.Q.map_isZero hE).op))

omit [HasSheafify X.J AddCommGrpCat.{u}] in
include hB in
/-- The class is closed under retracts. -/
theorem derivedHomInB_of_retract
    {E E' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (h : Retract E E') (hE' : DerivedHomInB X Bp L E') : DerivedHomInB X Bp L E :=
  have := DerivedCategoryB.derivedCategoryB_isStableUnderRetracts Bp hB
  ObjectProperty.prop_of_retract (DerivedCategoryB.derivedCategoryB Bp)
    ((h.map DerivedCategory.Q).op.map ((derivedSheafHomBifunctor X).flip.obj L)) hE'

include hB in
/-- The class satisfies two out of three for a degreewise split short exact sequence: the middle
term is in the class when the outer ones are. -/
theorem derivedHomInB_of_degreewiseSplit
    (S : ShortComplex (CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (hS : ∀ n, Nonempty ((S.map (HomologicalComplex.eval
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) n)).Splitting))
    (h₁ : DerivedHomInB X Bp L S.X₁) (h₃ : DerivedHomInB X Bp L S.X₃) :
    DerivedHomInB X Bp L S.X₂ := by
  obtain ⟨δ, hδ⟩ := exists_distinguished_derivedSheafHom_of_ses_obj X S hS L
  exact DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished Bp hB _ hδ h₃ h₁

/-- Sheaves of modules on a ringed site have finite biproducts, being abelian. -/
local instance hasFiniteBiproducts_sheafOfModules' :
    HasFiniteBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

include hB in
/-- **The structure sheaf placed in one degree.** `RSheafHom(O[-k], L) = L[k]`, whose cohomology
lies in `B` when that of `L` does. -/
theorem derivedHomInB_single_unit (hL : DerivedCategoryB.derivedCategoryB Bp L) (k : ℤ) :
    DerivedHomInB X Bp L ((HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) := by
  let O := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let e₁ : (derivedStructureSheaf X)⟦-k⟧ ≅ DerivedCategory.Q.obj ((HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k).obj
        O) :=
    (CategoryTheory.shiftFunctor _ (-k)).mapIso
        (eqToIso (derivedStructureSheaf_eq_singleFunctor_obj X)) ≪≫
      ((DerivedCategory.singleFunctors _).shiftIso (-k) k 0 (by omega)).app O ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ k).app O
  let e : ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj ((HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k).obj
        O)))).obj L ≅ L⟦k⟧ :=
    ((derivedSheafHomBifunctor X).mapIso e₁.op).app L ≪≫
      derivedSheafHomSourceShiftIso' X (derivedStructureSheaf X) L (-k) k (by omega) ≪≫
      (CategoryTheory.shiftFunctor _ k).mapIso (derivedStructureSheafHomIso X L)
  exact (DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms Bp hB).of_iso e.symm
    (DerivedCategoryB.derivedCategoryB_shift_mem Bp hB k hL)

include hB in
/-- **A power of the structure sheaf placed in one degree.** -/
theorem derivedHomInB_single_unitPower (hL : DerivedCategoryB.derivedCategoryB Bp L) (k : ℤ)
    (r : ℕ) :
    DerivedHomInB X Bp L ((HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k).obj
        (unitPower X r)) := by
  let Sg := HomologicalComplex.single
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k
  induction r with
  | zero =>
    rw [unitPower_zero]
    exact derivedHomInB_of_isZero X Bp hB L (Sg.map_isZero (isZero_zero _))
  | succ r ih =>
    rw [unitPower_succ]
    let T := (unitPowerShortComplex X r).map Sg
    have hT (p : ℤ) : Nonempty ((T.map (HomologicalComplex.eval _ _ p)).Splitting) :=
      ⟨((ShortComplex.Splitting.ofHasBinaryBiproduct (unitPower X r)
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).map Sg).map _⟩
    exact derivedHomInB_of_degreewiseSplit X Bp hB L T hT ih
      (derivedHomInB_single_unit X Bp hB L hL k)

include hB in
/-- **A direct summand of a finite free module placed in one degree.** -/
theorem derivedHomInB_single_of_isFiniteFreeSummand
    (hL : DerivedCategoryB.derivedCategoryB Bp L) (k : ℤ)
    {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hM : IsFiniteFreeSummand X M) :
    DerivedHomInB X Bp L ((HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k).obj
        M) := by
  obtain ⟨r, ⟨ρ⟩⟩ := hM
  exact derivedHomInB_of_retract X Bp hB L
    (ρ.map (HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k))
    (derivedHomInB_single_unitPower X Bp hB L hL k r)

include hB in
/-- **The bounded case.** If `E` vanishes outside the window `[a, a + r)` and each of its terms
is a direct summand of a finite free `O`-module, then `RSheafHom(E, L)` has its cohomology in
`B`. -/
theorem derivedCategoryB_derivedSheafHom_of_bounded
    (hL : DerivedCategoryB.derivedCategoryB Bp L) (r : ℕ) (a : ℤ)
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hlo : ∀ i, i < a → IsZero (E.X i)) (hhi : ∀ i, a + r ≤ i → IsZero (E.X i))
    (hterm : ∀ i, IsFiniteFreeSummand X (E.X i)) : DerivedHomInB X Bp L E := by
  induction r generalizing a E with
  | zero =>
    refine derivedHomInB_of_isZero X Bp hB L (complex_isZero_of_terms E fun i => ?_)
    by_cases hi : i < a
    · exact hlo i hi
    · exact hhi i (by push_cast; omega)
  | succ r ih =>
    have ha : IsZero (E.X (a - 1)) := hlo (a - 1) (by omega)
    set p := bottomProjection E a ha
    set K := kernel p
    have hz : IsZero (K.X a) := isZero_kernel_bottomProjection_X_self E a ha
    have hiso (i : ℤ) (hi : i ≠ a) : K.X i ≅ E.X i :=
      haveI := isIso_kernel_ι_bottomProjection_f E a ha i hi
      asIso ((kernel.ι p).f i)
    have hKterm (i : ℤ) : IsFiniteFreeSummand X (K.X i) := by
      by_cases hi : i = a
      · subst i
        exact IsFiniteFreeSummand.of_isZero X hz
      · exact IsFiniteFreeSummand.of_iso X (hiso i hi) (hterm i)
    have hKlo (i : ℤ) (hi : i < a + 1) : IsZero (K.X i) := by
      by_cases hia : i = a
      · subst i
        exact hz
      · exact IsZero.of_iso (hlo i (by omega)) (hiso i hia)
    have hKhi (i : ℤ) (hi : a + 1 + r ≤ i) : IsZero (K.X i) :=
      IsZero.of_iso (hhi i (by push_cast; omega)) (hiso i (by omega))
    let T := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    refine derivedHomInB_of_degreewiseSplit X Bp hB L T (fun i => ⟨?_⟩)
      (ih (a + 1) K hKlo hKhi hKterm)
      (derivedHomInB_single_of_isFiniteFreeSummand X Bp hB L hL a (hterm a))
    by_cases hi : i = a
    · subst i
      exact ShortComplex.Splitting.ofIsZeroOfIsIso _ hz (isIso_bottomProjection_f_self E a ha)
    · exact ShortComplex.Splitting.ofIsIsoOfIsZero _ (isIso_kernel_ι_bottomProjection_f E a ha i hi)
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (E.X a) i hi)

include hB in
/-- **The derived internal Hom out of a strictly perfect complex preserves `D_B`.**  If every
cohomology sheaf of `L` lies in the weak Serre subcategory `B` and `P` is strictly perfect
(Stacks 08FL), then every cohomology sheaf of `RSheafHom(P, L)` lies in `B`. -/
theorem derivedCategoryB_derivedSheafHom_of_isStrictlyPerfect
    [X.J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    (hL : DerivedCategoryB.derivedCategoryB Bp L)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P) :
    DerivedHomInB X Bp L P := by
  obtain ⟨a, ha⟩ := hP.bounded.bddBelow
  obtain ⟨b, hb⟩ := hP.bounded.bddAbove
  refine derivedCategoryB_derivedSheafHom_of_bounded X Bp hB L hL (b - a + 1).toNat a P ?_ ?_
    (fun i => IsDirectSummandOfFiniteFree.isFiniteFreeSummand X (hP.termDirectSummand i))
  · intro i hi
    by_contra hz
    have := ha hz
    omega
  · intro i hi
    by_contra hz
    have := hb hz
    omega

end AlgebraicGeometry.RingedSite

end
