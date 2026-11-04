module

public import Mathlib
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.InverseLimit
public import StacksFrontier.CategoryTheory.EssentiallyConstant.Defs
public import StacksFrontier.CategoryTheory.EssentiallyConstant.ProObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.OlssonLaszloSituation
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MittagLeffler
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Rlim

/-!
# Injectivity of the projection from a derived limit onto an eventual term

Let `K` be an inverse system indexed by `ℕᵒᵖ` in a pretriangulated category, and let `L` be a
derived limit of `K`, presented by the defining distinguished triangle
```
L ⟶ ∏ₙ Kₙ ⟶ ∏ₙ Kₙ ⟶ L[1]
```
whose second map is the usual difference `(xₙ) ↦ (xₙ - xₙ₊₁)`.  Suppose a cohomological functor
with values in abelian groups turns the transition maps of `K` into isomorphisms from some index
`N` on, in the two degrees `m - 1` and `m`.  Then that functor sends the projection `L ⟶ K_N` to
a monomorphism in degree `m`.

This is the engine behind the convergence statements for towers of truncations: Stacks 0D61 and
0D6L deduce it from the Milnor short exact sequence, and Stacks 0D62 and 0D6M use it to compare
an object of a derived category with the derived limit of its truncations from below.  The form
proved here takes neither the Milnor sequence nor the sheaf-theoretic input: it needs only the
long exact cohomology sequence of the defining triangle and the vanishing of `R¹lim` for an
eventually constant tower of abelian groups.

## Main results

* `isZero_cokernel_difference_of_eventually_iso`: the cokernel of the difference endomorphism of
  the product of an eventually constant tower of abelian groups vanishes, i.e. `R¹lim` vanishes.
* `Stacks.Cohomology.mono_projection_of_difference`: a functor preserving the product carries the
  projection onto an eventual term to a monomorphism, once it is a monomorphism on the derived
  limit and on the transition maps.
* `mono_homology_projection_of_eventually_iso`: the statement described above.

## Implementation notes

The vanishing of `R¹lim` is obtained from `Rlim.isMittagLeffler_iff_isZero_rightDerivedLim_one`
via the eventually constant pro-object machinery, rather than by exhibiting surjectivity of the
difference map by hand; the cokernel description
`Rlim.firstDerivedLimit_iso_cokernel_of_isRightDerivedFunctor` transports the conclusion back to
the explicit cokernel that the defining triangle uses.

The product occurring in the defining triangle is an honest categorical product, and the
functor is only assumed to preserve *that* product, as a limit over `Discrete ℕ`; this is what a
tower of K-injective representatives supplies in the intended applications.

## References

* [Stacks Project, Tag 0D61](https://stacks.math.columbia.edu/tag/0D61)
* [Stacks Project, Tag 0D6L](https://stacks.math.columbia.edu/tag/0D6L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w

/-- Transition maps of a tower which are invertible from `N` on are invertible between any two
indices beyond `N`. -/
public lemma isIso_map_to_of_successive_isIso {D : Type*} [Category* D] (F : ℕᵒᵖ ⥤ D) (N : ℕ)
    (h : ∀ n, N ≤ n → IsIso (F.map (homOfLE (Nat.le_succ n)).op))
    (n : ℕ) (hn : N ≤ n) : IsIso (F.map (homOfLE hn).op) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [show (homOfLE (le_refl N)).op = 𝟙 (Opposite.op N) from Subsingleton.elim _ _, F.map_id]
    infer_instance
  | succ n hn ih =>
    have := h n hn
    rw [show (homOfLE (Nat.le_succ_of_le hn)).op =
      (homOfLE (Nat.le_succ n)).op ≫ (homOfLE hn).op from Subsingleton.elim _ _, F.map_comp]
    infer_instance

/-- An eventually constant tower of abelian groups has vanishing first derived inverse limit. -/
public lemma isZero_firstDerivedLimit_of_eventually_iso
    (F : ℕᵒᵖ ⥤ AddCommGrpCat.{w}) (N : ℕ)
    (h : ∀ n, N ≤ n → IsIso (F.map (homOfLE (Nat.le_succ n)).op)) :
    IsZero (Rlim.firstDerivedLimit F) := by
  have : HasDerivedCategory Ab.{w} := HasDerivedCategory.standard _
  have : HasDerivedCategory Rlim.InvSystemAb.{w} := HasDerivedCategory.standard _
  have : (lim : Rlim.InvSystemAb.{w} ⥤ Ab.{w}).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hto : F.IsEventuallyConstantTo (Opposite.op N) := by
    intro i f
    have hi := isIso_map_to_of_successive_isIso F N h i.unop (leOfHom f.unop)
    convert hi using 1
    exact congrArg F.map (Subsingleton.elim _ _)
  have hpro : CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantPro F :=
    (CategoryTheory.EssentiallyConstantPro.isEssentiallyConstantPro_iff_op F).mpr
      (CategoryTheory.isEssentiallyConstantInverseSystem_of_isEventuallyConstantTo hto)
  have hML : (F ⋙ forget Ab.{w}).IsMittagLeffler :=
    isMittagLeffler_of_isEssentiallyConstantPro F hpro
  obtain ⟨RF, α, hRF, _⟩ := Rlim.lim_hasRightDerivedFunctor_and_computations.{w}
  have hlim :=
    (Rlim.isMittagLeffler_iff_isZero_rightDerivedLim_one_and_countable_coproduct
      F RF α hRF).mp hML
  obtain ⟨e⟩ := Rlim.firstDerivedLimit_iso_cokernel_of_isRightDerivedFunctor RF α hRF F
  exact hlim.1.of_iso e.symm

/-- The explicit form of the previous lemma: the cokernel of the difference endomorphism
`(xₙ) ↦ (xₙ - xₙ₊₁)` of the product of an eventually constant tower vanishes. -/
public lemma isZero_cokernel_difference_of_eventually_iso
    (F : ℕᵒᵖ ⥤ AddCommGrpCat.{w}) (N : ℕ)
    (h : ∀ n, N ≤ n → IsIso (F.map (homOfLE (Nat.le_succ n)).op)) :
    IsZero (cokernel (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op)) := by
  have hz := isZero_firstDerivedLimit_of_eventually_iso F N h
  have hd : Rlim.delta F = Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op := by
    apply Pi.hom_ext
    intro n
    rw [Rlim.delta_comp_π, Pi.lift_π]
  rw [← hd]
  exact hz




/-- From the long exact cohomology sequence of a distinguished triangle: if an exact functor is
epimorphic on `H^{m-1}` of the second map, it is monomorphic on `H^m` of the first. -/
public theorem mono_homology_eval_of_epi {A B : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] [Category* B]
    [Abelian B] (E : A ⥤ B) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang _) (m : ℤ)
    [Epi (E.map ((DerivedCategory.homologyFunctor A (m - 1)).map T.mor₂))] :
    Mono (E.map ((DerivedCategory.homologyFunctor A m).map T.mor₁)) := by
  have hd : E.map (DerivedCategory.HomologySequence.δ T (m - 1) m (by omega)) = 0 := by
    apply (cancel_epi (E.map ((DerivedCategory.homologyFunctor A (m - 1)).map T.mor₂))).1
    rw [← E.map_comp, DerivedCategory.HomologySequence.comp_δ T hT (m - 1) m (by omega),
      E.map_zero, comp_zero]
  have he := (DerivedCategory.HomologySequence.exact₁ T hT (m - 1) m (by omega)).map E
  exact (ShortComplex.exact_iff_mono _ hd).1 he

/-- From the long exact cohomology sequence: if an exact functor kills `H^m` and `H^{m+1}` of the
first vertex of a distinguished triangle, it inverts `H^m` of the second map. -/
public lemma isIso_homology_eval_of_isZero {A B : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] [Category* B]
    [Abelian B] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang _) (m : ℤ)
    (h₀ : IsZero (F.obj ((DerivedCategory.homologyFunctor A m).obj T.obj₁)))
    (h₁ : IsZero (F.obj ((DerivedCategory.homologyFunctor A (m + 1)).obj T.obj₁))) :
    IsIso (F.map ((DerivedCategory.homologyFunctor A m).map T.mor₂)) := by
  have : Mono (F.map ((DerivedCategory.homologyFunctor A m).map T.mor₂)) :=
    (ShortComplex.exact_iff_mono _ (h₀.eq_of_src _ _)).1
      ((DerivedCategory.HomologySequence.exact₂ T hT m).map F)
  have : Epi (F.map ((DerivedCategory.homologyFunctor A m).map T.mor₂)) :=
    (ShortComplex.exact_iff_epi _ (h₁.eq_of_tgt _ _)).1
      ((DerivedCategory.HomologySequence.exact₃ T hT m (m + 1)).map F)
  exact isIso_of_mono_of_epi _

/-- **The local injectivity criterion for a derived limit.**  Let `L` be a derived limit of a
tower `K`, presented by its defining distinguished triangle.  If a triangulated functor `R` to a
derived category, followed by `H^r` and an exact functor `F` to abelian groups, preserves the
product of the tower and inverts all transition maps beyond `N` in the degrees `m - 1` and `m`,
then it is monomorphic in degree `m` on the projection `L ⟶ K_N`. -/
public lemma mono_homology_projection_of_eventually_iso {D A : Type*} [Category* D]
    [Preadditive D] [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [Category* A] [Abelian A] [HasDerivedCategory A]
    (R : D ⥤ DerivedCategory A) [R.CommShift ℤ] [R.IsTriangulated]
    (F : A ⥤ AddCommGrpCat.{w}) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    {L : D} (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫ K.map (homOfLE (Nat.le_succ n)).op) δ ∈
      distTriang D)
    (m : ℤ) (N : ℕ)
    (hpres : ∀ r : ℤ, m - 1 ≤ r → r ≤ m →
      PreservesLimit (Discrete.functor (fun n : ℕ ↦ K.obj ⟨n⟩))
        (R ⋙ DerivedCategory.homologyFunctor A r ⋙ F))
    (hiso : ∀ r : ℤ, m - 1 ≤ r → r ≤ m → ∀ n : ℕ, N ≤ n →
      IsIso ((R ⋙ DerivedCategory.homologyFunctor A r ⋙ F).map
        (K.map (homOfLE (Nat.le_succ n)).op))) :
    Mono ((R ⋙ DerivedCategory.homologyFunctor A m ⋙ F).map (p ≫ Pi.π _ N)) := by
  let T := Triangle.mk p (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
    Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫ K.map (homOfLE (Nat.le_succ n)).op) δ
  let H₀ := R ⋙ DerivedCategory.homologyFunctor A (m - 1) ⋙ F
  let H₁ := R ⋙ DerivedCategory.homologyFunctor A m ⋙ F
  have : PreservesLimit (Discrete.functor (fun n : ℕ ↦ K.obj ⟨n⟩)) H₀ :=
    hpres _ (by omega) (by omega)
  have : PreservesLimit (Discrete.functor (fun n : ℕ ↦ K.obj ⟨n⟩)) H₁ :=
    hpres _ (by omega) (by omega)
  have hz := isZero_cokernel_difference_of_eventually_iso (K ⋙ H₀) N (hiso _ (by omega) (by omega))
  have hep : Epi (H₀.map T.mor₂) := Stacks.Cohomology.epi_map_difference K H₀ hz
  have : Epi (F.map ((DerivedCategory.homologyFunctor A (m - 1)).map
      (R.mapTriangle.obj T).mor₂)) := hep
  have hmono : Mono (H₁.map p) :=
    mono_homology_eval_of_epi F (R.mapTriangle.obj T) (R.map_distinguished T hT) m
  apply Stacks.Cohomology.mono_projection_of_difference K p (comp_distTriang_mor_zero₁₂ T hT) H₁ N
  intro n hn
  have : IsIso (H₁.map (K.map (homOfLE hn).op)) :=
    isIso_map_to_of_successive_isIso (K ⋙ H₁) N (hiso _ (by omega) (by omega)) n hn
  infer_instance

end
