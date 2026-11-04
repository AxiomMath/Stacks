module

public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.InternalHomUnitSource
import StacksCore.Tactic.StacksAttribute

/-!
# The internal Hom complex out of a strictly perfect source preserves quasi-isomorphisms

Let `(C, O)` be a ringed site, let `E` be a complex of `O`-modules with finitely many nonzero
terms, each of them a direct summand of a finite free `O`-module, and let `f : F ⟶ G` be a
quasi-isomorphism of complexes of `O`-modules. This file proves that the induced morphism

`SheafHom(E, F) ⟶ SheafHom(E, G)`

of internal Hom complexes (Stacks 0A8Z) is again a quasi-isomorphism. That is the content of
Stacks 08JH, and it is the one statement left open by the reduction in
`StacksFrontier/CategoryTheory/Sites/Cohomology/StrictlyPerfect/HomComplexComparison.lean`.

The proof is the stupid filtration of `E`. Its four steps are:

* a *retract* of the source gives a retract of the induced arrows, and quasi-isomorphisms are
  stable under retracts (`homMap_quasiIso_of_retract`);
* a *zero* source gives a zero internal Hom complex (`homMap_quasiIso_of_isZero`);
* a source short complex which is split in every degree gives a short exact sequence of
  internal Hom complexes, again split in every degree, so two out of three holds
  (`homMap_quasiIso_of_degreewiseSplit`);
* the base case is a source concentrated in one degree with that term `O`, which is
  `AlgebraicGeometry.RingedSite.homMap_quasiIso_of_unit`.

Those combine first to a source concentrated in one degree with that term a direct summand of a
finite free module (`homMap_single_quasiIso_of_isFiniteFreeSummand`), by induction on the rank
through the biproduct splitting `O^{⊕(r+1)} = O^{⊕r} ⊞ O`; and then, by induction on the length
of the window where `E` is allowed to be nonzero, to the general case: the top of the window is
split off by `bottomProjection`, whose kernel has a shorter window and terms again direct
summands of finite free modules.

## Main definitions

* `AlgebraicGeometry.RingedSite.unitPower`: `O^{⊕r}`, as an iterated binary biproduct.
* `AlgebraicGeometry.RingedSite.IsFiniteFreeSummand`: being a direct summand of a finite free
  `O`-module.
* `AlgebraicGeometry.RingedSite.homArrowFunctor`: the induced arrows, as a functor of the source.
* `AlgebraicGeometry.RingedSite.bottomProjection`: the projection of a complex vanishing below
  `a` onto its degree-`a` term.

## Main results

* `AlgebraicGeometry.RingedSite.homMap_quasiIso_of_isFiniteFreeSummand`: the statement above.
* `AlgebraicGeometry.RingedSite.homMap_quasiIso_of_bounded`: the same with an explicit window.

## Implementation notes

**Why the hypothesis is `IsFiniteFreeSummand` and not `IsStrictlyPerfect`.** The predicate
`IsStrictlyPerfect` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/StrictlyPerfect/ConeOfAMorphism.lean`, which
carries the Stacks 08FL tag,
is universe-monomorphic: its signature fixes the structure sheaf to `Sheaf J RingCat.{0}` and
the modules to `SheafOfModules.{0}`, because it is phrased through `SheafOfModules.free (Fin n)`
and `SheafOfModules.free` takes its index type in the ring universe. So it cannot even be
mentioned for a `RingedSite.{u, u, u}`, which is where the internal Hom complex and the
Stacks 08JH comparison live. The same obstruction is recorded at length in
`HomComplexOfAStrictlyPerfectComplex.lean`, whose proved half states boundedness directly for
exactly this reason.

`IsFiniteFreeSummand` is the same condition stated universe-polymorphically: `M` is a retract of
`O^{⊕r}`. The two agree wherever both can be written, because `SheafOfModules.free (Fin r)` *is*
the coproduct of `r` copies of `SheafOfModules.unit` — that is
`SheafOfModules.isColimitFreeCofan` — and a finite coproduct in an abelian category is the
biproduct. The theorems below are therefore generalizations of the source statement, not
weakenings of it: they assume boundedness and the termwise direct-summand condition, which are
the two clauses of Stacks 08FL, and nothing else.

`O^{⊕r}` is written as the iterated binary biproduct `unitPower` rather than as
`⨁ (fun _ : Fin r => O)` because the induction consumes exactly the binary splitting
`O^{⊕(r+1)} = O^{⊕r} ⊞ O`, which for the iterated form is `rfl`, whereas for the `Fin`-indexed
biproduct it is a reindexing isomorphism that Mathlib does not provide.

The internal Hom complex of Stacks 0A8Z is produced by `Classical.choice`, so nothing below
inspects its terms; all of them are reached through `homDegreeIsLimit`,
`homDegreeProjection` and `homMap`.

## References

* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex ZeroObject

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  {F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The internal Hom complexes out of a varying source, with the map induced by a fixed
morphism `f` of targets, as a functor to the arrow category. -/
def homArrowFunctor (f : F ⟶ G) :
    (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ ⥤
      Arrow
        (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) where
  obj E := Arrow.mk (homMap X (𝟙 E.unop) f)
  map g := Arrow.homMk (homMap X g.unop (𝟙 F)) (homMap X g.unop (𝟙 G)) (by
    dsimp
    rw [homMap_comp, homMap_comp, Category.id_comp, Category.comp_id, Category.id_comp,
      Category.comp_id])
  map_id E := by
    apply Arrow.hom_ext <;> exact homMap_id X _ _
  map_comp g h := by
    apply Arrow.hom_ext <;>
      simp only [Arrow.homMk_left, Arrow.homMk_right, Arrow.comp_left, Arrow.comp_right,
        homMap_comp, Category.comp_id, unop_comp]

/-- The induced map of internal Hom complexes passes to retracts of the source. -/
theorem homMap_quasiIso_of_retract
    {E E' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (ρ : Retract E E') (f : F ⟶ G) [QuasiIso (homMap X (𝟙 E') f)] :
    QuasiIso (homMap X (𝟙 E) f) :=
  quasiIso_of_retractArrow (ρ.op.map (homArrowFunctor X f))

/-- A complex all of whose terms are zero is zero. -/
theorem complex_isZero_of_terms {A : Type*} [Category A] [HasZeroMorphisms A]
    (K : CochainComplex A ℤ) (hK : ∀ i, IsZero (K.X i)) : IsZero K :=
  (IsZero.iff_id_eq_zero _).2 (by ext i; exact (hK i).eq_of_src _ _)

/-- The internal Hom complex out of a zero source is zero. -/
theorem sheafHomComplex_isZero_of_isZero
    {E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hE : IsZero E)
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    IsZero (sheafHomComplex X E L).obj := by
  apply complex_isZero_of_terms
  intro n
  apply (IsZero.iff_id_eq_zero _).2
  refine homDegree_hom_ext X n _ _ fun q => ?_
  exact (internalHomSheaf_isZero_of_isZero X
    ((HomologicalComplex.eval _ _ (-q)).map_isZero hE)).eq_of_tgt _ _

/-- A zero source gives a quasi-isomorphism for trivial reasons. -/
theorem homMap_quasiIso_of_isZero
    {E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hE : IsZero E) (f : F ⟶ G) : QuasiIso (homMap X (𝟙 E) f) := by
  have := StacksDraft.TotalComplexQuasiIso.isIso_of_isZero_of_isZero
    (homMap X (𝟙 E) f) (sheafHomComplex_isZero_of_isZero X hE F)
    (sheafHomComplex_isZero_of_isZero X hE G)
  infer_instance

/-- **Two out of three for a termwise split short complex of sources.** -/
theorem homMap_quasiIso_of_degreewiseSplit
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (σ : ∀ p : ℤ, (S.map (HomologicalComplex.eval _ _ p)).Splitting) (f : F ⟶ G)
    [QuasiIso (homMap X (𝟙 S.X₁) f)] [QuasiIso (homMap X (𝟙 S.X₃) f)] :
    QuasiIso (homMap X (𝟙 S.X₂) f) := by
  let φ : internalHomShortComplex X S F ⟶ internalHomShortComplex X S G :=
    { τ₁ := homMap X (𝟙 S.X₃) f
      τ₂ := homMap X (𝟙 S.X₂) f
      τ₃ := homMap X (𝟙 S.X₁) f
      comm₁₂ := by dsimp [internalHomShortComplex]; simp [homMap_comp]
      comm₂₃ := by dsimp [internalHomShortComplex]; simp [homMap_comp] }
  have h1 : QuasiIso φ.τ₁ := ‹QuasiIso (homMap X (𝟙 S.X₃) f)›
  have h3 : QuasiIso φ.τ₃ := ‹QuasiIso (homMap X (𝟙 S.X₁) f)›
  exact StacksDraft.TotalComplexQuasiIso.quasiIso_τ₂ φ
    (HomologicalComplex.shortExact_of_degreewise_shortExact _
      (fun n => (internalHomTermwiseSplitting X S F σ n).shortExact))
    (HomologicalComplex.shortExact_of_degreewise_shortExact _
      (fun n => (internalHomTermwiseSplitting X S G σ n).shortExact))

section FiniteFree

/-- Sheaves of modules on a ringed site have finite biproducts, being abelian. -/
local instance hasFiniteBiproducts_sheafOfModules :
    HasFiniteBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- `O^{⊕r}`, the direct sum of `r` copies of the structure sheaf, as an iterated binary
biproduct. -/
def unitPower : ℕ → SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  | 0 => 0
  | r + 1 => unitPower r ⊞ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- `O^{⊕0}` is the zero sheaf of modules. -/
@[simp] lemma unitPower_zero : unitPower X 0 = 0 := rfl

/-- `O^{⊕(r+1)}` is the biproduct of `O^{⊕r}` and `O`. -/
@[simp] lemma unitPower_succ (r : ℕ) :
    unitPower X (r + 1) =
      (unitPower X r ⊞ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) := rfl

/-- The degreewise split short complex `O^{⊕r} ⟶ O^{⊕(r+1)} ⟶ O`. -/
def unitPowerShortComplex (r : ℕ) :
    ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  ShortComplex.mk (biprod.inl : unitPower X r ⟶
      unitPower X r ⊞ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    biprod.snd (by simp)

/-- A direct summand of a finite free `O`-module: a retract of `O^{⊕r}` for some `r`.

This is the condition `IsDirectSummandOfFiniteFree` of Stacks 08FL, spelled so that it can be
stated at an arbitrary module universe; see the implementation notes. -/
def IsFiniteFreeSummand (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Prop :=
  ∃ r : ℕ, Nonempty (Retract M (unitPower X r))

/-- **The single-degree finite free case.** -/
theorem homMap_single_quasiIso_of_unitPower (f : F ⟶ G) [QuasiIso f] (k : ℤ) (r : ℕ) :
    QuasiIso (homMap X
      (𝟙 ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k).obj
          (unitPower X r))) f) := by
  let Sg := HomologicalComplex.single
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k
  have hone : QuasiIso (homMap X
      (𝟙 (Sg.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) f) := by
    refine homMap_quasiIso_of_unit X f k (HomologicalComplex.singleObjXSelf _ k _) ?_ ?_
    · exact HomologicalComplex.single_obj_d
        (V := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (c := ComplexShape.up ℤ) k _ k (k + 1)
    · intro p hp
      exact HomologicalComplex.isZero_single_obj_X _ _ _ p hp
  induction r with
  | zero =>
    rw [unitPower_zero]
    exact homMap_quasiIso_of_isZero X (Sg.map_isZero (isZero_zero _)) f
  | succ r ih =>
    rw [unitPower_succ]
    let T := (unitPowerShortComplex X r).map Sg
    have hT (p : ℤ) : (T.map (HomologicalComplex.eval _ _ p)).Splitting :=
      ((ShortComplex.Splitting.ofHasBinaryBiproduct (unitPower X r)
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).map Sg).map _
    have h1 : QuasiIso (homMap X (𝟙 T.X₁) f) := ih
    have h3 : QuasiIso (homMap X (𝟙 T.X₃) f) := hone
    exact homMap_quasiIso_of_degreewiseSplit X T hT f

/-- **The single-degree case for a direct summand of a finite free module.** -/
theorem homMap_single_quasiIso_of_isFiniteFreeSummand (f : F ⟶ G) [QuasiIso f] (k : ℤ)
    {A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hA : IsFiniteFreeSummand X A) :
    QuasiIso (homMap X
      (𝟙 ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k).obj
          A)) f) := by
  obtain ⟨r, ⟨ρ⟩⟩ := hA
  have := homMap_single_quasiIso_of_unitPower X f k r
  exact homMap_quasiIso_of_retract X
    (ρ.map (HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k)) f

/-- Being a direct summand of a finite free module transports along an isomorphism. -/
theorem IsFiniteFreeSummand.of_iso
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : M ≅ N)
    (hN : IsFiniteFreeSummand X N) : IsFiniteFreeSummand X M := by
  obtain ⟨r, ⟨ρ⟩⟩ := hN
  exact ⟨r, ⟨(Retract.ofIso e).trans ρ⟩⟩

/-- A zero module is a direct summand of a finite free module. -/
theorem IsFiniteFreeSummand.of_isZero
    {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (hM : IsZero M) :
    IsFiniteFreeSummand X M :=
  ⟨0, ⟨⟨0, 0, hM.eq_of_src _ _⟩⟩⟩

end FiniteFree

section Bounded

variable {A : Type*} [Category A] [Abelian A]

/-- The projection of a complex which vanishes below `a` onto its degree-`a` term, viewed as a
complex concentrated in degree `a`. -/
def bottomProjection (E : CochainComplex A ℤ) (a : ℤ) (ha : IsZero (E.X (a - 1))) :
    E ⟶ (HomologicalComplex.single A (ComplexShape.up ℤ) a).obj (E.X a) :=
  HomologicalComplex.mkHomToSingle (𝟙 (E.X a)) (fun i hi => by
    obtain rfl : i = a - 1 := by
      change i + 1 = a at hi
      omega
    simpa using ha.eq_of_src (E.d (a - 1) a) 0)

/-- In degree `a`, `bottomProjection E a ha` is the inverse of the canonical isomorphism from
the degree-`a` term of the single complex. -/
lemma bottomProjection_f_self (E : CochainComplex A ℤ) (a : ℤ) (ha : IsZero (E.X (a - 1))) :
    (bottomProjection E a ha).f a =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a (E.X a)).inv := by
  simp [bottomProjection, HomologicalComplex.mkHomToSingle_f]

/-- In degree `a`, `bottomProjection E a ha` is an isomorphism. -/
lemma isIso_bottomProjection_f_self (E : CochainComplex A ℤ) (a : ℤ)
    (ha : IsZero (E.X (a - 1))) : IsIso ((bottomProjection E a ha).f a) := by
  rw [bottomProjection_f_self]
  infer_instance

/-- The kernel of `bottomProjection E a ha` vanishes in degree `a`. -/
lemma isZero_kernel_bottomProjection_X_self (E : CochainComplex A ℤ) (a : ℤ)
    (ha : IsZero (E.X (a - 1))) : IsZero ((kernel (bottomProjection E a ha)).X a) := by
  have := isIso_bottomProjection_f_self E a ha
  refine IsZero.of_mono_eq_zero ((kernel.ι (bottomProjection E a ha)).f a) ?_
  apply zero_of_comp_mono ((bottomProjection E a ha).f a)
  rw [← HomologicalComplex.comp_f, kernel.condition, HomologicalComplex.zero_f]

/-- In every degree `i ≠ a`, the inclusion of the kernel of `bottomProjection E a ha` into `E`
is an isomorphism. -/
lemma isIso_kernel_ι_bottomProjection_f (E : CochainComplex A ℤ) (a : ℤ)
    (ha : IsZero (E.X (a - 1))) (i : ℤ) (hi : i ≠ a) :
    IsIso ((kernel.ι (bottomProjection E a ha)).f i) :=
  StacksDraft.TotalComplexQuasiIso.isIso_of_isLimit_kernelFork_of_isZero _
    (isLimitForkMapOfIsLimit' (HomologicalComplex.eval A (ComplexShape.up ℤ) i)
      (kernel.condition (bottomProjection E a ha)) (kernelIsKernel _))
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (E.X a) i hi)

end Bounded

section Main

/-- **The bounded case.** If `E` vanishes outside the window `[a, a + r)` and each of its terms
is a direct summand of a finite free `O`-module, then the internal Hom complex out of `E`
carries a quasi-isomorphism of targets to a quasi-isomorphism. -/
theorem homMap_quasiIso_of_bounded (f : F ⟶ G) [QuasiIso f] (r : ℕ) (a : ℤ)
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hlo : ∀ i, i < a → IsZero (E.X i)) (hhi : ∀ i, a + r ≤ i → IsZero (E.X i))
    (hterm : ∀ i, IsFiniteFreeSummand X (E.X i)) :
    QuasiIso (homMap X (𝟙 E) f) := by
  induction r generalizing a E with
  | zero =>
    refine homMap_quasiIso_of_isZero X (complex_isZero_of_terms E fun i => ?_) f
    by_cases hi : i < a
    · exact hlo i hi
    · exact hhi i (by push_cast; omega)
  | succ r ih =>
    have ha : IsZero (E.X (a - 1)) := hlo (a - 1) (by omega)
    set p := bottomProjection E a ha
    set K := kernel p
    have hz : IsZero (K.X a) := isZero_kernel_bottomProjection_X_self E a ha
    have eK (i : ℤ) (hi : i ≠ a) : K.X i ≅ E.X i :=
      have := isIso_kernel_ι_bottomProjection_f E a ha i hi
      asIso ((kernel.ι p).f i)
    have hKterm (i : ℤ) : IsFiniteFreeSummand X (K.X i) := by
      by_cases hi : i = a
      · subst i
        exact IsFiniteFreeSummand.of_isZero X hz
      · exact IsFiniteFreeSummand.of_iso X (eK i hi) (hterm i)
    have hKlo (i : ℤ) (hi : i < a + 1) : IsZero (K.X i) := by
      by_cases hia : i = a
      · subst i
        exact hz
      · exact (hlo i (by omega)).of_iso (eK i hia)
    have hKhi (i : ℤ) (hi : a + 1 + r ≤ i) : IsZero (K.X i) :=
      (hhi i (by push_cast; omega)).of_iso (eK i (by omega))
    have : QuasiIso (homMap X (𝟙 K) f) := ih (a + 1) K hKlo hKhi hKterm
    have : QuasiIso (homMap X
        (𝟙 ((HomologicalComplex.single
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ) a).obj (E.X a))) f) :=
      homMap_single_quasiIso_of_isFiniteFreeSummand X f a (hterm a)
    let T := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    refine homMap_quasiIso_of_degreewiseSplit X T (fun i => ?_) f
    by_cases hi : i = a
    · subst i
      exact ShortComplex.Splitting.ofIsZeroOfIsIso _ hz (isIso_bottomProjection_f_self E a ha)
    · exact ShortComplex.Splitting.ofIsIsoOfIsZero _
        (isIso_kernel_ι_bottomProjection_f E a ha i hi)
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (E.X a) i hi)

/-- **The strictly perfect case.** If `E` has only finitely many nonzero terms and each of them
is a direct summand of a finite free `O`-module, then the internal Hom complex out of `E`
carries a quasi-isomorphism of targets to a quasi-isomorphism. -/
theorem homMap_quasiIso_of_isFiniteFreeSummand (f : F ⟶ G) [QuasiIso f]
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i, IsFiniteFreeSummand X (E.X i)) :
    QuasiIso (homMap X (𝟙 E) f) := by
  obtain ⟨a, ha⟩ := hbdd.bddBelow
  obtain ⟨b, hb⟩ := hbdd.bddAbove
  refine homMap_quasiIso_of_bounded X f (b - a + 1).toNat a E ?_ ?_ hterm
  · intro i hi
    by_contra hz
    have := ha hz
    omega
  · intro i hi
    by_contra hz
    have := hb hz
    omega

end Main

end AlgebraicGeometry.RingedSite

end
