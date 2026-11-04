module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitTwoGeneratorLoc
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitTrivialisedHom
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundlesCube
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TrivialRingSheafModules

/-!
# The centre of an object of the fibre product of [Stacks, Tag 0EXD] is free locally on `Spec A`

Let `p` be a prime, `A` a ring in which `p` vanishes and `f₁, f₂ ∈ A`, and consider the almost
blowup square of [Stacks, Example 0EVH] with its comparison functor
`AlgebraicGeometry.twoGeneratorFrobeniusColimitComparison`
`G : colim_F Vect(X) ⟶ colim_F Vect(Z) ×_{colim_F Vect(E)} colim_F Vect(X')`.
The essential surjectivity half of [Stacks, Tag 0EXD] is a Zariski glueing of two local inputs:
an object whose centre component is free is in the essential image of `G`
(`AlgebraicGeometry.mem_essImage_twoGeneratorFrobeniusColimitComparison_of_free_center`, in
`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitStageLocalCase.lean`), and — this file —
the centre component of every object of the target becomes free over the members of a cover of
`Spec A` by basic opens, read as the two-generator squares over the localisations `A_a`. This is
the source's sentence "*We may choose a finite affine open covering `X = X_1 ∪ … ∪ X_n` such that
`ℱ|_{Z ∩ X_i}` is free*"; no Noetherian hypothesis is needed for it.

## Main results

* `AlgebraicGeometry.exists_cover_free_center_twoGeneratorFrobeniusColimitLoc`: **elements `a_s`
  of `A` generating the unit ideal over which the restriction
  `AlgebraicGeometry.twoGeneratorFrobeniusColimitLoc` of an object `T` has free centre
  component.**
* `AlgebraicGeometry.frobeniusColimitVectorBundlesIsoFreeOfIsEmpty`: every finite locally free
  `colim_F 𝒪_X`-module on an empty scheme is free.
* `AlgebraicGeometry.frobeniusColimitVectorBundlesPullbackFreeOfFactor`: a module made free by
  the transition functor along `g` is made free along every morphism factoring through `g`.

## Implementation notes

The centre component is trivialised over an open cover `W_i` of the centre
(`AlgebraicGeometry.exists_cover_free_frobeniusColimitVectorBundlesPullback`). Rather than
choosing basic opens, the family is taken to be *all* `a ∈ A` over which the restricted centre
component is free, and the ideal they generate is shown to lie in no maximal ideal `𝔪`. If
`f₁ ∉ 𝔪` (or `f₂ ∉ 𝔪`), then `f₁` itself is such an `a`: the centre over `A_{f₁}` is the spectrum
of the zero ring, and every module on an empty scheme is free. Otherwise `𝔪` comes from a point
of the centre, which lies in some `W_i` and hence in a basic open `D(ā) ⊆ W_i` of the centre, `ā`
the image of some `a ∈ A ∖ 𝔪`; the centre over `A_a` maps into `D(ā)`, so the restricted centre
component is free.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Frobenius Stacks.AlmostBlowUp

universe u

namespace AlgebraicGeometry

/-! ### Free modules over the Frobenius colimit -/

section Free

variable (p : ℕ) [Fact p.Prime]

/-- **Every sheaf of modules over `colim_F 𝒪_X` on an empty scheme is a zero object.** -/
theorem isZero_sheafOfModules_frobeniusColimitRingSheaf_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    (hX : IsInCharacteristic X p)
    (M : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)) : IsZero M := by
  refine Stacks.SheafOfModules.isZero_of_subsingleton_sections (fun V => ?_) M
  obtain rfl : V = ⊥ := by
    ext x
    exact isEmptyElim (show X from x)
  have h0 : Subsingleton (X.ringCatSheaf.obj.obj (op ⊥)) :=
    (inferInstance : Subsingleton Γ(X, ⊥))
  have h1 : (1 : (frobeniusColimitRingSheaf X p hX).obj.obj (op ⊥)) = 0 := by
    have := congrArg ((frobeniusStructureSheafι X p hX 0).hom.app (op ⊥)).hom (h0.elim 1 0)
    rwa [map_one, map_zero] at this
  exact subsingleton_of_forall_eq 0 fun x => by rw [← one_mul x, h1, zero_mul]

/-- **Every finite locally free `colim_F 𝒪_X`-module on an empty scheme is free**, on any finite
index type. -/
noncomputable def frobeniusColimitVectorBundlesIsoFreeOfIsEmpty {X : Scheme.{u}} [IsEmpty X]
    (hX : IsInCharacteristic X p) (M : frobeniusColimitVectorBundles X p hX) (I : Type u)
    [Finite I] :
    M ≅ ⟨_root_.SheafOfModules.free I, isFiniteLocallyFreeFrobeniusColimitFree p hX I⟩ :=
  ObjectProperty.isoMk _ ((isZero_sheafOfModules_frobeniusColimitRingSheaf_of_isEmpty p hX
    M.obj).iso (isZero_sheafOfModules_frobeniusColimitRingSheaf_of_isEmpty p hX _))

/-- **A module made free by the transition functor along `g` is made free by the transition
functor along every morphism factoring through `g`.** -/
noncomputable def frobeniusColimitVectorBundlesPullbackFreeOfFactor {X V Y : Scheme.{u}}
    (g : V ⟶ X) (j : Y ⟶ X) (θ : Y ⟶ V) (hθ : θ ≫ g = j)
    (hX : IsInCharacteristic X p) (hV : IsInCharacteristic V p) (hY : IsInCharacteristic Y p)
    (M : frobeniusColimitVectorBundles X p hX) (I : Type u) [Finite I]
    (e : (frobeniusColimitVectorBundlesPullback p g hV hX).obj M ≅
      ⟨_root_.SheafOfModules.free I, isFiniteLocallyFreeFrobeniusColimitFree p hV I⟩) :
    (frobeniusColimitVectorBundlesPullback p j hY hX).obj M ≅
      ⟨_root_.SheafOfModules.free I, isFiniteLocallyFreeFrobeniusColimitFree p hY I⟩ :=
  ((frobeniusColimitVectorBundlesPullbackTriangleIso p θ g j hY hV hX hθ).app M).symm ≪≫
    (frobeniusColimitVectorBundlesPullback p θ hY hV).mapIso e ≪≫
    ObjectProperty.isoMk _
      (_root_.SheafOfModules.pullbackObjFreeIso (frobeniusColimitStructureSheafHom p θ hY hV) I)

end Free

/-! ### The cover of `Spec A` over which the centre component is free -/

section TwoGenerator

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (f₁ f₂ : A) (p : ℕ) [Fact p.Prime] (hpA : (p : A) = 0)

omit [Fact p.Prime] in
/-- **The centre ring of the two-generator square is the zero ring as soon as one of the two
generators is a unit.** -/
theorem subsingleton_centerRing_of_isUnit (B : Type u) [CommRing B] (g₁ g₂ : B)
    (h : IsUnit g₁ ∨ IsUnit g₂) : Subsingleton (centerRing B g₁ g₂) := by
  rw [Ideal.Quotient.subsingleton_iff]
  rcases h with h | h <;> exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) h

/-- **The centre of an object of the categorical fibre product of [Stacks, Tag 0EXD] is free
locally on `Spec A`, in the sense of the two-generator squares over the localisations.** There
are elements `a_s` of `A` generating the unit ideal such that the restriction of `T` to the
square over `A_{a_s}` has free centre component. -/
theorem exists_cover_free_center_twoGeneratorFrobeniusColimitLoc
    (T : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      CategoricalPullback
        (frobeniusColimitVectorBundlesPullback p (exceptionalToCenter A f₁ f₂)
          (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
          (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA))
        (frobeniusColimitVectorBundlesPullback p (exceptionalToModification A f₁ f₂)
          (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
          (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA))) :
    ∃ (σ : Type u) (a : σ → A), Ideal.span (Set.range a) = ⊤ ∧ ∀ s : σ,
      ∃ (I : Type u) (_ : Finite I), Nonempty
        (((twoGeneratorFrobeniusColimitLoc A f₁ f₂ p hpA (Localization.Away (a s))
            (natCast_eq_zero_of_algebra A p hpA _)).obj T).fst ≅
          ⟨_root_.SheafOfModules.free I,
            isFiniteLocallyFreeFrobeniusColimitFree p
              (isInCharacteristic_twoGeneratorCenter (Localization.Away (a s)) _ _ p
                (natCast_eq_zero_of_algebra A p hpA _)) I⟩) := by
  let Good : A → Prop := fun a => ∃ (I : Type u) (_ : Finite I), Nonempty
    (((twoGeneratorFrobeniusColimitLoc A f₁ f₂ p hpA (Localization.Away a)
        (natCast_eq_zero_of_algebra A p hpA _)).obj T).fst ≅
      ⟨_root_.SheafOfModules.free I,
        isFiniteLocallyFreeFrobeniusColimitFree p
          (isInCharacteristic_twoGeneratorCenter (Localization.Away a) _ _ p
            (natCast_eq_zero_of_algebra A p hpA _)) I⟩)
  refine ⟨{a : A // Good a}, Subtype.val, ?_, fun s => s.2⟩
  have hZ := isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA
  have hgood_unit : ∀ a : A, (IsUnit (algebraMap A (Localization.Away a) f₁) ∨
      IsUnit (algebraMap A (Localization.Away a) f₂)) → Good a := by
    intro a ha
    have := subsingleton_centerRing_of_isUnit _ _ _ ha
    have : IsEmpty (Spec (.of (centerRing (Localization.Away a)
        (algebraMap A (Localization.Away a) f₁) (algebraMap A (Localization.Away a) f₂)))) :=
      inferInstanceAs (IsEmpty (PrimeSpectrum _))
    exact ⟨PEmpty, inferInstance,
      ⟨frobeniusColimitVectorBundlesIsoFreeOfIsEmpty p _ _ PEmpty⟩⟩
  obtain ⟨J, W, K, hKfin, hcov, hfree⟩ :=
    exists_cover_free_frobeniusColimitVectorBundlesPullback p
      (Spec (.of (centerRing A f₁ f₂))) hZ T.fst
  have hgood_W : ∀ (a : A) (i : J),
      ((PrimeSpectrum.basicOpen (Ideal.Quotient.mk (centerIdeal A f₁ f₂) a) :
        Set (PrimeSpectrum (centerRing A f₁ f₂))) ⊆
        (W i : Set (Spec (.of (centerRing A f₁ f₂))))) → Good a := by
    intro a i hle
    let j := Spec.map (CommRingCat.ofHom (centerCoeffHom A (Localization.Away a) f₁ f₂))
    have hr : Set.range j ⊆ Set.range (W i).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨q, rfl⟩
      apply hle
      intro hmem
      have hmem' : Ideal.Quotient.mk _ (algebraMap A (Localization.Away a) a) ∈ q.asIdeal :=
        hmem
      exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem'
        ((IsLocalization.Away.algebraMap_isUnit a).map _))
    have := hKfin i
    exact ⟨K i, hKfin i, ⟨frobeniusColimitVectorBundlesPullbackFreeOfFactor p (W i).ι j
      (IsOpenImmersion.lift (W i).ι j hr) (IsOpenImmersion.lift_fac _ _ _) hZ _ _ T.fst (K i)
      (hfree i).some⟩⟩
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : ∀ a, Good a → a ∈ m := fun a ha => hle (Ideal.subset_span ⟨⟨a, ha⟩, rfl⟩)
  have hI : centerIdeal A f₁ f₂ ≤ m := by
    rw [centerIdeal, Ideal.span_le]
    rintro x (rfl | rfl)
    exacts [hmem _ (hgood_unit _ (Or.inl (IsLocalization.Away.algebraMap_isUnit _))),
      hmem _ (hgood_unit _ (Or.inr (IsLocalization.Away.algebraMap_isUnit _)))]
  let y : PrimeSpectrum (centerRing A f₁ f₂) :=
    ⟨m.map (Ideal.Quotient.mk _), Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rwa [Ideal.mk_ker])⟩
  have hy : y ∈ (⨆ i, W i) := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨_, ⟨b, rfl⟩, hyb, hb⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hi (W i).isOpen
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact hyb ((Ideal.mem_quotient_iff_mem hI).2 (hmem b (hgood_W b i hb)))

end TwoGenerator

end AlgebraicGeometry

end
