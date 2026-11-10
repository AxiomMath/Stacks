module

public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import StacksFrontier.Algebra.Module.Adequate.SplittingLiftDomain
public import StacksFrontier.Algebra.Module.Adequate.SplittingWeightOneLarge

/-!
# The weight-one coproduct of Tag 06V7 on a restricted domain of algebras

Let `A` be a ring, `Q` a property of commutative `A`-algebras and `M` a finitely presented
`A`-module. The weight-one part of an adequate module-valued functor on the full subcategory of
algebras satisfying `Q`, evaluated at the symmetric algebra of `M × M`, is the direct sum of the
images of the weight-one parts coming from the two copies of `M`. This is the part of
[Stacks, Tag 06V7] that the splitting argument consumes, here on a restricted domain.

`StacksFrontier.Algebra.Module.Adequate.SplittingWeightOneLarge` proves the same statements for a
functor on all commutative `A`-algebras; that proof is left untouched, and nothing here depends
on its conclusions. Its *domain-free* ingredients — the symmetric-algebra algebra maps and the
tensor-level degree-one calculus — are `public` and are reused verbatim.

## Main definitions

* `AdequateFunctor.LaurentDomain.HasWeightOneCoproduct` — the weight-one direct-sum
  decomposition, on a restricted domain.

## Main results

* `AdequateFunctor.LaurentDomain.weightOne_eq_add_images` — the weight-one part over the
  symmetric algebra of two copies of a finitely presented module is the sum of the two factor
  images.
* `AdequateFunctor.LaurentDomain.weightOne_images_disjoint` — that sum is direct.
* `AdequateFunctor.LaurentDomain.adequate_hasWeightOneCoproduct` — an adequate functor on the
  domain has the weight-one coproduct.

## Implementation notes

The predicate `AdequateFunctor.LaurentDomain.HasWeightOneCoproduct` carries, for each finitely
presented module `M`, the memberships of the four algebras the statement mentions: the two
symmetric algebras and their Laurent polynomial algebras, the latter because the weight spaces
are only defined where the Laurent extension is in the domain. A caller holding a symmetric
algebra closure and a Laurent closure supplies all four.

Adequacy is used only through a monomorphism into a module extension. On a restricted domain
`AdequateFunctor.IsAdequate` presents the universe-lift of the functor as a kernel, so
`AdequateFunctor.presheafOfModulesUliftIso` is composed in first; that is
`exists_mono_to_moduleExtension`, which replaces the full-domain `AdequateFunctor.isAdequate_iff`
and needs no base algebra object, because only the forward direction is wanted.

The uniqueness of the weight decomposition, which is what rules out an element having two
distinct weights, is [Stacks, Tag 06UZ] on the domain,
`AdequateFunctor.LaurentDomain.weightSpace_eq_zero_of_mem_two_weights`; the hypothesis it needs
is `AdequateFunctor.LaurentDomain.adequate_preservesFlatBaseChange`, i.e. [Stacks, Tag 06UW] on
the domain. No Ext vanishing is used.

## References

* [Stacks Project, Tag 06UW](https://stacks.math.columbia.edu/tag/06UW)
* [Stacks Project, Tag 06UZ](https://stacks.math.columbia.edu/tag/06UZ)
* [Stacks Project, Tag 06V7](https://stacks.math.columbia.edu/tag/06V7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum TensorProduct

namespace AdequateFunctor.LaurentDomain

universe w v u

variable {A : Type u} [CommRing A] {Q : ObjectProperty (CommAlgCat.{max u v} A)}

/-! ### Adequacy as a monomorphism into a module extension -/

/-- An adequate module-valued functor on a domain of algebras admits a monomorphism into the
module extension of an `A`-module. This is the only use the weight-one argument makes of
adequacy, and unlike `AdequateFunctor.isAdequate_of_isLinearlyAdequate_on` it needs no base
algebra object: only the forward direction of `AdequateFunctor.isAdequate_iff` is wanted, and
the universe lift that `AdequateFunctor.IsAdequate` presents is absorbed by
`AdequateFunctor.presheafOfModulesUliftIso`. -/
public lemma exists_mono_to_moduleExtension (F : ModuleValuedFunctorOn.{max u v w} Q.ι)
    (hF : IsAdequate.{max u v w, v} Q.ι F) :
    ∃ (N : ModuleCat.{max u v w} A)
      (η : F ⟶ (moduleExtensionFunctorOn.{max u v w, v} Q.ι).obj N), Mono η := by
  obtain ⟨M, N, f, ⟨i⟩⟩ := hF
  exact ⟨M, (presheafOfModulesUliftIso.{max u v, w} (algebraRingDiagramOn.{v} Q.ι) F).inv ≫
    i.hom ≫ kernel.ι ((moduleExtensionFunctorOn.{max u v w, v} Q.ι).map f), inferInstance⟩

/-! ### Weight one through a module extension -/

/-- Weight-space membership for a module extension on the domain is the corresponding statement
about the base-changed Laurent maps on the tensor product. -/
public lemma moduleExtension_mem_weightSpace_iff (B : Type (max u v)) [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (N : ModuleCat.{max u v w} A) (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ)
    (y : TensorProduct A B N) :
    y ∈ weightSpace Q B hB hL ((moduleExtensionFunctorOn.{max u v w, v} Q.ι).obj N) 𝒜 k ↔
      (LaurentPolynomial.T k : LaurentPolynomial B) •
          (TensorProduct.map (constantLaurentMapLarge A B).toLinearMap LinearMap.id) y =
        (TensorProduct.map (gradedLaurentMapLarge A B 𝒜).toLinearMap LinearMap.id) y :=
  Iff.rfl

/-- Weight one over a symmetric algebra does not depend on which degree-one grading is used to
measure it. -/
public lemma weightSpace_one_iff_symmetricPower (V : Type (max u v))
    [AddCommGroup V] [Module A V]
    (hS : Q (CommAlgCat.of A (SymmetricAlgebra A V)))
    (hSL : Q (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A V))))
    (F : ModuleValuedFunctorOn.{max u v w} Q.ι)
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A V)) [GradedAlgebra 𝒜]
    (h𝒜 : ∀ m, SymmetricAlgebra.ι A V m ∈ 𝒜 1)
    (x : F.obj (algObj Q (SymmetricAlgebra A V) hS)) :
    x ∈ weightSpace Q (SymmetricAlgebra A V) hS hSL F 𝒜 1 ↔
      x ∈ weightSpace Q (SymmetricAlgebra A V) hS hSL F (symmetricPower A V) 1 := by
  rw [mem_weightSpace_iff, mem_weightSpace_iff, map_algMor_congr F
      (gradedLaurentMapLarge_symmetricAlgebra_eq_degreeOne A V 𝒜 h𝒜) hS hSL,
    map_algMor_congr F
      (gradedLaurentMapLarge_symmetricAlgebra_eq_degreeOne A V (symmetricPower A V)
        (symmetricAlgebra_generator_mem_symmetricPower_one A V)) hS hSL]

/-- Weight one in a functor embedded in a module extension is exactly degree one in the tensor
decomposition, on the domain. -/
public lemma weightOne_iff_tensor_degreeOne (V : Type (max u v)) [AddCommGroup V] [Module A V]
    (hS : Q (CommAlgCat.of A (SymmetricAlgebra A V)))
    (hSL : Q (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A V))))
    {N : ModuleCat.{max u v w} A} {F : ModuleValuedFunctorOn.{max u v w} Q.ι}
    (η : F ⟶ (moduleExtensionFunctorOn.{max u v w, v} Q.ι).obj N) [Mono η]
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A V)) [GradedAlgebra 𝒜]
    (h𝒜 : ∀ p, SymmetricAlgebra.ι A V p ∈ 𝒜 1)
    (x : F.obj (algObj Q (SymmetricAlgebra A V) hS)) :
    x ∈ weightSpace Q (SymmetricAlgebra A V) hS hSL F 𝒜 1 ↔
      (η.app (algObj Q (SymmetricAlgebra A V) hS)).hom x ∈
        DirectSum.decomposeTensor (symmetricPower A V) (N : Type (max u v w)) 1 := by
  refine (weightSpace_one_iff_symmetricPower V hS hSL F 𝒜 h𝒜 x).trans
    (((weightSpace_map_iff_of_mono hS hSL η (symmetricPower A V) 1 x).symm).trans
      ((moduleExtension_mem_weightSpace_iff (Q := Q) (SymmetricAlgebra A V) hS hSL N
        (symmetricPower A V) 1 _).trans ?_))
  refine ⟨moduleExtension_weightOne_mem_degreeOne_large A (SymmetricAlgebra A V)
      (N : Type (max u v w)) (symmetricPower A V)
      (gradedLaurentMapLarge_mem A (SymmetricAlgebra A V) (symmetricPower A V)) _,
    fun hx => moduleExtension_range_weightSpace_large A (SymmetricAlgebra A V)
      (N : Type (max u v w)) (symmetricPower A V) 1
      (gradedLaurentMapLarge_mem A (SymmetricAlgebra A V) (symmetricPower A V) 1) _ ?_⟩
  rwa [← DirectSum.decomposeTensor_apply]

/-- Everything in the image of the generator-killing endomorphism has weight zero. -/
public lemma symmetricAlgebraZeroMap_mem_weightSpace_zero (M : Type (max u v))
    [AddCommGroup M] [Module A M]
    (hS : Q (CommAlgCat.of A (SymmetricAlgebra A M)))
    (hSL : Q (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A M))))
    (F : ModuleValuedFunctorOn.{max u v w} Q.ι)
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A M)) [GradedAlgebra 𝒜]
    (x : F.obj (algObj Q (SymmetricAlgebra A M) hS)) :
    F.map (algMor Q (symmetricAlgebraZeroMapLarge A M) hS hS) x ∈
      weightSpace Q (SymmetricAlgebra A M) hS hSL F 𝒜 0 := by
  refine mem_weightSpace_iff.mpr ?_
  rw [map_algMor_comp F (symmetricAlgebraZeroMapLarge A M)
      (constantLaurentMapLarge A (SymmetricAlgebra A M)) hS hS hSL,
    map_algMor_comp F (symmetricAlgebraZeroMapLarge A M)
      (gradedLaurentMapLarge A (SymmetricAlgebra A M) 𝒜) hS hS hSL,
    map_algMor_congr F
      (gradedLaurentMapLarge_comp_symmetricAlgebraZeroMapLarge A M 𝒜) hS hSL]
  exact one_smul _ _

/-! ### The weight-one coproduct -/

/-- The weight-one part over the symmetric algebra on two copies of a finitely presented module
is the sum of the images from each copy, on the domain. -/
public lemma weightOne_eq_add_images {M : Type (max u v)}
    [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
    (hS : Q (CommAlgCat.of A (SymmetricAlgebra A M)))
    (hSL : Q (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A M))))
    (hT : Q (CommAlgCat.of A (SymmetricAlgebra A (M × M))))
    (hTL : Q (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A (M × M)))))
    (F : ModuleValuedFunctorOn.{max u v w} Q.ι) (hF : IsAdequate.{max u v w, v} Q.ι F)
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A M)) [GradedAlgebra 𝒜]
    (ℬ : ℕ → Submodule A (SymmetricAlgebra A (M × M))) [GradedAlgebra ℬ]
    (h𝒜 : ∀ m, SymmetricAlgebra.ι A M m ∈ 𝒜 1)
    (hℬ : ∀ m, SymmetricAlgebra.ι A (M × M) m ∈ ℬ 1) :
    let p₁ : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (M × M) :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inl A M M))
    let p₂ : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (M × M) :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inr A M M))
    ∀ z, z ∈ weightSpace Q (SymmetricAlgebra A (M × M)) hT hTL F ℬ 1 ↔
      ∃ x y, ∃ z₁ z₂ : F.obj (algObj Q (SymmetricAlgebra A (M × M)) hT),
        x ∈ weightSpace Q (SymmetricAlgebra A M) hS hSL F 𝒜 1 ∧
        y ∈ weightSpace Q (SymmetricAlgebra A M) hS hSL F 𝒜 1 ∧
        z₁ = F.map (algMor Q p₁ hS hT) x ∧
        z₂ = F.map (algMor Q p₂ hS hT) y ∧ z = z₁ + z₂ := by
  obtain ⟨N, η, _⟩ := exists_mono_to_moduleExtension.{w} F hF
  intro p₁ p₂ z
  let q₁ := SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp (LinearMap.fst A M M))
  let q₂ := SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp (LinearMap.snd A M M))
  let Y : ((Q.FullSubcategory)ᵒᵖ)ᵒᵖ := algObj Q (SymmetricAlgebra A (M × M)) hT
  constructor
  · intro hz
    have ht := (weightOne_iff_tensor_degreeOne (M × M) hT hTL η ℬ hℬ z).mp hz
    let x : F.obj (algObj Q (SymmetricAlgebra A M) hS) := F.map (algMor Q q₁ hT hS) z
    let y : F.obj (algObj Q (SymmetricAlgebra A M) hS) := F.map (algMor Q q₂ hT hS) z
    have proj : ∀ f : M × M →ₗ[A] M, F.map (algMor Q
        (SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp f)) hT hS) z ∈
        weightSpace Q (SymmetricAlgebra A M) hS hSL F 𝒜 1 := fun f => by
      refine (weightOne_iff_tensor_degreeOne M hS hSL η 𝒜 h𝒜 _).mpr ?_
      rw [app_map_algMor η _ hT hS z]
      exact tensor_symmetricAlgebra_map_degreeOne_large f _ ht
    have hx : x ∈ weightSpace Q (SymmetricAlgebra A M) hS hSL F 𝒜 1 := proj (LinearMap.fst A M M)
    have hy : y ∈ weightSpace Q (SymmetricAlgebra A M) hS hSL F 𝒜 1 := proj (LinearMap.snd A M M)
    refine ⟨x, y, F.map (algMor Q p₁ hS hT) x, F.map (algMor Q p₂ hS hT) y,
      hx, hy, rfl, rfl, ?_⟩
    apply PresheafOfModules.injective_of_mono η Y
    refine Eq.trans ?_ (map_add (ConcreteCategory.hom (η.app Y))
      (F.map (algMor Q p₁ hS hT) x) (F.map (algMor Q p₂ hS hT) y)).symm
    change η.app Y z = η.app Y (F.map (algMor Q p₁ hS hT) x) +
      η.app Y (F.map (algMor Q p₂ hS hT) y)
    rw [PresheafOfModules.naturality_apply η (algMor Q p₁ hS hT) x,
      PresheafOfModules.naturality_apply η (algMor Q p₂ hS hT) y]
    dsimp only [x, y]
    rw [PresheafOfModules.naturality_apply η (algMor Q q₁ hT hS) z,
      PresheafOfModules.naturality_apply η (algMor Q q₂ hT hS) z]
    exact (tensor_symmetricAlgebra_factor_sum_large (η.app Y z) ht).symm
  · rintro ⟨x, y, z₁, z₂, hx, hy, rfl, rfl, rfl⟩
    have key : η.app Y (F.map (algMor Q p₁ hS hT) x) +
        η.app Y (F.map (algMor Q p₂ hS hT) y) ∈
        DirectSum.decomposeTensor (symmetricPower A (M × M)) (N : Type (max u v w)) 1 := by
      rw [PresheafOfModules.naturality_apply η (algMor Q p₁ hS hT) x,
        PresheafOfModules.naturality_apply η (algMor Q p₂ hS hT) y]
      exact Submodule.add_mem _
        (tensor_symmetricAlgebra_map_degreeOne_large (LinearMap.inl A M M) _
          ((weightOne_iff_tensor_degreeOne M hS hSL η 𝒜 h𝒜 x).mp hx))
        (tensor_symmetricAlgebra_map_degreeOne_large (LinearMap.inr A M M) _
          ((weightOne_iff_tensor_degreeOne M hS hSL η 𝒜 h𝒜 y).mp hy))
    exact (weightOne_iff_tensor_degreeOne (M × M) hT hTL η ℬ hℬ _).mpr
      (Eq.subst (motive := fun c => c ∈ DirectSum.decomposeTensor
          (symmetricPower A (M × M)) (N : Type (max u v w)) 1)
        (map_add (ConcreteCategory.hom (η.app Y))
          (F.map (algMor Q p₁ hS hT) x) (F.map (algMor Q p₂ hS hT) y)).symm key)

/-- The two factor images in weight one have zero intersection, on the domain. -/
public lemma weightOne_images_disjoint {M : Type (max u v)}
    [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
    (hS : Q (CommAlgCat.of A (SymmetricAlgebra A M)))
    (hSL : Q (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A M))))
    (hSLL : Q (CommAlgCat.of A (LaurentPolynomial (LaurentPolynomial
      (SymmetricAlgebra A M)))))
    (hT : Q (CommAlgCat.of A (SymmetricAlgebra A (M × M))))
    (F : ModuleValuedFunctorOn.{max u v w} Q.ι) (hF : IsAdequate.{max u v w, v} Q.ι F)
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A M)) [GradedAlgebra 𝒜] :
    let p₁ : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (M × M) :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inl A M M))
    let p₂ : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (M × M) :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inr A M M))
    ∀ x y, ∀ z₁ z₂ : F.obj (algObj Q (SymmetricAlgebra A (M × M)) hT),
      x ∈ weightSpace Q (SymmetricAlgebra A M) hS hSL F 𝒜 1 →
      y ∈ weightSpace Q (SymmetricAlgebra A M) hS hSL F 𝒜 1 →
      z₁ = F.map (algMor Q p₁ hS hT) x →
      z₂ = F.map (algMor Q p₂ hS hT) y → z₁ + z₂ = 0 → x = 0 ∧ y = 0 := by
  intro p₁ p₂ x y z₁ z₂ hx hy hz₁ hz₂ hzero
  let q₁ : SymmetricAlgebra A (M × M) →ₐ[A] SymmetricAlgebra A M :=
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp (LinearMap.fst A M M))
  let q₂ : SymmetricAlgebra A (M × M) →ₐ[A] SymmetricAlgebra A M :=
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp (LinearMap.snd A M M))
  have hq₁p₁ : q₁.comp p₁ = AlgHom.id A (SymmetricAlgebra A M) := by
    ext m
    simp [p₁, q₁]
  have hq₁p₂ : q₁.comp p₂ = symmetricAlgebraZeroMapLarge A M := by
    ext m
    simp [p₂, q₁, symmetricAlgebraZeroMapLarge]
  have hq₂p₂ : q₂.comp p₂ = AlgHom.id A (SymmetricAlgebra A M) := by
    ext m
    simp [p₂, q₂]
  have hq₂p₁ : q₂.comp p₁ = symmetricAlgebraZeroMapLarge A M := by
    ext m
    simp [p₁, q₂, symmetricAlgebraZeroMapLarge]
  have hflat := adequate_preservesFlatBaseChange.{w} F hF
  have key : ∀ (q pa pb : _ →ₐ[A] _) (a b : F.obj (algObj Q (SymmetricAlgebra A M) hS)),
      q.comp pa = AlgHom.id A (SymmetricAlgebra A M) →
      q.comp pb = symmetricAlgebraZeroMapLarge A M →
      a ∈ weightSpace Q (SymmetricAlgebra A M) hS hSL F 𝒜 1 →
      ∀ z₁ z₂ : F.obj (algObj Q (SymmetricAlgebra A (M × M)) hT),
      z₁ = F.map (algMor Q pa hS hT) a → z₂ = F.map (algMor Q pb hS hT) b →
      z₁ + z₂ = 0 → a = 0 := by
    intro q pa pb a b hqa hqb ha z₁ z₂ hz₁ hz₂ hab
    have h1 := congrArg (fun z => F.map (algMor Q q hT hS) z) hab
    rw [(F.map (algMor Q q hT hS)).hom.map_add, (F.map (algMor Q q hT hS)).hom.map_zero, hz₁, hz₂,
      map_algMor_comp F pa q hS hT hS, map_algMor_congr F hqa hS hS, map_algMor_id,
      map_algMor_comp F pb q hS hT hS, map_algMor_congr F hqb hS hS] at h1
    have hb : F.map (algMor Q (symmetricAlgebraZeroMapLarge A M) hS hS) b ∈
        weightSpace Q (SymmetricAlgebra A M) hS hSL F 𝒜 1 := by
      rw [eq_neg_of_add_eq_zero_right h1]
      exact weightSpace_neg_mem hS hSL F 𝒜 1 ha
    rw [weightSpace_eq_zero_of_mem_two_weights Q (SymmetricAlgebra A M) hS hSL hSLL F hflat 𝒜
      (by norm_num) hb (symmetricAlgebraZeroMap_mem_weightSpace_zero M hS hSL F 𝒜 b)]
      at h1
    exact (add_zero a).symm.trans h1
  exact ⟨key q₁ p₁ p₂ x y hq₁p₁ hq₁p₂ hx _ _ hz₁ hz₂ hzero,
    key q₂ p₂ p₁ y x hq₂p₂ hq₂p₁ hy _ _ hz₂ hz₁ ((add_comm _ _).trans hzero)⟩

/-- In weight one on the symmetric algebra of two copies of a finitely presented module, every
element decomposes uniquely into the two factor images. Restricted-domain form: the memberships
of the four algebras the statement mentions are carried as hypotheses. -/
public def HasWeightOneCoproduct (Q : ObjectProperty (CommAlgCat.{max u v} A))
    (F : ModuleValuedFunctorOn.{max u v w} Q.ι) : Prop :=
  ∀ (M : Type (max u v)) [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
    (hS : Q (CommAlgCat.of A (SymmetricAlgebra A M)))
    (hSL : Q (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A M))))
    (hT : Q (CommAlgCat.of A (SymmetricAlgebra A (M × M))))
    (hTL : Q (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A (M × M)))))
    (𝒜 : ℕ → Submodule A (SymmetricAlgebra A M)) [GradedAlgebra 𝒜]
    (ℬ : ℕ → Submodule A (SymmetricAlgebra A (M × M))) [GradedAlgebra ℬ],
    (∀ m, SymmetricAlgebra.ι A M m ∈ 𝒜 1) →
    (∀ m, SymmetricAlgebra.ι A (M × M) m ∈ ℬ 1) →
    let p₁ : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (M × M) :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inl A M M))
    let p₂ : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (M × M) :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × M)).comp (LinearMap.inr A M M))
    ∀ z, z ∈ weightSpace Q (SymmetricAlgebra A (M × M)) hT hTL F ℬ 1 ↔
      ∃! xy : F.obj (algObj Q (SymmetricAlgebra A M) hS) ×
          F.obj (algObj Q (SymmetricAlgebra A M) hS),
        xy.1 ∈ weightSpace Q (SymmetricAlgebra A M) hS hSL F 𝒜 1 ∧
        xy.2 ∈ weightSpace Q (SymmetricAlgebra A M) hS hSL F 𝒜 1 ∧
        ∃ z₁ z₂ : F.obj (algObj Q (SymmetricAlgebra A (M × M)) hT),
          z₁ = F.map (algMor Q p₁ hS hT) xy.1 ∧
          z₂ = F.map (algMor Q p₂ hS hT) xy.2 ∧ z = z₁ + z₂

/-- **Stacks Lemma 06V7 on a restricted domain of algebras**, the weight-one coproduct: an
adequate module-valued functor on a domain of algebras closed under Laurent polynomial
extension has the weight-one direct-sum decomposition. -/
public lemma adequate_hasWeightOneCoproduct
    (hlau : ∀ (R : Type (max u v)) [CommRing R] [Algebra A R], Q (CommAlgCat.of A R) →
      Q (CommAlgCat.of A (LaurentPolynomial R)))
    (F : ModuleValuedFunctorOn.{max u v w} Q.ι) (hF : IsAdequate.{max u v w, v} Q.ι F) :
    HasWeightOneCoproduct.{w} Q F := by
  intro M _ _ _ hS hSL hT hTL 𝒜 _ ℬ _ hgenA hgenB _ _ z
  constructor
  · intro hz
    obtain ⟨x, y, _, _, hx, hy, rfl, rfl, hsum⟩ :=
      (weightOne_eq_add_images.{w} hS hSL hT hTL F hF 𝒜 ℬ hgenA hgenB z).mp hz
    refine ⟨(x, y), ⟨hx, hy, _, _, rfl, rfl, hsum⟩, ?_⟩
    rintro xy ⟨hx', hy', _, _, rfl, rfl, hsum'⟩
    have hxy0 := weightOne_images_disjoint.{w} hS hSL (hlau _ hSL) hT F hF 𝒜
      (x - xy.1) (y - xy.2) _ _
      (weightSpace_sub_mem hS hSL F 𝒜 1 hx hx') (weightSpace_sub_mem hS hSL F 𝒜 1 hy hy')
      rfl rfl (by
        rw [map_sub, map_sub]
        exact (sub_add_sub_comm _ _ _ _).trans (sub_eq_zero.mpr (hsum.symm.trans hsum')))
    exact Prod.ext (sub_eq_zero.mp hxy0.1).symm (sub_eq_zero.mp hxy0.2).symm
  · rintro ⟨xy, ⟨hx, hy, z₁, z₂, hz₁, hz₂, rfl⟩, -⟩
    exact (weightOne_eq_add_images.{w} hS hSL hT hTL F hF 𝒜 ℬ hgenA hgenB _).mpr
      ⟨xy.1, xy.2, z₁, z₂, hx, hy, hz₁, hz₂, rfl⟩

end AdequateFunctor.LaurentDomain

end
