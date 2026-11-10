module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Data.Finsupp.Encodable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ModuleSupportProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetUnion
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupportSerre

/-!
# Being proper over a base

Section 0CZB of the Stacks project ([Stacks, Tag 0CZB]), the analogue for algebraic spaces of
Section 0CYK, introduces for a morphism `f : X ⟶ Y` of algebraic spaces locally of finite type the
notion of a closed subset `T ⊆ |X|` being *proper over `Y`* (Definition 0CZD,
`AlgebraicGeometry.Space.IsProperOver`), resting on the equivalence of the conditions of
Lemma 0CZC (`AlgebraicGeometry.Space.isProper_reducedClosedSubspace_iff_exists` and
`AlgebraicGeometry.Space.exists_isProper_closedSubspace_iff_forall`). This file registers that
notion and the further lemmas of the section (Lemmas 0CZE to 0CZK) under the section's tag, and
proves the remark following Definition 0CZD: Lemma 0CZC is false without the hypothesis that `f`
is locally of finite type (`AlgebraicGeometry.Space.not_tfae_isProper_closedSubspace`).

## Main results

* `AlgebraicGeometry.Space.not_tfae_isProper_closedSubspace`: over every big fppf site there is a
  morphism of algebraic spaces `f : X ⟶ Y`, not locally of finite type, and a closed subset `T`
  of `|X|` for which the three conditions of Lemma 0CZC are not equivalent.

## Implementation notes

The counterexample is `f : Spec A ⟶ Spec k` for `k = 𝔽₂` and `A = k ⊕ k^{(ℕ)}`, the trivial
square-zero extension of `k` by a vector space of countably infinite dimension (that is,
`k[ε₀, ε₁, …]` with all products `εᵢεⱼ` zero), and `T = |X|`. The closed subscheme `Spec k`
cut out by the square-zero ideal has all the points of `Spec A` and is proper over `Spec k`,
being isomorphic to it; the whole of `X`, a closed subspace with the same points, is not, since
`A` is not a finitely generated `k`-algebra (`TrivSqZeroExt.module_finite_of_finiteType`). So
condition (2) of Lemma 0CZC holds and condition (3) fails. Both `Spec k` and `Spec A` are
countable, so they lie in every big fppf site.

## References

* [Stacks Project, Section 0CZB](https://stacks.math.columbia.edu/tag/0CZB)
* [Stacks Project, Tag 0CZC](https://stacks.math.columbia.edu/tag/0CZC)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
-/

@[expose] public section

namespace AlgebraicGeometry.Space

add_to_stacks 0CZB "the notion of the section: a closed subset T ⊆ |X| is proper over Y, for f \
  locally of finite type, when the reduced induced closed subspace on T is proper over Y \
  (Definition 0CZD)" AlgebraicGeometry.Space.IsProperOver

add_to_stacks 0CZB "the equivalence of the conditions of Lemma 0CZC that the notion rests on: the \
  reduced induced subspace is proper over Y iff some closed subspace with points T is"
  AlgebraicGeometry.Space.isProper_reducedClosedSubspace_iff_exists

add_to_stacks 0CZB "the equivalence of the conditions of Lemma 0CZC that the notion rests on: some \
  closed subspace with points T is proper over Y iff every one is"
  AlgebraicGeometry.Space.exists_isProper_closedSubspace_iff_forall

add_to_stacks 0CZB "Lemma 0CZE of the section: a closed subset of a closed subset proper over Y \
  is proper over Y" AlgebraicGeometry.Space.isProperOver_of_subset

add_to_stacks 0CZB "Lemma 0CZF of the section: the inverse image of a closed subset proper over \
  Y under a base change is proper over the new base" AlgebraicGeometry.Space.isProperOver_preimage

add_to_stacks 0CZB "Lemma 0CZG of the section: images of closed subsets proper over the base, \
  under a universally closed morphism"
  AlgebraicGeometry.Space.isProperOver_image_of_universallyClosed

add_to_stacks 0CZB "Lemma 0CZG of the section: images of closed subsets proper over the base, \
  under a morphism to a space separated over the base"
  AlgebraicGeometry.Space.isProperOver_image_of_isSeparated

add_to_stacks 0CZB "Lemma 0CZG of the section: inverse images of closed subsets proper over the \
  base, under a proper morphism" AlgebraicGeometry.Space.isProperOver_preimage_of_isProper

add_to_stacks 0CZB "Lemma 0CZH of the section: a finite union of closed subsets proper over Y is \
  proper over Y" AlgebraicGeometry.Space.isProperOver_iUnion

add_to_stacks 0CZB "Lemma 0CZI of the section: the equivalent conditions for a module to have \
  support proper over Y" AlgebraicGeometry.Space.hasProperSupport_tfae

add_to_stacks 0CZB "Lemma 0CZJ of the section: support proper over the base is preserved by \
  base change" AlgebraicGeometry.Space.isProperOver_supportOfSheaf_modulePullback

add_to_stacks 0CZB "Lemma 0CZK of the section, part (2): the coherent modules with support \
  proper over Y form a Serre subcategory" AlgebraicGeometry.Space.isSerreClass_isCoherentProperOver

end AlgebraicGeometry.Space

universe u

/-! ### A square-zero extension by a module that is not finite is not of finite type -/

namespace TrivSqZeroExt

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
  [IsCentralScalar R M]

/-- The second coordinate of an element of the subalgebra of `R ⊕ M` generated by a set `s` lies
in the `R`-span of the second coordinates of the elements of `s`. -/
theorem snd_mem_span_of_mem_adjoin {s : Set (TrivSqZeroExt R M)} {a : TrivSqZeroExt R M}
    (ha : a ∈ Algebra.adjoin R s) : a.snd ∈ Submodule.span R (snd '' s) := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | algebraMap r => rw [algebraMap_eq_inl, snd_inl]; exact zero_mem _
  | add x y _ _ hx hy => rw [snd_add]; exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [snd_mul, op_smul_eq_smul]
    exact add_mem (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hx)

/-- If the trivial square-zero extension `R ⊕ M` is a finitely generated `R`-algebra, then `M`
is a finite `R`-module. -/
theorem module_finite_of_finiteType [Algebra.FiniteType R (TrivSqZeroExt R M)] :
    Module.Finite R M := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := TrivSqZeroExt R M)
  refine ⟨⟨s.image snd, eq_top_iff.2 fun m _ ↦ ?_⟩⟩
  have hm : (inr m : TrivSqZeroExt R M) ∈ Algebra.adjoin R (s : Set (TrivSqZeroExt R M)) :=
    hs ▸ Algebra.mem_top
  rw [Finset.coe_image]
  simpa using snd_mem_span_of_mem_adjoin hm

end TrivSqZeroExt

/-! ### Lemma 0CZC fails without local finite type -/

namespace AlgebraicGeometry.Space

open CategoryTheory

attribute [local instance] pointTopology

/-- The field `𝔽₂`, in the universe of the schemes of a big fppf site. -/
abbrev squareZeroCounterexampleField : Type u := ULift.{u} (ZMod 2)

/-- The `𝔽₂`-algebra `𝔽₂ ⊕ 𝔽₂^{(ℕ)}`, that is `𝔽₂[ε₀, ε₁, …]` with all products `εᵢεⱼ` zero:
the trivial square-zero extension of `𝔽₂` by a vector space of countably infinite dimension. -/
abbrev squareZeroCounterexampleAlgebra : Type u :=
  TrivSqZeroExt squareZeroCounterexampleField.{u} (ℕ →₀ squareZeroCounterexampleField.{u})

/-- `𝔽₂ ⊕ 𝔽₂^{(ℕ)}` is not a finitely generated `𝔽₂`-algebra. -/
theorem not_finiteType_squareZeroCounterexampleAlgebra :
    ¬ Algebra.FiniteType squareZeroCounterexampleField.{u}
      squareZeroCounterexampleAlgebra.{u} := by
  intro h
  have := TrivSqZeroExt.module_finite_of_finiteType (R := squareZeroCounterexampleField.{u})
    (M := ℕ →₀ squareZeroCounterexampleField.{u})
  exact not_finite_iff_infinite.2 inferInstance
    (Module.Finite.finite_basis (Finsupp.basisSingleOne (R := squareZeroCounterexampleField.{u})
      (ι := ℕ)))

/-- The spectrum of a countable ring lies in every big fppf site. -/
theorem _root_.AlgebraicGeometry.BigFppfSite.contains_spec_of_countable (B : BigFppfSite.{u})
    (R : CommRingCat.{u}) [Countable R] : B.Contains (Spec R) := by
  rw [BigFppfSite.Contains, Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff (lt_of_le_of_lt Cardinal.mk_le_aleph0 B.aleph0_lt_cutoff)

/-- The inclusion of the range of a monomorphism `yoneda.map j` is `yoneda.map j` precomposed with
the inverse of the isomorphism onto its range. -/
theorem range_yoneda_map_ι_eq {C : Type*} [Category C] {R U : C} (j : R ⟶ U)
    [Mono (yoneda.map j)] :
    (Subfunctor.range (yoneda.map j)).ι =
      inv (Subfunctor.toRange (yoneda.map j)) ≫ yoneda.map j := by
  rw [IsIso.eq_inv_comp, Subfunctor.toRange_ι]

/-- **Lemma 0CZC fails without local finite type** (the remark after Definition 0CZD, Section
0CZB). Over every big fppf site there are a scheme `S`, a morphism `f : X ⟶ Y` of algebraic spaces
over `S` which is not locally of finite type, and a closed subset `T ⊆ |X|` for which the three
conditions of Lemma 0CZC are not equivalent: (1) the reduced induced closed subspace on `T` is
proper over `Y`, (2) some closed subspace with points `T` is, (3) every one is. -/
@[stacks 0CZB "the remark after Definition 0CZD: Lemma 0CZC is false if f is not locally of \
finite type"]
theorem not_tfae_isProper_closedSubspace (B : BigFppfSite.{u}) :
    ∃ (S : Scheme.{u}) (hS : B.Contains S) (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (hX : IsAlgebraicSpace B S hS X) (_hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
      (T : Set (points B S hS X)) (hT : IsClosed T),
      ¬ IsLocallyOfFiniteType B S hS f ∧
      ¬ [IsProper B S hS ((reducedClosedSubspace B S hS X hX T hT).ι ≫ f),
          ∃ (Z : Subfunctor X) (_ : IsClosedSubspace B S hS Z),
            Set.range (pointsMap B S hS Z.toFunctor Z.ι) = T ∧ IsProper B S hS (Z.ι ≫ f),
          ∀ (Z : Subfunctor X) (_ : IsClosedSubspace B S hS Z),
            Set.range (pointsMap B S hS Z.toFunctor Z.ι) = T →
              IsProper B S hS (Z.ι ≫ f)].TFAE := by
  let k := squareZeroCounterexampleField.{u}
  let A := squareZeroCounterexampleAlgebra.{u}
  let S : Scheme.{u} := Spec (.of k)
  have : Countable (CommRingCat.of A) := inferInstanceAs (Countable (k × (ℕ →₀ k)))
  have hS : B.Contains S := B.contains_spec_of_countable (.of k)
  have hA : B.Contains (Spec (.of A)) := B.contains_spec_of_countable (.of A)
  let ι : CommRingCat.of k ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap k A)
  let π : CommRingCat.of A ⟶ CommRingCat.of k :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom k k (ℕ →₀ k)).toRingHom
  have hιπ : ι ≫ π = 𝟙 _ := by ext; rfl
  let U : BigFppfOver B S hS := siteObject B S hS hA (Spec.map ι)
  let V : BigFppfOver B S hS := siteObject B S hS hS (𝟙 S)
  have hπι : Spec.map π ≫ Spec.map ι = 𝟙 S := by rw [← Spec.map_comp, hιπ, Spec.map_id]
  let p : U ⟶ V :=
    Over.homMk (ObjectProperty.homMk (Spec.map ι)) (ObjectProperty.hom_ext _ (Category.comp_id _))
  let j : V ⟶ U := Over.homMk (ObjectProperty.homMk (Spec.map π)) (ObjectProperty.hom_ext _ hπι)
  have hjp : j ≫ p = 𝟙 V := Over.OverMorphism.ext (ObjectProperty.hom_ext _ hπι)
  have hpj : (BigFppfOver.toScheme B S hS).map p = Spec.map ι := rfl
  have hj : (BigFppfOver.toScheme B S hS).map j = Spec.map π := rfl
  have : IsSplitMono j := ⟨⟨p, hjp⟩⟩
  have hp : ¬ IsLocallyOfFiniteType B S hS (yoneda.map p) := by
    rw [isLocallyOfFiniteType_yoneda_map_iff, hpj,
      HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    change ¬ (algebraMap k A).FiniteType
    rw [RingHom.finiteType_algebraMap]
    exact not_finiteType_squareZeroCounterexampleAlgebra
  have hπsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map j) := by
    rw [hj]
    refine (PrimeSpectrum.isHomeomorph_comap π.hom (fun x ↦ ⟨1, one_pos, ?_⟩) ?_).surjective
    · exact ⟨TrivSqZeroExt.inl x, (pow_one x).symm⟩
    · intro a ha
      have ha' : a = TrivSqZeroExt.inr a.snd := TrivSqZeroExt.ext (show a.fst = 0 from ha) rfl
      refine ⟨2, ?_⟩
      rw [ha', pow_two, TrivSqZeroExt.inr_mul_inr]
      exact zero_mem _
  have hrange : ∀ {R : BigFppfOver B S hS} (i : R ⟶ U) [Mono (yoneda.map i)],
      Function.Surjective ((BigFppfOver.toScheme B S hS).map i) →
        Set.range (pointsMap B S hS (Subfunctor.range (yoneda.map i)).toFunctor
          (Subfunctor.range (yoneda.map i)).ι) = Set.univ := by
    intro R i _ hi
    rw [range_yoneda_map_ι_eq, pointsMap_comp, Set.range_eq_univ]
    exact ((surjective_pointsMap_yoneda_iff B S hS i).2 hi).comp
      (pointsMap_surjective_of_isIso B S hS _)
  refine ⟨S, hS, yoneda.obj U, yoneda.obj V, isAlgebraicSpace_yoneda B S hS U,
    isAlgebraicSpace_yoneda B S hS V, yoneda.map p, Set.univ, isClosed_univ, hp, fun h ↦ ?_⟩
  rw [List.tfae_cons_cons, List.tfae_cons_cons] at h
  have hπs : Function.Surjective π.hom := fun x ↦ ⟨TrivSqZeroExt.inl x, rfl⟩
  have hjc : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j) := by
    rw [hj]
    exact IsClosedImmersion.spec_of_surjective π hπs
  have hidc :
      AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (𝟙 U)) := by
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  have hids : Function.Surjective ((BigFppfOver.toScheme B S hS).map (𝟙 U)) := by
    rw [CategoryTheory.Functor.map_id]
    exact Function.surjective_id
  have hZ : IsProper B S hS ((Subfunctor.range (yoneda.map j)).ι ≫ yoneda.map p) := by
    rw [range_yoneda_map_ι_eq, Category.assoc, ← Functor.map_comp, hjp,
      CategoryTheory.Functor.map_id, Category.comp_id]
    exact isProper_of_isIso B S hS _
  have h3 := h.2.1.1 ⟨Subfunctor.range (yoneda.map j),
    isClosedSubspace_range_yoneda_map B S hS j hjc, hrange j hπsurj, hZ⟩
    (Subfunctor.range (yoneda.map (𝟙 U))) (isClosedSubspace_range_yoneda_map B S hS (𝟙 U) hidc)
    (hrange (𝟙 U) hids)
  rw [range_yoneda_map_ι_eq, Category.assoc, isProper_isIso_comp_iff, CategoryTheory.Functor.map_id,
    Category.id_comp] at h3
  exact hp h3.2.1.1

end AlgebraicGeometry.Space

end
