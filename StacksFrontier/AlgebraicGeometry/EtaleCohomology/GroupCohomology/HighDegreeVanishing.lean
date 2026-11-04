module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.ForgetCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.Profinite
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# From torsion coefficients in degrees `≥ 2` to arbitrary coefficients in degrees `≥ 3`

Let `G` be a profinite group whose continuous cohomology with *torsion* discrete coefficients
vanishes in every degree `q ≥ 2`. Then its continuous cohomology with *arbitrary* discrete
coefficients vanishes in every degree `q ≥ 3`.

## Main definitions

* `Stacks.GroupCohomology.kernelImageShortComplex`: the short exact sequence
  `0 ⟶ ker φ ⟶ M ⟶ im φ ⟶ 0` of an endomorphism `φ` of a discrete `G`-module.
* `Stacks.GroupCohomology.imageCokernelShortComplex`: the short exact sequence
  `0 ⟶ im φ ⟶ M ⟶ coker φ ⟶ 0`.

## Main results

* `Stacks.GroupCohomology.isZero_continuousGroupCohomology_of_forall_isAddTorsion`: **the
  vanishing in every degree `q ≥ 3` for every discrete `G`-module**, from the vanishing in
  degrees `q ≥ 2` for torsion ones.

## Implementation notes

Multiplication by a positive integer `n` on a discrete `G`-module `M` has torsion kernel and
torsion cokernel — both are killed by `n` — so splitting it as `M ↠ im ↪ M` and running the long
exact sequence twice makes it injective on `H ^q` for `q ≥ 3`: the kernel contributes
`H ^q(ker) = 0`, which makes `H ^q(M) → H ^q(im)` injective, and the cokernel contributes
`H ^(q-1)(coker) = 0`, which makes the connecting map into `H ^q(im)` zero and hence
`H ^q(im) → H ^q(M)` injective. Since every class in positive-degree continuous cohomology of a
profinite group is killed by some positive integer
(`Stacks.GroupCohomology.continuousGroupCohomology_isTorsion`, Stacks 0DV3 part (1)), an
injective multiplication-by-`n` forces the whole group to vanish. The degree `q = 2` is out of
reach this way: it would need `H ¹(coker) = 0`, which the torsion hypothesis does not give.

The long exact sequence is `Stacks.DerivedIndexing.rightDerivedPlusDeltaFunctor`, the
`δ`-functor of Stacks 010Q attached to the right derived functors of the invariants functor; the
two exactness axioms used are `CategoryTheory.DeltaFunctor.exact_map` and
`CategoryTheory.DeltaFunctor.exact_δ₂`. The torsion of the kernel and of the cokernel is read on
carriers, through the exactness and faithfulness of
`Stacks.ContinuousCohomology.continuousGModuleUnderlying`.

## References

* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR): the cohomology groups.
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q): the `δ`-functor whose
  long exact sequence is used twice.
* [Stacks Project, Tag 0DV3](https://stacks.math.columbia.edu/tag/0DV3): part (1), that every
  class is torsion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ContinuousCohomology

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.GroupCohomology

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### The two short exact sequences of an endomorphism -/

/-- **The short exact sequence `0 ⟶ ker φ ⟶ M ⟶ im φ ⟶ 0`** of an endomorphism `φ` of a
discrete `G`-module, the second map being the canonical epimorphism onto the image. -/
def kernelImageShortComplex {M : ContinuousGModule.{u, v} G} (φ : M ⟶ M) :
    ShortComplex (ContinuousGModule.{u, v} G) :=
  ShortComplex.mk (kernel.ι (Abelian.factorThruImage φ)) (Abelian.factorThruImage φ)
    (kernel.condition _)

/-- The sequence `0 ⟶ ker φ ⟶ M ⟶ im φ ⟶ 0` of `kernelImageShortComplex φ` is short exact. -/
theorem kernelImageShortComplex_shortExact {M : ContinuousGModule.{u, v} G} (φ : M ⟶ M) :
    (kernelImageShortComplex φ).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (Abelian.factorThruImage φ)))
    (inferInstanceAs (Mono (kernel.ι (Abelian.factorThruImage φ))))
    (inferInstanceAs (Epi (Abelian.factorThruImage φ)))

/-- **The short exact sequence `0 ⟶ im φ ⟶ M ⟶ coker φ ⟶ 0`** of an endomorphism `φ` of a
discrete `G`-module. -/
def imageCokernelShortComplex {M : ContinuousGModule.{u, v} G} (φ : M ⟶ M) :
    ShortComplex (ContinuousGModule.{u, v} G) :=
  ShortComplex.mk (Abelian.image.ι φ) (cokernel.π φ) (kernel.condition _)

/-- The sequence `0 ⟶ im φ ⟶ M ⟶ coker φ ⟶ 0` of `imageCokernelShortComplex φ` is short
exact. -/
theorem imageCokernelShortComplex_shortExact {M : ContinuousGModule.{u, v} G} (φ : M ⟶ M) :
    (imageCokernelShortComplex φ).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (cokernel.π φ)))
    (inferInstanceAs (Mono (kernel.ι (cokernel.π φ))))
    (inferInstanceAs (Epi (cokernel.π φ)))

/-- The composite of the two middle maps of the two sequences is the endomorphism itself. -/
theorem kernelImageShortComplex_g_comp_imageCokernelShortComplex_f
    {M : ContinuousGModule.{u, v} G} (φ : M ⟶ M) :
    (kernelImageShortComplex φ).g ≫ (imageCokernelShortComplex φ).f = φ :=
  Abelian.image.fac φ

/-! ### The kernel and the cokernel of multiplication by `n` are killed by `n` -/

/-- The underlying map of the monomorphism of a short exact sequence of discrete `G`-modules is
injective. -/
theorem injective_underlying_f {S : ShortComplex (ContinuousGModule.{u, v} G)}
    (hS : S.ShortExact) :
    Function.Injective ((continuousGModuleUnderlying.{u, v} G).map S.f).hom :=
  (hS.map_of_exact (continuousGModuleUnderlying.{u, v} G)).moduleCat_injective_f

/-- The underlying map of the epimorphism of a short exact sequence of discrete `G`-modules is
surjective. -/
theorem surjective_underlying_g {S : ShortComplex (ContinuousGModule.{u, v} G)}
    (hS : S.ShortExact) :
    Function.Surjective ((continuousGModuleUnderlying.{u, v} G).map S.g).hom :=
  (hS.map_of_exact (continuousGModuleUnderlying.{u, v} G)).moduleCat_surjective_g

/-- **The sub-object of a short exact sequence is killed by `n`** as soon as its inclusion dies
against multiplication by `n` on the middle term. -/
theorem nsmul_eq_zero_of_shortExact_f {S : ShortComplex (ContinuousGModule.{u, v} G)}
    (hS : S.ShortExact) {n : ℕ} (hz : S.f ≫ ((n : ℤ) • 𝟙 S.X₂) = 0) (x : S.X₁.obj.obj.V) :
    n • x = 0 := by
  have hu : (n : ℤ) • ((continuousGModuleUnderlying.{u, v} G).map S.f).hom x = 0 :=
    congrArg (fun t : S.X₁ ⟶ S.X₂ ↦ ((continuousGModuleUnderlying.{u, v} G).map t).hom x) hz
  refine injective_underlying_f hS ?_
  exact (map_nsmul ((continuousGModuleUnderlying.{u, v} G).map S.f).hom n x).trans
    (((natCast_zsmul _ n).symm.trans hu).trans
      (map_zero ((continuousGModuleUnderlying.{u, v} G).map S.f).hom).symm)

/-- **The quotient of a short exact sequence is killed by `n`** as soon as multiplication by `n`
on the middle term dies against the projection. -/
theorem nsmul_eq_zero_of_shortExact_g {S : ShortComplex (ContinuousGModule.{u, v} G)}
    (hS : S.ShortExact) {n : ℕ} (hz : ((n : ℤ) • 𝟙 S.X₂) ≫ S.g = 0) (y : S.X₃.obj.obj.V) :
    n • y = 0 := by
  obtain ⟨z, rfl⟩ := surjective_underlying_g hS y
  have hu : ((continuousGModuleUnderlying.{u, v} G).map S.g).hom ((n : ℤ) • z) = 0 :=
    congrArg (fun t : S.X₂ ⟶ S.X₃ ↦ ((continuousGModuleUnderlying.{u, v} G).map t).hom z) hz
  exact (natCast_zsmul _ n).symm.trans
    ((map_zsmul ((continuousGModuleUnderlying.{u, v} G).map S.g).hom (n : ℤ) z).symm.trans hu)

/-- **The kernel of multiplication by `n` is killed by `n`.** -/
theorem nsmul_eq_zero_kernelImage {M : ContinuousGModule.{u, v} G} (n : ℕ)
    (x : (kernelImageShortComplex ((n : ℤ) • 𝟙 M)).X₁.obj.obj.V) : n • x = 0 := by
  refine nsmul_eq_zero_of_shortExact_f (kernelImageShortComplex_shortExact ((n : ℤ) • 𝟙 M))
    ?_ x
  have h : kernel.ι (Abelian.factorThruImage ((n : ℤ) • 𝟙 M)) ≫
      Abelian.factorThruImage ((n : ℤ) • 𝟙 M) ≫ Abelian.image.ι ((n : ℤ) • 𝟙 M) = 0 := by
    rw [← Category.assoc, kernel.condition, zero_comp]
  rwa [Abelian.image.fac] at h

/-- **The cokernel of multiplication by `n` is killed by `n`.** -/
theorem nsmul_eq_zero_imageCokernel {M : ContinuousGModule.{u, v} G} (n : ℕ)
    (y : (imageCokernelShortComplex ((n : ℤ) • 𝟙 M)).X₃.obj.obj.V) : n • y = 0 :=
  nsmul_eq_zero_of_shortExact_g (imageCokernelShortComplex_shortExact ((n : ℤ) • 𝟙 M))
    (cokernel.condition ((n : ℤ) • 𝟙 M)) y

/-! ### The vanishing in degrees `q ≥ 3` -/

/-- **If the continuous cohomology of a profinite group `G` with torsion discrete coefficients
vanishes in every degree `q ≥ 2`, then its continuous cohomology with arbitrary discrete
coefficients vanishes in every degree `q ≥ 3`.** -/
theorem isZero_continuousGroupCohomology_of_forall_isAddTorsion
    (hG : Stacks.Chapter05.Tag_0BR1.IsProfiniteTop G)
    (htor : ∀ N : ContinuousGModule.{u, max u v} G, IsAddTorsion N.obj.obj.V →
      ∀ q : ℕ, 2 ≤ q → IsZero (continuousGroupCohomology.{u, v} G q N))
    (M : ContinuousGModule.{u, max u v} G) (q : ℕ) (hq : 3 ≤ q) :
    IsZero (continuousGroupCohomology.{u, v} G q M) := by
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, q = p + 1 := ⟨q - 1, by omega⟩
  have hp : 2 ≤ p := by omega
  let F := continuousGModuleInvariants.{u, max u v} G
  let Δ := Stacks.DerivedIndexing.rightDerivedPlusDeltaFunctor F
    (Stacks.DerivedIndexing.derivedDeltaFunctorStructure F)
    (Stacks.DerivedIndexing.canonicalδ F) (fun _ _ ↦ rfl)
  apply (IsZero.iff_id_eq_zero _).mpr
  ext x
  obtain ⟨n, hn⟩ :=
    continuousGroupCohomology_isTorsion.{u, v} G hG (p + 1) (by omega) M (x := x)
  have hn' : (n : ℤ) • x = 0 := hn
  have hn0 : (n : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp n.2
  obtain ⟨m, hm0, hmx⟩ : ∃ m : ℕ, 0 < m ∧ (m : ℤ) • x = 0 := by
    refine ⟨(n : ℤ).natAbs, Int.natAbs_pos.mpr hn0, ?_⟩
    rcases Int.natAbs_eq (n : ℤ) with h | h
    · rw [← h]; exact hn'
    · have hmn : (((n : ℤ).natAbs : ℕ) : ℤ) = -(n : ℤ) := by omega
      rw [hmn, neg_smul, hn', neg_zero]
  have hmono1 : Mono ((Δ.functor (p + 1)).map
      (kernelImageShortComplex ((m : ℤ) • 𝟙 M)).g) := by
    refine (ShortComplex.exact_iff_mono _ ?_).1
      (Δ.exact_map (kernelImageShortComplex_shortExact ((m : ℤ) • 𝟙 M)) (p + 1))
    exact (htor _ (fun z ↦ isOfFinAddOrder_iff_nsmul_eq_zero.2
      ⟨m, hm0, nsmul_eq_zero_kernelImage m z⟩) (p + 1) (by omega)).eq_of_src _ _
  have hmono2 : Mono ((Δ.functor (p + 1)).map
      (imageCokernelShortComplex ((m : ℤ) • 𝟙 M)).f) := by
    refine (ShortComplex.exact_iff_mono _ ?_).1
      (Δ.exact_δ₂ (imageCokernelShortComplex_shortExact ((m : ℤ) • 𝟙 M)) p)
    exact (htor _ (fun z ↦ isOfFinAddOrder_iff_nsmul_eq_zero.2
      ⟨m, hm0, nsmul_eq_zero_imageCokernel m z⟩) p hp).eq_of_src _ _
  have hsplit : (Δ.functor (p + 1)).map ((m : ℤ) • 𝟙 M) =
      (Δ.functor (p + 1)).map (kernelImageShortComplex ((m : ℤ) • 𝟙 M)).g ≫
        (Δ.functor (p + 1)).map (imageCokernelShortComplex ((m : ℤ) • 𝟙 M)).f :=
    (congrArg (fun t : M ⟶ M ↦ (Δ.functor (p + 1)).map t)
        (kernelImageShortComplex_g_comp_imageCokernelShortComplex_f
          ((m : ℤ) • 𝟙 M)).symm).trans
      ((Δ.functor (p + 1)).map_comp _ _)
  have hmono : Mono ((Δ.functor (p + 1)).map ((m : ℤ) • 𝟙 M)) := by
    rw [hsplit]
    exact mono_comp' hmono1 hmono2
  have heq : (Δ.functor (p + 1)).map ((m : ℤ) • 𝟙 M) =
      (m : ℤ) • 𝟙 ((Δ.functor (p + 1)).obj M) :=
    ((Δ.functor (p + 1)).map_zsmul (f := 𝟙 M) (r := (m : ℤ))).trans
      (congrArg (fun t ↦ (m : ℤ) • t) ((Δ.functor (p + 1)).map_id M))
  have : Mono ((m : ℤ) • 𝟙 ((Δ.functor (p + 1)).obj M)) := heq ▸ hmono
  apply (AddCommGrpCat.mono_iff_injective
    ((m : ℤ) • 𝟙 ((Δ.functor (p + 1)).obj M))).mp inferInstance
  show (m : ℤ) • x = (m : ℤ) • 0
  rw [hmx, smul_zero]

end Stacks.GroupCohomology

end
