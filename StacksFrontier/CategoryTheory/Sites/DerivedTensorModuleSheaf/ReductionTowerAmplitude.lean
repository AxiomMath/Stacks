module

public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.ReductionTower
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.TorAmplitude
import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Constant

/-!
# Cohomological bounds along the tower of derived reductions

Let `(C, J)` be a site, `Λ` a commutative ring, `I ⊆ Λ` a finitely generated ideal and `K` an
object of `D(C, Λ)` such that `K ⊗_Λ^L Λ/I` has Tor amplitude in a set `S` of degrees. Then every
term `Kₙ = K ⊗_Λ^L \underline{Λ/Iⁿ}` of the tower of derived reductions has vanishing cohomology
sheaves off `S`, and in a degree `i` with `i + 1 ∉ S` the transition maps `Hⁱ(Kₙ₊₁) ⟶ Hⁱ(Kₙ)`
are epimorphisms.

Both statements come from the vanishing of `Hⁱ(G ⊗_Λ^L K)` off `S` for every sheaf `G` killed by
a power of `I`
(`Stacks.ModuleSheaf.HasTorAmplitude.isZero_homology_single_tensor_of_smul_id_eq_zero`): the
sheaf `\underline{Λ/Iⁿ}` is killed by `Iⁿ`, and the transition map
`\underline{Λ/Iⁿ⁺¹} ⟶ \underline{Λ/Iⁿ}` is an epimorphism whose kernel is killed by `Iⁿ⁺¹`, so
that tensoring the short exact sequence it defines with `K` gives a distinguished triangle whose
connecting map in degree `i` lands in `Hⁱ⁺¹(ker ⊗_Λ^L K) = 0`.

## Main results

* `Stacks.ModuleSheaf.smul_id_constantAdicQuotientTower_obj`: `\underline{M/IⁿM}` is killed by
  `Iⁿ`.
* `Stacks.ModuleSheaf.isZero_homology_derivedReductionTower_obj`: `Hⁱ(Kₙ) = 0` for `i ∉ S`.
* `Stacks.ModuleSheaf.epi_homology_derivedReductionTower_map`: `Hⁱ(Kₙ₊₁) ⟶ Hⁱ(Kₙ)` is an
  epimorphism when `i + 1 ∉ S`.

## References

* [Stacks Project, Tag 09C2](https://stacks.math.columbia.edu/tag/09C2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Pretriangulated

universe t t' w v u

namespace Stacks.ModuleSheaf

open AlgebraicGeometry.ProEtale (surjective_adicQuotient_transitionMap)

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory monoidalClosed
  CochainComplex.braidedCategory derivedMonoidal derivedSymmetric

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {Λ : Type w} [CommRing Λ] [UnivLE.{max u v, w}] (I : Ideal Λ)

/-- **The constant sheaf `\underline{M/IⁿM}` is killed by `Iⁿ`**, as `M/IⁿM` is. -/
theorem smul_id_constantAdicQuotientTower_obj (M : ModuleCat.{w} Λ) (n : ℕ) {x : Λ}
    (hx : x ∈ I ^ n) : x • 𝟙 ((constantAdicQuotientTower J Λ I M).obj ⟨n⟩) = 0 := by
  have h : x • 𝟙 ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem Λ I M).obj ⟨n⟩) = 0 := by
    ext y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (I ^ n • (⊤ : Submodule Λ M)) y
    exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul hx Submodule.mem_top)
  change x • 𝟙 ((constantSheaf J (ModuleCat.{w} Λ)).obj
    ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem Λ I M).obj ⟨n⟩)) = 0
  rw [← (constantSheaf J (ModuleCat.{w} Λ)).map_id, ← constantSheaf_map_smul, h,
    Functor.map_zero]

variable [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]
  [HasDerivedCategory.{t'} (Sheaf J (ModuleCat.{w} (Λ ⧸ I)))]

/-- **The reductions vanish off the Tor amplitude of the first one.** If `K ⊗_Λ^L Λ/I` has Tor
amplitude in `S`, then every term `K ⊗_Λ^L \underline{Λ/Iⁿ}` of the tower of derived reductions
has vanishing cohomology sheaves in the degrees outside `S`. -/
theorem isZero_homology_derivedReductionTower_obj (hI : I.FG)
    {K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))} {S : Set ℤ}
    (h : HasTorAmplitude ((derivedExtendScalars J (Ideal.Quotient.mk I)).obj K) S) (n : ℕ)
    {i : ℤ} (hi : i ∉ S) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj ((derivedReductionTower J Λ I K).obj ⟨n⟩)) :=
  (h.isZero_homology_single_tensor_of_smul_id_eq_zero I hI n _
    (fun _ hx => smul_id_constantAdicQuotientTower_obj I _ n hx) hi).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso (β_ _ _))

/-- **The transition maps of the reductions are surjective on cohomology below a gap.** If
`K ⊗_Λ^L Λ/I` has Tor amplitude in `S` and `i + 1 ∉ S`, then every transition map
`Hⁱ(K ⊗_Λ^L \underline{Λ/Iⁿ⁺¹}) ⟶ Hⁱ(K ⊗_Λ^L \underline{Λ/Iⁿ})` is an epimorphism: its cokernel
injects into `Hⁱ⁺¹` of `K` tensored with the kernel of `\underline{Λ/Iⁿ⁺¹} ⟶ \underline{Λ/Iⁿ}`,
a sheaf killed by `Iⁿ⁺¹`. -/
theorem epi_homology_derivedReductionTower_map (hI : I.FG)
    {K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))} {S : Set ℤ}
    (h : HasTorAmplitude ((derivedExtendScalars J (Ideal.Quotient.mk I)).obj K) S) (n : ℕ)
    {i : ℤ} (hi : i + 1 ∉ S) :
    Epi ((DerivedCategory.homologyFunctor _ i).map
      ((derivedReductionTower J Λ I K).map (homOfLE (Nat.le_succ n)).op)) := by
  obtain ⟨s, hs⟩ := exists_commShift_isTriangulated_tensorLeft J Λ K
  let := s
  let φ := (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem Λ I (ModuleCat.of Λ Λ)).map
    (homOfLE (Nat.le_succ n)).op
  have : Epi φ := (ModuleCat.epi_iff_surjective _).2
    (surjective_adicQuotient_transitionMap Λ I _ n)
  let g := (constantSheaf J (ModuleCat.{w} Λ)).map φ
  have : PreservesFiniteColimits (constantSheaf J (ModuleCat.{w} Λ)) :=
    preservesFiniteColimits_constantSheaf J Λ
  have : Epi g := (constantSheaf J (ModuleCat.{w} Λ)).map_epi φ
  have hSc : (ShortComplex.mk (kernel.ι g) g (kernel.condition g)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel g))
      inferInstance inferInstance
  have hT := (tensorLeft K).map_distinguished _ hSc.singleTriangle_distinguished
  refine (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hT i (i + 1) rfl).2 ?_
  have hker : ∀ x ∈ I ^ (n + 1), x • 𝟙 (kernel g) = 0 := fun x hx ↦ by
    have h0 := smul_id_constantAdicQuotientTower_obj (J := J) I (ModuleCat.of Λ Λ) (n + 1) hx
    rw [← cancel_mono (kernel.ι g), Linear.smul_comp, Category.id_comp, zero_comp,
      ← Category.comp_id (kernel.ι g), ← Linear.comp_smul]
    exact (congrArg (kernel.ι g ≫ ·) h0).trans comp_zero
  exact ((h.isZero_homology_single_tensor_of_smul_id_eq_zero I hI (n + 1) _ hker hi).of_iso
    ((DerivedCategory.homologyFunctor _ (i + 1)).mapIso (β_ _ _))).eq_of_tgt _ _

end Stacks.ModuleSheaf
