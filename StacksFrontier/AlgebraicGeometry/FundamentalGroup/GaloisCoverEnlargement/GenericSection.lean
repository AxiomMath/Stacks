module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverEnlargement.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.NormalLocalExactSequence
public import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Basic

/-!
# Sections of finite étale covers of normal integral schemes at the generic point

Let `S` be a normal integral locally Noetherian scheme with generic point `η`, `U ⊆ S` an open
containing `η`, and `H ⟶ U` finite étale. A `κ(η)`-point of `H` lying over `η` extends to a
section of `H ⟶ U`.

## Main results

* `AlgebraicGeometry.exists_section_of_genericPoint`.

## References

* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A section of a finite étale cover of a normal integral scheme at the generic point
extends.** Let `S` be normal, integral and locally Noetherian, `U ⊆ S` an open containing the
generic point `η`, and `H ⟶ U` finite étale. A `κ(η)`-point of `H` over `η` extends to a section
of `H ⟶ U`. -/
theorem exists_section_of_genericPoint {S : Scheme.{u}} [IsIntegral S] [IsNormal S]
    [IsLocallyNoetherian S] (U : S.Opens) (hη : genericPoint S ∈ U)
    (H : FiniteEtaleOver U.toScheme) (p : Spec (S.residueField (genericPoint S)) ⟶ H.left)
    (hp : p ≫ H.hom ≫ U.ι = S.fromSpecResidueField (genericPoint S)) :
    ∃ t : U.toScheme ⟶ H.left, t ≫ H.hom = 𝟙 _ := by
  obtain ⟨V, hV, hηV, hVU'⟩ := exists_isAffineOpen_mem_and_subset hη
  have hVU : V ≤ U := hVU'
  have : Nonempty V := ⟨⟨_, hηV⟩⟩
  let R := Γ(S, V)
  let K := S.residueField (genericPoint S)
  let ρ : R ⟶ K := S.presheaf.germ V (genericPoint S) hηV ≫ S.residue (genericPoint S)
  let : Algebra R K := ρ.hom.toAlgebra
  have hres : Function.Bijective (S.residue (genericPoint S)).hom :=
    ⟨RingHom.injective _, IsLocalRing.residue_surjective⟩
  let eK : S.functionField ≃ₐ[R] K :=
    { RingEquiv.ofBijective (S.residue (genericPoint S)).hom hres with
      commutes' := fun _ ↦ rfl }
  have : IsFractionRing R S.functionField := functionField_isFractionRing_of_isAffineOpen S V hV
  have : IsFractionRing R K := IsLocalization.isLocalization_of_algEquiv _ eK
  have : IsIntegrallyClosed Γ(V.toScheme, ⊤) := normal_globalSections V.toScheme
  have : IsIntegrallyClosed R :=
    IsIntegrallyClosed.of_equiv (Scheme.Opens.topIso V).commRingCatIsoToRingEquiv
  let j := S.homOfLE hVU
  have hj : j ≫ U.ι = V.ι := S.homOfLE_ι hVU
  have : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (S.homOfLE hVU))
  have : Nonempty U := ⟨⟨_, hη⟩⟩
  let HV : FiniteEtaleOver V.toScheme := (finiteEtaleBaseChange j).obj H
  let H' : FiniteEtaleOver (Spec (.of R)) := (finiteEtaleBaseChange hV.isoSpec.inv).obj HV
  have hgen : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ hV.isoSpec.inv ≫ V.ι =
      S.fromSpecResidueField (genericPoint S) := by
    change Spec.map ρ ≫ _ = _
    rw [Spec.map_comp, Category.assoc, ← Category.assoc (Spec.map (S.presheaf.germ _ _ _)),
      specMap_germ_isoSpec_inv S _ hV hηV, Scheme.Opens.fromSpecStalkOfMem_ι]
    rfl
  let sV : Spec (.of K) ⟶ HV.left :=
    pullback.lift p (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ hV.isoSpec.inv) (by
      rw [← cancel_mono U.ι, Category.assoc, hp, Category.assoc, Category.assoc, hj, hgen])
  let s : Spec (.of K) ⟶ H'.left :=
    pullback.lift sV (Spec.map (CommRingCat.ofHom (algebraMap R K))) (pullback.lift_snd _ _ _)
  obtain ⟨t', ht'⟩ := exists_section_of_section_fractionField R K H' s (pullback.lift_snd _ _ _)
  let tV : V.toScheme ⟶ HV.left :=
    hV.isoSpec.hom ≫ t' ≫ finiteEtaleBaseChangeProj hV.isoSpec.inv HV
  have htV : tV ≫ HV.hom = 𝟙 _ := by
    simp only [tV, Category.assoc, finiteEtaleBaseChangeProj_comp_hom]
    rw [← Category.assoc t', ht', Category.id_comp, Iso.hom_inv_id]
  have hdense : Dense (Set.range j) := by
    refine IsOpen.dense j.isOpenEmbedding.isOpen_range ⟨j ⟨_, hηV⟩, ⟨_, rfl⟩⟩
  obtain ⟨hff⟩ := nonempty_fullyFaithful_finiteEtaleBaseChange_of_isOpenImmersion j hdense
  let one : FiniteEtaleOver U.toScheme :=
    MorphismProperty.Over.mk ⊤ (𝟙 U.toScheme) ⟨inferInstance, inferInstance⟩
  let m : (finiteEtaleBaseChange j).obj one ⟶ (finiteEtaleBaseChange j).obj H :=
    MorphismProperty.Over.homMk (pullback.snd (𝟙 U.toScheme) j ≫ tV) (by
      change (pullback.snd (𝟙 U.toScheme) j ≫ tV) ≫ HV.hom = _
      rw [Category.assoc, htV, Category.comp_id]
      rfl) trivial
  exact ⟨(hff.preimage m).left, MorphismProperty.Over.w (hff.preimage m)⟩

end AlgebraicGeometry
