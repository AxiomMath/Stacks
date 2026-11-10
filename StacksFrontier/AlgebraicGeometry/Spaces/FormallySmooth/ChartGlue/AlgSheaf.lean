module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.AlgFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FormallyEtale
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas

/-!
# The functor of points over a section satisfies descent along faithfully flat algebras

Let `X` and `Y` be sheaves on the big fppf site over `S`, let `f : X ⟶ Y` and let `y` be a section
of `Y` over an affine object `T'`. For a faithfully flat, finitely presented map `C → D` of
algebras over `A' = Γ(T', ⊤)`, the functor of points over `y` is separated along `C → D` and
satisfies the sheaf condition along it, with the double intersection read through `D ⊗[C] D`.

## Main results

* `AlgebraicGeometry.Space.ChartGlue.specMap_mem_topology`: the spectrum of a faithfully flat,
  finitely presented map generates a covering sieve.
* `AlgebraicGeometry.Space.ChartGlue.eq_of_map_specMap_eq`: separation.
* `AlgebraicGeometry.Space.ChartGlue.exists_of_map_specMap_eq`: the sheaf condition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space.ChartGlue

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T' : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]

section Cover

variable {C D : Type u} [CommRing C] [Algebra (ringOf B S hS T') C] [CommRing D]
  [Algebra (ringOf B S hS T') D] (hC : B.Contains (Spec (CommRingCat.of C)))
  (hD : B.Contains (Spec (CommRingCat.of D))) (φ : C →ₐ[ringOf B S hS T'] D)

/-- **The spectrum of a faithfully flat, finitely presented algebra map generates a covering
sieve.** -/
theorem specMap_mem_topology (hff : (φ : C →+* D).FaithfullyFlat)
    (hfp : (φ : C →+* D).FinitePresentation) :
    Sieve.generate (Presieve.singleton (specMap B S hS T' hC hD φ)) ∈
      BigFppfOver.topology B S hS (specObj B S hS T' C hC) := by
  have hflat : Flat (Spec.map (CommRingCat.ofHom (φ : C →+* D))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]; exact hff.flat
  have hlfp : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (φ : C →+* D))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]; exact hfp
  have hsurj : Function.Surjective (Spec.map (CommRingCat.ofHom (φ : C →+* D))) :=
    (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.1 hff).2
  have h := mem_topology_of_family B S hS (U := specObj B S hS T' C hC) (I := PUnit.{u + 2})
    (fun _ ↦ B.obj hD) (fun _ ↦ (specMap B S hS T' hC hD φ).left) (fun _ ↦ hflat)
    (fun _ ↦ hlfp) (fun x ↦ ⟨PUnit.unit, hsurj x⟩)
  refine (BigFppfOver.topology B S hS).superset_covering ?_ h
  rintro W k ⟨V, a, b, ⟨⟩, rfl⟩
  let c : Over.mk ((specMap B S hS T' hC hD φ).left ≫ (specObj B S hS T' C hC).hom) ⟶
      specObj B S hS T' D hD := Over.homMk (𝟙 _) (by simp [Over.w])
  refine ⟨_, a ≫ c, specMap B S hS T' hC hD φ, Presieve.singleton.mk, ?_⟩
  apply (BigFppfOver.toScheme B S hS).map_injective
  simp only [Functor.map_comp]
  congr 1

end Cover

section Separation

variable {C D : Type u} [CommRing C] [Algebra (ringOf B S hS T') C] [CommRing D]
  [Algebra (ringOf B S hS T') D] (hC : B.Contains (Spec (CommRingCat.of C)))
  (hD : B.Contains (Spec (CommRingCat.of D))) (φ : C →ₐ[ringOf B S hS T'] D)
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)

include hF in
/-- **Separation along a faithfully flat, finitely presented algebra map.** -/
theorem eq_of_map_specMap_eq (hff : (φ : C →+* D).FaithfullyFlat)
    (hfp : (φ : C →+* D).FinitePresentation) (y₁ y₂ : F.obj (op (specObj B S hS T' C hC)))
    (h : F.map (specMap B S hS T' hC hD φ).op y₁ = F.map (specMap B S hS T' hC hD φ).op y₂) :
    y₁ = y₂ := by
  have key := Space.hom_ext_of_mem_topology (BigFppfOver.topology B S hS) hF _
    (specMap_mem_topology B S hS T' hC hD φ hff hfp)
    (c := yonedaEquiv.symm y₁) (d := yonedaEquiv.symm y₂) (fun Z e he ↦ by
      obtain ⟨W, g, k, ⟨⟩, rfl⟩ := he
      rw [yonedaEquiv_symm_naturality_left, yonedaEquiv_symm_naturality_left]
      congr 1
      rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, h])
  exact yonedaEquiv.symm.injective key

end Separation

section Glue

variable {D : Type u} [CommRing D] [Algebra (ringOf B S hS T') D]
  (hA : B.Contains (Spec (CommRingCat.of (ringOf B S hS T'))))
  (hD : B.Contains (Spec (CommRingCat.of D)))
  (hDD : B.Contains (Spec (CommRingCat.of (D ⊗[ringOf B S hS T'] D))))
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The two projections of `Spec (D ⊗ D)` and their pullback property. -/
lemma isPullback_specMap_tensor :
    IsPullback (Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeLeft :
        D →ₐ[ringOf B S hS T'] D ⊗[ringOf B S hS T'] D) : D →+* D ⊗[ringOf B S hS T'] D)))
      (Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
        D →ₐ[ringOf B S hS T'] D ⊗[ringOf B S hS T'] D) : D →+* D ⊗[ringOf B S hS T'] D)))
      (Spec.map (CommRingCat.ofHom (algebraMap (ringOf B S hS T') D)))
      (Spec.map (CommRingCat.ofHom (algebraMap (ringOf B S hS T') D))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct (ringOf B S hS T') D D)

include hF in
/-- **The sheaf condition along `A' → D`, read through `D ⊗[A'] D`.** -/
theorem exists_of_map_specMap_eq (hff : (algebraMap (ringOf B S hS T') D).FaithfullyFlat)
    (hfp : (algebraMap (ringOf B S hS T') D).FinitePresentation)
    (z : F.obj (op (specObj B S hS T' D hD)))
    (h : F.map (specMap B S hS T' hD hDD Algebra.TensorProduct.includeLeft).op z =
      F.map (specMap B S hS T' hD hDD Algebra.TensorProduct.includeRight).op z) :
    ∃ z₀ : F.obj (op (specObj B S hS T' (ringOf B S hS T') hA)),
      F.map (specMap B S hS T' hA hD (Algebra.ofId _ D)).op z₀ = z := by
  have hcov := specMap_mem_topology B S hS T' hA hD (Algebra.ofId _ D) hff hfp
  have hcov' : Sieve.ofArrows (fun _ : PUnit.{1} ↦ specObj B S hS T' D hD)
      (fun _ ↦ specMap B S hS T' hA hD (Algebra.ofId _ D)) ∈
        BigFppfOver.topology B S hS (specObj B S hS T' _ hA) := by
    refine (BigFppfOver.topology B S hS).superset_covering ?_ hcov
    rintro W k ⟨V, a, b, ⟨⟩, rfl⟩
    exact ⟨_, a, _, ⟨PUnit.unit⟩, rfl⟩
  obtain ⟨d, hd⟩ := Space.exists_glue_of_mem_topology (BigFppfOver.topology B S hS) hF
    (fun _ : PUnit.{1} ↦ specObj B S hS T' D hD)
    (fun _ ↦ specMap B S hS T' hA hD (Algebra.ofId _ D))
    hcov' (fun _ ↦ yonedaEquiv.symm z) (fun _ _ Z s t hst ↦ by
      have hst' : (BigFppfOver.toScheme B S hS).map s ≫
          Spec.map (CommRingCat.ofHom (algebraMap (ringOf B S hS T') D)) =
          (BigFppfOver.toScheme B S hS).map t ≫
            Spec.map (CommRingCat.ofHom (algebraMap (ringOf B S hS T') D)) := by
        have := congrArg (BigFppfOver.toScheme B S hS).map hst
        rw [Functor.map_comp, Functor.map_comp, toScheme_map_specMap] at this
        exact this
      let l' := (isPullback_specMap_tensor B S hS T').lift
        ((BigFppfOver.toScheme B S hS).map s) ((BigFppfOver.toScheme B S hS).map t) hst'
      have hl₁ := (isPullback_specMap_tensor (D := D) B S hS T').lift_fst _ _ hst'
      have hl₂ := (isPullback_specMap_tensor (D := D) B S hS T').lift_snd _ _ hst'
      obtain ⟨l, hl⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS
        (Y := specObj B S hS T' (D ⊗[ringOf B S hS T'] D) hDD) l' (by
          change l' ≫ specStr B S hS T' _ ≫ B.inclusion.map T'.hom = _
          rw [← specMap_comm B S hS T' (Algebra.TensorProduct.includeLeft :
            D →ₐ[ringOf B S hS T'] D ⊗[ringOf B S hS T'] D), Category.assoc]
          rw [← Category.assoc, hl₁]
          have := congrArg B.inclusion.map (Over.w s)
          rw [Functor.map_comp] at this
          exact this)
      obtain ⟨hs, ht⟩ : l ≫ specMap B S hS T' hD hDD Algebra.TensorProduct.includeLeft = s ∧
          l ≫ specMap B S hS T' hD hDD Algebra.TensorProduct.includeRight = t := by
        refine ⟨(BigFppfOver.toScheme B S hS).map_injective ?_,
          (BigFppfOver.toScheme B S hS).map_injective ?_⟩ <;>
        rw [Functor.map_comp, hl, toScheme_map_specMap]
        exacts [hl₁, hl₂]
      rw [yonedaEquiv_symm_naturality_left, yonedaEquiv_symm_naturality_left]
      congr 1
      rw [← hs, ← ht, op_comp, op_comp, Functor.map_comp_apply,
        Functor.map_comp_apply, h])
  refine ⟨yonedaEquiv d, ?_⟩
  rw [yonedaEquiv_naturality, hd PUnit.unit, Equiv.apply_symm_apply]

end Glue

end AlgebraicGeometry.Space.ChartGlue

end
