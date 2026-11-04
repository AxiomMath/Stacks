module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.TorsionFreeExtension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgetModuleHelpers
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison

/-!
# Extension of coefficients on complexes of sectionwise torsion-free étale sheaves

The previous file carried a *short exact sequence* with sectionwise torsion-free quotient to a
short exact sequence.  This file draws the two consequences for complexes: extension of
coefficients carries an acyclic complex of sectionwise torsion-free abelian sheaves to an acyclic
complex, and a quasi-isomorphism between such complexes to a quasi-isomorphism.

## Main results

* `Stacks.EtaleCohomology.acyclic_map_etaleAbelianSheafExtend_of_isTorsionFree`
* `Stacks.EtaleCohomology.quasiIso_map_etaleAbelianSheafExtend_of_isTorsionFree`

## Implementation notes

Both proofs are the standard ones and both are driven entirely by the short exact sequence
`0 → Z_i → K_i → Z_{i+1} → 0` of an acyclic complex: the cycles are a subobject of a sectionwise
torsion-free sheaf and so sectionwise torsion-free themselves, which is the hypothesis the
previous file's lemma needs.  The quasi-isomorphism statement reduces to the acyclic one for the
mapping cone, whose terms are biproducts of terms of the two complexes -- hence the biproduct
lemma below.

Everything here is stated in the abelian-group spelling and consumes the `ℤ`-module engine only
through `shortExact_map_etaleAbelianSheafExtend_of_isTorsionFree`, so the coefficient-spelling
bridge of the previous file is crossed once and does not reappear.

## References

* [Stacks Project, Tag 0GL6](https://stacks.math.columbia.edu/tag/0GL6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] (X : Scheme.{u})

/-- **A biproduct of two sectionwise torsion-free abelian étale sheaves is sectionwise
torsion-free.**  Needed for the terms of a mapping cone. -/
theorem isTorsionFree_biprod (F G : EtaleAbelianSheaves.{u, r} X)
    (hF : ∀ V, Module.IsTorsionFree ℤ (F.obj.obj V))
    (hG : ∀ V, Module.IsTorsionFree ℤ (G.obj.obj V)) (V : X.Etaleᵒᵖ) :
    Module.IsTorsionFree ℤ ((F ⊞ G).obj.obj V) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro n x hx
  by_cases hn : n = 0
  · exact Or.inl hn
  right
  have mono_smul (H : EtaleAbelianSheaves.{u, r} X)
      (hH : ∀ W, Module.IsTorsionFree ℤ (H.obj.obj W)) : Mono (n • 𝟙 H) := by
    apply (sheafToPresheaf _ _).mono_of_mono_map
    have (W : X.Etaleᵒᵖ) : Mono (((sheafToPresheaf _ _).map (n • 𝟙 H)).app W) := by
      have := hH W
      rw [AddCommGrpCat.mono_iff_injective]
      show Function.Injective (fun y : H.obj.obj W => n • y)
      exact IsSMulRegular.of_ne_zero hn
    exact NatTrans.mono_of_mono_app _
  have := mono_smul F hF
  have := mono_smul G hG
  have hb : n • 𝟙 (F ⊞ G) = biprod.map (n • 𝟙 F) (n • 𝟙 G) := by
    apply biprod.hom_ext <;> simp
  have hm : Mono (n • 𝟙 (F ⊞ G)) := by rw [hb]; infer_instance
  have hi := (AddCommGrpCat.mono_iff_injective ((n • 𝟙 (F ⊞ G)).hom.app V)).mp inferInstance
  change Function.Injective (fun y : (F ⊞ G).obj.obj V => n • y) at hi
  apply hi
  simpa only [smul_zero] using hx

/-- **Extension of coefficients carries an acyclic complex of sectionwise torsion-free abelian
sheaves to an acyclic complex.** -/
theorem acyclic_map_etaleAbelianSheafExtend_of_isTorsionFree
    (K : CochainComplex (EtaleAbelianSheaves.{u, r} X) ℤ) (hK : K.Acyclic)
    (hP : ∀ i V, Module.IsTorsionFree ℤ ((K.X i).obj.obj V)) :
    (((etaleAbelianSheafExtend.{u, r} Λ X).mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  set T := etaleAbelianSheafExtend.{u, r} Λ X with hT
  let S (i : ℤ) := ShortComplex.mk (K.iCycles i) (K.toCycles i (i + 1)) (by
    rw [← cancel_mono (K.iCycles (i + 1))]
    simp)
  have hs (i : ℤ) : ((S i).map T).ShortExact :=
    shortExact_map_etaleAbelianSheafExtend_of_isTorsionFree.{u, r} Λ X (S i)
      (Stacks.Cohomology.ForgetModule.cycles_shortExact K hK i)
      (fun V => ModuleSheafCohomology.isTorsionFree_of_mono _ (K.iCycles (i + 1))
        (hP (i + 1)) V)
  intro j
  obtain ⟨i, rfl⟩ : ∃ i : ℤ, i + 1 = j := ⟨j - 1, by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ i (i + 1) (i + 1 + 1) (by simp) (by simp)]
  have hm : Mono (T.map (K.iCycles (i + 1 + 1))) := (hs (i + 1 + 1)).mono_f
  let S' := ShortComplex.mk (T.map (K.iCycles (i + 1)))
    (T.map (K.d (i + 1) (i + 1 + 1))) (by
      rw [← T.map_comp, K.iCycles_d, T.map_zero])
  let f : (S (i + 1)).map T ⟶ S' :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := T.map (K.iCycles (i + 1 + 1))
      comm₂₃ := by simp [S, S', ← T.map_comp] }
  have hS' : S'.Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono f).mp (hs (i + 1)).exact
  have he : Epi (T.map (K.toCycles i (i + 1))) := (hs i).epi_g
  let f' : (((T.mapHomologicalComplex (.up ℤ)).obj K).sc' i (i + 1) (i + 1 + 1)) ⟶ S' :=
    { τ₁ := T.map (K.toCycles i (i + 1)), τ₂ := 𝟙 _, τ₃ := 𝟙 _
      comm₁₂ := by
        show T.map (K.toCycles i (i + 1)) ≫ T.map (K.iCycles (i + 1)) =
          T.map (K.d i (i + 1)) ≫ 𝟙 _
        rw [← T.map_comp, K.toCycles_i, Category.comp_id] }
  have : Epi f'.τ₁ := he
  -- `f'.τ₂` is the identity, but `f'` is a local definition, so instance search does not reduce
  -- to that at reducible transparency.  `change` states the reduced form, and search succeeds.
  have : IsIso f'.τ₂ := by change IsIso (𝟙 _); infer_instance
  have : Mono f'.τ₃ := by change Mono (𝟙 _); infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono f').mpr hS'

/-- **Extension of coefficients carries a quasi-isomorphism of complexes of sectionwise
torsion-free abelian sheaves to a quasi-isomorphism.** -/
theorem quasiIso_map_etaleAbelianSheafExtend_of_isTorsionFree
    {K L : CochainComplex (EtaleAbelianSheaves.{u, r} X) ℤ} (q : K ⟶ L) [QuasiIso q]
    (hK : ∀ i V, Module.IsTorsionFree ℤ ((K.X i).obj.obj V))
    (hL : ∀ i V, Module.IsTorsionFree ℤ ((L.X i).obj.obj V)) :
    QuasiIso (((etaleAbelianSheafExtend.{u, r} Λ X).mapHomologicalComplex (.up ℤ)).map q) := by
  apply Functor.quasiIso_of_acyclic_mappingCone
  -- The terms of the mapping cone are sectionwise torsion-free, being biproducts of terms of `K`
  -- and `L`.  The comparison isomorphism is named, with its source spelled as a term of
  -- `CochainComplex.mappingCone q`: `HomologicalComplex.homotopyCofiber.XIsoBiprod` states it
  -- with the source spelled `HomologicalComplex.homotopyCofiber.X q i` instead, and although the
  -- two are definitionally equal, `Mono` is then searched for at a spelling no instance matches
  -- at reducible transparency.  The ascription here is what makes `Iso.hom` apply.
  have htf : ∀ (i : ℤ) (V : X.Etaleᵒᵖ),
      Module.IsTorsionFree ℤ (((CochainComplex.mappingCone q).X i).obj.obj V) := by
    intro i V
    have e : (CochainComplex.mappingCone q).X i ≅ K.X (i + 1) ⊞ L.X i :=
      HomologicalComplex.homotopyCofiber.XIsoBiprod q i (i + 1) rfl
    exact ModuleSheafCohomology.isTorsionFree_of_mono X.smallEtaleTopology e.hom
      (isTorsionFree_biprod.{u, r} X (K.X (i + 1)) (L.X i) (hK (i + 1)) (hL i)) V
  have h := acyclic_map_etaleAbelianSheafExtend_of_isTorsionFree.{u, r} Λ X
    (CochainComplex.mappingCone q) (Functor.acyclic_mappingCone q inferInstance) htf
  intro i
  exact (exactAt_iff_of_quasiIsoAt
    (CochainComplex.mappingCone.mapHomologicalComplexIso q
      (etaleAbelianSheafExtend.{u, r} Λ X)).hom i).mp (h i)

end Stacks.EtaleCohomology

end
