module

public import StacksFrontier.AlgebraicGeometry.Cohomology.SectionsSurjective
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.ProperMapping
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.CohomologyBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AffineCovering

/-!
# Generation of the high tensor powers by the sections of one power

Let `X` be a scheme, `ℒ` an invertible `𝒪_X`-module, and `s_1, …, s_m` global sections of
`ℒ^{⊗ N}` generating it.  If `H¹(X, 𝒦 ⊗ ℒ^{⊗ k}) = 0`, where `𝒦` is the kernel of
`(s_i) : 𝒪_X^{⊕ m} ⟶ ℒ^{⊗ N}`, then every global section of `ℒ^{⊗ (N + k)}` is a combination
`Σ s_i · a_i` with `a_i` global sections of `ℒ^{⊗ k}`, the product being that of the Laurent
algebra `⨁_{n ∈ ℤ} ℒ^{⊗ n}`.

Tensoring the presentation `0 ⟶ 𝒦 ⟶ 𝒪_X^{⊕ m} ⟶ ℒ^{⊗ N} ⟶ 0` with the invertible `ℒ^{⊗ k}` is
exact, and the vanishing of `H¹` of the twisted kernel makes the twisted presentation surjective
on global sections.  This is the argument by which the source proves the finite generation of
the section ring of an ample invertible module ([Stacks, Tag 0B5T] (1)), which the proof of
[Stacks, Tag 0D4F] applies to a Noetherian model.

## Main results

* `Stacks.AlgebraicGeometry.SectionRingBaseChange.exists_eq_sum_mul_of_isZero_Hgroup`.

## References

* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorPower

universe u

namespace Stacks.AlgebraicGeometry.SectionRingBaseChange

/-- The structure sheaf of rings of `X` in the spelling of the integral tensor powers. -/
abbrev structSheaf (X : Scheme.{u}) :=
  Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
    (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)

variable {X : Scheme.{u}} (L : SheafOfModules.{u} (structSheaf X))
  [Stacks.SheafOfModules.IsInvertible X.presheaf
    (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) L]

/-- Tensoring on the right with `ℒ^{⊗ k}`, in the category the tensor powers live in. -/
abbrev twistRight (k : ℤ) :
    SheafOfModules.{u} (structSheaf X) ⥤ SheafOfModules.{u} (structSheaf X) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
    X.presheaf (forget₂ CommRingCat RingCat)
      (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)⟩).flip.obj
    (tensorPower X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) L k)

/-- In a preadditive category, the inclusions of a finite coproduct split it. -/
theorem exists_sum_comp_sigma_ι {C : Type*} [Category C] [Preadditive C] {I : Type*}
    [Fintype I] (f : I → C) [HasBiproduct f] [HasCoproduct f] :
    ∃ p : ∀ i, ∐ f ⟶ f i, ∑ i, p i ≫ Sigma.ι f i = 𝟙 (∐ f) := by
  refine ⟨fun i => (biproduct.isoCoproduct f).inv ≫ biproduct.π f i, ?_⟩
  have h1 : ∀ i, Sigma.ι f i = biproduct.ι f i ≫ (biproduct.isoCoproduct f).hom := by
    intro i
    rw [biproduct.isoCoproduct_hom, biproduct.ι_desc]
  simp_rw [h1, Category.assoc]
  rw [← Preadditive.comp_sum]
  simp_rw [← Category.assoc]
  have htot : ∑ j, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f) :=
    IsBilimit.total (biproduct.isBilimit f)
  rw [← Preadditive.sum_comp, htot, Category.id_comp, Iso.inv_hom_id]

section Sections

/-- Evaluating a sum of morphisms of sheaves of modules at a section is the sum of the
evaluations. -/
theorem sum_val_app_apply {I : Type*} [Fintype I] {M N : SheafOfModules.{u} (structSheaf X)}
    (f : I → (M ⟶ N)) (U : (X.Opens)ᵒᵖ) (x : M.val.obj U) :
    (∑ i, f i).val.app U x = ∑ i, (f i).val.app U x :=
  map_sum (AddMonoidHom.mk' (fun g : M ⟶ N => g.val.app U x) (fun _ _ => rfl)) f Finset.univ

/-- Tensoring a morphism on the right sends the section determined by a pair of sections to the
section determined by the image of the first one. -/
theorem twistRight_map_tensorSectionsAt {F F' : SheafOfModules.{u} (structSheaf X)} (g : F ⟶ F')
    (k : ℤ) (U : (X.Opens)ᵒᵖ) (a : F.val.obj U)
    (t : (tensorPower X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
      L k).val.obj U) :
    ((twistRight L k).map g).val.app U
        (Stacks.SheafOfModules.tensorSectionsAt X.presheaf
          (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) U F _ a t) =
      Stacks.SheafOfModules.tensorSectionsAt X.presheaf
        (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) U F' _ (g.val.app U a) t := by
  have h := Stacks.SheafOfModules.tensorSections_tensorMapAt X.presheaf
    (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) U F F' _ _ g (𝟙 _) a t
  have hm : (twistRight L k).map g = (Stacks.SheafOfModules.Invertible.tensorProductBifunctor
      X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)).map
        ((g, 𝟙 _) : (F, _) ⟶ (F', _)) := rfl
  rw [hm]
  exact h

/-- Tensoring on the right with `ℒ^{⊗ k}` is an equivalence. -/
private theorem twistRight_isEquivalence (k : ℤ) : (twistRight L k).IsEquivalence :=
  haveI : Stacks.SheafOfModules.IsInvertible X.presheaf
      (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
      (tensorPower X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) L k) :=
    isInvertible_tensorPower _ _ L k
  Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence X.presheaf
    (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
    (tensorPower X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) L k)

/-- **The twisted presentation is surjective on global sections** when the first cohomology of
the twisted kernel vanishes. -/
theorem surjective_twistRight_map_app {I : Type u} (k : ℤ) {M : SheafOfModules.{u} (structSheaf X)}
    (π : SheafOfModules.free I ⟶ M) [Epi π]
    (hvan : IsZero (Hgroup (structSheaf X) ⊤ 1 ((twistRight L k).obj (kernel π)))) :
    Function.Surjective (((twistRight L k).map π).val.app (op ⊤)) := by
  have := twistRight_isEquivalence L k
  have hS : (ShortComplex.mk (kernel.ι π) π (kernel.condition π)).ShortExact :=
    ShortComplex.shortExact_mk_kernel_ι π
  have hST := hS.map_of_exact (twistRight L k)
  have hzero := (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    (structSheaf X) ⊤ 1 _).mpr hvan
  have hepi := Stacks.Cohomology.epi_map_of_isZero_rightDerived_one
    (_root_.SheafOfModules.evaluation.{u} (structSheaf X) (op ⊤)) hST hzero
  exact (ModuleCat.epi_iff_surjective _).1 hepi

/-- **The sections of a twisted finite free module split into the twisted summands.** -/
theorem exists_eq_sum_twistRight_ιFree {I : Type u} [Fintype I] (k : ℤ)
    (c : ((twistRight L k).obj (SheafOfModules.free I)).val.obj (op ⊤)) :
    ∃ y : I → ((twistRight L k).obj (SheafOfModules.unit (structSheaf X))).val.obj (op ⊤),
      c = ∑ i, ((twistRight L k).map (SheafOfModules.ιFree i)).val.app (op ⊤) (y i) := by
  have := twistRight_isEquivalence L k
  have : (twistRight L k).IsRightAdjoint := (twistRight L k).asEquivalence.isRightAdjoint_functor
  have : (twistRight L k).Additive := Functor.additive_of_preserves_binary_products _
  have : HasBiproduct (fun _ : I => SheafOfModules.unit (structSheaf X)) :=
    HasBiproduct.of_hasCoproduct _
  obtain ⟨p, hp⟩ := exists_sum_comp_sigma_ι (fun _ : I => SheafOfModules.unit (structSheaf X))
  refine ⟨fun i => ((twistRight L k).map (p i)).val.app (op ⊤) c, ?_⟩
  have h1 := congrArg (fun φ => φ.val.app (op ⊤) c)
    (((twistRight L k).map_id _).symm.trans (congrArg (twistRight L k).map hp.symm))
  simp only [Functor.map_sum, Functor.map_comp] at h1
  exact h1.trans (sum_val_app_apply (fun i => (twistRight L k).map (p i) ≫
    (twistRight L k).map (SheafOfModules.ιFree i)) (op ⊤) c)

/-- Every global section of `𝒪 ⊗ ℒ^{⊗ k}` is `1 ⊗ a`. -/
theorem eq_tensorSectionsAt_one (k : ℤ)
    (y : ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
      X.presheaf (forget₂ CommRingCat RingCat)
        (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)⟩).obj
          (SheafOfModules.unit (structSheaf X))).obj
            (tensorPower X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
              L k))).val.obj (op ⊤)) :
    y = Stacks.SheafOfModules.tensorSectionsAt X.presheaf
      (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) (op ⊤)
        (SheafOfModules.unit (structSheaf X))
        (tensorPower X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) L k)
        (ProjF1Dehomogenization.toUnit (structSheaf X) (1 : (structSheaf X).obj.obj (op ⊤)))
        ((Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.presheaf
          (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
          (tensorPower X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
            L k)).hom.val.app (op ⊤) y) := by
  refine (bijective_iso_hom_app' (Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor
    X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
    (tensorPower X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) L k))
      (op ⊤)).1 ?_
  exact (Stacks.SheafOfModules.tensorSections_leftUnitorAt X.presheaf
    (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) (op ⊤) _ _).symm

/-- One summand of the twisted presentation, on global sections. -/
theorem coherentMulIso_twistRight_map_ιFree {I : Type u} (N k : ℤ)
    (s : I → (tensorPower X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
      L N).sections) (i : I)
    (y : ((twistRight L k).obj (SheafOfModules.unit (structSheaf X))).val.obj (op ⊤)) :
    (coherentMulIso X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
      L N k).hom.val.app (op ⊤)
        (((twistRight L k).map ((tensorPower X.presheaf
          (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) L N).freeHomEquiv.symm
            s)).val.app
            (op ⊤) (((twistRight L k).map (SheafOfModules.ιFree i)).val.app (op ⊤) y)) =
      (mulBilinear X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
        L N k).app (op ⊤) ((s i).val (op ⊤))
          ((Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.presheaf
            (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
            (tensorPower X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
              L k)).hom.val.app (op ⊤) y) := by
  have h1 : SheafOfModules.ιFree i ≫ (tensorPower X.presheaf
      (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) L N).freeHomEquiv.symm s =
      (tensorPower X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
        L N).unitHomEquiv.symm (s i) := by
    rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply, Equiv.apply_symm_apply]
  have h2 : ((twistRight L k).map ((tensorPower X.presheaf
      (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) L N).freeHomEquiv.symm s)).val.app
        (op ⊤) (((twistRight L k).map (SheafOfModules.ιFree i)).val.app (op ⊤) y) =
      ((twistRight L k).map ((tensorPower X.presheaf
        (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) L N).unitHomEquiv.symm
          (s i))).val.app (op ⊤) y := by
    rw [← h1, Functor.map_comp]
    rfl
  rw [h2]
  conv_lhs => rw [eq_tensorSectionsAt_one L k y, twistRight_map_tensorSectionsAt]
  have hg : (((tensorPower X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
      L N).unitHomEquiv.symm (s i)).val.app (op ⊤))
        (ProjF1Dehomogenization.toUnit (structSheaf X) 1) = (s i).val (op ⊤) :=
    (SheafOfModules.unitHomEquiv_apply_coe _ _ (op ⊤)).symm.trans
      (congrArg (fun z => z.val (op ⊤)) (Equiv.apply_symm_apply _ (s i)))
  rw [hg]
  rfl

/-- **Generation in high degree by the sections of one power.**  If the global sections `s_i` of
`ℒ^{⊗ N}` generate it and `H¹(X, 𝒦 ⊗ ℒ^{⊗ k})` vanishes, `𝒦` the kernel of the presentation
they define, then every global section of `ℒ^{⊗ (N + k)}` is `Σ s_i · a_i` for global sections
`a_i` of `ℒ^{⊗ k}`. -/
theorem exists_eq_sum_mul_of_isZero_Hgroup {I : Type u} [Fintype I] (N k : ℤ)
    (s : I → (tensorPower X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
      L N).sections)
    (hπ : Epi ((tensorPower X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
      L N).freeHomEquiv.symm s))
    (hvan : IsZero (Hgroup (structSheaf X) ⊤ 1 ((twistRight L k).obj (kernel
      ((tensorPower X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
        L N).freeHomEquiv.symm s)))))
    (b : (tensorPower X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
      L (N + k)).val.obj (op ⊤)) :
    ∃ a : I → (tensorPower X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
        L k).val.obj (op ⊤),
      b = ∑ i, (mulBilinear X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
        L N k).app (op ⊤) ((s i).val (op ⊤)) (a i) := by
  have := hπ
  obtain ⟨c, hc⟩ := surjective_twistRight_map_app L k _ hvan
    ((coherentMulIso X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
      L N k).inv.val.app (op ⊤) b)
  obtain ⟨y, hy⟩ := exists_eq_sum_twistRight_ιFree L k c
  refine ⟨fun i => (Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.presheaf
    (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
    (tensorPower X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
      L k)).hom.val.app (op ⊤) (y i), ?_⟩
  have hb := congrArg (fun φ => φ.val.app (op ⊤) b) (coherentMulIso X.presheaf
    (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) L N k).inv_hom_id
  refine hb.symm.trans ?_
  change (coherentMulIso X.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X)
    L N k).hom.val.app (op ⊤) ((coherentMulIso X.presheaf
      (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) L N k).inv.val.app (op ⊤) b) = _
  rw [← hc, hy, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => coherentMulIso_twistRight_map_ιFree L N k s i (y i)

end Sections

/-! ### Over a Noetherian ring -/

section Noetherian

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {Y : Scheme.{u}}
  (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f] (M : Y.Modules)
  [Stacks.Ample.IsInvertibleModule Y M]

/-- **An ample invertible module has arbitrarily high powers generated by finitely many global
sections.** -/
theorem exists_generatingSections_laurentPowers (hM : Stacks.Ample.IsAmple Y M) (n₀ : ℕ) :
    ∃ (n : ℕ) (I : Type u) (_ : Fintype I)
      (s : I → ((Stacks.RelativeAmple.laurentPowers M).piece (n : ℤ)).sections),
      n₀ ≤ n ∧ Epi ((tensorPower Y.presheaf
        (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct Y) M (n : ℤ)).freeHomEquiv.symm
          s) := by
  have hMinv := isInvertible_tensorPower_of_isInvertibleModule Y M
  obtain ⟨m₀, hm₀⟩ := Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple M hM
    (Stacks.Ample.unitModule Y) inferInstance inferInstance
  obtain ⟨σ, hσ⟩ := hm₀ ((max n₀ m₀.toNat : ℕ) : ℤ) (by omega)
  let e : _ ≅ (Stacks.RelativeAmple.laurentPowers M).piece ((max n₀ m₀.toNat : ℕ) : ℤ) :=
    Stacks.AmpleGlobalGeneration.unitTensorIso M ((max n₀ m₀.toNat : ℕ) : ℤ) ≪≫
      (Stacks.PowerFamilyBridge.tensorPowerModuleIso Y M ((max n₀ m₀.toNat : ℕ) : ℤ)).symm
  let σ' := SheafOfModules.GeneratingSections.equivOfIso e σ
  have : Finite σ'.I := hσ
  exact ⟨max n₀ m₀.toNat, σ'.I, Fintype.ofFinite _, σ'.s, le_max_left _ _, σ'.epi⟩

/-- The twist of a module by a tensor power, read in the category of the tensor powers. -/
theorem isZero_Hgroup_twistRight_of_isZero_tensorPower (K : Y.Modules) (k : ℤ)
    (h : IsZero (Hgroup Y.ringCatSheaf ⊤ 1
      (Stacks.RelativeVeryAmple.tensorModules Y K
        (tensorPower Y.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct Y)
          M k)))) :
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y M
    IsZero (Hgroup (structSheaf Y) ⊤ 1 ((twistRight M k).obj K)) := h

/-- The two spellings of the tensor powers have the same twisted cohomology. -/
theorem isZero_Hgroup_tensorModules_tensorPowerModule (K : Y.Modules) (k : ℤ)
    (h : IsZero (Hgroup Y.ringCatSheaf ⊤ 1
      (Stacks.RelativeVeryAmple.tensorModules Y K (Stacks.Ample.tensorPowModule Y M k)))) :
    IsZero (Hgroup Y.ringCatSheaf ⊤ 1
      (Stacks.RelativeVeryAmple.tensorModules Y K
        (Stacks.AmpleProjectiveImmersion.tensorPowerModule Y M k))) :=
  h.of_iso ((Hfunctor Y.ringCatSheaf ⊤ 1).mapIso
    (Stacks.RelativeVeryAmple.tensorModulesMapIso Y (Iso.refl K)
      (Stacks.PowerFamilyBridge.tensorPowerModuleIso Y M k)))

/-- The twist of a module by a tensor power has no `H¹` as soon as its spelling through
`Stacks.Ample.tensorPowModule` does. -/
theorem isZero_Hgroup_twistRight_of_isZero (K : Y.Modules) (k : ℤ)
    (h : IsZero (Hgroup Y.ringCatSheaf ⊤ 1
      (Stacks.RelativeVeryAmple.tensorModules Y K (Stacks.Ample.tensorPowModule Y M k)))) :
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y M
    IsZero (Hgroup (structSheaf Y) ⊤ 1 ((twistRight M k).obj K)) :=
  isZero_Hgroup_twistRight_of_isZero_tensorPower M K k
    (isZero_Hgroup_tensorModules_tensorPowerModule M K k h)

include f in
/-- **The twists of the kernel of a finite free presentation of a power have no `H¹` in high
degree**, by Serre vanishing ([Stacks, Tag 0B5T] (4)) for the coherent kernel. -/
theorem exists_isZero_Hgroup_twistRight_kernel (hM : Stacks.Ample.IsAmple Y M) {n : ℕ}
    {I : Type u} [Finite I]
    (s : I → ((Stacks.RelativeAmple.laurentPowers M).piece (n : ℤ)).sections) :
    ∃ d₀ : ℕ, ∀ k : ℕ, d₀ ≤ k →
      haveI := isInvertible_tensorPower_of_isInvertibleModule Y M
      IsZero (Hgroup (structSheaf Y) ⊤ 1 ((twistRight M (k : ℤ)).obj (kernel
        ((tensorPower Y.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct Y)
          M (n : ℤ)).freeHomEquiv.symm s)))) := by
  have : IsLocallyNoetherian (Spec (CommRingCat.of R)) :=
    AlgebraicGeometry.isLocallyNoetherian_Spec.mpr inferInstance
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have hMinv := isInvertible_tensorPower_of_isInvertibleModule Y M
  have hfree : (SheafOfModules.free (R := Y.ringCatSheaf) I).IsCoherent :=
    Stacks.AlgebraicGeometry.ProperMapping.isCoherent_sigma_modules _ fun _ =>
      Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Y
  have hP : ((Stacks.RelativeAmple.laurentPowers M).piece (n : ℤ) : Y.Modules).IsCoherent :=
    have := isInvertibleModule_laurentPowers_piece M (n : ℤ)
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible Y _
  have hK : (kernel ((tensorPower Y.presheaf
      (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct Y) M (n : ℤ)).freeHomEquiv.symm
        s) : Y.Modules).IsCoherent :=
    Stacks.AlgebraicGeometry.ProperMapping.isCoherent_kernel_modules hfree hP _
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist
      f (kernel ((tensorPower Y.presheaf (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct Y)
        M (n : ℤ)).freeHomEquiv.symm s) : Y.Modules) M hM
  exact ⟨d₀, fun k hk => isZero_Hgroup_twistRight_of_isZero M _ (k : ℤ) (hd₀ k 1 hk one_pos)⟩

include f in
/-- **The high powers of an ample invertible module on a scheme proper over a Noetherian ring
are generated by the sections of one power.**  For every `n₀` there are an `n ≥ n₀`, finitely
many global sections `s_i` of `ℳ^{⊗ n}`, and a bound `N`, such that for every `k ≥ N` each global
section of `ℳ^{⊗ (n + k)}` is `Σ s_i · a_i` with `a_i` global sections of `ℳ^{⊗ k}`. -/
theorem exists_forall_eq_sum_mul (hM : Stacks.Ample.IsAmple Y M) (n₀ : ℕ) :
    ∃ (n : ℕ) (I : Type u) (_ : Fintype I)
      (s : I → ((Stacks.RelativeAmple.laurentPowers M).piece (n : ℤ)).sections) (N : ℕ),
      n₀ ≤ n ∧ ∀ k : ℕ, N ≤ k →
        ∀ b : ((Stacks.RelativeAmple.laurentPowers M).piece ((n : ℤ) + (k : ℤ))).val.obj (op ⊤),
          ∃ a : I → ((Stacks.RelativeAmple.laurentPowers M).piece (k : ℤ)).val.obj (op ⊤),
            b = ∑ i, ((Stacks.RelativeAmple.laurentPowers M).mul (n : ℤ) (k : ℤ)).app (op ⊤)
              ((s i).val (op ⊤)) (a i) := by
  have hMinv := isInvertible_tensorPower_of_isInvertibleModule Y M
  obtain ⟨n, I, _, s, hn, hπ⟩ := exists_generatingSections_laurentPowers M hM n₀
  obtain ⟨d₀, hd₀⟩ := exists_isZero_Hgroup_twistRight_kernel f M hM s
  exact ⟨n, I, inferInstance, s, d₀, hn, fun k hk b =>
    exists_eq_sum_mul_of_isZero_Hgroup M (n : ℤ) (k : ℤ) s hπ (hd₀ k hk) b⟩

end Noetherian

end Stacks.AlgebraicGeometry.SectionRingBaseChange

end
