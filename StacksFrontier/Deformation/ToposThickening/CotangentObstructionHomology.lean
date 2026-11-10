module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Homology.DoubleHomology

/-!
# Maps into `G[1]` out of a complex in degrees `≤ -1`, read on `H^{-1}`

For a complex `M` of objects of an abelian category whose class lies in degrees `≤ -1`, the
maps `M ⟶ G[1]` in the derived category, for an object `G`, are the maps `H^{-1}(M) ⟶ G`
(Stacks 06XS). This file packages that identification together with its naturality in `M`, and
the elementary facts about the cohomology of a complex in a degree into which no nonzero
differential arrives: it is a subobject of the term, and the map induced on it by a morphism of
complexes is the restriction of the component of that morphism.

## Main definitions

* `HomologicalComplex.homologyToX`: the inclusion `Hⁱ(K) ⟶ Kⁱ` when the differential into
  degree `i` vanishes.
* `DerivedCategory.negOneHomologyMap`: the map `H^{-1}(M) ⟶ G` attached to `M ⟶ G[1]`.

## Main results

* `DerivedCategory.bijective_negOneHomologyMap`: for `M` in degrees `≤ -1` it is bijective.
* `DerivedCategory.negOneHomologyMap_Q_map_comp`: its naturality in `M`.

## References

* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  (K L : HomologicalComplex C c) (i : ι)

/-- The cohomology in a degree into which no nonzero differential arrives is a subobject of the
term in that degree. -/
noncomputable def homologyToX (h : K.d (c.prev i) i = 0) : K.homology i ⟶ K.X i :=
  (K.isoHomologyπ _ i rfl h).inv ≫ K.iCycles i

/-- The inclusion of the cohomology restricts to the inclusion of the cycles. -/
@[reassoc (attr := simp)]
theorem homologyπ_homologyToX (h : K.d (c.prev i) i = 0) :
    K.homologyπ i ≫ K.homologyToX i h = K.iCycles i := by
  rw [homologyToX, ← Category.assoc]
  exact (congrArg (· ≫ K.iCycles i) (K.isoHomologyπ _ i rfl h).hom_inv_id).trans
    (Category.id_comp _)

/-- The inclusion of the cohomology is a monomorphism. -/
instance mono_homologyToX (h : K.d (c.prev i) i = 0) : Mono (K.homologyToX i h) := by
  rw [homologyToX]
  infer_instance

variable {K L}

/-- The map on cohomology induced by a morphism of complexes, followed by the inclusion of the
cohomology of the target, is the inclusion of the cycles of the source followed by the
component of the morphism. -/
@[reassoc]
theorem homologyπ_homologyMap_homologyToX (φ : K ⟶ L) (hL : L.d (c.prev i) i = 0) :
    K.homologyπ i ≫ homologyMap φ i ≫ L.homologyToX i hL = K.iCycles i ≫ φ.f i := by
  rw [homologyπ_naturality_assoc, homologyπ_homologyToX, cyclesMap_i]

/-- The map induced on cohomology by a morphism of complexes into a complex with no nonzero
differential into degree `i` restricts the component of the morphism. -/
@[reassoc]
theorem homologyMap_homologyToX (φ : K ⟶ L) (hK : K.d (c.prev i) i = 0)
    (hL : L.d (c.prev i) i = 0) :
    homologyMap φ i ≫ L.homologyToX i hL = K.homologyToX i hK ≫ φ.f i := by
  rw [← cancel_epi (K.homologyπ i), homologyπ_homologyMap_homologyToX, homologyπ_homologyToX_assoc]

/-- Two morphisms of complexes with the same component in degree `i` induce the same map on
cohomology in degree `i`. -/
theorem homologyMap_eq_of_f_eq {φ ψ : K ⟶ L} (h : φ.f i = ψ.f i) :
    homologyMap φ i = homologyMap ψ i := by
  rw [← cancel_epi (K.homologyπ i), homologyπ_naturality, homologyπ_naturality]
  congr 1
  rw [← cancel_mono (L.iCycles i), cyclesMap_i, cyclesMap_i, h]

/-- The map induced on cohomology by a morphism into a single complex is its component, read
through the identification of the cohomology of the single complex with its object. -/
theorem homologyMap_singleObjHomologySelfIso_hom [DecidableEq ι] {A : C}
    (φ : K ⟶ (single C c i).obj A) (hK : K.d (c.prev i) i = 0) :
    homologyMap φ i ≫ (singleObjHomologySelfIso c i A).hom =
      K.homologyToX i hK ≫ φ.f i ≫ (singleObjXSelf c i A).hom := by
  rw [← cancel_epi (K.homologyπ i), homologyπ_naturality_assoc,
    homologyπ_singleObjHomologySelfIso_hom, homologyπ_homologyToX_assoc,
    singleObjCyclesSelfIso_hom, cyclesMap_i_assoc]

/-- The identification of the cohomology of a two-term complex at its source with the kernel of
its differential is the inclusion of the cohomology in the source. -/
theorem doubleHomologyIsoKernel_hom_comp_ι {X₀ X₁ : C} (f : X₀ ⟶ X₁) {i₀ i₁ : ι}
    (hi₀₁ : c.Rel i₀ i₁) (h : i₀ ≠ i₁) (hd : (double f hi₀₁).d (c.prev i₀) i₀ = 0) :
    (doubleHomologyIsoKernel f hi₀₁ h).hom ≫ kernel.ι f =
      (double f hi₀₁).homologyToX i₀ hd ≫ (doubleXIso₀ f hi₀₁).hom := by
  rw [← cancel_epi ((double f hi₀₁).homologyπ i₀), homologyπ_homologyToX_assoc]
  change ((double f hi₀₁).sc i₀).homologyπ ≫ (ShortComplex.homologyMap (doubleScIso₀ f hi₀₁ h).hom ≫
      (ShortComplex.asIsoHomologyπ _ rfl).inv ≫ (ShortComplex.cyclesIsoKernel _).hom) ≫
        kernel.ι f = ((double f hi₀₁).sc i₀).iCycles ≫ (doubleXIso₀ f hi₀₁).hom
  rw [Category.assoc, Category.assoc, ShortComplex.homologyπ_naturality_assoc,
    ShortComplex.homologyπ_comp_asIsoHomologyπ_inv_assoc]
  change ShortComplex.cyclesMap (doubleScIso₀ f hi₀₁ h).hom ≫
      kernel.lift _ (ShortComplex.iCycles _) _ ≫ kernel.ι f = _
  rw [kernel.lift_ι, ShortComplex.cyclesMap_i]
  congr 1
  simp only [doubleScIso₀, Iso.trans_hom, ShortComplex.comp_τ₂]
  exact Category.id_comp _

section SheafOfModules

variable {𝒞 : Type*} [Category* 𝒞] {J : GrothendieckTopology 𝒞} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- A monomorphism of sheaves of modules is injective on sections. -/
theorem _root_.SheafOfModules.injective_app_of_mono {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    [Mono f] (X : 𝒞ᵒᵖ) : Function.Injective (f.val.app X) :=
  (ModuleCat.mono_iff_injective ((SheafOfModules.evaluation R X).map f)).1 inferInstance

/-- **A section of the term in degree `i` killed by the differential is the image of a section
of the cohomology**, when no nonzero differential arrives in degree `i`. -/
theorem exists_homologyToX_app_eq {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (SheafOfModules.{u} R) c) (i : ι) (h : K.d (c.prev i) i = 0)
    (X : 𝒞ᵒᵖ) (s : (K.X i).val.obj X) (hs : (K.d i (c.next i)).val.app X s = 0) :
    ∃ e : (K.homology i).val.obj X, (K.homologyToX i h).val.app X e = s := by
  have hk := isLimitOfPreserves (SheafOfModules.evaluation R X) (K.cyclesIsKernel i (c.next i) rfl)
  have hk' := (isLimitMapConeForkEquiv' (SheafOfModules.evaluation R X) (K.iCycles_d i _)) hk
  have hex := ShortComplex.exact_of_f_is_kernel
    (ShortComplex.mk ((SheafOfModules.evaluation R X).map (K.iCycles i))
      ((SheafOfModules.evaluation R X).map (K.d i (c.next i)))
      (by rw [← Functor.map_comp, K.iCycles_d, Functor.map_zero])) hk'
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 hex s hs
  refine ⟨((K.isoHomologyπ _ i rfl h).hom.val.app X) z, ?_⟩
  change ((K.isoHomologyπ _ i rfl h).hom ≫ K.homologyToX i h).val.app X z = s
  rw [homologyToX, Iso.hom_inv_id_assoc]
  exact hz

end SheafOfModules

end HomologicalComplex

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The map `H^{-1}(M) ⟶ G` induced on cohomology in degree `-1` by a morphism `M ⟶ G[1]` in the
derived category, `M` a complex and `G` an object. -/
noncomputable def negOneHomologyMap (M : CochainComplex C ℤ) (G : C)
    (e : Q.obj M ⟶ ((singleFunctor C 0).obj G)⟦(1 : ℤ)⟧) : M.homology (-1) ⟶ G :=
  ((homologyFunctorFactors C (-1)).app M).inv ≫
    (homologyFunctor C 0).shiftMap e (-1) 0 (by norm_num) ≫
      ((singleFunctorCompHomologyFunctorIso C 0).app G).hom

/-- **Stacks 06XS for maps into `G[1]`.** When `M` lies in degrees `≤ -1`, a morphism
`M ⟶ G[1]` in the derived category is determined by the map it induces on `H^{-1}`, and every
map `H^{-1}(M) ⟶ G` arises. -/
theorem bijective_negOneHomologyMap (M : CochainComplex C ℤ) (G : C) [(Q.obj M).IsLE (-1)] :
    Function.Bijective (negOneHomologyMap M G) := by
  have h := bijective_homologyFunctor_shiftMap_of_isLE_of_isGE (Q.obj M)
    ((singleFunctor C 0).obj G) (-1) 0 1 0 (by norm_num) le_rfl
  have key : negOneHomologyMap M G = (fun k => ((homologyFunctorFactors C (-1)).app M).inv ≫ k ≫
      ((singleFunctorCompHomologyFunctorIso C 0).app G).hom) ∘
      (fun f : Q.obj M ⟶ ((singleFunctor C 0).obj G)⟦(1 : ℤ)⟧ ↦
        ((homologyFunctor C 0).shiftMap f (-1) 0 (by norm_num) :
          (homologyFunctor C (-1)).obj (Q.obj M) ⟶
            (homologyFunctor C 0).obj ((singleFunctor C 0).obj G))) := rfl
  rw [key]
  exact (((homologyFunctorFactors C (-1)).app M).homCongr
    ((singleFunctorCompHomologyFunctorIso C 0).app G)).bijective.comp h

/-- The map on `H^{-1}` is natural in the source complex. -/
theorem negOneHomologyMap_Q_map_comp {M M' : CochainComplex C ℤ} (φ : M ⟶ M') (G : C)
    (e : Q.obj M' ⟶ ((singleFunctor C 0).obj G)⟦(1 : ℤ)⟧) :
    negOneHomologyMap M G (Q.map φ ≫ e) = HomologicalComplex.homologyMap φ (-1) ≫
      negOneHomologyMap M' G e := by
  rw [negOneHomologyMap, negOneHomologyMap, Functor.shiftMap_comp']
  have h := (homologyFunctorFactors C (-1)).inv.naturality φ
  simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map] at h
  exact (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h.symm).trans (Category.assoc _ _ _)))

variable (G : C) (e₀ : Q.obj ((HomologicalComplex.single C (ComplexShape.up ℤ) (-1)).obj G) ⟶
  ((singleFunctor C 0).obj G)⟦(1 : ℤ)⟧) [IsIso e₀]

/-- The map on `H^{-1}` attached to an isomorphism `Q(G[-1]) ≅ G[1]` is an isomorphism. -/
instance isIso_negOneHomologyMap_single : IsIso (negOneHomologyMap _ G e₀) := by
  have : IsIso (((homologyFunctor C 0).shift (-1)).map e₀) := Functor.map_isIso _ _
  have : IsIso (((homologyFunctor C 0).shiftIso 1 (-1) 0 (by norm_num)).hom.app
    ((singleFunctor C 0).obj G)) := NatIso.isIso_app_of_isIso _ _
  have hs : IsIso ((homologyFunctor C 0).shiftMap e₀ (-1) 0 (by norm_num)) := by
    rw [Functor.shiftMap]
    infer_instance
  rw [negOneHomologyMap]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv _)
    (@IsIso.comp_isIso _ _ _ _ _ _ _ hs (Iso.isIso_hom _))

/-- The automorphism of `G` by which the map on `H^{-1}` attached to an isomorphism
`Q(G[-1]) ≅ G[1]` differs from the identification of the cohomology of `G[-1]` with `G`. -/
noncomputable def negOneHomologySingleIso : G ≅ G :=
  (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) (-1) G).symm ≪≫
    asIso (negOneHomologyMap _ G e₀)

/-- **The map on `H^{-1}` induced by a morphism into `G` placed in degree `-1`**, read through an
isomorphism `Q(G[-1]) ≅ G[1]`, is the restriction of the component of the morphism followed by
the automorphism `negOneHomologySingleIso` of `G`. -/
theorem negOneHomologyMap_Q_map_comp_single {M : CochainComplex C ℤ}
    (φ : M ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) (-1)).obj G)
    (hM : M.d ((ComplexShape.up ℤ).prev (-1)) (-1) = 0) :
    negOneHomologyMap M G (Q.map φ ≫ e₀) =
      M.homologyToX (-1) hM ≫ φ.f (-1) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1) G).hom ≫
          (negOneHomologySingleIso G e₀).hom := by
  rw [negOneHomologyMap_Q_map_comp, negOneHomologySingleIso, Iso.trans_hom, Iso.symm_hom,
    asIso_hom]
  calc HomologicalComplex.homologyMap φ (-1) ≫ negOneHomologyMap _ G e₀
      = (HomologicalComplex.homologyMap φ (-1) ≫
          (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) (-1) G).hom) ≫
          (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) (-1) G).inv ≫
            negOneHomologyMap _ G e₀ := by
        rw [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by
        rw [HomologicalComplex.homologyMap_singleObjHomologySelfIso_hom (-1) φ hM]
        simp only [Category.assoc]

end DerivedCategory

end
