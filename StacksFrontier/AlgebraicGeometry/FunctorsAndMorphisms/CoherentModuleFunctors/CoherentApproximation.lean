module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectColimit

/-!
# Coherent approximation of a short exact sequence

On a Noetherian scheme a short exact sequence of quasi-coherent modules is the colimit of a
filtered diagram of short exact sequences of coherent modules. Writing the middle term `F'` as
the filtered colimit of its quasi-coherent submodules `F'ᵢ` of finite type, the stages are the
short exact sequences `0 → F ∩ F'ᵢ → F'ᵢ → F''ᵢ → 0`, where `F''ᵢ` is the image of `F'ᵢ` in
`F''`; all three terms are coherent because the scheme is Noetherian.

## Main results

* `AlgebraicGeometry.CoherentModuleFunctors.exists_filtered_coherent_shortExact_approximation`:
  the approximation, as a filtered diagram in the category of short complexes together with a
  colimit cocone whose point is the given sequence.

## Implementation notes

The diagram is built in the category of short complexes of functors `J ⥤ 𝒪_X-Mod`, where the
stages are obtained from the kernel and the cokernel of the natural transformation `F'• → F''`
induced by the chosen cocone; the equivalence between short complexes of functors and functors
to short complexes then produces the diagram, so that functoriality and the stagewise short
exactness are automatic. The colimit is computed termwise: the middle term is the colimit by
construction, the left term because a filtered colimit in a Grothendieck abelian category is
left exact, and the right term because a colimit of cokernels is the cokernel of the colimit.
Consequently the colimit is taken in the category of short complexes, so its three terms and
both arrows are the respective colimits of the approximating terms and arrows, rather than
merely being isomorphic termwise.

## References

* [Stacks Project, Tag 0FZL](https://stacks.math.columbia.edu/tag/0FZL)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.CoherentModuleFunctors

attribute [local instance] IsFiltered.isConnected

/-! ### The approximating diagram in an abelian category -/

section Stages

variable {C : Type v} [Category.{u, v} C] [Abelian C] {J : Type u} [SmallCategory J]
  {S : ShortComplex C} {D : J ⥤ C} (κ : D ⟶ (Functor.const J).obj S.X₂)

/-- The natural transformation from the approximating diagram of `S.X₂` to the constant diagram
at `S.X₃`. -/
private noncomputable abbrev toQuot : D ⟶ (Functor.const J).obj S.X₃ :=
  κ ≫ (Functor.const J).map S.g

/-- The short complex of functors whose stages approximate `S`: the kernel of `toQuot κ`, the
diagram itself, and the cokernel of that kernel inclusion. -/
private noncomputable abbrev stageComplex : ShortComplex (J ⥤ C) :=
  ShortComplex.mk (kernel.ι (toQuot κ)) (cokernel.π (kernel.ι (toQuot κ)))
    (cokernel.condition _)

private lemma stageComplex_shortExact : (stageComplex κ).ShortExact :=
  { exact := ShortComplex.exact_cokernel _ }

/-- The approximating diagram of short complexes. -/
private noncomputable def stageDiagram : J ⥤ ShortComplex C :=
  (ShortComplex.functorEquivalence J C).functor.obj (stageComplex κ)

private lemma stageDiagram_shortExact (j : J) : ((stageDiagram κ).obj j).ShortExact := by
  have h : (stageDiagram κ).obj j = (stageComplex κ).map ((evaluation J C).obj j) := rfl
  rw [h]
  exact (stageComplex_shortExact κ).map_of_exact _

/-- The first term of a stage is the kernel of the corresponding component of `toQuot κ`. -/
private noncomputable def stageX₁Iso (j : J) :
    ((stageDiagram κ).obj j).X₁ ≅ kernel (κ.app j ≫ S.g) :=
  PreservesKernel.iso ((evaluation J C).obj j) (toQuot κ)

/-- The constant short complex at `S`. -/
private noncomputable abbrev constComplex : ShortComplex (J ⥤ C) :=
  ShortComplex.mk ((Functor.const J).map S.f) ((Functor.const J).map S.g)
    (by ext j; simp [S.zero])

private noncomputable def constComplex_fIsKernel (hS : S.ShortExact) :
    IsLimit (KernelFork.ofι (constComplex (S := S) (J := J)).f
      (constComplex (S := S) (J := J)).zero) :=
  evaluationJointlyReflectsLimits _ fun _ => (KernelFork.isLimitMapConeEquiv _ _).2 hS.fIsKernel

/-- The comparison from the diagram of kernels to the constant diagram at `S.X₁`. -/
private noncomputable def kerToX₁ (hS : S.ShortExact) :
    kernel (toQuot κ) ⟶ (Functor.const J).obj S.X₁ :=
  (KernelFork.IsLimit.lift' (constComplex_fIsKernel (S := S) (J := J) hS)
    (kernel.ι (toQuot κ) ≫ κ) (by rw [Category.assoc]; exact kernel.condition _)).1

private lemma kerToX₁_comp (hS : S.ShortExact) :
    kerToX₁ κ hS ≫ (constComplex (S := S) (J := J)).f = kernel.ι (toQuot κ) ≫ κ :=
  (KernelFork.IsLimit.lift' (constComplex_fIsKernel (S := S) (J := J) hS)
    (kernel.ι (toQuot κ) ≫ κ) (by rw [Category.assoc]; exact kernel.condition _)).2

private lemma kerToX₁_app_comp (hS : S.ShortExact) (j : J) :
    (kerToX₁ κ hS).app j ≫ S.f = (kernel.ι (toQuot κ)).app j ≫ κ.app j := by
  have h := congrArg (fun α : kernel (toQuot κ) ⟶ (Functor.const J).obj S.X₂ => α.app j)
    (kerToX₁_comp κ hS)
  simpa using h

/-- The comparison from the diagram of cokernels to the constant diagram at `S.X₃`. -/
private noncomputable def cokToX₃ :
    cokernel (kernel.ι (toQuot κ)) ⟶ (Functor.const J).obj S.X₃ :=
  cokernel.desc _ (toQuot κ) (kernel.condition _)

private lemma cokToX₃_comp :
    cokernel.π (kernel.ι (toQuot κ)) ≫ cokToX₃ κ = toQuot κ := cokernel.π_desc _ _ _

private lemma cokToX₃_app_comp (j : J) :
    κ.app j ≫ S.g = (cokernel.π (kernel.ι (toQuot κ))).app j ≫ (cokToX₃ κ).app j := by
  have h := congrArg (fun α : D ⟶ (Functor.const J).obj S.X₃ => α.app j) (cokToX₃_comp κ)
  simpa using h.symm

/-- The cocone from the approximating diagram to `S`. -/
private noncomputable def stageCocone (hS : S.ShortExact) : Cocone (stageDiagram κ) where
  pt := S
  ι :=
    { app := fun j => ShortComplex.homMk ((kerToX₁ κ hS).app j) (κ.app j) ((cokToX₃ κ).app j)
        (kerToX₁_app_comp κ hS j) (cokToX₃_app_comp κ j)
      naturality := fun _ _ f => ShortComplex.hom_ext _ _ ((kerToX₁ κ hS).naturality f)
        (κ.naturality f) ((cokToX₃ κ).naturality f) }

end Stages

/-! ### The colimit of a constant diagram -/

section Const

variable {C : Type v} [Category.{u, v} C] {J : Type u} [SmallCategory J] [IsFiltered J]
  [HasColimitsOfShape J C]

/-- A filtered colimit of a constant diagram is its value. -/
private noncomputable def constColimIso (Z : C) : colimit ((Functor.const J).obj Z) ≅ Z :=
  (colimit.isColimit _).coconePointUniqueUpToIso (isColimitConstCocone J Z)

omit [HasColimitsOfShape J C] in
private lemma colimit_ι_constColimIso_hom (Z : C) (j : J) :
    colimit.ι ((Functor.const J).obj Z) j ≫ (constColimIso (J := J) Z).hom
      = 𝟙 (((Functor.const J).obj Z).obj j) :=
  (colimit.isColimit ((Functor.const J).obj Z)).comp_coconePointUniqueUpToIso_hom
    (isColimitConstCocone J Z) j

omit [HasColimitsOfShape J C] in
private lemma colimit_ι_constColimIso_hom_comp (Z : C) (j : J) {W : C} (h : Z ⟶ W) :
    colimit.ι ((Functor.const J).obj Z) j ≫ (constColimIso (J := J) Z).hom ≫ h = h := by
  rw [← Category.assoc, colimit_ι_constColimIso_hom, Category.id_comp]

private lemma constColimIso_hom_naturality {Z Z' : C} (g : Z ⟶ Z') :
    colim.map ((Functor.const J).map g) ≫ (constColimIso (J := J) Z').hom
      = (constColimIso (J := J) Z).hom ≫ g := by
  refine colimit.hom_ext fun j => ?_
  rw [← colimMap_eq, ← Category.assoc, ι_colimMap, Category.assoc,
    colimit_ι_constColimIso_hom, Category.comp_id, colimit_ι_constColimIso_hom_comp]
  rfl

end Const

/-! ### Termwise identification of the colimit -/

section Colimit

variable {C : Type v} [Category.{u, v} C] [Abelian C] {J : Type u} [SmallCategory J]
  [IsFiltered J] [HasColimitsOfShape J C] {S : ShortComplex C} {D : J ⥤ C}
  (κ : D ⟶ (Functor.const J).obj S.X₂)

/-- The map induced on the colimit by the cocone `κ`. -/
private noncomputable def colimDesc : colimit D ⟶ S.X₂ := colimit.desc D (Cocone.mk S.X₂ κ)

omit [IsFiltered J] in
private lemma colimit_ι_colimDesc (j : J) : colimit.ι D j ≫ colimDesc κ = κ.app j :=
  colimit.ι_desc _ _

omit [IsFiltered J] in
private lemma isIso_colimDesc (hκ : IsColimit (Cocone.mk S.X₂ κ)) : IsIso (colimDesc κ) := by
  have h : colimDesc κ = ((colimit.isColimit D).coconePointUniqueUpToIso hκ).hom := rfl
  rw [h]; infer_instance

private lemma colim_map_comp_constColimIso :
    colim.map κ ≫ (constColimIso (J := J) S.X₂).hom = colimDesc κ := by
  refine colimit.hom_ext fun j => ?_
  rw [← colimMap_eq, ← Category.assoc, ι_colimMap, Category.assoc,
    colimit_ι_constColimIso_hom, Category.comp_id, colimit_ι_colimDesc]

private lemma colimDesc_comp_g :
    colimDesc κ ≫ S.g = colim.map (toQuot κ) ≫ (constColimIso (J := J) S.X₃).hom := by
  rw [← colim_map_comp_constColimIso κ, Category.assoc,
    ← constColimIso_hom_naturality (J := J) S.g, ← Category.assoc, ← Functor.map_comp]

private lemma colim_kerToX₁_comp (hS : S.ShortExact) :
    (colim.map (kerToX₁ κ hS) ≫ (constColimIso (J := J) S.X₁).hom) ≫ S.f
      = colim.map (kernel.ι (toQuot κ)) ≫ colimDesc κ := by
  rw [Category.assoc, ← constColimIso_hom_naturality (J := J) S.f, ← Category.assoc,
    ← Functor.map_comp, kerToX₁_comp κ hS, Functor.map_comp, Category.assoc,
    colim_map_comp_constColimIso κ]

private lemma colim_cokToX₃_comp :
    colim.map (cokernel.π (kernel.ι (toQuot κ)))
        ≫ colim.map (cokToX₃ κ) ≫ (constColimIso (J := J) S.X₃).hom
      = colimDesc κ ≫ S.g := by
  rw [← Category.assoc, ← Functor.map_comp, cokToX₃_comp, ← colimDesc_comp_g]

end Colimit

/-! ### The approximating cocone is a colimit -/

section IsColimit

variable {C : Type v} [Category.{u, v} C] [Abelian C] {J : Type u} [SmallCategory J]
  [IsFiltered J] [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] {S : ShortComplex C}
  {D : J ⥤ C} (κ : D ⟶ (Functor.const J).obj S.X₂)

private lemma isIso_colim_kerToX₁ (hS : S.ShortExact) (hκ : IsColimit (Cocone.mk S.X₂ κ)) :
    IsIso (colim.map (kerToX₁ κ hS) ≫ (constColimIso (J := J) S.X₁).hom) := by
  have := hS.mono_f
  have := isIso_colimDesc κ hκ
  have h3 := (KernelFork.isLimitMapConeEquiv
      (KernelFork.ofι (kernel.ι (toQuot κ)) (kernel.condition (toQuot κ)))
      (colim (J := J) (C := C))).1
      (isLimitOfPreserves (colim (J := J) (C := C)) (kernelIsKernel (toQuot κ)))
  have h4 := isKernelCompMono h3 (constColimIso (J := J) S.X₃).hom (colimDesc_comp_g κ)
  have : Mono (colim.map (kernel.ι (toQuot κ))) := mono_of_isLimit_fork h4
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' h4 (S.f ≫ inv (colimDesc κ)) (by simp [S.zero])
  have hl' : l ≫ colim.map (kernel.ι (toQuot κ)) = S.f ≫ inv (colimDesc κ) := hl
  have hR1 : (colim.map (kerToX₁ κ hS) ≫ (constColimIso (J := J) S.X₁).hom) ≫ S.f
      = colim.map (kernel.ι (toQuot κ)) ≫ colimDesc κ := colim_kerToX₁_comp κ hS
  have hla : l ≫ (colim.map (kerToX₁ κ hS) ≫ (constColimIso (J := J) S.X₁).hom) = 𝟙 S.X₁ := by
    rw [← cancel_mono S.f, Category.assoc, hR1, ← Category.assoc, hl', Category.assoc,
      IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
  have : Mono (colim.map (kerToX₁ κ hS) ≫ (constColimIso (J := J) S.X₁).hom) := by
    have h : Mono ((colim.map (kerToX₁ κ hS) ≫ (constColimIso (J := J) S.X₁).hom) ≫ S.f) := by
      rw [hR1]; infer_instance
    exact mono_of_mono _ S.f
  have hal : (colim.map (kerToX₁ κ hS) ≫ (constColimIso (J := J) S.X₁).hom) ≫ l = 𝟙 _ := by
    rw [← cancel_mono (colim.map (kerToX₁ κ hS) ≫ (constColimIso (J := J) S.X₁).hom),
      Category.assoc, hla, Category.comp_id, Category.id_comp]
  exact ⟨⟨l, hal, hla⟩⟩

private lemma isIso_colim_cokToX₃ (hS : S.ShortExact) (hκ : IsColimit (Cocone.mk S.X₂ κ)) :
    IsIso (colim.map (cokToX₃ κ) ≫ (constColimIso (J := J) S.X₃).hom) := by
  have := hS.epi_g
  have := isIso_colimDesc κ hκ
  have := isIso_colim_kerToX₁ κ hS hκ
  have g3 := (CokernelCofork.isColimitMapCoconeEquiv
      (CokernelCofork.ofπ (cokernel.π (kernel.ι (toQuot κ))) (cokernel.condition _))
      (colim (J := J) (C := C))).1
      (isColimitOfPreserves (colim (J := J) (C := C))
        (cokernelIsCokernel (kernel.ι (toQuot κ))))
  have : Epi (colim.map (cokernel.π (kernel.ι (toQuot κ)))) := epi_of_isColimit_cofork g3
  have hmn : colim.map (kernel.ι (toQuot κ))
      ≫ colim.map (cokernel.π (kernel.ι (toQuot κ))) = 0 := by
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
  have hR1 : (colim.map (kerToX₁ κ hS) ≫ (constColimIso (J := J) S.X₁).hom) ≫ S.f
      = colim.map (kernel.ι (toQuot κ)) ≫ colimDesc κ := colim_kerToX₁_comp κ hS
  have hSf : S.f = inv (colim.map (kerToX₁ κ hS) ≫ (constColimIso (J := J) S.X₁).hom)
      ≫ colim.map (kernel.ι (toQuot κ)) ≫ colimDesc κ := by
    rw [← hR1, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hzero : S.f ≫ inv (colimDesc κ)
      ≫ colim.map (cokernel.π (kernel.ι (toQuot κ))) = 0 := by
    rw [hSf]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [hmn, comp_zero]
  obtain ⟨r, hr⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel
    (inv (colimDesc κ) ≫ colim.map (cokernel.π (kernel.ι (toQuot κ)))) hzero
  simp only [Cofork.π_ofπ] at hr
  have hR3 : colim.map (cokernel.π (kernel.ι (toQuot κ)))
      ≫ (colim.map (cokToX₃ κ) ≫ (constColimIso (J := J) S.X₃).hom)
      = colimDesc κ ≫ S.g := colim_cokToX₃_comp κ
  have hrc : r ≫ (colim.map (cokToX₃ κ) ≫ (constColimIso (J := J) S.X₃).hom) = 𝟙 S.X₃ := by
    rw [← cancel_epi S.g, ← Category.assoc, hr, Category.assoc, hR3, ← Category.assoc,
      IsIso.inv_hom_id, Category.id_comp, Category.comp_id]
  have hcr : (colim.map (cokToX₃ κ) ≫ (constColimIso (J := J) S.X₃).hom) ≫ r = 𝟙 _ := by
    rw [← cancel_epi (colim.map (cokernel.π (kernel.ι (toQuot κ)))), Category.comp_id,
      ← Category.assoc, hR3, Category.assoc, hr, ← Category.assoc, IsIso.hom_inv_id,
      Category.id_comp]
  exact ⟨⟨r, hcr, hrc⟩⟩

/-- A cocone over a filtered diagram is a colimit if the induced map on colimits, followed by
the identification of the constant colimit, is an isomorphism. -/
private noncomputable def isColimitOfIsIso_colim_map_comp_constColimIso {Z : C} {E : J ⥤ C}
    (α : E ⟶ (Functor.const J).obj Z) (h : IsIso (colim.map α ≫ (constColimIso (J := J) Z).hom)) :
    IsColimit (Cocone.mk Z α) :=
  have : IsIso (colimMap (Cocone.mk Z α).ι) := by
    rw [colimMap_eq]; exact IsIso.of_isIso_comp_right _ (constColimIso (J := J) Z).hom
  Cocone.isColimitOfIsIsoColimMapι _

private noncomputable def isColimitKerCocone (hS : S.ShortExact)
    (hκ : IsColimit (Cocone.mk S.X₂ κ)) : IsColimit (Cocone.mk S.X₁ (kerToX₁ κ hS)) :=
  isColimitOfIsIso_colim_map_comp_constColimIso _ (isIso_colim_kerToX₁ κ hS hκ)

private noncomputable def isColimitCokCocone (hS : S.ShortExact)
    (hκ : IsColimit (Cocone.mk S.X₂ κ)) : IsColimit (Cocone.mk S.X₃ (cokToX₃ κ)) :=
  isColimitOfIsIso_colim_map_comp_constColimIso _ (isIso_colim_cokToX₃ κ hS hκ)

private noncomputable def isColimitStageCocone (hS : S.ShortExact)
    (hκ : IsColimit (Cocone.mk S.X₂ κ)) : IsColimit (stageCocone κ hS) :=
  ShortComplex.isColimitOfIsColimitπ _ (isColimitKerCocone κ hS hκ) hκ
    (isColimitCokCocone κ hS hκ)

end IsColimit

/-! ### Coherent approximation on a Noetherian scheme -/

private lemma essentiallySmall_finiteTypeQuasicoherentSubobject {X : Scheme.{u}}
    (F : X.Modules) : EssentiallySmall.{u} (FiniteTypeQuasicoherentSubobject F) := by
  have : Small.{u} (Subobject F) := inferInstance
  have : ObjectProperty.Small.{u} (finiteTypeQuasicoherentSubobjectProperty F) :=
    ObjectProperty.Small.of_le (P := finiteTypeQuasicoherentSubobjectProperty F) (Q := ⊤)
      (by intro G _; trivial)
  have : Small.{u} (FiniteTypeQuasicoherentSubobject F) := inferInstance
  have : LocallySmall.{u} (Subobject F) := CategoryTheory.locallySmall_of_thin
  have : LocallySmall.{u} (FiniteTypeQuasicoherentSubobject F) :=
    locallySmall_of_faithful (finiteTypeQuasicoherentSubobjectProperty F).ι
  exact essentiallySmall_of_small_of_locallySmall _

/-- On a Noetherian scheme a short exact sequence of quasi-coherent modules is the colimit of a
filtered diagram of short exact sequences of coherent modules. -/
theorem exists_filtered_coherent_shortExact_approximation
    {X : Scheme.{u}} [IsNoetherian X]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
      (T : J ⥤ ShortComplex X.Modules) (c : Cocone T),
      c.pt = S ∧ Nonempty (IsColimit c) ∧
        (∀ j : J, (T.obj j).ShortExact ∧ (T.obj j).X₁.IsCoherent ∧
          (T.obj j).X₂.IsCoherent ∧ (T.obj j).X₃.IsCoherent) := by
  classical
  have : EssentiallySmall.{u} (FiniteTypeQuasicoherentSubobject S.X₂) :=
    essentiallySmall_finiteTypeQuasicoherentSubobject S.X₂
  let e : FiniteTypeQuasicoherentSubobject S.X₂ ≌
      SmallModel.{u} (FiniteTypeQuasicoherentSubobject S.X₂) :=
    equivSmallModel (FiniteTypeQuasicoherentSubobject S.X₂)
  have hJ : IsFiltered (SmallModel.{u} (FiniteTypeQuasicoherentSubobject S.X₂)) :=
    IsFiltered.of_equivalence e
  let D : SmallModel.{u} (FiniteTypeQuasicoherentSubobject S.X₂) ⥤ X.Modules :=
    e.symm.functor ⋙ finiteTypeQuasicoherentSubobjectFunctor S.X₂
  let cD : Cocone D :=
    Cocone.whisker e.symm.functor (finiteTypeQuasicoherentSubobjectCocone S.X₂)
  have hcD : IsColimit cD :=
    (isColimit_finiteTypeQuasicoherentSubobjectCocone S.X₂).whiskerEquivalence e.symm
  let κ : D ⟶ (Functor.const
      (SmallModel.{u} (FiniteTypeQuasicoherentSubobject S.X₂))).obj S.X₂ := cD.ι
  have hκ : IsColimit (Cocone.mk S.X₂ κ) := hcD
  refine ⟨SmallModel.{u} (FiniteTypeQuasicoherentSubobject S.X₂), inferInstance, hJ,
    stageDiagram κ, stageCocone κ hS, rfl, ⟨isColimitStageCocone κ hS hκ⟩, fun j => ?_⟩
  have hprop := (e.symm.functor.obj j).2
  have hqc₂ : (D.obj j).IsQuasicoherent := hprop.1
  have hft₂ : (D.obj j).IsFiniteType := hprop.2
  have hX₂ : ((stageDiagram κ).obj j).X₂.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType
      (D.obj j)
  have hSEj : ((stageDiagram κ).obj j).ShortExact := stageDiagram_shortExact κ j
  have hkerqc : (kernel (κ.app j ≫ S.g)).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel _
  have hX₁qc : ((stageDiagram κ).obj j).X₁.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (stageX₁Iso κ j).symm hkerqc
  have : Mono ((stageDiagram κ).obj j).f := hSEj.mono_f
  have hX₁ : ((stageDiagram κ).obj j).X₁.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono
      ((stageDiagram κ).obj j).f
  exact ⟨hSEj, hX₁, hX₂,
    AlgebraicGeometry.CoherentAbelian.isCoherent_X₃_of_shortExact hSEj hX₁ hX₂⟩

end AlgebraicGeometry.CoherentModuleFunctors

end
