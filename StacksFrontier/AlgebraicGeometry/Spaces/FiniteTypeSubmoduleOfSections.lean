module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeFilteredColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSubmoduleGluing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeBiprod

/-!
# Finite type quasi-coherent submodules containing given sections

Let `X` be an algebraic space over a scheme `S` and `ℋ` a quasi-coherent `𝒪_X`-module.  This
file collects the elementary facts about the *finite type quasi-coherent submodules* of `ℋ`
(sheaf submodules, `SheafOfModules.Submodule`, whose sheaf of modules is quasi-coherent and of
finite type).

* Two finite type quasi-coherent submodules have a least upper bound among all submodules which
  is again of finite type and quasi-coherent: the image of their direct sum.
* On an *affine* algebraic space every section of `ℋ` over an affine étale chart lies in a finite
  type quasi-coherent submodule: over an affine chart the sections of `ℋ` are spanned by
  restrictions of sections over the terminal chart (Descent, Proposition 03DX (2)), and each of
  those generates a finite type quasi-coherent submodule.
* A submodule of finite type of a module on a *quasi-compact* algebraic space is generated, in
  the sense of being contained in every submodule containing them, by finitely many sections
  over finitely many affine étale charts.

## Main results

* `AlgebraicGeometry.Space.exists_submodule_sup_isQuasicoherentOnSite_isFiniteType`: the least
  upper bound of two finite type quasi-coherent submodules.
* `AlgebraicGeometry.Space.exists_submodule_isFiniteType_mem_of_isAffineSpace`: a section over an
  affine chart of an affine algebraic space lies in a finite type quasi-coherent submodule.
* `AlgebraicGeometry.Space.exists_finite_affine_sections_of_isFiniteType`: finite generation of a
  finite type submodule over a quasi-compact algebraic space.

## References

* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SheafOfModules.ImageSubsheaf

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Sup

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}

set_option synthInstance.maxHeartbeats 400000 in
-- instance synthesis through the sheaf-of-modules and `Subobject` APIs over the small étale site
/-- The subobject defined by a finite type quasi-coherent submodule is a finite type
quasi-coherent subobject. -/
theorem finiteTypeQuasicoherentSubobjectProperty_mk {H : Modules.{u, u} B S hS X hX}
    (K : H.Submodule)
    (hK : K.toSheafOfModules.IsQuasicoherentOnSite ∧ K.toSheafOfModules.IsFiniteType) :
    finiteTypeQuasicoherentSubobjectProperty B S hS X hX H (Subobject.mk K.ι) :=
  ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso (Subobject.underlyingIso K.ι).symm hK.1,
    Stacks.SheafOfModules.isFiniteType_of_epi (Subobject.underlyingIso K.ι).inv hK.2⟩

set_option synthInstance.maxHeartbeats 400000 in
-- instance synthesis through the sheaf-of-modules and `Subobject` APIs over the small étale site
/-- The submodule attached to a finite type quasi-coherent subobject is a finite type
quasi-coherent submodule. -/
theorem isQuasicoherentOnSite_isFiniteType_monoRangeSubmodule {H : Modules.{u, u} B S hS X hX}
    (G : Subobject H) (hG : finiteTypeQuasicoherentSubobjectProperty B S hS X hX H G) :
    (monoRangeSubmodule G.arrow).toSheafOfModules.IsQuasicoherentOnSite ∧
      (monoRangeSubmodule G.arrow).toSheafOfModules.IsFiniteType :=
  ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso (monoRangeSubmoduleIso G.arrow) hG.1,
    Stacks.SheafOfModules.isFiniteType_of_epi (monoRangeSubmoduleIso G.arrow).hom hG.2⟩

/-- The inclusion of one sheaf submodule into a larger one. -/
def submoduleInclusion {M : Modules.{u, u} B S hS X hX} {N₁ N₂ : M.Submodule} (h : N₁ ≤ N₂) :
    N₁.toSheafOfModules ⟶ N₂.toSheafOfModules :=
  ⟨{ app U := ModuleCat.ofHom (LinearMap.codRestrict (N₂.obj U) (N₁.ι.val.app U).hom
        (fun x => h U x.2))
     naturality {U V} g := by
       ext x
       exact Subtype.ext (PresheafOfModules.naturality_apply N₁.ι.val g x) }⟩

/-- The inclusion `N₁ ⟶ N₂` followed by the inclusion of `N₂` is the inclusion of `N₁`. -/
theorem submoduleInclusion_ι {M : Modules.{u, u} B S hS X hX} {N₁ N₂ : M.Submodule}
    (h : N₁ ≤ N₂) : submoduleInclusion B S hS h ≫ N₂.ι = N₁.ι := rfl

set_option synthInstance.maxHeartbeats 400000 in
-- instance synthesis through the sheaf-of-modules and `Subobject` APIs over the small étale site
/-- **The least upper bound of two finite type quasi-coherent submodules.**  For two finite type
quasi-coherent submodules `K₁, K₂` of a quasi-coherent `𝒪_X`-module `ℋ`, the image of
`K₁ ⊕ K₂ ⟶ ℋ` is a finite type quasi-coherent submodule containing both, and it is contained in
every submodule containing both. -/
theorem exists_submodule_sup_isQuasicoherentOnSite_isFiniteType
    {H : Modules.{u, u} B S hS X hX} (hH : H.IsQuasicoherentOnSite) (K₁ K₂ : H.Submodule)
    (h₁ : K₁.toSheafOfModules.IsQuasicoherentOnSite ∧ K₁.toSheafOfModules.IsFiniteType)
    (h₂ : K₂.toSheafOfModules.IsQuasicoherentOnSite ∧ K₂.toSheafOfModules.IsFiniteType) :
    ∃ K : H.Submodule,
      (K.toSheafOfModules.IsQuasicoherentOnSite ∧ K.toSheafOfModules.IsFiniteType) ∧
        K₁ ≤ K ∧ K₂ ≤ K ∧ ∀ N : H.Submodule, K₁ ≤ N → K₂ ≤ N → K ≤ N := by
  classical
  have hres : ∀ (M : Modules.{u, u} B S hS X hX)
      {Y Z : (smallEtaleRingedSite B S hS X hX).C}, (Y ⟶ Z) →
      (M.over Z).HasGlobalPresentation → (M.over Y).HasGlobalPresentation :=
    fun M _ _ f h => Stacks.SheafOfModules.hasGlobalPresentation_overMap M f h
  let f : K₁.toSheafOfModules ⊞ K₂.toSheafOfModules ⟶ H := biprod.desc K₁.ι K₂.ι
  let I : Subobject H := imageSubobject f
  have hsumq : (K₁.toSheafOfModules ⊞ K₂.toSheafOfModules).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.biprod hres h₁.1 h₂.1
  have : K₁.toSheafOfModules.IsFiniteType := h₁.2
  have : K₂.toSheafOfModules.IsFiniteType := h₂.2
  have hsumf : (K₁.toSheafOfModules ⊞ K₂.toSheafOfModules).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_biprod
  have hIq : (I : Modules.{u, u} B S hS X hX).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_image B S hS X hX
      (isClosedUnderKernels_quasicoherentSheaves B S hS X hX
        (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X hX))
      (isClosedUnderCokernels_quasicoherentSheaves B S hS X hX) f hsumq hH
  have hIf : (I : Modules.{u, u} B S hS X hX).IsFiniteType := by
    have : Epi (factorThruImageSubobject f) := by
      dsimp [factorThruImageSubobject]
      apply epi_comp
    exact Stacks.SheafOfModules.isFiniteType_of_epi
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))
      (factorThruImageSubobject f) hsumf
  have hKI : Subobject.mk (monoRangeSubmodule I.arrow).ι = I :=
    subobject_mk_monoRangeSubmodule_ι I
  have hle : ∀ N : H.Submodule, Subobject.mk N.ι ≤ I → N ≤ monoRangeSubmodule I.arrow :=
    fun N h => submodule_le_of_subobject_mk_ι_le (by rw [hKI]; exact h)
  refine ⟨monoRangeSubmodule I.arrow,
    isQuasicoherentOnSite_isFiniteType_monoRangeSubmodule B S hS I ⟨hIq, hIf⟩, ?_, ?_, ?_⟩
  · exact hle K₁ (Subobject.mk_le_of_comm (biprod.inl ≫ factorThruImageSubobject f)
      (by simp [f, I]))
  · exact hle K₂ (Subobject.mk_le_of_comm (biprod.inr ≫ factorThruImageSubobject f)
      (by simp [f, I]))
  · intro N hN₁ hN₂
    refine submodule_le_of_subobject_mk_ι_le ?_
    rw [hKI]
    exact imageSubobject_le_mk N.ι f
      (biprod.desc (submoduleInclusion B S hS hN₁) (submoduleInclusion B S hS hN₂))
      (by ext; simp [f, submoduleInclusion_ι])

/-- Some submodule is a finite type quasi-coherent submodule. -/
theorem exists_submodule_bot_isQuasicoherentOnSite_isFiniteType
    {H : Modules.{u, u} B S hS X hX} (hH : H.IsQuasicoherentOnSite) :
    ∃ K : H.Submodule,
      K.toSheafOfModules.IsQuasicoherentOnSite ∧ K.toSheafOfModules.IsFiniteType := by
  have := hH
  obtain ⟨G⟩ := (isFiltered_finiteTypeQuasicoherentSubobject B S hS X hX H).nonempty
  exact ⟨monoRangeSubmodule G.obj.arrow,
    isQuasicoherentOnSite_isFiniteType_monoRangeSubmodule B S hS G.obj G.property⟩

/-- **Finitely many finite type quasi-coherent submodules have a finite type quasi-coherent upper
bound.** -/
theorem exists_submodule_isFiniteType_forall_le {H : Modules.{u, u} B S hS X hX}
    (hH : H.IsQuasicoherentOnSite) {ι : Type*} [Finite ι] (K : ι → H.Submodule)
    (hK : ∀ i, (K i).toSheafOfModules.IsQuasicoherentOnSite ∧
      (K i).toSheafOfModules.IsFiniteType) :
    ∃ K' : H.Submodule,
      (K'.toSheafOfModules.IsQuasicoherentOnSite ∧ K'.toSheafOfModules.IsFiniteType) ∧
        ∀ i, K i ≤ K' := by
  classical
  have := Fintype.ofFinite ι
  suffices h : ∀ s : Finset ι, ∃ K' : H.Submodule,
      (K'.toSheafOfModules.IsQuasicoherentOnSite ∧ K'.toSheafOfModules.IsFiniteType) ∧
        ∀ i ∈ s, K i ≤ K' by
    obtain ⟨K', hK', h⟩ := h Finset.univ
    exact ⟨K', hK', fun i => h i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨K', hK'⟩ := exists_submodule_bot_isQuasicoherentOnSite_isFiniteType B S hS hH
    exact ⟨K', hK', fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s _ ih =>
    obtain ⟨K', hK', hle⟩ := ih
    obtain ⟨K'', hK'', ha, hs, -⟩ :=
      exists_submodule_sup_isQuasicoherentOnSite_isFiniteType B S hS hH (K a) K' (hK a) hK'
    refine ⟨K'', hK'', fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact ha
    · exact (hle i hi).trans hs

/-- Membership in a submodule passes to a larger submodule. -/
theorem mem_of_submodule_le {M : Modules.{u, u} B S hS X hX} {N₁ N₂ : M.Submodule} (h : N₁ ≤ N₂)
    {U : SmallEtale B S hS X} {s : M.val.obj (op U)} (hs : s ∈ N₁.obj (op U)) :
    s ∈ N₂.obj (op U) :=
  h (op U) hs

end Sup

section Affine

/-- **The affine case of the section form of Stacks 0829.**  On an affine algebraic space `V`,
every section of a quasi-coherent `𝒪_V`-module `ℋ` over an affine étale chart `T` lies in a
finite type quasi-coherent submodule of `ℋ`. -/
theorem exists_submodule_isFiniteType_mem_of_isAffineSpace
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (hVa : IsAffineSpace B S hS V) (H : Modules.{u, u} B S hS V hV)
    (hH : H.IsQuasicoherentOnSite) (T : SmallEtale B S hS V)
    (hT : IsAffine ((SmallEtale.toOver B S hS V ⋙ BigFppfOver.toScheme B S hS).obj T))
    (s : H.val.obj (op T)) :
    ∃ K : H.Submodule,
      (K.toSheafOfModules.IsQuasicoherentOnSite ∧ K.toSheafOfModules.IsFiniteType) ∧
        s ∈ K.obj (op T) := by
  classical
  obtain ⟨T₀, hT₀, ⟨e⟩⟩ := hVa
  have hcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS V hV H hH
  obtain ⟨x, hx⟩ := (hcart _ _ (isAffine_isoChart B S hS e hT₀) hT (toIsoChart B S hS e T)).2 s
  suffices h : ∀ y, ∃ K : H.Submodule,
      (K.toSheafOfModules.IsQuasicoherentOnSite ∧ K.toSheafOfModules.IsFiniteType) ∧
        sectionsBaseChange H (toIsoChart B S hS e T) y ∈ K.obj (op T) by
    obtain ⟨K, hK, hmem⟩ := h x
    exact ⟨K, hK, hx ▸ hmem⟩
  intro y
  induction y using TensorProduct.inductionOn with
  | tmul b n =>
    rw [chartBaseChange_tmul]
    have := hH
    let u := isoChartSectionHom B S hS hV e H n
    let G : Subobject H := imageSubobject u
    refine ⟨monoRangeSubmodule G.arrow, isQuasicoherentOnSite_isFiniteType_monoRangeSubmodule
      B S hS G (imageSubobject_unit_mem B S hS hV H u), Submodule.smul_mem _ b ?_⟩
    refine ⟨(factorThruImageSubobject u).val.app (op T)
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V hV).O).obj.obj
        (op T)), ?_⟩
    change ((factorThruImageSubobject u ≫ G.arrow).val.app (op T)) _ = _
    rw [imageSubobject_arrow_comp, isoChartSectionHom_app_one B S hS hV e H n T]
    rfl
  | add a c ha hc =>
    obtain ⟨K₁, hK₁, h₁⟩ := ha
    obtain ⟨K₂, hK₂, h₂⟩ := hc
    obtain ⟨K, hK, hle₁, hle₂, -⟩ :=
      exists_submodule_sup_isQuasicoherentOnSite_isFiniteType B S hS hH K₁ K₂ hK₁ hK₂
    refine ⟨K, hK, ?_⟩
    rw [map_add]
    exact Submodule.add_mem _
      (mem_of_submodule_le B S hS hle₁ h₁) (mem_of_submodule_le B S hS hle₂ h₂)

end Affine

section Generation

/-- **A submodule of finite type on a quasi-compact algebraic space is generated by finitely many
sections over affine charts.**  For a submodule `𝒢` of finite type of an `𝒪_Z`-module `ℳ` on a
quasi-compact algebraic space `Z`, there are finitely many affine étale charts `Tᵢ` of `Z` and
sections `sᵢ` of `𝒢` over them such that every submodule of `ℳ` containing the `sᵢ` contains
`𝒢`. -/
theorem exists_finite_affine_sections_of_isFiniteType {Z : AlgebraicSpaces B S hS}
    (hZqc : IsQuasiCompactSpace B S hS Z.1) {M : Modules.{u, u} B S hS Z.1 Z.2}
    (G : M.Submodule) (hG : G.toSheafOfModules.IsFiniteType) :
    ∃ (ι : Type u) (_ : Finite ι) (T : ι → SmallEtale B S hS Z.1)
      (s : ∀ i, M.val.obj (op (T i))),
      (∀ i, IsAffine ((SmallEtale.toOver B S hS Z.1 ⋙ BigFppfOver.toScheme B S hS).obj (T i))) ∧
        (∀ i, s i ∈ G.obj (op (T i))) ∧
          ∀ N : M.Submodule, (∀ i, s i ∈ N.obj (op (T i))) → G ≤ N := by
  classical
  have : G.toSheafOfModules.IsFiniteType := hG
  set J := (smallEtaleRingedSite B S hS Z.1 Z.2).J
  obtain ⟨I₀, W, hW, hgen⟩ :=
    (Stacks.SheafOfModules.isFiniteTypeSections_of_isFiniteType (J := J)
      G.toSheafOfModules).exists_generators
  choose n g hg using hgen
  obtain ⟨U₀, φ, haff, hsurj, het⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Z.1 Z.2).1 hZqc
  have hid : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj U₀)) := by
    have het₀ : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (𝟙 U₀)) := by
      rw [CategoryTheory.Functor.map_id]
      infer_instance
    simpa using (presheaf_yoneda_map_etale_iff B S hS (𝟙 U₀)).2 het₀
  have hchart : IsEtaleChart B S hS Z.1 (CostructuredArrow.mk φ) := by
    have h₀ := het U₀ (𝟙 (yoneda.obj U₀)) hid
    rwa [Category.id_comp] at h₀
  set A : SmallEtale B S hS Z.1 := ⟨CostructuredArrow.mk φ, hchart⟩
  have hAaff : IsAffine
      ((SmallEtale.toOver B S hS Z.1 ⋙ BigFppfOver.toScheme B S hS).obj A) := haff
  have hAcov : J.CoversTop (fun _ : PUnit.{u + 2} => A) :=
    SmallEtale.coversTop_of_isSurjective B S hS Z.1 Z.2 A
      ((presheafSurjective_iff_isSurjective_yoneda B S hS Z.1 Z.2 U₀ φ).1 hsurj)
  obtain ⟨ι₁, hι₁, V, f₁, hVaff, hle₁, hcov₁⟩ :=
    SmallEtale.exists_finite_affine_refinement B S hS Z.1 A hAaff _ (hW A)
  have := hι₁
  choose b hb using fun t => (Sieve.mem_ofObjects_iff W (f₁ t)).1
    (hle₁ _ (Sieve.ofArrows_mk V f₁ t))
  set q : ∀ t, V t ⟶ W (b t) := fun t => (hb t).some
  have hs₁ : ∀ t, Stacks.SheafOfModules.GeneratesLocally J G.toSheafOfModules.val
      (fun j => G.toSheafOfModules.val.restrictₛₗ (q t).op (g (b t) j)) := fun t =>
    Stacks.SheafOfModules.generatesLocally_restrict (q t) (hg (b t))
  have hVcov : J.CoversTop V :=
    Stacks.Sites.coversTop_of_exists_hom
      (Stacks.Sites.coversTop_bind hAcov (fun (_ : PUnit.{u + 2}) t => f₁ t) (fun _ => hcov₁))
      fun p => ⟨p.2, ⟨𝟙 _⟩⟩
  let r : ∀ t, Fin (n (b t)) → G.toSheafOfModules.val.obj (op (V t)) :=
    fun t j => G.toSheafOfModules.val.restrictₛₗ (q t).op (g (b t) j)
  refine ⟨ULift.{u} (Σ t : ι₁, Fin (n (b t))), inferInstance, fun p => V p.down.1,
    fun p => (r p.down.1 p.down.2).1, fun p => hVaff p.down.1,
    fun p => (r p.down.1 p.down.2).2, ?_⟩
  intro N hN Y x hx
  refine N.isSheaf (X := Y) x ?_
  refine J.transitive (hVcov Y.unop) _ fun Y' h hh => ?_
  obtain ⟨t, ⟨k⟩⟩ := (Sieve.mem_ofObjects_iff V h).1 hh
  obtain ⟨S', hS', hlin⟩ := hs₁ t Y' k (G.toSheafOfModules.val.map h.op ⟨x, hx⟩)
  refine J.superset_covering ?_ hS'
  intro Y'' a ha
  obtain ⟨coef, hcoef⟩ := hlin Y'' a ha
  change M.val.map (a ≫ h).op x ∈ N.obj (op Y'')
  have hval : M.val.map (a ≫ h).op x =
      (G.toSheafOfModules.val.restrictₛₗ a.op (G.toSheafOfModules.val.map h.op ⟨x, hx⟩)).1 := by
    change M.val.map (a ≫ h).op x = M.val.map a.op (M.val.map h.op x)
    rw [op_comp, PresheafOfModules.map_comp_apply]
  rw [hval, ← hcoef]
  change (G.ι.val.app (op Y'')) _ ∈ N.obj (op Y'')
  rw [map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  exact N.map (a ≫ k).op (hN ⟨⟨t, j⟩⟩)

end Generation

end AlgebraicGeometry.Space

end
