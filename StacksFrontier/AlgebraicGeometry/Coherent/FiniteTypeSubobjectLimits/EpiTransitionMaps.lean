module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeColimit
public import StacksFrontier.AlgebraicGeometry.Coherent.FiniteTypeSubobjectLimits.DirectedColimit
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectColimit
/-!
# Finite type modules as directed colimits with surjective transition maps

On a quasi-compact and quasi-separated scheme a quasi-coherent module of finite type is a
directed colimit of finitely presented modules whose transition maps are surjective.

The construction starts from the directed system of
`AlgebraicGeometry.exists_directed_system_of_isFinitePresentation`. One stage `G` of that system
already surjects onto the module `M`, because `M` is of finite type; the kernel `K` of that
surjection is the colimit of its quasi-coherent finite type submodules, and dividing `G` by those
submodules gives a filtered system of finitely presented quotients of `G` with colimit `M`. Being
quotients of a single object, its transition maps are surjective. Reindexing by a directed
partial order through a final functor finishes the proof.

## Main results

* `AlgebraicGeometry.exists_directed_colimit_finitePresentation_with_epi_maps`: the directed
  system of finitely presented modules with surjective transition maps.

## References

* [Stacks Project, Tag 086M](https://stacks.math.columbia.edu/tag/086M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.QcohLimits (isQuasicoherent_kernel)
open Stacks.SheafOfModules (isFiniteType_of_iso isFinitePresentation_cokernel)

universe u

namespace AlgebraicGeometry

open Scheme.Modules

section

universe v w c wC

/-- For a natural transformation into a constant functor, the cokernel projection at one index
followed by a transition map of the cokernel is the cokernel projection at the other index. -/
@[reassoc]
private lemma cokernel_π_app_comp_map {J : Type v} [Category.{w, v} J]
    {C : Type c} [Category.{wC, c} C] [Abelian C] {A : J ⥤ C} {B : C}
    (α : A ⟶ (Functor.const J).obj B) {j j' : J} (f : j ⟶ j') :
    (cokernel.π α).app j ≫ (cokernel α).map f = (cokernel.π α).app j' := by
  simpa using ((cokernel.π α).naturality f).symm

/-- In the cokernel of a natural transformation to a constant functor, every transition map is
an epimorphism: it is preceded by the epimorphism `cokernel.π` at the source index, and that
composite is the epimorphism `cokernel.π` at the target index. -/
private lemma epi_cokernel_transition {J : Type v} [Category.{w, v} J]
    {C : Type c} [Category.{wC, c} C] [Abelian C]
    (B : C) (A : J ⥤ C) (α : A ⟶ (Functor.const J).obj B)
    {j j' : J} (f : j ⟶ j') : Epi ((cokernel α).map f) :=
  have : Epi ((cokernel.π α).app j') := inferInstance
  epi_of_epi_fac (cokernel_π_app_comp_map α f)

/-- Over a filtered index category, the composites of the cokernel projections with the legs of
a cocone on the cokernel of a natural transformation to a constant functor all agree. -/
private lemma cokernel_π_app_comp_ι_app_eq {J : Type v} [Category.{w, v} J] [IsFilteredOrEmpty J]
    {C : Type c} [Category.{wC, c} C] [Abelian C] {A : J ⥤ C} {B : C}
    (α : A ⟶ (Functor.const J).obj B) (s : Cocone (cokernel α)) (j j' : J) :
    (cokernel.π α).app j ≫ s.ι.app j = (cokernel.π α).app j' ≫ s.ι.app j' := by
  obtain ⟨k, f, g, -⟩ := IsFilteredOrEmpty.cocone_objs j j'
  rw [← s.w f, ← s.w g, cokernel_π_app_comp_map_assoc α f, cokernel_π_app_comp_map_assoc α g]

/-- The cocone with point `M` on the cokernel of `α` followed by the inclusion of `kernel p`,
induced by `p`. -/
private noncomputable abbrev cokernelCoconeOfKernel
    {J : Type v} [Category.{w, v} J] {C : Type c} [Category.{wC, c} C]
    [Abelian C] {G M : C} (p : G ⟶ M) {A : J ⥤ C}
    (α : A ⟶ (Functor.const J).obj (kernel p)) :
    Cocone (cokernel (α ≫ (Functor.const J).map (kernel.ι p))) :=
  Cocone.mk M (cokernel.desc (α ≫ (Functor.const J).map (kernel.ι p))
    ((Functor.const J).map p) (by ext; simp))

/-- The legs of `cokernelCoconeOfKernel p α` factor `p` through the cokernel projections. -/
@[reassoc]
private lemma cokernel_π_app_comp_cokernelCoconeOfKernel_ι_app
    {J : Type v} [Category.{w, v} J] {C : Type c} [Category.{wC, c} C]
    [Abelian C] {G M : C} (p : G ⟶ M) {A : J ⥤ C}
    (α : A ⟶ (Functor.const J).obj (kernel p)) (j : J) :
    (cokernel.π (α ≫ (Functor.const J).map (kernel.ι p))).app j ≫
      (cokernelCoconeOfKernel p α).ι.app j = p := by
  dsimp only [cokernelCoconeOfKernel]
  rw [← NatTrans.comp_app, cokernel.π_desc, Functor.const_map_app]

/-- If `α` exhibits `kernel p` as a filtered colimit, then every cocone on the cokernel of
`α` followed by the inclusion of `kernel p` gives a morphism out of `G` killing `kernel p`. -/
private lemma kernel_ι_comp_cokernel_π_app_comp_ι_app
    {J : Type v} [Category.{w, v} J] {C : Type c} [Category.{wC, c} C]
    [Abelian C] {G M : C} (p : G ⟶ M) {A : J ⥤ C}
    (α : A ⟶ (Functor.const J).obj (kernel p)) [IsFilteredOrEmpty J]
    (hα : IsColimit (Cocone.mk _ α))
    (s : Cocone (cokernel (α ≫ (Functor.const J).map (kernel.ι p)))) (j₀ : J) :
    kernel.ι p ≫ (cokernel.π (α ≫ (Functor.const J).map (kernel.ι p))).app j₀ ≫ s.ι.app j₀ = 0 :=
  hα.hom_ext fun j => by
    have h := NatTrans.congr_app (cokernel.condition (α ≫ (Functor.const J).map (kernel.ι p))) j
    simp only [NatTrans.comp_app, Functor.const_map_app, NatTrans.app_zero, Category.assoc] at h
    rw [cokernel_π_app_comp_ι_app_eq _ s j₀ j]
    simp [reassoc_of% h]

/-- If `α` exhibits `kernel p` as a filtered colimit and `p` is an epimorphism, then
`cokernelCoconeOfKernel p α` is a colimit cocone. -/
private noncomputable def isColimitCokernelCoconeOfKernel
    {J : Type v} [Category.{w, v} J] {C : Type c} [Category.{wC, c} C]
    [Abelian C] {G M : C} (p : G ⟶ M) {A : J ⥤ C}
    (α : A ⟶ (Functor.const J).obj (kernel p)) [IsFiltered J] [Epi p]
    (hα : IsColimit (Cocone.mk _ α)) : IsColimit (cokernelCoconeOfKernel p α) where
  desc s := Abelian.epiDesc p _
    (kernel_ι_comp_cokernel_π_app_comp_ι_app p α hα s IsFiltered.nonempty.some)
  fac s j := by
    refine (cancel_epi ((cokernel.π (α ≫ (Functor.const J).map (kernel.ι p))).app j)).1 ?_
    rw [cokernel_π_app_comp_cokernelCoconeOfKernel_ι_app_assoc, Abelian.comp_epiDesc,
      cokernel_π_app_comp_ι_app_eq _ s _ j]
  uniq s m hm := by
    refine (cancel_epi p).1 ?_
    rw [Abelian.comp_epiDesc, ← hm, cokernel_π_app_comp_cokernelCoconeOfKernel_ι_app_assoc]

end

/-- **Stacks Project, Tag 086M.** A finite type quasi-coherent module on a quasi-compact and
quasi-separated scheme is a directed colimit of finitely presented modules with surjective
transition maps. -/
@[stacks 086M, ega "IV 1.7.9" "I.9.6.5 clause"]
theorem exists_directed_colimit_finitePresentation_with_epi_maps
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ (ι : Type u) (_ : PartialOrder ι) (_ : Nonempty ι) (_ : IsDirected ι (· ≤ ·))
      (F : ι ⥤ X.Modules) (_e : colimit F ≅ M),
      (∀ i, (F.obj i).IsFinitePresentation) ∧
        ∀ ⦃i j : ι⦄ (h : i ≤ j), Epi (F.map (homOfLE h)) := by
  obtain ⟨I, hI, hIne, hIdir, D, φ, hfp, ⟨hc⟩⟩ :=
    exists_directed_system_of_isFinitePresentation X M
  let eM : colimit D ≅ M := (hc.coconePointUniqueUpToIso (colimit.isColimit D)).symm
  have hMft : SheafOfModules.IsFiniteType.{u, u, u} M := inferInstance
  have hcolft : (colimit D).IsFiniteType :=
    @Stacks.SheafOfModules.isFiniteType_of_iso.{u} _ _ _ _ _ _ _ _ _ eM.symm hMft
  have : CompactSpace X.toPresheafedSpace := inferInstance
  obtain ⟨i, hi⟩ := @Stacks.SheafOfModules.exists_epi_to_colimit_of_isFiniteType.{u}
    X.toPresheafedSpace X.ringCatSheaf _ _ _ _ I _ _ _ _ D hcolft
  let G := D.obj i
  let p : G ⟶ M := colimit.ι D i ≫ eM.hom
  have : Epi (colimit.ι D i) := hi
  have : Epi p := inferInstanceAs (Epi (colimit.ι D i ≫ eM.hom))
  let K := kernel p
  have : K.IsQuasicoherent :=
    @isQuasicoherent_kernel X G M p
      (@SheafOfModules.instIsQuasicoherentOfIsFinitePresentation _ _ _ _ _ _ G (hfp i))
      inferInstance
  let J := FiniteTypeQuasicoherentSubobject K
  let A := finiteTypeQuasicoherentSubobjectFunctor K
  let cA := finiteTypeQuasicoherentSubobjectCocone K
  have hA : IsColimit cA := isColimit_finiteTypeQuasicoherentSubobjectCocone K
  let B := (Functor.const J).obj G
  let β : A ⟶ B := cA.ι ≫ (Functor.const J).map (kernel.ι p)
  let Q := cokernel β
  have hQfp (j : J) : (Q.obj j).IsFinitePresentation := by
    have : (A.obj j).IsFiniteType := j.property.2
    have : (B.obj j).IsFinitePresentation := hfp i
    exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
      (PreservesCokernel.iso ((evaluation J X.Modules).obj j) β).symm
      (isFinitePresentation_cokernel (β.app j))
  have : FinallySmall.{u} J := finallySmall_of_essentiallySmall J
  obtain ⟨S, _, _, e, _⟩ := FinallySmall.exists_of_isFiltered.{u} J
  obtain ⟨ι, _, hιdir, hιne, r, _⟩ := CategoryTheory.IsFiltered.exists_directed S
  let F := (r ⋙ e) ⋙ Q
  exact ⟨ι, inferInstance, hιne, hιdir, F,
    (((Functor.Final.isColimitWhiskerEquiv (r ⋙ e) _).symm
      (isColimitCokernelCoconeOfKernel p cA.ι hA)).coconePointUniqueUpToIso
        (colimit.isColimit F)).symm,
    fun j => hQfp (e.obj (r.obj j)),
    fun _ _ h => epi_cokernel_transition G A β (e.map (r.map (homOfLE h)))⟩

end AlgebraicGeometry

end
