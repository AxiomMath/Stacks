module

public import Mathlib.Basic.Finite.Sum
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.DirectedColimit.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationCokernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitFinitePresentationSite

/-!
# Finite presentation of sheaves of modules is closed under finite colimits

The property `SheafOfModules.isFinitePresentation` of sheaves of modules on the site of opens
of a topological space, and in particular of `𝒪_X`-modules on a scheme, is closed under finite
colimits. Consequently the canonical diagram of finitely presented `𝒪_X`-modules over a fixed
`𝒪_X`-module is filtered, as in [Stacks, Tag 01PJ].

## Main results

* `Stacks.Tag01PJFiniteColimits.coprodPresentation`: a coproduct of two presentations of sheaves
  of modules is a presentation of their coproduct, finite when both are finite.
* `Stacks.Tag01PJFiniteColimits.isFinitePresentation_coprod`: a coproduct of two finitely
  presented sheaves of modules on an arbitrary site is finitely presented.
* `Stacks.Tag01PJFiniteColimits.isClosedUnderFiniteColimits_isFinitePresentation`: on the site of
  opens of a topological space, `SheafOfModules.isFinitePresentation` is closed under finite
  colimits.
* `Stacks.Tag01PJFiniteColimits.isClosedUnderFiniteColimits_scheme`: the same for the `𝒪_X`-modules
  of a scheme, proposition (1) of [Stacks, Tag 01PJ].
* `Stacks.Tag01PJFiniteColimits.isFiltered_finitePresentationOver_scheme`: the canonical diagram
  of finitely presented `𝒪_X`-modules over a fixed `F` is filtered.
* `Stacks.Tag01PJFiniteColimits.exists_directed_system_of_essentiallySmall_of_isDenseAt`: an
  `𝒪_X`-module at which the finitely presented modules are dense, and among which they are
  essentially small, is a directed colimit of finitely presented modules.

## References

* [Stacks Project, Tag 01PJ](https://stacks.math.columbia.edu/tag/01PJ)
* [Stacks Project, Tag 01PK](https://stacks.math.columbia.edu/tag/01PK)
* [Stacks Project, Tag 0H96](https://stacks.math.columbia.edu/tag/0H96)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits SheafOfModules

universe w v u v₂ u₂

namespace Stacks.Tag01PJFiniteColimits

section General

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryCoproducts C]

/-- The coproduct of two composable pairs with zero composites has zero composite. -/
theorem coprod_map_comp_eq_zero {P₁ B₁ Q₁ P₂ B₂ Q₂ : C} {f₁ : P₁ ⟶ B₁} {g₁ : B₁ ⟶ Q₁}
    {f₂ : P₂ ⟶ B₂} {g₂ : B₂ ⟶ Q₂} (h₁ : f₁ ≫ g₁ = 0) (h₂ : f₂ ≫ g₂ = 0) :
    coprod.map f₁ f₂ ≫ coprod.map g₁ g₂ = 0 := by
  apply coprod.hom_ext <;> simp [h₁, h₂]

/-- The coproduct of two cokernel diagrams is a cokernel diagram. -/
noncomputable def isColimitCokernelCoforkCoprodMap {P₁ B₁ Q₁ P₂ B₂ Q₂ : C} {f₁ : P₁ ⟶ B₁}
    {g₁ : B₁ ⟶ Q₁} {f₂ : P₂ ⟶ B₂} {g₂ : B₂ ⟶ Q₂} {h₁ : f₁ ≫ g₁ = 0} {h₂ : f₂ ≫ g₂ = 0}
    (c₁ : IsColimit (CokernelCofork.ofπ g₁ h₁)) (c₂ : IsColimit (CokernelCofork.ofπ g₂ h₂)) :
    IsColimit (CokernelCofork.ofπ (f := coprod.map f₁ f₂) (coprod.map g₁ g₂)
      (coprod_map_comp_eq_zero h₁ h₂)) := by
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun {T} t ht => coprod.desc
      (c₁.desc (CokernelCofork.ofπ (coprod.inl ≫ t) ?_))
      (c₂.desc (CokernelCofork.ofπ (coprod.inr ≫ t) ?_))) ?_ ?_
  · simpa using (coprod.inl : P₁ ⟶ P₁ ⨿ P₂) ≫= ht
  · simpa using (coprod.inr : P₂ ⟶ P₁ ⨿ P₂) ≫= ht
  · intro T t ht
    simp only [coprod.map_desc]
    refine coprod.hom_ext ?_ ?_
    · simp only [coprod.inl_desc]
      exact c₁.fac (CokernelCofork.ofπ (coprod.inl ≫ t) _) WalkingParallelPair.one
    · simp only [coprod.inr_desc]
      exact c₂.fac (CokernelCofork.ofπ (coprod.inr ≫ t) _) WalkingParallelPair.one
  · intro T t ht m hm
    refine coprod.hom_ext ?_ ?_
    · simp only [coprod.inl_desc]
      refine Cofork.IsColimit.hom_ext c₁ ?_
      refine Eq.trans ?_ (c₁.fac (CokernelCofork.ofπ (coprod.inl ≫ t) _)
        WalkingParallelPair.one).symm
      simpa using (coprod.inl : B₁ ⟶ B₁ ⨿ B₂) ≫= hm
    · simp only [coprod.inr_desc]
      refine Cofork.IsColimit.hom_ext c₂ ?_
      refine Eq.trans ?_ (c₂.fac (CokernelCofork.ofπ (coprod.inr ≫ t) _)
        WalkingParallelPair.one).symm
      simpa using (coprod.inr : B₂ ⟶ B₁ ⨿ B₂) ≫= hm

end General

section Presentations

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The two legs of a presentation of `M ⨿ N` built from presentations of `M` and of `N`:
the free sheaf of modules on the sum of the two generator types maps onto `M ⨿ N`. -/
noncomputable def coprodPresentationπ {M N : SheafOfModules.{w} R}
    (P : M.Presentation) (Q : N.Presentation) :
    free (R := R) (P.generators.I ⊕ Q.generators.I) ⟶ M ⨿ N :=
  (freeSumIso P.generators.I Q.generators.I).inv ≫ coprod.map P.generators.π Q.generators.π

/-- The relations leg of the presentation of `M ⨿ N` built from presentations of `M` and of `N`:
the free sheaf of modules on the sum of the two relation types maps to the free sheaf of modules
on the sum of the two generator types. -/
noncomputable def coprodPresentationRel {M N : SheafOfModules.{w} R}
    (P : M.Presentation) (Q : N.Presentation) :
    free (R := R) (P.relations.I ⊕ Q.relations.I) ⟶
      free (R := R) (P.generators.I ⊕ Q.generators.I) :=
  (freeSumIso P.relations.I Q.relations.I).inv ≫
    coprod.map ((freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π)
      ((freeHomEquiv _).symm Q.relations.s ≫ kernel.ι Q.generators.π) ≫
    (freeSumIso P.generators.I Q.generators.I).hom

/-- The relations leg composed with the generators leg of the presentation of `M ⨿ N` is
zero. -/
theorem coprodPresentationRel_comp_π {M N : SheafOfModules.{w} R}
    (P : M.Presentation) (Q : N.Presentation) :
    coprodPresentationRel P Q ≫ coprodPresentationπ P Q = 0 := by
  dsimp only [coprodPresentationRel, coprodPresentationπ]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [coprod_map_comp_eq_zero (by simp) (by simp), comp_zero]

/-- The presentation of `M ⨿ N` built from presentations of `M` and of `N`: if `M` is the
cokernel of a map `free ι₁ ⟶ free σ₁` and `N` the cokernel of `free ι₂ ⟶ free σ₂`, then `M ⨿ N`
is the cokernel of the induced map `free (ι₁ ⊕ ι₂) ⟶ free (σ₁ ⊕ σ₂)`. -/
noncomputable def coprodPresentation {M N : SheafOfModules.{w} R}
    (P : M.Presentation) (Q : N.Presentation) : (M ⨿ N).Presentation :=
  presentationOfIsCokernelFree (coprodPresentationRel P Q) (coprodPresentationπ P Q)
    (coprodPresentationRel_comp_π P Q) <| by
  refine CokernelCofork.isColimitOfIsColimitOfIff
    (isColimitCokernelCoforkCoprodMap P.isColimit Q.isColimit)
    (coprodPresentationRel P Q) (freeSumIso P.generators.I Q.generators.I).symm ?_
  intro W φ
  dsimp only [coprodPresentationRel, Iso.symm_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, comp_zero]
  · exact (cancel_epi (freeSumIso P.relations.I Q.relations.I).inv).1 (by simpa using h)

/-- A coproduct of two finite presentations is a finite presentation. -/
instance coprodPresentation_isFinite {M N : SheafOfModules.{w} R}
    (P : M.Presentation) (Q : N.Presentation) [P.IsFinite] [Q.IsFinite] :
    (coprodPresentation P Q).IsFinite := by
  have hg₁ : Finite P.generators.I := GeneratingSections.IsFiniteType.finite
  have hg₂ : Finite Q.generators.I := GeneratingSections.IsFiniteType.finite
  have hr₁ : Finite P.relations.I := GeneratingSections.IsFiniteType.finite
  have hr₂ : Finite Q.relations.I := GeneratingSections.IsFiniteType.finite
  exact ⟨⟨inferInstanceAs (Finite (P.generators.I ⊕ Q.generators.I))⟩,
    ⟨inferInstanceAs (Finite (P.relations.I ⊕ Q.relations.I))⟩⟩

/-- The image of a finite presentation under a colimit-preserving functor taking the unit sheaf
to the unit sheaf is again finite. -/
theorem presentation_map_isFinite {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
    {S : Sheaf K RingCat.{w}} [HasSheafify K AddCommGrpCat.{w}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {M : SheafOfModules.{w} R} (P : M.Presentation) [P.IsFinite]
    (T : SheafOfModules.{w} R ⥤ SheafOfModules.{w} S) [PreservesColimitsOfSize.{w, w} T]
    (η : SheafOfModules.unit S ≅ T.obj (SheafOfModules.unit R)) :
    (P.map T η).IsFinite := by
  have hg : Finite P.generators.I := GeneratingSections.IsFiniteType.finite
  have hr : Finite P.relations.I := GeneratingSections.IsFiniteType.finite
  exact ⟨⟨by simpa only [Presentation.map_generators_I] using hg⟩,
    ⟨by simpa only [Presentation.map_relations_I] using hr⟩⟩

end Presentations

section Locality

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A sheaf of modules with a global finite presentation is of finite presentation. -/
theorem isFinitePresentation_of_presentation {M : SheafOfModules.{w} R}
    (P : M.Presentation) [P.IsFinite] : M.IsFinitePresentation := by
  refine IsFinitePresentation.mk ⟨P.quasicoherentData, ?_⟩
  refine QuasicoherentData.IsFinitePresentation.mk ?_
  intro x
  change C at x
  dsimp only [Presentation.quasicoherentData]
  exact presentation_map_isFinite P (T := pushforward (𝟙 (R.over x))) (η := Iso.refl _)

/-- A finite free sheaf of modules is of finite presentation. -/
instance isFinitePresentation_free (I : Type w) [Finite I] :
    (free (R := R) I).IsFinitePresentation :=
  isFinitePresentation_of_presentation (Stacks.SheafOfModules.Site.freePresentation I)

/-- Over an object of the site where both `M` and `N` carry a finite presentation, so does
`M ⨿ N`. -/
theorem exists_finitePresentation_coprod_over (M N : SheafOfModules.{w} R) (U : C)
    (P : (M.over U).Presentation) [P.IsFinite] (Q : (N.over U).Presentation) [Q.IsFinite] :
    ∃ S : ((M ⨿ N).over U).Presentation, S.IsFinite := by
  let T := overFunctor R U
  let _ : PreservesFiniteColimits T :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U
  exact ⟨(coprodPresentation P Q).ofIsIso (PreservesColimitPair.iso T M N).hom, inferInstance⟩

/-- The objects of the site over which `M ⨿ N` carries a finite presentation cover the final
object. -/
theorem coversTop_finitePresentation_coprod (M N : SheafOfModules.{w} R)
    [M.IsFinitePresentation] [N.IsFinitePresentation] :
    J.CoversTop (Subtype.val :
      { U : C // ∃ S : ((M ⨿ N).over U).Presentation, S.IsFinite } → C) := by
  classical
  obtain ⟨qM, hqM⟩ := IsFinitePresentation.exists_quasicoherentData M
  obtain ⟨qN, hqN⟩ := IsFinitePresentation.exists_quasicoherentData N
  intro Y
  apply J.transitive (qM.coversTop Y)
  intro V f hf
  obtain ⟨i, ⟨c⟩⟩ := (Sieve.mem_ofObjects_iff _ f).1 hf
  have _ : (qM.presentation i).IsFinite := hqM.isFinite_presentation i
  obtain ⟨PV, hPV⟩ := Stacks.SheafOfModules.LocalCokernel.exists_finitePresentation_overMap
    M c (qM.presentation i)
  refine J.superset_covering ?_ (qN.coversTop V)
  intro W g hg
  obtain ⟨j, ⟨d⟩⟩ := (Sieve.mem_ofObjects_iff _ g).1 hg
  have _ : (qN.presentation j).IsFinite := hqN.isFinite_presentation j
  obtain ⟨QW, hQW⟩ := Stacks.SheafOfModules.LocalCokernel.exists_finitePresentation_overMap
    N d (qN.presentation j)
  obtain ⟨PW, hPW⟩ := Stacks.SheafOfModules.LocalCokernel.exists_finitePresentation_overMap
    M g PV
  exact (Sieve.mem_ofObjects_iff _ _).2
    ⟨⟨W, exists_finitePresentation_coprod_over M N W PW QW⟩, ⟨𝟙 W⟩⟩

/-- A coproduct of two finitely presented sheaves of modules is finitely presented. -/
instance isFinitePresentation_coprod (M N : SheafOfModules.{w} R)
    [M.IsFinitePresentation] [N.IsFinitePresentation] : (M ⨿ N).IsFinitePresentation := by
  classical
  exact IsFinitePresentation.mk
    ⟨{ I := { U : C // ∃ S : ((M ⨿ N).over U).Presentation, S.IsFinite }
       X := Subtype.val
       coversTop := coversTop_finitePresentation_coprod M N
       presentation := fun i => i.2.choose },
     QuasicoherentData.IsFinitePresentation.mk fun i => i.2.choose_spec⟩

end Locality

section Space

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- The finitely presented sheaves of modules contain a zero object. -/
instance containsZero_isFinitePresentation :
    (SheafOfModules.isFinitePresentation R).ContainsZero := by
  refine ⟨cokernel (𝟙 (free (R := R) PUnit.{u + 1})), ?_, ?_⟩
  · exact CokernelCofork.IsColimit.isZero_of_epi
      (colimit.isColimit (parallelPair (𝟙 (free (R := R) PUnit.{u + 1})) 0))
  · exact Stacks.SheafOfModules.isFinitePresentation_cokernel (𝟙 _)

/-- Finite presentation is closed under binary coproducts. -/
instance isClosedUnderBinaryCoproducts_isFinitePresentation :
    (SheafOfModules.isFinitePresentation R).IsClosedUnderBinaryCoproducts := by
  refine ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro Z ⟨F, hF⟩
  have h₁ : (F.obj ⟨WalkingPair.left⟩).IsFinitePresentation := hF _
  have h₂ : (F.obj ⟨WalkingPair.right⟩).IsFinitePresentation := hF _
  exact (SheafOfModules.isFinitePresentation R).prop_of_iso
    (HasColimit.isoOfNatIso (diagramIsoPair F)).symm
    (isFinitePresentation_coprod (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩))

/-- Finite presentation is closed under coequalizers. -/
instance isClosedUnderCoequalizers_isFinitePresentation :
    (SheafOfModules.isFinitePresentation R).IsClosedUnderColimitsOfShape
      WalkingParallelPair := by
  refine ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro Z ⟨F, hF⟩
  have h₀ : (F.obj WalkingParallelPair.zero).IsFinitePresentation := hF _
  have h₁ : (F.obj WalkingParallelPair.one).IsFinitePresentation := hF _
  have hfp : (cokernel (F.map WalkingParallelPairHom.left -
      F.map WalkingParallelPairHom.right)).IsFinitePresentation :=
    Stacks.SheafOfModules.isFinitePresentation_cokernel _
  refine (SheafOfModules.isFinitePresentation R).prop_of_iso ?_ hfp
  refine (IsColimit.coconePointUniqueUpToIso
    (Preadditive.isColimitCokernelCoforkOfCofork (colimit.isColimit (parallelPair
      (F.map WalkingParallelPairHom.left) (F.map WalkingParallelPairHom.right))))
    (colimit.isColimit (parallelPair (F.map WalkingParallelPairHom.left -
      F.map WalkingParallelPairHom.right) 0))).symm.trans ?_
  exact (HasColimit.isoOfNatIso (diagramIsoParallelPair F)).symm

/-- Finite presentation is closed under finite coproducts. -/
instance isClosedUnderFiniteCoproducts_isFinitePresentation :
    (SheafOfModules.isFinitePresentation R).IsClosedUnderFiniteCoproducts :=
  ObjectProperty.IsClosedUnderFiniteCoproducts.mk'

/-- [Stacks, Tag 01PJ], proposition (1): the property of being a finitely presented sheaf of
modules on the site of opens of a topological space is closed under finite colimits. -/
instance isClosedUnderFiniteColimits_isFinitePresentation :
    (SheafOfModules.isFinitePresentation R).IsClosedUnderFiniteColimits := by
  have hA : HasColimitsOfShape WalkingParallelPair (SheafOfModules.{u} R) := inferInstance
  have h₁ : PreservesFiniteCoproducts (SheafOfModules.isFinitePresentation R).ι :=
    ⟨fun _ => PreservesFiniteCoproducts.of_preserves_binary_and_initial _ _⟩
  have h₂ : HasFiniteColimits (SheafOfModules.isFinitePresentation R).FullSubcategory :=
    hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts
  have h₃ : PreservesFiniteColimits (SheafOfModules.isFinitePresentation R).ι :=
    preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts _
  exact ⟨fun _ _ _ => (SheafOfModules.isFinitePresentation R)
    |>.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι _⟩

end Space

section Scheme

/-- [Stacks, Tag 01PJ], proposition (1), on a scheme: the property of being a finitely presented
`𝒪_X`-module is closed under finite colimits. -/
instance isClosedUnderFiniteColimits_scheme (X : AlgebraicGeometry.Scheme.{u}) :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderFiniteColimits :=
  isClosedUnderFiniteColimits_isFinitePresentation

/-- The canonical diagram of [Stacks, Tag 01PJ] is filtered: the category
`Stacks.Tag01PKDirectedColimit.FinitePresentationOver F` of finitely presented `𝒪_X`-modules
equipped with a morphism to `F` is filtered, for every `𝒪_X`-module `F`. -/
instance isFiltered_finitePresentationOver_scheme {X : AlgebraicGeometry.Scheme.{u}}
    (F : SheafOfModules.{u} X.ringCatSheaf) :
    IsFiltered.{u, u + 1} (Stacks.Tag01PKDirectedColimit.FinitePresentationOver F) :=
  Stacks.Tag01PKDirectedColimit.isFiltered_finitePresentationOver F

/-- The conclusion of [Stacks, Tag 01PK] from essential smallness and density: if the finitely
presented `𝒪_X`-modules are essentially `u`-small and dense at `F`, then `F` is the colimit of a
directed system of finitely presented `𝒪_X`-modules. -/
theorem exists_directed_system_of_essentiallySmall_of_isDenseAt {X : AlgebraicGeometry.Scheme.{u}}
    (F : SheafOfModules.{u} X.ringCatSheaf)
    [ObjectProperty.EssentiallySmall.{u} (SheafOfModules.isFinitePresentation X.ringCatSheaf)]
    (h : (SheafOfModules.isFinitePresentation X.ringCatSheaf).ι.isDenseAt F) :
    ∃ (I : Type u) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ X.Modules) (φ : D ⟶ (Functor.const I).obj F)
      (_ : IsColimit (Cocone.mk F φ)), ∀ i, (D.obj i).IsFinitePresentation :=
  Stacks.Tag01PKDirectedColimit.exists_directed_system_of_essentiallySmall_of_isDenseAt F h

end Scheme

end Stacks.Tag01PJFiniteColimits

end
