module

public import StacksFrontier.Algebra.Homology.TriangleOfSESHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.Interface
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.ConnectingMorphism.MappingConePlusDelta

/-!
# The `derivedδ_eq` field of the Čech-to-derived comparison of Stacks 01EN

`Stacks.Cohomology.CechComparison.CechDerivedComparison` has a field `derivedδ_eq`, which
identifies the connecting morphism of
`Stacks.Cohomology.CechComparison.derivedDeltaFunctor` — the one attached to a distinguished
triangle of `D⁺` — with
`Stacks.Cohomology.CechComparison.rightDerivedConnecting`, the one computed degreewise on a
short exact sequence of injective resolutions.  This file proves that field, as
`Stacks.Cohomology.CechComparison.derivedδ_eq`.

The proof has two halves, and both are here.  First the field is reduced, by the chain
`derivedδ_eq_of_rightDerivedPlusδ_eq`, `derivedδ_eq_of_resolution_rightDerivedPlusδ_eq`,
`rightDerivedPlusδ_eq_mappedShortExactδ`, `derivedδ_eq_of_resolutionTriangleδ`,
`rightDerivedPlusδ_eq_of_comm₃` and `derivedδ_eq_of_comm₃`, to **one commuting square** of the
full derived category `D(ℬ)`: the third square of a morphism of triangles from the image under
`RF` of the triangle of `S[0]` to `DerivedCategory.triangleOfSES` of the degreewise image under
`F` of the extended sequence of resolutions.  Then that square is proved, abstractly as
`Stacks.Cohomology.HigherDirectImagePresheaf.comm₃_resolutionDerivedComparison` and concretely
as `Stacks.Cohomology.CechComparison.comm₃_cech`.

## Main results

* `derivedδ_eq_of_rightDerivedPlusδ_eq`: the field follows from the equality

  `(derivedPlusToStandard F n).inv.app S.X₃ ≫ rightDerivedPlusδ F hS n ≫`
  `(derivedPlusToStandard F (n + 1)).hom.app S.X₁ = rightDerivedConnecting O 𝒰 J n`

  for `F = cechCohomologyZeroFunctor O 𝒰`.  The two `eqToHom`s of the field cost nothing:
  `derivedDeltaFunctor_functor` holds by `rfl`, so each of them is the identity, and
  `CategoryTheory.DeltaFunctor.ofIso_δ` is also `rfl`, so the connecting morphism of
  `derivedDeltaFunctor` *is* the conjugate of `Stacks.Cohomology.CechDelta.rightDerivedPlusδ`
  by `Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard`.
* `derivedδ_eq_of_resolution_rightDerivedPlusδ_eq`: the same, with the comparison of the two
  conventions for `Rⁿ F` read through the resolutions carried by `J` itself rather than through
  the resolution chosen by `CategoryTheory.injectiveResolution`.  This is the form in which the
  remaining obligation should be attacked, because
  `Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandardObjOfResolution` contains
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj` as its last factor, and
  `rightDerivedConnecting` contains the same isomorphism at the same two resolutions: the two
  occurrences cancel, rather than having to be transported past each other.
* `rightDerivedPlusδ_eq_mappedShortExactδ` and `derivedδ_eq_of_resolutionTriangleδ`: the field,
  granted the third piece described below.
* `rightDerivedPlusδ_eq_of_comm₃` and `derivedδ_eq_of_comm₃`: the field, granted the *one
  commuting square* of `D(ℬ)` that the third piece reduces to.
* `Stacks.Cohomology.HigherDirectImagePresheaf.comm₃_resolutionDerivedComparison`: that square,
  proved, for an arbitrary additive functor between abelian categories with enough injectives
  in the source.
* `Stacks.Cohomology.CechComparison.comm₃_cech`: the square at degree-zero Čech cohomology, in
  the form `derivedδ_eq_of_comm₃` asks for, and
  `Stacks.Cohomology.CechComparison.derivedδ_eq`: the field itself, unconditionally.

## How the square is proved

The square is the third square of a morphism of triangles and nothing more: no morphism of
triangles and no isomorphism of triangles has to be built, because
`CategoryTheory.Functor.homologySequenceδ` is `CategoryTheory.Functor.shiftMap` of `mor₃`.  The
whole calculation is run on `CategoryTheory.Functor.mapδ` — the third morphism of the image of a
triangle under a functor commuting with the shift — whose calculus lives in
`StacksFrontier.Algebra.Homology.TriangleOfSESHomology`.

It is proved by composing two squares.

*(a)* In `D(𝒜)`, the naturality of `DerivedCategory.triangleOfSESδ` along the morphism
`augmentationShortComplexHom` of short exact sequences of cochain complexes `S[0] ⟶ extend J`,
whose components are `resolutionSingleHom` (natural by `resolutionSingleHom_naturality`) and
whose two squares are `J.comm_f` and `J.comm_g` read in degree zero
(`single₀_comm_of_degree_zero`).  Since
`CategoryTheory.ShortComplex.ShortExact.singleδ` is by definition `triangleOfSESδ` of `S[0]`,
and since `resolutionDerivedIso` is induced by `resolutionSingleHom`
(`Q_map_resolutionSingleHom`), this identifies `Stacks.Cohomology.CechDelta.singlePlusδ` with
the connecting morphism `resolutionPlusδ` of the extended sequence of resolutions in `D⁺(𝒜)`.
That is `singlePlusδ_eq`; it is checked in `D(𝒜)` and pulled back through the faithful inclusion
of `D⁺(𝒜)` by `CategoryTheory.Functor.mapδ_cancel`.

*(b)* is proved in `ConnectingMorphism.MappingConePlusDelta`.

The two squares are assembled in `comm₃_resolutionDerivedComparison`, cancelling the unit and
the image of `descKPlus`, and `comm₃_cech` instantiates it at degree-zero Čech cohomology.

The first two pieces, and `extendedHomologyIso_conj_mapExtendTriangleδ`, are proved in
`ConnectingMorphism.ExtendedHomologyDelta`.

## References

* [Stacks Project, Tag 01EN](https://stacks.math.columbia.edu/tag/01EN)
* [Stacks Project, Tag 01E4](https://stacks.math.columbia.edu/tag/01E4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.HigherDirectImagePresheaf

universe u

namespace Stacks.Cohomology.HigherDirectImagePresheaf

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- **The morphism of short exact sequences of cochain complexes from `S` placed in degree zero
to the extension of a compatible sequence of injective resolutions.**  Its components are
`resolutionSingleHom` and its two squares are the two commuting augmentation squares. -/
noncomputable def augmentationShortComplexHom {S : ShortComplex A}
    (I₁ : InjectiveResolution S.X₁) (I₂ : InjectiveResolution S.X₂)
    (I₃ : InjectiveResolution S.X₃)
    (f : I₁.cocomplex ⟶ I₂.cocomplex) (g : I₂.cocomplex ⟶ I₃.cocomplex) (zero : f ≫ g = 0)
    (comm_f : I₁.ι.f 0 ≫ f.f 0 = S.f ≫ I₂.ι.f 0)
    (comm_g : I₂.ι.f 0 ≫ g.f 0 = S.g ≫ I₃.ι.f 0) :
    S.map (HomologicalComplex.single A (up ℤ) 0) ⟶
      extendShortComplex (ShortComplex.mk f g zero) where
  τ₁ := resolutionSingleHom I₁
  τ₂ := resolutionSingleHom I₂
  τ₃ := resolutionSingleHom I₃
  comm₁₂ := (resolutionSingleHom_naturality I₁ I₂ S.f f
    (single₀_comm_of_degree_zero I₁ I₂ S.f f comm_f)).symm
  comm₂₃ := (resolutionSingleHom_naturality I₂ I₃ S.g g
    (single₀_comm_of_degree_zero I₂ I₃ S.g g comm_g)).symm

end Stacks.Cohomology.HigherDirectImagePresheaf

namespace Stacks.Cohomology.HigherDirectImagePresheaf

section Standard

attribute [local instance] HasDerivedCategory.standard

variable {A : Type*} [Category* A] [Abelian A]

/-- **The `D⁺(𝒜)` square.**  The connecting morphism `Stacks.Cohomology.CechDelta.singlePlusδ`
of the triangle of `S` placed in degree zero is, transported along the comparisons
`resolutionDerivedIso` of `S.X₃` and `S.X₁` with the extensions of their resolutions, the
connecting morphism `resolutionPlusδ` of the extended sequence of resolutions.

By faithfulness of `DerivedCategory.Plus.ι` the square may be checked in the full derived
category, where `Stacks.Cohomology.CechDelta.ι_map_singlePlusδ` turns the left-hand side into
`CategoryTheory.ShortComplex.ShortExact.singleδ` — that is, into
`DerivedCategory.triangleOfSESδ` of `S` placed in degree zero — and
`DerivedCategory.triangleOfSESδ_naturality` along `augmentationShortComplexHom` is exactly the
required identity. -/
theorem singlePlusδ_eq {S : ShortComplex A} (hS : S.ShortExact)
    (I₁ : InjectiveResolution S.X₁) (I₂ : InjectiveResolution S.X₂)
    (I₃ : InjectiveResolution S.X₃)
    (f : I₁.cocomplex ⟶ I₂.cocomplex) (g : I₂.cocomplex ⟶ I₃.cocomplex) (zero : f ≫ g = 0)
    (comm_f : I₁.ι.f 0 ≫ f.f 0 = S.f ≫ I₂.ι.f 0)
    (comm_g : I₂.ι.f 0 ≫ g.f 0 = S.g ≫ I₃.ι.f 0)
    (hR : (extendShortComplex (ShortComplex.mk f g zero)).ShortExact) :
    CechDelta.singlePlusδ hS ≫ ((resolutionDerivedIso I₁).hom)⟦(1 : ℤ)⟧' =
      (resolutionDerivedIso I₃).hom ≫
        resolutionPlusδ (ShortComplex.mk f g zero) hR := by
  refine Functor.mapδ_cancel DerivedCategory.Plus.ι _ _ _ _ ?_
  have hnat := DerivedCategory.triangleOfSESδ_naturality
    (hS.map_of_exact (HomologicalComplex.single A (up ℤ) 0)) hR
    (augmentationShortComplexHom I₁ I₂ I₃ f g zero comm_f comm_g)
  have hsingle : Functor.mapδ DerivedCategory.Plus.ι (CechDelta.singlePlusδ hS) =
      DerivedCategory.triangleOfSESδ
        (hS.map_of_exact (HomologicalComplex.single A (up ℤ) 0)) :=
    CechDelta.ι_map_singlePlusδ hS
  have hq₁ := Q_map_resolutionSingleHom I₁
  have hq₃ := Q_map_resolutionSingleHom I₃
  have hf := mapδ_ι_resolutionPlusδ (ShortComplex.mk f g zero) hR
  refine (cancel_mono (((DerivedCategory.quotientCompQhIso A).hom.app
    (I₁.cocomplex.extend ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧')).1 ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (CategoryTheory.Functor.map_comp
    (CategoryTheory.shiftFunctor (DerivedCategory A) (1 : ℤ)) _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (congrArg
    (fun u => (CategoryTheory.shiftFunctor (DerivedCategory A) (1 : ℤ)).map u) hq₁)) ?_
  refine Eq.trans (eq_whisker hsingle _) ?_
  refine Eq.trans hnat ?_
  refine Eq.trans (eq_whisker hq₃.symm _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ hf.symm) ?_
  exact (Category.assoc _ _ _).symm

end Standard

end Stacks.Cohomology.HigherDirectImagePresheaf

namespace Stacks.Cohomology.HigherDirectImagePresheaf

section Standard

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [EnoughInjectives A] (F : A ⥤ B) [F.Additive]

/-- The two factors of `derivedPlusResolutionIso`. -/
theorem derivedPlusResolutionIso_hom {M : A} (I : InjectiveResolution M) :
    (derivedPlusResolutionIso F I).hom =
      F.rightDerivedFunctorPlus.map (resolutionDerivedIso I).hom ≫
        inv (F.rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient A).obj (resolutionCochainPlus I))) := rfl

/-- **The one commuting square of `derivedδ_eq`, abstractly.**  For an additive functor `F`
between abelian categories with enough injectives in the source, a short exact sequence `S` and
a compatible short exact sequence of injective resolutions whose degreewise `F`-image is short
exact, the connecting morphism of the image under `RF` of the triangle of `S[0]` becomes, after
transport along `resolutionDerivedComparison`, the connecting morphism
`DerivedCategory.triangleOfSESδ` of the degreewise `F`-image of the extended sequence of
resolutions. -/
theorem comm₃_resolutionDerivedComparison {S : ShortComplex A} (hS : S.ShortExact)
    (I₁ : InjectiveResolution S.X₁) (I₂ : InjectiveResolution S.X₂)
    (I₃ : InjectiveResolution S.X₃)
    (f : I₁.cocomplex ⟶ I₂.cocomplex) (g : I₂.cocomplex ⟶ I₃.cocomplex) (zero : f ≫ g = 0)
    (comm_f : I₁.ι.f 0 ≫ f.f 0 = S.f ≫ I₂.ι.f 0)
    (comm_g : I₂.ι.f 0 ≫ g.f 0 = S.g ≫ I₃.ι.f 0)
    (hR : (ShortComplex.mk f g zero).ShortExact)
    (hFR : (((ShortComplex.mk f g zero)).map
      (F.mapHomologicalComplex (up ℕ))).ShortExact) :
    (resolutionDerivedComparison F I₃).hom ≫
        mapExtendSESδ F (R := ShortComplex.mk f g zero) hFR =
      Functor.mapδ (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
          (CechDelta.singlePlusδ hS) ≫
        ((resolutionDerivedComparison F I₁).hom)⟦(1 : ℤ)⟧' := by
  set R : ShortComplex (CochainComplex A ℕ) := ShortComplex.mk f g zero with hRdef
  have hRext : (extendShortComplex R).ShortExact :=
    ComplexShape.embeddingUpNat.shortExact_map_extendFunctor hR
  have hFRext : ((extendShortComplex R).map (F.mapHomologicalComplex (up ℤ))).ShortExact :=
    shortExact_mapExtend F hFR
  -- the degreewise `F`-image of `descShortComplex` is a quasi-isomorphism
  have hdesc : QuasiIso ((F.mapHomologicalComplex (up ℤ)).map
      (CochainComplex.mappingCone.descShortComplex (extendShortComplex R))) := by
    rw [← CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex F
      (extendShortComplex R)]
    have := CochainComplex.mappingCone.quasiIso_descShortComplex hFRext
    infer_instance
  have hw : IsIso (DerivedCategory.Plus.Qh.map
      (F.mapHomotopyCategoryPlus.map (descKPlus R))) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso B) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hdesc)
  have h1 := descKPlus_comp_triangleOfSESδ F R hFRext
  have h2 := descKPlus_comp_unit_comp_mapδ F R hRext
  have hwι : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
    (F.mapHomotopyCategoryPlus.map (descKPlus R)))) := inferInstance
  have hε₃ι : IsIso (DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app
    ((HomotopyCategory.Plus.quotient A).obj (resolutionCochainPlus I₃)))) := inferInstance
  have hε₁ι : IsIso (DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app
    ((HomotopyCategory.Plus.quotient A).obj (resolutionCochainPlus I₁)))) := inferInstance
  have hG : @inv _ _ _ _ (DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient A).obj (resolutionCochainPlus I₃)))) hε₃ι ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((F.mapHomologicalComplex (up ℤ)).obj (extendShortComplex R).X₃) ≫
        DerivedCategory.triangleOfSESδ hFRext =
      Functor.mapδ (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
          (resolutionPlusδ R hRext) ≫
        (@inv _ _ _ _ (DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app
              ((HomotopyCategory.Plus.quotient A).obj (resolutionCochainPlus I₁)))) hε₁ι ≫
          (DerivedCategory.quotientCompQhIso B).hom.app
            ((F.mapHomologicalComplex (up ℤ)).obj (extendShortComplex R).X₁))⟦(1 : ℤ)⟧' := by
    refine (IsIso.inv_comp_eq _).2 ?_
    refine (cancel_epi (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
      (F.mapHomotopyCategoryPlus.map (descKPlus R))))).1 ?_
    refine Eq.trans h1 ?_
    have hz : (DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient A).obj (resolutionCochainPlus I₁))))⟦(1 : ℤ)⟧' ≫
          (@inv _ _ _ _ (DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app
                ((HomotopyCategory.Plus.quotient A).obj (resolutionCochainPlus I₁)))) hε₁ι ≫
            (DerivedCategory.quotientCompQhIso B).hom.app
              ((F.mapHomologicalComplex (up ℤ)).obj (extendShortComplex R).X₁))⟦(1 : ℤ)⟧' =
        ((DerivedCategory.quotientCompQhIso B).hom.app
          ((F.mapHomologicalComplex (up ℤ)).obj (extendShortComplex R).X₁))⟦(1 : ℤ)⟧' := by
      refine Eq.trans (CategoryTheory.Functor.map_comp _ _ _).symm ?_
      exact congrArg
        (fun u => (CategoryTheory.shiftFunctor (DerivedCategory B) (1 : ℤ)).map u)
        (IsIso.hom_inv_id_assoc _ _)
    refine Eq.trans (whisker_eq _ hz.symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker h2.symm _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact whisker_eq _ (Category.assoc _ _ _)
  have hsq1 := singlePlusδ_eq hS I₁ I₂ I₃ f g zero comm_f comm_g hRext
  have hnat := Functor.mapδ_naturality
    (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
    (CechDelta.singlePlusδ hS) (resolutionPlusδ R hRext)
    (resolutionDerivedIso I₃).hom (resolutionDerivedIso I₁).hom hsq1
  rw [resolutionDerivedComparison_hom, resolutionDerivedComparison_hom,
    derivedPlusResolutionIso_hom, derivedPlusResolutionIso_hom,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_inv, CategoryTheory.Functor.map_inv]
  refine Eq.trans (eq_whisker (Category.assoc _ _ _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ hG) ?_
  refine Eq.trans ?_ (whisker_eq _ (congrArg
    (fun u => (CategoryTheory.shiftFunctor (DerivedCategory B) (1 : ℤ)).map u)
    (Category.assoc _ _ _).symm))
  refine Eq.trans ?_ (whisker_eq _ (CategoryTheory.Functor.map_comp
    (CategoryTheory.shiftFunctor (DerivedCategory B) (1 : ℤ)) _ _)).symm
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (eq_whisker hnat _).symm
  exact (Category.assoc _ _ _).symm

end Standard

end Stacks.Cohomology.HigherDirectImagePresheaf

namespace Stacks.Cohomology.HigherDirectImagePresheaf

section Standard2

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit
  CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [EnoughInjectives A] (F : A ⥤ B) [F.Additive]

/-- The connecting morphism of `Stacks.Cohomology.CechDelta.derivedDeltaFunctorStructure`, read
in the full derived category of `ℬ`, is `CategoryTheory.Functor.mapδ` of
`Stacks.Cohomology.CechDelta.singlePlusδ` along `RF` followed by the inclusion of `D⁺(ℬ)`. -/
theorem mapδ_rightDerivedFunctorPlus_comp_ι_singlePlusδ
    {S : ShortComplex A} (hS : S.ShortExact) :
    Functor.mapδ (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
        (CechDelta.singlePlusδ hS) =
      DerivedCategory.Plus.ι.map ((CechDelta.derivedDeltaFunctorStructure F).δ hS) ≫
        (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
          (F.rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor A 0).obj S.X₁)) := by
  have hδ : (CechDelta.derivedDeltaFunctorStructure F).δ hS =
      F.rightDerivedFunctorPlus.map (CechDelta.singlePlusδ hS) ≫
        (F.rightDerivedFunctorPlus.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.Plus.singleFunctor A 0).obj S.X₁) := rfl
  dsimp only [Functor.mapδ]
  rw [hδ, CategoryTheory.Functor.map_comp,
    Functor.commShiftIso_comp_hom_app F.rightDerivedFunctorPlus DerivedCategory.Plus.ι,
    Category.assoc]
  rfl

end Standard2

end Stacks.Cohomology.HigherDirectImagePresheaf

namespace Stacks.Cohomology.CechComparison

attribute [local instance] HasDerivedCategory.standard
-- The same instances the connecting morphism of `rightDerivedPlusδ` is built from: a second copy
-- would be definitionally equal but not syntactically so, and the commutation of `RF` with the
-- shift appears explicitly in that morphism.
attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit
  CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (𝒰 : CechExactFunctor.CechOpenCover.{u, u} (TopCat.of X))

/-- **The `derivedδ_eq` field of `CechDerivedComparison`, with its transport discharged.**  The
field conjugates the connecting morphism of `derivedDeltaFunctor` by the `eqToHom`s of
`derivedDeltaFunctor_functor`; since that equality of functors holds by `rfl` both `eqToHom`s
are identities, and since `CategoryTheory.DeltaFunctor.ofIso_δ` also holds by `rfl` the
connecting morphism is on the nose the conjugate of
`Stacks.Cohomology.CechDelta.rightDerivedPlusδ` by
`Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard`.  So the field reduces to
the displayed equality of morphisms, with no transport left in it. -/
theorem derivedδ_eq_of_rightDerivedPlusδ_eq {S : ShortComplex (Modules.{u} O)}
    (hS : S.ShortExact) (J : ResolutionShortComplex.{u} O 𝒰 S) (n : ℕ)
    (h : (derivedPlusToStandard (cechCohomologyZeroFunctor.{u} O 𝒰) n).inv.app S.X₃ ≫
          CechDelta.rightDerivedPlusδ (cechCohomologyZeroFunctor.{u} O 𝒰) hS n ≫
          (derivedPlusToStandard (cechCohomologyZeroFunctor.{u} O 𝒰) (n + 1)).hom.app S.X₁ =
        rightDerivedConnecting.{u} O 𝒰 J n) :
    (eqToHom (derivedDeltaFunctor_functor.{u} O 𝒰 n).symm).app S.X₃ ≫
        (derivedDeltaFunctor.{u} O 𝒰).δ hS n ≫
        (eqToHom (derivedDeltaFunctor_functor.{u} O 𝒰 (n + 1))).app S.X₁ =
      rightDerivedConnecting.{u} O 𝒰 J n :=
  (Category.id_comp _).trans ((Category.comp_id _).trans h)

/-- **The `derivedδ_eq` field of `CechDerivedComparison`, read through the resolutions of `J`.**
The comparison of the derived-category and injective-resolution conventions for `Rⁿ F` does not
depend on which injective resolution computes it
(`Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard_app_eq`), so the field may
be stated through the resolutions `J.J₃` and `J.J₁` carried by the sequence of resolutions
itself.  That is the form to work in: by
`Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandardObjOfResolution_eq_trans`
each side then carries `J.J₃.isoRightDerivedObj` and `J.J₁.isoRightDerivedObj` as outer
factors, exactly as `rightDerivedConnecting` does, so those isomorphisms cancel instead of
having to be moved across the junction between `(homologyFunctor _ _ n).obj K` and
`K.homology n`. -/
theorem derivedδ_eq_of_resolution_rightDerivedPlusδ_eq {S : ShortComplex (Modules.{u} O)}
    (hS : S.ShortExact) (J : ResolutionShortComplex.{u} O 𝒰 S) (n : ℕ)
    (h : (derivedPlusToStandardObjOfResolution
            (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₃ n).inv ≫
          CechDelta.rightDerivedPlusδ (cechCohomologyZeroFunctor.{u} O 𝒰) hS n ≫
          (derivedPlusToStandardObjOfResolution
            (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₁ (n + 1)).hom =
        rightDerivedConnecting.{u} O 𝒰 J n) :
    (eqToHom (derivedDeltaFunctor_functor.{u} O 𝒰 n).symm).app S.X₃ ≫
        (derivedDeltaFunctor.{u} O 𝒰).δ hS n ≫
        (eqToHom (derivedDeltaFunctor_functor.{u} O 𝒰 (n + 1))).app S.X₁ =
      rightDerivedConnecting.{u} O 𝒰 J n := by
  refine derivedδ_eq_of_rightDerivedPlusδ_eq O 𝒰 hS J n ?_
  rw [← Iso.app_inv, ← Iso.app_hom,
    derivedPlusToStandard_app_eq _ J.J₃, derivedPlusToStandard_app_eq _ J.J₁]
  exact h

/-- **The connecting morphism of the derived-category triangle attached to the sequence of
resolutions carried by `J`.**  Take the sequence `J.J₁.cocomplex ⟶ J.J₂.cocomplex ⟶
J.J₃.cocomplex` of injective resolutions, extend it by zero to a sequence of `ℤ`-indexed
complexes, apply degree-zero Čech cohomology in each degree — this is still short exact, which
is `J.mappedShortExact` — and take the connecting morphism in cohomology of
`DerivedCategory.triangleOfSES` of the result, read in the `Qh ∘ quotient` spelling that
`Stacks.Cohomology.HigherDirectImagePresheaf.extendedHomologyIso` presents.

This is the target of the one remaining obligation,
`rightDerivedPlusδ_eq_mappedShortExactδ`. -/
def resolutionTriangleδ {S : ShortComplex (Modules.{u} O)}
    (J : ResolutionShortComplex.{u} O 𝒰 S) (n : ℕ) :
    (DerivedCategory.homologyFunctor (SectionModules.{u} O 𝒰) (n : ℤ)).obj
        (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (SectionModules.{u} O 𝒰) (up ℤ)).obj
            (((cechCohomologyZeroFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).obj
              (J.J₃.cocomplex.extend ComplexShape.embeddingUpNat)))) ⟶
      (DerivedCategory.homologyFunctor (SectionModules.{u} O 𝒰) ((n + 1 : ℕ) : ℤ)).obj
        (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (SectionModules.{u} O 𝒰) (up ℤ)).obj
            (((cechCohomologyZeroFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).obj
              (J.J₁.cocomplex.extend ComplexShape.embeddingUpNat)))) :=
  (DerivedCategory.homologyFunctor (SectionModules.{u} O 𝒰) (n : ℤ)).map
      ((DerivedCategory.quotientCompQhIso (SectionModules.{u} O 𝒰)).hom.app _) ≫
    mapExtendTriangleδ (cechCohomologyZeroFunctor.{u} O 𝒰) J.mappedShortExact n ≫
    (DerivedCategory.homologyFunctor (SectionModules.{u} O 𝒰) ((n + 1 : ℕ) : ℤ)).map
      ((DerivedCategory.quotientCompQhIso (SectionModules.{u} O 𝒰)).inv.app _)

/-- **The remaining content of `derivedδ_eq`, with pieces 1 and 2 discharged.**  Granted the
single hypothesis that `Stacks.Cohomology.CechDelta.rightDerivedPlusδ`, conjugated by
`Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusResolutionHomologyIso`, is
`resolutionTriangleδ` — that is, granted that the connecting morphism of the total right derived
functor on `D⁺` is the connecting morphism of the derived-category triangle of the degreewise
image of the resolutions — the displayed equality of `derivedδ_eq` follows, by
`Stacks.Cohomology.HigherDirectImagePresheaf.extendedHomologyIso_conj_mapExtendTriangleδ`.

The hypothesis is the whole of the third piece described in the module docstring; everything
else in the field is now proved. -/
theorem rightDerivedPlusδ_eq_mappedShortExactδ {S : ShortComplex (Modules.{u} O)}
    (hS : S.ShortExact) (J : ResolutionShortComplex.{u} O 𝒰 S) (n : ℕ)
    (h : (derivedPlusResolutionHomologyIso
            (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₃ n).inv ≫
          CechDelta.rightDerivedPlusδ (cechCohomologyZeroFunctor.{u} O 𝒰) hS n ≫
          (derivedPlusResolutionHomologyIso
            (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₁ (n + 1)).hom =
        resolutionTriangleδ.{u} O 𝒰 J n) :
    (extendedHomologyIso (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₃.cocomplex n).inv ≫
        (derivedPlusResolutionHomologyIso (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₃ n).inv ≫
        CechDelta.rightDerivedPlusδ (cechCohomologyZeroFunctor.{u} O 𝒰) hS n ≫
        (derivedPlusResolutionHomologyIso
          (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₁ (n + 1)).hom ≫
        (extendedHomologyIso (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₁.cocomplex (n + 1)).hom =
      J.mappedShortExact.δ n (n + 1) rfl := by
  have hα := extendedHomologyIso_conj_mapExtendTriangleδ
    (cechCohomologyZeroFunctor.{u} O 𝒰) J.mappedShortExact n
  dsimp only at hα
  refine Eq.trans ?_ hα
  rw [resolutionTriangleδ] at h
  rw [← h]
  exact (whisker_eq _
    ((Category.assoc _ _ _).trans (whisker_eq _ (Category.assoc _ _ _)))).symm

/-- **The `derivedδ_eq` field of `CechDerivedComparison`, reduced to a single obligation.**
Granted that `Stacks.Cohomology.CechDelta.rightDerivedPlusδ`, conjugated by
`Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusResolutionHomologyIso`, is
`resolutionTriangleδ`, the field holds.

The two occurrences of `CategoryTheory.InjectiveResolution.isoRightDerivedObj` — the outer
factors of
`Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandardObjOfResolution` and the
outer factors of `rightDerivedConnecting` — cancel, so what is left is exactly
`rightDerivedPlusδ_eq_mappedShortExactδ`.  The reassociation that performs the cancellation
crosses the junction between the two presentations of the cohomology of `F(I)` — as
`K.homology n` and as `(F.mapHomologicalComplex _ ⋙ homologyFunctor _ _ n).obj K` — across
which neither `rw` nor `simp` fires on `CategoryTheory.Category.assoc`, so it is built as a
chain of explicit `Category.assoc` terms. -/
theorem derivedδ_eq_of_resolutionTriangleδ {S : ShortComplex (Modules.{u} O)}
    (hS : S.ShortExact) (J : ResolutionShortComplex.{u} O 𝒰 S) (n : ℕ)
    (h : (derivedPlusResolutionHomologyIso
            (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₃ n).inv ≫
          CechDelta.rightDerivedPlusδ (cechCohomologyZeroFunctor.{u} O 𝒰) hS n ≫
          (derivedPlusResolutionHomologyIso
            (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₁ (n + 1)).hom =
        resolutionTriangleδ.{u} O 𝒰 J n) :
    (eqToHom (derivedDeltaFunctor_functor.{u} O 𝒰 n).symm).app S.X₃ ≫
        (derivedDeltaFunctor.{u} O 𝒰).δ hS n ≫
        (eqToHom (derivedDeltaFunctor_functor.{u} O 𝒰 (n + 1))).app S.X₁ =
      rightDerivedConnecting.{u} O 𝒰 J n := by
  refine derivedδ_eq_of_resolution_rightDerivedPlusδ_eq O 𝒰 hS J n ?_
  have hβ := rightDerivedPlusδ_eq_mappedShortExactδ O 𝒰 hS J n h
  rw [derivedPlusToStandardObjOfResolution_eq_trans,
    derivedPlusToStandardObjOfResolution_eq_trans, rightDerivedConnecting]
  have u₃ : (derivedPlusResolutionHomologyIso (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₃ n ≪≫
        extendedHomologyIso (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₃.cocomplex n ≪≫
        (J.J₃.isoRightDerivedObj (cechCohomologyZeroFunctor.{u} O 𝒰) n).symm).inv =
      ((J.J₃.isoRightDerivedObj (cechCohomologyZeroFunctor.{u} O 𝒰) n).hom ≫
          (extendedHomologyIso (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₃.cocomplex n).inv) ≫
        (derivedPlusResolutionHomologyIso
          (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₃ n).inv := rfl
  have v₁ : (derivedPlusResolutionHomologyIso (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₁ (n + 1) ≪≫
        extendedHomologyIso (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₁.cocomplex (n + 1) ≪≫
        (J.J₁.isoRightDerivedObj (cechCohomologyZeroFunctor.{u} O 𝒰) (n + 1)).symm).hom =
      (derivedPlusResolutionHomologyIso (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₁ (n + 1)).hom ≫
        ((extendedHomologyIso (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₁.cocomplex (n + 1)).hom ≫
          (J.J₁.isoRightDerivedObj
            (cechCohomologyZeroFunctor.{u} O 𝒰) (n + 1)).inv) := rfl
  rw [u₃, v₁]
  refine (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (whisker_eq _ ?_))
  exact ((Category.assoc _ _ _).trans (whisker_eq _ ((Category.assoc _ _ _).trans
    (whisker_eq _ ((Category.assoc _ _ _).trans
      (whisker_eq _ (Category.assoc _ _ _))))))).symm.trans (hβ =≫ _)

/-- **The one remaining obligation of `derivedδ_eq`, as a single commuting square.**  The
hypothesis is the third square of the morphism of triangles of `D(ℬ)` from the image under
`DerivedCategory.Plus.ι` of the triangle of `Stacks.Cohomology.CechDelta.rightDerivedPlusδ` — the
image under `RF` of the triangle of `S[0]` in `D⁺(𝒜)` — to
`DerivedCategory.triangleOfSES` of the degreewise image under `Ȟ⁰(𝒰, -)` of the extended
sequence of resolutions, along `resolutionDerivedComparison`.

Granted it, the hypothesis of `rightDerivedPlusδ_eq_mappedShortExactδ` holds, so with
`derivedδ_eq_of_resolutionTriangleδ` the field `derivedδ_eq` follows
(`derivedδ_eq_of_comm₃`).

No morphism of triangles and no isomorphism of triangles is needed, only this one square:
`CategoryTheory.Functor.homologySequenceδ` of a triangle is `CategoryTheory.Functor.shiftMap` of
its third morphism, `DerivedCategory.Plus.homologyFunctor` is by definition
`DerivedCategory.Plus.ι ⋙ DerivedCategory.homologyFunctor` — so
`CategoryTheory.Functor.comp_shiftMap` reads the `D⁺(ℬ)` connecting morphism off `D(ℬ)` — and
`CategoryTheory.Functor.shiftMap_comp` and `….shiftMap_comp'` absorb the two comparison
isomorphisms into the argument of `shiftMap`.  Everything else in the proof is the cancellation
of `DerivedCategory.quotientCompQhIso`, done in term mode because the two presentations of the
image of a resolution in `D(ℬ)` are definitionally but not syntactically equal. -/
theorem rightDerivedPlusδ_eq_of_comm₃ {S : ShortComplex (Modules.{u} O)}
    (hS : S.ShortExact) (J : ResolutionShortComplex.{u} O 𝒰 S) (n : ℕ)
    (hsq : (resolutionDerivedComparison (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₃).hom ≫
        mapExtendSESδ (cechCohomologyZeroFunctor.{u} O 𝒰)
          (R := ShortComplex.mk J.f J.g J.zero) J.mappedShortExact =
      (DerivedCategory.Plus.ι.map
            ((CechDelta.derivedDeltaFunctorStructure (cechCohomologyZeroFunctor.{u} O 𝒰)).δ hS) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
            ((cechCohomologyZeroFunctor.{u} O 𝒰).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor (Modules.{u} O) 0).obj S.X₁))) ≫
        ((resolutionDerivedComparison (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₁).hom)⟦(1 : ℤ)⟧') :
    (derivedPlusResolutionHomologyIso (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₃ n).inv ≫
        CechDelta.rightDerivedPlusδ (cechCohomologyZeroFunctor.{u} O 𝒰) hS n ≫
        (derivedPlusResolutionHomologyIso (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₁ (n + 1)).hom =
      resolutionTriangleδ.{u} O 𝒰 J n := by
  have hA : CechDelta.rightDerivedPlusδ (cechCohomologyZeroFunctor.{u} O 𝒰) hS n =
      (DerivedCategory.homologyFunctor (SectionModules.{u} O 𝒰) 0).shiftMap
        (DerivedCategory.Plus.ι.map
            ((CechDelta.derivedDeltaFunctorStructure (cechCohomologyZeroFunctor.{u} O 𝒰)).δ hS) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
            ((cechCohomologyZeroFunctor.{u} O 𝒰).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor (Modules.{u} O) 0).obj S.X₁)))
        (n : ℤ) ((n + 1 : ℕ) : ℤ) (by push_cast; ring) :=
    Functor.comp_shiftMap DerivedCategory.Plus.ι _ _ _ _ _
  have key : (resolutionDerivedComparison (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₃).inv ≫
      (DerivedCategory.Plus.ι.map
            ((CechDelta.derivedDeltaFunctorStructure (cechCohomologyZeroFunctor.{u} O 𝒰)).δ hS) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
            ((cechCohomologyZeroFunctor.{u} O 𝒰).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor (Modules.{u} O) 0).obj S.X₁))) ≫
        ((resolutionDerivedComparison (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₁).hom)⟦(1 : ℤ)⟧' =
      mapExtendSESδ (cechCohomologyZeroFunctor.{u} O 𝒰)
          (R := ShortComplex.mk J.f J.g J.zero) J.mappedShortExact := by
    rw [Iso.inv_comp_eq]
    exact hsq.symm
  have hkey : (DerivedCategory.homologyFunctor (SectionModules.{u} O 𝒰) (n : ℤ)).map
          (resolutionDerivedComparison (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₃).inv ≫
        (DerivedCategory.homologyFunctor (SectionModules.{u} O 𝒰) 0).shiftMap
          (DerivedCategory.Plus.ι.map
              ((CechDelta.derivedDeltaFunctorStructure (cechCohomologyZeroFunctor.{u} O 𝒰)).δ hS) ≫
            (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
              ((cechCohomologyZeroFunctor.{u} O 𝒰).rightDerivedFunctorPlus.obj
                ((DerivedCategory.Plus.singleFunctor (Modules.{u} O) 0).obj S.X₁)))
          (n : ℤ) ((n + 1 : ℕ) : ℤ) (by push_cast; ring) ≫
        (DerivedCategory.homologyFunctor (SectionModules.{u} O 𝒰) ((n + 1 : ℕ) : ℤ)).map
          (resolutionDerivedComparison (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₁).hom =
      mapExtendTriangleδ (cechCohomologyZeroFunctor.{u} O 𝒰) J.mappedShortExact n := by
    rw [mapExtendTriangleδ_eq, ← key]
    conv_rhs => rw [Functor.shiftMap_comp', Functor.shiftMap_comp]
    rfl
  have e₃ : ((DerivedCategory.quotientCompQhIso (SectionModules.{u} O 𝒰)).app
          (((cechCohomologyZeroFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).obj
            (J.J₃.cocomplex.extend ComplexShape.embeddingUpNat))).hom ≫
        (resolutionDerivedComparison (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₃).inv =
      DerivedCategory.Plus.ι.map
        (derivedPlusResolutionIso (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₃).inv :=
    (Category.assoc _ _ _).symm.trans
      ((eq_whisker (Iso.hom_inv_id _) _).trans (Category.id_comp _))
  have e₁ : (resolutionDerivedComparison (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₁).hom ≫
        ((DerivedCategory.quotientCompQhIso (SectionModules.{u} O 𝒰)).app
          (((cechCohomologyZeroFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).obj
            (J.J₁.cocomplex.extend ComplexShape.embeddingUpNat))).inv =
      DerivedCategory.Plus.ι.map
        (derivedPlusResolutionIso (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₁).hom :=
    (Category.assoc _ _ _).trans
      ((whisker_eq _ (Iso.hom_inv_id _)).trans (Category.comp_id _))
  have hc₃ := (CategoryTheory.Functor.map_comp
      (DerivedCategory.homologyFunctor (SectionModules.{u} O 𝒰) (n : ℤ))
      (((DerivedCategory.quotientCompQhIso (SectionModules.{u} O 𝒰)).app
        (((cechCohomologyZeroFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).obj
          (J.J₃.cocomplex.extend ComplexShape.embeddingUpNat))).hom)
      (resolutionDerivedComparison (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₃).inv).symm.trans
    (congrArg (fun f => (DerivedCategory.homologyFunctor (SectionModules.{u} O 𝒰) (n : ℤ)).map f)
      e₃)
  have hc₁ := (CategoryTheory.Functor.map_comp
      (DerivedCategory.homologyFunctor (SectionModules.{u} O 𝒰) ((n + 1 : ℕ) : ℤ))
      (resolutionDerivedComparison (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₁).hom
      (((DerivedCategory.quotientCompQhIso (SectionModules.{u} O 𝒰)).app
        (((cechCohomologyZeroFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).obj
          (J.J₁.cocomplex.extend ComplexShape.embeddingUpNat))).inv)).symm.trans
    (congrArg (fun f =>
      (DerivedCategory.homologyFunctor (SectionModules.{u} O 𝒰) ((n + 1 : ℕ) : ℤ)).map f) e₁)
  rw [hA, derivedPlusResolutionHomologyIso_inv, derivedPlusResolutionHomologyIso_hom,
    resolutionTriangleδ]
  refine Eq.symm ((whisker_eq _ (eq_whisker hkey.symm _)).trans ?_)
  refine (whisker_eq _ ((Category.assoc _ _ _).trans
    (whisker_eq _ (Category.assoc _ _ _)))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact (eq_whisker hc₃ _).trans (whisker_eq _ (whisker_eq _ hc₁))

/-- **The `derivedδ_eq` field of `CechDerivedComparison`, reduced to one commuting square of the
full derived category `D(ℬ)`.**  This is `derivedδ_eq_of_resolutionTriangleδ` with its
hypothesis replaced, through `rightDerivedPlusδ_eq_of_comm₃`, by the third square of the
morphism of triangles described there.  It is the whole of what is left of Stacks 01EN's
comparison of connecting morphisms. -/
theorem derivedδ_eq_of_comm₃ {S : ShortComplex (Modules.{u} O)}
    (hS : S.ShortExact) (J : ResolutionShortComplex.{u} O 𝒰 S) (n : ℕ)
    (hsq : (resolutionDerivedComparison (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₃).hom ≫
        mapExtendSESδ (cechCohomologyZeroFunctor.{u} O 𝒰)
          (R := ShortComplex.mk J.f J.g J.zero) J.mappedShortExact =
      (DerivedCategory.Plus.ι.map
            ((CechDelta.derivedDeltaFunctorStructure (cechCohomologyZeroFunctor.{u} O 𝒰)).δ hS) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
            ((cechCohomologyZeroFunctor.{u} O 𝒰).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor (Modules.{u} O) 0).obj S.X₁))) ≫
        ((resolutionDerivedComparison (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₁).hom)⟦(1 : ℤ)⟧') :
    (eqToHom (derivedDeltaFunctor_functor.{u} O 𝒰 n).symm).app S.X₃ ≫
        (derivedDeltaFunctor.{u} O 𝒰).δ hS n ≫
        (eqToHom (derivedDeltaFunctor_functor.{u} O 𝒰 (n + 1))).app S.X₁ =
      rightDerivedConnecting.{u} O 𝒰 J n :=
  derivedδ_eq_of_resolutionTriangleδ O 𝒰 hS J n
    (rightDerivedPlusδ_eq_of_comm₃ O 𝒰 hS J n hsq)

/-- **The one commuting square that `derivedδ_eq_of_comm₃` asks for.** -/
theorem comm₃_cech {S : ShortComplex (Modules.{u} O)} (hS : S.ShortExact)
    (J : ResolutionShortComplex.{u} O 𝒰 S) :
    (resolutionDerivedComparison (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₃).hom ≫
        mapExtendSESδ (cechCohomologyZeroFunctor.{u} O 𝒰)
          (R := ShortComplex.mk J.f J.g J.zero) J.mappedShortExact =
      (DerivedCategory.Plus.ι.map
            ((CechDelta.derivedDeltaFunctorStructure
              (cechCohomologyZeroFunctor.{u} O 𝒰)).δ hS) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
            ((cechCohomologyZeroFunctor.{u} O 𝒰).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor (Modules.{u} O) 0).obj S.X₁))) ≫
        ((resolutionDerivedComparison (cechCohomologyZeroFunctor.{u} O 𝒰) J.J₁).hom)⟦(1 : ℤ)⟧' :=
  (comm₃_resolutionDerivedComparison (cechCohomologyZeroFunctor.{u} O 𝒰) hS J.J₁ J.J₂ J.J₃
    J.f J.g J.zero J.comm_f J.comm_g J.shortExact J.mappedShortExact).trans
    (eq_whisker (mapδ_rightDerivedFunctorPlus_comp_ι_singlePlusδ
      (cechCohomologyZeroFunctor.{u} O 𝒰) hS) _)

/-- **The `derivedδ_eq` field of `CechDerivedComparison`.** -/
theorem derivedδ_eq {S : ShortComplex (Modules.{u} O)}
    (hS : S.ShortExact) (J : ResolutionShortComplex.{u} O 𝒰 S) (n : ℕ) :
    (eqToHom (derivedDeltaFunctor_functor.{u} O 𝒰 n).symm).app S.X₃ ≫
        (derivedDeltaFunctor.{u} O 𝒰).δ hS n ≫
        (eqToHom (derivedDeltaFunctor_functor.{u} O 𝒰 (n + 1))).app S.X₁ =
      rightDerivedConnecting.{u} O 𝒰 J n :=
  derivedδ_eq_of_comm₃ O 𝒰 hS J n (comm₃_cech O 𝒰 hS J)

end Stacks.Cohomology.CechComparison

end
