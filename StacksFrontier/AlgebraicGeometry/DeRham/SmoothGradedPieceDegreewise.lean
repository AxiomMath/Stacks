module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequenceFiltered
public import StacksFrontier.AlgebraicGeometry.DeRham.PulledBackFormsComparisonEpi
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceAsImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.DerivedFunctor
public import StacksFrontier.CategoryTheory.Subobject.CokernelOfLE
public import StacksCore.CategoryTheory.Abelian.Subobject
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.DerivedFunctor
public import StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltrationDegreewise

/-!
# The graded pieces of the filtration of Section 0FMK, degree by degree

[Stacks, Section 0FMK] filters the relative de Rham complex `Ω^•_{X/S}` of a morphism
`f : X ⟶ Y` over a base `S` by the forms pulled back from `Y`, and identifies the graded pieces.
This file proves the identification one degree at a time: for every cut `k` and `n = k + 1 + m`,

`(gr^kΩ^•_{X/S})^n  ≅  (gr^kΩ^n_{X/S})|_{(f∘g)^{-1}𝒪_S}`.

## Main definitions

* `Stacks.DeRhamSmooth.gradedPieceXIsoExteriorGraded`: **the degreewise identification**,
  `(gr^kΩ^•_{X/S})^n ≅ (gr^kΩ^n_{X/S})|_{(f∘g)^{-1}𝒪_S}`, for every `k` and `n = k + 1 + m`.
* `Stacks.GradedPieceImage.cokernelIsoCokernelOfLEMk`: the quotient `A/B` of a composable pair
  read as a quotient of the two subobjects of the ambient object they present, with
  `Stacks.GradedPieceImage.π_cokernelIsoCokernelOfLEMk_hom` and
  `Stacks.GradedPieceImage.π_cokernelOfLEIsoOfEq'_hom` saying that it and the change of
  description of the two subobjects carry the projection out of the numerator to the projection
  out of the numerator.

## Main results

* `Stacks.DeRhamSmooth.mk_ι_app_f_eq`: the degree-`n` term of the `k`-th step of the
  complex-level filtration, as a subobject, is the step at `k` of the filtration of the single
  sheaf `Ω^n_{X/S}`, for every `k ≤ n` — including `k = 0`, where both are the whole of degree
  `n`.
* `Stacks.DeRhamSmooth.relativeDifferentialsExteriorFiltration_eq` and
  `Stacks.DeRhamSmooth.relativeDifferentialsExteriorFiltration_succ_eq`: the two steps of the
  filtration of `Ω^n_{X/S}` that bound the `k`-th graded piece, written as images of the wedge
  maps.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 0129](https://stacks.math.columbia.edu/tag/0129)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.DeRhamDirectImage

universe v u

namespace Stacks.GradedPieceImage

variable {C : Type u} [Category.{v} C] [Abelian C] {B A Z : C}

/-- **`A/B ≅ N/W`** where `W ≤ N` are the subobjects of `Z` that `i ≫ j = ψ` and `j` present:
for `j : A ⟶ Z` and `ψ : B ⟶ Z` monomorphisms and `i : B ⟶ A` with `i ≫ j = ψ`, the cokernel of
`i` is the quotient of the subobject presented by `j` by the one presented by `ψ`. -/
def cokernelIsoCokernelOfLEMk (i : B ⟶ A) (j : A ⟶ Z) [Mono j] (ψ : B ⟶ Z) [Mono ψ]
    (hij : i ≫ j = ψ) :
    cokernel i ≅ cokernel (Subobject.ofLE (Subobject.mk ψ) (Subobject.mk j)
      (Subobject.mk_le_mk_of_comm i hij)) :=
  cokernel.mapIso _ _ (Subobject.underlyingIso ψ).symm (Subobject.underlyingIso j).symm (by
    rw [← cancel_mono (Subobject.mk j).arrow, Category.assoc, Category.assoc,
      Iso.symm_hom, Iso.symm_hom, Subobject.underlyingIso_arrow, Subobject.ofLE_arrow,
      Subobject.underlyingIso_arrow, hij])

/-- **`Stacks.GradedPieceImage.cokernelIsoCokernelOfLEMk` carries the projection `A ⟶ A/B` to the
projection onto the quotient of subobjects**, up to the identification of `A` with the subobject
it presents. -/
@[reassoc]
theorem π_cokernelIsoCokernelOfLEMk_hom (i : B ⟶ A) (j : A ⟶ Z) [Mono j] (ψ : B ⟶ Z) [Mono ψ]
    (hij : i ≫ j = ψ) :
    cokernel.π i ≫ (cokernelIsoCokernelOfLEMk i j ψ hij).hom =
      (Subobject.underlyingIso j).inv ≫
        cokernel.π (Subobject.ofLE (Subobject.mk ψ) (Subobject.mk j)
          (Subobject.mk_le_mk_of_comm i hij)) :=
  cokernel.π_desc _ _ _

omit [Abelian C] in
/-- The inverse of an isomorphism is a monomorphism. -/
theorem mono_iso_inv {A' B' : C} (e : A' ≅ B') : Mono e.inv := inferInstance

/-- In an abelian category, the isomorphism `N / W ≅ N' / W'` of quotients of subobjects induced
by equalities `W = W'` and `N = N'`. -/
def cokernelOfLEIsoOfEq' {Y : C} {W N W' N' : Subobject Y} (h : W ≤ N) (h' : W' ≤ N')
    (hW : W = W') (hN : N = N') :
    cokernel (Subobject.ofLE W N h) ≅ cokernel (Subobject.ofLE W' N' h') :=
  CategoryTheory.Subobject.cokernelOfLEIsoOfEq h h' hW hN

/-- **`Stacks.GradedPieceImage.cokernelOfLEIsoOfEq'` is induced by the inclusion `N ⟶ N'`**, so
it carries the projection out of `N` to the projection out of `N'`. -/
@[reassoc]
theorem π_cokernelOfLEIsoOfEq'_hom {Y : C} {W N W' N' : Subobject Y} (h : W ≤ N) (h' : W' ≤ N')
    (hW : W = W') (hN : N = N') :
    cokernel.π (Subobject.ofLE W N h) ≫ (cokernelOfLEIsoOfEq' h h' hW hN).hom =
      Subobject.ofLE N N' hN.le ≫ cokernel.π (Subobject.ofLE W' N' h') :=
  CategoryTheory.Subobject.π_cokernelOfLEIsoOfEq_hom h h' hW hN

/-- Transporting a subobject along a functor preserving monomorphisms presents it by the image
of its inclusion. -/
theorem mapSubobjects_obj {C₁ : Type*} [Category* C₁] {D₁ : Type*} [Category* D₁]
    (U : C₁ ⥤ D₁) [U.PreservesMonomorphisms] {Z : C₁} (P : Subobject Z) :
    (mapSubobjects U Z).obj P = Subobject.mk (U.map P.arrow) :=
  (congrArg (mapSubobjects U Z).obj (Subobject.mk_arrow P).symm).trans
    (mapSubobjects_mk U P.arrow)

omit [Abelian C] in
/-- **The whole object stays the whole object** under transport along a functor preserving
monomorphisms followed by transport along an isomorphism: both carry `⊤` to `⊤`. -/
theorem map_mapSubobjects_top {D : Type*} [Category* D] (U : C ⥤ D)
    [U.PreservesMonomorphisms] {Z' : D} (e : U.obj Z ≅ Z') :
    (Subobject.map e.hom).obj ((mapSubobjects U Z).obj ⊤) = ⊤ := by
  rw [mapSubobjects_obj, Subobject.mk_eq_top_of_isIso (U.map (⊤ : Subobject Z).arrow),
    Subobject.map_top, Subobject.mk_eq_top_of_isIso]

end Stacks.GradedPieceImage

namespace Stacks.DeRhamSmooth

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The degree-`m` term of the `k`-th step of the filtration of Section 50.12, as a subobject
of the degree-`m` term of `Ω^•_{X/S}`**, for `k ≤ m`: it is the step at `k` of the filtration of
the single sheaf `Ω^m_{X/S}` by the forms pulled back from `Y`, read over `(f∘g)^{-1}𝒪_S` and
pushed into the extension by zero. -/
theorem mk_ι_app_f_eq (k m : ℕ) (hk : k ≤ m) :
    Subobject.mk (((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f (m : ℤ)) =
      (_root_.CategoryTheory.Subobject.map
            ((AlgebraicGeometry.SheafOfModules.deRhamComplex
                (Scheme.Hom.deRhamAlgebras (f ≫ g))
                (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                  (Scheme.Hom.deRhamAlgebras (f ≫ g)))).extendXIso
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv).obj
        ((AlgebraicGeometry.SheafOfModules.exteriorPowerSubobjectRestriction
            (Scheme.Hom.deRhamAlgebras (f ≫ g)) m).obj
          (Scheme.Hom.relativeDifferentialsExteriorFiltration f g m k)) := by
  obtain rfl | hk0 := Nat.eq_zero_or_pos k
  · have : IsIso ((deRhamSmoothFiltration f g).filtration.ι.app (op ((0 : ℕ) : ℤ))) :=
      AlgebraicGeometry.SheafOfModules.isIso_wedgeFiltered_ι_of_nonpos _ _ _ _ _ le_rfl
    refine Eq.trans (Subobject.mk_eq_top_of_isIso _) ?_
    refine Eq.trans ?_ (congrArg (_root_.CategoryTheory.Subobject.map
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex
            (Scheme.Hom.deRhamAlgebras (f ≫ g))
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential
              (Scheme.Hom.deRhamAlgebras (f ≫ g)))).extendXIso
          ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv).obj
      (congrArg (AlgebraicGeometry.SheafOfModules.exteriorPowerSubobjectRestriction
          (Scheme.Hom.deRhamAlgebras (f ≫ g)) m).obj
        (_root_.SheafOfModules.exteriorImageFiltration_zero _ _ _ m))).symm
    exact (Stacks.GradedPieceImage.map_mapSubobjects_top
      (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom
          (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g))))
      ((AlgebraicGeometry.SheafOfModules.deRhamComplex
            (Scheme.Hom.deRhamAlgebras (f ≫ g))
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential
              (Scheme.Hom.deRhamAlgebras (f ≫ g)))).extendXIso
          ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).symm).symm
  · exact (congrArg (mapSubobjects (HomologicalComplex.eval _ (ComplexShape.up ℤ) (m : ℤ)) _).obj
        (AlgebraicGeometry.SheafOfModules.wedgeFiltered_subobject _ _ _ _ (k : ℤ))).trans
      (mapSubobjects_wedgeFiltrationStep_eq_exteriorFiltration' f g k m hk0 hk)

/-- **The `(k+1)`-st step of the filtration of `Ω^n_{X/S}`, `n = k + 1 + m`, is the image of the
wedge map `⋀^{k+1}(f^*Ω_{Y/S}) ⊗_{𝒪_X} Ω^m_{X/S} ⟶ Ω^n_{X/S}`**. -/
theorem relativeDifferentialsExteriorFiltration_succ_eq (k m : ℕ) :
    Scheme.Hom.relativeDifferentialsExteriorFiltration f g (k + 1 + m) (k + 1) =
      imageSubobject (_root_.SheafOfModules.prodWedgeHom
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f g).X₁)
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂)
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂)
        (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) m) :=
  (_root_.SheafOfModules.exteriorImageFiltration_eq_imageSubobject _ _ _ (k + 1) m (k + 1 + m)
    rfl).trans (CategoryTheory.Abelian.SpectralObject.imageSubobject_congr
      (_root_.SheafOfModules.prodWedgeHomOfEq_rfl _ _ _ _ _ (k + 1) m))

/-- **The `k`-th step of the filtration of `Ω^n_{X/S}`, `n = k + 1 + m`, is the image of the
wedge map `⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} Ω^{1+m}_{X/S} ⟶ Ω^n_{X/S}`**, transported along
`k + (1 + m) = n`. -/
theorem relativeDifferentialsExteriorFiltration_eq (k m : ℕ) :
    Scheme.Hom.relativeDifferentialsExteriorFiltration f g (k + 1 + m) k =
      imageSubobject (_root_.SheafOfModules.prodWedgeHom
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
            (Scheme.Hom.relativeDifferentialsShortComplex f g).X₁)
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
            (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂)
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
            (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂)
          (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) k (1 + m) ≫
        eqToHom (congrArg (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
            (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂).exterior.piece
          (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm)) :=
  _root_.SheafOfModules.exteriorImageFiltration_eq_imageSubobject _ _ _ k (1 + m)
    (k + 1 + m) (by omega)

/-- **The degree-`n` term of the `k`-th graded piece of the filtration of Section 0FMK is the
cokernel of the degree-`n` term of the step `F^{k+1}Ω^•_{X/S} ⟶ F^kΩ^•_{X/S}`**,
`n = k + 1 + m`. -/
def gradedPieceXIsoCokernelStep (k m : ℕ) :
    (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)).X ((k + 1 + m : ℕ)
        : ℤ) ≅
      cokernel ((HomologicalComplex.eval _ (ComplexShape.up ℤ) ((k + 1 + m : ℕ) : ℤ)).map
        ((deRhamSmoothFiltration f g).filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : ((k : ℤ) : ℤ) ⟶ (k : ℤ) + 1).op)) :=
  have G : ∀ (𝒜 : Type (u + 1)) [Category.{u} 𝒜] [Abelian 𝒜]
        (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ),
        ((FilteredObject.gr (k : ℤ)).obj K).X ((k + 1 + m : ℕ) : ℤ) ≅
          cokernel ((HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) ((k + 1 + m : ℕ) : ℤ)).map
            (K.filtration.diagram.map
              (homOfLE (Int.le_add_one le_rfl) : ((k : ℤ) : ℤ) ⟶ (k : ℤ) + 1).op)) :=
      fun 𝒜 _ _ K ↦ PreservesCokernel.iso
        (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) ((k + 1 + m : ℕ) : ℤ))
        (K.filtration.diagram.map
          (homOfLE (Int.le_add_one le_rfl) : ((k : ℤ) : ℤ) ⟶ (k : ℤ) + 1).op)
  G _ (deRhamSmoothFiltration f g)

/-- **`Stacks.DeRhamSmooth.gradedPieceXIsoCokernelStep` carries the projection onto the graded
piece to the cokernel projection**. -/
theorem grMapπ_f_gradedPieceXIsoCokernelStep_hom (k m : ℕ) :
    (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ)) (deRhamSmoothFiltration f g)).f ((k + 1
        + m : ℕ) : ℤ) ≫
        (gradedPieceXIsoCokernelStep f g k m).hom =
      cokernel.π ((HomologicalComplex.eval _ (ComplexShape.up ℤ) ((k + 1 + m : ℕ) : ℤ)).map
        ((deRhamSmoothFiltration f g).filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : ((k : ℤ) : ℤ) ⟶ (k : ℤ) + 1).op)) :=
  have Gπ : ∀ (𝒜 : Type (u + 1)) [Category.{u} 𝒜] [Abelian 𝒜]
      (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ),
      (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ)) K).f ((k + 1 + m : ℕ) : ℤ) ≫
          (PreservesCokernel.iso
            (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) ((k + 1 + m : ℕ) : ℤ))
            (K.filtration.diagram.map
              (homOfLE (Int.le_add_one le_rfl) : ((k : ℤ) : ℤ) ⟶ (k : ℤ) + 1).op)).hom =
        cokernel.π ((HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) ((k + 1 + m : ℕ) : ℤ)).map
          (K.filtration.diagram.map
            (homOfLE (Int.le_add_one le_rfl) : ((k : ℤ) : ℤ) ⟶ (k : ℤ) + 1).op)) :=
    fun 𝒜 _ _ K ↦ PreservesCokernel.π_iso_hom
      (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) ((k + 1 + m : ℕ) : ℤ))
      (K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : ((k : ℤ) : ℤ) ⟶ (k : ℤ) + 1).op)
  Gπ _ (deRhamSmoothFiltration f g)

/-- For `f : X ⟶ Y` over a base `S`, a cut `k` and `n = k + 1 + m`, the degree-`n` term of the
`k`-th graded piece of the filtration of `Ω^•_{X/S}` by the forms pulled back from `Y` is the
graded piece `gr^kΩ^n_{X/S}` of the single sheaf, read over `(f∘g)^{-1}𝒪_S`:

`(gr^kΩ^•_{X/S})^n  ≅  (gr^kΩ^n_{X/S})|_{(f∘g)^{-1}𝒪_S}`. -/
def gradedPieceXIsoExteriorGraded (k m : ℕ) :
    (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)).X
        ((k + 1 + m : ℕ) : ℤ) ≅
      (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom
          (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g)))).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialsExteriorGraded f g k m) := by
  have hle : Scheme.Hom.relativeDifferentialsExteriorFiltration f g (k + 1 + m) (k + 1) ≤
      Scheme.Hom.relativeDifferentialsExteriorFiltration f g (k + 1 + m) k :=
    _root_.SheafOfModules.exteriorImageFiltration_antitone _ _ _ (k + 1 + m) (Nat.le_succ k)
  have hle2 := AlgebraicGeometry.SheafOfModules.exteriorPowerSubobjectRestriction_monotone
    (Scheme.Hom.deRhamAlgebras (f ≫ g)) (k + 1 + m) hle
  have hle3 := leOfHom ((_root_.CategoryTheory.Subobject.map
    ((AlgebraicGeometry.SheafOfModules.deRhamComplex
        (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential
          (Scheme.Hom.deRhamAlgebras (f ≫ g)))).extendXIso
      ComplexShape.embeddingUpNat (i := k + 1 + m) (i' := ((k + 1 + m : ℕ) : ℤ)) rfl).inv).map
        (homOfLE hle2))
  haveI := Stacks.GradedPieceImage.mono_iso_inv
    ((AlgebraicGeometry.SheafOfModules.deRhamComplex
        (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential
          (Scheme.Hom.deRhamAlgebras (f ≫ g)))).extendXIso
      ComplexShape.embeddingUpNat (i := k + 1 + m) (i' := ((k + 1 + m : ℕ) : ℤ)) rfl)
  refine gradedPieceXIsoCokernelStep f g k m ≪≫
    Stacks.GradedPieceImage.cokernelIsoCokernelOfLEMk _
      (((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f ((k + 1 + m : ℕ) : ℤ))
      (((deRhamSmoothFiltration f g).filtration.ι.app (op ((k + 1 : ℕ) : ℤ))).f
        ((k + 1 + m : ℕ) : ℤ))
      ((HomologicalComplex.comp_f _ _ _).symm.trans (HomologicalComplex.congr_hom
        ((deRhamSmoothFiltration f g).filtration.diagram_map_comp_ι_app
          (homOfLE (Int.le_add_one le_rfl) : (k : ℤ) ⟶ (k : ℤ) + 1).op) _)) ≪≫
    Stacks.GradedPieceImage.cokernelOfLEIsoOfEq' _ hle3
      (mk_ι_app_f_eq f g (k + 1) (k + 1 + m) (by omega))
      (mk_ι_app_f_eq f g k (k + 1 + m) (by omega)) ≪≫
    CategoryTheory.Abelian.Subobject.cokernelOfLEMapIso
      ((AlgebraicGeometry.SheafOfModules.deRhamComplex
          (Scheme.Hom.deRhamAlgebras (f ≫ g))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (f ≫ g)))).extendXIso
        ComplexShape.embeddingUpNat (i := k + 1 + m) (i' := ((k + 1 + m : ℕ) : ℤ)) rfl).inv
      hle2 ≪≫
    Stacks.GradedPieceImage.cokernelOfLEIsoOfEq' hle2
      (Stacks.GradedPieceImage.mk_map_arrow_le _ _ _ hle)
      (Stacks.GradedPieceImage.mapSubobjects_obj _ _)
      (Stacks.GradedPieceImage.mapSubobjects_obj _ _) ≪≫
    Stacks.GradedPieceImage.cokernelOfLEFunctorMapIso
      (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom
          (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g)))) _ _ hle ≪≫
    Functor.mapIso (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom
          (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g))))
      (Stacks.GradedPieceImage.cokernelOfLEIsoOfEq' hle
        (_root_.SheafOfModules.imageSubobject_prodWedgeHom_succ_le _ _ _ k m)
        (relativeDifferentialsExteriorFiltration_succ_eq f g k m)
        (relativeDifferentialsExteriorFiltration_eq f g k m) ≪≫
      _root_.SheafOfModules.cokernelOfLEIsoExteriorGraded _ _ _ k m)

end Stacks.DeRhamSmooth

end
