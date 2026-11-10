module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatPullbackTensorTriangle
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BraidingNatIso
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackFromTheStalkCriterion
public import StacksFrontier.AlgebraicGeometry.RingedSpace.KFlatResolution

/-!
# The descent of `M ↦ Tot(f^*M ⊗ 𝒢)` is `Lf^*(-) ⊗^L 𝒢`

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `𝒢` a bounded complex of
`𝒪_X`-modules with terms flat over `Y`.  The functor `M ↦ Tot(f^*M ⊗_{𝒪_X} 𝒢)` on complexes
preserves quasi-isomorphisms and descends to `R : D(𝒪_Y) ⥤ D(𝒪_X)`
(`Stacks.Cohomology.FlatPullbackTensor.derivedFunctor`).  This file identifies `R` with the
derived functor

`M ↦ Lf^*M ⊗^L_{𝒪_X} 𝒢`

on all of `D(𝒪_Y)`, and with `M ↦ 𝒢 ⊗^L_{𝒪_X} Lf^*M` through the symmetry of the derived tensor
product ([Stacks, Tag 0FPT]).  This is the identification `𝒢 ⊗^L_{𝒪_X} Lf^*ℱ = 𝒢 ⊗_{𝒪_X} f^*ℱ`
which the proof of [Stacks, Tag 0A1F] derives from [Stacks, Tag 08DE] and flatness of the terms
of `𝒢` over `Y`, in the form of an isomorphism of functors on `D(𝒪_Y)`.

## Main definitions

* `Stacks.Cohomology.FlatPullbackTensor.comparison`: the canonical map
  `Lf^*(QM) ⊗^L Q𝒢 ⟶ Q(f^*M) ⊗^L Q𝒢 ⟶ Q(Tot(f^*M ⊗ 𝒢))`, natural in the complex `M`.
* `Stacks.Cohomology.FlatPullbackTensor.derivedPullbackTensorIso`:
  `Lf^*(-) ⊗^L 𝒢 ≅ R` on `D(𝒪_Y)`.
* `Stacks.Cohomology.FlatPullbackTensor.derivedPullbackTensorLeftIso`:
  `𝒢 ⊗^L Lf^*(-) ≅ R` on `D(𝒪_Y)`.

## Main results

* `Stacks.Cohomology.FlatPullbackTensor.isIso_comparison_app`: the canonical map is invertible
  at every complex.  At a K-flat `M` both of its factors are invertible: `Lf^*` is computed by
  the K-flat `M` and the derived tensor product by the K-flat `f^*M` ([Stacks, Tag 06YC]).  A
  K-flat resolution `P ⟶ M` carries this to `M`, because both sides invert quasi-isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.Cohomology.FlatPullbackTensor

universe u

attribute [local instance] HasDerivedCategory.standard

open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (Modules)
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex derivedPullbackNatTrans)

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (G : CochainComplex (Modules X) ℤ)

/-- `- ⊗^L_{𝒪_X} 𝒢` on `D(𝒪_X)`, for the derived tensor product of [Stacks, Tag 06YU]. -/
abbrev tensorRightQ : DerivedCategory (Modules X) ⥤ DerivedCategory (Modules X) :=
  (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).flip.obj
    (DerivedCategory.Q.obj G)

/-- `M ↦ Lf^*M ⊗^L_{𝒪_X} 𝒢` on `D(𝒪_Y)`. -/
abbrev derivedPullbackTensor :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤ DerivedCategory (Modules X) :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f ⋙ tensorRightQ G

/-- **The canonical map `Lf^*(QM) ⊗^L Q𝒢 ⟶ Q(Tot(f^*M ⊗ 𝒢))`**, natural in the complex `M` of
`𝒪_Y`-modules: the comparison of `Lf^*` with the degreewise pullback, followed by the canonical
map from the derived to the ordinary total tensor product (the `toTensor` field of
[Stacks, Tag 06YU]). -/
def comparison :
    DerivedCategory.Q ⋙ derivedPullbackTensor f G ⟶ complexFunctor f G ⋙ DerivedCategory.Q where
  app M := (tensorRightQ G).map ((derivedPullbackNatTrans f).app M) ≫
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).toTensor
      ((pullbackComplex f).obj M) G
  naturality {M M'} φ := by
    have h := (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf
      ).toTensor_naturality ((pullbackComplex f).map φ) (𝟙 G)
    simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
    have hn := (derivedPullbackNatTrans f).naturality φ
    have hn2 := (((tensorRightQ G).map_comp _ _).symm.trans
      ((congrArg (tensorRightQ G).map hn).trans ((tensorRightQ G).map_comp _ _)))
    exact (Category.assoc _ _ _).symm.trans ((eq_whisker hn2 _).trans
      ((Category.assoc _ _ _).trans ((whisker_eq _ h).trans (Category.assoc _ _ _).symm)))

/-- The component of `comparison` at a complex `M` is `Lf^*` of the comparison map for `M`,
followed by the canonical map from the derived to the ordinary total tensor product. -/
theorem comparison_app (M : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) :
    (comparison f G).app M = (tensorRightQ G).map ((derivedPullbackNatTrans f).app M) ≫
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).toTensor
        ((pullbackComplex f).obj M) G :=
  rfl

/-- **At a K-flat complex the canonical map is invertible**: `Lf^*` is computed by the K-flat
complex itself, and the derived tensor product by the K-flat complex `f^*M`
([Stacks, Tag 06YC]) in its left factor. -/
theorem isIso_comparison_app_of_kFlat (M : CochainComplex (Modules Y) ℤ)
    (hM : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y M) :
    IsIso ((comparison f G).app M) := by
  have h₁ := Stacks.Cohomology.DerivedPullbackTensor.isIso_derivedPullbackNatTrans_app f M hM
  have hK : Stacks.SheafOfModules.KFlat X.sheaf ((pullbackComplex f).obj M) :=
    Stacks.SheafOfModules.KFlatPullback.kFlat_pullback_unconditional f M hM
  have e := (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf
      ).toTensor_eq_comparisonLeft ((pullbackComplex f).obj M) G hK
  have h₂ : IsIso ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).toTensor
      ((pullbackComplex f).obj M) G) :=
    (congrArg (fun g => IsIso g) e).mpr inferInstance
  have h₃ := @Functor.map_isIso _ _ _ _ _ _ (tensorRightQ G) _ h₁
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₃ h₂

variable (hflat : ∀ q : ℤ, AlgebraicGeometry.IsFlatOver f (G.X q))
  (hb : ∃ a b : ℤ, G.IsStrictlyGE a ∧ G.IsStrictlyLE b)

include hflat hb in
/-- **The canonical map `Lf^*(QM) ⊗^L Q𝒢 ⟶ Q(Tot(f^*M ⊗ 𝒢))` is invertible at every complex.**
A K-flat resolution `P ⟶ M` ([Stacks, Tag 06YS]) is a quasi-isomorphism, which both sides
invert: the left side because it factors through `D(𝒪_Y)`, the right side because
`M ↦ Tot(f^*M ⊗ 𝒢)` preserves quasi-isomorphisms. -/
theorem isIso_comparison_app (M : CochainComplex (Modules Y) ℤ) :
    IsIso ((comparison f G).app M) := by
  obtain ⟨P, p, hP, -, hp, -⟩ :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlatResolution Y M
  have hPiso := isIso_comparison_app_of_kFlat f G P hP
  have hQ : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
  have hΨ : IsIso ((complexFunctor f G ⋙ DerivedCategory.Q).map p) := by
    obtain ⟨a, b, ha, hb'⟩ := hb
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (quasiIso_complexFunctor_map f G hflat a b p hp)
  have hL : IsIso ((DerivedCategory.Q ⋙ derivedPullbackTensor f G).map p) :=
    @Functor.map_isIso _ _ _ _ _ _ (derivedPullbackTensor f G) _ hQ
  have : IsIso ((DerivedCategory.Q ⋙ derivedPullbackTensor f G).map p ≫
      (comparison f G).app M) :=
    ((comparison f G).naturality p ▸ inferInstance)
  exact IsIso.of_isIso_comp_left ((DerivedCategory.Q ⋙ derivedPullbackTensor f G).map p) _

include hflat hb in
/-- The canonical map `comparison` is an isomorphism of functors on cochain complexes. -/
theorem isIso_comparison : IsIso (comparison f G) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (comparison f G)
    (fun M => isIso_comparison_app f G hflat hb M)

/-- The canonical isomorphism `Lf^*(QM) ⊗^L Q𝒢 ≅ Q(Tot(f^*M ⊗ 𝒢))` of functors on complexes of
`𝒪_Y`-modules, whose forward map is `comparison`. -/
def comparisonIso :
    DerivedCategory.Q ⋙ derivedPullbackTensor f G ≅ complexFunctor f G ⋙ DerivedCategory.Q :=
  @asIso _ _ _ _ (comparison f G) (isIso_comparison f G hflat hb)

/-- The forward map of `comparisonIso` is `comparison`. -/
@[simp]
theorem comparisonIso_hom : (comparisonIso f G hflat hb).hom = comparison f G :=
  rfl

/-- **`Lf^*(-) ⊗^L_{𝒪_X} 𝒢 ≅ R` on `D(𝒪_Y)`**, `R` the descent of `M ↦ Tot(f^*M ⊗ 𝒢)`: the
isomorphism of functors on `D(𝒪_Y)` whose restriction along `Q` is `comparisonIso` followed by
`derivedFunctorFactors`. -/
def derivedPullbackTensorIso : derivedPullbackTensor f G ≅ derivedFunctor f G hflat hb :=
  (Localization.whiskeringLeftFunctor' DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
      (DerivedCategory (Modules X))).preimageIso
    (comparisonIso f G hflat hb ≪≫ derivedFunctorFactors f G hflat hb)

/-- On the class of a complex `M`, the forward map of `derivedPullbackTensorIso` is the component
of `comparison` at `M` followed by `Q(Tot(f^*M ⊗ 𝒢)) ≅ R(QM)`. -/
theorem derivedPullbackTensorIso_hom_app
    (M : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) :
    (derivedPullbackTensorIso f G hflat hb).hom.app (DerivedCategory.Q.obj M) =
      (comparison f G).app M ≫ (derivedFunctorFactors f G hflat hb).hom.app M := by
  have := congrArg (fun τ => NatTrans.app τ M)
    ((Localization.whiskeringLeftFunctor' DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
      (DerivedCategory (Modules X))).map_preimage
        (comparisonIso f G hflat hb ≪≫ derivedFunctorFactors f G hflat hb).hom)
  refine Eq.trans ?_ this
  rfl

/-- `𝒢 ⊗^L_{𝒪_X} -` on `D(𝒪_X)`. -/
abbrev tensorLeftQ : DerivedCategory (Modules X) ⥤ DerivedCategory (Modules X) :=
  (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj
    (DerivedCategory.Q.obj G)

/-- **`𝒢 ⊗^L_{𝒪_X} Lf^*(-) ≅ R` on `D(𝒪_Y)`**: `derivedPullbackTensorIso` preceded by the
commutativity constraint of the derived tensor product ([Stacks, Tag 0FPT]). -/
def derivedPullbackTensorLeftIso :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f ⋙ tensorLeftQ G ≅
      derivedFunctor f G hflat hb :=
  Functor.isoWhiskerLeft (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
      ((Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso
        (AlgebraicGeometry.RingedSpace.ringedSite X)
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf)).app
          (DerivedCategory.Q.obj G)) ≪≫
    derivedPullbackTensorIso f G hflat hb

end Stacks.Cohomology.FlatPullbackTensor

end
