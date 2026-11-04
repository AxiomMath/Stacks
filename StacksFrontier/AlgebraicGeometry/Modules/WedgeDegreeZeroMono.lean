module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraDegreeZeroIso
public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorGradedPiece
public import StacksFrontier.AlgebraicGeometry.Modules.ExteriorGradedOpenSubspaceAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite

/-!
# The wedge-product morphism at complementary degree zero is a monomorphism

Let `0 ⟶ T.X₁ ⟶ T.X₂ ⟶ T.X₃ ⟶ 0` be a short exact sequence of sheaves of modules which splits
over an open neighbourhood of every point of a scheme. The wedge-product morphism

`⋀^pT.X₁ ⊗ ⋀^0T.X₂ ⟶ ⋀^pT.X₂`

is a monomorphism, so the top step `p = n` of the filtration of `⋀ⁿT.X₂` by the images of the
wedge-product morphisms `⋀^pT.X₁ ⊗ ⋀^qT.X₂ ⟶ ⋀ⁿT.X₂`, `p + q = n`, is its source.

## Main results

* `SheafOfModules.isIso_exteriorPieceMap_of_eq_zero`: `⋀^0` of any morphism is an isomorphism.
* `SheafOfModules.mono_prodWedgeHomOfEq_splitting` and
  `SheafOfModules.mono_prodWedgeHom_splitting`: the wedge-product morphism along a splitting is a
  monomorphism in every bidegree `p + q = n`.
* `SheafOfModules.mono_prodWedgeHom_id_right_of_splitting`: the wedge-product morphism along the
  identity is a monomorphism at complementary degree zero, for a split sequence.
* `SheafOfModules.mono_openSubspaceRestriction_map_prodWedgeHom_id_right_of_splitting`: the same
  for its restriction to an open subspace over which the sequence splits.
* `Stacks.AlgebraicGeometry.Modules.mono_of_mono_openSubspaceRestriction_cover`: monomorphy of a
  morphism of `𝒪_X`-modules is local, with restriction to open subspaces.
* `SheafOfModules.mono_prodWedgeHom_id_right_of_locally_split` and
  `SheafOfModules.mono_prodWedgeHomOfEq_id_right_of_locally_split`: the wedge-product morphism at
  complementary degree zero is a monomorphism for a sequence of `𝒪_X`-modules on a scheme which
  splits over an open neighbourhood of every point.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace
open Stacks.Cohomology.HigherDirectImage (restrictToOpen)
open Stacks.SheafOfModules.PushforwardSheafification

attribute [local instance] SheafOfModules.monoidalSheaves
attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite

universe u

namespace Stacks.CategoryTheory

/-- If `u` is an isomorphism and `u ≫ v` is a monomorphism, then `v` is a monomorphism. -/
theorem mono_of_isIso_comp {C₁ : Type*} [_root_.CategoryTheory.Category C₁] {P Q R : C₁}
    (u : P ⟶ Q) (v : Q ⟶ R) (hu : IsIso u) (h : Mono (u ≫ v)) : Mono v :=
  have := hu
  have := h
  Eq.mpr (congrArg Mono (IsIso.inv_hom_id_assoc u v).symm)
    (mono_comp (_root_.CategoryTheory.inv u) (u ≫ v))

end Stacks.CategoryTheory

namespace SheafOfModules

open MonoidalCategory

/-! ### Degree zero carries no information -/

section DegreeZero

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F G : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)
  (AG : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G)

/-- `⋀^0` of any morphism of sheaves of modules is an isomorphism, stated at a degree `n` with
`n = 0`. -/
theorem isIso_exteriorPieceMap_of_eq_zero (φ : F ⟶ G) (n : ℤ) (hn : n = 0) :
    IsIso (AF.exterior_isExteriorAlgebra.pieceMap AG.exterior_isExteriorAlgebra φ n) := by
  subst hn
  exact GradedAlgebra.isIso_unitalHom_app_zero AF.exteriorPieceIso_zero
    AF.exteriorPieceIso_zero_one AG.exteriorPieceIso_zero AG.exteriorPieceIso_zero_one _

end DegreeZero

/-! ### The wedge-product morphism along a splitting, in every bidegree -/

section Splitting

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {T : ShortComplex
    (SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp))}
  (AF₁ : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) T.X₁)
  (AG₃ : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) T.X₃)
  (A₂ : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) T.X₂)

/-- The wedge-product morphism `⋀^pT.X₁ ⊗ ⋀^qT.X₃ ⟶ ⋀ⁿT.X₂`, `p + q = n`, formed from the
inclusion of the sub and the section of a splitting, is a monomorphism: it is split by
`SheafOfModules.exteriorKunnethRetraction`. -/
theorem mono_prodWedgeHomOfEq_splitting (sp : T.Splitting) (p q n : ℕ) (h : p + q = n) :
    Mono (prodWedgeHomOfEq AF₁ AG₃ A₂ T.f sp.s p q n h) :=
  Stacks.CategoryTheory.mono_of_comp_eq_id _
    (exteriorKunnethRetraction AF₁ AG₃ A₂ sp p q n h)
    (prodWedgeHomOfEq_comp_exteriorKunnethRetraction AF₁ AG₃ A₂ sp p q n h)

/-- `SheafOfModules.mono_prodWedgeHomOfEq_splitting` at the untransported total degree
`p + q`. -/
theorem mono_prodWedgeHom_splitting (sp : T.Splitting) (p q : ℕ) :
    Mono (prodWedgeHom AF₁ AG₃ A₂ T.f sp.s p q) :=
  Eq.mpr (congrArg Mono (prodWedgeHomOfEq_rfl AF₁ AG₃ A₂ T.f sp.s p q).symm)
    (mono_prodWedgeHomOfEq_splitting AF₁ AG₃ A₂ sp p q (p + q) rfl)

include AG₃ in
/-- For a split sequence, the wedge-product morphism `⋀^pT.X₁ ⊗ ⋀^qT.X₂ ⟶ ⋀^pT.X₂` along the
identity of `T.X₂` is a monomorphism at complementary degree `q = 0`. -/
theorem mono_prodWedgeHom_id_right_of_splitting (sp : T.Splitting) (p q : ℕ) (hq : q = 0) :
    Mono (prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) p q) := by
  subst hq
  exact Stacks.CategoryTheory.mono_of_isIso_comp
    (AF₁.exteriorPower p ◁ AG₃.exterior_isExteriorAlgebra.pieceMap
      A₂.exterior_isExteriorAlgebra sp.s ((0 : ℕ) : ℤ))
    (prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) p 0)
    ((whiskerLeftIso (AF₁.exteriorPower p)
      (@asIso _ _ _ _ (AG₃.exterior_isExteriorAlgebra.pieceMap
          A₂.exterior_isExteriorAlgebra sp.s ((0 : ℕ) : ℤ))
        (isIso_exteriorPieceMap_of_eq_zero AG₃ A₂ sp.s ((0 : ℕ) : ℤ)
          (Nat.cast_zero)))).isIso_hom)
    (Eq.mpr (congrArg Mono
        (prodWedgeHom_eq_whiskerLeft_pieceMap_comp AF₁ AG₃ A₂ T.f sp.s p 0).symm)
      (mono_prodWedgeHom_splitting AF₁ AG₃ A₂ sp p 0))

end Splitting

/-! ### The crossing of restriction to an open subspace -/

section OpenSubspace

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  {T : ShortComplex (SheafOfModules.{u} (structureSheafRing X))}
  (AF₁ : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) T.X₁)
  (A₂ : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) T.X₂)

/-- The restriction to an open subspace `U` of the wedge-product morphism along the identity at
complementary degree zero is a monomorphism when the sequence restricted to `U` splits. -/
theorem mono_openSubspaceRestriction_map_prodWedgeHom_id_right_of_splitting
    (sp : (openSubspaceShortComplex U (T := T)).Splitting) (p q : ℕ) (hq : q = 0) :
    Mono ((openSubspaceRestriction U).map (prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) p q)) :=
  mono_of_comp_iso_eq_iso_comp _ _
    (openSubspaceRestriction_map_prodWedgeHom_comp_exteriorRestrictOpenSubspaceIso_hom U
      AF₁ A₂ A₂
      (ringedSpaceAlgebras (restrictToOpen X U) ((openSubspaceRestriction U).obj T.X₁))
      (ringedSpaceAlgebras (restrictToOpen X U) ((openSubspaceRestriction U).obj T.X₂))
      (ringedSpaceAlgebras (restrictToOpen X U) ((openSubspaceRestriction U).obj T.X₂))
      T.f (𝟙 T.X₂) p q)
    (mono_prodWedgeHom_id_right_of_splitting (T := openSubspaceShortComplex U (T := T))
      (ringedSpaceAlgebras (restrictToOpen X U) ((openSubspaceRestriction U).obj T.X₁))
      (ringedSpaceAlgebras (restrictToOpen X U) ((openSubspaceRestriction U).obj T.X₃))
      (ringedSpaceAlgebras (restrictToOpen X U) ((openSubspaceRestriction U).obj T.X₂))
      sp p q hq)

end OpenSubspace

end SheafOfModules

/-! ### Monomorphy is local in the open-subspace spelling -/

namespace Stacks.AlgebraicGeometry.Modules

/-- Monomorphy of a morphism of `𝒪_X`-modules on a scheme is local, with restriction to open
subspaces: a morphism whose restriction to an open neighbourhood of every point is a monomorphism
is a monomorphism. -/
theorem mono_of_mono_openSubspaceRestriction_cover {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N)
    (H : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Mono ((SheafOfModules.openSubspaceRestriction (X := X.toRingedSpace) U).map φ)) :
    Mono φ :=
  mono_of_mono_restrict_cover φ (fun x : X => (H x).choose.ι)
    (fun x => ⟨x, ⟨x, (H x).choose_spec.1⟩, rfl⟩)
    (fun x => SheafOfModules.mono_restrictFunctor_map_of_mono_openSubspaceRestriction_map X
      (H x).choose φ (H x).choose_spec.2)

end Stacks.AlgebraicGeometry.Modules

namespace SheafOfModules

/-! ### The globalization -/

section Locality

variable {X : Scheme.{u}}
  {T : ShortComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))}
  (AF₁ : TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.toRingedSpace.carrier) T.X₁)
  (A₂ : TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.toRingedSpace.carrier) T.X₂)

/-- The wedge-product morphism `⋀^pT.X₁ ⊗_{𝒪_X} ⋀^qT.X₂ ⟶ ⋀^pT.X₂` along the identity at
complementary degree `q = 0` is a monomorphism, for a short complex of `𝒪_X`-modules on a scheme
whose restriction to an open neighbourhood of every point splits. -/
theorem mono_prodWedgeHom_id_right_of_locally_split (p q : ℕ) (hq : q = 0)
    (H : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (openSubspaceShortComplex (X := X.toRingedSpace) U (T := T)).Splitting) :
    Mono (prodWedgeHom AF₁ A₂ A₂ T.f (𝟙 T.X₂) p q) :=
  Stacks.AlgebraicGeometry.Modules.mono_of_mono_openSubspaceRestriction_cover _
    (fun x => ⟨(H x).choose, (H x).choose_spec.1,
      mono_openSubspaceRestriction_map_prodWedgeHom_id_right_of_splitting (H x).choose AF₁ A₂
        (H x).choose_spec.2.some p q hq⟩)

/-- `SheafOfModules.mono_prodWedgeHom_id_right_of_locally_split` at the transported total
degree `n` with `p + q = n`. -/
theorem mono_prodWedgeHomOfEq_id_right_of_locally_split (p q n : ℕ) (hq : q = 0) (h : p + q = n)
    (H : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (openSubspaceShortComplex (X := X.toRingedSpace) U (T := T)).Splitting) :
    Mono (prodWedgeHomOfEq AF₁ A₂ A₂ T.f (𝟙 T.X₂) p q n h) :=
  Stacks.CategoryTheory.mono_comp_of_mono _ _
    (mono_prodWedgeHom_id_right_of_locally_split AF₁ A₂ p q hq H)
    (IsIso.mono_of_iso (eqToHom (congrArg (fun m : ℕ => A₂.exteriorPower m) h)))

end Locality

end SheafOfModules

end
