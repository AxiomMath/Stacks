module

public import StacksFrontier.AlgebraicGeometry.Descent.Module.AmitsurCoefficientsProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.CechVanishingOnAffineSlice
public import StacksFrontier.AlgebraicGeometry.Topologies.CechVanishingStandardCovering

/-!
# Čech vanishing for the base-change coefficients of a module in an arbitrary universe

Let `Y` be an affine scheme with coordinate ring `R = Γ(Y, 𝒪)` and let `M` be an `R`-module in
an arbitrary universe. The presheaf

    `V ↦ Γ(V, 𝒪_V) ⊗_R M`

on the schemes over `Y` has vanishing Čech cohomology in positive degrees on every standard
covering of `Y`.

Over an affine `V` these are the sections of the pullback of the quasi-coherent module attached
to `M`; over a non-affine `V` they are not, and the presheaf is not a Zariski sheaf. It preserves
finite products: global sections take a finite disjoint union of schemes over `Y` to the product
of the coordinate rings, and tensoring with `M` commutes with finite products.

## Main definitions

* `AlgebraicGeometry.overAffineAlgΓBase`: the coordinate-algebra functor of
  `AlgebraicGeometry.overAffineAlgΓ`, read on the schemes over `U.left` rather than on the slice
  at `U`.
* `AlgebraicGeometry.overForgetIsoIteratedSliceFunctor`: the identification of the two readings
  of the slice at an identity morphism.
* `AlgebraicGeometry.amitsurSliceModulePresheaf`: the presheaf `V ↦ Γ(V, 𝒪_V) ⊗_R M` of
  `R`-modules, on the slice at an affine object.
* `AlgebraicGeometry.baseChangeAbelianPresheaf`: the same presheaf of abelian groups, on the
  schemes over an affine scheme `Y`.

## Main results

* `AlgebraicGeometry.preservesFiniteProducts_overAffineAlgΓ_leftOp` and
  `AlgebraicGeometry.preservesFiniteProducts_overAffineAlgΓBase_leftOp`: the coordinate-algebra
  functors preserve finite products.
* `AlgebraicGeometry.overAffineAlgΓBase_algebraMap`: the structure map of the coordinate algebra
  of an object of `Over U.left` is the pullback of global sections along its structure morphism.
* `AlgebraicGeometry.preservesFiniteProducts_baseChangeAbelianPresheaf`: the base-change presheaf
  preserves finite products.
* `AlgebraicGeometry.isZero_cechCohomology_singleton_succ_of_amitsurRestriction`: positive-degree
  Čech vanishing for the one-member covering of an affine object by the spectrum of a faithfully
  flat algebra.
* `AlgebraicGeometry.isZero_cechCohomology_succ_of_amitsurRestriction`: positive-degree Čech
  vanishing on an arbitrary standard `τ`-covering, for a finite-product-preserving abelian presheaf
  given together with the identification of its restriction to the slice.
* `AlgebraicGeometry.isZero_cechCohomology_succ_baseChange`: positive-degree Čech vanishing on a
  standard `τ`-covering of an affine scheme, for the base-change presheaf of a module over its
  coordinate ring.

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CechSite Stacks.Descent

universe u m

namespace AlgebraicGeometry

/-! ### Global sections on an affine slice preserve finite products -/

section Gamma

variable {S : Scheme.{u}} (U : Over S) [IsAffine U.left]

/-- The coordinate-algebra functor on the slice at an affine object preserves finite products:
the coordinate ring of a finite disjoint union of schemes over `U` is the product of their
coordinate rings. -/
instance preservesFiniteProducts_overAffineAlgΓ_leftOp :
    PreservesFiniteProducts (overAffineAlgΓ U).leftOp where
  preserves n := by
    have : PreservesColimitsOfShape (Discrete (Fin n))ᵒᵖ (overAffineAlgΓ U) :=
      (overAffineAlgAdjunction U).leftAdjoint_preservesColimits.preservesColimitsOfShape
    exact preservesLimitsOfShape_leftOp (J := Discrete (Fin n)) (overAffineAlgΓ U)

/-- The coordinate-algebra functor of `AlgebraicGeometry.overAffineAlgΓ`, read on the schemes
over `U.left` instead of on the slice at `U`. -/
abbrev overAffineAlgΓBase : Over U.left ⥤ (CommAlgCat.{u} (ULift.{u} Γ(U.left, ⊤)))ᵒᵖ :=
  (Over.mapIso (specOverAffineBaseRingIso U)).inverse ⋙ algΓ (overAffineBaseRing U)

/-- `AlgebraicGeometry.overAffineAlgΓ` is the slice-of-slice equivalence followed by
`AlgebraicGeometry.overAffineAlgΓBase`, by definition. -/
theorem overAffineAlgΓ_eq_comp :
    overAffineAlgΓ U = (Over.iteratedSliceEquiv U).functor ⋙ overAffineAlgΓBase U := rfl

/-- The coordinate-algebra functor on the schemes over `U.left` preserves finite products. -/
instance preservesFiniteProducts_overAffineAlgΓBase_leftOp :
    PreservesFiniteProducts (overAffineAlgΓBase U).leftOp where
  preserves n := by
    have h : PreservesColimitsOfShape (Discrete (Fin n))ᵒᵖ (algΓ (overAffineBaseRing U)) :=
      (algΓAlgSpecAdjunction
        (overAffineBaseRing U)).leftAdjoint_preservesColimits.preservesColimitsOfShape
    exact preservesLimitsOfShape_leftOp (J := Discrete (Fin n)) (overAffineAlgΓBase U)

/-- The structure map of the coordinate algebra of an object of `Over U.left` is the pullback of
global sections along its structure morphism. -/
theorem overAffineAlgΓBase_algebraMap (Z : Over U.left)
    (c : ULift.{u} (Γ(U.left, ⊤) : Type u)) :
    algebraMap (ULift.{u} (Γ(U.left, ⊤) : Type u))
        (((overAffineAlgΓBase U).obj Z).unop : Type u) c =
      (Scheme.Γ.map Z.hom.op).hom c.down := by
  change (Scheme.Γ.map (Z.hom ≫ (specOverAffineBaseRingIso U).inv).op).hom
      ((Scheme.ΓSpecIso (overAffineBaseRing U)).inv.hom c) = _
  rw [op_comp, Scheme.Γ.map_comp]
  change (Scheme.Γ.map Z.hom.op).hom
    (((Scheme.ΓSpecIso (overAffineBaseRing U)).inv ≫
      Scheme.Γ.map (specOverAffineBaseRingIso U).inv.op).hom c) = _
  rw [ΓSpecIso_inv_comp_Γ_map_specOverAffineBaseRingIso_inv]
  rfl

end Gamma

/-! ### The slice at a terminal object -/

/-- The projection out of the slice at an identity is isomorphic to the functor of the
slice-of-slice equivalence. Both functors send an object of `Over (Over.mk (𝟙 X))` to its
underlying object of `Over X`. -/
def overForgetIsoIteratedSliceFunctor {C : Type*} [Category C] (X : C) :
    Over.forget (Over.mk (𝟙 X)) ≅ (Over.iteratedSliceEquiv (Over.mk (𝟙 X))).functor :=
  NatIso.ofComponents
    (fun X' ↦ Over.isoMk (Iso.refl X'.left.left)
      (by
        change 𝟙 X'.left.left ≫ X'.hom.left = X'.left.hom
        rw [Category.id_comp, ← Category.comp_id X'.hom.left]
        exact Over.w X'.hom))
    (by intro _ _ f; ext; change f.left.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left.left; simp)

/-! ### Čech vanishing with the Amitsur restriction as input -/

section Vanishing

variable {S : Scheme.{u}} (U : Over S) [IsAffine U.left] (M : Type m) [AddCommGroup M]
  [Module (Γ(U.left, ⊤) : Type u) M]

/-- The Amitsur coefficient presheaf `V ↦ Γ(V, 𝒪_V) ⊗_R M` on the slice at `U`, as a presheaf of
`R`-modules for `R = Γ(U.left, 𝒪)`. -/
abbrev amitsurSliceModulePresheaf : (Over U)ᵒᵖ ⥤ ModuleCat.{max u m} (Γ(U.left, ⊤) : Type u) :=
  (overAffineAlgΓ U).leftOp ⋙ amitsurCoefficients.{u, u, m} (Γ(U.left, ⊤) : Type u) M

/-- Positive-degree Čech vanishing for the one-member covering of an affine object of `Over S`
by the spectrum of a faithfully flat algebra, for an abelian presheaf whose restriction to the
slice is the Amitsur coefficient presheaf of `M`. -/
theorem isZero_cechCohomology_singleton_succ_of_amitsurRestriction
    (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u m})
    (e : (Over.forget U).op ⋙ F ≅ amitsurSliceModulePresheaf U M ⋙
      forget₂ (ModuleCat.{max u m} (Γ(U.left, ⊤) : Type u)) AddCommGrpCat.{max u m})
    (A : Type u) [CommRing A] [Algebra (Γ(U.left, ⊤) : Type u) A]
    [Module.FaithfullyFlat (Γ(U.left, ⊤) : Type u) A] (p : ℕ) :
    IsZero (cechCohomology (PreZeroHypercover.singleton.{max u m}
      ((overAffineAlgSpec U).obj (op (overAffineAlgObj U A))).hom) F (p + 1)) :=
  isZero_cechCohomology_singleton_succ_overAffine U A M F (amitsurSliceModulePresheaf U M) e
    (overAffineAlgObj U A) (Iso.refl _) (sectionsTerminalArrowIsoAlgebraMapArrow U A) p

/-- Positive-degree Čech vanishing on a standard `τ`-covering of an affine object of `Over S`,
for a finite-product-preserving abelian presheaf whose restriction to the slice is the Amitsur
coefficient presheaf of `M`. -/
theorem isZero_cechCohomology_succ_of_amitsurRestriction (τ : CoveringTopology)
    (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u m}) [PreservesFiniteProducts F]
    (e : (Over.forget U).op ⋙ F ≅ amitsurSliceModulePresheaf U M ⋙
      forget₂ (ModuleCat.{max u m} (Γ(U.left, ⊤) : Type u)) AddCommGrpCat.{max u m})
    (𝒱 : PreZeroHypercover.{max u m} U)
    (h : IsStandardCovering τ (fun i ↦ (𝒱.X i).left) (fun i ↦ (𝒱.f i).left))
    (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology 𝒱 F p) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp).symm⟩
  have hfin : Finite 𝒱.I₀ := h.finite_index
  have haff : IsAffine (∐ 𝒱.X).left := h.isAffine_left_sigmaObj τ S 𝒱
  let halg := overAffineSliceAlgebra U (Sigma.desc 𝒱.f)
  have hff := h.faithfullyFlat_left_sigmaDesc τ S 𝒱
  have hone : IsZero (cechCohomology
      (PreZeroHypercover.singleton.{max u m} (Sigma.desc 𝒱.f)) F (q + 1)) :=
    isZero_cechCohomology_singleton_of_iso.{max u m} (Sigma.desc 𝒱.f)
      ((overAffineAlgSpec U).obj
        (op (overAffineAlgObj U (Γ((∐ 𝒱.X).left, ⊤) : Type u)))).hom
      (mkIsoMkSpecOverAffineAlgObj U (Sigma.desc 𝒱.f)) F (q + 1)
      (isZero_cechCohomology_singleton_succ_of_amitsurRestriction U M F e
        (Γ((∐ 𝒱.X).left, ⊤) : Type u) q)
  have := Stacks.CechSite.isIso_cechComplexMap_of_preservesFiniteProducts.{max u m} 𝒱 F
  exact hone.of_iso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u m}
    (ComplexShape.up ℕ) (q + 1)).mapIso (asIso (Stacks.CechSite.cechComplexMap 𝒱
      (PreZeroHypercover.singleton.{max u m} (Sigma.desc 𝒱.f))
      (Stacks.CechSite.coproductRefinement 𝒱) F))).symm

end Vanishing

/-! ### The base-change presheaf of a module on the schemes over an affine scheme -/

section BaseChange

variable (Y : Scheme.{u}) [IsAffine Y] (M : Type m) [AddCommGroup M]
  [Module (Γ(Y, ⊤) : Type u) M]

/-- The terminal object `Over.mk (𝟙 Y)` of `Over Y`. -/
abbrev terminalOver : Over Y := Over.mk (𝟙 Y)

/-- The underlying scheme of `terminalOver Y` is affine. -/
instance isAffine_terminalOver_left : IsAffine (terminalOver Y).left := ‹IsAffine Y›

/-- The `R`-module structure on `M` read at `Γ((terminalOver Y).left, 𝒪)` rather than at
`Γ(Y, 𝒪)`, to which it is definitionally equal. -/
local instance module_terminalOver_left : Module (Γ((terminalOver Y).left, ⊤) : Type u) M :=
  inferInstanceAs (Module (Γ(Y, ⊤) : Type u) M)

/-- The base-change presheaf `V ↦ Γ(V, 𝒪_V) ⊗_R M` of abelian groups on the schemes over `Y`. -/
abbrev baseChangeAbelianPresheaf : (Over Y)ᵒᵖ ⥤ AddCommGrpCat.{max u m} :=
  (overAffineAlgΓBase (terminalOver Y)).leftOp ⋙
    amitsurCoefficients.{u, u, m} (Γ((terminalOver Y).left, ⊤) : Type u) M ⋙
      forget₂ (ModuleCat.{max u m} (Γ((terminalOver Y).left, ⊤) : Type u)) AddCommGrpCat.{max u m}

/-- The restriction of the base-change presheaf to the slice at the terminal object is
isomorphic to the Amitsur coefficient presheaf. -/
def baseChangeAbelianRestrictionIso :
    (Over.forget (terminalOver Y)).op ⋙ baseChangeAbelianPresheaf Y M ≅
      amitsurSliceModulePresheaf (terminalOver Y) M ⋙
        forget₂ (ModuleCat.{max u m} (Γ((terminalOver Y).left, ⊤) : Type u))
          AddCommGrpCat.{max u m} :=
  Functor.isoWhiskerRight (NatIso.op (overForgetIsoIteratedSliceFunctor Y).symm)
    ((overAffineAlgΓBase (terminalOver Y)).leftOp ⋙
      amitsurCoefficients.{u, u, m} (Γ((terminalOver Y).left, ⊤) : Type u) M ⋙
        forget₂ (ModuleCat.{max u m} (Γ((terminalOver Y).left, ⊤) : Type u))
          AddCommGrpCat.{max u m})

/-- The base-change presheaf preserves finite products. -/
instance preservesFiniteProducts_baseChangeAbelianPresheaf :
    PreservesFiniteProducts (baseChangeAbelianPresheaf Y M) where
  preserves n := by
    have h : PreservesLimitsOfShape (Discrete (Fin n))
        (amitsurCoefficients.{u, u, m} (Γ((terminalOver Y).left, ⊤) : Type u) M) :=
      (preservesFiniteProducts_amitsurCoefficients.{u, m}
        (Γ((terminalOver Y).left, ⊤) : Type u) M).preserves n
    exact inferInstanceAs (PreservesLimitsOfShape (Discrete (Fin n))
      ((overAffineAlgΓBase (terminalOver Y)).leftOp ⋙
        amitsurCoefficients.{u, u, m} (Γ((terminalOver Y).left, ⊤) : Type u) M ⋙
          forget₂ (ModuleCat.{max u m} (Γ((terminalOver Y).left, ⊤) : Type u))
            AddCommGrpCat.{max u m}))

/-- Positive-degree Čech vanishing on a standard `τ`-covering of an affine scheme `Y`, with the
base-change presheaf of an `R`-module in an arbitrary universe as coefficients. -/
theorem isZero_cechCohomology_succ_baseChange (τ : CoveringTopology)
    (𝒱 : PreZeroHypercover.{max u m} (terminalOver Y))
    (h : IsStandardCovering τ (fun i ↦ (𝒱.X i).left) (fun i ↦ (𝒱.f i).left))
    (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology 𝒱 (baseChangeAbelianPresheaf Y M) p) :=
  isZero_cechCohomology_succ_of_amitsurRestriction (terminalOver Y) M τ
    (baseChangeAbelianPresheaf Y M) (baseChangeAbelianRestrictionIso Y M) 𝒱 h p hp

end BaseChange

end AlgebraicGeometry

end
