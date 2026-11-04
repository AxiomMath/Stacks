module

public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistGlue.Basic
public import StacksFrontier.AlgebraicGeometry.TwistRigidity.Determines
public import StacksFrontier.Topology.Sheaves.Glueing.OModuleMapGluing

/-!
# Uniqueness of a compatible isomorphism of glued twist algebras

Two isomorphisms of the glued graded algebras of two twist data on a relative projective spectrum
which both commute with the homogeneous-section maps are equal. Consequently
`Stacks.AlgebraicGeometry.RelativeProjTwists.IsUniqueTwistData` holds as soon as, for every two
twist data, one such isomorphism exists.

## Main results

* `Stacks.AlgebraicGeometry.TwistUnique.hom_ext_of_cover`: a morphism of sheaves of modules on a
  scheme is determined by its action on the sections over the opens inside the members of an open
  covering.
* `Stacks.AlgebraicGeometry.TwistUnique.app_eq_of_restrictFunctor_map_eq`: two morphisms with
  equal restrictions along an open immersion agree on the sections over every image open.
* `Stacks.AlgebraicGeometry.TwistUnique.image_preimage_eq_self`: an open inside the image of an
  open immersion is the image of its own preimage.
* `Stacks.AlgebraicGeometry.TwistUnique.app_eq_of_restrict_chart_eq`: equal restrictions along
  the chart of a relative Proj over an affine open force agreement over every open inside the
  inverse image of that affine open.
* `Stacks.AlgebraicGeometry.TwistUnique.hom_app_eq`: two isomorphisms of the glued graded
  algebras of two twist data which both commute with the homogeneous-section maps have the same
  homogeneous components.
* `Stacks.AlgebraicGeometry.TwistUnique.iso_eq`: such isomorphisms are equal.
* `Stacks.AlgebraicGeometry.TwistUnique.isUniqueTwistData_of_exists`: if for every two twist data
  there is an isomorphism of graded algebras commuting with the homogeneous-section maps, then
  there is exactly one.

## Implementation notes

The sections of the restriction of a module along an open immersion `f` over `V` are
definitionally the sections over `f ''ᵁ V`, but the two components live in `ModuleCat` over
`𝒪_X(V)` and over `𝒪_Y(f ''ᵁ V)`, which are different rings. So
`app_eq_of_restrictFunctor_map_eq` is stated on a section rather than on the component, and the
equation is moved from `f ''ᵁ (f ⁻¹ᵁ W)` to `W` by `app_eq_congr_open`.

The instance `Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart` applies to
`(relativeProj A).chart U hU` with the two arguments separate, not to `chart i.1 i.2` for
`i : S.affineOpens`, so the covering is indexed through
`Stacks.AlgebraicGeometry.RelativeProjTwistGlue.iSup_toBase_preimage_eq_top`, whose statement
mentions no chart.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.TwistUnique

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### Locality of morphisms of sheaves of modules on a scheme -/

section Generic

variable {X Y : Scheme.{u}}

/-- A morphism of sheaves of modules on a scheme is determined by its action on the sections over
the opens inside the members of an open covering. -/
public theorem hom_ext_of_cover {M N : X.Modules} {ι : Type u} {U : ι → X.Opens}
    (hU : ⨆ i, U i = ⊤) {φ φ' : M ⟶ N}
    (h : ∀ (i : ι) (V : X.Opens), V ≤ U i → ∀ s : M.val.obj (op V),
      φ.val.app (op V) s = φ'.val.app (op V) s) :
    φ = φ' :=
  SheafOfModules.hom_ext
    (TopCat.Sheaf.eq_hom_of_restrict hU N.isSheaf (fun _ V _ => φ.val.app (op V))
      (fun _ _ _ => rfl)
      (fun i V hV => (ModuleCat.hom_ext (LinearMap.ext (h i V hV))).symm))

/-- Agreement on the sections over an open transports along an equality of opens. -/
public theorem app_eq_congr_open {M N : X.Modules} {φ φ' : M ⟶ N} {W W' : X.Opens}
    (hW : W = W') (h : ∀ s : M.val.obj (op W), φ.val.app (op W) s = φ'.val.app (op W) s)
    (s : M.val.obj (op W')) : φ.val.app (op W') s = φ'.val.app (op W') s := by
  subst hW
  exact h s

/-- Two morphisms whose restrictions along an open immersion agree act in the same way on the
sections over every image open. -/
public theorem app_eq_of_restrictFunctor_map_eq (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} {φ φ' : M ⟶ N}
    (h : (Scheme.Modules.restrictFunctor f).map φ = (Scheme.Modules.restrictFunctor f).map φ')
    (V : X.Opens) (s : M.val.obj (op (f ''ᵁ V))) :
    φ.val.app (op (f ''ᵁ V)) s = φ'.val.app (op (f ''ᵁ V)) s :=
  congrArg
    (fun ρ : (Scheme.Modules.restrictFunctor f).obj M ⟶
        (Scheme.Modules.restrictFunctor f).obj N => ρ.val.app (op V) s) h

/-- An open inside the image of an open immersion is the image of its own preimage. -/
public theorem image_preimage_eq_self (f : X ⟶ Y) [IsOpenImmersion f] {W : Y.Opens}
    (hW : W ≤ f ''ᵁ ⊤) : f ''ᵁ (f ⁻¹ᵁ W) = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, ← Scheme.Hom.image_top_eq_opensRange]
  exact inf_eq_right.mpr hW

/-- Equal restrictions along an open immersion force agreement on the sections over every open
inside its image. -/
public theorem app_eq_of_restrictFunctor_map_eq_of_le (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} {φ φ' : M ⟶ N}
    (h : (Scheme.Modules.restrictFunctor f).map φ = (Scheme.Modules.restrictFunctor f).map φ')
    {W : Y.Opens} (hW : W ≤ f ''ᵁ ⊤) (s : M.val.obj (op W)) :
    φ.val.app (op W) s = φ'.val.app (op W) s :=
  app_eq_congr_open (image_preimage_eq_self f hW)
    (app_eq_of_restrictFunctor_map_eq f h (f ⁻¹ᵁ W)) s

end Generic

/-! ### The two uniqueness assertions of Tag 01NR -/

section Relative

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-- Equal restrictions along the chart over an affine open of the base force agreement on the
sections over every open inside the inverse image of that affine open. -/
public theorem app_eq_of_restrict_chart_eq (U : S.Opens) (hU : IsAffineOpen U)
    {M N : (relativeProj A).scheme.Modules} {φ φ' : M ⟶ N}
    (h : (Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map φ =
      (Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map φ')
    {W : (relativeProj A).scheme.Opens} (hW : W ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (s : M.val.obj (op W)) : φ.val.app (op W) s = φ'.val.app (op W) s :=
  app_eq_of_restrictFunctor_map_eq_of_le ((relativeProj A).chart U hU) h
    (hW.trans (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU).ge) s

/-- Two isomorphisms of the glued graded algebras of two twist data which both commute with the
homogeneous-section maps have equal restrictions along every chart over an affine open. -/
public theorem restrictFunctor_map_hom_app_eq (D E : TwistData A)
    (e₁ e₂ : D.algebra ≅ E.algebra)
    (h₁ : ∀ n : ℕ, D.ψ n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
      (e₁.hom.app (n : ℤ)) = E.ψ n)
    (h₂ : ∀ n : ℕ, D.ψ n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
      (e₂.hom.app (n : ℤ)) = E.ψ n)
    (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ) :
    (Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map (e₁.hom.app n) =
      (Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map (e₂.hom.app n) := by
  let := D.chartData.chart_isOpenImmersion U hU
  exact (Iso.cancel_iso_hom_right _ _ (E.chartData.chartIso U hU n)).mp
    ((TwistRigidity.determinesChartIso A D E e₁ h₁ U hU n).trans
      (TwistRigidity.determinesChartIso A D E e₂ h₂ U hU n).symm)

/-- Two isomorphisms of the glued graded algebras of two twist data which both commute with the
homogeneous-section maps have the same homogeneous components. -/
public theorem hom_app_eq (D E : TwistData A) (e₁ e₂ : D.algebra ≅ E.algebra)
    (h₁ : ∀ n : ℕ, D.ψ n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
      (e₁.hom.app (n : ℤ)) = E.ψ n)
    (h₂ : ∀ n : ℕ, D.ψ n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
      (e₂.hom.app (n : ℤ)) = E.ψ n)
    (n : ℤ) : e₁.hom.app n = e₂.hom.app n :=
  hom_ext_of_cover
    (RelativeProjTwistGlue.iSup_toBase_preimage_eq_top (relativeProj A))
    fun i _W hW s =>
      app_eq_of_restrict_chart_eq (i.1 : S.Opens) i.2
        (restrictFunctor_map_hom_app_eq D E e₁ e₂ h₁ h₂ (i.1 : S.Opens) i.2 n) hW s

/-- At most one isomorphism of the glued graded algebras of two twist data commutes with the
homogeneous-section maps. -/
public theorem iso_eq (D E : TwistData A) (e₁ e₂ : D.algebra ≅ E.algebra)
    (h₁ : ∀ n : ℕ, D.ψ n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
      (e₁.hom.app (n : ℤ)) = E.ψ n)
    (h₂ : ∀ n : ℕ, D.ψ n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
      (e₂.hom.app (n : ℤ)) = E.ψ n) : e₁ = e₂ :=
  Iso.ext (SheafOfModules.GradedAlgebra.Hom.ext (hom_app_eq D E e₁ e₂ h₁ h₂))

/-- If for every two twist data on a relative Proj there is an isomorphism of their glued graded
algebras commuting with the homogeneous-section maps, then there is exactly one. -/
public theorem isUniqueTwistData_of_exists (A : SheafGradedAlgebra S)
    (h : ∀ D E : TwistData A, ∃ e : D.algebra ≅ E.algebra,
      ∀ n : ℕ, D.ψ n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
        (e.hom.app (n : ℤ)) = E.ψ n) :
    IsUniqueTwistData A := fun D E =>
  let ⟨e, he⟩ := h D E
  ⟨e, he, fun e' he' => iso_eq D E e' e he' he⟩

end Relative

end Stacks.AlgebraicGeometry.TwistUnique

end
