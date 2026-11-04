module

public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Pullback
public import StacksFrontier.AlgebraicGeometry.Morphism.TwistGlue

/-!
# The maps on twists induced by a homomorphism of graded algebras

Let `ψ : A ⟶ B` be a homomorphism of quasi-coherent graded `𝒪_S`-algebras, let `U(ψ)` be the open
of `Proj_S(B)` on which it induces a morphism and let `r_ψ : U(ψ) ⟶ Proj_S(A)` be that morphism.
For every `n : ℤ` there is a unique map

`θ_n : r_ψ^* 𝒪_{Proj_S(A)}(n) ⟶ 𝒪_{Proj_S(B)}(n)|_{U(ψ)}`

whose restriction to the piece of `U(ψ)` over each affine open `U` of the base is the absolute
comparison map of Tag 01MY for `ψ_U`, conjugated by the chart identifications of Tag 01NR.

## Main definitions

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap`: the map `θ_n`.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.iSup_image_pieceIncl_eq_top`: the pieces of `U(ψ)`, read
  as the images of their inclusions, cover `U(ψ)`.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.image_pieceIncl_inf_le_iSup`: the overlap of two pieces is
  covered by the pieces over the affine opens of the base refining the intersection.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.localApp_relativeTwistChart_nested` and
  `Stacks.AlgebraicGeometry.Tag07ZGTwist.localApp_relativeTwistChart_eq`: the affine-local
  comparison maps agree over a nested pair of affine opens, and wherever two pieces of `U(ψ)` see
  a common open subset of it.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.existsUnique_relativeTwistMap`: there is a unique map on
  the `n`-th twists restricting to each affine-local comparison map.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap_chart`: the inverse image of `θ_n` along
  the inclusion of the piece of `U(ψ)` over an affine open `U` of the base is the affine-local
  comparison map over `U`.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ModuleHomGlue
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism

namespace Stacks.AlgebraicGeometry.Tag07ZGTwist

universe u

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)

/-! ### The pieces as a cover of `U(ψ)` -/

/-- The image of the inclusion of the piece over `U` is the part of `U(ψ)` lying over the chart. -/
private theorem image_pieceIncl_top (U : AffineOpen S) :
    pieceIncl ψ U ''ᵁ (⊤ : (chartImage ψ U).toScheme.Opens) =
      ψ.relativeMapDomain.ι ⁻¹ᵁ chartImage ψ U :=
  Tag07ZGTwistLocality.image_top_homOfLE_chartImage_le ψ U

/-- The pieces of `U(ψ)`, read as the images of their inclusions, cover `U(ψ)`. -/
public theorem iSup_image_pieceIncl_eq_top :
    (⨆ U : AffineOpen S, pieceIncl ψ U ''ᵁ (⊤ : (chartImage ψ U).toScheme.Opens)) = ⊤ :=
  (iSup_congr (image_pieceIncl_top ψ)).trans
    (Tag07ZGTwistLocality.iSup_preimage_chartImage_eq_top ψ)

/-- The overlap of two pieces of `U(ψ)` is covered by the pieces over the affine opens of the
base refining the intersection. -/
public theorem image_pieceIncl_inf_le_iSup (T U : AffineOpen S) :
    pieceIncl ψ T ''ᵁ (⊤ : (chartImage ψ T).toScheme.Opens) ⊓
        pieceIncl ψ U ''ᵁ (⊤ : (chartImage ψ U).toScheme.Opens) ≤
      ⨆ W : {W : AffineOpen S // W.1 ≤ T.1 ⊓ U.1},
        pieceIncl ψ W.1 ''ᵁ (⊤ : (chartImage ψ W.1).toScheme.Opens) := by
  intro x hx
  rw [image_pieceIncl_top, image_pieceIncl_top] at hx
  have hx' : (x.1 : (relativeProj B).scheme) ∈ chartImage ψ T ⊓ chartImage ψ U := hx
  rw [chartImage_inf_eq_iSup ψ T U] at hx'
  obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨W, (image_pieceIncl_top ψ W.1).symm ▸ hW⟩

/-! ### The local data glue -/

/-- The affine-local comparison maps, read on sections over an open of `U(ψ)`, agree over a
nested pair `U ≤ T` of affine opens of the base. -/
public theorem localApp_relativeTwistChart_nested (n : ℤ) (T U : AffineOpen S) (h : U.1 ≤ T.1)
    (V : ψ.relativeMapDomain.toScheme.Opens) (W₁ : (chartImage ψ T).toScheme.Opens)
    (W₂ : (chartImage ψ U).toScheme.Opens) (h₁ : pieceIncl ψ T ''ᵁ W₁ = V)
    (h₂ : pieceIncl ψ U ''ᵁ W₂ = V) :
    localApp (pieceIncl ψ T) (ofPullback (pieceIncl ψ T) (relativeTwistChart ψ n T)) h₁ =
      localApp (pieceIncl ψ U) (ofPullback (pieceIncl ψ U) (relativeTwistChart ψ n U)) h₂ :=
  localApp_ofPullback_eq (pieceIncl ψ T)
    ((relativeProj B).scheme.homOfLE (chartImage_mono ψ h)) (homOfLE_comp_pieceIncl ψ h)
    (relativeTwistChart ψ n T) (relativeTwistChart ψ n U)
    (relativeTwistChart_nested ψ n U T h
      ((relativeProj B).scheme.homOfLE (chartImage_mono ψ h)) (homOfLE_comp_pieceIncl ψ h)) h₁ h₂

/-- The affine-local comparison maps, read on sections, agree wherever two pieces of `U(ψ)` see
the same open subset of it. -/
public theorem localApp_relativeTwistChart_eq (n : ℤ) (T U : AffineOpen S)
    (W₁ : (chartImage ψ T).toScheme.Opens) (W₂ : (chartImage ψ U).toScheme.Opens)
    (V : ψ.relativeMapDomain.toScheme.Opens) (h₁ : pieceIncl ψ T ''ᵁ W₁ = V)
    (h₂ : pieceIncl ψ U ''ᵁ W₂ = V) :
    localApp (pieceIncl ψ T) (ofPullback (pieceIncl ψ T) (relativeTwistChart ψ n T)) h₁ =
      localApp (pieceIncl ψ U) (ofPullback (pieceIncl ψ U) (relativeTwistChart ψ n U)) h₂ :=
  localApp_eq_of_refine (fun U : AffineOpen S => pieceIncl ψ U)
    (fun U => ofPullback (pieceIncl ψ U) (relativeTwistChart ψ n U))
    (κ := fun T U => {W : AffineOpen S // W.1 ≤ T.1 ⊓ U.1})
    (fun _ _ W => W.1) (fun T U => U.1 ≤ T.1)
    (fun _ _ W => W.2.trans inf_le_left) (fun _ _ W => W.2.trans inf_le_right)
    (image_pieceIncl_inf_le_iSup ψ) (localApp_relativeTwistChart_nested ψ n)
    T U W₁ W₂ V h₁ h₂

/-- There is a unique map on the `n`-th twists whose restriction to the piece of `U(ψ)` over every
affine open `U` of the base is the affine-local comparison map over `U`. -/
public theorem existsUnique_relativeTwistMap (n : ℤ) :
    ∃! θ : (Scheme.Modules.pullback (relativeMapHom ψ)).obj (relativeTwist A n) ⟶
        (Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj (relativeTwist B n),
      ∀ U : AffineOpen S, (Scheme.Modules.restrictFunctor (pieceIncl ψ U)).map θ =
        ofPullback (pieceIncl ψ U) (relativeTwistChart ψ n U) :=
  existsUnique_hom_of_restrict_cover (fun U : AffineOpen S => pieceIncl ψ U)
    (iSup_image_pieceIncl_eq_top ψ)
    (fun U => ofPullback (pieceIncl ψ U) (relativeTwistChart ψ n U))
    (localApp_relativeTwistChart_eq ψ n)

/-! ### The map on twists -/

/-- The map `θ_n : r_ψ^* 𝒪_{Proj_S(A)}(n) ⟶ 𝒪_{Proj_S(B)}(n)|_{U(ψ)}` on the `n`-th twists
induced by a homomorphism `ψ : A ⟶ B` of quasi-coherent graded `𝒪_S`-algebras: the unique
morphism whose inverse image along the inclusion of the piece of `U(ψ)` over every affine open `U`
of the base is Tag 01MY's comparison map for the induced homomorphism `Γ(U, A) ⟶ Γ(U, B)`,
conjugated by the chart identifications of Tag 01NR. -/
public def relativeTwistMap (n : ℤ) :
    (Scheme.Modules.pullback (relativeMapHom ψ)).obj (relativeTwist A n) ⟶
      (Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj (relativeTwist B n) :=
  (existsUnique_relativeTwistMap ψ n).exists.choose

/-- The restriction of `θ_n` to the piece over an affine open `U` of the base is the affine-local
comparison map, read through `Stacks.AlgebraicGeometry.ModuleHomGlue.ofPullback`. -/
public theorem restrictFunctor_map_relativeTwistMap (n : ℤ) (U : AffineOpen S) :
    (Scheme.Modules.restrictFunctor (pieceIncl ψ U)).map (relativeTwistMap ψ n) =
      ofPullback (pieceIncl ψ U) (relativeTwistChart ψ n U) :=
  (existsUnique_relativeTwistMap ψ n).exists.choose_spec U

/-- Over the piece of `U(ψ)` over an affine open `U` of the base, `θ_n` is the affine-local
comparison map `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistChart`: Tag 01MY's `θ` for the
induced homomorphism `Γ(U, A) ⟶ Γ(U, B)` of graded rings of sections, conjugated by the
identifications of the source and the target with the inverse images of the two absolute
twists. -/
public theorem relativeTwistMap_chart (n : ℤ) (U : S.affineOpens) :
    (Scheme.Modules.pullback (pieceIncl ψ U)).map (relativeTwistMap ψ n) =
      relativeTwistChart ψ n U :=
  pullback_map_eq_of_restrictFunctor_map_eq (pieceIncl ψ U) (relativeTwistMap ψ n)
    (relativeTwistChart ψ n U) (restrictFunctor_map_relativeTwistMap ψ n U)

end Stacks.AlgebraicGeometry.Tag07ZGTwist

end
