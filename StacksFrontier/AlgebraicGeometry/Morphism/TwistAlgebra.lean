module

public import StacksFrontier.AlgebraicGeometry.Morphism.TwistMulProof
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedAlgebra
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The map `θ` of `ℤ`-graded algebras attached to a homomorphism of graded algebras

Let `ψ : A ⟶ B` be a homomorphism of quasi-coherent graded `𝒪_S`-algebras, with open
`U(ψ) ⊆ Proj_S(B)` and morphism `r_ψ : U(ψ) ⟶ Proj_S(A)` over `S`. This file defines the map of
`ℤ`-graded `𝒪_{U(ψ)}`-algebras

`θ : r_ψ^*(⨁_{d ∈ ℤ} 𝒪_{Proj_S(A)}(d)) ⟶ ⨁_{d ∈ ℤ} 𝒪_{U(ψ)}(d)`

and proves that the triple `(U(ψ), r_ψ, θ)` is characterised by agreeing, over every affine open
`W` of the base, with the triple attached to the induced homomorphism `Γ(W, A) ⟶ Γ(W, B)` of graded
rings.

Here `⨁_{d ∈ ℤ} 𝒪_{Proj_S(A)}(d)` is the glued graded algebra
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra A |>.algebra`, and the source
and target of `θ` are its inverse images `pullbackGradedAlgebra r_ψ (twistAlgebra A)` and
`pullbackGradedAlgebra ι (twistAlgebra B)` (`Stacks.RingedSpace.pullbackGradedAlgebra`).

## Main definitions

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra`: `⨁_{d ∈ ℤ} 𝒪(d)` on a relative `Proj`.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistAlgebraHom`: `θ`, as a homomorphism of
  sheaves of `ℤ`-graded algebras whose degreewise components are the maps `relativeTwistMap`.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.comparison_comp_mulSheaf_pullbackGradedAlgebra` and
  `mulSheaf_pullbackGradedAlgebra_eq_pbMul`: the product of a pulled-back graded algebra is the
  pulled-back product.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.mulSheaf_comp_relativeTwistMap`: the maps
  `relativeTwistMap` are multiplicative for the products of the two pulled-back graded algebras.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeProjMapTriple`: the triple `(U(ψ), r_ψ, θ)` and
  its affine-local characterisation.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NM](https://stacks.math.columbia.edu/tag/01NM)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.RingedSpace PresheafOfModules RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjMapCard
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.ProjTwistTheta
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.Tag07ZGTwist

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}}

/-! ### `⨁_d 𝒪(d)` on a relative `Proj` -/

/-- **`⨁_{d ∈ ℤ} 𝒪(d)` on the relative projective spectrum**, as a sheaf of `ℤ`-graded algebras:
the glued graded algebra whose homogeneous pieces are the relative twists
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwist`. -/
public abbrev twistAlgebra (A : SheafGradedAlgebra S) :=
  (GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra

/-! ### The product of a pulled-back graded algebra -/

variable {X Y : Scheme.{u}}

/-- The comparison `f^*A_i ⊗ f^*A_j ≅ f^*(A_i ⊗ A_j)` followed by the morphism-level product of
`f^*A` is the inverse image of the morphism-level product of `A`. -/
public theorem comparison_comp_mulSheaf_pullbackGradedAlgebra (f : X ⟶ Y)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y.toRingedSpace)) (i j : ℤ) :
    (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app
          (A.piece i, A.piece j) ≫
        SheafOfModules.GradedAlgebra.mulSheaf
          (Stacks.RingedSpace.pullbackGradedAlgebra f.toLRSHom.toShHom A) i j =
      (Scheme.Modules.pullback f).map (SheafOfModules.GradedAlgebra.mulSheaf A i j) := by
  refine pullbackTensor_hom_ext f.toLRSHom.toShHom (A.piece i) (A.piece j) _ _ fun V a b => ?_
  refine Eq.trans
    (congrArg
      (Hom.app (SheafOfModules.GradedAlgebra.mulSheaf
        (Stacks.RingedSpace.pullbackGradedAlgebra f.toLRSHom.toShHom A) i j).val
        (op ((opensMap f.toLRSHom.toShHom).obj V)))
      (comparison_pullbackUnit_tensorSheafUnit f.toLRSHom.toShHom
        (A.piece i) (A.piece j) V a b)) ?_
  refine Eq.trans
    (SheafOfModules.GradedAlgebra.mulSheaf_unit
      (Stacks.RingedSpace.pullbackGradedAlgebra f.toLRSHom.toShHom A) i j
      (op ((opensMap f.toLRSHom.toShHom).obj V))
      (pullbackUnit f.toLRSHom.toShHom (A.piece i) (op V) a)
      (pullbackUnit f.toLRSHom.toShHom (A.piece j) (op V) b)) ?_
  refine Eq.trans
    (Stacks.RingedSpace.pullbackGradedAlgebra_mul_pullbackUnit
      f.toLRSHom.toShHom A i j V a b) ?_
  refine Eq.trans
    (congrArg (pullbackUnit f.toLRSHom.toShHom (A.piece (i + j)) (op V))
      (SheafOfModules.GradedAlgebra.mulSheaf_unit A i j (op V) a b).symm) ?_
  exact (pullbackUnit_naturality f.toLRSHom.toShHom
    (SheafOfModules.GradedAlgebra.mulSheaf A i j) (op V)
    (Hom.app ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.RingedSpace.structureRingSheaf (Y.toRingedSpace))
        (𝟙 (Stacks.RingedSpace.structureRingSheaf (Y.toRingedSpace)).obj)).unit.app
      (PresheafOfModules.tensorObj (O := (Y.toRingedSpace).presheaf)
        ((A.piece i)).val ((A.piece j)).val)) (op V) (a ⊗ₜ b))).symm

/-- The product of `f^*A` is the inverse image of the product of `A`, in the form
`Stacks.AlgebraicGeometry.TwistMulLeg.pbMul` of the product of `A`. -/
public theorem mulSheaf_pullbackGradedAlgebra_eq_pbMul (f : X ⟶ Y)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y.toRingedSpace)) (i j : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf
        (Stacks.RingedSpace.pullbackGradedAlgebra f.toLRSHom.toShHom A) i j =
      TwistMulLeg.pbMul f (SheafOfModules.GradedAlgebra.mulSheaf A i j) :=
  (cancel_epi ((Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app
      (A.piece i, A.piece j))).mp
    ((comparison_comp_mulSheaf_pullbackGradedAlgebra f A i j).trans
      (TwistMulLeg.comparison_comp_pbMul f (SheafOfModules.GradedAlgebra.mulSheaf A i j)).symm)

/-! ### `θ` as a homomorphism of sheaves of graded algebras -/

variable {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)

/-- The maps `θ_n = relativeTwistMap ψ n` are multiplicative: the product of
`r_ψ^*(⨁_d 𝒪(d))` followed by `θ_{i+j}` is `θ_i ⊗ θ_j` followed by the product of
`ι^*(⨁_d 𝒪(d))`. -/
public theorem mulSheaf_comp_relativeTwistMap (i j : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf
          (Stacks.RingedSpace.pullbackGradedAlgebra
            (relativeMapHom ψ).toLRSHom.toShHom (twistAlgebra A)) i j ≫
        relativeTwistMap ψ (i + j) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((ψ.relativeMapDomain.toScheme.toRingedSpace)).presheaf,
            ((ψ.relativeMapDomain.toScheme.toRingedSpace)).IsSheaf⟩)).map
          (((relativeTwistMap ψ i), (relativeTwistMap ψ j)) : (_, _) ⟶ (_, _))) ≫
        SheafOfModules.GradedAlgebra.mulSheaf
          (Stacks.RingedSpace.pullbackGradedAlgebra
            ψ.relativeMapDomain.ι.toLRSHom.toShHom (twistAlgebra B)) i j := by
  refine Eq.trans (eq_whisker
    (mulSheaf_pullbackGradedAlgebra_eq_pbMul (relativeMapHom ψ) (twistAlgebra A) i j)
    (relativeTwistMap ψ (i + j))) ?_
  exact Eq.trans (relativeTwistMap_mul ψ i j)
    (whisker_eq _ (mulSheaf_pullbackGradedAlgebra_eq_pbMul ψ.relativeMapDomain.ι
      (twistAlgebra B) i j).symm)

/-- The map `θ : r_ψ^*(⨁_{d ∈ ℤ} 𝒪_{Proj_S(A)}(d)) ⟶ ⨁_{d ∈ ℤ} 𝒪_{U(ψ)}(d)`, a homomorphism of
sheaves of `ℤ`-graded algebras whose component in degree `n` is the comparison map `θ_n` of
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap`. -/
@[ega "II 3.5.6" "(3.5.6.2) for g = id_Y"]
public def relativeTwistAlgebraHom :
    SheafOfModules.GradedAlgebra.Hom
      (Stacks.RingedSpace.pullbackGradedAlgebra
        (relativeMapHom ψ).toLRSHom.toShHom (twistAlgebra A))
      (Stacks.RingedSpace.pullbackGradedAlgebra
        ψ.relativeMapDomain.ι.toLRSHom.toShHom (twistAlgebra B)) where
  app n := relativeTwistMap ψ n
  map_mul i j U x y :=
    (congrArg (Hom.app (relativeTwistMap ψ (i + j)).val U)
        (SheafOfModules.GradedAlgebra.mulSheaf_unit
          (Stacks.RingedSpace.pullbackGradedAlgebra
            (relativeMapHom ψ).toLRSHom.toShHom (twistAlgebra A)) i j U x y).symm).trans
      ((congrArg
          (fun φ => Hom.app (SheafOfModules.Hom.val φ) U
            (Hom.app ((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.RingedSpace.structureRingSheaf
                  (ψ.relativeMapDomain.toScheme.toRingedSpace))
                (𝟙 (Stacks.RingedSpace.structureRingSheaf
                  (ψ.relativeMapDomain.toScheme.toRingedSpace)).obj)).unit.app
              (PresheafOfModules.tensorObj
                (O := (ψ.relativeMapDomain.toScheme.toRingedSpace).presheaf)
                (((Scheme.Modules.pullback (relativeMapHom ψ)).obj (relativeTwist A i))).val
                (((Scheme.Modules.pullback (relativeMapHom ψ)).obj (relativeTwist A j))).val)) U
                (x ⊗ₜ y)))
          (mulSheaf_comp_relativeTwistMap ψ i j)).trans
        ((congrArg
            (Hom.app (SheafOfModules.GradedAlgebra.mulSheaf
              (Stacks.RingedSpace.pullbackGradedAlgebra
                ψ.relativeMapDomain.ι.toLRSHom.toShHom (twistAlgebra B)) i j).val U)
            (tensorSheaf_map_unit_tmul ψ.relativeMapDomain.toScheme.toRingedSpace
              (relativeTwistMap ψ i) (relativeTwistMap ψ j) U x y)).trans
          (SheafOfModules.GradedAlgebra.mulSheaf_unit
            (Stacks.RingedSpace.pullbackGradedAlgebra
              ψ.relativeMapDomain.ι.toLRSHom.toShHom (twistAlgebra B)) i j U
            (Hom.app (relativeTwistMap ψ i).val U x)
            (Hom.app (relativeTwistMap ψ j).val U y))))

/-- The degreewise components of `θ` are the comparison maps `θ_n`. -/
@[simp] public theorem relativeTwistAlgebraHom_app (n : ℤ) :
    (relativeTwistAlgebraHom ψ).app n = relativeTwistMap ψ n := rfl

/-! ### The triple `(U(ψ), r_ψ, θ)` -/

/-- Let `S` be a scheme, let `A` and `B` be quasi-coherent graded `𝒪_S`-algebras, set
`p : X = Proj_S(A) ⟶ S` and `q : Y = Proj_S(B) ⟶ S`, and let `ψ : A ⟶ B` be a homomorphism of
graded `𝒪_S`-algebras. There is a canonical open `U(ψ) ⊆ Y`, a canonical morphism of schemes
`r_ψ : U(ψ) ⟶ X` over `S`, and a map of `ℤ`-graded `𝒪_{U(ψ)}`-algebras

`θ = θ_ψ : r_ψ^*(⨁_{d ∈ ℤ} 𝒪_X(d)) ⟶ ⨁_{d ∈ ℤ} 𝒪_{U(ψ)}(d)`,

and the triple `(U(ψ), r_ψ, θ)` is characterised by the property that for every affine open
`W ⊆ S` the triple `(U(ψ) ∩ q⁻¹W, r_ψ|_{U(ψ) ∩ q⁻¹W}, θ|_{U(ψ) ∩ q⁻¹W})` is the triple attached
to `ψ : A(W) ⟶ B(W)`, via the identifications `p⁻¹W = Proj(A(W))` and `q⁻¹W = Proj(B(W))`.

The triple is `ψ.relativeMapDomain`, `relativeMapHom ψ` and `relativeTwistAlgebraHom ψ`, and the
seven conjuncts are, in order:

1. `r_ψ` is a morphism over `S`.
2. The inverse image of `U(ψ)` under the chart over an affine open `W` of the base is the open
   `mapDomain` of `ψ_W` in `Proj(B(W))`.
3. Under the canonical identification of `U(ψ) ∩ q⁻¹W` with `U(ψ_W)`, the restriction of `r_ψ` is
   the morphism `mapHom` of `ψ_W` followed by the chart of `X` over `W`.
4. In every degree `n`, the restriction of the `n`-th component of `θ` to the piece over `W` is
   `relativeTwistChart ψ n W`, the comparison map for `ψ_W` conjugated by the chart
   identifications.
5., 6., 7. Each of the three is determined by its affine-local description. -/
@[stacks 07ZG "the tag in one statement: the open U(ψ) of Proj_S(B), the morphism r_ψ : U(ψ) ⟶ \
  Proj_S(A) over S, and θ as a map of ℤ-graded 𝒪_{U(ψ)}-algebras, together with the \
  characterisation of all three over every affine open of the base by the triple Lemma 01MY \
  attaches to the induced homomorphism of graded rings of sections, and the uniqueness of each",
  ega "II 3.5.1" "partial",
  ega "II 8.12.4" "special case"]
public theorem relativeProjMapTriple :
    (relativeMapHom ψ ≫ (relativeProj A).toBase =
        ψ.relativeMapDomain.ι ≫ (relativeProj B).toBase) ∧
      (∀ (V : S.Opens) (hV : IsAffineOpen V),
        (relativeProj B).chart V hV ⁻¹ᵁ ψ.relativeMapDomain =
          mapDomain (A.grading V) (B.grading V) (ψ.sectionHom V)) ∧
      (∀ U : AffineOpen S,
        (chartPieceIso ψ U).hom ≫
            (relativeProj B).scheme.homOfLE
                (inf_le_left : ψ.relativeMapDomain ⊓ ((relativeProj B).toBase ⁻¹ᵁ U.1) ≤ _) ≫
              relativeMapHom ψ =
          mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) ≫
            (relativeProj A).chart U.1 U.2) ∧
      (∀ (n : ℤ) (U : S.affineOpens),
        (Scheme.Modules.pullback (pieceIncl ψ U)).map ((relativeTwistAlgebraHom ψ).app n) =
          relativeTwistChart ψ n U) ∧
      (∀ W : (relativeProj B).scheme.Opens,
        (∀ (V : S.Opens) (hV : IsAffineOpen V),
            (relativeProj B).chart V hV ⁻¹ᵁ W =
              mapDomain (A.grading V) (B.grading V) (ψ.sectionHom V)) →
          W = ψ.relativeMapDomain) ∧
      (∀ r : ψ.relativeMapDomain.toScheme ⟶ (relativeProj A).scheme,
        (∀ U : AffineOpen S,
            (((relativeProj B).chart U.1 U.2).isoImage
                  (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))).hom ≫
                (relativeProj B).scheme.homOfLE (chartImage_le ψ U) ≫ r =
              mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) ≫
                (relativeProj A).chart U.1 U.2) →
          r = relativeMapHom ψ) ∧
      (∀ (n : ℤ)
          (θ : (Scheme.Modules.pullback (relativeMapHom ψ)).obj (relativeTwist A n) ⟶
            (Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj (relativeTwist B n)),
        (∀ U : S.affineOpens,
            (Scheme.Modules.pullback (pieceIncl ψ U)).map θ = relativeTwistChart ψ n U) →
          θ = (relativeTwistAlgebraHom ψ).app n) :=
  ⟨relativeMapHom_comp_toBase ψ,
    fun V hV => ψ.chart_preimage_relativeMapDomain V hV,
    chartPieceIso_hom_comp_homOfLE_comp_relativeMapHom ψ,
    fun n U => relativeTwistMap_chart ψ n U,
    fun W hW => ψ.relativeMapDomain_unique W hW,
    fun r hr => relativeMapHom_unique ψ r hr,
    fun n _ hθ => relativeTwistMap_unique ψ n hθ (relativeTwistMap_chart ψ n)⟩

end Stacks.AlgebraicGeometry.Tag07ZGTwist

end
