module

public import StacksFrontier.AlgebraicGeometry.ProjMapCard.Multiplication
public import StacksFrontier.AlgebraicGeometry.TwistDataConstruction.Absolute
public import StacksFrontier.AlgebraicGeometry.TwistTensor.RelativeLaurentComparison

/-!
# The comparison on twists as one homomorphism of sheaves of graded algebras

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings, `U(ψ) ⊆ Proj ℬ` its domain of
definition and `r_ψ : U(ψ) ⟶ Proj 𝒜` the induced morphism. The comparison maps on the integer
twists are a family `θ n : r_ψ^*𝒪_{Proj 𝒜}(n) ⟶ ι^*𝒪_{Proj ℬ}(n)` indexed by `n : ℤ`
(`Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap`), and their compatibility with the
multiplication maps `𝒪(n) ⊗ 𝒪(m) → 𝒪(n + m)` is
`Stacks.AlgebraicGeometry.ProjMapCard.twistMap_comp_pullbackTwistMultiplication`, an equation
between morphisms out of a tensor product sheaf, one pair of degrees at a time. This file assembles
the family into a single morphism
`θ : r_ψ^*(⨁_{n ∈ ℤ} 𝒪_{Proj 𝒜}(n)) ⟶ ⨁_{n ∈ ℤ} 𝒪_{Proj ℬ}(n)|_{U(ψ)}` of sheaves of `ℤ`-graded
algebras ([Stacks, Tag 01MY], [Stacks, Tag 02NC]).

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistGradedAlgebra.pullbackTwistAlgebra`: the sheaf of
  `ℤ`-graded algebras `f^*(⨁_{n ∈ ℤ} 𝒪_{Proj 𝒜}(n))` on a scheme over `Proj 𝒜`, as the
  stalkwise pullback (Tag 01CD) of the graded algebra of all integer twists.
* `Stacks.AlgebraicGeometry.ProjTwistGradedAlgebra.thetaGraded`: the comparison maps on all
  integer twists, as one homomorphism of sheaves of `ℤ`-graded algebras.
* `SheafOfModules.GradedAlgebra.isoOfIsIsoApp`: a homomorphism of sheaves of graded algebras
  whose every homogeneous component is an isomorphism is an isomorphism.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistGradedAlgebra.mulSheaf_twistAlgebra`: the morphism-level
  multiplication of the graded algebra of integer twists is the canonical multiplication map of
  Tag 01MO.
* `Stacks.AlgebraicGeometry.ProjTwistGradedAlgebra.mulSheaf_pullbackTwistAlgebra`: the same for
  the pullback, where it is `Stacks.AlgebraicGeometry.ProjTwistTheta.pullbackTwistMultiplication`.
* `Stacks.AlgebraicGeometry.ProjTwistGradedAlgebra.mulSheaf_comp_twistMap`: the comparison maps
  on the twists intertwine the multiplications of the two pulled-back graded algebras.

## References

* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.RingedSpace PresheafOfModules RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare Stacks.AlgebraicGeometry.ProjTwistTheta
open Stacks.AlgebraicGeometry.ProjMapCard Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.AlgebraicGeometry.TwistDataConstruction
open Stacks.AlgebraicGeometry.RelativeProjTwists
open scoped TensorProduct

universe t a v u

/-! ### Isomorphisms of sheaves of graded algebras from their components -/

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : GradedAlgebra.{t, t} R}

/-- If a degreewise family of isomorphisms of sheaves of graded algebras preserves products of
homogeneous local sections, then so does its inverse family. -/
theorem inv_map_mul_of_pieces (e : ∀ n : ℤ, A.piece n ≅ B.piece n)
    (hhom : ∀ (i j : ℤ) (U : Cᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
      ((e (i + j)).hom.val.app U) ((A.mul i j).app U x y) =
        (B.mul i j).app U (((e i).hom.val.app U) x) (((e j).hom.val.app U) y))
    (i j : ℤ) (U : Cᵒᵖ) (x : (B.piece i).val.obj U) (y : (B.piece j).val.obj U) :
    ((e (i + j)).inv.val.app U) ((B.mul i j).app U x y) =
      (A.mul i j).app U (((e i).inv.val.app U) x) (((e j).inv.val.app U) y) := by
  have hx : ((e i).hom.val.app U) (((e i).inv.val.app U) x) = x :=
    Stacks.SheafOfModules.hom_val_app_inv_val_app (e i) U x
  have hy : ((e j).hom.val.app U) (((e j).inv.val.app U) y) = y :=
    Stacks.SheafOfModules.hom_val_app_inv_val_app (e j) U y
  have key : (B.mul i j).app U x y =
      ((e (i + j)).hom.val.app U) ((A.mul i j).app U
        (((e i).inv.val.app U) x) (((e j).inv.val.app U) y)) :=
    ((hhom i j U (((e i).inv.val.app U) x) (((e j).inv.val.app U) y)).trans
      (congrArg₂ (fun p q => (B.mul i j).app U p q) hx hy)).symm
  exact Eq.trans (congrArg (fun z => ((e (i + j)).inv.val.app U) z) key)
    (Stacks.SheafOfModules.inv_val_app_hom_val_app (e (i + j)) U
      ((A.mul i j).app U (((e i).inv.val.app U) x) (((e j).inv.val.app U) y)))

/-- The isomorphism of sheaves of graded algebras given by a degreewise family of isomorphisms
preserving products of homogeneous local sections. -/
def isoOfPieces (e : ∀ n : ℤ, A.piece n ≅ B.piece n)
    (hhom : ∀ (i j : ℤ) (U : Cᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
      ((e (i + j)).hom.val.app U) ((A.mul i j).app U x y) =
        (B.mul i j).app U (((e i).hom.val.app U) x) (((e j).hom.val.app U) y)) :
    A ≅ B :=
  Stacks.AlgebraicGeometry.GradedVeronese.isoOfPiecesOfHoms e hhom
    (inv_map_mul_of_pieces e hhom)

/-- A homomorphism of sheaves of graded algebras whose every homogeneous component is an
isomorphism, as an isomorphism. -/
def isoOfIsIsoApp (f : A ⟶ B) (h : ∀ n : ℤ, IsIso (f.app n)) : A ≅ B :=
  isoOfPieces (fun n => @asIso _ _ _ _ (f.app n) (h n)) f.map_mul

/-- The degree-`n` component of `isoOfIsIsoApp f h` is the degree-`n` component of `f`. -/
@[simp] theorem isoOfIsIsoApp_hom_app (f : A ⟶ B) (h : ∀ n : ℤ, IsIso (f.app n)) (n : ℤ) :
    (isoOfIsIsoApp f h).hom.app n = f.app n := rfl

end SheafOfModules.GradedAlgebra

namespace Stacks.AlgebraicGeometry.ProjTwistGradedAlgebra

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-! ### The graded algebra of integer twists, and its pullback -/

section One

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The morphism-level multiplication of `⨁_{n ∈ ℤ} 𝒪_{Proj 𝒜}(n)` is the canonical
multiplication map of Tag 01MO. -/
theorem mulSheaf_twistAlgebra (i j : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf (twistAlgebra 𝒜) i j = twistMultiplicationMap 𝒜 i j :=
  Stacks.PullbackTensorCoherence.tensor_hom_ext fun U x y =>
    (SheafOfModules.GradedAlgebra.mulSheaf_unit (twistAlgebra 𝒜) i j U x y).trans
      (twistAlgebra_mul_app 𝒜 i j x y)

/-- The sheaf of `ℤ`-graded algebras `f^*(⨁_{n ∈ ℤ} 𝒪_{Proj 𝒜}(n))`, for a morphism of
schemes `f : W ⟶ Proj 𝒜`: the stalkwise pullback of Tag 01CD applied to the graded algebra of
all integer twists. Its degree-`n` piece is `f^*𝒪_{Proj 𝒜}(n)`. -/
def pullbackTwistAlgebra {W : Scheme.{u}} (f : W ⟶ AlgebraicGeometry.Proj 𝒜) :
    SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf W.toRingedSpace) :=
  pullbackGradedAlgebra f.toLRSHom.toShHom (twistAlgebra 𝒜)

/-- The degree-`n` piece of `pullbackTwistAlgebra 𝒜 f` is `f^*𝒪_{Proj 𝒜}(n)`. -/
theorem pullbackTwistAlgebra_piece {W : Scheme.{u}} (f : W ⟶ AlgebraicGeometry.Proj 𝒜) (n : ℤ) :
    (pullbackTwistAlgebra 𝒜 f).piece n =
      (Scheme.Modules.pullback f).obj (twistingSheaf 𝒜 n) := rfl

/-- The morphism-level multiplication of `f^*(⨁_{n ∈ ℤ} 𝒪(n))` is
`Stacks.AlgebraicGeometry.ProjTwistTheta.pullbackTwistMultiplication`, the canonical
multiplication map of Tag 01MO pulled back and conjugated by the comparison of Tag 01CD. -/
theorem mulSheaf_pullbackTwistAlgebra {W : Scheme.{u}} (f : W ⟶ AlgebraicGeometry.Proj 𝒜)
    (i j : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf (pullbackTwistAlgebra 𝒜 f) i j =
      pullbackTwistMultiplication 𝒜 f i j := by
  refine (mulSheaf_pullbackGradedAlgebra f.toLRSHom.toShHom _ i j).trans ?_
  refine Eq.trans (congrArg₂ (fun p q => p ≫ (pullbackFunctor f.toLRSHom.toShHom).map q)
    (IsIso.inv_eq_of_hom_inv_id
      ((Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom_inv_id_app
        (twistingSheaf 𝒜 i, twistingSheaf 𝒜 j)))
    (mulSheaf_twistAlgebra 𝒜 i j)) ?_
  rfl

end One

/-! ### The comparison as one homomorphism of sheaves of graded algebras -/

section Two

variable {A B : Type u} {σ : Type u} {τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- The comparison maps on the twists intertwine the morphism-level multiplications of the two
pulled-back graded algebras of integer twists. -/
theorem mulSheaf_comp_twistMap (ψ : 𝒜 →+*ᵍ ℬ) (i j : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf (pullbackTwistAlgebra 𝒜 (mapHom 𝒜 ℬ ψ)) i j ≫
        twistMap 𝒜 ℬ ψ (i + j) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(((mapDomain 𝒜 ℬ ψ).toScheme.toRingedSpace)).presheaf,
            (((mapDomain 𝒜 ℬ ψ).toScheme.toRingedSpace)).IsSheaf⟩)).map
          (((twistMap 𝒜 ℬ ψ i), (twistMap 𝒜 ℬ ψ j)) : (_, _) ⟶ (_, _))) ≫
        SheafOfModules.GradedAlgebra.mulSheaf
          (pullbackTwistAlgebra ℬ (mapDomain 𝒜 ℬ ψ).ι) i j := by
  refine Eq.trans (eq_whisker (mulSheaf_pullbackTwistAlgebra 𝒜 (mapHom 𝒜 ℬ ψ) i j)
    (twistMap 𝒜 ℬ ψ (i + j))) ?_
  exact Eq.trans (twistMap_comp_pullbackTwistMultiplication 𝒜 ℬ ψ i j)
    (whisker_eq _ (mulSheaf_pullbackTwistAlgebra ℬ (mapDomain 𝒜 ℬ ψ).ι i j).symm)

/-- The comparison maps on all integer twists, as one homomorphism of sheaves of `ℤ`-graded
algebras
`θ : r_ψ^*(⨁_{n ∈ ℤ} 𝒪_{Proj 𝒜}(n)) ⟶ ⨁_{n ∈ ℤ} 𝒪_{Proj ℬ}(n)|_{U(ψ)}`.
Its degree-`n` component is `Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap`. -/
@[stacks 01MY "theta as a single morphism of sheaves of Z-graded algebras: the comparison maps \
on all integer twists, assembled into one morphism from the pullback along r_psi of the graded \
algebra of integer twists of Proj A to the pullback along the inclusion of U(psi) of that of \
Proj B"]
def thetaGraded (ψ : 𝒜 →+*ᵍ ℬ) :
    pullbackTwistAlgebra 𝒜 (mapHom 𝒜 ℬ ψ) ⟶
      pullbackTwistAlgebra ℬ (mapDomain 𝒜 ℬ ψ).ι where
  app n := twistMap 𝒜 ℬ ψ n
  map_mul i j U x y := by
    refine Eq.trans (congrArg (Hom.app (twistMap 𝒜 ℬ ψ (i + j)).val U)
      (SheafOfModules.GradedAlgebra.mulSheaf_unit
        (pullbackTwistAlgebra 𝒜 (mapHom 𝒜 ℬ ψ)) i j U x y).symm) ?_
    refine Eq.trans (congrArg (fun φ => Hom.app (SheafOfModules.Hom.val φ) U
      ((tensorSheafUnit ((pullbackTwistAlgebra 𝒜 (mapHom 𝒜 ℬ ψ)).piece i)
        ((pullbackTwistAlgebra 𝒜 (mapHom 𝒜 ℬ ψ)).piece j)).app U (x ⊗ₜ y)))
      (mulSheaf_comp_twistMap 𝒜 ℬ ψ i j)) ?_
    refine Eq.trans (congrArg (Hom.app (SheafOfModules.GradedAlgebra.mulSheaf
      (pullbackTwistAlgebra ℬ (mapDomain 𝒜 ℬ ψ).ι) i j).val U)
      (Stacks.RingedSpace.tensorSheaf_map_unit_tmul
        (mapDomain 𝒜 ℬ ψ).toScheme.toRingedSpace (twistMap 𝒜 ℬ ψ i) (twistMap 𝒜 ℬ ψ j)
        U x y)) ?_
    exact SheafOfModules.GradedAlgebra.mulSheaf_unit
      (pullbackTwistAlgebra ℬ (mapDomain 𝒜 ℬ ψ).ι) i j U _ _

/-- The degree-`n` component of `thetaGraded 𝒜 ℬ ψ` is `twistMap 𝒜 ℬ ψ n`. -/
theorem thetaGraded_app (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ) :
    (thetaGraded 𝒜 ℬ ψ).app n = twistMap 𝒜 ℬ ψ n := rfl

/-- The homomorphism `θ` as an isomorphism of sheaves of `ℤ`-graded algebras, when every `θ_n` is
an isomorphism of sheaves of modules. -/
def thetaGradedIso (ψ : 𝒜 →+*ᵍ ℬ) (h : ∀ n : ℤ, IsIso (twistMap 𝒜 ℬ ψ n)) :
    pullbackTwistAlgebra 𝒜 (mapHom 𝒜 ℬ ψ) ≅
      pullbackTwistAlgebra ℬ (mapDomain 𝒜 ℬ ψ).ι :=
  SheafOfModules.GradedAlgebra.isoOfIsIsoApp (thetaGraded 𝒜 ℬ ψ) h

/-- The degree-`n` component of `thetaGradedIso 𝒜 ℬ ψ h` is `twistMap 𝒜 ℬ ψ n`. -/
theorem thetaGradedIso_hom_app (ψ : 𝒜 →+*ᵍ ℬ) (h : ∀ n : ℤ, IsIso (twistMap 𝒜 ℬ ψ n)) (n : ℤ) :
    (thetaGradedIso 𝒜 ℬ ψ h).hom.app n = twistMap 𝒜 ℬ ψ n := rfl

end Two

end Stacks.AlgebraicGeometry.ProjTwistGradedAlgebra

end
