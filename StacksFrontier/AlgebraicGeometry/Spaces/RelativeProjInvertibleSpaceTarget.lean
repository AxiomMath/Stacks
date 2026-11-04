module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceModule
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PointComparisonPullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationSchemeDescent

/-!
# The tensor powers of an invertible module on an algebraic space at its scheme points

Let `ℒ` be an invertible `𝒪_X`-module on the small étale site of an algebraic space `X`, and
`x : T ⟶ X` a scheme point.  The restriction `x^*ℒ` of `ℒ` to the scheme `T`
(`AlgebraicGeometry.Space.pointLine`) is an invertible `𝒪_T`-module, and the Zariski reading of
the inverse image of `⨁_n ℒ^{⊗ n}` along `x` is the Laurent algebra `⨁_n (x^*ℒ)^{⊗ n}`
(`AlgebraicGeometry.Space.pointLaurentHom`).  This file reads the identification back on the small
étale site of `T`: **the inverse image `x^*(ℒ^{⊗ n})` of the `n`-th tensor power along `x`, as an
`𝒪`-module on the represented algebraic space of `T`, is the module attached by Stacks 03DX (2) to
`(x^*ℒ)^{⊗ n}`**, and this identification is **natural in the scheme point**: along a morphism
`τ : T' ⟶ T` of test schemes it carries the composition comparison
`τ^*(x^*ℒ^{⊗ n}) ≅ (x ∘ τ)^*ℒ^{⊗ n}` of Stacks 03LU to the comparison of tensor powers
`τ^*((x^*ℒ)^{⊗ n}) ≅ (τ^*(x^*ℒ))^{⊗ n}` followed by the tensor power of the identification
`τ^*(x^*ℒ) ≅ (x ∘ τ)^*ℒ` (`AlgebraicGeometry.Space.pointLineIso`).

This is the identification of the target `⨁_d ℒ^{⊗ d}|_{U(ψ)}` of the map `θ` of Stacks 0D2Z on
the scheme points of `U(ψ)`.

## Main definitions

* `AlgebraicGeometry.Space.pointLaurentPieceQcoh`: `(x^*ℒ)^{⊗ n}`, as a quasi-coherent module on
  `T`.
* `AlgebraicGeometry.Space.pointTargetIso`: **`x^*(ℒ^{⊗ n}) ≅ ((x^*ℒ)^{⊗ n})^a`**.

## Main results

* `AlgebraicGeometry.Space.pointTargetIso_naturality`: **the identification is natural in the
  scheme point.**

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace AlgebraicGeometry.Space

/-- The abstract shape of `AlgebraicGeometry.Space.pointTargetIso_naturality`, at variables: a
composite of four morphisms rewritten by a naturality square, a square of the target functor and
a reading of the source. -/
theorem comp_comp_comp_eq_of_squares {D : Type*} [Category D] {a b c d e g h a' : D}
    (z : a ⟶ b) (l : b ⟶ c) (c₃ : c ⟶ d) (t : d ⟶ h) (c₃' : b ⟶ e) (q : e ⟶ d) (p : e ⟶ g)
    (l' : g ⟶ h) (κ : a ⟶ a') (z' : a' ⟶ g) (h₁ : l ≫ c₃ = c₃' ≫ q) (h₂ : q ≫ t = p ≫ l')
    (h₃ : z ≫ c₃' ≫ p = κ ≫ z') :
    z ≫ l ≫ c₃ ≫ t = κ ≫ z' ≫ l' := by
  rw [reassoc_of% h₁, h₂, ← reassoc_of% h₃]

/-- The image of a commutative square of morphisms of quasi-coherent modules under a functor,
read on underlying morphisms. -/
theorem hom_map_comp_hom_map_eq {C : Type*} [Category C] {D : Type*} [Category D]
    {Q : ObjectProperty D} (F : C ⥤ Q.FullSubcategory) {a b c b' : C} (f : a ⟶ b) (g : b ⟶ c)
    (f' : a ⟶ b') (g' : b' ⟶ c) (h : f ≫ g = f' ≫ g') :
    (F.map f).hom ≫ (F.map g).hom = (F.map f').hom ≫ (F.map g').hom := by
  rw [← ObjectProperty.FullSubcategory.comp_hom, ← F.map_comp, h, F.map_comp,
    ObjectProperty.FullSubcategory.comp_hom]

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (L : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))
  [hL : Stacks.SheafOfModules.IsInvertible (smallEtaleRingedTopos B S hS X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L]

/-- The Zariski reading on `T` of the inverse image of `ℒ^{⊗ n}` along a scheme point
`x : T ⟶ X`, as a quasi-coherent module on `T`. -/
abbrev pointLaurentReadingQcoh (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) (n : ℤ) :
    (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf).FullSubcategory :=
  zariskiReadingQcoh T ((etalePointAlgebra (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos B S hS X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L)
        T x).piece n)
    (isQuasicoherentOnSite_etalePointAlgebra_piece (Stacks.SheafOfModules.TensorPower.laurentAlgebra
          (smallEtaleRingedTopos B S hS X).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L)
      (isQuasicoherentOnSite_laurentAlgebra_piece_of_isInvertible L) x n)

/-- **`(x^*ℒ)^{⊗ n}`, as a quasi-coherent module on the scheme `T`** of a scheme point
`x : T ⟶ X`: the degree-`n` piece of the Laurent algebra of the restriction `x^*ℒ`, which is
quasi-coherent as the image of the Zariski reading of `x^*(ℒ^{⊗ n})` under
`AlgebraicGeometry.Space.pointLaurentHom`. -/
def pointLaurentPieceQcoh (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) (n : ℤ) :
    (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf).FullSubcategory :=
  ⟨(laurent (pointLine B S hS L T x)).piece n,
    (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf).prop_of_iso
      (@asIso _ _ _ _ ((pointLaurentHom B S hS L T x).app n)
        (isIso_pointLaurentHom_app B S hS L T x n)) (pointLaurentReadingQcoh L T x n).property⟩

/-- The identification of the Zariski reading of `x^*(ℒ^{⊗ n})` with `(x^*ℒ)^{⊗ n}`, as
quasi-coherent modules on `T`. -/
def pointLaurentReadingIso (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) (n : ℤ) :
    pointLaurentReadingQcoh L T x n ≅ pointLaurentPieceQcoh L T x n :=
  ObjectProperty.isoMk _ (@asIso _ _ _ _ ((pointLaurentHom B S hS L T x).app n)
        (isIso_pointLaurentHom_app B S hS L T x n))

/-- **The inverse image of `ℒ^{⊗ n}` along a scheme point is the module attached to
`(x^*ℒ)^{⊗ n}`**: for a scheme point `x : T ⟶ X`, the identification
`x^*(ℒ^{⊗ n}) ≅ ((x^*ℒ)^{⊗ n})^a` of `𝒪`-modules on the represented algebraic space of `T`, the
identification of a quasi-coherent module with the module attached to its Zariski reading
(`AlgebraicGeometry.Space.zariskiReadingQuasicoherentIso`) followed by the module attached to
`AlgebraicGeometry.Space.pointLaurentHom`. -/
def pointTargetIso (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) (n : ℤ) :
    (modulePullback B S hS (pointHom x)).obj
        (SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property
              L) n) ≅
      ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
        (pointLaurentPieceQcoh L T x n)).obj :=
  zariskiReadingQuasicoherentIso T
      ((etalePointAlgebra (Stacks.SheafOfModules.TensorPower.laurentAlgebra
          (smallEtaleRingedTopos B S hS X).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L)
        T x).piece n)
      (isQuasicoherentOnSite_etalePointAlgebra_piece
        (Stacks.SheafOfModules.TensorPower.laurentAlgebra
          (smallEtaleRingedTopos B S hS X).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L)
        (isQuasicoherentOnSite_laurentAlgebra_piece_of_isInvertible L) x n) ≪≫
    (ObjectProperty.ι _).mapIso
      ((representedQuasicoherentSchemeEquivalence B S hS T).functor.mapIso
        (pointLaurentReadingIso L T x n))

/-- The identification of the inverse image of `ℒ^{⊗ n}`, written out. -/
theorem pointTargetIso_hom (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) (n : ℤ) :
    (pointTargetIso L T x n).hom =
      (zariskiReadingQuasicoherentIso T
        ((etalePointAlgebra (Stacks.SheafOfModules.TensorPower.laurentAlgebra
            (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L)
          T x).piece n)
        (isQuasicoherentOnSite_etalePointAlgebra_piece
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra
            (smallEtaleRingedTopos B S hS X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L)
          (isQuasicoherentOnSite_laurentAlgebra_piece_of_isInvertible L) x n)).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
        (pointLaurentReadingIso L T x n).hom).hom :=
  rfl

variable {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (x : yoneda.obj T ⟶ X.1)

/-- The comparison `τ^*((x^*ℒ)^{⊗ n}) ≅ ((x ∘ τ)^*ℒ)^{⊗ n}` of quasi-coherent modules on `T'`:
the comparison of tensor powers under pullback followed by the tensor power of
`τ^*(x^*ℒ) ≅ (x ∘ τ)^*ℒ`. -/
def pointLaurentPiecePullbackHom (n : ℤ) :
    quasicoherentPullbackObj B S hS τ (pointLaurentPieceQcoh L T x n) ⟶
      pointLaurentPieceQcoh L T' (yoneda.map τ ≫ x) n :=
  ObjectProperty.homMk
    (laurentPullback ((BigFppfOver.toScheme B S hS).map τ) (pointLine B S hS L T x) n ≫
      (LaurentCongr.congrIso (pointLineIso L τ x) n).hom)

/-- The square of `AlgebraicGeometry.Space.pointComparison_comp_pointLaurentHom_app`, as a square
of quasi-coherent modules on `T'`. -/
theorem quasicoherentPullbackMap_pointLaurentReadingIso_comp (n : ℤ) :
    quasicoherentPullbackMap B S hS τ (pointLaurentReadingIso L T x n).hom ≫
        pointLaurentPiecePullbackHom L τ x n =
      (ObjectProperty.homMk ((pointComparison (Stacks.SheafOfModules.TensorPower.laurentAlgebra
          (smallEtaleRingedTopos B S hS X).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L)
            τ x (yoneda.map τ ≫ x) rfl).app n) :
        quasicoherentPullbackObj B S hS τ (pointLaurentReadingQcoh L T x n) ⟶
          pointLaurentReadingQcoh L T' (yoneda.map τ ≫ x) n) ≫
        (pointLaurentReadingIso L T' (yoneda.map τ ≫ x) n).hom := by
  refine ObjectProperty.hom_ext _ ?_
  exact (pointComparison_comp_pointLaurentHom_app L τ x n).symm

/-- The inverse image along `τ` of the module attached to `AlgebraicGeometry.Space.pointLaurentHom`
at `x`, read through `τ^*(M^a) ≅ (τ^*M)^a`. -/
theorem modulePullback_map_pointLaurentReadingIso_comp (n : ℤ) :
    type_of% (modulePullbackRepresentedQuasicoherentIso_naturality B S hS τ
      (pointLaurentReadingIso L T x n).hom) :=
  modulePullbackRepresentedQuasicoherentIso_naturality B S hS τ (pointLaurentReadingIso L T x n).hom

/-- `AlgebraicGeometry.Space.quasicoherentPullbackMap_pointLaurentReadingIso_comp`, read on the
attached modules. -/
theorem map_quasicoherentPullbackMap_pointLaurentReadingIso_comp (n : ℤ) :
    type_of% (hom_map_comp_hom_map_eq
      (representedQuasicoherentSchemeEquivalence B S hS T').functor _ _ _ _
      (quasicoherentPullbackMap_pointLaurentReadingIso_comp L τ x n)) :=
  hom_map_comp_hom_map_eq (representedQuasicoherentSchemeEquivalence B S hS T').functor _ _ _ _
    (quasicoherentPullbackMap_pointLaurentReadingIso_comp L τ x n)

/-- **The identification `x^*(ℒ^{⊗ n}) ≅ ((x^*ℒ)^{⊗ n})^a` is natural in the scheme point**: along
`τ : T' ⟶ T`, the inverse image along `τ` of the identification at `x`, followed by
`τ^*(M^a) ≅ (τ^*M)^a` and the module attached to the comparison
`τ^*((x^*ℒ)^{⊗ n}) ≅ ((x ∘ τ)^*ℒ)^{⊗ n}`, is the composition comparison
`τ^*(x^*ℒ^{⊗ n}) ≅ (x ∘ τ)^*ℒ^{⊗ n}` of Stacks 03LU followed by the identification at `x ∘ τ`.

Both identifications appear through their two factors (the identification
`AlgebraicGeometry.Space.zariskiReadingQuasicoherentIso` with the attached module of the Zariski
reading, and the module attached to `AlgebraicGeometry.Space.pointLaurentReadingIso`; see
`AlgebraicGeometry.Space.pointTargetIso_hom`).  The statement is spelled as the instance of the
abstract chase `AlgebraicGeometry.Space.comp_comp_comp_eq_of_squares` at the three squares it is
proved from, so that it can be composed with them without re-elaborating differently spelled
inverse images. -/
theorem pointTargetIso_naturality (n : ℤ) :
    type_of% (comp_comp_comp_eq_of_squares _ _ _ _ _ _ _ _ _ _
      (modulePullback_map_pointLaurentReadingIso_comp L τ x n)
      (map_quasicoherentPullbackMap_pointLaurentReadingIso_comp L τ x n)
      (modulePullback_map_zariskiReadingQuasicoherentIso_hom_comp_pointComparison τ
        (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L)
        (isQuasicoherentOnSite_laurentAlgebra_piece_of_isInvertible L) x (yoneda.map τ ≫ x) rfl
          n)) :=
  comp_comp_comp_eq_of_squares _ _ _ _ _ _ _ _ _ _
    (modulePullback_map_pointLaurentReadingIso_comp L τ x n)
    (map_quasicoherentPullbackMap_pointLaurentReadingIso_comp L τ x n)
    (modulePullback_map_zariskiReadingQuasicoherentIso_hom_comp_pointComparison τ
        (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L)
        (isQuasicoherentOnSite_laurentAlgebra_piece_of_isInvertible L) x (yoneda.map τ ≫ x) rfl n)

end AlgebraicGeometry.Space

end
