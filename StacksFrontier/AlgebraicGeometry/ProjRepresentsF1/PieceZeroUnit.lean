module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TensorAlgebraMul
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerInteger

/-!
# The degree-zero piece of a sheaf of graded algebras is the structure sheaf

Let `A` be a sheaf of graded algebras over a sheaf of rings on a site. If the degree-zero piece
`A₀` is invertible and the multiplication `A₀ ⊗ A₀ ⟶ A₀` is an isomorphism, then the unit
`𝒪 ⟶ A₀` is itself an isomorphism, and so `A₀` is the structure sheaf by an identification
carrying the algebra unit to `1`.

On a relative `Proj` both hypotheses hold for the twist datum of Tag 01NR: invertibility of `𝒪(0)`
is `Stacks.AlgebraicGeometry.TwistMapsInvertible.twistData_stacksIsInvertible`, and invertibility
of `𝒪(0) ⊗ 𝒪(0) ⟶ 𝒪(0)` is `Stacks.AlgebraicGeometry.TwistMapsInvertible.twistData_isIso_mulSheaf`
in bidegree `(0, 0)`. Since `twistsAreTensorPowers_of_pieceZeroIsoUnit` reduces
`Stacks.AlgebraicGeometry.ProjRepresentsF1.TwistsAreTensorPowers` to such an identification of
`𝒪(0)` with `𝒪_X`, the canonicality clause of Tag 01O4 holds under generation in degree one alone,
and the criterion `Stacks.AlgebraicGeometry.ProjRepresentsF1.isCanonicalTwistPair_iff` loses its
isomorphy clause.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.pieceZeroIsoUnit`: `A₀ ≅ 𝒪`, the inverse of the unit
  of `A`.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.twistPieceZeroIsoUnit`: `𝒪(0) ≅ 𝒪_X` for the twist
  datum of Tag 01NR on a relative `Proj`.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_oneHom`: the unit of a sheaf of graded
  algebras with invertible degree-zero piece is an isomorphism as soon as the degree-`(0, 0)`
  multiplication is one.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.pieceZeroIsoUnit_one` and
  `twistPieceZeroIsoUnit_one`: the identification carries the algebra unit to `1`, the
  normalisation `SheafOfModules.GradedAlgebra.isIso_unitalHom_app_zero` asks for.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.twistsAreTensorPowers`: the canonicality clause of
  Tag 01O4, with no hypothesis beyond generation in degree one.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isCanonicalTwistPair_iff_psi`: a pair on relative
  `Proj` is the canonical twist pair exactly when its graded map is compatible with the
  homogeneous-section map of the twist datum.

## Proof

The left unit law of a sheaf of graded algebras in degree `(0, 0)`,
`SheafOfModules.GradedAlgebra.mulSheaf_one_mul` at `i = 0`, reads

> `oneHom A ▷ A₀ ≫ mulSheaf A 0 0 = (λ_ A₀).hom ≫ eqToHom _`,

whose right-hand side is an isomorphism. The multiplication being an isomorphism, the whiskering
`oneHom A ▷ A₀` is one; and tensoring on the right by the invertible `A₀` is an equivalence
(`Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor`), hence reflects
isomorphisms, so `oneHom A` is one.

## Implementation notes

The monoidal whiskering is identified with the right-tensor functor of Tag 01CU by
`Stacks.SheafOfModules.whiskerRight_eq_sheafify_map`, not by instance search: the functor
`Stacks.SheafOfModules.TensorPower.tensorRightFunctor` carries no monoidal instance in its type,
while the whiskering of `mulSheaf_one_mul` lives at `Stacks.TensorSheafWorld.monoidalCategory`.
The two spellings of the ring sheaf,
`Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO` and
`CategoryTheory.Sheaf.toRingCat J O♯`, are equal by `rfl` but are different discrimination-tree
keys, so `reflects` is reached through the private `isIso_of_isIso_map`, whose two categories,
functor and morphism are all free: the crossing is then done by the unifier at the application
rather than by instance search, which fails. For the same reason the invertibility
hypothesis is passed to `isEquivalence_tensorRightFunctor` explicitly.

Invertibility of the multiplication is destructured, not used as an instance: `IsIso.inv` is not
available at these spellings, so the inverse is taken out of `CategoryTheory.IsIso.out` and the
cancellation is the private `isIso_of_comp_eq`, which takes every inverse as an argument.

The isomorphism `pieceZeroIsoUnit` is the inverse of `oneHom` rather than one of the library's
`𝒪(0) ≅ 𝒪`s (such as `Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit` or
`Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistZeroIsoUnit`), which concern the twisting sheaves
of a graded ring rather than a `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` on a
relative `Proj`, and rather than one built by
`Stacks.AlgebraicGeometry.ProjTwistTensorPow.isoUnitModuleOfTensorSelfIso`, which says nothing
about where the algebra unit goes. As the inverse of `oneHom` it carries the algebra unit to `1` by
definition.

This file constructs no term of `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Representation`.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf MonoidalCategory TopologicalSpace Opposite

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

universe v u w

section Abstract

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

/-- Cancellation: a morphism whose composite with an isomorphism is an isomorphism is one. -/
private theorem isIso_of_comp_eq {D : Type*} [Category D] {P Q R : D}
    (a : P ⟶ Q) {b : Q ⟶ R} {bInv : R ⟶ Q} (hb₁ : b ≫ bInv = 𝟙 Q) (_hb₂ : bInv ≫ b = 𝟙 R)
    {c : P ⟶ R} {cInv : R ⟶ P} (hc₁ : c ≫ cInv = 𝟙 P) (hc₂ : cInv ≫ c = 𝟙 R)
    (h : a ≫ b = c) : IsIso a := by
  have ha : c ≫ bInv = a := by rw [← h, Category.assoc, hb₁, Category.comp_id]
  refine ⟨b ≫ cInv, ?_, ?_⟩
  · rw [← Category.assoc, h, hc₁]
  · rw [← ha, Category.assoc, reassoc_of% hc₂, hb₁]

/-- A functor which is an equivalence reflects isomorphisms. -/
private theorem isIso_of_isIso_map {D E : Type*} [Category D] [Category E] (F : D ⥤ E)
    [F.IsEquivalence] {X Y : D} (f : X ⟶ Y) (h : IsIso (F.map f)) : IsIso f := by
  have := h
  exact isIso_of_reflects_iso f F

variable (A : SheafOfModules.GradedAlgebra.{w, w} (toRingCat J Osharp))
  (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))

include hO

/-- The unit of a graded algebra, right-whiskered by the degree-zero piece, is an isomorphism
when the degree-`(0,0)` multiplication is. -/
private theorem isIso_whiskerRight_oneHom
    (hmul : IsIso (SheafOfModules.GradedAlgebra.mulSheaf A 0 0)) :
    IsIso (SheafOfModules.GradedAlgebra.oneHom A ▷ A.piece 0) := by
  obtain ⟨m, hm₁, hm₂⟩ := hmul.out
  refine isIso_of_comp_eq _ (bInv := m) hm₁ hm₂
    (cInv := eqToHom (congrArg A.piece (zero_add (0 : ℤ))) ≫ (λ_ (A.piece 0)).inv) ?_ ?_
    (SheafOfModules.GradedAlgebra.mulSheaf_one_mul A hO 0) <;> simp

/-- The unit of a graded algebra with invertible degree-zero piece is an isomorphism as soon as
the degree-`(0,0)` multiplication is one. -/
public theorem isIso_oneHom
    (hinv : Stacks.SheafOfModules.IsInvertible Osharp.obj hO (A.piece 0))
    (hmul : IsIso (SheafOfModules.GradedAlgebra.mulSheaf A 0 0)) :
    IsIso (SheafOfModules.GradedAlgebra.oneHom A) := by
  have := @Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor _ _ _ Osharp.obj hO
    _ _ (A.piece 0) hinv
  refine @isIso_of_isIso_map _ _ _ _ _ this _ _ (SheafOfModules.GradedAlgebra.oneHom A) ?_
  exact Eq.mpr (congrArg IsIso (Stacks.SheafOfModules.whiskerRight_eq_sheafify_map Osharp.obj hO
    (SheafOfModules.GradedAlgebra.oneHom A) (A.piece 0)).symm) (isIso_whiskerRight_oneHom A hO hmul)

/-- The degree-zero piece of a graded algebra with invertible degree-zero piece and invertible
degree-`(0,0)` multiplication is the structure sheaf, by the inverse of the algebra unit. -/
public def pieceZeroIsoUnit
    (hinv : Stacks.SheafOfModules.IsInvertible Osharp.obj hO (A.piece 0))
    (hmul : IsIso (SheafOfModules.GradedAlgebra.mulSheaf A 0 0)) :
    A.piece 0 ≅ SheafOfModules.unit (toRingCat J Osharp) :=
  (@asIso _ _ _ _ (SheafOfModules.GradedAlgebra.oneHom A) (isIso_oneHom A hO hinv hmul)).symm

/-- `pieceZeroIsoUnit` carries the algebra unit to `1`. -/
public theorem pieceZeroIsoUnit_one
    (hinv : Stacks.SheafOfModules.IsInvertible Osharp.obj hO (A.piece 0))
    (hmul : IsIso (SheafOfModules.GradedAlgebra.mulSheaf A 0 0)) (U : Cᵒᵖ) :
    (pieceZeroIsoUnit A hO hinv hmul).hom.val.app U (A.one.eval U) =
      (1 : (toRingCat J Osharp).obj.obj U) := by
  have h1 : (SheafOfModules.GradedAlgebra.oneHom A).val.app U
      (1 : (toRingCat J Osharp).obj.obj U) = A.one.eval U :=
    (SheafOfModules.GradedAlgebra.oneHom_val_app A U 1).trans (one_smul _ _)
  refine Eq.trans (congrArg ((pieceZeroIsoUnit A hO hinv hmul).hom.val.app U) h1.symm) ?_
  exact congrFun (congrArg (fun g => ⇑(ConcreteCategory.hom ((SheafOfModules.Hom.val g).app U)))
      (@asIso _ _ _ _ (SheafOfModules.GradedAlgebra.oneHom A)
        (isIso_oneHom A hO hinv hmul)).hom_inv_id)
    (1 : (toRingCat J Osharp).obj.obj U)

end Abstract

section Relative

open _root_.AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} (TA : TensorAlgebras.{u})
  (D : TwistData A)

/-- The degree-zero twist `𝒪(0)` on a relative `Proj` is the structure sheaf `𝒪_X`, by the
inverse of the unit of the graded algebra of twists. -/
public def twistPieceZeroIsoUnit (hgen : IsGeneratedInDegreeOne A) :
    D.algebra.piece 0 ≅ SheafOfModules.unit (relativeProj A).scheme.ringCatSheaf :=
  pieceZeroIsoUnit D.algebra (relativeProj A).scheme.ringCatSheaf.2
    (Stacks.AlgebraicGeometry.TwistMapsInvertible.twistData_stacksIsInvertible D hgen 0)
    (Stacks.AlgebraicGeometry.TwistMapsInvertible.twistData_isIso_mulSheaf D hgen 0 0)

/-- `twistPieceZeroIsoUnit` carries the unit of the algebra of twists to `1`. -/
public theorem twistPieceZeroIsoUnit_one (hgen : IsGeneratedInDegreeOne A)
    (U : ((relativeProj A).scheme.Opens)ᵒᵖ) :
    (twistPieceZeroIsoUnit D hgen).hom.val.app U (D.algebra.one.eval U) =
      (1 : (relativeProj A).scheme.ringCatSheaf.obj.obj U) :=
  pieceZeroIsoUnit_one _ _ _ _ U

/-- The canonicality clause of Tag 01O4: for a graded algebra generated in degree one, the
canonical comparison out of the tensor algebra of a module on relative `Proj` identified with the
degree-one twist is an isomorphism in every nonnegative degree. -/
public theorem twistsAreTensorPowersOf (hgen : IsGeneratedInDegreeOne A)
    (L : (relativeProj A).scheme.Modules) (β : L ≅ D.algebra.piece 1) :
    TwistsAreTensorPowersOf TA D L β :=
  twistsAreTensorPowersOf_of_pieceZeroIsoUnit TA D hgen L β
    (twistPieceZeroIsoUnit D hgen) (twistPieceZeroIsoUnit_one D hgen)

/-- The canonicality clause of Tag 01O4 for a pair: the canonical comparison out of the tensor
algebra of the pair's invertible sheaf is an isomorphism in every nonnegative degree. -/
public theorem twistsAreTensorPowers (hgen : IsGeneratedInDegreeOne A)
    (P : F1Pair A TA (relativeProj A).toBase) (β : P.L ≅ D.algebra.piece 1) :
    TwistsAreTensorPowers TA D P β :=
  twistsAreTensorPowersOf TA D hgen P.L β

/-- For a graded algebra generated in degree one, a twist pair is canonical exactly when, for
some identification of its invertible sheaf with the degree-one twist, its graded map is
compatible with the homogeneous-section map of the twist datum. -/
public theorem isCanonicalTwistPair_iff_psi (hgen : IsGeneratedInDegreeOne A)
    (P : F1Pair A TA (relativeProj A).toBase) :
    IsCanonicalTwistPair A TA D P ↔
      ∃ β : P.L ≅ D.algebra.piece 1,
        ∀ n : ℕ, P.ψ (n : ℤ) ≫
          (Scheme.Modules.pushforward (relativeProj A).toBase).map
            ((pairTwistComparison TA D P β).app (n : ℤ)) = D.ψ n :=
  (isCanonicalTwistPair_iff TA D P).trans
    ⟨fun ⟨β, _, hψ⟩ => ⟨β, hψ⟩,
      fun ⟨β, hψ⟩ => ⟨β, twistsAreTensorPowers TA D hgen P β, hψ⟩⟩

end Relative

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
