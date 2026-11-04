module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraComap
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.ReesPullback
public import StacksFrontier.AlgebraicGeometry.SymmetricPullback.Transpose

/-!
# The Rees algebra of an inverse image ideal as a pullback

Let `g : Z ⟶ X` be a morphism of schemes and `ℐ` a quasi-coherent sheaf of ideals on `X`.
`Stacks.Blowup.reesPieceComap` is the comparison `ℐⁿ ⟶ g_*((ℐ𝒪_Z)ⁿ)`, multiplicative and
unital; this file packages it as a unital homomorphism of sheaves of graded algebras
`⨁ₙ ℐⁿ ⟶ g_*(⨁ₙ (ℐ𝒪_Z)ⁿ)` and transposes it across `g^* ⊣ g_*` into

`Φ : g^*(⨁ₙ ℐⁿ) ⟶ ⨁ₙ (ℐ𝒪_Z)ⁿ`.

## Main definitions

* `Stacks.Blowup.reesComapUnitalHom`: the comparison as a unital homomorphism into the
  pushforward of the Rees algebra of `ℐ𝒪_Z`.
* `Stacks.Blowup.reesGradedPullbackHom`: its adjoint transpose, a unital homomorphism out of the
  pulled-back Rees algebra.

## Main results

* `Stacks.Blowup.reesGradedPullbackHom_pullbackSection`: the transpose carries the pullback of a
  homogeneous section of `ℐⁿ` to the comparison's value on that section, which is the only
  description of it there is.
* `Stacks.Blowup.reesPieceAmbient_reesGradedPullbackHom_pullbackSection`: on ambient sections
  that value is `g^♯`.

## Implementation notes

The transpose is `Stacks.RingedSpace.transposeUnitalHom`, which needs multiplicativity only on
pullback-unit images; nothing here reproves it. The two sheaves of rings `X.ringCatSheaf` and
`Stacks.RingedSpace.structureRingSheaf X.toRingedSpace`, and the two morphisms
`g.toRingCatSheafHom` and `Stacks.RingedSpace.structureSheafHom g.toLRSHom.toShHom`, are equal
by `rfl`, which is why the pushforward of `Stacks.Blowup.reesPieceComap` and the pushforward the
transpose consumes are the same object; the identification is made at `exact`, never inside a
rewrite.

## References

* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open SheafOfModules.GradedAlgebra

universe u

namespace Stacks.Blowup

variable {Z X : Scheme.{u}} (g : Z ⟶ X) (I : X.IdealSheafData)

/-- **The comparison `⨁ₙ ℐⁿ ⟶ g_*(⨁ₙ (ℐ𝒪_Z)ⁿ)`**, a unital homomorphism of sheaves of graded
algebras: degreewise `Stacks.Blowup.reesPieceComap`, with `reesPieceComap_mul` and
`reesPieceComap_one` as its two laws. -/
noncomputable def reesComapUnitalHom :
    UnitalHom (reesGradedAlgebra I)
      (Stacks.RingedSpace.pushforwardAlgebra g.toLRSHom.toShHom
        (reesGradedAlgebra (I.comap g))) where
  app n := reesPieceComap g I n
  map_mul i j U x y := by
    obtain ⟨U⟩ := U
    exact reesPieceComap_mul g I i j U x y
  map_one U := by
    obtain ⟨U⟩ := U
    exact reesPieceComap_one g I U

/-- In degree `n`, `Stacks.Blowup.reesComapUnitalHom` is `Stacks.Blowup.reesPieceComap`. -/
@[simp] lemma reesComapUnitalHom_app (n : ℤ) :
    (reesComapUnitalHom g I).app n = reesPieceComap g I n := rfl

/-- **The comparison `Φ : g^*(⨁ₙ ℐⁿ) ⟶ ⨁ₙ (ℐ𝒪_Z)ⁿ`**, the adjoint transpose of
`Stacks.Blowup.reesComapUnitalHom`. -/
noncomputable def reesGradedPullbackHom :
    UnitalHom (Stacks.Conormal.gradedPullback g (reesGradedAlgebra I))
      (reesGradedAlgebra (I.comap g)) :=
  Stacks.RingedSpace.transposeUnitalHom g.toLRSHom.toShHom (reesComapUnitalHom g I)

/-- **The only description of `Φ`:** on the pullback of a homogeneous section of `ℐⁿ` over an
open `V` of `X` it is the comparison `Stacks.Blowup.reesPieceComap` on that section. -/
lemma reesGradedPullbackHom_pullbackSection (n : ℤ) (V : X.Opens)
    (a : (reesPiece I n).val.obj (op V)) :
    ((reesGradedPullbackHom g I).app n).val.app (op (g ⁻¹ᵁ V))
        (Scheme.Modules.pullbackSection g (reesPiece I n) V (g ⁻¹ᵁ V) le_rfl a) =
      (reesPieceComap g I n).val.app (op V) a := by
  rw [Stacks.Conormal.pullbackSection_self g (reesPiece I n) V a]
  exact Stacks.RingedSpace.transposeApp_pullbackUnit g.toLRSHom.toShHom
    (reesComapUnitalHom g I) n V a

/-- On ambient sections `Φ` is `g^♯`: the ambient section of the value of `Φ` on the pullback of
`a` is the pullback of the ambient section of `a`. -/
lemma reesPieceAmbient_reesGradedPullbackHom_pullbackSection (n : ℤ) (V : X.Opens)
    (a : (reesPiece I n).val.obj (op V)) :
    reesPieceAmbient (I.comap g) n (g ⁻¹ᵁ V)
        (((reesGradedPullbackHom g I).app n).val.app (op (g ⁻¹ᵁ V))
          (Scheme.Modules.pullbackSection g (reesPiece I n) V (g ⁻¹ᵁ V) le_rfl a)) =
      (g.app V) (reesPieceAmbient I n V a) :=
  (congrArg (reesPieceAmbient (I.comap g) n (g ⁻¹ᵁ V))
      (reesGradedPullbackHom_pullbackSection g I n V a)).trans
    (reesPieceAmbient_comap g I n V a)

/-- `Φ` for the relative `Proj` situations of `Stacks.Blowup.reesSituation`: the datum that the
base-change square of a relative `Proj` consumes. -/
noncomputable def reesSituationGradedPullbackHom :
    UnitalHom (Stacks.Conormal.gradedPullback g (reesSituation I).algebra)
      (reesSituation (I.comap g)).algebra :=
  reesGradedPullbackHom g I

end Stacks.Blowup

end
