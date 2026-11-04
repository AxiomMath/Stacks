module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.GluedRepresents
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.TripleComparison

/-!
# The quadruple-to-triple map is a map out of the graded ring `A = Γ(S, 𝒜)`

In Situation 01NN the homogeneous sections of `𝒜` over an open `U ⊆ S` form a graded
commutative ring, `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.sectionRing`,
whose degree-`n` piece is `Γ(U, 𝒜_n)`; for `U = S` this is the graded ring `A = Γ(S, 𝒜)` that
Tag 01NU's proof forms `Proj(A)` from, and the source's map out of the Veronese subring
`A^{(d)}` has the pieces `A_{kd} = Γ(S, 𝒜_{kd})` as its sources.

`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.globalSectionHom`, built in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.TripleComparison`, is a map out of
`Γ(S, (situationAlgebra 𝒜)_{kd})`. This file records that its source *is* the degree-`kd` piece
of that graded ring, and that the multiplication its multiplicativity statement uses *is* the
graded multiplication of that ring — both on the nose, with no comparison map. So the family of
maps of `TripleComparison` is literally a homomorphism of graded rings out of the Veronese
regrading `A^{(d)}`, which is the `ψ` of a triple of Section 01N4 except for its target.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.sectionPieces_eq_globalSectionHom_domain`:
  **the source of the degree-`k` component is `A_{kd}`**, the degree-`kd` piece of the graded
  ring of global sections of `𝒜`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra_mul_app_eq_gMul`: **the
  multiplication is the graded multiplication of that ring.**
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.sectionRingHom`: the degree-`k` component
  retyped as a map out of `A_{kd}`.

## What is still missing for a triple of Section 01N4

The *target*. A triple's `ψ` lands in `Γ_*(T, L) = ⨁_{n ≥ 0} Γ(T, L^{⊗ n})` as the library
spells it, `Stacks.AlgebraicGeometry.ProjTriple.gammaStar`, whose degree-`n` summand is the
sections of `Stacks.SheafOfModules.TensorPower.tensorPower` over the *terminal* open
`⊤_ (Opens T)` rather than over `⊤`, and whose multiplication is
`Stacks.SheafOfModules.sectionRingMul`. The maps here land in the sections over `⊤` of
`(laurent L).piece k`, which is the same tensor power by `rfl`
(`Stacks.SheafOfModules.TensorPower.laurentAlgebra_piece`), and their multiplicativity is
stated for the Laurent multiplication `Stacks.SheafOfModules.TensorPower.mulBilinear`. Two
comparisons therefore remain: the restriction `⊤_ (Opens T) ⟶ ⊤` of
`Stacks.AlgebraicGeometry.ProjTriple.toTopSection`, and the agreement of `mulBilinear` with
`sectionRingMul`. Neither is carried out here, and neither is the converse direction of Tag
01NU; see the "What this is and is not" section of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.TripleComparison`.

## References

* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {T S : Scheme.{u}} {f : T ⟶ S} {B : SheafGradedAlgebra S} {d : ℕ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- **The source of the degree-`k` component of the quadruple-to-triple map is `A_{kd}`**, the
degree-`kd` homogeneous piece of the graded ring `A = Γ(S, 𝒜)` of Situation 01NN — equivalently
the degree-`k` piece of the Veronese regrading `A^{(d)}`.

Both sides are `Γ(S, 𝒜_{kd})`; the `ℤ`-degree `k · d` of the sheaf of graded algebras and the
`ℕ`-degree `kd` of the graded ring of sections agree definitionally. -/
theorem sectionPieces_eq_globalSectionHom_domain (B : SheafGradedAlgebra S) (d k : ℕ) :
    ((situationAlgebra B).piece ((k : ℤ) * (d : ℤ))).val.obj
        (op (⊤ : Opens S.toRingedSpace.carrier)) =
      B.sectionPieces ⊤ (k * d) :=
  rfl

/-- **The multiplication that the multiplicativity statement uses is the graded multiplication
of the ring `A = Γ(S, 𝒜)`.** The graded ring of Tag 01NN multiplies two homogeneous sections by
the multiplication of `𝒜` itself (`SheafGradedAlgebra.gMul_def`), and `situationAlgebra` reads
that multiplication off `𝒜` without transporting it. -/
theorem situationAlgebra_mul_app_eq_gMul (B : SheafGradedAlgebra S) (n m : ℕ)
    (a : B.sectionPieces ⊤ n) (b : B.sectionPieces ⊤ m) :
    ((situationAlgebra B).mul (n : ℤ) (m : ℤ)).app (op (⊤ : Opens S.toRingedSpace.carrier)) a b =
      (GradedMonoid.GMul.mul a b : B.sectionPieces ⊤ (n + m)) :=
  rfl

/-- **The degree-`k` component of the map `A^{(d)} ⟶ Γ_*(T, L)` of Section 01N4**, retyped as a
map out of `A_{kd} = Γ(S, 𝒜_{kd})`, the degree-`k` piece of the Veronese regrading of the graded
ring of Situation 01NN. This is
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.globalSectionHom` with its source read
through `sectionPieces_eq_globalSectionHom_domain`. -/
def sectionRingHom (ψ : Twisting f (situationAlgebra B) (d : ℤ) L) (k : ℕ) :
    B.sectionPieces ⊤ (k * d) →+
      ((laurent L).piece (k : ℤ)).val.obj (op (⊤ : Opens T.toRingedSpace.carrier)) :=
  ψ.globalSectionHom (k : ℤ)

/-- `sectionRingHom ψ k` sends a section `a ∈ Γ(S, 𝒜_{kd})` to its image under the degree-`k`
global section map `ψ.globalSectionHom k`. -/
theorem sectionRingHom_apply (ψ : Twisting f (situationAlgebra B) (d : ℤ) L) (k : ℕ)
    (a : B.sectionPieces ⊤ (k * d)) : sectionRingHom ψ k a = ψ.globalSectionHom (k : ℤ) a :=
  rfl

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
