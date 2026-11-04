module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.Global

/-!
# The comparison `ℳ̃_T ≅ h^*ℳ̃` for a quadruple

Let `(f : T → S, d, L, ψ)` be a quadruple and `h : T ⟶ Proj_S(𝒜)` the morphism it classifies.
For a graded `𝒜`-module `ℳ` with quasi-coherent homogeneous pieces there is a canonical
isomorphism `ℳ̃_T ≅ h^*ℳ̃` between the module of [Stacks, Tag 01O6] attached to the quadruple and
the pullback of the sheaf `ℳ̃` on `Proj_S(𝒜)`.

The isomorphism is `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.Quadruple.tildeComparison`.
It is characterized locally: around every point of `T` the triple `(f, ψ, h)` has a chart datum
(an affine open `U` of the base, a section `c` of `𝒜_d` over `U` with `ψ(c)` generating `L`, and
the factorization `g` of `h` through `D₊(c) ⊆ Proj 𝒜(U)`), and over a chart datum the isomorphism
is the chart comparison, which sends a pure tensor `x ⊗ l` of `f^*ℳ_{nd} ⊗ L^{⊗ (-n)}` to
`(ψ(c)^n · l) · g^*(x / c^n)`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.tag01O7_property1`: property (1) of
  [Stacks, Tag 01O7]: chart data exist locally on `T`, the isomorphism restricts to the chart
  comparison over every chart datum, the chart comparison is given on pure tensors by the formula
  above, and the isomorphism is the only one restricting to the chart comparisons.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01O6](https://stacks.math.columbia.edu/tag/01O6)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MonoidalCategory
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.RelativeProj.Situation

universe u

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

namespace Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

variable {s : Stacks.RelativeProj.Situation.{u}}
  (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] {d : ℕ} (hd : 0 < d)
  {T : Scheme.{u}} {f : T ⟶ s.base} (P : Quadruple f s.algebra (d : ℤ))

/-- For a quadruple `P = (f : T → S, d, L, ψ)` and the morphism `h : T ⟶ Proj_S(𝒜)` it
classifies, the isomorphism `Quadruple.tildeComparison ℳ hd P : ℳ̃_T ≅ h^*ℳ̃` satisfies:

* chart data of `(f, ψ, h)` exist around every point of `T`;
* along every morphism `a : Z ⟶ T` carrying a chart datum `D`, its pullback is the local
  comparison `localHom ℳ hd a D`, which is `a^*ℳ̃_T ≅ ℳ̃_Z`, then the chart comparison of `D`, then
  `(a ≫ h)^*ℳ̃ ≅ a^*h^*ℳ̃` (`localHom_eq`);
* the chart comparison of a datum sends the pure tensor `x ⊗ l` in degree `n` to
  `(w^n · l) · g^*(x / c^n)`, `w = ψ(c)`;
* it is the only isomorphism `ℳ̃_T ≅ h^*ℳ̃` with the second property along the opens of `T`. -/
@[stacks 01O7 "property (1): the canonical isomorphism M~_T ≅ h^*M~"]
theorem tag01O7_property1 :
    letI := P.isInvertible
    (∀ t : T, ∃ V : T.Opens, t ∈ V ∧ Nonempty (ChartDatum (V.ι ≫ f) (P.twisting.pullback V.ι)
      (V.ι ≫ classifyingHom s (by exact_mod_cast hd) P))) ∧
    (∀ {Z : Scheme.{u}} (a : Z ⟶ T) (D : ChartDatum (a ≫ f) (P.twisting.pullback a)
        (a ≫ classifyingHom s (by exact_mod_cast hd) P)),
      (Scheme.Modules.pullback a).map (Quadruple.tildeComparison ℳ hd P).hom =
        localHom ℳ hd a D) ∧
    (∀ {Z : Scheme.{u}} (a : Z ⟶ T) (D : ChartDatum (a ≫ f) (P.twisting.pullback a)
        (a ≫ classifyingHom s (by exact_mod_cast hd) P)) (n : ℤ),
      Twisting.pureTensor (ℳ.toGradedModule s.mul_comm) (P.twisting.pullback a) n ≫
          (D.iso ℳ hd).hom =
        bmap ℳ D.U D.c (a ≫ f) D.hf D.g D.hg D.hgf D.w n ≫
          (moduleSheafPullbackChartIso ℳ D.U D.g D.fac).inv) ∧
    (∀ Φ : Twisting.associatedSheaf (ℳ.toGradedModule s.mul_comm) P.twisting ≅
        (Scheme.Modules.pullback (classifyingHom s (by exact_mod_cast hd) P)).obj (moduleSheaf ℳ),
      (∀ (V : T.Opens) (D : ChartDatum (V.ι ≫ f) (P.twisting.pullback V.ι)
          (V.ι ≫ classifyingHom s (by exact_mod_cast hd) P)),
        (Scheme.Modules.pullback V.ι).map Φ.hom = localHom ℳ hd V.ι D) →
        Φ = Quadruple.tildeComparison ℳ hd P) :=
  let := P.isInvertible
  ⟨exists_chartDatum s hd f P, Quadruple.tildeComparison_chart ℳ hd P,
    fun _ D => ChartDatum.pureTensor_iso_hom ℳ D hd, Quadruple.eq_tildeComparison ℳ hd P⟩

end Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

end
