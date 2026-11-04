module

public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.NonnegTruncation
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.Locus
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.TensorPowerDivision.LocalProduct
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartRatioPullbackLocalMul

/-!
# The graded algebra `f_*(⨁_{d ≥ 0} L^{⊗ d})` and its adjunction map

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes and `L` an invertible
`𝒪_X`-module. Clause (5) of [Stacks, Tag 01VJ] and [Stacks, Tag 0C6J] use the quasi-coherent
graded `𝒪_S`-algebra

`𝒜 = f_*(⨁_{d ≥ 0} L^{⊗ d}) = ⨁_{d ≥ 0} f_* L^{⊗ d}`

together with the adjunction map `ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} L^{⊗ d}`. This file builds both, for an
arbitrary quasi-compact quasi-separated `f` and an arbitrary invertible `L`.

## Main definitions

* `Stacks.RelativeAmple.laurentPowers`: the Laurent algebra `⨁_{n ∈ ℤ} L^{⊗ n}` of
  [Stacks, Tag 01CU], as a sheaf of `ℤ`-graded `𝒪_X`-algebras over `X.ringCatSheaf`; its piece in
  degree `n` is `Stacks.AmpleProjectiveImmersion.tensorPowerModule X L n`.
* `Stacks.RelativeAmple.directImageAlgebra`: **`𝒜 = ⨁_{d ≥ 0} f_* L^{⊗ d}`** as a quasi-coherent
  graded `𝒪_S`-algebra in the sense of Situation [Stacks, Tag 01NN]: the direct image of the
  Laurent algebra, truncated to the nonnegative degrees. In degree `d ≥ 0` its piece is
  `f_* L^{⊗ d}`, and its multiplication over an open `V` of `S` is the multiplication of the
  tensor powers over `f⁻¹(V)`; both hold by `rfl` (`directImageAlgebra_piece`,
  `directImageAlgebra_mul_app`). Quasi-coherence of the pieces is [Stacks, Tag 01LC].
* `Stacks.RelativeAmple.directImagePowerMap`: **the adjunction map `ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} L^{⊗ d}`**
  as the datum of [Stacks, Tag 01O8],
  `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap`.
  That datum records the components of `ψ` in adjoint form, as maps `𝒜_d ⟶ f_*(L^{⊗ d})`, and the
  adjoint of the counit `f^* f_* M ⟶ M` is the identity of `f_* M`; so the component in degree `d`
  is the identity of `f_* L^{⊗ d}`, read through the comparison
  `Stacks.AlgebraicGeometry.CoherentMulSections.powCompare` of the two spellings of the tensor
  powers (the iterated one the datum uses and the one of [Stacks, Tag 01CU]).

The morphism `r_{L, ψ}` of [Stacks, Tag 01O9] attached to this datum is
`Stacks.RelativeAmple.relativeAmpleProjHom`, and the isomorphism of [Stacks, Tag 0C6J] is
`Stacks.RelativeAmple.isIso_relativeAmpleProjHom`.

## References

* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare hStruct)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)

universe u

namespace Stacks.RelativeAmple

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **The Laurent algebra `⨁_{n ∈ ℤ} L^{⊗ n}` of an invertible `𝒪_X`-module**, [Stacks, Tag 01CU],
as a sheaf of `ℤ`-graded algebras over `X.ringCatSheaf`. -/
def laurentPowers : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf :=
  Stacks.SheafOfModules.TensorPower.laurentAlgebra X.presheaf (hStruct X) L

/-- The piece of degree `n` of the Laurent algebra is the `n`-th tensor power of `L`. -/
theorem laurentPowers_piece (n : ℤ) : (laurentPowers L).piece n = tensorPowerModule X L n := rfl

/-- The Laurent algebra is commutative. -/
theorem isCommutative_laurentPowers :
    Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.IsCommutative (laurentPowers L) :=
  fun i j U a b =>
    Stacks.SheafOfModules.TensorPower.laurentAlgebra_mul_comm X.presheaf (hStruct X) L i j U a b

/-- **The direct images of the tensor powers of `L` are quasi-coherent** along a quasi-compact
quasi-separated morphism: [Stacks, Tag 01LC] applied to the invertible, hence quasi-coherent,
modules `L^{⊗ n}`. -/
theorem isQuasicoherent_pushforward_laurentPowers [QuasiCompact f] [QuasiSeparated f] (n : ℤ) :
    (((Scheme.Modules.pushforward f).obj ((laurentPowers L).piece n) :
      S.Modules)).IsQuasicoherent := by
  have hinv : Stacks.Ample.IsInvertibleModule X (tensorPowerModule X L n) :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      X.presheaf (hStruct X) _).mp
      (Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower X.presheaf (hStruct X) L n)
  have : ((laurentPowers L).piece n).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule (tensorPowerModule X L n)
  exact AlgebraicGeometry.pushforward_isQuasicoherent f _

/-- **The quasi-coherent graded `𝒪_S`-algebra `𝒜 = ⨁_{d ≥ 0} f_* L^{⊗ d}`** of
[Stacks, Tag 01VJ] (5) and [Stacks, Tag 0C6J], in the sense of Situation [Stacks, Tag 01NN]: the
direct image along `f` of the Laurent algebra of `L`, truncated to the nonnegative degrees. -/
def directImageAlgebra [QuasiCompact f] [QuasiSeparated f] : SheafGradedAlgebra S :=
  Stacks.AlgebraicGeometry.NonnegTruncation.pushforwardNonnegSheafGradedAlgebra f
    (laurentPowers L) (isCommutative_laurentPowers L)
    (isQuasicoherent_pushforward_laurentPowers f L)

variable [QuasiCompact f] [QuasiSeparated f]

/-- In degree `d ≥ 0` the piece of `𝒜` is `f_* L^{⊗ d}`, by definition. -/
theorem directImageAlgebra_piece (n : ℕ) :
    (directImageAlgebra f L).piece (n : ℤ)
      = (Scheme.Modules.pushforward f).obj (tensorPowerModule X L (n : ℤ)) := rfl

/-- In nonnegative degrees the multiplication of `𝒜` over an open `V` of `S` is the
multiplication `Γ(f⁻¹V, L^{⊗ n}) × Γ(f⁻¹V, L^{⊗ m}) ⟶ Γ(f⁻¹V, L^{⊗ (n + m)})` of the tensor powers,
by definition. -/
theorem directImageAlgebra_mul_app (n m : ℕ) (V : S.Opens)
    (a : Γ((directImageAlgebra f L).piece (n : ℤ), V))
    (b : Γ((directImageAlgebra f L).piece (m : ℤ), V)) :
    ((directImageAlgebra f L).mul (n : ℤ) (m : ℤ)).app V a b
      = Stacks.TensorPowerDivision.localMul L (n := (n : ℤ)) (m := (m : ℤ)) (W := f ⁻¹ᵁ V) a b :=
  rfl

/-- **The adjunction map `ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} L^{⊗ d}`** of [Stacks, Tag 01VJ] (5), as the datum
of [Stacks, Tag 01O8]. The datum records `ψ` in adjoint form, by maps `𝒜_d ⟶ f_*(L^{⊗ d})`, and the
adjoint of the adjunction map is the identity: in degree `d` it is the identity of
`f_* L^{⊗ d}`, read through the comparison `powCompare` between the tensor powers of
[Stacks, Tag 01CU] and the iterated tensor powers the datum is written with. Multiplicativity is
the definition of the product of sections of iterated tensor powers,
`Stacks.AlgebraicGeometry.NatTensorPowLocalMul.localMulSections`, as the product of
[Stacks, Tag 01CU] conjugated by `powCompare`. -/
def directImagePowerMap : GradedPowerMap (directImageAlgebra f L) f where
  L := L
  invertible := inferInstance
  ψ n := (Scheme.Modules.pushforward f).map (powCompare L n).inv
  map_mul n m V a b := by
    change (powCompare L (n + m)).inv.app (f ⁻¹ᵁ V)
        (Stacks.TensorPowerDivision.localMul L (n := (n : ℤ)) (m := (m : ℤ)) a b) =
      (powCompare L (n + m)).inv.app (f ⁻¹ᵁ V)
        (Stacks.TensorPowerDivision.localMul L
          ((powCompare L n).hom.app (f ⁻¹ᵁ V) ((powCompare L n).inv.app (f ⁻¹ᵁ V) a))
          ((powCompare L m).hom.app (f ⁻¹ᵁ V) ((powCompare L m).inv.app (f ⁻¹ᵁ V) b)))
    have ha := Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app
      (powCompare L n) (f ⁻¹ᵁ V) (show Γ(tensorPowerModule X L n, f ⁻¹ᵁ V) from a)
    have hb := Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app
      (powCompare L m) (f ⁻¹ᵁ V) (show Γ(tensorPowerModule X L m, f ⁻¹ᵁ V) from b)
    rw [ha, hb]

/-- The component of the adjunction map in degree `d`, on a section over an open `V` of `S`: the
section of `f_* L^{⊗ d}` over `V` read as a section of the iterated tensor power over `f⁻¹(V)`. -/
theorem directImagePowerMap_value (n : ℕ) (V : S.Opens)
    (a : Γ((directImageAlgebra f L).piece (n : ℤ), V)) :
    (directImagePowerMap f L).value n V a = (powCompare L n).inv.app (f ⁻¹ᵁ V) a := rfl

end Stacks.RelativeAmple

end
