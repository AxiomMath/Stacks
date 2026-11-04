module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.CharacterTorsorFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.RootsOfUnityFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusEigenTorsionBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.MultiplicativeFirstCohomologyNaturality

/-!
# The Picard class of the torsor of a character is a `q`-eigenvector of Frobenius

Let `Y` be a scheme over a finite field `k₀` with `q` elements, `Ȳ = Y ×_{k₀} k̄₀`, and let `P` be
the `μ_n`-torsor over `Ȳ` of the torsor cover of a character
(`AlgebraicGeometry.CharacterTorsorData.baseTorsor`), `q` prime to `n`. The Frobenius twist
`σ = id_Y × Spec(x ↦ x ^ q)` of `Ȳ` fixes the projection to `Y` and pulls a primitive `n`-th
root of unity `ζ` back to `ζ ^ q`, so `σ^*[P] = q • [P]` in `H¹(Ȳ, μ_n)`
(`AlgebraicGeometry.CharacterTorsorData.rootsOfUnityPullbackMap_baseTorsor`). By the
compatibility of `H¹(-, μ_n) → Pic(-)` with pullback, the image of `[P]` in `Pic(Ȳ)` is
an eigenvector of the Frobenius `Stacks.Picard.frobeniusPicardHom` with eigenvalue `q`.

## Main results

* `AlgebraicGeometry.CharacterTorsorData.galoisTwist_appTop_baseRingMap`: `σ^# ζ = ζ ^ q`.
* `AlgebraicGeometry.CharacterTorsorData.frobeniusPicardHom_h1RootsOfUnityToPicard_baseTorsor`:
  the eigenvalue `q`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  Stacks.Cohomology.Torsors Stacks.EtaleCohomology Stacks.Kummer

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [ConnectedSpace X] {x : GeometricPoint X} {n : ℕ} [NeZero n]
  {V : Subgroup (EtaleFundamentalGroup X x)} {Y : FiniteEtaleOver X}
  {eY : (finiteEtaleFiberFunctor x).obj Y ≃ EtaleFundamentalGroup X x ⧸ V}
  {χ : V → ZMod n} {hadd : ∀ a b, χ (a * b) = χ a + χ b}

namespace CharacterTorsorData

variable {K₀ : Type u} [Field K₀] [Fintype K₀] (r : Y.left ⟶ Spec (.of K₀))

omit [ConnectedSpace X] in
/-- **The Frobenius twist pulls a constant back to its `q`-th power**: for `c ∈ k̄₀`, the twist
`σ = id_Y × Spec(Frob)` of `Y ×_{k₀} k̄₀` sends the constant function `c` to `c ^ q`. -/
theorem galoisTwist_appTop_baseRingMap [DecidableEq (AlgebraicClosure K₀)]
    (c : AlgebraicClosure K₀) :
    (Stacks.Picard.galoisTwist K₀ (AlgebraicClosure K₀) (Over.mk r)
        (FiniteField.frobeniusAlgEquivOfAlgebraic K₀ (AlgebraicClosure K₀))).appTop.hom
        (baseRingMap (pullback.snd r (spectrumMap K₀ (AlgebraicClosure K₀))) (𝟙 _) c) =
      baseRingMap (pullback.snd r (spectrumMap K₀ (AlgebraicClosure K₀))) (𝟙 _) c ^
        Fintype.card K₀ := by
  set σ := Stacks.Picard.galoisTwist K₀ (AlgebraicClosure K₀) (Over.mk r)
    (FiniteField.frobeniusAlgEquivOfAlgebraic K₀ (AlgebraicClosure K₀))
  set fS := pullback.snd r (spectrumMap K₀ (AlgebraicClosure K₀))
  have hsnd : σ ≫ fS = fS ≫ specMapAlgAut K₀ (AlgebraicClosure K₀)
      (FiniteField.frobeniusAlgEquivOfAlgebraic K₀ (AlgebraicClosure K₀)) :=
    Stacks.Picard.galoisTwist_comp_snd K₀ (AlgebraicClosure K₀) (Over.mk r) _
  rw [← map_pow]
  show ((Scheme.ΓSpecIso (.of (AlgebraicClosure K₀))).inv ≫ fS.appTop ≫
      Scheme.Hom.appTop (𝟙 (pullback r (spectrumMap K₀ (AlgebraicClosure K₀)))) ≫ σ.appTop).hom c =
    ((Scheme.ΓSpecIso (.of (AlgebraicClosure K₀))).inv ≫ fS.appTop ≫
      Scheme.Hom.appTop (𝟙 (pullback r (spectrumMap K₀ (AlgebraicClosure K₀))))).hom
        (c ^ Fintype.card K₀)
  simp only [Scheme.Hom.id_appTop, Category.id_comp, Category.comp_id]
  rw [← Scheme.Hom.comp_appTop, hsnd, Scheme.Hom.comp_appTop, specMapAlgAut,
    ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, CommRingCat.hom_comp,
    RingHom.comp_apply]
  rfl

variable (D : CharacterTorsorData x χ hadd Y eY) [ConnectedSpace Y.left]
  [DecidableEq (AlgebraicClosure K₀)] {ζ : AlgebraicClosure K₀} (hζ : IsPrimitiveRoot ζ n)
  [HasExt.{u + 1} (Sheaf (pullback r (spectrumMap K₀ (AlgebraicClosure K₀))).smallEtaleTopology
    AddCommGrpCat.{u + 1})]

/-- **The Picard class of the torsor of a character is a `q`-eigenvector of Frobenius.** Let
`P` be the `μ_n`-torsor over `Ȳ = Y ×_{k₀} k̄₀` of the torsor cover of a character, `q = #k₀`
prime to `n`. Then the image `z` of `[P]` in `Pic(Ȳ)` satisfies `Frob z = q • z`. -/
theorem frobeniusPicardHom_h1RootsOfUnityToPicard_baseTorsor
    (hq : Nat.Coprime (Fintype.card K₀) n) :
    Stacks.Picard.frobeniusPicardHom (Over.mk r)
        (h1RootsOfUnityToPicard.{u + 1, 0, u} _ n (torsorIsoClassesEquivH1 _ (Quotient.mk _
          (D.baseTorsor hζ (pullback.snd r (spectrumMap K₀ (AlgebraicClosure K₀)))
            (pullback.fst r (spectrumMap K₀ (AlgebraicClosure K₀))))))) =
      (Fintype.card K₀ : ℤ) • h1RootsOfUnityToPicard.{u + 1, 0, u} _ n
        (torsorIsoClassesEquivH1 _ (Quotient.mk _
          (D.baseTorsor hζ (pullback.snd r (spectrumMap K₀ (AlgebraicClosure K₀)))
            (pullback.fst r (spectrumMap K₀ (AlgebraicClosure K₀)))))) := by
  set m := ((Fintype.card K₀ : ZMod n)⁻¹).val
  have hqm : ((Fintype.card K₀ * m : ℕ) : ZMod n) = 1 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one _ hq
  have hσπ := Stacks.Picard.galoisTwist_comp_fst K₀ (AlgebraicClosure K₀) (Over.mk r)
    (FiniteField.frobeniusAlgEquivOfAlgebraic K₀ (AlgebraicClosure K₀))
  have h := D.rootsOfUnityPullbackMap_baseTorsor hζ
    (pullback.snd r (spectrumMap K₀ (AlgebraicClosure K₀)))
    (pullback.fst r (spectrumMap K₀ (AlgebraicClosure K₀))) _ hσπ (Fintype.card K₀) m
    (galoisTwist_appTop_baseRingMap r ζ) hqm
  rw [natCast_zsmul, ← map_nsmul, ← h]
  exact (h1RootsOfUnityToPicard_naturality _ n _).symm

end CharacterTorsorData

end AlgebraicGeometry
