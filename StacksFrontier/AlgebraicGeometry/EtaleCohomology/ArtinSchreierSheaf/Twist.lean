module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.Sheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationCoefficients

/-!
# The twist `ℱ_ρ ⊗ L_ψ(g)` of an `O`-sheaf by an Artin–Schreier sheaf

Let `ρ : π₁(Spec A, x̄) → GL_r(O)` be a representation with coefficients in a finite free
`ℤ_ℓ`-algebra `O`, and `ψ : 𝔽_q → O^×` an additive character. The twist of `ℱ_ρ` by the
Artin–Schreier sheaf `L_ψ(g)` is the `O`-sheaf of the representation `σ ↦ ψ(-χ_g(σ)) ρ(σ)`, `χ_g`
the character of the Artin–Schreier cover `t^q - t = g`. Its geometric Frobenius at a closed point
`y` has `O`-trace `ψ(Tr_{κ(y)/𝔽_q}(g(y))) · tr ρ(F_y)`: the trace function of `ℱ_ρ ⊗ L_ψ(g)` is the
product of the trace function of `ℱ_ρ` with the additive character `ψ(Tr g)`. For `A = 𝔽_q[x]_f`,
`g = t x` this is the sheaf whose compactly supported cohomology `Hⁱ_c(U_{k̄}, ℱ_ρ ⊗ L_ψ(t x))`
(with its `O`-linear Frobenius `LAdicSheaf.CoefficientSheaf.geometricCompactlySupportedFrobenius`)
is the fibre at `t` of the Fourier–Deligne transform of `ℱ_ρ` [Laumon, 1.2], [Kiehl–Weissauer,
III.8].

## Main definitions

* `Stacks.ArtinSchreier.artinSchreierTwistSheaf`: the `O`-sheaf `ℱ_ρ ⊗ L_ψ(g)`.

## Main results

* `Stacks.ArtinSchreier.artinSchreierCharacter_frobenius`: the Artin–Schreier character takes the
  value `ψ(Tr g(y))` at the geometric Frobenius of `y`.
* `Stacks.ArtinSchreier.trace_artinSchreierTwistSheaf_frobenius`: the Frobenius trace of the twist.

## References

* [G. Laumon, Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil, 1.1–1.2]
* [R. Kiehl, R. Weissauer, Weil conjectures, perverse sheaves and ℓ-adic Fourier transform, I.2,
  III.8]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.EtaleCohomology
  Stacks.Frobenius

universe u

namespace Stacks.ArtinSchreier

variable (k : Type u) [Field k] [Fintype k] (A : Type u) [CommRing A] [Algebra k A] (g : A)
  [ConnectedSpace (Spec (.of A))]
  {O : Type} [CommRing O] (ψ : AddChar k O)

/-- **The Artin–Schreier character at the geometric Frobenius of a closed point `y` is
`ψ(Tr_{κ(y)/𝔽_q}(g(y)))`**, the geometric Frobenius element being transported to the base point
along a path `t`. -/
public theorem artinSchreierCharacter_frobenius (x : GeometricPoint (Spec (.of A)))
    (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g)) (y : closedPoints (Spec (.of A)))
    [Finite ((Spec (.of A)).residueField y.1)]
    (t : finiteEtaleFiberFunctor (geometricPointAt _ y.1) ≅ finiteEtaleFiberFunctor x) :
    (artinSchreierCharacter k A g ψ x p₀
        (etaleFundamentalGroupMulEquiv t (frobeniusDataOfPath x y t).localElement⁻¹) : O) =
      ψ (letI := residueAlgebra k A y.1; Algebra.trace k _ (residueRingHom A y.1 g)) := by
  let := residueAlgebra k A y.1
  set q₀ : (finiteEtaleFiberFunctor (geometricPointAt _ y.1)).obj (cover k A g) :=
    (t.inv.app (cover k A g)).hom p₀
  have h1 := (torsorCover k A g).character_etaleFundamentalGroupMulEquiv t q₀ p₀
    (frobeniusDataOfPath x y t).localElement⁻¹
  have h2 := character_localElement y x t q₀ (g := g)
  have h3 := MonoidHom.map_inv ((torsorCover k A g).character (geometricPointAt _ y.1) q₀)
    (frobeniusDataOfPath x y t).localElement
  replace h1 := h1.trans h3
  rw [artinSchreierCharacter_apply]
  congr 1
  refine (congrArg (fun m => -Multiplicative.toAdd m) h1).trans ?_
  rw [toAdd_inv, neg_neg]
  exact h2

variable (B : BigEtaleSite.{u}) (hX : schemeSizeBelow B.cutoff (Spec (.of A)))
  {ℓ : ℕ} [Fact ℓ.Prime] [Algebra ℤ_[ℓ] O] {d : ℕ} (b : Module.Basis (Fin d) ℤ_[ℓ] O) {r : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B (specObject A B hX).1 (specObject A B hX).2)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian (Spec (.of A))]
  (x : GeometricPoint (Spec (.of A))) (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g))
  (ρ : EtaleFundamentalGroup (specObject A B hX).1 x →* GL (Fin r) O)

section

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B (specObject A B hX).1 (specObject A B hX).2)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian (Spec (.of A))]

/-- The restriction of scalars of a twist is the product of the restriction of scalars of `ρ`
with the scalar matrices of the character. -/
public theorem restrictScalarsRepresentation_characterTwist
    (χ : EtaleFundamentalGroup (specObject A B hX).1 x →* Oˣ)
    (σ : EtaleFundamentalGroup (specObject A B hX).1 x) :
    restrictScalarsRepresentation B (specObject A B hX) x b (characterTwist ρ χ) σ =
      restrictScalarsRepresentation B (specObject A B hX) x b ρ σ *
        Units.map (coefficientScalarRingHom b r).toMonoidHom (χ σ) := by
  ext : 1
  change coefficientMatrixRingHom b r ((ρ σ).val * Matrix.scalar (Fin r) (χ σ : O)) = _
  rw [map_mul]
  rfl

/-- **The twist of a continuous `ℱ_ρ` by `L_ψ(g)` is continuous**: the Artin–Schreier character
factors through the finite discrete group `𝔽_q`. -/
public theorem continuous_restrictScalarsRepresentation_artinSchreierTwist
    (hρ : Continuous (restrictScalarsRepresentation B (specObject A B hX) x b ρ)) :
    Continuous (restrictScalarsRepresentation B (specObject A B hX) x b
      (characterTwist ρ (artinSchreierCharacter k A g ψ x p₀))) := by
  let : TopologicalSpace (Multiplicative k) := ⊥
  have : DiscreteTopology (Multiplicative k) := ⟨rfl⟩
  have hχ : Continuous fun σ : EtaleFundamentalGroup (specObject A B hX).1 x =>
      Units.map (coefficientScalarRingHom b r).toMonoidHom
        (artinSchreierCharacter k A g ψ x p₀ σ) :=
    (continuous_of_discreteTopology (f := fun m : Multiplicative k =>
      Units.map (coefficientScalarRingHom b r).toMonoidHom (ψ.toMonoidHom.toHomUnits m⁻¹))).comp
      ((torsorCover k A g).continuous_character x p₀)
  have h : ⇑(restrictScalarsRepresentation B (specObject A B hX) x b
      (characterTwist ρ (artinSchreierCharacter k A g ψ x p₀))) = fun σ =>
      restrictScalarsRepresentation B (specObject A B hX) x b ρ σ *
        Units.map (coefficientScalarRingHom b r).toMonoidHom
          (artinSchreierCharacter k A g ψ x p₀ σ) :=
    funext fun σ => restrictScalarsRepresentation_characterTwist A B hX b x ρ _ σ
  rw [h]
  exact hρ.mul hχ

end

/-- **The twist `ℱ_ρ ⊗ L_ψ(g)`** of the `O`-sheaf of a representation
`ρ : π₁(Spec A, x̄) → GL_r(O)` by the Artin–Schreier sheaf `L_ψ(g)`: the `O`-sheaf of
`σ ↦ ψ(-χ_g(σ)) ρ(σ)`. -/
public def artinSchreierTwistSheaf
    (hρ : Continuous (restrictScalarsRepresentation B (specObject A B hX) x b ρ)) :
    LAdicSheaf.CoefficientSheaf B (specObject A B hX) ℓ O :=
  coefficientRepresentationSheaf B (specObject A B hX) x b
    (characterTwist ρ (artinSchreierCharacter k A g ψ x p₀))
    (continuous_restrictScalarsRepresentation_artinSchreierTwist k A g ψ B hX b x p₀ ρ hρ)

/-- **The trace function of `ℱ_ρ ⊗ L_ψ(g)`**: the geometric Frobenius at a closed point `y` acts on
the stalk at `ȳ` with `O`-trace `ψ(Tr_{κ(y)/𝔽_q}(g(y))) · tr ρ(F_y)`, `F_y` the geometric Frobenius
element transported to the base point along a path `t`. -/
public theorem trace_artinSchreierTwistSheaf_frobenius
    (hρ : Continuous (restrictScalarsRepresentation B (specObject A B hX) x b ρ))
    (y : closedPoints (Spec (.of A))) [Finite ((Spec (.of A)).residueField y.1)]
    (t : finiteEtaleFiberFunctor (geometricPointAt _ y.1) ≅ finiteEtaleFiberFunctor x) :
    LinearMap.trace O _ ((artinSchreierTwistSheaf k A g ψ B hX b x p₀ ρ hρ).stalkEnd
        (frobeniusPointHom _ y.1)) =
      ψ (letI := residueAlgebra k A y.1; Algebra.trace k _ (residueRingHom A y.1 g)) *
        (ρ (etaleFundamentalGroupMulEquiv t
          (frobeniusDataOfPath x y t).localElement⁻¹)).val.trace := by
  rw [artinSchreierTwistSheaf, trace_characterTwist_stalkEnd B (specObject A B hX) x b ρ _ _ t
    (frobeniusPointHom _ y.1) _ (inv_localElement_hom x y t)]
  exact congrArg (· * _) (artinSchreierCharacter_frobenius k A g ψ x p₀ y t)

end Stacks.ArtinSchreier
