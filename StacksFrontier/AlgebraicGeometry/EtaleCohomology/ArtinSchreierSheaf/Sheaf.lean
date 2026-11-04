module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.CharacterSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.Frobenius
public import Mathlib.Algebra.Group.AddChar

/-!
# The Artin–Schreier sheaf `L_ψ`

Let `k = 𝔽_q`, let `A` be a `k`-algebra with `Spec A` connected and Noetherian, let `g ∈ A`, and
let `ψ : k → O^×` be an additive character with values in a finite free `ℤ_ℓ`-algebra `O` (for
instance `O = ℤ_ℓ[ζ_p]`).  The Artin–Schreier cover `t^q - t = g` is an `𝔽_q`-torsor, whose
character `π₁(Spec A, x̄) → 𝔽_q` composed with `ψ⁻¹` is a continuous character with values in
`O^×`; its rank-one `O`-sheaf is the Artin–Schreier sheaf `L_ψ(g)` (`L_ψ` itself for `A = k[x]`,
`g = x`). It is lisse, its stalks are free of rank one over `O`, and the geometric Frobenius at a
closed point `y` acts on its stalk by the scalar `ψ(Tr_{κ(y)/𝔽_q}(g(y)))`.

## Main definitions

* `Stacks.ArtinSchreier.artinSchreierCharacter`: `σ ↦ ψ(-χ(σ))`, `χ` the character of the cover.
* `Stacks.ArtinSchreier.artinSchreierSheaf`: the `O`-sheaf `L_ψ(g)`.

## Main results

* `Stacks.ArtinSchreier.artinSchreierSheaf_isLisse`.
* `Stacks.ArtinSchreier.artinSchreierSheafStalkEquiv`: the stalk at `ȳ` is `O`.
* `Stacks.ArtinSchreier.artinSchreierSheaf_stalkEnd_frobenius`: the geometric Frobenius at a closed
  point `y` acts on the stalk at `ȳ` as multiplication by `ψ(Tr_{κ(y)/𝔽_q}(g(y)))`.

## References

* [P. Deligne, SGA 4½, Sommes trigonométriques, 1.7]
* [G. Laumon, Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil, 1.1]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.EtaleCohomology
  Stacks.Frobenius

universe u

namespace Stacks.ArtinSchreier

variable (k : Type u) [Field k] [Fintype k] (A : Type u) [CommRing A] [Algebra k A] (g : A)
  [ConnectedSpace (Spec (.of A))]
  {O : Type} [CommRing O] (ψ : AddChar k O)

/-- **The Artin–Schreier character** `σ ↦ ψ(-χ(σ))` of `π₁(Spec A, x̄)`, where `χ` is the
character of the Artin–Schreier cover `t^q - t = g`, read at a point `p₀` of the fibre at `x̄`. -/
public def artinSchreierCharacter (x : GeometricPoint (Spec (.of A)))
    (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g)) :
    EtaleFundamentalGroup (Spec (.of A)) x →* Oˣ :=
  ψ.toMonoidHom.toHomUnits.comp ((torsorCover k A g).character x p₀)⁻¹

/-- The Artin–Schreier character at `σ` is `ψ` of minus the character of the cover at `σ`. -/
public theorem artinSchreierCharacter_apply (x : GeometricPoint (Spec (.of A)))
    (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g)) (σ : EtaleFundamentalGroup _ x) :
    (artinSchreierCharacter k A g ψ x p₀ σ : O) =
      ψ (-Multiplicative.toAdd ((torsorCover k A g).character x p₀ σ)) :=
  rfl

variable (B : BigEtaleSite.{u}) (hX : schemeSizeBelow B.cutoff (Spec (.of A)))

/-- `Spec A` as an object of the big étale site. -/
public abbrev specObject : B.Scheme := ⟨Spec (.of A), hX⟩

variable {ℓ : ℕ} [Fact ℓ.Prime] [Algebra ℤ_[ℓ] O] {d : ℕ} (b : Module.Basis (Fin d) ℤ_[ℓ] O)
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
  [AlgebraicGeometry.IsNoetherian (Spec (.of A))] in
/-- The `ℤ_ℓ`-representation of the Artin–Schreier character is continuous: it factors through
the character of the cover, which is continuous for the discrete topology on `𝔽_q`. -/
public theorem continuous_artinSchreierRepresentation (x : GeometricPoint (Spec (.of A)))
    (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g)) :
    Continuous (characterRepresentation B (specObject A B hX) x b
      (artinSchreierCharacter k A g ψ x p₀)) := by
  let : TopologicalSpace (Multiplicative k) := ⊥
  have : DiscreteTopology (Multiplicative k) := ⟨rfl⟩
  exact (continuous_of_discreteTopology (f := fun m : Multiplicative k =>
      Units.map (Algebra.leftMulMatrix b).toMonoidHom (ψ.toMonoidHom.toHomUnits m⁻¹))).comp
    ((torsorCover k A g).continuous_character x p₀)

/-- **The Artin–Schreier sheaf `L_ψ(g)`** on `Spec A`, an `O`-sheaf of rank one: the sheaf of the
character `ψ(-χ)` of `π₁(Spec A, x̄)`, `χ` the character of the Artin–Schreier cover
`t^q - t = g`. -/
public def artinSchreierSheaf (x : GeometricPoint (Spec (.of A)))
    (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g)) :
    LAdicSheaf.CoefficientSheaf B (specObject A B hX) ℓ O :=
  characterSheaf B (specObject A B hX) x b (artinSchreierCharacter k A g ψ x p₀)
    (continuous_artinSchreierRepresentation k A g ψ B hX b x p₀)

/-- **`L_ψ(g)` is lisse.** -/
public theorem artinSchreierSheaf_isLisse (x : GeometricPoint (Spec (.of A)))
    (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g)) :
    (artinSchreierSheaf k A g ψ B hX b x p₀).toLAdicSheaf.IsLisse :=
  have := additive_canonicalFiniteLocallyConstantAbelianSheafEquivalence B (specObject A B hX) x
  representationLAdicSheaf_isLisse B (specObject A B hX) x
    (canonicalFiniteLocallyConstantAbelianSheafEquivalence B (specObject A B hX) x) _ _

/-- **The stalks of `L_ψ(g)` are free of rank one over `O`**, along a path `t` from `s̄` to the
base point. -/
public def artinSchreierSheafStalkEquiv (x : GeometricPoint (Spec (.of A)))
    (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g)) {s : GeometricPoint (Spec (.of A))}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) :
    LAdicSheaf.stalk B (specObject A B hX) ℓ (artinSchreierSheaf k A g ψ B hX b x p₀).toLAdicSheaf s
      ≃ₗ[O] O :=
  characterSheafStalkLinearEquiv B (specObject A B hX) x b _ _ t

/-- **The geometric Frobenius at a closed point `y` acts on the stalk of `L_ψ(g)` at `ȳ` as
multiplication by `ψ(Tr_{κ(y)/𝔽_q}(g(y)))`.**  The geometric Frobenius is the inverse of the
arithmetic one, which moves the fibre of the cover by `Tr(g(y))`, and `L_ψ(g)` is the sheaf of
`ψ(-χ)`. -/
public theorem artinSchreierSheaf_stalkEnd_frobenius (x : GeometricPoint (Spec (.of A)))
    (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g)) (y : closedPoints (Spec (.of A)))
    [Finite ((Spec (.of A)).residueField y.1)]
    (t : finiteEtaleFiberFunctor (geometricPointAt _ y.1) ≅ finiteEtaleFiberFunctor x) :
    (artinSchreierSheaf k A g ψ B hX b x p₀).stalkEnd (frobeniusPointHom _ y.1) =
      ψ (letI := residueAlgebra k A y.1; Algebra.trace k _ (residueRingHom A y.1 g)) •
        LinearMap.id := by
  let := residueAlgebra k A y.1
  set q₀ : (finiteEtaleFiberFunctor (geometricPointAt _ y.1)).obj (cover k A g) :=
    (t.inv.app (cover k A g)).hom p₀
  have h1 := (torsorCover k A g).character_etaleFundamentalGroupMulEquiv t q₀ p₀
    (frobeniusDataOfPath x y t).localElement⁻¹
  have h2 := character_localElement y x t q₀ (g := g)
  have h3 := MonoidHom.map_inv ((torsorCover k A g).character (geometricPointAt _ y.1) q₀)
    (frobeniusDataOfPath x y t).localElement
  replace h1 := h1.trans h3
  rw [artinSchreierSheaf, characterSheaf_stalkEnd_eq_smul B (specObject A B hX) x b _ _ t
    (frobeniusPointHom _ y.1) _ (inv_localElement_hom x y t), artinSchreierCharacter_apply]
  congr 2
  refine (congrArg (fun m => -Multiplicative.toAdd m) h1).trans ?_
  rw [toAdd_inv, neg_neg]
  exact h2

end Stacks.ArtinSchreier
