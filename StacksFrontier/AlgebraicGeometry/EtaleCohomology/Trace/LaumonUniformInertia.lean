module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibreDualReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.BasePointChangeEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CurvePointInertia

/-!
# The inertia at `∞` of the fibres of the Fourier family, uniformly in the constant field

Let `σ : π₁(U, x̄) → GL_m(E)` be continuous on `U ≅ 𝔸¹_k` and `ψ ≠ 1` an additive character of the
finite field `k`. For a finite extension `k'` of `k`, `a ∈ k'ˣ`, `c ∈ k'`, the fibre of the Fourier
family over `(a, c)` is the representation `τ = σ' ⊗ χ` of `π₁(𝔸¹_{k'}, x̄')`, with `σ'` the
restriction of `σ` and `χ` the Artin–Schreier character of `a xⁿ + c x` for `ψ ∘ Tr_{k'/k}`. This
file states, as the named input `Stacks.EtaleCohomology.LaumonUniformInertiaInput`, that there is
one `N`, independent of `k'`, `a`, `c` and every choice of base points and places, such that for
`n > N` prime to `p` the inertia group at every place at infinity of `𝔸¹_{k'}` fixes no nonzero
vector of `τ` or of its contragredient and has no coinvariants on them.

For a single constant field this is
`Stacks.ArtinSchreier.exists_forall_invariants_eq_bot_and_subsingleton_coinvariants`, whose `N`
comes from a finiteness argument over `K = k(x)` and therefore depends on `k'`. The intended route
to uniformity: the geometric inertia at `∞` is unchanged by the constant extension, `I_{K'} = I_K`
for `K' = k'(x)`, because `K'/K` is unramified at `∞`, so `I ∩ U' = I ∩ U` for the open subgroups
`U' = U ∩ Gal(L/K')` that control `σ`. The Artin–Schreier pole-order argument of
`IsDiscreteValuationRing.exists_forall_exists_mem_inertia_mem_ne` is then redone over `K'`, with
the finitely many classes taken from `K`. Finally `π₁(𝔸¹_{k'}, x̄')`, `π₁(U, x̄)` and
`Stacks.FundamentalGroup.curvePointInertia` are compared across `k'/k` and across the base-point
changes `Stacks.EtaleCohomology.etaleFundamentalGroupBasePointHom`.

This is the uniform bound used by the Poincaré duality on the fibres
(`Stacks.EtaleCohomology.LaumonFibreDualityInput`: no local terms at `∞`) and by the vanishing of
`H²_c` (`Stacks.EtaleCohomology.LaumonFibreTopVanishingInput`: no coinvariants), in the purity
half of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH). The proposition is not registered
and is not a hypothesis of any registered statement.

## Main definitions

* `Stacks.EtaleCohomology.LaumonUniformInertiaInput`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Matrix Stacks.FundamentalGroup

universe u

namespace Stacks.EtaleCohomology

/-- **The inertia at `∞` of the fibres `σ' ⊗ L_ψ(a xⁿ + c x)` of the Fourier family has no
invariants and no coinvariants for `n` large, uniformly in the constant field.** For `σ`
continuous on `U ≅ 𝔸¹_k` and `ψ ≠ 1` there is `N` such that for every `n > N` prime to `p`,
every finite extension `k'` of `k` and geometric point `x̄'` of `𝔸¹_{k'}` over `x̄`, every
`a ≠ 0`, `c` in `k'` and point `p₀` of the Artin–Schreier cover, every isomorphism `t` of fibre
functors from `x̄'` to the geometric generic point `η̄` (built from a separable closure `L` and an
algebraic closure `Ω` of `k'(x)`), and every place `P` over a discrete valuation ring `A` of
`k'(x)` not containing `k'[x]` (a place at `∞`), the inertia group of `P` acting on
`τ = Res_b(σ' ⊗ χ) ∘ φ_t` and on `Res_b((σ' ⊗ χ)^∨) ∘ φ_t` fixes no nonzero vector and has
trivial coinvariants. -/
public def LaumonUniformInertiaInput : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fintype k] (U : Scheme.{u}) [ConnectedSpace U]
    (e : U ⟶ Spec (.of (Polynomial k))) [IsIso e] (p : ℕ) [Fact p.Prime] [CharP k p]
    (x : GeometricPoint U) (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ}
    (σ : EtaleFundamentalGroup U x →* GL (Fin m) E)
    (_ : Continuous (restrictScalarsRep b σ)) (ψ : AddChar k E), ψ ≠ 1 →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ¬ p ∣ n →
    ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k k']
      [ConnectedSpace (Spec (.of (Polynomial k')))] [IrreducibleSpace (Spec (.of (Polynomial k')))]
      (x' : GeometricPoint (Spec (.of (Polynomial k'))))
      (hx' : x'.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫
        inv e) = x)
      (a c : k'), a ≠ 0 →
      ∀ (p₀ : (finiteEtaleFiberFunctor x').obj (Stacks.ArtinSchreier.cover k' (Polynomial k')
          (Polynomial.C a * Polynomial.X ^ n + Polynomial.C c * Polynomial.X)))
        (L Ω : Type u) [Field L] [Field Ω]
        [Algebra ((Spec (.of (Polynomial k'))).residueField
          (genericPoint (Spec (.of (Polynomial k'))))) L]
        [IsSepClosure ((Spec (.of (Polynomial k'))).residueField
          (genericPoint (Spec (.of (Polynomial k'))))) L]
        [Algebra L Ω] [Algebra ((Spec (.of (Polynomial k'))).residueField
          (genericPoint (Spec (.of (Polynomial k'))))) Ω]
        [IsScalarTower ((Spec (.of (Polynomial k'))).residueField
          (genericPoint (Spec (.of (Polynomial k'))))) L Ω] [IsAlgClosed Ω]
        [Algebra.IsAlgebraic ((Spec (.of (Polynomial k'))).residueField
          (genericPoint (Spec (.of (Polynomial k'))))) Ω]
        (t : finiteEtaleFiberFunctor x' ≅ finiteEtaleFiberFunctor ((algebraicClosureGeometricPoint
          ((Spec (.of (Polynomial k'))).residueField
            (genericPoint (Spec (.of (Polynomial k'))))) Ω).map
            ((Spec (.of (Polynomial k'))).fromSpecResidueField
              (genericPoint (Spec (.of (Polynomial k')))))))
        (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
        [Algebra A ((Spec (.of (Polynomial k'))).residueField
          (genericPoint (Spec (.of (Polynomial k')))))]
        [IsFractionRing A ((Spec (.of (Polynomial k'))).residueField
          (genericPoint (Spec (.of (Polynomial k')))))] [Algebra A L]
        [IsScalarTower A ((Spec (.of (Polynomial k'))).residueField
          (genericPoint (Spec (.of (Polynomial k'))))) L]
        (P : Ideal (integralClosure A L)) [P.IsMaximal],
        (∃ g : Γ(Spec (.of (Polynomial k')), ⊤),
          ((Spec (.of (Polynomial k'))).evaluation ⊤ (genericPoint (Spec (.of (Polynomial k'))))
            trivial).hom g ∉ Set.range (algebraMap A ((Spec (.of (Polynomial k'))).residueField
              (genericPoint (Spec (.of (Polynomial k'))))))) →
        Representation.invariants ((matrixRepresentation ((restrictScalarsRep b (characterTwist
            (σ.comp (hx' ▸ (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom
              (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) x').toMonoidHom))
            (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial k')
              (Polynomial.C a * Polynomial.X ^ n + Polynomial.C c * Polynomial.X)
              (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) x' p₀))).comp
            (etaleFundamentalGroupBasePointHom t).toMonoidHom)).comp
          (curvePointInertia (Spec (.of (Polynomial k'))) L Ω A P).subtype) = ⊥ ∧
        Subsingleton (Representation.Coinvariants ((matrixRepresentation ((restrictScalarsRep b
            (characterTwist
            (σ.comp (hx' ▸ (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom
              (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) x').toMonoidHom))
            (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial k')
              (Polynomial.C a * Polynomial.X ^ n + Polynomial.C c * Polynomial.X)
              (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) x' p₀))).comp
            (etaleFundamentalGroupBasePointHom t).toMonoidHom)).comp
          (curvePointInertia (Spec (.of (Polynomial k'))) L Ω A P).subtype)) ∧
        Representation.invariants ((matrixRepresentation ((restrictScalarsRep b (contragredient
            (characterTwist
            (σ.comp (hx' ▸ (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom
              (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) x').toMonoidHom))
            (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial k')
              (Polynomial.C a * Polynomial.X ^ n + Polynomial.C c * Polynomial.X)
              (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) x' p₀)))).comp
            (etaleFundamentalGroupBasePointHom t).toMonoidHom)).comp
          (curvePointInertia (Spec (.of (Polynomial k'))) L Ω A P).subtype) = ⊥ ∧
        Subsingleton (Representation.Coinvariants ((matrixRepresentation ((restrictScalarsRep b
            (contragredient (characterTwist
            (σ.comp (hx' ▸ (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom
              (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) x').toMonoidHom))
            (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial k')
              (Polynomial.C a * Polynomial.X ^ n + Polynomial.C c * Polynomial.X)
              (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) x' p₀)))).comp
            (etaleFundamentalGroupBasePointHom t).toMonoidHom)).comp
          (curvePointInertia (Spec (.of (Polynomial k'))) L Ω A P).subtype))

end Stacks.EtaleCohomology

end
