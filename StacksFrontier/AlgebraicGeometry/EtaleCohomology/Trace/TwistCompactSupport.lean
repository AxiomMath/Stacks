module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientChangeCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistFunctorAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GroupRingSelfInjective

/-!
# Compactly supported cohomology of a twisted sheaf

Let `ℓ` be a prime, `k₀ = ℤ/ℓᴹ`, `G` a finite group, `R = k₀[G]`, `Λ` a commutative `k₀`-algebra,
`E` a finite `Λ`-module with a `Λ`-linear action of `G` and `Ψ = Hom_R(E^∨, -)` the twist functor
(`Stacks.EtaleCohomology.twistFunctor`).  For a bounded below complex `K` of sheaves of
`R`-modules on `X` whose terms are `Ψ`-acyclic, and a bounded below complex `Q` of projective
`R`-modules with `Q ≅ RΓ_c(X_k̄, K)` and a chain endomorphism `g` representing `π_X^*`, there is
an isomorphism `Ψ(Q) ≅ RΓ_c(X_k̄, Ψ K)` carrying `Ψ(g)` to `π_X^*`.

This is `Stacks.EtaleCohomology.exists_iso_compactSupport_coefficientChange` for `Ψ`, with its
acyclicity hypotheses discharged: `(j_! K)|_{X̄_k̄}` has `Ψ`-acyclic terms because extension by
zero and inverse image preserve `Ψ`-acyclicity, `Ψ` carries injective sheaves to sheaves acyclic
everywhere, and projective `R`-modules are injective (`R` is self-injective).  It is step 6 of the
proof of [Tag 03UZ], with `K = 𝒫_M` on a stratum.

## Main results

* `Stacks.EtaleCohomology.exists_iso_compactSupport_twistFunctor`

## References

* [Stacks Project, Tag 03UZ](https://stacks.math.columbia.edu/tag/03UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (ℓ M : ℕ) [Fact ℓ.Prime] (G : Type) [Group G] [Fintype G] (Λ : Type) [CommRing Λ]
  [Algebra (ZMod (ℓ ^ M)) Λ] (E : Type (u + 1)) [AddCommGroup E] [Module Λ E]
  [Module (ZMod (ℓ ^ M)) E] [IsScalarTower (ZMod (ℓ ^ M)) Λ E] (ρ : Representation Λ G E)
  [Finite E]
  {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **`Ψ(Q) ≅ RΓ_c(X_k̄, Ψ K)` carrying `Ψ(g)` to `π_X^*`**, for the twist functor
`Ψ = Hom_{k₀[G]}(E^∨, -)`, a bounded below complex `K` of sheaves of `k₀[G]`-modules with
`Ψ`-acyclic terms and a bounded below complex `Q` of projective `k₀[G]`-modules with
`e_M : Q ≅ RΓ_c(X_k̄, K)` and a chain endomorphism `g` of `Q` representing `π_X^*`. -/
theorem exists_iso_compactSupport_twistFunctor
    (K : CochainComplex.Plus (EtaleModules.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) G) X))
    (hK : ∀ n, (sheafCompose X.smallEtaleTopology
      (twistFunctor (ZMod (ℓ ^ M)) G Λ E ρ)).rightAcyclic (K.obj.X n))
    (Q : CochainComplex (ModuleCat.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) G)) ℤ)
    (hQ : CochainComplex.plus _ Q) (hQp : ∀ i, Projective (Q.X i)) (g : Q ⟶ Q)
    (eM : DerivedCategory.Q.obj Q ≅
      DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, 0} _ f j kbar K))
    (hg : DerivedCategory.Q.map g = eM.hom ≫
      DerivedCategory.Plus.ι.map (canonicalCompactSupportFrobenius.{u, 0} _ f j kbar p q hcard K) ≫
        eM.inv) :
    ∃ e : DerivedCategory.Q.obj
        (((twistFunctor (ZMod (ℓ ^ M)) G Λ E ρ).mapHomologicalComplex _).obj Q) ≅
        DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar
          ((sheafCompose X.smallEtaleTopology
            (twistFunctor (ZMod (ℓ ^ M)) G Λ E ρ)).mapCochainComplexPlus.obj K)),
      DerivedCategory.Q.map
          (((twistFunctor (ZMod (ℓ ^ M)) G Λ E ρ).mapHomologicalComplex _).map g) ≫
          e.hom =
        e.hom ≫ DerivedCategory.Plus.ι.map (canonicalCompactSupportFrobenius.{u, 0} Λ f j kbar p q
          hcard ((sheafCompose X.smallEtaleTopology
            (twistFunctor (ZMod (ℓ ^ M)) G Λ E ρ)).mapCochainComplexPlus.obj K)) := by
  have : NeZero (ℓ ^ M) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have := isIso_extensionByZeroMate_twistFunctor (ZMod (ℓ ^ M)) G Λ E ρ j.immersion
  have := isIso_inverseImageMate_twistFunctor (ZMod (ℓ ^ M)) G Λ E ρ
    (fieldBaseChangeProj (Over.mk j.toBase) kbar)
  exact exists_iso_compactSupport_coefficientChange (twistFunctor (ZMod (ℓ ^ M)) G Λ E ρ) f j kbar
    p q hcard K
    (fun n => rightAcyclic_twistFunctor_inverseImage ℓ M G Λ E ρ _ _
      (rightAcyclic_twistFunctor_extensionByZero ℓ M G Λ E ρ j.immersion _ (hK n)))
    (fun I hI => have := hI; isAcyclicEverywhere_twistFunctor_obj ℓ M G Λ E ρ I)
    Q hQ (fun i => have := injective_of_projective_groupRing G (Q.X i)
      Functor.rightAcyclic_of_injective _ _) g eM hg

end Stacks.EtaleCohomology

end
