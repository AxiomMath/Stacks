module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleModuleHomExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.RegularDescentSheaf
public import StacksFrontier.Algebra.Module.Injective.LocallyConstantInjective
public import StacksFrontier.Algebra.Module.Injective.GroupAlgebraSelfInjective
public import StacksFrontier.Algebra.Module.Injective.ZModPrimePower
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# `Hom_{A[H]}(-, D(A[H]))` is exact on finite modules

Let `G : V ⟶ U` be a Galois covering with finite group `H`, `A = ℤ/ℓⁿ` and `D = D(A[H])` the
descent sheaf of the regular representation
(`AlgebraicGeometry.EtaleGaloisCovering.regularDescentSheaf`). Over an étale `U`-scheme `W` which
maps to `V`, the sections of `D` are the locally constant maps `W → A[H]`
(`AlgebraicGeometry.EtaleGaloisCovering.bijective_restrictGraph`), an injective `A[H]`-module
(`Module.injective_locallyConstant`, `A[H]` being self-injective and Noetherian). Every étale `W`
is covered by `W ×_U V`, which maps to `V`. Hence for an injective map `N₁ → N₂` of `A[H]`-modules,
`Hom(N₂, D) → Hom(N₁, D)` is surjective on sections over every `W ×_U V`, and so it is an
epimorphism of sheaves: `D` is locally an injective `A[H]`-module.

This is the local input of the vanishing of the sheaf `Ext^i_{A[H]}(N, D)` for `i > 0`, in Step 7
of the proof of [Stacks, Tag 03UG].

## Main results

* `AlgebraicGeometry.EtaleGaloisCovering.injective_regularDescentSheaf_obj_fiberObj`: the
  sections of `D` over `W ×_U V` form an injective `A[H]`-module.
* `AlgebraicGeometry.EtaleGaloisCovering.epi_etaleModuleHomPrecomp_regularDescentSheaf`: for an
  injective map `v : N₁ → N₂`, `Hom(N₂, D) → Hom(N₁, D)` is an epimorphism of sheaves.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry.EtaleGaloisCovering

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} [NeZero n] {H : Type} [Group H] [Finite H]
  {U : Scheme.{u}} (G : EtaleGaloisCovering U H)

omit [NeZero n] in
/-- **Over `W ×_U V` the sections of `D(A[H])` form an injective `A[H]`-module**: they are the
locally constant maps to `A[H]`. -/
theorem injective_regularDescentSheaf_obj_fiberObj (W : U.Etale) :
    Injective ((G.regularDescentSheaf (A := ZMod (ℓ ^ n))).obj.obj (op (G.fiberObj W))) := by
  have := Fintype.ofFinite H
  let R := MonoidAlgebra (ZMod (ℓ ^ n)) H
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have : Finite R := Module.finite_of_finite (ZMod (ℓ ^ n))
  have : IsNoetherianRing R := isNoetherian_of_finite R R
  have hR : Module.Injective R R :=
    MonoidAlgebra.injective_self Stacks.ZModPrimePower.baer_self
  have : Module.Injective R (ULift.{u + 1} R) := Module.ulift_injective_of_injective _ hR
  let T : Over G.cover := Over.mk (G.fiberObjSnd W)
  let e := LinearEquiv.ofBijective
    (G.restrictGraph R (ULift.{u + 1} R) (rightRegularRepULift.{u} _ H) T)
    (G.bijective_restrictGraph R (ULift.{u + 1} R) (rightRegularRepULift.{u} _ H) T)
  have hb : Module.Baer R (LocallyConstant T.left.left (ULift.{u + 1} R)) :=
    Module.baer_locallyConstant _
  have hinj : Module.Injective R (G.equivariantMaps R (ULift.{u + 1} R)
      (rightRegularRepULift.{u} _ H) T.left) := (hb.of_equiv e.symm).injective
  exact Module.injective_object_of_injective_module (inj := hinj)

omit [NeZero n] in
/-- **`Hom(-, D(A[H]))` carries injections of modules to epimorphisms of sheaves.** -/
theorem epi_etaleModuleHomPrecomp_regularDescentSheaf
    {N₁ N₂ : ModuleCat.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ n)) H)} (v : N₁ ⟶ N₂) [Mono v] :
    Epi ((etaleModuleHomPrecomp (A := ZMod (ℓ ^ n)) v U).app
      (G.regularDescentSheaf (A := ZMod (ℓ ^ n)))) := by
  let D := G.regularDescentSheaf (A := ZMod (ℓ ^ n))
  let φ := (etaleModuleHomPrecomp (A := ZMod (ℓ ^ n)) v U).app D
  have : Sheaf.IsLocallySurjective φ := ⟨fun {W} s => by
    refine (Scheme.smallEtaleTopology U).superset_covering ?_ (G.ofArrows_fiberObjFst_mem W)
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨⟩
    have hI := G.injective_regularDescentSheaf_obj_fiberObj (ℓ := ℓ) (n := n) W
    let s' : N₁ ⟶ D.obj.obj (op (G.fiberObj W)) :=
      (show N₁ ⟶ D.obj.obj (op W) from s) ≫ D.obj.map (G.fiberObjFst W).op
    exact ⟨@Injective.factorThru _ _ _ _ _ hI s' v _,
      @Injective.comp_factorThru _ _ _ _ _ hI s' v _⟩⟩
  exact Sheaf.epi_of_isLocallySurjective φ

end AlgebraicGeometry.EtaleGaloisCovering
