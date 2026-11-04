module

public import Mathlib.RingTheory.Ideal.Colon
public import StacksFrontier.AlgebraicGeometry.Duality.IdentityKernelNaturalPullback
public import StacksFrontier.AlgebraicGeometry.Duality.IdentityKernelSectionRigidity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.TestModuleStalk

/-!
# The identity kernel pins the local ring at a closed point

Let `X` be smooth and proper over a field `k`, let `K` be an object of `D(𝒪_{X ×_k X})`
representing the identity on `D_perf(𝒪_X)`, and let `s` be a section of the second projection
with `K ≅ Rs_*𝒪_X`.  Writing `g = pr_1 ∘ s`, the last step of the proof of [Stacks, Tag 0G0E]
needs `g = 𝟙 X`, and
`AlgebraicGeometry.comp_fst_eq_id_of_forall_closedPoint_fromSpecResidueField` reduces that to:
for every closed point `x`, `g` leaves `Spec κ(x) ⟶ X` unchanged.  Since
`AlgebraicGeometry.base_comp_fst_eq_self_of_representsIdentityOnPerfect` already gives
`g(x) = x`, what is left is the comorphism at `x`: the local homomorphism
`g^♯_x : 𝒪_{X,x} ⟶ 𝒪_{X,x}` must induce the identity of `κ(x)`.

This file settles the first half of that and isolates the second.

*The ideal.*  `g^♯_x(𝔪_x)·𝒪_{X,x} = 𝔪_x`.  This is unconditional under the hypotheses of
Tag 0G0E together with `K ≅ Rs_*𝒪_X`, and it is what rules out the absolute Frobenius of
`𝔸^1_{𝔽_p}`, whose comorphism `t ↦ t^p` has
`g^♯(𝔪_0)·𝒪 = 𝔪_0^p ≠ 𝔪_0`.  The proof reads the isomorphism `g^*ℱ ≅ ℱ` of
`Stacks.Duality.nonempty_natIso_pullback_coherentObjects_of_representsIdentityOnPerfect` at the
test module `ℱ = 𝒪_X/𝔪_x`, whose two stalks at `x` are
`AlgebraicGeometry.pointTestModuleStalkEquiv`'s `𝒪_{X,x}/𝔪_x` and
`AlgebraicGeometry.pullbackPointTestModuleStalkEquiv`'s `𝒪_{X,x}/(g^♯𝔪_x·𝒪_{X,x})`; isomorphic
modules have the same annihilator, and the annihilator of a cyclic module `A/I` is `I`.

*The residue map.*  `g^♯_x(a) ≡ a mod 𝔪_x` does **not** follow from the ideal: over
`Spec 𝔽_4`, smooth and proper over `𝔽_2`, the Frobenius has `𝔪_x = 0` and every `g^*ℱ ≅ ℱ`
holds.  What forces it is the naturality square of the isomorphism of functors at the
endomorphisms "multiplication by `c`" of `𝒪_X/𝔪_x`, and
`Stacks.Duality.quotient_mk_eq_of_linearEquiv_smul_comp` is that implication in the form of
commutative algebra.  That route is not the one finally taken: realizing `κ(x)` inside
`End_{𝒪_X}(𝒪_X/𝔪_x)` is not needed, because naturality at the morphisms *out of* `𝒪_X` — the
global sections of the test module, which on a one-point closed subscheme exhaust its stalk —
already pins the residue map.  See
`Stacks.Duality.residue_stalkMap_germ_eq_of_natIso` of
`StacksFrontier/AlgebraicGeometry/Duality/IdentityKernelComorphism.lean`, which proves
`g^♯_x(a) ≡ a mod 𝔪_x` outright, and
`Stacks.Duality.comp_fst_eq_id_of_representsIdentityOnPerfect`, which concludes `pr_1 ∘ s = 𝟙`.

## Main results

* `Stacks.Duality.quotient_mk_eq_of_linearEquiv_smul_comp` — an `A`-linear self-equivalence of
  `A/I` intertwining multiplication by `σ c` with multiplication by `c` forces `σ` to be the
  identity on `A/I`.  No geometry.
* `Stacks.Duality.fromSpecResidueField_comp_eq_of_stalkMap_residue` — a self-map fixing `x` and
  inducing the canonical identification of `κ(x)` leaves `Spec κ(x) ⟶ X` unchanged; this is what
  `AlgebraicGeometry.comp_fst_eq_id_of_forall_closedPoint_fromSpecResidueField` consumes.
* `Stacks.Duality.stalkMapMaximalIdeal_eq_maximalIdeal_of_iso_pullback_pointTestModule` — the
  annihilator argument, for an arbitrary self-map of a locally Noetherian scheme fixing a closed
  point and pulling the test module there back to itself.
* `Stacks.Duality.stalkMapMaximalIdeal_comp_fst_eq_of_representsIdentityOnPerfect` — the same
  under the hypotheses of [Stacks, Tag 0G0E]: `g^♯(𝔪_x)·𝒪_{X,x} = 𝔪_x` at every closed point.

## References

* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace Stacks.Duality

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### The residue field of a semilinear self-equivalence of `A/I` -/

/-- **An `A`-linear self-equivalence of `A/I` intertwining multiplication by `σ c` with
multiplication by `c` forces `σ` to be the identity on `A/I`.**

This is the piece of commutative algebra that the naturality of an isomorphism `g^* ≅ 𝟭`
supplies and the mere existence of isomorphisms `g^*ℱ ≅ ℱ` does not: the hypothesis is the
naturality square at the endomorphisms "multiplication by `c`" of `A/I`, and the conclusion is
that the residue map of `σ` is the identity.  With `A = 𝒪_{X,x}` and `I = 𝔪_x` it says that the
residue field map of a morphism at a closed point is the identity.

Both sides of the square are `A`-linear, so the hypothesis and the `A`-linearity of `Θ` together
read `σ c • z = c • z` for every `z` in the image of `Θ`, which is everything. -/
theorem quotient_mk_eq_of_linearEquiv_smul_comp {A : Type*} [CommRing A] (I : Ideal A)
    (σ : A →+* A) (Θ : (A ⧸ I) ≃ₗ[A] (A ⧸ I))
    (hΘ : ∀ (c : A) (y : A ⧸ I), Θ (σ c • y) = c • Θ y) (a : A) :
    Ideal.Quotient.mk I (σ a) = Ideal.Quotient.mk I a := by
  have h := hΘ a (Θ.symm 1)
  rw [map_smul, Θ.apply_symm_apply] at h
  simpa [Algebra.smul_def] using h

/-! ### From the residue map at a point to the morphism out of `Spec κ(x)` -/

/-- **A self-map fixing a point and inducing the canonical identification of its residue field
leaves `Spec κ(x) ⟶ X` unchanged.**  The hypothesis is stated on the stalk rather than on the
residue field because that is the form a module-theoretic computation at `x` produces; the two
are the same statement, `X.residue _` being an epimorphism.

This is the input that
`AlgebraicGeometry.comp_fst_eq_id_of_forall_closedPoint_fromSpecResidueField` consumes, one
closed point at a time. -/
theorem fromSpecResidueField_comp_eq_of_stalkMap_residue {X : Scheme.{u}} (g : X ⟶ X) (x : X)
    (hgx : g.base x = x)
    (h : g.stalkMap x ≫ X.residue x =
      X.residue (g.base x) ≫ (X.residueFieldCongr hgx).hom) :
    X.fromSpecResidueField x ≫ g = X.fromSpecResidueField x := by
  have hmap : g.residueFieldMap x = (X.residueFieldCongr hgx).hom := by
    rw [← cancel_epi (X.residue (g.base x)), Scheme.residue_residueFieldMap, h]
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, hmap]
  exact X.residueFieldCongr_fromSpecResidueField hgx

/-! ### The maximal ideal at a closed point is carried onto itself -/

/-- **A self-map pulling the test module at a closed point back to itself carries the maximal
ideal onto the maximal ideal.** -/
theorem stalkMapMaximalIdeal_eq_maximalIdeal_of_iso_pullback_pointTestModule
    {X : Scheme.{u}} [IsLocallyNoetherian X] (g : X ⟶ X) (x : X)
    (hx : IsClosed ({x} : Set X)) (hgx : g.base x = x)
    (e : (Scheme.Modules.pullback g).obj (pointTestModule (g.base x) 1) ≅
      pointTestModule x 1) :
    AlgebraicGeometry.stalkMapMaximalIdeal g x =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  have hx' : IsClosed ({g.base x} : Set X) := by rwa [hgx]
  have E1 := AlgebraicGeometry.pullbackPointTestModuleStalkEquiv g x hx' (t := 1) one_ne_zero
  have E2 := AlgebraicGeometry.pointTestModuleStalkEquiv x hx (t := 1) one_ne_zero
  have E3 := ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapIso e).toLinearEquiv
  have E : (X.presheaf.stalk x ⧸ AlgebraicGeometry.stalkMapMaximalIdeal g x ^ 1) ≃ₗ[
      X.presheaf.stalk x]
      (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 1) :=
    E1.symm.trans (E3.trans E2)
  have := E.annihilator_eq
  rw [Ideal.annihilator_quotient, Ideal.annihilator_quotient, pow_one, pow_one] at this
  exact this

/-- **The comorphism of `pr_1 ∘ s` carries the maximal ideal of a closed point onto itself.** -/
theorem stalkMapMaximalIdeal_comp_fst_eq_of_representsIdentityOnPerfect
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [IsProper f]
    (K : DerivedCategory (Limits.pullback f f).Modules) (hΦ : RepresentsIdentityOnPerfect f K)
    (s : X ⟶ Limits.pullback f f) (hsnd : s ≫ Limits.pullback.snd f f = 𝟙 X)
    (eK : K ≅ (dpush s).obj (derivedUnitObject X))
    (x : X) (hx : IsClosed ({x} : Set X)) :
    AlgebraicGeometry.stalkMapMaximalIdeal (s ≫ Limits.pullback.fst f f) x =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  have : IsNoetherian (Spec (CommRingCat.of k)) :=
    isNoetherian_Spec.mpr (inferInstanceAs (IsNoetherianRing k))
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have hgx : (s ≫ Limits.pullback.fst f f).base x = x :=
    AlgebraicGeometry.base_comp_fst_eq_self_of_representsIdentityOnPerfect f K hΦ s hsnd eK x
  refine (nonempty_natIso_pullback_coherentObjects_of_representsIdentityOnPerfect
    f K hΦ s hsnd eK).elim fun θ => ?_
  have hQ : coherentObjects X
      (AlgebraicGeometry.pointTestModule ((s ≫ Limits.pullback.fst f f).base x) 1) :=
    AlgebraicGeometry.isCoherent_pointTestModule _ 1
  exact stalkMapMaximalIdeal_eq_maximalIdeal_of_iso_pullback_pointTestModule
    (s ≫ Limits.pullback.fst f f) x hx hgx
    (θ.app ⟨_, hQ⟩ ≪≫ eqToIso (congrArg (fun y => AlgebraicGeometry.pointTestModule y 1) hgx))

end Stacks.Duality

end
