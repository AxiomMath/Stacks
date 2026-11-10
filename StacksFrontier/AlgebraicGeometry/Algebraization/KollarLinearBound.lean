module

public import StacksFrontier.AlgebraicGeometry.Algebraization.GlobalSectionsMapNaturality
public import StacksFrontier.AlgebraicGeometry.Algebraization.PuncturedSpectrumPicardInjectivitySGA2
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistZero
public import StacksFrontier.AlgebraicGeometry.Algebraization.PuncturedSectionsInputs
public import StacksFrontier.AlgebraicGeometry.Algebraization.UnitSectionMultiplication
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleEulerFormula
public import StacksFrontier.RingTheory.Dualizing.ExtFiniteLengthFromLocalCohomology
public import StacksFrontier.RingTheory.Dualizing.ExtKollarBound
public import StacksFrontier.RingTheory.Dualizing.ExtQuotientSupportKollar
public import StacksFrontier.RingTheory.Length.SmulPowQuotient

import all StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleInvertible

/-!
# Kollár's linear bound for the Euler characteristics of the negative twists

Let `(A, 𝔪)` be a Noetherian local ring of depth at least three carrying a normalized dualizing
complex `ω`, let `f ∈ 𝔪` be a nonzerodivisor, and assume the fourth condition of
[Stacks, Tag 0F2B]: every prime `𝔭 ∋ f` with `dim(A/𝔭) = 2` satisfies `depth(A_𝔭) ≥ 2`. Let
`T = (ℒ, 𝒪_{X₀}, λ)` be an invertible coherent triple for `(A, f)` whose closed-fibre member is
the structure sheaf. This file proves the last step of [Stacks, Tag 0F2B]: the Euler
characteristics of the negative twists of the unit triple by `T`,

`χ(n) = χ(𝒪_U ⊗ ℒ^{⊗ n}, 𝒪_{X₀}, …)`,

satisfy `χ(-n) ≤ c · n` for a constant `c` and every `n : ℕ`.

## The argument

Write `S k` for the `k`-th twist of the unit triple, `M k = Γ(U, (S k).F)` and
`N k = Γ(U₀, (S k).F₀)` for the two modules of global sections, and
`ρ k : M k → N k` for the canonical map between them.

1. By [Stacks, Tag 0F28] the Euler characteristic of `S k` is the length of `N k / ρ k (M k)`.
2. A global section of `ℒ` and its closed-fibre partner give, for every `k`, a morphism of
   triples `S k ⟶ S (k + 1)`, hence a commuting square between the maps `ρ k` and `ρ (k+1)`.
   Composing `n` of those squares produces `ν n : N (-n) → N 0` and `τ n : M (-n) → M 0` with
   `ν n ∘ ρ (-n) = ρ 0 ∘ τ n`.
3. Kollár's length bound
   `Dualizing.length_quotient_range_le_length_quotient_range_objExtPrecomp` turns that into
   `length (N(-n)/ρ(-n)) ≤ length (Ext^{-2}(N(-n), ω) / im Ext^{-2}(ν n))`, the vanishing of
   `Ext^{-2}(M 0, ω)` being Hartogs for the structure sheaf of the punctured spectrum.
4. Subadditivity of colength along a composite (`Module.length_quotient_range_comp_le`) bounds
   the right-hand side by the sum of the `n` colengths of the duals of the single steps.
5. Each step is, up to isomorphisms, one endomorphism `τ` of the structure sheaf of the closed
   fibre, so all `n` summands are equal; and a colength does not change when the map is composed
   with bijections.
6. The common summand is finite. The global sections over the punctured closed fibre are a copy
   of `A/fA`, so `τ` acts there as multiplication by a scalar `a : A`, and the summand is the
   length of `Ext^{-2}(A/fA, ω) / a·Ext^{-2}(A/fA, ω)`. By [Stacks, Tag 0F2B] the support of
   `Ext^{-2}(A/fA, ω)` is the closed point together with finitely many primes `𝔭 ∋ f` with
   `dim(A/𝔭) = 1`, so the summand is finite as soon as `a` avoids those finitely many primes.
7. Such a section exists. The cokernel of `ρ` for the triple `T` itself has finite length, so the
   image of `ρ`, pulled back to an ideal of `A`, is contained in no prime of the support other
   than the closed point; prime avoidance produces a global section whose image avoids all of
   them at once.

Step 7 is where this development parts from the source, which chooses the section by
[Stacks, Tag 0F20] on the quasi-affine punctured spectrum, arranging it to be nonvanishing at the
finitely many bad primes, and then transports the nonvanishing to the closed fibre through the
triple's gluing isomorphism. That route is available but longer: what the bound needs is not that
the section is nowhere vanishing on those primes as a section of `ℒ`, but only that the scalar it
induces on `A/fA` avoids them, and finite length of the cokernel of the canonical map on global
sections — [Stacks, Tag 0F28] — gives that directly.

## Main definitions

* `Stacks.Algebraization.unitTwistZ`, `Stacks.Algebraization.unitTwistZRestrict`,
  `Stacks.Algebraization.unitTwistZStep` and
  `Stacks.Algebraization.unitTwistZRestrictStep`: the twists `S k` of the unit triple, the
  restriction of their closed-fibre members to the punctured closed fibre, the multiplication
  morphism `S k ⟶ S (k + 1)` attached to a section pair, and the map it induces on global
  sections.

## Main results

* `Module.length_quotient_range_comp_bijective`: a colength is unchanged by composing with
  bijections.
* `Dualizing.length_quotient_range_le_mul_of_chain`: **steps 2 to 4**, as a statement about an
  abstract chain of maps of depth-two modules.
* `Stacks.Algebraization.exists_endo_eq_conj_tensorModulesMap_id_mulSectionPowScheme` and
  `Stacks.Algebraization.length_quotient_range_objExtPrecomp_sectionsMap_conj`: **step 5**.
* `Stacks.Algebraization.exists_nat_length_quotient_range_objExtPrecomp_le_of_notMem`:
  **step 6**.
* `Stacks.Algebraization.exists_notMem_of_isFiniteLength_quotient_range`: **step 7**.
* `Stacks.Algebraization.eulerCharacteristic_unitTwistZ_neg_le_of_length_step_le`: the geometric
  assembly of steps 1 to 4, taking the uniform bound on the steps as a hypothesis.
* `Stacks.Algebraization.exists_linear_bound_eulerCharacteristic_twistZ_neg`: **the bound.**

## Implementation notes

The chain of steps 2 to 4 is proved as a statement about two families `MM NN : ℤ → Type u` of
`A`-modules rather than about the modules of global sections themselves. That is what makes the
instance bookkeeping possible: the `A`-module structure on `Γ(F, ⊤)` is supplied by
`Stacks.Algebraization.puncturedSectionsModule` and
`Stacks.Algebraization.puncturedClosedFibreSectionsModule`, which are not instances, so a `letI`
is needed for each module separately and cannot be given uniformly in `k` -- whereas
`[∀ k, Module A (MM k)]` is a perfectly good instance binder. The index juggling of the induction
is confined to the hypothesis `hstep`, which is stated for an arbitrary pair `k, k'` with
`k + 1 = k'` and so can be `subst`ed by its supplier.

The degree `k` of a step is invisible because
`Stacks.Algebraization.exists_iso_tensorModulesMap_id_mulSectionPowScheme_unit` makes every
multiplication map on the integer tensor powers of the structure sheaf a conjugate of one
endomorphism. Its hypothesis is that the twisting module *is* the structure sheaf, which `hF₀`
supplies, and it is consumed through a `subst`: the conjugating isomorphisms it produces in
different degrees are unrelated, which is exactly what a colength computation needs.

`AlgebraicGeometry.Scheme.unitModule X` and `Stacks.Ample.unitModule X` are the same module, but
only definitionally -- the first is a `def` and the second an `abbrev` for
`SheafOfModules.unit X.ringCatSheaf`. A goal mentioning
`Scheme.Modules.unitHomEquivTop`, whose target is spelled at the first, is therefore not
type-correct at the transparency at which `rw` checks its motive, and the two places where the
section attached to `x₀` has to be moved past a functor are written as `congrArg` of an explicitly
typed function instead.

## References

* [Stacks Project, Lemma 0F2B](https://stacks.math.columbia.edu/tag/0F2B)
* [Stacks Project, Lemma 0F28](https://stacks.math.columbia.edu/tag/0F28)
* [Stacks Project, Lemma 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 0DWZ](https://stacks.math.columbia.edu/tag/0DWZ)
* [Stacks Project, Tag 090R](https://stacks.math.columbia.edu/tag/090R)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing Opposite
open Stacks.RelativeVeryAmple

open scoped Pointwise

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Module

/-- **Colength is unchanged by composing with bijections.** For `α : Q →ₗ[A] P` bijective and
`β : S →ₗ[A] R` surjective, the image of `α ∘ₗ g ∘ₗ β` is the image of `LinearMap.range g` under
`α`, so the two quotients are isomorphic and have the same length. -/
public theorem length_quotient_range_comp_bijective {A : Type*} [CommRing A]
    {P Q R S : Type*} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    [AddCommGroup R] [Module A R] [AddCommGroup S] [Module A S]
    (α : Q →ₗ[A] P) (hα : Function.Bijective α) (g : R →ₗ[A] Q) (β : S →ₗ[A] R)
    (hβ : Function.Surjective β) :
    Module.length A (P ⧸ LinearMap.range (α ∘ₗ g ∘ₗ β)) =
      Module.length A (Q ⧸ LinearMap.range g) := by
  have hr : LinearMap.range (g ∘ₗ β) = LinearMap.range g := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hβ, Submodule.map_top]
  exact ((Submodule.Quotient.equiv (LinearMap.range g) (LinearMap.range (α ∘ₗ g ∘ₗ β))
    (LinearEquiv.ofBijective α hα) (by rw [LinearMap.range_comp, hr]; rfl)).length_eq).symm

end Module

namespace Dualizing

/-- **The colength of a chain of maps of depth-two modules grows at most linearly.** Let `MM` and
`NN` be families of finite `A`-modules indexed by `ℤ` and `ρ k : MM k →ₗ[A] NN k` a family of maps
to which Kollár's bound
`Dualizing.length_quotient_range_le_length_quotient_range_objExtPrecomp` applies in every degree,
and suppose each step of the chain -- a commuting square from `ρ k` to `ρ k'` for `k + 1 = k'` --
has dual colength at most `c`. Then the cokernel of `ρ (-n)` has length at most `n · c`.

The composite of the first `n` steps, dualised, is a composite of `n` maps whose colengths add up
subadditively (`Module.length_quotient_range_comp_le`), which is the induction; Kollár's bound
then compares that colength with the one actually wanted. The vanishing hypothesis `hM0` is used
only in degree `0`, where it is the vanishing of `Ext_A^{-2}` of the global sections of the
structure sheaf. -/
public theorem length_quotient_range_le_mul_of_chain
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω) (f : A)
    (MM NN : ℤ → Type u)
    [∀ k, AddCommGroup (MM k)] [∀ k, Module A (MM k)]
    [∀ k, AddCommGroup (NN k)] [∀ k, Module A (NN k)]
    [∀ k, Module.Finite A (MM k)] [∀ k, Module.Finite A (NN k)]
    (ρ : ∀ k, MM k →ₗ[A] NN k) (c : ℕ∞)
    (hMreg : ∀ k, IsSMulRegular (MM k) f)
    (hdM : ∀ k, 2 ≤ Module.depth A (IsLocalRing.maximalIdeal A) (MM k))
    (hdN : ∀ k, 2 ≤ Module.depth A (IsLocalRing.maximalIdeal A) (NN k))
    (hExtM : ∀ k, IsFiniteLength A (Dualizing.moduleExtInto (MM k) ω (-2)))
    (hM0 : Subsingleton (Dualizing.moduleExtInto (MM 0) ω (-2)))
    (hker : ∀ k, LinearMap.ker (ρ k) = f • (⊤ : Submodule A (MM k)))
    (hQ : ∀ k, IsFiniteLength A (NN k ⧸ LinearMap.range (ρ k)))
    (hstep : ∀ k k' : ℤ, k + 1 = k' →
      ∃ (sk : NN k →ₗ[A] NN k') (tk : MM k →ₗ[A] MM k'),
        sk ∘ₗ ρ k = ρ k' ∘ₗ tk ∧
          Module.length A (Dualizing.moduleExtInto (NN k) ω (-2) ⧸
            LinearMap.range (Dualizing.objExtPrecomp (ModuleCat.ofHom sk) ω (-2))) ≤ c)
    (n : ℕ) :
    Module.length A (NN (-(n : ℤ)) ⧸ LinearMap.range (ρ (-(n : ℤ)))) ≤ (n : ℕ∞) * c := by
  have key : ∀ m : ℕ, ∃ (ν : NN (-(m : ℤ)) →ₗ[A] NN 0) (tau : MM (-(m : ℤ)) →ₗ[A] MM 0),
      ν ∘ₗ ρ (-(m : ℤ)) = ρ 0 ∘ₗ tau ∧
      Module.length A (Dualizing.moduleExtInto (NN (-(m : ℤ))) ω (-2) ⧸
        LinearMap.range (Dualizing.objExtPrecomp (ModuleCat.ofHom ν) ω (-2))) ≤ (m : ℕ∞) * c := by
    intro m
    induction m with
    | zero =>
      simp only [Nat.cast_zero, zero_mul]
      refine ⟨LinearMap.id, LinearMap.id, by simp, ?_⟩
      have htop : LinearMap.range (Dualizing.objExtPrecomp
          (ModuleCat.ofHom (LinearMap.id (R := A) (M := NN 0))) ω (-2)) = ⊤ := by
        rw [ModuleCat.ofHom_id, Dualizing.objExtPrecomp_id, LinearMap.range_id]
      rw [htop]
      have : Subsingleton (Dualizing.moduleExtInto (NN 0) ω (-2) ⧸
          (⊤ : Submodule A (Dualizing.moduleExtInto (NN 0) ω (-2)))) :=
        Submodule.Quotient.subsingleton_iff.mpr rfl
      exact le_of_eq (Module.length_eq_zero (R := A))
    | succ m ih =>
      obtain ⟨ν, tau, hsq, hbd⟩ := ih
      obtain ⟨sk, tk, hsqs, hcs⟩ := hstep (-((m + 1 : ℕ) : ℤ)) (-(m : ℤ)) (by push_cast; ring)
      refine ⟨ν ∘ₗ sk, tau ∘ₗ tk, ?_, ?_⟩
      · rw [LinearMap.comp_assoc, hsqs, ← LinearMap.comp_assoc, hsq, LinearMap.comp_assoc]
      · rw [ModuleCat.ofHom_comp, Dualizing.objExtPrecomp_comp]
        refine le_trans (Module.length_quotient_range_comp_le _ _) ?_
        calc Module.length A (Dualizing.moduleExtInto (NN (-(m : ℤ))) ω (-2) ⧸
                LinearMap.range (Dualizing.objExtPrecomp (ModuleCat.ofHom ν) ω (-2))) +
              Module.length A (Dualizing.moduleExtInto (NN (-((m + 1 : ℕ) : ℤ))) ω (-2) ⧸
                LinearMap.range (Dualizing.objExtPrecomp (ModuleCat.ofHom sk) ω (-2)))
            ≤ (m : ℕ∞) * c + c := add_le_add hbd hcs
          _ = ((m + 1 : ℕ) : ℕ∞) * c := by push_cast; rw [add_mul, one_mul]
  obtain ⟨ν, tau, hsq, hbd⟩ := key n
  refine le_trans ?_ hbd
  exact Dualizing.length_quotient_range_le_length_quotient_range_objExtPrecomp ω hω f
    (hMreg _) (hdM _) (hExtM _) (hdN _) (ρ (-(n : ℤ))) (hker _) (hQ _) ν tau (ρ 0) hM0 hsq

end Dualizing

namespace Stacks.Algebraization

/-! ### Sections of an isomorphism -/

/-- **An isomorphism of modules on a scheme is bijective on global sections**, for the `A`-module
structures that a ring map `A →+* Γ(X, ⊤)` induces. The inverse is the map on global sections of
the inverse isomorphism. Both
`Stacks.Algebraization.puncturedSectionsMap` and
`Stacks.Algebraization.puncturedClosedFibreSectionsMap` are instances of
`Stacks.Algebraization.sectionsMapOfScalars`, so this one statement serves the punctured spectrum
and the punctured closed fibre alike. -/
public theorem bijective_sectionsMapOfScalars_of_iso {X : Scheme.{u}} (A : Type u) [CommRing A]
    (q : A →+* Γ(X, ⊤)) {F G : X.Modules} (e : F ≅ G) :
    Function.Bijective (sectionsMapOfScalars A q e.hom) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun z => Scheme.Modules.Hom.app e.inv ⊤ z, fun z => ?_, fun z => ?_⟩
  · exact (ConcreteCategory.congr_hom
      (congrArg (fun t => Scheme.Modules.Hom.app t ⊤) e.hom_inv_id) z).trans
      (CategoryTheory.id_apply z)
  · exact (ConcreteCategory.congr_hom
      (congrArg (fun t => Scheme.Modules.Hom.app t ⊤) e.inv_hom_id) z).trans
      (CategoryTheory.id_apply z)

/-! ### From depth three on `A` to depth two on `A / fA` -/

/-- **From `depth(A) ≥ 3` to `depth_A(A/fA) ≥ 2`**, the depth of the quotient being measured over
`A` itself. This is [Stacks, Tag 090R] read in the direction this file needs: the `mpr` of
`Stacks.Algebraization.le_depth_quotient_span_singleton_iff` at `n = 2`, where
`(2 : ℕ∞) + 1 = 3` holds by `rfl`. -/
public theorem two_le_depth_quotient_of_three_le_depth (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (f : A) (hfm : f ∈ maximalIdeal A)
    (hf : IsSMulRegular A f)
    (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A) :
    2 ≤ Module.depth A (maximalIdeal A) (A ⧸ Ideal.span {f}) :=
  (le_depth_quotient_span_singleton_iff A f hfm hf 2).2 hdepth

/-! ### Dualising a bijection -/

/-- **The dual of a bijective map of modules is bijective.** -/
public theorem Dualizing.bijective_objExtPrecomp_ofHom_of_bijective {A : Type u} [CommRing A]
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (g : M →ₗ[A] N)
    (hg : Function.Bijective g) (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    Function.Bijective (Dualizing.objExtPrecomp (ModuleCat.ofHom g) K i) :=
  (Dualizing.linearEquiv_moduleExtInto_of_linearEquiv
    (LinearEquiv.ofBijective g hg) K i).bijective

/-! ### Multiplying by a section of the structure sheaf -/

/-- **When the module being tensored with is the structure sheaf, every multiplication map of the
twisting family is a single endomorphism of the structure sheaf, conjugated by isomorphisms.**
This is `Stacks.Algebraization.exists_iso_tensorModulesMap_id_mulSectionPowScheme_unit` with the
hypothesis `L = 𝒪_X` substituted, so that the endomorphism produced does not depend on the
degree. -/
public theorem exists_endo_eq_conj_tensorModulesMap_id_mulSectionPowScheme (X : Scheme.{u})
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : L = Stacks.Ample.unitModule X) (w : L ≅ Stacks.Ample.unitModule X)
    (σ : Stacks.Ample.unitModule X ⟶ L) :
    ∃ τ : Stacks.Ample.unitModule X ⟶ Stacks.Ample.unitModule X, σ ≫ w.hom = τ ∧ ∀ k : ℤ,
      ∃ (u : tensorModules X (Stacks.Ample.unitModule X) (tensorPowScheme X L k) ≅
              Stacks.Ample.unitModule X)
        (v : tensorModules X (Stacks.Ample.unitModule X) (tensorPowScheme X L (k + 1)) ≅
              Stacks.Ample.unitModule X),
        tensorModulesMap X (𝟙 (Stacks.Ample.unitModule X)) (mulSectionPowScheme X L σ k) =
          u.hom ≫ τ ≫ v.inv := by
  subst hL
  refine ⟨σ ≫ w.hom, rfl, fun k => ?_⟩
  obtain ⟨u, v, huv⟩ := exists_iso_tensorModulesMap_id_mulSectionPowScheme_unit X σ k
  refine ⟨u, v ≪≫ w, ?_⟩
  simp [huv]

/-! ### The morphism attached to a global section, at the unit section -/

/-- **The morphism out of the structure sheaf attached to a global section sends the unit section
back to that global section.** -/
public theorem unitHomEquivTop_app_top_one {X : Scheme.{u}} (M : X.Modules) (y : Γ(M, ⊤)) :
    (Scheme.Modules.unitHomEquivTop M y).app ⊤ (1 : Γ(X, ⊤)) = y := by
  have h1 : (Scheme.Modules.unitHomEquivTop M y).app ⊤ (1 : Γ(X, ⊤)) =
      (SheafOfModules.unitHomEquiv M (Scheme.Modules.unitHomEquivTop M y)).val (op ⊤) := rfl
  rw [h1, Scheme.Modules.unitHomEquiv_unitHomEquivTop, Scheme.Modules.sectionsTopEquiv_val]
  have h2 : M.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ := by
    rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (Opposite.op (⊤ : X.Opens)) from
      Subsingleton.elim _ _]
    exact M.presheaf.map_id _
  rw [h2]
  exact CategoryTheory.id_apply y

/-! ### Endomorphisms of a cyclic module -/

/-- **An `A`-linear endomorphism of a cyclic module is multiplication by a scalar.** Cyclicity is
given as a surjection `A →ₗ[A] M`; every element of `M` is then a multiple of the image of `1`,
and the endomorphism is multiplication by any preimage of the image of that element. -/
public theorem exists_smul_eq_of_surjective_linearMap {A : Type*} [CommRing A] {M : Type*}
    [AddCommGroup M] [Module A M] (q : A →ₗ[A] M) (hq : Function.Surjective q)
    (g : M →ₗ[A] M) : ∃ a : A, ∀ z : M, g z = a • z := by
  obtain ⟨a, ha⟩ := hq (g (q 1))
  have hscal (c : A) : q c = c • q 1 := by rw [← map_smul, smul_eq_mul, mul_one]
  refine ⟨a, fun z => ?_⟩
  obtain ⟨c, rfl⟩ := hq z
  rw [hscal c, map_smul, ← ha, hscal a, smul_comm]

/-! ### The dual colength of multiplication by a scalar on a copy of `A / fA` -/

/-- **The dual colength of multiplication by `a` on a module isomorphic to `A / fA` is finite**,
provided `a` lies outside every prime of the support of `Ext_A^{-2}(A/fA, ω)` other than the closed
point.

Dualising, multiplication by `a` on the module becomes multiplication by `a` on
`Ext_A^{-2}(A/fA, ω)` (`Dualizing.objExtPrecomp_smul_id`), so the quotient in question is
`QuotSMulTop a Ext_A^{-2}(A/fA, ω)`. Its support is the intersection of the support of
`Ext_A^{-2}(A/fA, ω)` with the zero locus of `a` (`Module.support_quotSMulTop`), which the
hypothesis confines to the closed point; a finite module supported at the closed point has finite
length. -/
public theorem exists_nat_length_quotient_range_objExtPrecomp_le_of_notMem (A : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (f : A)
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (W : Type u) [AddCommGroup W] [Module A W] (e : W ≃ₗ[A] A ⧸ Ideal.span {f})
    (g : W →ₗ[A] W) (a : A) (hg : ∀ z : W, g z = a • z)
    (hna : ∀ p : PrimeSpectrum A,
      p ∈ Module.support A (Dualizing.moduleExtInto (A ⧸ Ideal.span {f}) ω (-2)) →
      p ≠ closedPoint A → a ∉ p.asIdeal) :
    ∃ L : ℕ, Module.length A (Dualizing.moduleExtInto W ω (-2) ⧸
      LinearMap.range (Dualizing.objExtPrecomp (ModuleCat.ofHom g) ω (-2))) ≤ (L : ℕ∞) := by
  have hBfin : Module.Finite A (Dualizing.moduleExtInto (A ⧸ Ideal.span {f}) ω (-2)) :=
    Dualizing.moduleExtInto_finite.{u, u} (M := A ⧸ Ideal.span {f}) ω hω 2
  have hid : ModuleCat.ofHom g = a • 𝟙 (ModuleCat.of A W) := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
    change g z = _
    rw [hg z]
    rfl
  have hrange : LinearMap.range (Dualizing.objExtPrecomp (ModuleCat.ofHom g) ω (-2)) =
      a • (⊤ : Submodule A (Dualizing.moduleExtInto W ω (-2))) := by
    rw [hid, Dualizing.objExtPrecomp_smul_id]
    ext z
    rw [Submodule.mem_smul_pointwise_iff_exists]
    simp
  have hlen : Module.length A (QuotSMulTop a (Dualizing.moduleExtInto (A ⧸ Ideal.span {f}) ω (-2)))
      = Module.length A (Dualizing.moduleExtInto W ω (-2) ⧸
        a • (⊤ : Submodule A (Dualizing.moduleExtInto W ω (-2)))) :=
    (QuotSMulTop.congr a (Dualizing.linearEquiv_moduleExtInto_of_linearEquiv e ω (-2))).length_eq
  have hsupp : Module.support A
      (QuotSMulTop a (Dualizing.moduleExtInto (A ⧸ Ideal.span {f}) ω (-2))) ⊆
      {closedPoint A} := by
    intro p hp
    rw [Module.support_quotSMulTop] at hp
    by_contra hne
    exact hna p hp.1 hne (hp.2 (Set.mem_singleton a))
  have hFL : IsFiniteLength A
      (QuotSMulTop a (Dualizing.moduleExtInto (A ⧸ Ideal.span {f}) ω (-2))) := by
    rcases subsingleton_or_nontrivial
        (QuotSMulTop a (Dualizing.moduleExtInto (A ⧸ Ideal.span {f}) ω (-2))) with hsub | hnt
    · exact IsFiniteLength.of_subsingleton
    · refine isFiniteLength_of_support ?_
      rcases Set.subset_singleton_iff_eq.mp hsupp with hempty | heq
      · exact absurd (Module.support_eq_empty_iff.mp hempty) (not_subsingleton _)
      · exact heq
  refine ⟨(Module.length A
    (QuotSMulTop a (Dualizing.moduleExtInto (A ⧸ Ideal.span {f}) ω (-2)))).toNat, ?_⟩
  rw [hrange, ← hlen]
  exact le_of_eq (ENat.natCast_toNat (Module.length_ne_top_iff.mpr hFL)).symm

/-! ### Avoiding finitely many primes inside the image of a map onto `A / fA` -/

/-- **A map into `A/fA` whose cokernel has finite length hits an element avoiding any prescribed
finite set of primes other than the closed point.**

Let `ψ : M →ₗ[A] A/fA` have cokernel of finite length, and let `E` be a finite set of primes of
`A`, each containing `f` and none of them the closed point. Then `ψ` takes some value whose
representatives in `A` all lie outside every prime of `E`.

The point is that the image of `ψ`, pulled back to an ideal `J` of `A`, is contained in no prime
of `E`: if it were contained in `𝔭`, then `A/𝔭` would be a quotient of the cokernel of `ψ`, so
`𝔭` would lie in the support of that cokernel, which finite length confines to the closed point.
Prime avoidance (`Ideal.subset_union_prime`) then produces an element of `J` outside the union. -/
public theorem exists_notMem_of_isFiniteLength_quotient_range (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (f : A) {M : Type u} [AddCommGroup M] [Module A M]
    (ψ : M →ₗ[A] A ⧸ Ideal.span {f})
    (hcoker : IsFiniteLength A ((A ⧸ Ideal.span {f}) ⧸ LinearMap.range ψ))
    {E : Set (PrimeSpectrum A)} (hE : E.Finite)
    (hEf : ∀ p ∈ E, f ∈ p.asIdeal) (hEne : ∀ p ∈ E, p ≠ closedPoint A) :
    ∃ z : M, ∀ p ∈ E, ∀ c : A,
      ψ z = Submodule.Quotient.mk (p := Ideal.span {f}) c → c ∉ p.asIdeal := by
  classical
  have hsupp : Module.support A ((A ⧸ Ideal.span {f}) ⧸ LinearMap.range ψ) ⊆
      {closedPoint A} := by
    rcases subsingleton_or_nontrivial ((A ⧸ Ideal.span {f}) ⧸ LinearMap.range ψ) with hs | hn
    · simp [Module.support_eq_empty_iff.mpr hs]
    · exact le_of_eq (support_of_isFiniteLength hcoker)
  have hfp : ∀ p ∈ E, (Ideal.span {f} : Submodule A A) ≤ p.asIdeal := fun p hp => by
    rw [Ideal.span_le]
    simpa using hEf p hp
  have hnle : ∀ p ∈ E,
      ¬ (Submodule.comap (Ideal.span {f} : Submodule A A).mkQ (LinearMap.range ψ) ≤ p.asIdeal) := by
    intro p hp hle
    have hπker : (Ideal.span {f} : Submodule A A) ≤
        LinearMap.ker (Submodule.mkQ p.asIdeal) := by
      rw [Submodule.ker_mkQ]
      exact hfp p hp
    have hπsurj : Function.Surjective
        (Submodule.liftQ (Ideal.span {f} : Submodule A A) (Submodule.mkQ p.asIdeal) hπker) := by
      intro w
      obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective p.asIdeal w
      exact ⟨Submodule.mkQ _ c, rfl⟩
    have hle2 : LinearMap.range ψ ≤ LinearMap.ker
        (Submodule.liftQ (Ideal.span {f} : Submodule A A) (Submodule.mkQ p.asIdeal) hπker) := by
      rintro - ⟨m, rfl⟩
      obtain ⟨c, hc⟩ := Submodule.mkQ_surjective (Ideal.span {f} : Submodule A A) (ψ m)
      have hcp : c ∈ p.asIdeal := hle (by
        rw [Submodule.mem_comap, hc]
        exact ⟨m, rfl⟩)
      rw [LinearMap.mem_ker, ← hc]
      change Submodule.mkQ p.asIdeal c = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr hcp
    have hq : Function.Surjective (Submodule.liftQ (LinearMap.range ψ) _ hle2) := by
      intro w
      obtain ⟨v, hv⟩ := hπsurj w
      exact ⟨Submodule.mkQ _ v, hv⟩
    have hpmem : p ∈ Module.support A (A ⧸ p.asIdeal) := by
      rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
      exact fun _ h => h
    exact hEne p hp (hsupp (Module.support_subset_of_surjective _ hq hpmem))
  obtain ⟨y, hyJ, hy⟩ : ∃ y : A,
      y ∈ Submodule.comap (Ideal.span {f} : Submodule A A).mkQ (LinearMap.range ψ) ∧
        ∀ q ∈ E, y ∉ q.asIdeal := by
    by_contra hcon
    push Not at hcon
    have hsub : ((Submodule.comap (Ideal.span {f} : Submodule A A).mkQ
        (LinearMap.range ψ) : Ideal A) : Set A) ⊆
        ⋃ q ∈ (↑hE.toFinset : Set (PrimeSpectrum A)), (q.asIdeal : Set A) := by
      intro w hw
      obtain ⟨q, hq, hwq⟩ := hcon w hw
      exact Set.mem_biUnion (hE.mem_toFinset.mpr hq) hwq
    obtain ⟨q, hq, hql⟩ := (Ideal.subset_union_prime (f := PrimeSpectrum.asIdeal)
      (closedPoint A) (closedPoint A) (fun i _ _ _ => i.isPrime)).mp hsub
    exact hnle q (hE.mem_toFinset.mp hq) hql
  obtain ⟨z, hz⟩ := hyJ
  refine ⟨z, fun p hp c hc hcp => hy p hp ?_⟩
  have hdiff : c - y ∈ (Ideal.span {f} : Submodule A A) :=
    (Submodule.Quotient.eq _).mp (hc.symm.trans hz)
  simpa using p.asIdeal.sub_mem hcp (hfp p hp hdiff)

/-! ### Conjugating a morphism on the closed fibre by isomorphisms -/

/-- **Multiplying by a conjugate of `τ` has the same dual colength as multiplying by `τ`.** For
`ψ = u.hom ≫ τ ≫ v.inv` with `u` and `v` isomorphisms, the maps induced on global sections over
the punctured closed fibre differ by two `A`-linear bijections, and so do their duals; a colength
is unchanged by composing with bijections
(`Module.length_quotient_range_comp_bijective`). -/
public theorem length_quotient_range_objExtPrecomp_sectionsMap_conj (A : Type u) [CommRing A]
    [IsLocalRing A] (f : A) {F G H : (closedFibre A f).Modules} (u : F ≅ H) (v : G ≅ H)
    (τ : H ⟶ H) (ψ : F ⟶ G) (hψ : ψ = u.hom ≫ τ ≫ v.inv)
    (ω : DerivedCategory (ModuleCat.{u} A)) :
    letI := puncturedClosedFibreSectionsModule A f
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj F)
    letI := puncturedClosedFibreSectionsModule A f
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj G)
    letI := puncturedClosedFibreSectionsModule A f
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj H)
    Module.length A (Dualizing.moduleExtInto
        Γ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj F, ⊤) ω (-2) ⧸
      LinearMap.range (Dualizing.objExtPrecomp (ModuleCat.ofHom
        (puncturedClosedFibreSectionsMap A f
          ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map ψ))) ω (-2))) =
      Module.length A (Dualizing.moduleExtInto
          Γ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj H, ⊤) ω (-2) ⧸
        LinearMap.range (Dualizing.objExtPrecomp (ModuleCat.ofHom
          (puncturedClosedFibreSectionsMap A f
            ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map τ))) ω (-2))) := by
  subst hψ
  let := puncturedClosedFibreSectionsModule A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj F)
  let := puncturedClosedFibreSectionsModule A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj G)
  let := puncturedClosedFibreSectionsModule A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj H)
  have hΓ : puncturedClosedFibreSectionsMap A f
        ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map (u.hom ≫ τ ≫ v.inv)) =
      (puncturedClosedFibreSectionsMap A f
          ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map v.inv)) ∘ₗ
        (puncturedClosedFibreSectionsMap A f
            ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map τ)) ∘ₗ
          (puncturedClosedFibreSectionsMap A f
            ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map u.hom)) := by
    refine LinearMap.ext fun z => ?_
    rw [Functor.map_comp, Functor.map_comp, puncturedClosedFibreSectionsMap_comp,
      puncturedClosedFibreSectionsMap_comp]
    rfl
  have hofHom : ModuleCat.ofHom (puncturedClosedFibreSectionsMap A f
        ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map (u.hom ≫ τ ≫ v.inv))) =
      ModuleCat.ofHom (puncturedClosedFibreSectionsMap A f
          ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map u.hom)) ≫
        ModuleCat.ofHom (puncturedClosedFibreSectionsMap A f
            ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map τ)) ≫
          ModuleCat.ofHom (puncturedClosedFibreSectionsMap A f
            ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map v.inv)) := by
    rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp, hΓ]
  rw [hofHom, Dualizing.objExtPrecomp_comp, Dualizing.objExtPrecomp_comp]
  exact Module.length_quotient_range_comp_bijective _
    (Dualizing.bijective_objExtPrecomp_ofHom_of_bijective _
      (bijective_sectionsMapOfScalars_of_iso A (puncturedClosedFibreScalars A f)
        ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).mapIso u)) ω (-2))
    _ _
    (Dualizing.bijective_objExtPrecomp_ofHom_of_bijective _
      (bijective_sectionsMapOfScalars_of_iso A (puncturedClosedFibreScalars A f)
        ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).mapIso v).symm) ω (-2)).surjective

/-! ### The twists of the unit triple by an invertible triple -/

section Twist

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (f : A)
  (htf : IsFTorsionFree A f
    (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme))
  (T : CoherentTriple A f) (hT : IsInvertibleTriple T)

/-- **The `k`-th twist of the unit coherent triple by the invertible triple `T`.** Its
punctured-spectrum member is `𝒪_U ⊗ (T.F)^{⊗ k}`. -/
public noncomputable abbrev unitTwistZ (k : ℤ) : CoherentTriple A f :=
  (CoherentTriple.unit A f htf).twistZ T hT k

/-- Every twist of the unit triple by an invertible triple is invertible. -/
public theorem isInvertibleTriple_unitTwistZ (k : ℤ) :
    IsInvertibleTriple (unitTwistZ A f htf T hT k) :=
  isInvertibleTriple_twistZ (isInvertibleTriple_unit A f htf) hT k

/-- **The restriction to the punctured closed fibre of the closed-fibre member of the `k`-th
twist of the unit triple.** Its global sections are the target of the canonical map on global
sections of that twist. -/
public noncomputable abbrev unitTwistZRestrict (k : ℤ) :
    (puncturedClosedFibre A f).toScheme.Modules :=
  (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj ((unitTwistZ A f htf T hT k).F₀)

variable (x : Γ(T.F, ⊤)) (x₀ : Γ(T.F₀, ⊤))
  (hx : globalSectionsMap A f T x =
    pullbackGlobalSections (puncturedClosedFibre A f).ι T.F₀ x₀)

/-- **Multiplication by the section pair `(x, x₀)`, as a morphism from the `k`-th twist of the
unit triple to its `(k + 1)`-st.** -/
public noncomputable abbrev unitTwistZStep (k : ℤ) :
    (unitTwistZ A f htf T hT k).Hom (unitTwistZ A f htf T hT (k + 1)) :=
  (CoherentTriple.unit A f htf).mulSectionTwistZOfGlobalSections T hT x x₀ hx k

/-- **The map induced by `Stacks.Algebraization.unitTwistZStep` on global sections over the
punctured closed fibre.** -/
public noncomputable abbrev unitTwistZRestrictStep (k : ℤ) :
    letI := puncturedClosedFibreSectionsModule A f (unitTwistZRestrict A f htf T hT k)
    letI := puncturedClosedFibreSectionsModule A f (unitTwistZRestrict A f htf T hT (k + 1))
    Γ(unitTwistZRestrict A f htf T hT k, ⊤) →ₗ[A]
      Γ(unitTwistZRestrict A f htf T hT (k + 1), ⊤) :=
  puncturedClosedFibreSectionsMap A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
      (unitTwistZStep A f htf T hT x x₀ hx k).onClosedFibre)

/-- **Every step map is the same endomorphism of the structure sheaf up to isomorphism, and so
has the same dual colength.** When the closed-fibre member of the twisting triple is the structure
sheaf of the closed fibre, the closed-fibre member of the `k`-th step is a single endomorphism `τ`
of that structure sheaf conjugated by isomorphisms
(`Stacks.Algebraization.exists_endo_eq_conj_tensorModulesMap_id_mulSectionPowScheme`); taking
global sections over the punctured closed fibre and dualising, the conjugating isomorphisms become
bijections, which do not change a colength
(`Stacks.Algebraization.length_quotient_range_objExtPrecomp_sectionsMap_conj`).

The endomorphism produced is the morphism attached to the closed-fibre section `x₀`, transported
along `hF₀`; that is what the first conjunct records, and it is how a caller identifies the scalar
`τ` acts by. -/
public theorem exists_endo_length_quotient_range_objExtPrecomp_unitTwistZRestrictStep_eq
    (hF₀ : T.F₀ = Stacks.Ample.unitModule (closedFibre A f))
    (ω : DerivedCategory (ModuleCat.{u} A)) :
    ∃ τ : Stacks.Ample.unitModule (closedFibre A f) ⟶ Stacks.Ample.unitModule (closedFibre A f),
      Scheme.Modules.unitHomEquivTop T.F₀ x₀ ≫ (eqToIso hF₀).hom = τ ∧
        ∀ k : ℤ,
          letI := puncturedClosedFibreSectionsModule A f (unitTwistZRestrict A f htf T hT k)
          letI := puncturedClosedFibreSectionsModule A f
            (unitTwistZRestrict A f htf T hT (k + 1))
          letI := puncturedClosedFibreSectionsModule A f
            ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj
              (Stacks.Ample.unitModule (closedFibre A f)))
          Module.length A (Dualizing.moduleExtInto
              Γ(unitTwistZRestrict A f htf T hT k, ⊤) ω (-2) ⧸
            LinearMap.range (Dualizing.objExtPrecomp
              (ModuleCat.ofHom (unitTwistZRestrictStep A f htf T hT x x₀ hx k)) ω (-2))) =
            Module.length A (Dualizing.moduleExtInto
                Γ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj
                  (Stacks.Ample.unitModule (closedFibre A f)), ⊤) ω (-2) ⧸
              LinearMap.range (Dualizing.objExtPrecomp (ModuleCat.ofHom
                (puncturedClosedFibreSectionsMap A f
                  ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map τ))) ω (-2))) := by
  have := hT.invertible_F₀
  obtain ⟨τ, hwτ, hτ⟩ := exists_endo_eq_conj_tensorModulesMap_id_mulSectionPowScheme
    (closedFibre A f) T.F₀ hF₀ (eqToIso hF₀) (Scheme.Modules.unitHomEquivTop T.F₀ x₀)
  refine ⟨τ, hwτ, fun k => ?_⟩
  obtain ⟨u, v, huv⟩ := hτ k
  exact length_quotient_range_objExtPrecomp_sectionsMap_conj A f u v τ
    (unitTwistZStep A f htf T hT x x₀ hx k).onClosedFibre huv ω

/-- **The linear bound on the Euler characteristics of the negative twists, given a uniform bound
on the dual colength of the step maps.** -/
public theorem eulerCharacteristic_unitTwistZ_neg_le_of_length_step_le
    (hfm : f ∈ maximalIdeal A) (hreg : IsRegular f)
    (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A)
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω) (c : ℕ)
    (hstep : ∀ k : ℤ,
      letI := puncturedClosedFibreSectionsModule A f (unitTwistZRestrict A f htf T hT k)
      letI := puncturedClosedFibreSectionsModule A f (unitTwistZRestrict A f htf T hT (k + 1))
      Module.length A (Dualizing.moduleExtInto
          Γ(unitTwistZRestrict A f htf T hT k, ⊤) ω (-2) ⧸
        LinearMap.range (Dualizing.objExtPrecomp
          (ModuleCat.ofHom (unitTwistZRestrictStep A f htf T hT x x₀ hx k)) ω (-2))) ≤ (c : ℕ∞))
    (n : ℕ) :
    (unitTwistZ A f htf T hT (-(n : ℤ))).eulerCharacteristic ≤ (c * n : ℤ) := by
  have hd2 : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A :=
    (show (2 : ℕ∞) ≤ 3 by decide).trans hdepth
  have hb := two_le_depth_quotient_of_three_le_depth A f hfm hreg.left hdepth
  have hinvF : ∀ k : ℤ, Stacks.Ample.IsInvertibleModule
      (Stacks.Divisors.puncturedSpectrum A).toScheme (unitTwistZ A f htf T hT k).F :=
    fun k => (isInvertibleTriple_unitTwistZ A f htf T hT k).invertible_F
  have hinvF₀ : ∀ k : ℤ, Stacks.Ample.IsInvertibleModule (closedFibre A f)
      (unitTwistZ A f htf T hT k).F₀ :=
    fun k => (isInvertibleTriple_unitTwistZ A f htf T hT k).invertible_F₀
  let instM : ∀ k : ℤ, Module A Γ((unitTwistZ A f htf T hT k).F, ⊤) :=
    fun k => puncturedSectionsModule A (unitTwistZ A f htf T hT k).F
  let instN : ∀ k : ℤ, Module A Γ(unitTwistZRestrict A f htf T hT k, ⊤) :=
    fun k => puncturedClosedFibreSectionsModule A f (unitTwistZRestrict A f htf T hT k)
  have instMfin : ∀ k : ℤ, Module.Finite A Γ((unitTwistZ A f htf T hT k).F, ⊤) := fun k =>
    finite_puncturedSections_of_isInvertible A (unitTwistZ A f htf T hT k).F hd2
  have instNfin : ∀ k : ℤ, Module.Finite A Γ(unitTwistZRestrict A f htf T hT k, ⊤) := fun k =>
    finite_puncturedClosedFibreSections A f hfm hreg (unitTwistZ A f htf T hT k).F₀ hdepth
  have hMreg : ∀ k : ℤ, IsSMulRegular Γ((unitTwistZ A f htf T hT k).F, ⊤) f := fun k =>
    isSMulRegular_puncturedSections A hreg.left (unitTwistZ A f htf T hT k).F
  have hdM : ∀ k : ℤ, 2 ≤ Module.depth A (maximalIdeal A)
      Γ((unitTwistZ A f htf T hT k).F, ⊤) := fun k =>
    two_le_depth_puncturedSections_of_isInvertible A (unitTwistZ A f htf T hT k).F hd2
  have hdN : ∀ k : ℤ, 2 ≤ Module.depth A (maximalIdeal A)
      Γ(unitTwistZRestrict A f htf T hT k, ⊤) := fun k =>
    two_le_depth_puncturedClosedFibreSections A f hfm hreg
      (unitTwistZ A f htf T hT k).F₀ hdepth hb
  have hker : ∀ k : ℤ, LinearMap.ker (globalSectionsMap A f (unitTwistZ A f htf T hT k)) =
      f • (⊤ : Submodule A Γ((unitTwistZ A f htf T hT k).F, ⊤)) := fun k =>
    ker_globalSectionsMap A f hfm hreg (unitTwistZ A f htf T hT k) hdepth
  have hQ : ∀ k : ℤ, IsFiniteLength A (Γ(unitTwistZRestrict A f htf T hT k, ⊤) ⧸
      LinearMap.range (globalSectionsMap A f (unitTwistZ A f htf T hT k))) := fun k =>
    finiteLength_cokernel_globalSectionsMap A f hfm hreg (unitTwistZ A f htf T hT k) hdepth
  -- the dual Ext of the punctured-spectrum sections has finite length
  have hExtM : ∀ k : ℤ, IsFiniteLength A
      (Dualizing.moduleExtInto Γ((unitTwistZ A f htf T hT k).F, ⊤) ω (-2)) := by
    intro k
    have hlc := finite_localCohomology_globalSections_pushforward_of_isInvertible A
      (unitTwistZ A f htf T hT k).F hdepth 2 le_rfl
    have : Module.Finite A ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj
        ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj
          (unitTwistZ A f htf T hT k).F) : Type u) :=
      Module.Finite.equiv (puncturedSectionsPushforwardEquiv A (unitTwistZ A f htf T hT k).F)
    have h1 := Dualizing.isFiniteLength_moduleExtInto_of_finite_localCohomology ω hω
      ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj
        ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj
          (unitTwistZ A f htf T hT k).F) : Type u) ((2 : ℕ) : ℤ) hlc
    rw [show -((2 : ℕ) : ℤ) = (-2 : ℤ) by norm_num] at h1
    exact IsFiniteLength.of_surjective h1
      (Dualizing.linearEquiv_moduleExtInto_of_linearEquiv
        (puncturedSectionsPushforwardEquiv A (unitTwistZ A f htf T hT k).F) ω (-2)).surjective
  -- the dual Ext of the degree-zero punctured-spectrum sections vanishes
  have hM0 : Subsingleton
      (Dualizing.moduleExtInto Γ((unitTwistZ A f htf T hT 0).F, ⊤) ω (-2)) := by
    have := subsingleton_moduleExtInto_globalSections_pushforward_unit A ω hω hdepth
    have := ((CoherentTriple.unit A f htf).isIso_twistZZeroHom hT).1
    have e0 := asIso ((CoherentTriple.unit A f htf).twistZZeroHom hT).onPunctured
    have eΓ := LinearEquiv.ofBijective (puncturedSectionsMap A e0.hom)
      (bijective_sectionsMapOfScalars_of_iso A (puncturedScalars A) e0)
    exact (Dualizing.linearEquiv_moduleExtInto_of_linearEquiv
      (eΓ.trans (puncturedSectionsPushforwardEquiv A
        (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme)))
      ω (-2)).symm.toEquiv.subsingleton
  -- the step square, with the index normalised
  have hstep' : ∀ k k' : ℤ, k + 1 = k' →
      ∃ (sk : Γ(unitTwistZRestrict A f htf T hT k, ⊤) →ₗ[A]
          Γ(unitTwistZRestrict A f htf T hT k', ⊤))
        (tk : Γ((unitTwistZ A f htf T hT k).F, ⊤) →ₗ[A]
          Γ((unitTwistZ A f htf T hT k').F, ⊤)),
        sk ∘ₗ globalSectionsMap A f (unitTwistZ A f htf T hT k) =
            globalSectionsMap A f (unitTwistZ A f htf T hT k') ∘ₗ tk ∧
          Module.length A (Dualizing.moduleExtInto
              Γ(unitTwistZRestrict A f htf T hT k, ⊤) ω (-2) ⧸
            LinearMap.range (Dualizing.objExtPrecomp (ModuleCat.ofHom sk) ω (-2))) ≤ (c : ℕ∞) := by
    intro k k' hk
    subst hk
    exact ⟨unitTwistZRestrictStep A f htf T hT x x₀ hx k,
      puncturedSectionsMap A (unitTwistZStep A f htf T hT x x₀ hx k).onPunctured,
      globalSectionsMap_naturality A f (unitTwistZStep A f htf T hT x x₀ hx k), hstep k⟩
  have hchain := Dualizing.length_quotient_range_le_mul_of_chain ω hω f
    (fun k => Γ((unitTwistZ A f htf T hT k).F, ⊤))
    (fun k => Γ(unitTwistZRestrict A f htf T hT k, ⊤))
    (fun k => globalSectionsMap A f (unitTwistZ A f htf T hT k)) (c : ℕ∞)
    hMreg hdM hdN hExtM hM0 hker hQ hstep' n
  rw [CoherentTriple.eulerCharacteristic_eq_length_cokernel A f hfm hreg
    (unitTwistZ A f htf T hT (-(n : ℤ))) hdepth]
  have hle : Module.length A (Γ(unitTwistZRestrict A f htf T hT (-(n : ℤ)), ⊤) ⧸
      LinearMap.range (globalSectionsMap A f (unitTwistZ A f htf T hT (-(n : ℤ))))) ≤
      ((c * n : ℕ) : ℕ∞) := by
    refine hchain.trans ?_
    push_cast
    rw [mul_comm]
  exact_mod_cast ENat.toNat_le_of_le_natCast hle

end Twist

/-! ### The linear bound -/

/-- **[Stacks, Tag 0F2B]: the Euler characteristics of the negative twists of the unit triple by
an invertible triple whose closed-fibre member is the structure sheaf are bounded by a linear
function of the twist.**

Choose a global section `x` of `T.F` whose image under the canonical map on global sections avoids
the finitely many primes of `Supp Ext_A^{-2}(A/fA, ω)` other than the closed point — possible
because that cokernel has finite length
(`Stacks.Algebraization.exists_notMem_of_isFiniteLength_quotient_range`) — and let `x₀` be its
closed-fibre partner (`Stacks.Algebraization.exists_eq_globalSectionsMap`). Multiplication by the
pair `(x, x₀)` carries each twist to the next, and on global sections over the punctured closed
fibre it is, up to bijections, multiplication by one scalar `a` of `A`
(`exists_endo_length_quotient_range_objExtPrecomp_unitTwistZRestrictStep_eq`). That scalar is
the value chosen above, so it avoids those primes, and the dual colength of multiplication by it is
therefore finite
(`Stacks.Algebraization.exists_nat_length_quotient_range_objExtPrecomp_le_of_notMem`). Feeding that
one number into `Stacks.Algebraization.eulerCharacteristic_unitTwistZ_neg_le_of_length_step_le`
gives the slope. -/
public theorem exists_linear_bound_eulerCharacteristic_twistZ_neg
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (f : A)
    (hfm : f ∈ IsLocalRing.maximalIdeal A) (hreg : IsRegular f)
    (hdepth : 3 ≤ Module.depth A (IsLocalRing.maximalIdeal A) A)
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (h4 : ∀ p : Ideal A, ∀ _ : p.IsPrime, f ∈ p → ringKrullDim (A ⧸ p) = 2 →
      2 ≤ Module.depth (Localization.AtPrime p)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p))
    (htf : IsFTorsionFree A f
      (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme))
    (T : CoherentTriple A f) (hT : IsInvertibleTriple T)
    (hF₀ : T.F₀ = Stacks.Ample.unitModule (closedFibre A f)) :
    ∃ c : ℕ, ∀ n : ℕ,
      ((CoherentTriple.unit A f htf).twistZ T hT (-(n : ℤ))).eulerCharacteristic
        ≤ (c * n : ℤ) := by
  have := hT.invertible_F
  have := hT.invertible_F₀
  let := puncturedSectionsModule A T.F
  let := puncturedClosedFibreSectionsModule A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
  let := puncturedClosedFibreSectionsModule A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj
      (Stacks.Ample.unitModule (closedFibre A f)))
  have hwbij : Function.Bijective (puncturedClosedFibreSectionsMap A f
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map (eqToIso hF₀).hom)) :=
    bijective_sectionsMapOfScalars_of_iso A (puncturedClosedFibreScalars A f)
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).mapIso (eqToIso hF₀))
  obtain ⟨e⟩ := nonempty_linearEquiv_puncturedClosedFibreSections A f hfm hreg
    (Stacks.Ample.unitModule (closedFibre A f)) hdepth
  set EE := (LinearEquiv.ofBijective (puncturedClosedFibreSectionsMap A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map (eqToIso hF₀).hom)) hwbij).trans e
    with hEEdef
  set ψ := EE.toLinearMap ∘ₗ globalSectionsMap A f T with hψdef
  have hcoker : IsFiniteLength A ((A ⧸ Ideal.span {f}) ⧸ LinearMap.range ψ) :=
    IsFiniteLength.of_surjective
      (finiteLength_cokernel_globalSectionsMap A f hfm hreg T hdepth)
      (Submodule.Quotient.equiv (LinearMap.range (globalSectionsMap A f T))
        (LinearMap.range ψ) EE (by rw [hψdef, LinearMap.range_comp])).surjective
  obtain ⟨x, hx'⟩ := exists_notMem_of_isFiniteLength_quotient_range A f ψ hcoker
    (Dualizing.finite_support_moduleExtInto_quotient_diff_closedPoint ω hω f hfm hreg.left h4)
    (fun p hp => Dualizing.mem_of_mem_support_moduleExtInto_quotient ω hω f p hp.1)
    (fun p hp => by simpa using hp.2)
  obtain ⟨x₀, hx⟩ := exists_eq_globalSectionsMap hfm hreg hdepth hT x
  obtain ⟨τ, hwτ, hlen⟩ :=
    exists_endo_length_quotient_range_objExtPrecomp_unitTwistZRestrictStep_eq
      A f htf T hT x x₀ hx hF₀ ω
  obtain ⟨a, ha⟩ := exists_smul_eq_of_surjective_linearMap
    (e.symm.toLinearMap ∘ₗ (Ideal.span {f} : Submodule A A).mkQ)
    (e.symm.surjective.comp (Submodule.mkQ_surjective _))
    (puncturedClosedFibreSectionsMap A f
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map τ))
  -- the unit section of the restricted structure sheaf, and the value of `τ` on it
  have e3 : puncturedClosedFibreSectionsMap A f
        ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
          (Scheme.Modules.unitHomEquivTop T.F₀ x₀))
        (pullbackGlobalSections (puncturedClosedFibre A f).ι
          (Stacks.Ample.unitModule (closedFibre A f)) (1 : Γ(closedFibre A f, ⊤))) =
      globalSectionsMap A f T x :=
    (Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality
        (puncturedClosedFibre A f).ι
        (Scheme.Modules.unitHomEquivTop T.F₀ x₀) (1 : Γ(closedFibre A f, ⊤))).symm.trans
      ((congrArg (fun y : Γ(T.F₀, ⊤) =>
          pullbackGlobalSections (puncturedClosedFibre A f).ι T.F₀ y)
        (unitHomEquivTop_app_top_one T.F₀ x₀)).trans hx.symm)
  have hkey : puncturedClosedFibreSectionsMap A f
        ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map τ)
        (pullbackGlobalSections (puncturedClosedFibre A f).ι
          (Stacks.Ample.unitModule (closedFibre A f)) (1 : Γ(closedFibre A f, ⊤))) =
      puncturedClosedFibreSectionsMap A f
        ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map (eqToIso hF₀).hom)
        (globalSectionsMap A f T x) := by
    rw [← hwτ]
    erw [(Scheme.Modules.pullback _).map_comp, puncturedClosedFibreSectionsMap_comp]
    exact congrArg _ e3
  have hna : ∀ p : PrimeSpectrum A,
      p ∈ Module.support A (Dualizing.moduleExtInto (A ⧸ Ideal.span {f}) ω (-2)) →
      p ≠ closedPoint A → a ∉ p.asIdeal := by
    intro p hp hpne hap
    obtain ⟨c₀, hc₀⟩ := Submodule.mkQ_surjective (Ideal.span {f} : Submodule A A)
      (e (pullbackGlobalSections (puncturedClosedFibre A f).ι
        (Stacks.Ample.unitModule (closedFibre A f)) (1 : Γ(closedFibre A f, ⊤))))
    refine hx' p ⟨hp, by simpa using hpne⟩ (a * c₀) ?_ (Ideal.mul_mem_right _ _ hap)
    change e (puncturedClosedFibreSectionsMap A f
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map (eqToIso hF₀).hom)
      (globalSectionsMap A f T x)) = _
    rw [← hkey, ha, map_smul, ← hc₀, ← map_smul, smul_eq_mul]
    rfl
  obtain ⟨L, hL⟩ := exists_nat_length_quotient_range_objExtPrecomp_le_of_notMem A f ω hω
    Γ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj
      (Stacks.Ample.unitModule (closedFibre A f)), ⊤) e
    (puncturedClosedFibreSectionsMap A f
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map τ)) a ha hna
  exact ⟨L, eulerCharacteristic_unitTwistZ_neg_le_of_length_step_le A f htf T hT x x₀ hx
    hfm hreg hdepth ω hω L fun k => (hlen k).trans_le hL⟩

end Stacks.Algebraization

end
