module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.IntoField
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveTheory
public import StacksFrontier.Homology.DoubleExtend
public import StacksFrontier.RingTheory.Noetherian.ArtinRees

/-!
# Versality and the derived fibre of the naive cotangent complex

Let `S` be a locally Noetherian scheme, let `𝒳` be a category fibred in groupoids over
`(Sch/S)_{fppf}` satisfying (RS*), let `U = Spec A` be affine of finite type over `S` mapping
into an affine open `Spec Λ`, let `x` be an object of `𝒳` over `U`, and let
`ξ : E ⟶ NL_{A/Λ}` be a morphism of `D⁻(A)` satisfying conditions (i) and (ii) of Stacks
07YM. At a finite type point `u₀ ∈ U` with residue field `k`, that tag asserts that `x` is
versal at `u₀` as soon as `ξ` induces a surjection
`H^{-1}(E ⊗ᴸ_A k) ⟶ H^{-1}(NL_{A/Λ} ⊗ᴸ_A k)` and an injection
`H^0(E ⊗ᴸ_A k) ⟶ H^0(NL_{A/Λ} ⊗ᴸ_A k)`, and conversely when `u₀` is a closed point.

This file contributes the two steps of that proof which the dependencies of the tag make
available: the translation of its condition (2) into a statement about `Ext` groups, and the
Artin–Rees step by which the thickening produced by Stacks 07YL is cut down to a small
extension of Artinian local rings.

## Main results

* `Deformation.Artin.surjective_derivedFibre_neg_one_iff_injective_extOne` and
  `Deformation.Artin.injective_derivedFibre_zero_iff_surjective_extZero` — the two halves of
  condition (2) of Stacks 07YM, read through the duality of Stacks 07YK: the surjectivity of
  `H^{-1}(ξ ⊗ᴸ_A k)` is the injectivity of `Ext¹_A(NL_{A/Λ}, k) ⟶ Ext¹_A(E, k)`, and the
  injectivity of `H^0(ξ ⊗ᴸ_A k)` is the surjectivity of
  `Ext⁰_A(NL_{A/Λ}, k) ⟶ Ext⁰_A(E, k)`. These are exactly the two invocations of Stacks 07YK
  in the proof of Stacks 07YM: the first is what turns a failure of surjectivity into a
  nonzero class killed by `ξ`, which is the input of Stacks 07YL, and the second is what
  identifies `H^0(ξ ⊗ᴸ_A k)` with the dual of the map on tangent spaces.
* `Deformation.Artin.exists_pow_inf_eq_bot_of_mul_eq_bot` — the Artin–Rees step: if the ideal
  `I` of a Noetherian ring is annihilated by an ideal `p'`, then `(p')^n ∩ I = 0` for some
  `n > 1`. In the source `A' ⟶ A` is the extension supplied by Stacks 07YL, `I` its kernel,
  which is a one-dimensional `k`-vector space and hence killed by `p' = Ker(A' ⟶ k)`; the
  conclusion is what makes `A'/(p')^n ⟶ A/p^n` an extension with kernel `I`.
* `Deformation.Artin.minus_derivedNaiveCotangentComplex` — the naive cotangent complex is
  bounded above, so that the duality of Stacks 07YK applies to it. Stacks 07YL takes the
  corresponding property of `E` as a hypothesis; for `NL_{A/Λ}` it is a fact and is proved
  here.

## Implementation notes

The derived fibre `E ⊗ᴸ_A k` is presented as the total derived extension of scalars along
`A ⟶ k`, which is the presentation the duality of Stacks 07YK is stated in; its value is a
complex of `k`-modules, so `H^i(E ⊗ᴸ_A k)` is a `k`-vector space and the duality is a
statement about `k`-linear duals. Stacks 07YL states the same groups through a chosen
`Deformation.Artin.DerivedTensorProduct`; the comparison of the two presentations is internal
to the file proving 07YL and is not available here, so the two are not composed.

With the grading conventions of `StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic` the
duality reads `Ext^i_A(E, k) = (H^{-i}(E ⊗ᴸ_A k))^*`, so condition (2) in degree `-1` is a
statement about `Ext¹` and condition (2) in degree `0` is a statement about `Ext⁰`. The
coefficient module is `ULift k`, viewed as an `A`-module by restriction of scalars, because
`Ext` is formed in a module universe above that of the ring; the duality is `k`-linear by
`DerivedCategory.extIntoFieldEquivDualBaseChangeHomology_smul`, so nothing is lost by
recording it as a bijection of underlying sets here.

The map `Ext^i_A(NL_{A/Λ}, k) ⟶ Ext^i_A(E, k)` induced by `ξ` is precomposition with `ξ`,
written out rather than named; the duality is contravariantly natural, so it carries
precomposition with `ξ` to precomposition with `H^{-i}(ξ ⊗ᴸ_A k)`, and over a field
precomposition with a linear map is injective exactly when the map is surjective and
surjective exactly when the map is injective.

What is **not** proved here is the equivalence of condition (2) with versality, in either
direction. Both directions need a bridge from `Deformation.Artin.IsVersalAt` to the
deformation theory of the associated formal object, that is from Tag 07XF through Tag 0CXK
to Tag 06IU. That bridge exists in the direction which *reads* versality: Tag 0CXK is
`Deformation.Artin.isVersalAt_iff_isVersal`, and
`Deformation.Artin.isVersalAt_iff_liftsAtResiduePoint` with
`Deformation.Artin.liftsAtResiduePoint_of_isVersalAt` and
`Deformation.Artin.liftsAtResiduePoint_changeBase` present versality at a point as a lifting
property over whatever deformation base the argument needs. With the bridge, and with the
extension `A'/(p')^n ⟶ A/p^n` of the Artin–Rees step realised as a small extension in
`Deformation.ArtinianLocalAlgCat`, which is the form Stacks 06H0 is stated in, the
implication `(1) ⇒ (2)` is proved in both degrees, by
`Deformation.Artin.surjective_derivedTensorFibre_neg_one_of_isVersalAt` and
`Deformation.Artin.injective_derivedTensorFibre_zero_of_isVersalAt`. The obstruction class of
Stacks 07YI is likewise available in the geometric setting of a category fibred in groupoids,
through `Deformation.Artin.exists_algHom_section_of_surjective_derivedTensorFibre_neg_one`.

The opposite direction of the bridge is available as well. Tag 0CXK is an equivalence, so it
produces versality at `u₀` from versality of the formal object over `A_𝔭^∧`, and
`Deformation.Artin.exists_approximation_isVersalAt_iff_isVersal` supplies every argument that
equivalence asks about the base: the complete local object over the completion at `u₀` and the
Cartesian arrow to `x`, the presentation of the completed local ring by the base of the
approximation, the ring to which 0CXK pins the base — the local ring `𝒪_{S,s}` — together with
the canonical morphism out of its spectrum and the two identifications 0CXK asks of them, the
algebra structure of that base over `𝒪_{S,s}` and the factorization of its structure morphism
through `Spec 𝒪_{S,s}`. Its right-hand side is versality of a formal object (Tag 0CXJ), which
is versality of a formal object of a predeformation category over `𝒞_{𝒪_{S,s}}`, the form the
criterion of Tag 06IU is stated in; `Deformation.Artin.isVersalAt_iff_isVersal_stalkBase` is
the same comparison with the base data taken as hypotheses.

What `(2) ⇒ (1)` still lacks is therefore the two conditions of Tag 06IU for that formal
object — the surjectivity of `Deformation.mapIsomorphismClasses` for its associated morphism
at the dual numbers, and the lifting of algebra maps along a small extension — over
`𝒞_{𝒪_{S,s}}`. Conditions (i) and (ii) and `ξ` are stated over the ring `Λ` of the affine
open, so proving them there and transferring will need a change of deformation base at the
level of versality, from `𝒞_Λ` to `𝒞_{𝒪_{S,s}}`. That is the direction opposite to
`Deformation.Artin.liftsAtResiduePoint_changeBase`, and one level up — for
`Deformation.IsVersal` rather than `Deformation.Artin.LiftsAtResiduePoint` — and unlike that
transfer it needs an actual ring map `Λ ⟶ 𝒪_{S,s}` compatible with `iΛ`, since restriction of
scalars is what carries an `𝒪_{S,s}`-algebra back to a `Λ`-algebra. The tree has no such
transfer at the level of versality.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 07YK](https://stacks.math.columbia.edu/tag/07YK)
* [Stacks Project, Tag 07YL](https://stacks.math.columbia.edu/tag/07YL)
* [Stacks Project, Tag 00IN](https://stacks.math.columbia.edu/tag/00IN)
-/

@[expose] public noncomputable section

open CategoryTheory
open ComplexShape (upIntRelNegOneZero)
open CochainComplex.DerivedExtensionScalars

universe u

namespace Deformation.Artin

attribute [local instance] HasDerivedCategory.standard

/-! ### Boundedness of the naive cotangent complex -/

/-- The naive cotangent complex `NL_{A/Λ}` lies in `D⁻(A)`: it is the image of a complex
concentrated in the cohomological degrees `-1` and `0`. This is the hypothesis under which
the duality of Stacks 07YK applies to it. -/
public theorem minus_derivedNaiveCotangentComplex (Λ A : Type u) [CommRing Λ] [CommRing A]
    [Algebra Λ A] :
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).minus
      (derivedNaiveCotangentComplex Λ A) := by
  refine ⟨0, ?_⟩
  have hstrict : (naiveCotangentDouble Λ A).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact HomologicalComplex.isZero_double_X _ upIntRelNegOneZero i (by omega) (by omega)
  exact inferInstanceAs ((DerivedCategory.Q.obj (naiveCotangentDouble Λ A)).IsLE 0)

/-! ### Precomposition on linear duals -/

/-- A square of bijections turns one map into the other. -/
private theorem conj_eq {A B C D : Type*} (ea : A ≃ C) (eb : B ≃ D)
    (F : A → B) (G : C → D) (hFG : ∀ a, eb (F a) = G (ea a)) :
    G = eb ∘ F ∘ ea.symm := by
  funext c
  rw [Function.comp_apply, Function.comp_apply, hFG, ea.apply_symm_apply]

/-- Over a field, precomposition with `h` on maps into a one-dimensional space is injective
exactly when `h` is surjective, and surjective exactly when `h` is injective. -/
private theorem precompDual_iff {k : Type u} [Field k] {M N K : ModuleCat.{u} k}
    (e : (K : Type u) ≃ₗ[k] k) (h : M ⟶ N) :
    (Function.Injective (fun α : N ⟶ K => h ≫ α) ↔ Function.Surjective h) ∧
    (Function.Surjective (fun α : N ⟶ K => h ≫ α) ↔ Function.Injective h) := by
  let a : ∀ P : ModuleCat.{u} k, (P ⟶ K) ≃ Module.Dual k P := fun P =>
    ModuleCat.homEquiv.trans (LinearEquiv.congrRight e).toEquiv
  have hconj := conj_eq (a N) (a M) (fun α => h ≫ α) h.hom.dualMap fun _ => rfl
  exact ⟨(by rw [hconj, Equiv.comp_injective, Equiv.injective_comp] :
      Function.Injective h.hom.dualMap ↔ _).symm.trans LinearMap.dualMap_injective_iff,
    (by rw [hconj, Equiv.comp_surjective, Equiv.surjective_comp] :
      Function.Surjective h.hom.dualMap ↔ _).symm.trans LinearMap.dualMap_surjective_iff⟩

/-! ### Condition (2) of Stacks 07YM in terms of `Ext` -/

/-- The duality of Stacks 07YK carries precomposition with `ξ` on `Ext^i_A(−, k)` to
precomposition with `H^{-i}(ξ ⊗ᴸ_A k)` on `k`-linear duals, so it exchanges injectivity and
surjectivity of the two. -/
private theorem extPrecomp_iff {A k : Type u} [CommRing A] [Field k] (f : A →+* k)
    (E N : DerivedCategory.Minus (ModuleCat.{u} A)) (ξ : E.1 ⟶ N.1) (i : ℤ) :
    (Function.Injective
        (fun α : DerivedCategory.Ext N.1
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              ((ModuleCat.restrictScalars f).obj (ModuleCat.of k (ULift.{u} k)))) i =>
          ξ ≫ α) ↔
      Function.Surjective
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (-i)).map
          ((totalDerivedExtensionScalars.{u, u, u} f).functor.map ξ))) ∧
    (Function.Surjective
        (fun α : DerivedCategory.Ext N.1
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              ((ModuleCat.restrictScalars f).obj (ModuleCat.of k (ULift.{u} k)))) i =>
          ξ ≫ α) ↔
      Function.Injective
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (-i)).map
          ((totalDerivedExtensionScalars.{u, u, u} f).functor.map ξ))) := by
  let g := (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (-i)).map
    ((totalDerivedExtensionScalars.{u, u, u} f).functor.map ξ)
  let eE := DerivedCategory.extIntoFieldEquivDualBaseChangeHomology.{u, u, u} f E i
  let eN := DerivedCategory.extIntoFieldEquivDualBaseChangeHomology.{u, u, u} f N i
  have hconj := conj_eq eN.toEquiv eE.toEquiv (fun α => ξ ≫ α) (fun β => g ≫ β)
    (fun α => DerivedCategory.extIntoFieldEquivDualBaseChangeHomology_naturality f N E i ξ α)
  have hdual := precompDual_iff (K := ModuleCat.of k (ULift.{u} k)) ULift.moduleEquiv g
  rwa [hconj, Equiv.comp_injective, Equiv.injective_comp, Equiv.comp_surjective,
    Equiv.surjective_comp] at hdual

/-- **Stacks 07YM, condition (2) in degree `-1`.** For a morphism `ξ : E ⟶ NL_{A/Λ}` of
`D⁻(A)` and a ring map `A ⟶ k` to a field, the map
`H^{-1}(E ⊗ᴸ_A k) ⟶ H^{-1}(NL_{A/Λ} ⊗ᴸ_A k)` is surjective exactly when the induced map
`Ext¹_A(NL_{A/Λ}, k) ⟶ Ext¹_A(E, k)`, that is precomposition with `ξ`, is injective. This is
the first of the two invocations of Stacks 07YK in the proof of Stacks 07YM: in the direction
`(1) ⇒ (2)` a failure of the surjectivity produces a nonzero class of `Ext¹_A(NL_{A/Λ}, k)`
killed by `ξ`, which is the input of Stacks 07YL, and in the direction `(2) ⇒ (1)` the
injectivity is what forces the obstruction class to vanish. -/
@[stacks 07YM "condition (2) in degree -1 as injectivity of Ext¹(NL_{A/Λ}, k) → Ext¹(E, k)"]
public theorem surjective_derivedFibre_neg_one_iff_injective_extOne
    {Λ A k : Type u} [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] (f : A →+* k)
    (E : DerivedCategory (ModuleCat.{u} A))
    (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).minus E)
    (ξ : E ⟶ derivedNaiveCotangentComplex Λ A) :
    Function.Surjective
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (-1)).map
          ((totalDerivedExtensionScalars.{u, u, u} f).functor.map ξ)) ↔
      Function.Injective
        (fun α : DerivedCategory.Ext (derivedNaiveCotangentComplex Λ A)
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              ((ModuleCat.restrictScalars f).obj (ModuleCat.of k (ULift.{u} k)))) 1 =>
          ξ ≫ α) :=
  (extPrecomp_iff f ⟨E, hE⟩ ⟨derivedNaiveCotangentComplex Λ A,
    minus_derivedNaiveCotangentComplex Λ A⟩ ξ 1).1.symm

/-- **Stacks 07YM, condition (2) in degree `0`.** For a morphism `ξ : E ⟶ NL_{A/Λ}` of
`D⁻(A)` and a ring map `A ⟶ k` to a field, the map `H^0(E ⊗ᴸ_A k) ⟶ H^0(NL_{A/Λ} ⊗ᴸ_A k)` is
injective exactly when the induced map `Ext⁰_A(NL_{A/Λ}, k) ⟶ Ext⁰_A(E, k)`, that is
precomposition with `ξ`, is surjective. This is the second of the two invocations of Stacks
07YK in the proof of Stacks 07YM: condition (ii) identifies the right-hand map with the map
`Der_Λ(A, k) ⟶ T_x(k)` from tangent vectors of `U` at `u₀` to infinitesimal deformations of
`x₀`, whose surjectivity is what versality provides. -/
@[stacks 07YM "condition (2) in degree 0 as surjectivity of Ext⁰(NL_{A/Λ}, k) → Ext⁰(E, k)"]
public theorem injective_derivedFibre_zero_iff_surjective_extZero
    {Λ A k : Type u} [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] (f : A →+* k)
    (E : DerivedCategory (ModuleCat.{u} A))
    (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).minus E)
    (ξ : E ⟶ derivedNaiveCotangentComplex Λ A) :
    Function.Injective
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
          ((totalDerivedExtensionScalars.{u, u, u} f).functor.map ξ)) ↔
      Function.Surjective
        (fun α : DerivedCategory.Ext (derivedNaiveCotangentComplex Λ A)
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              ((ModuleCat.restrictScalars f).obj (ModuleCat.of k (ULift.{u} k)))) 0 =>
          ξ ≫ α) :=
  (extPrecomp_iff f ⟨E, hE⟩ ⟨derivedNaiveCotangentComplex Λ A,
    minus_derivedNaiveCotangentComplex Λ A⟩ ξ 0).2.symm

/-! ### The Artin–Rees step -/

/-- **Stacks 07YM, the Artin–Rees step of the implication `(1) ⇒ (2)`.** Let `A'` be a
Noetherian ring and let `p'` and `I` be ideals with `p' · I = 0`. Then `(p')^n ∩ I = 0` for
some `n > 1`.

In the source `A' ⟶ A` is the square-zero extension supplied by Stacks 07YL, `I` is its
kernel and `p' = Ker(A' ⟶ k)` is the prime over the closed point `u₀`; the kernel is a
one-dimensional `k`-vector space, so it is annihilated by `p'`, and the conclusion is what
makes the kernel of `A'/(p')^n ⟶ A/p^n` equal to `I` and hence that map a small extension of
local Artinian rings. The proof is the Artin–Rees lemma (Stacks 00IN) applied to the ideal
`p'` of `A'` and the submodule `I` of `A'`: beyond the Artin–Rees constant `c` the
intersection `(p')^n ∩ I` is contained in `(p')^{n - c} · I`, which vanishes as soon as
`n > c`. -/
@[stacks 07YM "the Artin–Rees step of (1) ⇒ (2): (p')^n ∩ I = 0 for some n > 1"]
public theorem exists_pow_inf_eq_bot_of_mul_eq_bot {A' : Type*} [CommRing A']
    [IsNoetherianRing A'] (p' I : Ideal A') (hpI : p' * I = ⊥) :
    ∃ n > 1, p' ^ n ⊓ I = ⊥ := by
  obtain ⟨c, hc, hr⟩ := artin_rees p' (I : Submodule A' A')
  refine ⟨c + 2, by omega, ?_⟩
  have h := hr (c + 2) (by omega)
  rw [show p' ^ (c + 2) • (⊤ : Submodule A' A') = p' ^ (c + 2) by simp,
    show c + 2 - c = 2 by omega] at h
  have hle : p' ^ 2 • ((p' ^ c • (⊤ : Submodule A' A')) ⊓ (I : Submodule A' A'))
      ≤ p' ^ 1 • (I : Submodule A' A') :=
    Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) inf_le_right
  have hbot : p' ^ 1 • (I : Submodule A' A') = ⊥ := by
    rw [pow_one, Ideal.smul_eq_mul, hpI]
  exact le_antisymm (h.le.trans (hle.trans hbot.le)) bot_le

end Deformation.Artin
