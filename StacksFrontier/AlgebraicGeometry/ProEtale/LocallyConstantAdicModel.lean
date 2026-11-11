module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleComplexes
public import StacksFrontier.CategoryTheory.Abelian.InverseSystemProDominated
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible.WContractibleRings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Adic models of a constructible complex with locally constant reduction

Let `X` be a weakly contractible affine scheme, `Λ` a Noetherian ring and `I ⊆ Λ` an ideal.
This file supplies vocabulary for the section "A suitable derived category" of the chapter on
pro-étale cohomology (the adic local structure of Stacks 09C3, the sections modules of Stacks
09C5) and the pro-domination step of the source's proof of Stacks 09C5. Stacks 09C5 itself is
`AlgebraicGeometry.ProEtale.isMittagLefflerCategorical_derivedReductionSectionsSystem`
(`StacksFrontier/AlgebraicGeometry/ProEtale/ConstructibleReductionSections.lean`) and
`isMittagLefflerCategorical_derivedReductionSectionsSystem_of_isConstructibleViaDerivedReduction`
(`StacksFrontier/AlgebraicGeometry/ProEtale/AdicModelReductionSections.lean`), stated for the
inverse system with its canonical transition maps.

Stacks 09C5 says: if `K` is an object of `D_cons(X, Λ)` and every `K ⊗_Λ^L Λ/Iⁿ` is isomorphic
to a complex of constant sheaves of `Λ/Iⁿ`-modules, then the inverse system
`n ↦ H⁰(X, K ⊗_Λ^L Λ/Iⁿ)` satisfies the Mittag-Leffler condition.

Its proof goes through Stacks 09C3, which says that `X` decomposes into a finite disjoint union
of opens `U_i` on each of which `K` is represented by a complex
`\underline{M^a}^∧ → ⋯ → \underline{M^b}^∧` of completed constant sheaves of finite projective
`Λ^∧`-modules, *for some* maps of sheaves of `Λ`-modules between those terms — the
differentials are not asserted to be the constant ones. That statement is **not** formalized
here; see "Stacks 09C3 is not formalized here" below. What is provided is its conclusion as a
predicate, `HasFiniteDisjointCompletedConstantModel`, so that the statement is available to be
proved later and to be cited as a hypothesis in the meantime.

## Main definitions

* `AlgebraicGeometry.ProEtale.constantSheafOverCoefficients`: the constant sheaf of a
  `Λ`-module, read over the constant coefficient ring sheaf.
* `AlgebraicGeometry.ProEtale.IsConstantSheafComplexModel`: an object of `D(X_proét, Λ)` is
  isomorphic to a complex of constant sheaves of `Λ`-modules.
* `AlgebraicGeometry.ProEtale.IsCompletedConstantComplexModel`: an object of `D(X_proét, Λ)` is
  isomorphic to a bounded complex whose terms are completed constant sheaves of finite
  projective `Λ^∧`-modules, with unspecified differentials. This is the local conclusion of
  Stacks 09C3, and it is strictly weaker than
  `AlgebraicGeometry.ProEtale.IsAdicLisseDerivedSheaf` of Stacks 09C4, where the differentials
  are the constant ones induced by a complex of `Λ^∧`-modules.
* `AlgebraicGeometry.ProEtale.HasFiniteDisjointCompletedConstantModel`: the conclusion of
  Stacks 09C3, a finite disjoint open covering carrying such models. The predicate only; the
  statement that it holds is not proved here.
* `AlgebraicGeometry.ProEtale.reductionSectionsObj`: the `Λ`-module `H⁰(X, K ⊗_Λ^L Λ/Iⁿ)`.
* `AlgebraicGeometry.ProEtale.reductionSectionsSystem`: an inverse system with terms
  `H⁰(X, K ⊗_Λ^L Λ/Iⁿ)`, assembled from an arbitrary family of transition maps. The system with
  the canonical transition maps is `AlgebraicGeometry.ProEtale.derivedReductionSectionsSystem`.

## Main results

* `AlgebraicGeometry.ProEtale.hasFiniteDisjointCompletedConstantModel_of_constantDifferentialModel`:
  the forgetting step, from a finite disjoint open covering carrying models whose differentials
  are the constant ones to the same covering read as carrying models with unspecified
  differentials. This is infrastructure, not Stacks 09C3: it assumes the covering.
* `AlgebraicGeometry.ProEtale.surjective_adicQuotientModuleSystem_map`: the transition maps of
  the adic quotient system `n ↦ N/IⁿN` are surjective.
* `AlgebraicGeometry.ProEtale.isMittagLefflerCategorical_of_proDominated_adicQuotient`: an
  inverse system of `Λ`-modules pro-dominated by an adic quotient system is Mittag-Leffler.
* `AlgebraicGeometry.ProEtale.isMittagLefflerCategorical_reductionSectionsSystem`: the
  pro-domination step of the source's proof of Stacks 09C5: a system with terms
  `H⁰(X, K ⊗_Λ^L Λ/Iⁿ)` pro-dominated by an adic quotient system is Mittag-Leffler. It is not
  Stacks 09C5 and is untagged.

## Implementation notes

The universe conventions, the ringed site `constantCoefficientRingedSite`, the derived category
`DerivedSheaves`, the constructibility condition `IsConstructibleDerivedSheaf`, the completed
constant sheaves `completedConstantCoefficientSheafFunctor` and the restriction data
`CoefficientRestriction` are all those of
`StacksFrontier/AlgebraicGeometry/ProEtale/ConstructibleComplexes.lean`, where the preceding
lemma 09C4 of the same section lives; nothing is redefined here.

A "finite disjoint open covering `X = ∐ U_i`" is a finite family of opens of `X` which is
pairwise disjoint and whose supremum is `⊤`; the restriction of `K` to `U_i` is taken along a
`CoefficientRestriction` datum for the open immersion `U_i.ι`, exactly as Stacks 09C4 (2) takes
the restriction to a stratum.

Weak contractibility of `X` is `ProetaleWContractible.IsWeaklyContractibleObj` of Stacks 090L,
the property of the scheme itself as an object of the big pro-étale site, rather than the
property of the terminal object of its small site; this is how the chapter's other statements
about weakly contractible schemes are phrased in the library.

A complex of constant sheaves is a complex of sheaves of coefficient modules each of whose
*terms* is a constant sheaf; its differentials are arbitrary morphisms of sheaves. This is what
the source asserts, both in 09C3 (for the completed constant sheaves) and in the hypothesis of
09C5, and it is why these conditions are expressed through termwise isomorphisms rather than by
applying a functor to a complex of modules.

### Stacks 09C3 is not formalized here

No declaration in this file carries `@[stacks 09C3]`, and none should until the statement is
proved. The entire content of 09C3 is that the finite disjoint open covering *exists*, and that
is what the library cannot yet supply. The source's proof is an induction on `b - a` whose base
case rests on the surjection onto `H^b(K)` from a finite free completed constant sheaf
(Stacks 09BQ), on Nakayama for derived complete sheaves (Stacks 09BP), on the recognition of a
flat finite type module over `Λ/I` as finite projective, and on lifting idempotents along
`Λ^∧ = lim Λ/Iⁿ`; and whose inductive step rests on lifting that surjection to
`D(X_proét, Λ)` through weak contractibility and on the Tor amplitude of the third term of the
resulting triangle (Stacks 09C2). None of those inputs is available.

What this file contributes towards 09C3 is vocabulary and one forgetting step:
`HasFiniteDisjointCompletedConstantModel`, the predicate in which the conclusion is phrased,
and `hasFiniteDisjointCompletedConstantModel_of_constantDifferentialModel`, which passes from a
covering carrying models whose differentials are the constant ones induced by a complex of
`Λ^∧`-modules — Stacks 09C4 (1) realised globally on each member — to the same covering read as
carrying the source's weaker termwise models. That lemma assumes the covering, so it is not the
tag and is deliberately untagged: the existence of the covering is exactly what 09C3 asserts,
and the only thing the lemma adds is to forget that the differentials were the induced constant
ones. It is the step reconciling the library's `IsAdicLisseDerivedSheaf` shape with the shape
09C3 asserts, and it is what a future proof of 09C3 composes with.

### Stacks 09C5 is not stated here

The source's proof of 09C5 has six steps. Steps (1)–(5) produce, out of 09C3, Stacks 0658
(perfectness of the reduction), Stacks 09BE (local constancy of a map of complexes of constant
sheaves) and Stacks 09AW (the complex `M^•` of finite projective `Λ^∧`-modules with
`M^•/IⁿM^• ≅ E_n`), an identification of the inverse system `n ↦ H⁰(X, K ⊗_Λ^L Λ/Iⁿ)` with the
system `n ↦ H⁰(M^•/IⁿM^•)` of `Λ`-modules. Step (6) then compares that system, through the Tor
spectral sequence and the strict pro-vanishing of Tor of Stacks 0911, with the adic quotient
system `n ↦ H⁰(M^•)/IⁿH⁰(M^•)`, whose transition maps are surjective.

`isMittagLefflerCategorical_reductionSectionsSystem` below is the last step of that argument:
given pro-domination data for a system with terms `H⁰(X, K ⊗_Λ^L Λ/Iⁿ)` and arbitrary
transition maps, the system is Mittag-Leffler. The pro-domination data is an input of the
theorem, so it does not state 09C5 and carries no tag. Stacks 09C5 is proved, from exactly the
source's setting and with the canonical transition maps, in
`StacksFrontier/AlgebraicGeometry/ProEtale/ConstructibleReductionSections.lean` and
`StacksFrontier/AlgebraicGeometry/ProEtale/AdicModelReductionSections.lean`, along a different
route (an adic model through Stacks 0CQF and the Artin–Rees lemma).

### The reading of "a complex of constant sheaves" in 09C5

`IsConstantSheafComplexModel` (constant terms, arbitrary differentials) is the literal reading
of the hypothesis of 09C5, and under it the statement fails. Let `X = Spec C(βℕ, k)` with `k`
algebraically closed, a weakly contractible affine scheme with `π₀(X) = βℕ`; let `Λ = ℤ_p`,
`I = (p)`, and let `f : βℕ → ℤ_p` be the continuous extension of `j ↦ p^(j+1)`. The complex
`K = [\underline{Λ}^∧ --f--> \underline{Λ}^∧]` in degrees `0, 1` is derived complete, and
`K ⊗_Λ^L Λ/I = \underline{𝔽_p} ⊕ \underline{𝔽_p}[-1]`, so `K` lies in `D_cons(X, Λ)`; every
`K ⊗_Λ^L Λ/pⁿ = [\underline{ℤ/pⁿ} --f--> \underline{ℤ/pⁿ}]` is a complex of constant
sheaves. But `H⁰(X, K ⊗_Λ^L Λ/pⁿ) = {g ∈ C(βℕ, ℤ/pⁿ) | f g = 0}`, and for `m ≥ 1`, `N ≥ m` the
function supported on the isolated point `j = N - m` with value `p^(m-1)` lies in the image of
level `N` in level `m` but not in that of level `N + 1`; so the system is not Mittag-Leffler.
The source's proof begins "Say `K ⊗_Λ^L \underline{Λ/Iⁿ}` is isomorphic to `\underline{E_n}`
for some object `E_n` of `D(Λ/Iⁿ)`", which fixes the intended reading: the complex of
constant sheaves is the constant complex of an object of `D(Λ/Iⁿ)`. That is the hypothesis of
the tagged statements.

## References

* [Stacks Project, Tag 09C3](https://stacks.math.columbia.edu/tag/09C3)
* [Stacks Project, Tag 09C5](https://stacks.math.columbia.edu/tag/09C5)
* [Stacks Project, Tag 09C4](https://stacks.math.columbia.edu/tag/09C4)
* [Stacks Project, Tag 09C1](https://stacks.math.columbia.edu/tag/09C1)
* [Stacks Project, Tag 02N0](https://stacks.math.columbia.edu/tag/02N0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard
  SheafOfModules.hasSheafify_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat

/-- The transition maps of the adic quotient system `n ↦ N/IⁿN` of a module are surjective:
they are the canonical surjections between successive quotients of `N`. -/
theorem surjective_adicQuotientModuleSystem_map.{z, s}
    (Λ : Type s) [CommRing Λ] (I : Ideal Λ) (N : ModuleCat.{z} Λ) (n : ℕ) :
    Function.Surjective
      ((adicQuotientModuleSystem Λ I N).map (homOfLE (Nat.le_succ n)).op).hom := by
  rw [adicQuotientModuleSystem, Functor.ofOpSequence_map_homOfLE_succ]
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨Submodule.Quotient.mk y, rfl⟩

/-- **Mittag-Leffler from pro-domination by an adic quotient system.** An inverse system `F` of
`Λ`-modules admitting pro-domination data of shift `c` from the adic quotient system
`n ↦ N/IⁿN` satisfies the Mittag-Leffler condition of Stacks Tag 02N0. -/
theorem isMittagLefflerCategorical_of_proDominated_adicQuotient.{z, s}
    (Λ : Type s) [CommRing Λ] (I : Ideal Λ) (N : ModuleCat.{z} Λ)
    (F : ℕᵒᵖ ⥤ ModuleCat.{z} Λ) (c : ℕ)
    (β : ∀ n : ℕ, (adicQuotientModuleSystem Λ I N).obj (op (n + c)) ⟶ F.obj (op n))
    (hβ : ∀ (i j : ℕ) (h : i ≤ j),
      (adicQuotientModuleSystem Λ I N).map (homOfLE (Nat.add_le_add_right h c)).op ≫ β i =
        β j ≫ F.map (homOfLE h).op)
    (α : ∀ n : ℕ, F.obj (op (n + c)) ⟶ (adicQuotientModuleSystem Λ I N).obj (op n))
    (hαβ : ∀ n : ℕ, α (n + c) ≫ β n = F.map (homOfLE (show n ≤ n + c + c by omega)).op) :
    IsMittagLefflerCategorical F :=
  isMittagLefflerCategorical_of_proDominated F (adicQuotientModuleSystem Λ I N) c
    (surjective_adicQuotientModuleSystem_map Λ I N) β hβ α hαβ

variable (X : Scheme.{u}) (Λ : Type r) [CommRing Λ]

/-- The constant sheaf of a coefficient module, read as a sheaf of modules over the constant
coefficient ring sheaf. -/
def constantSheafOverCoefficients :
    ModuleCat.{max (u + 1) r w} Λ ⥤
      RingedSite.Modules.{u + 1, u, max (u + 1) r w}
        (constantCoefficientRingedSite.{u, r, w} X Λ) :=
  constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ) ⋙
    moduleSheafOverConstantCoefficientsFunctor.{u, r, w} X Λ

/-- An object of `D(X_proét, Λ)` is isomorphic to a complex of constant sheaves of
`Λ`-modules: there is a complex of sheaves of coefficient modules, with arbitrary
differentials, each of whose terms is the constant sheaf of a `Λ`-module.

This is weaker than being the constant complex of an object of `D(Λ)`: on a weakly contractible
affine scheme with infinitely many connected components the differentials can vary over
`π₀(X)`. With this reading in place of the constant complex, Stacks 09C5 fails; see the module
docstring. -/
def IsConstantSheafComplexModel (L : DerivedSheaves.{u, r, w} X Λ) : Prop :=
  ∃ C : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r w}
      (constantCoefficientRingedSite.{u, r, w} X Λ)) ℤ,
    (∀ k : ℤ, ∃ E : ModuleCat.{max (u + 1) r w} Λ,
      Nonempty (C.X k ≅ (constantSheafOverCoefficients.{u, r, w} X Λ).obj E)) ∧
    Nonempty (L ≅ DerivedCategory.Q.obj C)

variable (I : Ideal Λ)

/-- **The local conclusion of Stacks 09C3.** An object `L` of `D(X_proét, Λ)` is isomorphic to
a complex `\underline{M^a}^∧ → ⋯ → \underline{M^b}^∧` of completed constant sheaves of finite
projective `Λ^∧`-modules, the differentials being arbitrary morphisms of sheaves of coefficient
modules.

This is weaker than `AlgebraicGeometry.ProEtale.IsAdicLisseDerivedSheaf` of Stacks 09C4 (1) in
two ways: the isomorphism is global rather than pro-étale local, and the differentials are not
required to be the constant ones induced by a complex of `Λ^∧`-modules. -/
def IsCompletedConstantComplexModel (L : DerivedSheaves.{u, r, w} X Λ) : Prop :=
  ∃ (a b : ℤ) (C : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r w}
      (constantCoefficientRingedSite.{u, r, w} X Λ)) ℤ),
    C.IsStrictlyGE a ∧ C.IsStrictlyLE b ∧
    (∀ k : ℤ, ∃ M : ModuleCat.{max (u + 1) r w} (AdicCompletion I Λ),
      Module.Finite (AdicCompletion I Λ) M ∧ Module.Projective (AdicCompletion I Λ) M ∧
      Nonempty (C.X k ≅ (completedConstantCoefficientSheafFunctor.{u, r, w} X Λ I).obj
        ((restrictToCoefficients.{max (u + 1) r w, r} Λ I).obj M))) ∧
    Nonempty (L ≅ DerivedCategory.Q.obj C)

/-- **The conclusion of Stacks 09C3.** There is a finite disjoint open covering `X = ∐ U_i`
such that on each `U_i` the restriction of `K` has a model by a bounded complex of completed
constant sheaves of finite projective `Λ^∧`-modules. -/
def HasFiniteDisjointCompletedConstantModel (K : DerivedSheaves.{u, r, w} X Λ) : Prop :=
  ∃ (n : ℕ) (U : Fin n → X.Opens),
    Pairwise (fun i j => Disjoint (U i) (U j)) ∧ ⨆ i, U i = ⊤ ∧
    ∀ i, ∃ ρ : CoefficientRestriction.{u, r, w} Λ (U i).ι,
      IsCompletedConstantComplexModel.{u, r, w} (U i).toScheme Λ I (ρ.derived.obj K)

/-- The `Λ`-module `H⁰(X, K ⊗_Λ^L Λ/Iⁿ)`: the sections over the terminal object of the small
pro-étale site of the degree-zero cohomology sheaf of the derived reduction of `K` modulo `Iⁿ`,
read as a `Λ`-module by restricting scalars along `Λ → Λ/Iⁿ`. -/
def reductionSectionsObj (Tn : ∀ n : ℕ, DerivedReduction.{u, r, w} X Λ (I ^ n))
    (K : DerivedSheaves.{u, r, w} X Λ) (n : ℕ) : ModuleCat.{max (u + 1) r w} Λ :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj
    (((sheafSections (Scheme.ProEt.topology X)
        (ModuleCat.{max (u + 1) r w} (Λ ⧸ I ^ n))).obj (op (⊤_ X.ProEt))).obj
      ((toCoefficientModuleSheaf.{u, r, w} X (Λ ⧸ I ^ n)).obj
        ((DerivedCategory.homologyFunctor
          (RingedSite.Modules.{u + 1, u, max (u + 1) r w}
            (constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I ^ n))) 0).obj
          ((Tn n).baseChange.obj K))))

/-- An inverse system of `Λ`-modules with terms `H⁰(X, K ⊗_Λ^L Λ/Iⁿ)`, assembled from an
arbitrary family `t` of transition maps. The system with the canonical transition maps,
induced by the reductions `Λ/Iⁿ⁺¹ → Λ/Iⁿ`, is
`AlgebraicGeometry.ProEtale.derivedReductionSectionsSystem`. -/
def reductionSectionsSystem (Tn : ∀ n : ℕ, DerivedReduction.{u, r, w} X Λ (I ^ n))
    (K : DerivedSheaves.{u, r, w} X Λ)
    (t : ∀ n : ℕ, reductionSectionsObj.{u, r, w} X Λ I Tn K (n + 1) ⟶
      reductionSectionsObj.{u, r, w} X Λ I Tn K n) :
    ℕᵒᵖ ⥤ ModuleCat.{max (u + 1) r w} Λ :=
  Functor.ofOpSequence (X := reductionSectionsObj.{u, r, w} X Λ I Tn K) t

section Statements

variable [IsNoetherianRing Λ]
  [∀ U : X.ProEt,
    HasWeakSheafify ((Scheme.ProEt.topology X).over U) (ModuleCat.{max (u + 1) r w} (Λ ⧸ I))]
  [∀ U : (constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r w, max (u + 1) r w,
      max (u + 1) r w}
      ((constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) r w, max (u + 1) r w,
      max (u + 1) r w}
      ((constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).over U).O).obj M).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).C)
    (P Q : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) r w}
      ((constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor P Q
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).over U).O) (ComplexShape.up ℤ)]

/-- Forgetting the constancy of the differentials of a finite disjoint family of adic models.

Given a finite disjoint open covering `X = ∐ U_i` on each member of which `K` is isomorphic to
the complex `\underline{M^a}^∧ → ⋯ → \underline{M^b}^∧` of completed constant sheaves attached
to a bounded complex `M^•` of finite projective `Λ^∧`-modules, with *its* differentials, the
same covering carries models in the weaker sense of
`AlgebraicGeometry.ProEtale.IsCompletedConstantComplexModel`, where the differentials are
arbitrary morphisms of sheaves. The strict bounds are transported through the completed
constant sheaf functor, which preserves zero objects, and the termwise models are the terms of
the transported complex.

This is infrastructure, not Stacks 09C3: the covering, which is the whole content of that tag,
is a hypothesis here. It is the shape change that lets a future proof of 09C3 — which will have
to produce the covering from Stacks 09BQ, 09BP, idempotent lifting along `Λ^∧ = lim Λ/Iⁿ` and
Stacks 09C2 — be stated against the library's `IsAdicLisseDerivedSheaf` of Stacks 09C4 (1). -/
theorem hasFiniteDisjointCompletedConstantModel_of_constantDifferentialModel [IsAffine X]
    (_hX : ProetaleWContractible.IsWeaklyContractibleObj X)
    (T : DerivedReduction.{u, r, w} X Λ I)
    (D : ∀ U : (constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r w,
          max (u + 1) r w + 1}
        ((constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).over U))
    (K : DerivedSheaves.{u, r, w} X Λ)
    (_hK : IsConstructibleDerivedSheaf.{u, r, w} X Λ I T D K)
    (_hloc : ∀ i : ℤ, Stacks.ConstantSheaf.IsLocallyConstant (Scheme.ProEt.topology X)
      ((toCoefficientModuleSheaf.{u, r, w} X (Λ ⧸ I)).obj
        ((DerivedCategory.homologyFunctor
          (RingedSite.Modules.{u + 1, u, max (u + 1) r w}
            (constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I))) i).obj (T.baseChange.obj K))))
    (hmodel : ∃ (n : ℕ) (U : Fin n → X.Opens),
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧ ⨆ i, U i = ⊤ ∧
      ∀ i, ∃ ρ : CoefficientRestriction.{u, r, w} Λ (U i).ι,
        ∃ (a b : ℤ) (M : CochainComplex
            (ModuleCat.{max (u + 1) r w} (AdicCompletion I Λ)) ℤ),
          M.IsStrictlyGE a ∧ M.IsStrictlyLE b ∧
          (∀ k : ℤ, Module.Finite (AdicCompletion I Λ) (M.X k) ∧
            Module.Projective (AdicCompletion I Λ) (M.X k)) ∧
          Nonempty (ρ.derived.obj K ≅ DerivedCategory.Q.obj
            ((completedConstantCoefficientComplex.{u, r, w} (U i).toScheme Λ I).obj M))) :
    HasFiniteDisjointCompletedConstantModel.{u, r, w} X Λ I K := by
  obtain ⟨n, U, hdisj, hcover, hpiece⟩ := hmodel
  refine ⟨n, U, hdisj, hcover, fun i => ?_⟩
  obtain ⟨ρ, a, b, M, hGE, hLE, hfp, ⟨e⟩⟩ := hpiece i
  have hF {Z : ModuleCat.{max (u + 1) r w} (AdicCompletion I Λ)} (hZ : IsZero Z) :=
    Functor.map_isZero (restrictToCoefficients.{max (u + 1) r w, r} Λ I ⋙
      completedConstantCoefficientSheafFunctor.{u, r, w} (U i).toScheme Λ I) hZ
  refine ⟨ρ, a, b, (completedConstantCoefficientComplex.{u, r, w} (U i).toScheme Λ I).obj M,
    ?_, ?_, fun k => ⟨M.X k, (hfp k).1, (hfp k).2, ⟨Iso.refl _⟩⟩, ⟨e⟩⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    exact fun k hk => hF (M.isZero_of_isStrictlyGE a k hk)
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun k hk => hF (M.isZero_of_isStrictlyLE b k hk)

omit [∀ U : X.ProEt,
  HasWeakSheafify ((Scheme.ProEt.topology X).over U) (ModuleCat.{max (u + 1) r w} (Λ ⧸ I))] in
/-- **The pro-domination step of the proof of Stacks 09C5.** Let `X` be an affine scheme, `K`
an object of `D(X_proét, Λ)` and `t` any family of transition maps for the modules
`H⁰(X, K ⊗_Λ^L Λ/Iⁿ)`. If the resulting inverse system is pro-dominated, with shift `c`, by the
adic quotient system `n ↦ N/IⁿN` of a `Λ`-module `N` (the maps `β`, `α` and the
compatibilities `hβ`, `hαβ`), then it is Mittag-Leffler.

This is step (6) of the source's proof once steps (1)–(5) have produced the pro-domination; the
data `N`, `c`, `α`, `β` is an input, and the transition maps are arbitrary, so this is not
Stacks 09C5. The hypotheses `_hX`, `_hK` and `_hconstant` are not used. Stacks 09C5 itself, with
the canonical transition maps and no pro-domination input, is
`AlgebraicGeometry.ProEtale.isMittagLefflerCategorical_derivedReductionSectionsSystem`. -/
theorem isMittagLefflerCategorical_reductionSectionsSystem [IsAffine X]
    (_hX : ProetaleWContractible.IsWeaklyContractibleObj X)
    (T : DerivedReduction.{u, r, w} X Λ I)
    (D : ∀ U : (constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) r w,
          max (u + 1) r w + 1}
        ((constantCoefficientRingedSite.{u, r, w} X (Λ ⧸ I)).over U))
    (K : DerivedSheaves.{u, r, w} X Λ)
    (_hK : IsConstructibleDerivedSheaf.{u, r, w} X Λ I T D K)
    (Tn : ∀ n : ℕ, DerivedReduction.{u, r, w} X Λ (I ^ n))
    (_hconstant : ∀ n : ℕ, IsConstantSheafComplexModel.{u, r, w} X (Λ ⧸ I ^ n)
      ((Tn n).baseChange.obj K))
    (t : ∀ n : ℕ, reductionSectionsObj.{u, r, w} X Λ I Tn K (n + 1) ⟶
      reductionSectionsObj.{u, r, w} X Λ I Tn K n)
    (N : ModuleCat.{max (u + 1) r w} Λ) (c : ℕ)
    (β : ∀ n : ℕ, (adicQuotientModuleSystem Λ I N).obj (op (n + c)) ⟶
      (reductionSectionsSystem.{u, r, w} X Λ I Tn K t).obj (op n))
    (hβ : ∀ (i j : ℕ) (h : i ≤ j),
      (adicQuotientModuleSystem Λ I N).map (homOfLE (Nat.add_le_add_right h c)).op ≫ β i =
        β j ≫ (reductionSectionsSystem.{u, r, w} X Λ I Tn K t).map (homOfLE h).op)
    (α : ∀ n : ℕ, (reductionSectionsSystem.{u, r, w} X Λ I Tn K t).obj (op (n + c)) ⟶
      (adicQuotientModuleSystem Λ I N).obj (op n))
    (hαβ : ∀ n : ℕ, α (n + c) ≫ β n =
      (reductionSectionsSystem.{u, r, w} X Λ I Tn K t).map
        (homOfLE (show n ≤ n + c + c by omega)).op) :
    IsMittagLefflerCategorical (reductionSectionsSystem.{u, r, w} X Λ I Tn K t) :=
  isMittagLefflerCategorical_of_proDominated_adicQuotient Λ I N
    (reductionSectionsSystem.{u, r, w} X Λ I Tn K t) c β hβ α hαβ

end Statements

end AlgebraicGeometry.ProEtale

end
