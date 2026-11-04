module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSections
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsBaseChange
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.PseudoCoherent.BaseChangeFlat

/-!
# One finite projective complex computing the cohomology of every base change

Let `A` be a Noetherian ring, `f : X ⟶ Spec A` a proper morphism and `F` a coherent
`𝒪_X`-module flat over `A`. This file produces a *single* bounded complex `M` of finite
projective `A`-modules which computes the cohomology of **every** base change: for a ring
homomorphism `φ : A ⟶ A'` and a cartesian square exhibiting `X'` as `X ×_{Spec A} Spec A'`,

`RΓ(X', g^* F) ≅ M ⊗_A A'`  in  `D(A')`,  hence  `Hⁱ(X', g^* F) ≅ Hⁱ(M ⊗_A A')`.

This is [Stacks, Tag 07VL]. The complex `M` is the perfect model of `RΓ(X, F)` supplied by
[Stacks, Tag 07VK] (1), and the comparison is the base-change map of [Stacks, Tag 07VK] (2)
composed with the identification of the derived extension of scalars of a bounded termwise flat
complex with the termwise one ([Stacks, Tag 06XY]) — a finite projective module is flat, so `M`
qualifies.

## Main results

* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.exists_finiteProjectiveModel_derivedIso`:
  the model `M` together with, for every base change, an isomorphism
  `RΓ(X', g^* F) ≅ Q(M ⊗_A A')` in `D(A')`.
* `…exists_finiteProjectiveModel_homology_iso`: the same model together
  with the degreewise comparison `Hⁱ(X', g^* F) ≅ Hⁱ(M ⊗_A A')`.

## Implementation notes

`Hⁱ(X', g^* F)` is spelled as the `i`-th homology of `RΓ(X', g^* F)` read in `D(A')`, namely
`DerivedCategory.homologyFunctor (ModuleCat A') i` applied to `derivedGlobalSectionsOverBase`;
this is the spelling the surrounding `Perfect` development uses, and the one in which the
right-hand side `Hⁱ(M ⊗_A A')` is the homology of an honest complex of `A'`-modules.

The whole file runs under `HasDerivedCategory.standard` at priority `10000`, as
`ProperFlatGlobalSections.lean` does; results proved under a different choice of derived-category
model do not unify with those.

The base change is taken in the universe of the geometry, as everything in
`ProperFlatGlobalSectionsBaseChange.lean` is. The cover that the base-change map of
[Stacks, Tag 07VK] (2) takes as data does not appear in the statements below: properness supplies
one through `exists_finiteAffineCover_of_isProper`, so the model is universal for the morphism
and not relative to a choice of cover.

**Where the functoriality is.** The source says the identification holds "functorially in `A'`".
The statements below are the identification for every base change, by a canonical comparison; the
naturality squares relating two base changes `A' ⟶ A''` are the subject of
`ProperFlatGlobalSections.exists_finiteProjectiveModel_homology_iso_functorial`
of `StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatGlobalSectionsFunctorialModel.lean`, which
states both clauses of the remark together, under the same hypotheses, and carries the tag.

**No conditional hypothesis.** [Stacks, Tag 07VK] (1) is available unconditionally as
`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.isPerfect_derivedGlobalSections`: the
finiteness input it needs — the affine-base case of [Stacks, Tag 02O5], equivalent to
[Stacks, Tag 02O6] — is discharged there by the hypothesis-free
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase`. Clause (2)
of [Stacks, Tag 07VK], the base-change comparison, is unconditional as well. So the statements
below assume nothing beyond the source's own hypotheses.

## References

* [Stacks Project, Tag 07VL](https://stacks.math.columbia.edu/tag/07VL)
* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657)
* [Stacks Project, Tag 06XY](https://stacks.math.columbia.edu/tag/06XY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (F : X.Modules)

/-- **The termwise extension of scalars of a complex of `A`-modules along `φ : A ⟶ A'`.** This is
the complex written `M ⊗_A A'` in [Stacks, Tag 07VL]. -/
abbrev extendScalarsComplex {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
    (M : CochainComplex (ModuleCat.{u} A) ℤ) : CochainComplex (ModuleCat.{u} A') ℤ :=
  ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M

/-- **A bounded complex of finite projective `A`-modules computing `RΓ` of every base change.**
For `A` Noetherian, `f` proper and `F` coherent and flat over `A`, there is a single bounded
complex `M` of finite projective `A`-modules such that for every homomorphism `φ : A ⟶ A'` and
every cartesian square exhibiting `X'` as the base change of `X` along `Spec A' ⟶ Spec A`,

`RΓ(X', g^* F) ≅ M ⊗_A A'`  in  `D(A')`.

`M` is the perfect model of `RΓ(X, F)` of [Stacks, Tag 07VK] (1); the isomorphism is the inverse
of the base-change map of [Stacks, Tag 07VK] (2) followed by that model and by the comparison of
derived with termwise extension of scalars, which is invertible because the terms of `M` are
projective, hence flat. -/
theorem exists_finiteProjectiveModel_derivedIso [IsNoetherianRing A] [IsProper f]
    [F.IsCoherent] (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    ∃ (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ),
      M.IsStrictlyGE a ∧ M.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Finite A (M.X i)) ∧ (∀ i : ℤ, Module.Projective A (M.X i)) ∧
        ∀ {A' : Type u} [CommRing A'] (φ : A →+* A') {X' : Scheme.{u}}
          {f' : X' ⟶ Spec (.of A')} {g : X' ⟶ X}
          (_hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))),
          Nonempty (derivedGlobalSectionsOverBase f' ((Scheme.Modules.pullback g).obj F) ≅
            DerivedCategory.Q.obj (extendScalarsComplex φ M)) := by
  classical
  have hqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  obtain ⟨M, a, b, hGE, hLE, hfin, hproj, ⟨e⟩⟩ :=
    isPerfect_derivedGlobalSections f F hflat
  refine ⟨M, a, b, hGE, hLE, hfin, hproj, ?_⟩
  intro A' _ φ X' f' g hsq
  have hLE' : M.IsStrictlyLE b := hLE
  have hflatM : ∀ n : ℤ, Module.Flat A (M.X n) := fun n =>
    have := hproj n
    Module.Flat.of_projective
  obtain ⟨I, hI, hIlin, U, hU, hUaff, haff⟩ := exists_finiteAffineCover_of_isProper f
  have := hI
  have := hIlin
  have hbc := isIso_derivedGlobalSectionsBaseChangeMap φ hsq F U hU hUaff haff hflat
  exact ⟨(asIso (derivedGlobalSectionsBaseChangeMap φ hsq F U hU hUaff haff)).symm ≪≫
    (StacksDraft.PseudoCoherence.extendScalarsDerived φ).mapIso e ≪≫
    StacksDraft.PseudoCoherence.extendScalarsDerivedIsoOfFlat φ M b⟩

/-- **One finite projective model for every base change.** Let `A` be a Noetherian ring,
`f : X ⟶ Spec A` proper and `F` a coherent `𝒪_X`-module flat over `A`. Then there is a bounded
complex `M` of finite projective `A`-modules such that for every homomorphism `φ : A ⟶ A'`, every
cartesian square exhibiting `X'` as the base change of `X` along `Spec A' ⟶ Spec A` and every
degree `i`,

`Hⁱ(X', g^* F) ≅ Hⁱ(M ⊗_A A')`.

This is the consequence the source draws from [Stacks, Tag 07VK]: the cohomology of every base
change is computed by one fixed finite complex of finite projective modules. Flatness of `F` over
the base is what makes the comparison invertible, and is essential — without it the base-change
map of [Stacks, Tag 07VK] (2) need not be an isomorphism.

The comparison is obtained from `exists_finiteProjectiveModel_derivedIso` by applying the homology
functor of `D(A')` and reading the homology of a complex through
`DerivedCategory.homologyFunctorFactors`. -/
theorem exists_finiteProjectiveModel_homology_iso [IsNoetherianRing A] [IsProper f]
    [F.IsCoherent] (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    ∃ (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ),
      M.IsStrictlyGE a ∧ M.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Finite A (M.X i)) ∧ (∀ i : ℤ, Module.Projective A (M.X i)) ∧
        ∀ {A' : Type u} [CommRing A'] (φ : A →+* A') {X' : Scheme.{u}}
          {f' : X' ⟶ Spec (.of A')} {g : X' ⟶ X}
          (_hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) (i : ℤ),
          Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') i).obj
              (derivedGlobalSectionsOverBase f' ((Scheme.Modules.pullback g).obj F)) ≅
            (extendScalarsComplex φ M).homology i) := by
  obtain ⟨M, a, b, hGE, hLE, hfin, hproj, hiso⟩ :=
    exists_finiteProjectiveModel_derivedIso f F hflat
  refine ⟨M, a, b, hGE, hLE, hfin, hproj, ?_⟩
  intro A' _ φ X' f' g hsq i
  obtain ⟨e⟩ := hiso φ hsq
  exact ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} A') i).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A') i).app (extendScalarsComplex φ M)⟩

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end
