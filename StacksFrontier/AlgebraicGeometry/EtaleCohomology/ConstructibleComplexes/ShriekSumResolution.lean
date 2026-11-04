module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.BoundedAboveShriekComplex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Bounded above resolutions by shriek sums, and the implication (1) ⟹ (2) of Tag 0960

Let `X` be a quasi-compact and quasi-separated scheme, let `Λ` be a Noetherian ring and let
`K ∈ D^-(X_étale, Λ)`. Tag 0960 asserts the equivalence of

1. `K` lies in `D_c(X_étale, Λ)`, i.e. all cohomology sheaves of `K` are constructible;
2. `K` is represented by a bounded above complex whose terms are finite direct sums of sheaves
   `j_{U!} Λ-underline` with `U` an affine object of `X_étale`;
3. `K` is represented by a bounded above complex of flat constructible sheaves of `Λ`-modules.

The module
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.BoundedAboveShriekComplex`
states conditions (2) and (3) and proves (2) ⟹ (3), (3) ⟹ (1) and (2) ⟹ (1). This module
proves the converse (1) ⟹ (2), and with it the two remaining implications (1) ⟹ (3) and
(3) ⟹ (2), closing the equivalence; the equivalence itself is
`Stacks.EtaleCohomology.isConstructible_tfae`, and it is unconditional.

## Main definitions

* `Stacks.EtaleCohomology.IsAffineShriekSum` — a sheaf of `Λ`-modules isomorphic to a finite
  direct sum of sheaves `j_{U!} Λ-underline` with `U` affine; the predicate on the terms which
  condition (2) of Tag 0960 asks for.

## Main results

* `Stacks.EtaleCohomology.isConstructible_tfae` — **Tag 0960**, the equivalence of the three
  conditions, which this module completes.
* `Stacks.EtaleCohomology.isRepresentedByAffineShriekSumComplex_of_isConstructible` —
  **Tag 0960, the implication (1) ⟹ (2)**.
* `Stacks.EtaleCohomology.isRepresentedByBoundedAboveConstructibleFlatComplex_of_isConstructible`
  — **Tag 0960, the implication (1) ⟹ (3)**.
* `Stacks.EtaleCohomology.isRepresentedByAffineShriekSumComplex_of_constructibleFlat` —
  **Tag 0960, the implication (3) ⟹ (2)**.

## Implementation notes

### The shape of the proof

The source proves (1) ⟹ (2) by descending induction on `a`, building a complex
`ℱ^a → … → ℱ^b` of finite affine shriek sums together with a map to `K` which is an isomorphism
on cohomology in degrees `> a` and surjective in degree `a`; the inductive step applies Tag 095Z
to the cone of the map constructed so far and then invokes the octahedral axiom to assemble the
extended complex, and the complex of condition (2) is the limit of the resulting tower. That
step, in the derived category, is
`Stacks.EtaleCohomology.exists_affineShriekSum_distTriang_of_isConstructible`.

The construction carried out here replaces the tower of triangles by the same induction performed
on a cochain complex representing `K`, which avoids the limit entirely: a bounded above `K` is
`DerivedCategory.Q.obj` of a cochain complex `A` with `A^i = 0` for `i > a`
(`DerivedCategory.exists_iso_Q_obj_of_isLE`), and the complex of condition (2) is then built
degree by degree downwards from `a`, as a `ℕ`-indexed chain complex of layers which is extended
back to a `ℤ`-indexed cochain complex along `ComplexShape.embeddingUpIntLE`. Instead of a
cohomology isomorphism in high degrees and a surjection in the lowest degree built so far, each
layer records a map to the corresponding term of `A`, and the two conditions which make the
resulting map of complexes a quasi-isomorphism are checked once and for all at the end, in
`Stacks.Homology.BoundedAboveResolution.exists_quasiIso_isStrictlyLE_of_coversEpis`: surjectivity
on cohomology, which is why each layer contains a summand covering the cohomology of `A` in its
degree, and injectivity on cohomology up to refinements, which is why each layer contains a
second summand covering the cycles of the previous layer which become boundaries in `A`. The
map `DerivedCategory.Q` sends a quasi-isomorphism to an isomorphism, which produces the required
representation of `K`.

The engine is stated for an arbitrary abelian category, an arbitrary weak Serre class `R` and an
arbitrary class `G` of objects covering epimorphisms onto objects of `R`; nothing about étale
sheaves enters it, so it lives in
`StacksFrontier.Algebra.Homology.DerivedCategory.BoundedAboveResolution` and is shared with
Tag 0FCL. There the terms of the resolution are asked to lie in the very class `P` whose objects
the cohomology lies in, which is the case `R = G = P`; that would not be enough here, since the
terms must be finite affine shriek sums while the cohomology is merely constructible, which is
why the engine separates the two classes.

The intermediate layers are chosen, not canonical: `CoversEpis` asserts that a cover exists, and
the recursion picks one at each degree with `Nonempty.some`, which is why `Classical.choice`
appears in the axioms of every declaration of the construction. Nothing in the public interface
extracts data from an existence statement: the engine's conclusion and condition (2) of the source
are both existential, and every definition which does make such a choice is private to the engine's
module.

### Nothing is carried

All three implications of this module are unconditional. The one input of (1) ⟹ (3) which is not
shared with (1) ⟹ (2) is the flat constructibility of a finite affine shriek sum, used through
the second step (2) ⟹ (3) and supplied by
`AlgebraicGeometry.isConstructibleFlatModuleSheaf_sigma_moduleShriekConstant_of_quasiSeparated`;
see "Why quasi-separatedness is assumed" in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.BoundedAboveShriekComplex`
for what that input is and why quasi-separatedness of the ambient scheme is the only hypothesis
it needs. For (1) ⟹ (2) and (3) ⟹ (2) the class `G` of this module's application is
`Stacks.EtaleCohomology.IsAffineShriekSum`, and

* `G` contains the zero object and is closed under binary biproducts and isomorphism, which is
  proved here from nothing;
* `G` is contained in `R`, which is
  `AlgebraicGeometry.isConstructibleModuleSheaf_sigma_moduleShriekConstant` — Stacks 03S8 for
  sheaves of modules on each summand, assembled by the weak Serre property below;
* `G` covers epimorphisms onto objects of `R`, which is Stacks 093B (2) followed by Stacks 095P,
  `AlgebraicGeometry.exists_finite_epi_comp_sigma_moduleShriekConstant_affine`;
* `R` is a weak Serre class, which is Stacks 03RZ (3) for sheaves of modules,
  `AlgebraicGeometry.isWeakSerreClass_isConstructibleModuleSheafProperty`.

### Boundedness of `K`

Condition (1) of the source is `K ∈ D_c`, under the standing assumption `K ∈ D^-`. The latter is
carried as the hypothesis `hvan`, the vanishing of `H^i(K)` for `i > b`, in the same shape as in
`Stacks.EtaleCohomology.exists_affineShriekSum_distTriang_of_isConstructible`; by
`DerivedCategory.isLE_iff` it says exactly that `K` lies in `D^-`. It is not needed for
(3) ⟹ (2), where condition (3) supplies the bound.

## References

* [Stacks Project, Tag 0960](https://stacks.math.columbia.edu/tag/0960)
* [Stacks Project, Tag 095Z](https://stacks.math.columbia.edu/tag/095Z)
* [Stacks Project, Tag 095W](https://stacks.math.columbia.edu/tag/095W)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 013H](https://stacks.math.columbia.edu/tag/013H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Terms

open ZeroObject

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]

/-- A sheaf of `Λ`-modules on the small étale site of `X` which is isomorphic to a finite direct
sum of sheaves `j_{U!} Λ-underline` with `U` an affine object of that site.

This is the condition `Stacks.EtaleCohomology.IsRepresentedByAffineShriekSumComplex` imposes on
each term of the representing complex, named so that it can be handed to the resolution engine
`Stacks.Homology.BoundedAboveResolution.exists_quasiIso_isStrictlyLE_of_coversEpis` as the class
of allowed terms. -/
public def IsAffineShriekSum
    (M : Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ)) : Prop :=
  ∃ (n : ℕ) (U : Fin n → SmallEtale B X.obj X.property),
    (∀ j, IsAffine ((SmallEtale.toScheme B X.obj X.property).obj (U j))) ∧
      Nonempty (M ≅ ∐ fun j ↦ moduleShriekConstant.{u, r, r} B X Λ (U j))

/-- A sheaf isomorphic to a finite direct sum of affine shriek constants is itself one. -/
public theorem isAffineShriekSum_of_iso
    {M N : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)}
    (e : M ≅ N) (hM : IsAffineShriekSum.{u, r} B X Λ M) :
    IsAffineShriekSum.{u, r} B X Λ N := by
  obtain ⟨n, U, hU, ⟨eM⟩⟩ := hM
  exact ⟨n, U, hU, ⟨e.symm ≪≫ eM⟩⟩

/-- The zero sheaf is the empty direct sum of affine shriek constants. -/
public theorem isAffineShriekSum_zero
    [HasZeroObject (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ))] :
    IsAffineShriekSum.{u, r} B X Λ
      (0 : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)) := by
  refine ⟨0, Fin.elim0, (fun j ↦ j.elim0), ⟨HasZeroObject.zeroIsoIsInitial (IsInitial.ofUniqueHom
    (fun _ ↦ Sigma.desc (fun j : Fin 0 ↦ Fin.elim0 j)) (fun _ f ↦ ?_))⟩⟩
  exact Sigma.hom_ext _ _ (fun j ↦ Fin.elim0 j)

/-- A binary biproduct of finite direct sums of affine shriek constants is again one: the two
index sets are concatenated along `finSumFinEquiv`. -/
public theorem isAffineShriekSum_biprod
    [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)]
    {M N : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)}
    (hM : IsAffineShriekSum.{u, r} B X Λ M) (hN : IsAffineShriekSum.{u, r} B X Λ N) :
    IsAffineShriekSum.{u, r} B X Λ (M ⊞ N) := by
  classical
  let _ : HasFiniteBiproducts (Sheaf (SmallEtale.topology B X.obj X.property)
    (ModuleCat.{max (u + 1) r} Λ)) := Abelian.hasFiniteBiproducts
  obtain ⟨n, U, hU, ⟨eM⟩⟩ := hM
  obtain ⟨m, V, hV, ⟨eN⟩⟩ := hN
  let F : Fin n → Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ) := fun i ↦ moduleShriekConstant.{u, r, r} B X Λ (U i)
  let G : Fin m → Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ) := fun i ↦ moduleShriekConstant.{u, r, r} B X Λ (V i)
  let H : Fin n ⊕ Fin m → Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ) := Sum.elim F G
  let W : WalkingPair → Type := fun i ↦
    match i with
    | WalkingPair.left => Fin n
    | WalkingPair.right => Fin m
  let T : (i : WalkingPair) → W i → Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ) := fun i ↦
    match i with
    | WalkingPair.left => F
    | WalkingPair.right => G
  let eindex : (Σ i : WalkingPair, W i) ≃ (Fin n ⊕ Fin m) :=
    { toFun := fun
        | ⟨WalkingPair.left, i⟩ => Sum.inl i
        | ⟨WalkingPair.right, i⟩ => Sum.inr i
      invFun := fun
        | Sum.inl i => ⟨WalkingPair.left, i⟩
        | Sum.inr i => ⟨WalkingPair.right, i⟩
      left_inv := by rintro ⟨i, j⟩; cases i <;> rfl
      right_inv := by rintro (_ | _) <;> rfl }
  let b := biproduct.bicone (pairFunction (∐ F) (∐ G))
  have hb : b.toBinaryBicone.IsBilimit :=
    (Bicone.toBinaryBiconeIsBilimit b).symm (biproduct.isBilimit (pairFunction (∐ F) (∐ G)))
  let ebiprod : M ⊞ N ≅ ∐ (pairFunction (∐ F) (∐ G)) :=
    (biprod.mapIso eM eN).trans
      ((biprod.uniqueUpToIso (∐ F) (∐ G) hb).symm.trans
        (biproduct.isoCoproduct (pairFunction (∐ F) (∐ G))))
  let eFamily : (∐ (pairFunction (∐ F) (∐ G))) ≅ ∐ (fun i : WalkingPair => ∐ (T i)) :=
    Sigma.mapIso (fun i => by cases i <;> rfl)
  let esum : (∐ (pairFunction (∐ F) (∐ G))) ≅ ∐ H :=
    (eFamily.trans (sigmaSigmaIso W T)).trans
      (Sigma.whiskerEquiv (f := fun p : Σ i : WalkingPair, W i => T p.1 p.2) (g := H)
        eindex (fun x ↦ by cases x with | mk i j => cases i <;> rfl))
  let eFin := finSumFinEquiv (m := n) (n := m)
  let U' : Fin (n + m) → SmallEtale B X.obj X.property := fun i => (eFin.symm i).elim U V
  let eH : (∐ H) ≅ ∐ (fun i : Fin (n + m) => moduleShriekConstant.{u, r, r} B X Λ (U' i)) :=
    Sigma.whiskerEquiv (f := H)
      (g := fun i : Fin (n + m) => moduleShriekConstant.{u, r, r} B X Λ (U' i))
      eFin (fun i ↦ eqToIso (by cases i <;> simp [U', H, F, G]))
  refine ⟨n + m, U', fun i => ?_, ⟨ebiprod.trans (esum.trans eH)⟩⟩
  cases hi : eFin.symm i with
  | inl j => simpa [U', hi] using hU j
  | inr j => simpa [U', hi] using hV j

end Terms

section Covers

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r} Λ)]

/-- The finite direct sums of affine shriek constants cover epimorphisms onto constructible
sheaves of `Λ`-modules.

This is `AlgebraicGeometry.exists_finite_epi_comp_sigma_moduleShriekConstant_affine`, Stacks
093B (2) followed by Stacks 095P, whose conclusion refines a given epimorphism `p : Z ⟶ H` onto
a constructible sheaf by a finite affine shriek sum mapping to `Z` so that the composite stays
epimorphic. That the refining object is itself constructible, which the covering property also
asks for, is `AlgebraicGeometry.isConstructibleModuleSheaf_sigma_moduleShriekConstant`. -/
public theorem coversEpis_isAffineShriekSum [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] :
    Stacks.Homology.BoundedAboveResolution.CoversEpis
      (isConstructibleModuleSheafProperty.{u, max (u + 1) r, r} B X Λ)
      (IsAffineShriekSum.{u, r} B X Λ) := by
  intro V W f hf hW
  have := hf
  obtain ⟨n, U, hU, g, hg⟩ :=
    exists_finite_epi_comp_sigma_moduleShriekConstant_affine B X Λ f hW
  exact ⟨_, g, ⟨n, U, hU, ⟨Iso.refl _⟩⟩,
    isConstructibleModuleSheaf_sigma_moduleShriekConstant B X Λ U hU, hg⟩

end Covers

section Shriek

open DerivedCategory

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r} Λ)]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)]

/-- **Tag 0960, the implication (1) ⟹ (2).** Let `X` be a quasi-compact and quasi-separated
scheme, let `Λ` be a Noetherian ring and let `K ∈ D^-(X_étale, Λ)` have constructible cohomology
sheaves. Then `K` is represented by a bounded above complex each of whose terms is a finite
direct sum of sheaves `j_{U!} Λ-underline` with `U` an affine object of the small étale site
of `X`.

Boundedness above of `K` is the vanishing `hvan` of `H^i(K)` for `i > b`, which by
`DerivedCategory.isLE_iff` says exactly that `K` lies in `D^-(X_étale, Λ)`; it is the standing
assumption of the source's equivalence.

The proof chooses a cochain complex `A` with `A^i = 0` for `i > b` representing `K`
(`DerivedCategory.exists_iso_Q_obj_of_isLE`) and resolves it by the finite affine shriek sums
using `Stacks.Homology.BoundedAboveResolution.exists_quasiIso_isStrictlyLE_of_coversEpis`. The
three closure properties that engine needs of the class of finite affine shriek sums are
`Stacks.EtaleCohomology.isAffineShriekSum_zero`,
`Stacks.EtaleCohomology.isAffineShriekSum_biprod` and
`Stacks.EtaleCohomology.isAffineShriekSum_of_iso`, and the covering property is
`Stacks.EtaleCohomology.coversEpis_isAffineShriekSum`, which rests on Stacks 093B (2) with
Stacks 095P and on Stacks 03S8 for sheaves of modules. The weak Serre class the engine tests its
kernels against is the constructible sheaves of `Λ`-modules, Stacks 03RZ (3), supplied by
`AlgebraicGeometry.isWeakSerreClass_isConstructibleModuleSheafProperty`. Nothing is carried. -/
@[stacks 0960 "the implication (1) => (2)"]
public theorem isRepresentedByAffineShriekSumComplex_of_isConstructible
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ))) (hK : IsConstructible B X Λ K) (b : ℤ)
    (hvan : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)) i).obj K)) :
    IsRepresentedByAffineShriekSumComplex.{u, r} B X Λ K := by
  have := isWeakSerreClass_isConstructibleModuleSheafProperty B X Λ
  set P := isConstructibleModuleSheafProperty.{u, max (u + 1) r, r} B X Λ with hP
  have hLE : K.IsLE b := by rw [DerivedCategory.isLE_iff]; exact hvan
  obtain ⟨A, hA, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE b
  have hAhom : ∀ i : ℤ, P (A.homology i) := fun i =>
    P.prop_of_iso
      ((((DerivedCategory.homologyFunctorFactors _ i).app A).symm ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso e.symm).symm) (hK i)
  obtain ⟨Y, hY, f, hf, hterms⟩ :=
    Stacks.Homology.BoundedAboveResolution.exists_quasiIso_isStrictlyLE_of_coversEpis
      P (IsAffineShriekSum.{u, r} B X Λ) A
      (coversEpis_isAffineShriekSum B X Λ)
      (isAffineShriekSum_zero B X Λ)
      (fun _ _ => isAffineShriekSum_biprod B X Λ)
      (fun _ _ g hg hM => by
        have := hg
        exact isAffineShriekSum_of_iso B X Λ (asIso g) hM)
      b hAhom
  have := hf
  exact ⟨Y, ⟨b, hY⟩, hterms, ⟨asIso (DerivedCategory.Q.map f) ≪≫ e.symm⟩⟩

/-- **Tag 0960, the implication (1) ⟹ (3).** Let `X` be a quasi-compact and quasi-separated
scheme, let `Λ` be a Noetherian ring and let `K ∈ D^-(X_étale, Λ)` have constructible cohomology
sheaves. Then `K` is represented by a bounded above complex of flat constructible sheaves of
`Λ`-modules.

This is the composite of (1) ⟹ (2),
`Stacks.EtaleCohomology.isRepresentedByAffineShriekSumComplex_of_isConstructible`, with
(2) ⟹ (3),
`Stacks.EtaleCohomology.isRepresentedByBoundedAboveConstructibleFlatComplex_of_shriekSum`. Both
steps are unconditional. -/
@[stacks 0960 "the implication (1) => (3)", sga "4½ Rapport 4.7" "partial"]
public theorem isRepresentedByBoundedAboveConstructibleFlatComplex_of_isConstructible
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ))) (hK : IsConstructible B X Λ K) (b : ℤ)
    (hvan : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)) i).obj K)) :
    IsRepresentedByBoundedAboveConstructibleFlatComplex.{u, max (u + 1) r, r} B X Λ K :=
  isRepresentedByBoundedAboveConstructibleFlatComplex_of_shriekSum B X Λ K
    (isRepresentedByAffineShriekSumComplex_of_isConstructible B X Λ K hK b hvan)

/-- **Tag 0960, the implication (3) ⟹ (2).** An object of `D(X_étale, Λ)` represented by a
bounded above complex of flat constructible sheaves of `Λ`-modules is represented by a bounded
above complex each of whose terms is a finite direct sum of sheaves `j_{U!} Λ-underline` with
`U` an affine object of the small étale site of `X`.

This is the composite of (3) ⟹ (1),
`Stacks.EtaleCohomology.isConstructible_of_isRepresentedByBoundedAboveConstructibleFlatComplex`,
with (1) ⟹ (2),
`Stacks.EtaleCohomology.isRepresentedByAffineShriekSumComplex_of_isConstructible`. No
boundedness hypothesis on `K` is needed here: condition (3) exhibits a complex which vanishes
above some degree `a`, and `DerivedCategory.isLE_Q_obj_iff` transports that bound to `K`. -/
@[stacks 0960 "the implication (3) => (2)"]
public theorem isRepresentedByAffineShriekSumComplex_of_constructibleFlat
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ)))
    (hK : IsRepresentedByBoundedAboveConstructibleFlatComplex.{u, max (u + 1) r, r} B X Λ K) :
    IsRepresentedByAffineShriekSumComplex.{u, r} B X Λ K := by
  obtain ⟨L, ⟨a, hLa⟩, hterm, ⟨e⟩⟩ := hK
  have hLE : K.IsLE a := DerivedCategory.TStructure.t.isLE_of_iso e a
  refine isRepresentedByAffineShriekSumComplex_of_isConstructible B X Λ K
    (isConstructible_of_isRepresentedByBoundedAboveConstructibleFlatComplex B X Λ
      (isWeakSerreClass_isConstructibleModuleSheafProperty B X Λ) K
      ⟨L, ⟨a, hLa⟩, hterm, ⟨e⟩⟩) a (fun i hi => ?_)
  exact DerivedCategory.isZero_of_isLE K a i hi

/-- **Tag 0960.** Let `X` be a quasi-compact and quasi-separated scheme, let `Λ` be a Noetherian
ring and let `K ∈ D^-(X_étale, Λ)`, the bound being the hypothesis `hvan`. Then the following
are equivalent:

1. `K` lies in `D_c(X_étale, Λ)`, i.e. every cohomology sheaf of `K` is constructible;
2. `K` is represented by a bounded above complex whose terms are finite direct sums of sheaves
   `j_{U!} Λ-underline` with `U` an affine object of the small étale site of `X`;
3. `K` is represented by a bounded above complex of flat constructible sheaves of `Λ`-modules.

The equivalence is closed along the cycle (1) ⟹ (2) ⟹ (3) ⟹ (1), by
`Stacks.EtaleCohomology.isRepresentedByAffineShriekSumComplex_of_isConstructible`,
`Stacks.EtaleCohomology.isRepresentedByBoundedAboveConstructibleFlatComplex_of_shriekSum` and
`Stacks.EtaleCohomology.isConstructible_of_isRepresentedByBoundedAboveConstructibleFlatComplex`,
whose weak Serre hypothesis is discharged at this coefficient universe by Stacks 03RZ (3),
`AlgebraicGeometry.isWeakSerreClass_isConstructibleModuleSheafProperty`. The three remaining
implications are also stated separately, as the composites they are; `hvan` is used only in
(1) ⟹ (2), the other two steps producing their own bound. -/
@[stacks 0960, sga "4½ Rapport 4.7" "(1) ⇒ (3)"]
public theorem isConstructible_tfae
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ))) (b : ℤ)
    (hvan : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)) i).obj K)) :
    List.TFAE
      [IsConstructible B X Λ K,
        IsRepresentedByAffineShriekSumComplex.{u, r} B X Λ K,
        IsRepresentedByBoundedAboveConstructibleFlatComplex.{u, max (u + 1) r, r} B X Λ K] := by
  tfae_have 1 → 2 := fun hK =>
    isRepresentedByAffineShriekSumComplex_of_isConstructible B X Λ K hK b hvan
  tfae_have 2 → 3 := fun hK =>
    isRepresentedByBoundedAboveConstructibleFlatComplex_of_shriekSum B X Λ K hK
  tfae_have 3 → 1 := fun hK =>
    isConstructible_of_isRepresentedByBoundedAboveConstructibleFlatComplex B X Λ
      (isWeakSerreClass_isConstructibleModuleSheafProperty B X Λ) K hK
  tfae_finish

end Shriek

end Stacks.EtaleCohomology

end
