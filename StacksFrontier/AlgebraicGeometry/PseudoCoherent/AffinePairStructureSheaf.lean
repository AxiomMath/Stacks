module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairs
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SideCondition
public import StacksFrontier.Homology.PseudoCoherent.Relative.Presentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The per-pair content of Stacks 09VF at the structure sheaf

For `f : X ⟶ S` locally of finite type and a compatible pair of affine opens `U ⊆ f ⁻¹ᵁ V`, the
local condition of Stacks 09UI for `𝒪_X` at that pair asks for a closed immersion
`i : U ⟶ 𝔸ⁿ_V` over `V` through which `f|_U` factors and along whose derived pushforward `𝒪_U`
becomes `m`-pseudo-coherent. This file proves that the condition holds if and only if `Γ(X, U)` is
`m`-pseudo-coherent as a module over itself relative to `Γ(S, V)`, which is
`AlgebraicGeometry.AffinePairStructureSheafComparison` — the hypothesis `(B)` into which
`AlgebraicGeometry.relativeStructureSheafComparison_of_affinePair` splits the hypothesis of
`AlgebraicGeometry.pseudoCoherent_tfae_of_relativeComparison`.

The proof has no mathematical content beyond what is already in the library; it is the dictionary between
the geometric and the algebraic side of one pair. Both sides of the equivalence are read at *one*
closed immersion at a time, and the passage from one immersion to every immersion is Stacks 065H
(`PseudoCoherence.isPseudoCoherentFrom_polynomialPresentation_independent`) rather than
Stacks 09VC: the module-level predicate
`PseudoCoherence.IsModuleRelativelyPseudoCoherentFrom` quantifies over every finite polynomial
presentation, and Stacks 065H says that one presentation suffices.

## Main definitions

* `AlgebraicGeometry.AffineSpace.isoSpecFinOfIso`: affine `n`-space over a scheme `W` presented as
  `Spec R` is `Spec R[x₁, …, x_n]`, with the variables indexed by `Fin n` rather than by
  `ULift (Fin n)`.

## Main results

* `AlgebraicGeometry.exists_ringHom_of_isClosedImmersion_affineSpace_resLE`: a closed immersion
  `U ⟶ 𝔸ⁿ_V` over `V` through which `f|_U` factors is `Spec` of a surjection
  `Γ(S, V)[x₁, …, x_n] ↠ Γ(X, U)` of `Γ(S, V)`-algebras, the algebra structure on `Γ(X, U)` being
  the one given by `f.appLE V U e`.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_restrictUnit_iff`:
  the local condition of Stacks 09UI for `𝒪_X` at such an immersion is `m`-pseudo-coherence of
  `Γ(X, U)` over `Γ(S, V)[x₁, …, x_n]`.
* `AlgebraicGeometry.exists_algHom_isPseudoCoherentFromAfterPushforward_iff`: the two previous
  results combined, with the surjection packaged as a morphism of `Γ(S, V)`-algebras so that
  Stacks 065H applies to it.
* `AlgebraicGeometry.affinePairStructureSheafComparison`:
  **`AlgebraicGeometry.AffinePairStructureSheafComparison` holds, with no hypotheses.**

## Implementation notes

**What this does and does not discharge.** `AffinePairStructureSheafComparison` is the half `(B)`
of the hypothesis of `AlgebraicGeometry.pseudoCoherent_tfae_of_relativeComparison`. The other
half, `(A)`, is `AlgebraicGeometry.AffinePairComparison` at `𝒪_X` — Stacks 09UJ — and it is
proved, as `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_forall_affinePair` in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffinePairLocality.lean`, which is where the tag
sits; `AlgebraicGeometry.relativeStructureSheafComparison_of_affinePair` takes both, so the
three-condition form of Stacks 067Y at the structure sheaf no longer waits on anything. No
declaration here carries a `stacks` attribute: the content proved is the case `E = 𝒪_X` of one
implication pair of Stacks 09VF at one pair of affine opens, which is not the statement of any
tag.

**Every hypothesis here carries the compatibility with the structure morphisms, and must.** The
immersion `i` is always accompanied by `i ≫ 𝔸ⁿ_V ↘ V = f.resLE V U e`. Without it the induced map
of rings is not a map of `Γ(S, V)`-algebras, Stacks 065H does not apply, and the statement is
false: the implementation notes of
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/SideCondition.lean` exhibit a closed immersion of
affine spaces *not* over the base for which the corresponding pseudo-coherence fails. The
compatibility is also what makes the hypothesis dischargeable at all — the immersions produced by
`AlgebraicGeometry.exists_isClosedImmersion_affineSpace_resLE`, which is how the right-to-left
direction below obtains one, come with exactly this equation.

**Why the geometry is read at `Spec Γ(X, U)` and not at `U`.** The module-level side of the
comparison is about `Γ(X, U)` and `Γ(S, V)`, whereas the sheaf-level side is about the open
subschemes `U` and `V`, whose rings of global sections are `Γ(U, ⊤)` and `Γ(V, ⊤)`. These agree
only up to `AlgebraicGeometry.Scheme.Opens.topIso`, so the comparison is made by conjugating the
closed immersion with `AlgebraicGeometry.IsAffineOpen.isoSpec` on the source and with
`AlgebraicGeometry.AffineSpace.isoSpecFinOfIso` on the target, after which it is literally `Spec`
of a ring map and
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_specMap_unit_iff` applies.
No pseudo-coherence statement is transported along a ring isomorphism, and the `ULift (Fin n)`
reindexing of the variables of the affine space is done once, geometrically, inside
`AlgebraicGeometry.AffineSpace.isoSpecFinOfIso`.

`AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE` is the one lemma that relates the two
conjugations: it says that `f.resLE V U e` read through `isoSpec` on both sides is
`Spec (f.appLE V U e)`. It is proved in Mathlib without
`backward.isDefEq.respectTransparency`, unlike `AlgebraicGeometry.Scheme.Hom.resLE_app_top`, which
is why the proof below goes through `toSpecΓ` rather than through global sections of the
restriction.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 36.61.6 (09VF)](https://stacks.math.columbia.edu/tag/09VF)
* [The Stacks Project, Lemma 36.61.5 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.60.1 (067Y)](https://stacks.math.columbia.edu/tag/067Y)
* [The Stacks Project, Lemma 15.82.3 (065H)](https://stacks.math.columbia.edu/tag/065H)
* [The Stacks Project, Definition 15.82.4 (065I)](https://stacks.math.columbia.edu/tag/065I)
* [The Stacks Project, Lemma 36.17.1 (08E7)](https://stacks.math.columbia.edu/tag/08E7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AffineSpace

/-- **Affine `n`-space over a scheme presented as the spectrum of a ring is the spectrum of a
polynomial ring in `Fin n` variables.** Given `w : W ≅ Spec R`, this is the functoriality of
affine space in its base (`AlgebraicGeometry.AffineSpace.map`) followed by
`AlgebraicGeometry.AffineSpace.SpecIso` and the renaming
`AlgebraicGeometry.AffineSpace.mvPolynomialFinUliftIso` of the index type.

The index type of an affine space over a scheme in `Scheme.{u}` must live in `Type u`, so the
`n`-dimensional one is `𝔸(ULift (Fin n); W)`; doing the renaming here, once and geometrically,
is what keeps every pseudo-coherence statement below free of a transport along a ring
isomorphism. -/
@[ega "IV 13.3.1" "special case", ega "IV 2.4.7" "special case"]
public def isoSpecFinOfIso (n : ℕ) {W : Scheme.{u}} {R : CommRingCat.{u}} (w : W ≅ Spec R) :
    AffineSpace (ULift.{u} (Fin n)) W ≅ Spec (CommRingCat.of (MvPolynomial (Fin n) R)) :=
  { hom := map (ULift.{u} (Fin n)) w.hom
    inv := map (ULift.{u} (Fin n)) w.inv
    hom_inv_id := by rw [← map_comp, w.hom_inv_id, map_id]
    inv_hom_id := by rw [← map_comp, w.inv_hom_id, map_id] } ≪≫
  SpecIso (ULift.{u} (Fin n)) R ≪≫
  { hom := Spec.map (mvPolynomialFinUliftIso n R).hom
    inv := Spec.map (mvPolynomialFinUliftIso n R).inv
    hom_inv_id := by rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
    inv_hom_id := by rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id] }

/-- The identification `AlgebraicGeometry.AffineSpace.isoSpecFinOfIso` is compatible with the
structure morphisms: it carries the structure morphism of `𝔸(ULift (Fin n); W)` to the spectrum of
the inclusion of constants, read through `w`. -/
public theorem isoSpecFinOfIso_inv_over (n : ℕ) {W : Scheme.{u}} {R : CommRingCat.{u}}
    (w : W ≅ Spec R) :
    (isoSpecFinOfIso n w).inv ≫ (AffineSpace.over (ULift.{u} (Fin n)) W).hom =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin n) (R := R))) ≫ w.inv := by
  have hC : CommRingCat.ofHom (MvPolynomial.C (σ := ULift.{u} (Fin n)) (R := R)) ≫
      (mvPolynomialFinUliftIso n R).inv =
      CommRingCat.ofHom (MvPolynomial.C (σ := Fin n) (R := R)) := by
    ext r
    simp [mvPolynomialFinUliftIso]
  rw [isoSpecFinOfIso, over_hom_eq]
  simp only [Iso.trans_inv, Category.assoc, map_over, SpecIso_inv_over_assoc,
    ← Spec.map_comp_assoc, hC]

end AffineSpace

/-- **A closed immersion of an affine open into an affine space over an affine open of the base,
over that open, is the spectrum of a surjection of polynomial rings.** Let `f : X ⟶ S`, let
`U ⊆ f ⁻¹ᵁ V` be a compatible pair of affine opens and let
`i : U ⟶ 𝔸(ULift (Fin n); V)` be a closed immersion with
`i ≫ 𝔸ⁿ_V ↘ V = f.resLE V U e`. Then there is a ring map
`α : Γ(S, V)[x₁, …, x_n] ⟶ Γ(X, U)` which is surjective, restricts on constants to
`f.appLE V U e`, and whose spectrum is `i` read through
`AlgebraicGeometry.IsAffineOpen.isoSpec` and
`AlgebraicGeometry.AffineSpace.isoSpecFinOfIso`.

Surjectivity is surjectivity on global sections of a closed immersion of affine schemes
(`AlgebraicGeometry.Scheme.Hom.app_surjective`). That `α` restricts to `f.appLE V U e` on
constants is the hypothesis that `i` lies over `V`, read through
`AlgebraicGeometry.AffineSpace.isoSpecFinOfIso_inv_over`,
`AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE` and the faithfulness of `Spec`; it is what
makes `α` a morphism of `Γ(S, V)`-algebras in
`AlgebraicGeometry.exists_algHom_isPseudoCoherentFromAfterPushforward_iff`. -/
public theorem exists_ringHom_of_isClosedImmersion_affineSpace_resLE {X S : Scheme.{u}} (f : X ⟶ S)
    {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)
    {n : ℕ} (i : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.toScheme) [IsClosedImmersion i]
    (hi : i ≫ (AffineSpace.over (ULift.{u} (Fin n)) V.toScheme).hom = f.resLE V U e) :
    ∃ α : CommRingCat.of (MvPolynomial (Fin n) Γ(S, V)) ⟶ Γ(X, U),
      Function.Surjective (CommRingCat.Hom.hom α) ∧
        CommRingCat.ofHom (MvPolynomial.C (σ := Fin n) (R := Γ(S, V))) ≫ α = f.appLE V U e ∧
        Spec.map α = hU.isoSpec.inv ≫ i ≫ (AffineSpace.isoSpecFinOfIso n hV.isoSpec).hom := by
  set g := hU.isoSpec.inv ≫ i ≫ (AffineSpace.isoSpecFinOfIso n hV.isoSpec).hom with hg
  have hmap := Spec.map_preimage g
  have hkey : g ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin n) (R := Γ(S, V)))) =
      Spec.map (f.appLE V U e) := by
    rw [hg, ← cancel_mono hV.isoSpec.inv, Category.assoc,
      ← AffineSpace.isoSpecFinOfIso_inv_over n hV.isoSpec, Category.assoc, Category.assoc,
      Iso.hom_inv_id_assoc, hi]
    have hnat : hU.isoSpec.hom ≫ Spec.map (f.appLE V U e) =
        f.resLE V U e ≫ hV.isoSpec.hom := by
      rw [hU.isoSpec_hom, hV.isoSpec_hom]
      exact Scheme.Opens.toSpecΓ_SpecMap_appLE f V U e
    rw [Iso.inv_comp_eq, ← Category.assoc, hnat, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hsurj : Function.Surjective (CommRingCat.Hom.hom (Spec.preimage g)) := by
    have hnat := Scheme.ΓSpecIso_naturality (Spec.preimage g)
    rw [hmap] at hnat
    have hq : Function.Surjective (CommRingCat.Hom.hom g.appTop) :=
      Scheme.Hom.app_surjective _ ⊤ (isAffineOpen_top _)
    have heq := congrArg (fun g => (CommRingCat.Hom.hom g : _ → _)) hnat
    simp only [CommRingCat.hom_comp, RingHom.coe_comp] at heq
    have hcomp : Function.Surjective
        ((CommRingCat.Hom.hom (Spec.preimage g)) ∘
          (CommRingCat.Hom.hom
            ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Γ(S, V)))).hom))) :=
      heq ▸ ((ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso Γ(X, U)).hom)).2.comp hq)
    exact hcomp.of_comp
  refine ⟨Spec.preimage g, hsurj, ?_, hmap⟩
  exact Spec.map_injective (by rwa [Spec.map_comp, hmap])

namespace Scheme.Modules

/-- **The local condition of Stacks 09UI for `𝒪_X` at one pair of affine opens is module-level
pseudo-coherence over a polynomial ring.** Let `U` be an affine open of `X`, let `V` be an affine
open of `S`, let `i : U ⟶ 𝔸(ULift (Fin n); V)` be a closed immersion, and let `α` be a ring map
whose spectrum is `i` read through `AlgebraicGeometry.IsAffineOpen.isoSpec` and
`AlgebraicGeometry.AffineSpace.isoSpecFinOfIso`. Then the restriction of `𝒪_X` to `U` is
`m`-pseudo-coherent after derived pushforward along `i` if and only if `Γ(X, U)` is an
`m`-pseudo-coherent `Γ(S, V)[x₁, …, x_n]`-module through `α`.

The proof identifies the restriction of `𝒪_X` to `U` with `𝒪_U`
(`AlgebraicGeometry.Scheme.Modules.restrictUnitIso`), conjugates `i` into `Spec α`
(`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_conj_unit_iff`, whose own
proof is where the pushforwards along the two isomorphisms are absorbed), and applies the
crossing
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_specMap_unit_iff`, which is
Stacks 08E7 at the structure sheaf. The last step commutes restriction of scalars past the
degree-zero placement with `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`.

Note that the hypothesis is only that `α` *presents* `i`; the compatibility of `i` with the
structure morphisms is not needed here, and enters in
`AlgebraicGeometry.exists_algHom_isPseudoCoherentFromAfterPushforward_iff`, where it is what makes
`α` a morphism of `Γ(S, V)`-algebras. -/
public theorem isPseudoCoherentFromAfterPushforward_restrictUnit_iff
    {X S : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V)
    {n : ℕ} (i : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.toScheme) [IsClosedImmersion i]
    (α : CommRingCat.of (MvPolynomial (Fin n) Γ(S, V)) ⟶ Γ(X, U))
    (hα : Spec.map α = hU.isoSpec.inv ≫ i ≫ (AffineSpace.isoSpecFinOfIso n hV.isoSpec).hom)
    (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward i
        ((restrictFunctor U.ι).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj
            (SheafOfModules.unit X.ringCatSheaf))) m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        ((ModuleCat.restrictScalars (CommRingCat.Hom.hom α)).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
            (ModuleCat.of Γ(X, U) Γ(X, U)))) m := by
  have : IsClosedImmersion (Spec.map α) := by rw [hα]; infer_instance
  have eU := (Functor.mapDerivedCategorySingleFunctor (restrictFunctor U.ι) 0).app
      (SheafOfModules.unit X.ringCatSheaf) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (restrictUnitIso U.ι)
  refine (isPseudoCoherentFromAfterPushforward_iff_of_iso i eU m).trans ?_
  refine (isPseudoCoherentFromAfterPushforward_conj_unit_iff hU.isoSpec.inv i
    (AffineSpace.isoSpecFinOfIso n hV.isoSpec).hom m).symm.trans ?_
  refine (isPseudoCoherentFromAfterPushforward_congr hα.symm _ m).trans ?_
  refine (isPseudoCoherentFromAfterPushforward_specMap_unit_iff α m).trans ?_
  have esc := (Functor.mapDerivedCategorySingleFunctor
    (ModuleCat.restrictScalars (CommRingCat.Hom.hom α)) 0).app (ModuleCat.of Γ(X, U) Γ(X, U))
  exact ⟨fun h => h.ofIso esc.symm, fun h => h.ofIso esc⟩

end Scheme.Modules

/-- **One closed immersion over `V` presents `Γ(X, U)` as a quotient of a polynomial ring over
`Γ(S, V)`, and the local condition of Stacks 09UI at it is `m`-pseudo-coherence for that
presentation.** This is
`AlgebraicGeometry.exists_ringHom_of_isClosedImmersion_affineSpace_resLE` and
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_restrictUnit_iff`
combined, with the ring map packaged as a morphism of `Γ(S, V)`-algebras — which is the shape
Stacks 065H consumes, and which the compatibility of `i` with the structure morphisms is exactly
what supplies.

The algebra structure on `Γ(X, U)` is given abstractly by an instance together with the
identification `halg` of its structure map with `f.appLE V U e`, so that a caller which has
already installed `(f.appLE V U e).hom.toAlgebra` can pass `rfl`. -/
public theorem exists_algHom_isPseudoCoherentFromAfterPushforward_iff {X S : Scheme.{u}}
    (f : X ⟶ S) {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) [Algebra Γ(S, V) Γ(X, U)]
    (halg : algebraMap Γ(S, V) Γ(X, U) = (f.appLE V U e).hom)
    {n : ℕ} (i : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.toScheme) [IsClosedImmersion i]
    (hi : i ≫ (AffineSpace.over (ULift.{u} (Fin n)) V.toScheme).hom = f.resLE V U e) (m : ℤ) :
    ∃ α : MvPolynomial (Fin n) Γ(S, V) →ₐ[Γ(S, V)] Γ(X, U), Function.Surjective α ∧
      (Scheme.Modules.IsPseudoCoherentFromAfterPushforward i
          ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj
              (SheafOfModules.unit X.ringCatSheaf))) m ↔
        StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
          ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
              (ModuleCat.of Γ(X, U) Γ(X, U)))) m) := by
  obtain ⟨α, hsurj, hC, hspec⟩ :=
    exists_ringHom_of_isClosedImmersion_affineSpace_resLE f hU hV e i hi
  refine ⟨{ CommRingCat.Hom.hom α with commutes' := fun r => ?_ }, hsurj,
    Scheme.Modules.isPseudoCoherentFromAfterPushforward_restrictUnit_iff
      hU hV i α hspec m⟩
  rw [MvPolynomial.algebraMap_eq, halg]
  exact congrArg (fun g => (CommRingCat.Hom.hom g) r) hC

/-- **The per-pair content of Stacks 09VF at the structure sheaf, with no hypotheses.** For
`f : X ⟶ S` locally of finite type, an integer `m` and a compatible pair of affine opens
`U ⊆ f ⁻¹ᵁ V`, the local condition of Stacks 09UI for `𝒪_X` at that pair holds if and only if
`Γ(X, U)` is `m`-pseudo-coherent as a module over itself relative to `Γ(S, V)`.

This is `AlgebraicGeometry.AffinePairStructureSheafComparison`, the half `(B)` of the hypothesis
of `AlgebraicGeometry.pseudoCoherent_tfae_of_relativeComparison`; the other half, Stacks 09UJ at
the structure sheaf, is still owed.

Each direction instantiates
`AlgebraicGeometry.exists_algHom_isPseudoCoherentFromAfterPushforward_iff` at a single closed
immersion and crosses the gap between "some immersion" and "every presentation" with Stacks 065H
(`PseudoCoherence.isPseudoCoherentFrom_polynomialPresentation_independent`). Left to right, the
immersion is the one the local condition provides; right to left it is the one produced by
`AlgebraicGeometry.exists_isClosedImmersion_affineSpace_resLE`, which exists because `f` is
locally of finite type and which comes with the required compatibility with the structure
morphisms. The finite-typeness of `Γ(X, U)` over `Γ(S, V)` that Stacks 065H needs is
`AlgebraicGeometry.algebraFiniteType_appLE`. -/
public theorem affinePairStructureSheafComparison {X S : Scheme.{u}} (f : X ⟶ S) :
    AffinePairStructureSheafComparison f := by
  intro hft m U hU V hV e
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  have _ : Algebra.FiniteType Γ(S, V) Γ(X, U) := algebraFiniteType_appLE f U hU V hV e
  have hpres := (PseudoCoherence.isPseudoCoherentFrom_polynomialPresentation_independent.{u, u, u}
    (R := Γ(S, V)) (A := Γ(X, U))
    ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
      (ModuleCat.of Γ(X, U) Γ(X, U))) m).1
  refine ⟨fun hL => ?_, fun hR => ?_⟩
  · obtain ⟨N, j, hcj, hoverj, hpc⟩ := hL
    obtain ⟨α, hα, hiff⟩ := exists_algHom_isPseudoCoherentFromAfterPushforward_iff f hU hV e rfl
      j hoverj m
    exact hpres.mp ⟨N, α, hα, hiff.mp hpc⟩
  · obtain ⟨N, j, hcj, hoverj⟩ := exists_isClosedImmersion_affineSpace_resLE f ⟨V, hV⟩ ⟨U, hU⟩ e
    obtain ⟨α, hα, hiff⟩ := exists_algHom_isPseudoCoherentFromAfterPushforward_iff f hU hV e rfl
      j hoverj m
    exact ⟨N, j, hcj, hoverj, hiff.mpr (hR N α hα)⟩

end AlgebraicGeometry

end
