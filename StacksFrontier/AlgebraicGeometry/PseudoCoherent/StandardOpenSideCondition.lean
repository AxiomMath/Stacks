module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StandardCoverSideCondition
public import StacksFrontier.Homology.PseudoCoherent.Relative.Localization

/-!
# The side condition of Stacks 09VA at the standard opens of an affine space

Stacks 09VE and Stacks 09VD are proved in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/StandardCoverSideCondition.lean` granted three
residual hypotheses `hOb`, `hOV` and `hOS`, each a form of the side condition of Stacks 09VA at
an intermediate scheme. This file discharges them and places the two tags.

## Main results

* `AlgebraicGeometry.AffineSpace.algEquivMvPolynomial`: the ring of global sections of
  `𝔸(n; S)` over an affine base is the polynomial ring `Γ(S, ⊤)[xᵢ]`, as a `Γ(S, ⊤)`-algebra.
* `AlgebraicGeometry.exists_algHom_specMap_of_isAffine`: a closed immersion of an affine scheme
  into a finite-dimensional affine space over an affine base, *over that base*, is the spectrum
  of a surjection of `Γ(S, ⊤)`-algebras out of a polynomial ring.
* `AlgebraicGeometry.Scheme.Modules.pushforwardStructureSheafPseudoCoherentOver_of_relative`:
  **the side condition of Stacks 09VA at every closed immersion of `Y` into an affine space over
  `S` lying over `S`**, granted that `Γ(Y, ⊤)` is pseudo-coherent relative to `Γ(S, ⊤)` as a
  module over itself.
* `AlgebraicGeometry.Scheme.Modules.pushforwardStructureSheafPseudoCoherentOver_basicOpen`:
  that side condition at a standard open of an affine space over `S`.
* `AlgebraicGeometry.Scheme.Modules.pushforwardStructureSheafPseudoCoherentOver_affineSpace`:
  that side condition at an affine space over a standard open of `S`.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_basicOpen`:
  **Stacks 09VE**, with nothing assumed.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_restrict`:
  **Stacks 09VD**, with nothing assumed.

## Implementation notes

**Why the residual hypotheses are replaced rather than supplied.** The three hypotheses `hOb`, `hOV`
and `hOS` of
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_basicOpen'` and
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_affineOpen'` ask for
the side condition at *every* closed immersion `p : Y ⟶ 𝔸ᴺ_S`, with no compatibility with the
structure morphisms, and in that shape they are **false**: the counterexample recorded in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/SideCondition.lean` applies verbatim at `N = 1` and
`Y = D(1) ⊆ 𝔸⁰_S`. So nothing can be obtained from those results by instantiation, and the proofs
are replayed here against the predicate
`AlgebraicGeometry.Scheme.Modules.PushforwardStructureSheafPseudoCoherentOver`, which carries the
compatibility `p ≫ 𝔸ᴺ_S ↘ S = g`. Every call site has that equation: it is the `hqo` produced by
`AlgebraicGeometry.exists_isClosedImmersion_affineSpace`.

**Where the mathematics is.** The one algebraic input is
`PseudoCoherence.isModuleRelativelyPseudoCoherent_localizationAway`: a localization away from one
element of a relatively pseudo-coherent algebra is relatively pseudo-coherent. Applied to a
polynomial algebra — which is relatively pseudo-coherent over its base by
`PseudoCoherence.isModuleRelativelyPseudoCoherent_mvPolynomial_self` — it says that
`Γ(S, ⊤)[x₁, …, x_M]_a` is pseudo-coherent relative to `Γ(S, ⊤)`. That single statement covers all
three residues: `Γ(D(a) ⊆ 𝔸ᴹ_S, ⊤)` is such a localization for `hOb` and, with `Γ(S, ⊤)` replaced
by `Γ(V, ⊤)`, for `hOV`; and for `hOS`, with `V = S_b` a standard open,
`Γ(𝔸ⁿ_V, ⊤) = Γ(V, ⊤)[y₁, …, yₙ] = (Γ(S, ⊤)[y₁, …, yₙ])_b` is again one.

**Why `hV` is restored in Stacks 09VD.** The library's arbitrary-affine-open form drops the
hypothesis that `V` is a *standard* open of `S` as a free strengthening. It is not free: `hOS` is
dischargeable only because for `V = S_b` the sections `Γ(𝔸ⁿ_V, ⊤)` are a localization away of a
polynomial ring over `Γ(S, ⊤)`, which for an arbitrary affine open `V` they are not. Stacks 09VD
makes that hypothesis, and the statement tagged below is the one Stacks 09VD states.

**No `isoSpecFin` transport of pseudo-coherence.** The passage from the module-level statement to
the sheaf-level one is
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_singleFunctor_pushforward_unit_specMap`
followed by `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_pushforward_isIso_iff`, exactly as
in `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_singleFunctor_pushforward_unit_affineSpace`;
the renaming of the index type is done once and geometrically, inside
`AlgebraicGeometry.AffineSpace.isoSpecFin`.

**An expected linter finding.** The two tagged statements carry the instance `[QuasiCompact f]`
that Stacks 09VE and Stacks 09VD include and that their proofs do not use — it is automatic for a
morphism of affine schemes. It is kept because the statement follows the source, so `lake lint`
reports one `unusedArguments` finding on this file, on
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_standardCover`; the same
pattern is already present in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/StandardCoverGluing.lean`,
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffineOpenLocalization.lean` and
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/StandardCoverSideCondition.lean`.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 36.61.5 (09VE)](https://stacks.math.columbia.edu/tag/09VE)
* [The Stacks Project, Lemma 36.61.4 (09VD)](https://stacks.math.columbia.edu/tag/09VD)
* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
* [The Stacks Project, Lemma 36.60.9 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [The Stacks Project, Lemma 15.82.11 (0679)](https://stacks.math.columbia.edu/tag/0679)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect MvPolynomial
open scoped AlgebraicGeometry

universe u

namespace PseudoCoherence

attribute [local instance] HasDerivedCategory.standard

/-- **A localization of a polynomial algebra away from one element is pseudo-coherent relative to
the coefficient ring as a module over itself.** For `R` commutative, `a` a polynomial in finitely
many variables over `R`, and `Aₐ` a localization of `R[x₁, …, x_n]` away from `a`, the ring `Aₐ` is
pseudo-coherent relative to `R`.

This is the algebraic content of the side condition of Stacks 09VA at the standard opens of the
affine spaces over an affine base: it is
`PseudoCoherence.isModuleRelativelyPseudoCoherent_localizationAway` applied to
`PseudoCoherence.isModuleRelativelyPseudoCoherent_mvPolynomial_self`. -/
public theorem isModuleRelativelyPseudoCoherent_localizationAway_mvPolynomial
    {R : Type u} [CommRing R] (n : ℕ) (a : MvPolynomial (Fin n) R)
    (Aa : Type u) [CommRing Aa] [Algebra (MvPolynomial (Fin n) R) Aa]
    [IsLocalization.Away a Aa] [Algebra R Aa]
    [IsScalarTower R (MvPolynomial (Fin n) R) Aa] :
    letI : Algebra.FiniteType (MvPolynomial (Fin n) R) Aa :=
      IsLocalization.finiteType_of_monoid_fg (Submonoid.powers a) Aa
    letI : Algebra.FiniteType R Aa := Algebra.FiniteType.trans
      (inferInstance : Algebra.FiniteType R (MvPolynomial (Fin n) R))
      (inferInstance : Algebra.FiniteType (MvPolynomial (Fin n) R) Aa)
    IsModuleRelativelyPseudoCoherent (R := R) (A := Aa) Aa :=
  isModuleRelativelyPseudoCoherent_localizationAway a
    (isModuleRelativelyPseudoCoherent_mvPolynomial_self R n)

end PseudoCoherence

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

namespace AffineSpace

/-- **The global sections of affine `n`-space over an affine base form the polynomial ring in `n`
variables**, as an algebra over the global sections of the base.

The underlying ring map is the one Mathlib's `AlgebraicGeometry.AffineSpace.isoOfIsAffine`
produces, namely evaluation of a polynomial at the coordinates of the affine space; it is an
isomorphism because `AlgebraicGeometry.AffineSpace.isoOfIsAffine_hom_appTop` factors the global
sections of that isomorphism of schemes through it, and it is a morphism of `Γ(S, ⊤)`-algebras
because evaluation restricts on constants to the structure map. -/
public def algEquivMvPolynomial (n : Type u) (S : Scheme.{u}) [IsAffine S]
    [Algebra Γ(S, ⊤) Γ(AffineSpace n S, ⊤)]
    (halg : algebraMap Γ(S, ⊤) Γ(AffineSpace n S, ⊤) =
      ((AffineSpace.over n S).hom.appTop).hom) :
    MvPolynomial n Γ(S, ⊤) ≃ₐ[Γ(S, ⊤)] Γ(AffineSpace n S, ⊤) :=
  have h2 : IsIso ((AffineSpace.isoOfIsAffine n S).hom.appTop) := by
    rw [← Scheme.Γ_map_op]
    exact Functor.map_isIso Scheme.Γ _
  have hiso : IsIso (CommRingCat.ofHom
      (eval₂Hom ((AffineSpace.over n S).hom.appTop).hom (AffineSpace.coord S))) := by
    rw [AffineSpace.isoOfIsAffine_hom_appTop (n := n) (S := S)] at h2
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ _ h2
  { (asIso (CommRingCat.ofHom
      (eval₂Hom ((AffineSpace.over n S).hom.appTop).hom
        (AffineSpace.coord S)))).commRingCatIsoToRingEquiv with
    commutes' := fun r => by
      change eval₂Hom ((AffineSpace.over n S).hom.appTop).hom (AffineSpace.coord S)
        (algebraMap Γ(S, ⊤) (MvPolynomial n Γ(S, ⊤)) r) = _
      rw [MvPolynomial.algebraMap_eq, eval₂Hom_C, halg] }

/-- The polynomial presentation of the global sections of a finite-dimensional affine space over
an affine base, with the variables indexed by `Fin M`. -/
public def algEquivMvPolynomialFin (M : ℕ) (S : Scheme.{u}) [IsAffine S]
    [Algebra Γ(S, ⊤) Γ(AffineSpace (ULift.{u} (Fin M)) S, ⊤)]
    (halg : algebraMap Γ(S, ⊤) Γ(AffineSpace (ULift.{u} (Fin M)) S, ⊤) =
      ((AffineSpace.over (ULift.{u} (Fin M)) S).hom.appTop).hom) :
    MvPolynomial (Fin M) Γ(S, ⊤) ≃ₐ[Γ(S, ⊤)] Γ(AffineSpace (ULift.{u} (Fin M)) S, ⊤) :=
  (MvPolynomial.renameEquiv (σ := Fin M) (τ := ULift.{u} (Fin M)) Γ(S, ⊤)
    Equiv.ulift.symm).trans (algEquivMvPolynomial _ S halg)

/-- The global sections of a finite-dimensional affine space over an affine base are a finite-type
algebra over the global sections of the base. -/
public theorem algebraFiniteType_appTop (M : ℕ) (S : Scheme.{u}) [IsAffine S]
    [Algebra Γ(S, ⊤) Γ(AffineSpace (ULift.{u} (Fin M)) S, ⊤)]
    (halg : algebraMap Γ(S, ⊤) Γ(AffineSpace (ULift.{u} (Fin M)) S, ⊤) =
      ((AffineSpace.over (ULift.{u} (Fin M)) S).hom.appTop).hom) :
    Algebra.FiniteType Γ(S, ⊤) Γ(AffineSpace (ULift.{u} (Fin M)) S, ⊤) :=
  Algebra.FiniteType.of_surjective (algEquivMvPolynomialFin M S halg).toAlgHom
    (algEquivMvPolynomialFin M S halg).surjective

/-- **The global sections of a finite-dimensional affine space over an affine base are
pseudo-coherent relative to the base as a module over themselves.** This is
`PseudoCoherence.isModuleRelativelyPseudoCoherent_mvPolynomial_self` carried along
`AlgebraicGeometry.AffineSpace.algEquivMvPolynomialFin`. -/
public theorem isModuleRelativelyPseudoCoherent_appTop (M : ℕ) (S : Scheme.{u}) [IsAffine S]
    [Algebra Γ(S, ⊤) Γ(AffineSpace (ULift.{u} (Fin M)) S, ⊤)]
    [Algebra.FiniteType Γ(S, ⊤) Γ(AffineSpace (ULift.{u} (Fin M)) S, ⊤)]
    (halg : algebraMap Γ(S, ⊤) Γ(AffineSpace (ULift.{u} (Fin M)) S, ⊤) =
      ((AffineSpace.over (ULift.{u} (Fin M)) S).hom.appTop).hom) :
    PseudoCoherence.IsModuleRelativelyPseudoCoherent (R := Γ(S, ⊤))
      (A := Γ(AffineSpace (ULift.{u} (Fin M)) S, ⊤)) Γ(AffineSpace (ULift.{u} (Fin M)) S, ⊤) :=
  PseudoCoherence.isModuleRelativelyPseudoCoherent_of_algEquiv
    (algEquivMvPolynomialFin M S halg)
    (PseudoCoherence.isModuleRelativelyPseudoCoherent_mvPolynomial_self Γ(S, ⊤) M)

end AffineSpace

/-- **A closed immersion of an affine scheme into a finite-dimensional affine space over an affine
base, over that base, is the spectrum of a surjection of polynomial algebras.** Let `S` be affine,
`Y` affine, and `p : Y ⟶ 𝔸ᴺ_S` a closed immersion with `p ≫ 𝔸ᴺ_S ↘ S = g`. Read through
`AlgebraicGeometry.Scheme.isoSpec` on the source and
`AlgebraicGeometry.AffineSpace.isoSpecFin` on the target, `p` is `Spec α` for a surjection of
`Γ(S, ⊤)`-algebras `α : Γ(S, ⊤)[x₁, …, x_N] ↠ Γ(Y, ⊤)`.

This is `AlgebraicGeometry.AffineSpace.exists_algHom_specMap` with the source allowed to be an
arbitrary affine scheme rather than an affine space, and with the algebra structure on `Γ(Y, ⊤)`
supplied by `g`. Surjectivity of `α` is surjectivity on global sections of a closed immersion of
affine schemes, and that `α` is a morphism of `Γ(S, ⊤)`-algebras is the hypothesis `hp`. -/
public theorem exists_algHom_specMap_of_isAffine {S Y : Scheme.{u}} [IsAffine S] [IsAffine Y]
    {N : ℕ} (p : Y ⟶ AffineSpace (ULift.{u} (Fin N)) S) [IsClosedImmersion p] (g : Y ⟶ S)
    (hp : p ≫ (AffineSpace.over (ULift.{u} (Fin N)) S).hom = g)
    [Algebra Γ(S, ⊤) Γ(Y, ⊤)] (halg : algebraMap Γ(S, ⊤) Γ(Y, ⊤) = g.appTop.hom) :
    ∃ α : MvPolynomial (Fin N) Γ(S, ⊤) →ₐ[Γ(S, ⊤)] Γ(Y, ⊤),
      Function.Surjective α ∧
        Spec.map (CommRingCat.ofHom α.toRingHom) =
          Y.isoSpec.inv ≫ p ≫ (AffineSpace.isoSpecFin N S).hom := by
  have hfac : Y.isoSpec.inv ≫ g ≫ S.isoSpec.hom = Spec.map g.appTop := by
    rw [← Scheme.isoSpec_hom_naturality g, Iso.inv_hom_id_assoc]
  have hmap := Spec.map_preimage (Y.isoSpec.inv ≫ p ≫ (AffineSpace.isoSpecFin N S).hom)
  have key : (Y.isoSpec.inv ≫ p ≫ (AffineSpace.isoSpecFin N S).hom) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin N) (R := Γ(S, ⊤)))) =
      Spec.map g.appTop := by
    rw [← cancel_mono S.isoSpec.inv, ← hfac]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [← AffineSpace.isoSpecFin_inv_over N S, Iso.hom_inv_id_assoc, hp]
  have hcomm : CommRingCat.ofHom (MvPolynomial.C (σ := Fin N) (R := Γ(S, ⊤))) ≫
      Spec.preimage (Y.isoSpec.inv ≫ p ≫ (AffineSpace.isoSpecFin N S).hom) = g.appTop :=
    Spec.map_injective (by rwa [Spec.map_comp, hmap])
  have hsurj : Function.Surjective
      (CommRingCat.Hom.hom
        (Spec.preimage (Y.isoSpec.inv ≫ p ≫ (AffineSpace.isoSpecFin N S).hom))) := by
    have hnat := Scheme.ΓSpecIso_naturality
      (Spec.preimage (Y.isoSpec.inv ≫ p ≫ (AffineSpace.isoSpecFin N S).hom))
    rw [hmap] at hnat
    have hq : Function.Surjective
        (CommRingCat.Hom.hom
          ((Y.isoSpec.inv ≫ p ≫ (AffineSpace.isoSpecFin N S).hom).appTop)) :=
      Scheme.Hom.app_surjective _ ⊤ (isAffineOpen_top _)
    have heq := congrArg (fun f => (CommRingCat.Hom.hom f : _ → _)) hnat
    simp only [CommRingCat.hom_comp, RingHom.coe_comp] at heq
    have hcomp : Function.Surjective
        ((CommRingCat.Hom.hom
            (Spec.preimage (Y.isoSpec.inv ≫ p ≫ (AffineSpace.isoSpecFin N S).hom))) ∘
          (CommRingCat.Hom.hom
            ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Γ(S, ⊤)))).hom))) :=
      heq ▸ ((ConcreteCategory.bijective_of_isIso
        ((Scheme.ΓSpecIso Γ(Y, ⊤)).hom)).2.comp hq)
    exact hcomp.of_comp
  refine ⟨{ CommRingCat.Hom.hom
      (Spec.preimage (Y.isoSpec.inv ≫ p ≫ (AffineSpace.isoSpecFin N S).hom)) with
      commutes' := fun r => ?_ }, hsurj, by rwa [CommRingCat.ofHom_hom]⟩
  rw [MvPolynomial.algebraMap_eq, halg]
  exact congrArg (fun f => (CommRingCat.Hom.hom f) r) hcomm

namespace Scheme.Modules

/-- **The side condition of Stacks 09VA at the closed immersions of `Y` into the
finite-dimensional affine spaces over `S` that lie over `S`**: for every closed immersion
`p : Y ⟶ 𝔸ᴺ_S` with `N` finite and `p ≫ 𝔸ᴺ_S ↘ S = g`, the pushforward `p_*𝒪_Y` is a
pseudo-coherent sheaf of `𝒪_{𝔸ᴺ_S}`-modules.

This is `AlgebraicGeometry.Scheme.Modules.PushforwardStructureSheafPseudoCoherent` with the
compatibility with the structure morphisms added. That compatibility is not optional: without it
the predicate is false even at `Y = D(1) ⊆ 𝔸⁰_S`, by the counterexample in the implementation
notes of `StacksFrontier/AlgebraicGeometry/PseudoCoherent/SideCondition.lean`. -/
public abbrev PushforwardStructureSheafPseudoCoherentOver (S Y : Scheme.{u}) (g : Y ⟶ S) : Prop :=
  ∀ (N : ℕ) (p : Y ⟶ AffineSpace (ULift.{u} (Fin N)) S), IsClosedImmersion p →
    p ≫ (AffineSpace.over (ULift.{u} (Fin N)) S).hom = g →
      RingedSpace.IsPseudoCoherent (X := (AffineSpace (ULift.{u} (Fin N)) S).toRingedSpace)
        ((DerivedCategory.singleFunctor (AffineSpace (ULift.{u} (Fin N)) S).Modules 0).obj
          ((pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf)))

/-- **The side condition of Stacks 09VA over `S`, reduced to relative pseudo-coherence of the
global sections.** If `Γ(Y, ⊤)` is pseudo-coherent relative to `Γ(S, ⊤)` as a module over itself,
then for every closed immersion `p : Y ⟶ 𝔸ᴺ_S` over `S` the sheaf `p_*𝒪_Y` is pseudo-coherent.

`AlgebraicGeometry.exists_algHom_specMap_of_isAffine` writes `p` as the spectrum of a surjection
`α` of `Γ(S, ⊤)`-algebras out of a polynomial ring; relative pseudo-coherence applied to that one
presentation is the side condition on `Spec α` by
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_singleFunctor_pushforward_unit_specMap`; and
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_pushforward_isIso_iff` carries it back to
`𝔸ᴺ_S`. -/
public theorem pushforwardStructureSheafPseudoCoherentOver_of_relative {S Y : Scheme.{u}}
    [IsAffine S] [IsAffine Y] (g : Y ⟶ S)
    [Algebra Γ(S, ⊤) Γ(Y, ⊤)] (halg : algebraMap Γ(S, ⊤) Γ(Y, ⊤) = g.appTop.hom)
    [Algebra.FiniteType Γ(S, ⊤) Γ(Y, ⊤)]
    (h : PseudoCoherence.IsModuleRelativelyPseudoCoherent (R := Γ(S, ⊤)) (A := Γ(Y, ⊤))
      Γ(Y, ⊤)) :
    PushforwardStructureSheafPseudoCoherentOver S Y g := by
  intro N p hp hover
  have := hp
  obtain ⟨α, hα, hspec⟩ := exists_algHom_specMap_of_isAffine p g hover halg
  have hmod := fun m : ℤ => StacksDraft.PseudoCoherence.IsPseudoCoherentFrom.ofIso (h m N α hα)
    (((ModuleCat.restrictScalars.{u} α.toRingHom).mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of Γ(Y, ⊤) Γ(Y, ⊤)))
  have hside := isPseudoCoherent_singleFunctor_pushforward_unit_specMap
    (CommRingCat.ofHom α.toRingHom) hmod
  have e := (Functor.mapDerivedCategorySingleFunctor
        (pushforward (AffineSpace.isoSpecFin N S).inv) 0).app
      ((pushforward (Spec.map (CommRingCat.ofHom α.toRingHom))).obj
        (SheafOfModules.unit (Spec Γ(Y, ⊤)).ringCatSheaf))
      ≪≫ (DerivedCategory.singleFunctor
        (AffineSpace (ULift.{u} (Fin N)) S).Modules 0).mapIso
      (pushforwardUnitCongrIso p (Spec.map (CommRingCat.ofHom α.toRingHom))
        Y.isoSpec (AffineSpace.isoSpecFin N S) hspec.symm)
  exact ((isPseudoCoherent_pushforward_isIso_iff (AffineSpace.isoSpecFin N S).inv _).mpr
    hside).of_iso e

/-- **The side condition of Stacks 09VA at a standard open of a finite-dimensional affine space
over an affine base.** This is the hypothesis `hOb` of
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_basicOpen'`, repaired by
the compatibility with the structure morphisms and discharged.

`Γ(D(a) ⊆ 𝔸ᴹ_S, ⊤)` is the localization of `Γ(𝔸ᴹ_S, ⊤)` away from `a`
(`AlgebraicGeometry.Γ_restrict_isLocalization`), and `Γ(𝔸ᴹ_S, ⊤)` is pseudo-coherent relative to
`Γ(S, ⊤)` as a module over itself
(`AlgebraicGeometry.AffineSpace.isModuleRelativelyPseudoCoherent_appTop`), so
`PseudoCoherence.isModuleRelativelyPseudoCoherent_localizationAway` applies. -/
public theorem pushforwardStructureSheafPseudoCoherentOver_basicOpen (M : ℕ) (S : Scheme.{u})
    [IsAffine S] (a : Γ(AffineSpace (ULift.{u} (Fin M)) S, ⊤)) :
    PushforwardStructureSheafPseudoCoherentOver S
      ((AffineSpace (ULift.{u} (Fin M)) S).basicOpen a).toScheme
      (((AffineSpace (ULift.{u} (Fin M)) S).basicOpen a).ι ≫
        (AffineSpace.over (ULift.{u} (Fin M)) S).hom) := by
  have hUaff : IsAffine ((AffineSpace (ULift.{u} (Fin M)) S).basicOpen a).toScheme :=
    (isAffineOpen_top _).basicOpen a
  let algX : Algebra Γ(S, ⊤) Γ(AffineSpace (ULift.{u} (Fin M)) S, ⊤) :=
    ((AffineSpace.over (ULift.{u} (Fin M)) S).hom.appTop).hom.toAlgebra
  have halgX : algebraMap Γ(S, ⊤) Γ(AffineSpace (ULift.{u} (Fin M)) S, ⊤) =
      ((AffineSpace.over (ULift.{u} (Fin M)) S).hom.appTop).hom := rfl
  have hFTX := AffineSpace.algebraFiniteType_appTop M S halgX
  have hloc : IsLocalization.Away a
      Γ(((AffineSpace (ULift.{u} (Fin M)) S).basicOpen a).toScheme, ⊤) :=
    Γ_restrict_isLocalization (AffineSpace (ULift.{u} (Fin M)) S) a
  let algU : Algebra Γ(S, ⊤)
      Γ(((AffineSpace (ULift.{u} (Fin M)) S).basicOpen a).toScheme, ⊤) :=
    ((((AffineSpace (ULift.{u} (Fin M)) S).basicOpen a).ι ≫
      (AffineSpace.over (ULift.{u} (Fin M)) S).hom).appTop).hom.toAlgebra
  have htow : IsScalarTower Γ(S, ⊤) Γ(AffineSpace (ULift.{u} (Fin M)) S, ⊤)
      Γ(((AffineSpace (ULift.{u} (Fin M)) S).basicOpen a).toScheme, ⊤) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((((AffineSpace (ULift.{u} (Fin M)) S).basicOpen a).ι ≫
      (AffineSpace.over (ULift.{u} (Fin M)) S).hom).appTop).hom = _
    rw [Scheme.Hom.comp_appTop]
    rfl
  have hFTU : Algebra.FiniteType Γ(S, ⊤)
      Γ(((AffineSpace (ULift.{u} (Fin M)) S).basicOpen a).toScheme, ⊤) :=
    Algebra.FiniteType.trans hFTX (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers a) _)
  exact pushforwardStructureSheafPseudoCoherentOver_of_relative _ rfl
    (PseudoCoherence.isModuleRelativelyPseudoCoherent_localizationAway a
      (AffineSpace.isModuleRelativelyPseudoCoherent_appTop M S halgX))

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- **The side condition of Stacks 09VA at an affine space over a standard open of an affine
base.** This is the hypothesis `hOS` of
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_affineOpen'`,
repaired by the compatibility with the structure morphisms and discharged — and the one place
where Stacks 09VD's hypothesis that `V` is a *standard* open of `S` is used.

`Γ(𝔸ⁿ_{S_b}, ⊤)` is the polynomial ring `Γ(S_b, ⊤)[y₁, …, yₙ]`
(`AlgebraicGeometry.AffineSpace.algEquivMvPolynomialFin`), and `Γ(S_b, ⊤)` is the localization of
`Γ(S, ⊤)` away from `b`, so that ring is the localization of `Γ(S, ⊤)[y₁, …, yₙ]` away from the
constant `b`. For an arbitrary affine open `V` of `S` in place of `S_b` the sections `Γ(𝔸ⁿ_V, ⊤)`
need not be a localization of a polynomial ring over `Γ(S, ⊤)`, which is why the hypothesis is
needed. -/
public theorem pushforwardStructureSheafPseudoCoherentOver_affineSpace (n : ℕ) (S : Scheme.{u})
    [IsAffine S] (b : Γ(S, ⊤)) :
    PushforwardStructureSheafPseudoCoherentOver S
      (AffineSpace (ULift.{u} (Fin n)) (S.basicOpen b).toScheme)
      ((AffineSpace.over (ULift.{u} (Fin n)) (S.basicOpen b).toScheme).hom ≫
        (S.basicOpen b).ι) := by
  have hVaff : IsAffine (S.basicOpen b).toScheme := (isAffineOpen_top S).basicOpen b
  have hlocW : IsLocalization.Away b Γ((S.basicOpen b).toScheme, ⊤) :=
    Γ_restrict_isLocalization S b
  let algWC : Algebra Γ((S.basicOpen b).toScheme, ⊤)
      Γ(AffineSpace (ULift.{u} (Fin n)) (S.basicOpen b).toScheme, ⊤) :=
    ((AffineSpace.over (ULift.{u} (Fin n)) (S.basicOpen b).toScheme).hom.appTop).hom.toAlgebra
  have halgWC : algebraMap Γ((S.basicOpen b).toScheme, ⊤)
      Γ(AffineSpace (ULift.{u} (Fin n)) (S.basicOpen b).toScheme, ⊤) =
      ((AffineSpace.over (ULift.{u} (Fin n)) (S.basicOpen b).toScheme).hom.appTop).hom := rfl
  have hlocP : IsLocalization.Away (MvPolynomial.C b : MvPolynomial (Fin n) Γ(S, ⊤))
      (MvPolynomial (Fin n) Γ((S.basicOpen b).toScheme, ⊤)) := by
    simpa only [Submonoid.map_powers] using
      (inferInstance : IsLocalization ((Submonoid.powers b).map MvPolynomial.C)
        (MvPolynomial (Fin n) Γ((S.basicOpen b).toScheme, ⊤)))
  have hFTPb : Algebra.FiniteType Γ(S, ⊤)
      (MvPolynomial (Fin n) Γ((S.basicOpen b).toScheme, ⊤)) :=
    Algebra.FiniteType.trans
      (inferInstance : Algebra.FiniteType Γ(S, ⊤) (MvPolynomial (Fin n) Γ(S, ⊤)))
      (IsLocalization.finiteType_of_monoid_fg
        (Submonoid.powers (MvPolynomial.C b : MvPolynomial (Fin n) Γ(S, ⊤))) _)
  have hPb := PseudoCoherence.isModuleRelativelyPseudoCoherent_localizationAway
    (Aa := MvPolynomial (Fin n) Γ((S.basicOpen b).toScheme, ⊤))
    (MvPolynomial.C b : MvPolynomial (Fin n) Γ(S, ⊤))
    (PseudoCoherence.isModuleRelativelyPseudoCoherent_mvPolynomial_self Γ(S, ⊤) n)
  let algSC : Algebra Γ(S, ⊤)
      Γ(AffineSpace (ULift.{u} (Fin n)) (S.basicOpen b).toScheme, ⊤) :=
    ((((AffineSpace.over (ULift.{u} (Fin n)) (S.basicOpen b).toScheme).hom ≫
      (S.basicOpen b).ι).appTop)).hom.toAlgebra
  have htow : IsScalarTower Γ(S, ⊤) Γ((S.basicOpen b).toScheme, ⊤)
      Γ(AffineSpace (ULift.{u} (Fin n)) (S.basicOpen b).toScheme, ⊤) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((((AffineSpace.over (ULift.{u} (Fin n)) (S.basicOpen b).toScheme).hom ≫
      (S.basicOpen b).ι).appTop)).hom = _
    rw [Scheme.Hom.comp_appTop]
    rfl
  have e' := (AffineSpace.algEquivMvPolynomialFin n (S.basicOpen b).toScheme halgWC).restrictScalars
    Γ(S, ⊤)
  have hFTC : Algebra.FiniteType Γ(S, ⊤)
      Γ(AffineSpace (ULift.{u} (Fin n)) (S.basicOpen b).toScheme, ⊤) :=
    Algebra.FiniteType.of_surjective e'.toAlgHom e'.surjective
  exact pushforwardStructureSheafPseudoCoherentOver_of_relative _ rfl
    (PseudoCoherence.isModuleRelativelyPseudoCoherent_of_algEquiv e' hPb)

/-! ### Stacks 09VE and Stacks 09VD -/

/-- **Enlarging the base of the local condition of Stacks 09UI along a morphism locally of finite
type.** This is
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_comp` with its
side condition asked for only at the closed immersions that lie over `S`. -/
public theorem exists_isPseudoCoherentFromAfterPushforward_of_comp_over {X Y S : Scheme.{u}}
    [IsAffine Y] [IsAffine S] (i : X ⟶ Y) [IsClosedImmersion i] (g : Y ⟶ S)
    [LocallyOfFiniteType g] (hO : PushforwardStructureSheafPseudoCoherentOver S Y g)
    (E : DerivedCategory X.Modules) (m : ℤ) (h : IsPseudoCoherentFromAfterPushforward i E m) :
    ∃ (N : ℕ) (j : X ⟶ AffineSpace (ULift.{u} (Fin N)) S),
      IsClosedImmersion j ∧
        j ≫ (AffineSpace.over (ULift.{u} (Fin N)) S).hom = i ≫ g ∧
          IsPseudoCoherentFromAfterPushforward j E m := by
  obtain ⟨N, p, hp, hpo⟩ := exists_isClosedImmersion_affineSpace g
  have := hp
  exact ⟨N, i ≫ p, inferInstance, by rw [Category.assoc, hpo],
    IsPseudoCoherentFromAfterPushforward.comp i p (hO N p hp hpo) h⟩

/-- The structure morphism of a finite-dimensional affine space is locally of finite type. -/
private theorem locallyOfFiniteType_affineSpace_over_hom (N : ℕ) (S : Scheme.{u}) :
    LocallyOfFiniteType (AffineSpace.over (ULift.{u} (Fin N)) S).hom := by
  rw [AffineSpace.over_hom_eq]
  infer_instance

/-- The composite of the inclusion of a standard open of a finite-dimensional affine space with the
structure morphism is locally of finite type. -/
private theorem locallyOfFiniteType_basicOpen_ι_comp_over (N : ℕ) (S : Scheme.{u})
    (a : Γ(AffineSpace (ULift.{u} (Fin N)) S, ⊤)) :
    LocallyOfFiniteType (((AffineSpace (ULift.{u} (Fin N)) S).basicOpen a).ι ≫
      (AffineSpace.over (ULift.{u} (Fin N)) S).hom) :=
  MorphismProperty.comp_mem _ _ _ inferInstance (locallyOfFiniteType_affineSpace_over_hom N S)

/-- **The first step of the proof of Stacks 09VD.** This is
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_affineOpen` with
its side condition asked for only at the closed immersions that lie over `S`. -/
public theorem exists_isPseudoCoherentFromAfterPushforward_of_affineOpen_over {S X : Scheme.{u}}
    [IsAffine S] (V : S.affineOpens) (f : X ⟶ (V.1 : Scheme.{u}))
    (hOS : ∀ n : ℕ, PushforwardStructureSheafPseudoCoherentOver S
      (AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u}))
      ((AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom ≫ V.1.ι))
    (E : DerivedCategory X.Modules) (m : ℤ)
    (h : ∃ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u})),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom = f ∧
          IsPseudoCoherentFromAfterPushforward i E m) :
    ∃ (N : ℕ) (j : X ⟶ AffineSpace (ULift.{u} (Fin N)) S),
      IsClosedImmersion j ∧
        j ≫ (AffineSpace.over (ULift.{u} (Fin N)) S).hom = f ≫ V.1.ι ∧
          IsPseudoCoherentFromAfterPushforward j E m := by
  have hVaff : IsAffine (V.1 : Scheme.{u}) := V.2
  obtain ⟨n, i, hi, hio, hpc⟩ := h
  have := hi
  have hg : LocallyOfFiniteType
      ((AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom ≫ V.1.ι) :=
    MorphismProperty.comp_mem _ _ _ (locallyOfFiniteType_affineSpace_over_hom n _) inferInstance
  obtain ⟨N, j, hj, hjo, hjpc⟩ :=
    exists_isPseudoCoherentFromAfterPushforward_of_comp_over i
      ((AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom ≫ V.1.ι) (hOS n) E m hpc
  exact ⟨N, j, hj, by rw [hjo, ← Category.assoc, hio], hjpc⟩

/-- **The second paragraph of the proof of Stacks 09VD.** This is
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_basicOpen` with its
side condition asked for only at the closed immersions that lie over `S`. -/
public theorem exists_isPseudoCoherentFromAfterPushforward_basicOpen_over {X S : Scheme.{u}}
    [IsAffine S] (f : X ⟶ S)
    (hO : ∀ (N : ℕ) (a : Γ(AffineSpace (ULift.{u} (Fin N)) S, ⊤)),
      PushforwardStructureSheafPseudoCoherentOver S
        ((AffineSpace (ULift.{u} (Fin N)) S).basicOpen a).toScheme
        (((AffineSpace (ULift.{u} (Fin N)) S).basicOpen a).ι ≫
          (AffineSpace.over (ULift.{u} (Fin N)) S).hom))
    (E : DerivedCategory X.Modules) (m : ℤ) (g : Γ(X, ⊤))
    (h : ∃ (N : ℕ) (j : X ⟶ AffineSpace (ULift.{u} (Fin N)) S),
      IsClosedImmersion j ∧
        j ≫ (AffineSpace.over (ULift.{u} (Fin N)) S).hom = f ∧
          IsPseudoCoherentFromAfterPushforward j E m) :
    ∃ (N' : ℕ) (l : (X.basicOpen g).toScheme ⟶ AffineSpace (ULift.{u} (Fin N')) S),
      IsClosedImmersion l ∧
        l ≫ (AffineSpace.over (ULift.{u} (Fin N')) S).hom = (X.basicOpen g).ι ≫ f ∧
          IsPseudoCoherentFromAfterPushforward l
            ((restrictFunctor (X.basicOpen g).ι).mapDerivedCategory.obj E) m := by
  obtain ⟨N, j, hj, hjo, hpc⟩ := h
  have := hj
  obtain ⟨g', hg'⟩ := j.app_surjective ⊤ (isAffineOpen_top _) g
  have hpre : j ⁻¹ᵁ ((AffineSpace (ULift.{u} (Fin N)) S).basicOpen g') = X.basicOpen g := by
    rw [Scheme.preimage_basicOpen_top]
    exact congrArg X.basicOpen hg'
  rw [← hpre]
  have hWa : IsAffineOpen ((AffineSpace (ULift.{u} (Fin N)) S).basicOpen g') :=
    (isAffineOpen_top _).basicOpen g'
  have hWaff : IsAffine ((AffineSpace (ULift.{u} (Fin N)) S).basicOpen g').toScheme := hWa
  have hgft := locallyOfFiniteType_basicOpen_ι_comp_over N S g'
  obtain ⟨N', l, hl, hlo, hlpc⟩ :=
    exists_isPseudoCoherentFromAfterPushforward_of_comp_over
      (j ∣_ ((AffineSpace (ULift.{u} (Fin N)) S).basicOpen g'))
      (((AffineSpace (ULift.{u} (Fin N)) S).basicOpen g').ι ≫
        (AffineSpace.over (ULift.{u} (Fin N)) S).hom) (hO N g') _ m
      (IsPseudoCoherentFromAfterPushforward.morphismRestrict j
        ((AffineSpace (ULift.{u} (Fin N)) S).basicOpen g') E m hpc)
  refine ⟨N', l, hl, ?_, hlpc⟩
  rw [hlo, ← Category.assoc, morphismRestrict_ι, Category.assoc, hjo]

/-- **Stacks 09VD at a standard open of `X`**, with both side conditions asked for only at the
closed immersions that lie over the base. This is the namesake
`exists_isPseudoCoherentFromAfterPushforward_basicOpen_of_affineOpen` of
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/RestrictTarget.lean` in that form. -/
public theorem exists_isPseudoCoherentFromAfterPushforward_basicOpen_of_affineOpen_over
    {S X : Scheme.{u}} [IsAffine S] (V : S.affineOpens) (f : X ⟶ (V.1 : Scheme.{u}))
    (hOV : ∀ (N : ℕ) (a : Γ(AffineSpace (ULift.{u} (Fin N)) (V.1 : Scheme.{u}), ⊤)),
      PushforwardStructureSheafPseudoCoherentOver (V.1 : Scheme.{u})
        ((AffineSpace (ULift.{u} (Fin N)) (V.1 : Scheme.{u})).basicOpen a).toScheme
        (((AffineSpace (ULift.{u} (Fin N)) (V.1 : Scheme.{u})).basicOpen a).ι ≫
          (AffineSpace.over (ULift.{u} (Fin N)) (V.1 : Scheme.{u})).hom))
    (hOS : ∀ n : ℕ, PushforwardStructureSheafPseudoCoherentOver S
      (AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u}))
      ((AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom ≫ V.1.ι))
    (E : DerivedCategory X.Modules) (m : ℤ) (g : Γ(X, ⊤))
    (h : ∃ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u})),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom = f ∧
          IsPseudoCoherentFromAfterPushforward i E m) :
    ∃ (N : ℕ) (j : (X.basicOpen g).toScheme ⟶ AffineSpace (ULift.{u} (Fin N)) S),
      IsClosedImmersion j ∧
        j ≫ (AffineSpace.over (ULift.{u} (Fin N)) S).hom = ((X.basicOpen g).ι ≫ f) ≫ V.1.ι ∧
          IsPseudoCoherentFromAfterPushforward j
            ((restrictFunctor (X.basicOpen g).ι).mapDerivedCategory.obj E) m :=
  have : IsAffine (V.1 : Scheme.{u}) := V.2
  exists_isPseudoCoherentFromAfterPushforward_of_affineOpen_over V ((X.basicOpen g).ι ≫ f) hOS _ m
    (exists_isPseudoCoherentFromAfterPushforward_basicOpen_over f hOV E m g h)

/-- **The local step of the proof of Stacks 09VE.** This is
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_morphismRestrict_basicOpen'`
with its side condition asked for only at the closed immersions that lie over `S`. -/
public theorem isPseudoCoherentFromAfterPushforward_morphismRestrict_basicOpen_over
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] {M : ℕ}
    (i : X ⟶ AffineSpace (ULift.{u} (Fin M)) S) [IsClosedImmersion i] (f : X ⟶ S)
    [LocallyOfFiniteType f]
    (hover : i ≫ (AffineSpace.over (ULift.{u} (Fin M)) S).hom = f)
    (y : Γ(AffineSpace (ULift.{u} (Fin M)) S, ⊤))
    (hOy : PushforwardStructureSheafPseudoCoherentOver S
      ((AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).toScheme
      (((AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).ι ≫
        (AffineSpace.over (ULift.{u} (Fin M)) S).hom))
    (E : DerivedCategory X.Modules) (m : ℤ)
    (h : ∃ (k : ℕ) (l : (i ⁻¹ᵁ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).toScheme ⟶
        AffineSpace (ULift.{u} (Fin k)) S),
      IsClosedImmersion l ∧
        l ≫ (AffineSpace.over (ULift.{u} (Fin k)) S).hom =
          (i ⁻¹ᵁ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).ι ≫ f ∧
          IsPseudoCoherentFromAfterPushforward l
            ((restrictFunctor
              (i ⁻¹ᵁ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).ι).mapDerivedCategory.obj E)
            m) :
    IsPseudoCoherentFromAfterPushforward (i ∣_ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y)
      ((restrictFunctor
        (i ⁻¹ᵁ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).ι).mapDerivedCategory.obj E) m := by
  have hWa : IsAffineOpen ((AffineSpace (ULift.{u} (Fin M)) S).basicOpen y) :=
    (isAffineOpen_top _).basicOpen y
  have hWaff : IsAffine ((AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).toScheme := hWa
  have hUaff : IsAffine (i ⁻¹ᵁ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).toScheme := by
    rw [Scheme.preimage_basicOpen_top]
    exact (isAffineOpen_top X).basicOpen _
  have hWft := locallyOfFiniteType_basicOpen_ι_comp_over M S y
  obtain ⟨N, q, hq, hqo⟩ := exists_isClosedImmersion_affineSpace
    (((AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).ι ≫
      (AffineSpace.over (ULift.{u} (Fin M)) S).hom)
  have := hq
  have key : IsPseudoCoherentFromAfterPushforward
      ((i ∣_ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y) ≫ q) _ m :=
    (isPseudoCoherentFrom_some_iff_forall_fin
      ((i ⁻¹ᵁ (AffineSpace (ULift.{u} (Fin M)) S).basicOpen y).ι ≫ f) _ m).mp h N _
      inferInstance (by rw [Category.assoc, hqo, ← Category.assoc, morphismRestrict_ι,
        Category.assoc, hover])
  rw [isPseudoCoherentFromAfterPushforward_comp_iff] at key
  rw [isPseudoCoherentFromAfterPushforward_iff]
  exact isPseudoCoherentFrom_of_pushforward_mapDerivedCategory q (hOy N q hq hqo) m _ key

/-- **The implication (1) ⇒ (2) of Stacks 09VE.** This is
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_forall_basicOpen'`
with its side condition asked for only at the closed immersions that lie over `S`. -/
public theorem exists_isPseudoCoherentFromAfterPushforward_of_forall_basicOpen_over
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) [LocallyOfFiniteType f]
    (hOb : ∀ (N : ℕ) (a : Γ(AffineSpace (ULift.{u} (Fin N)) S, ⊤)),
      PushforwardStructureSheafPseudoCoherentOver S
        ((AffineSpace (ULift.{u} (Fin N)) S).basicOpen a).toScheme
        (((AffineSpace (ULift.{u} (Fin N)) S).basicOpen a).ι ≫
          (AffineSpace.over (ULift.{u} (Fin N)) S).hom))
    (E : DerivedCategory X.Modules) (m : ℤ) {n : ℕ} (g : Fin n → Γ(X, ⊤))
    (hg : PrimeSpectrum.IsStandardOpenCoverOfSpectrum g)
    (h : ∀ j : Fin n, ∃ (k : ℕ) (l : (X.basicOpen (g j)).toScheme ⟶
        AffineSpace (ULift.{u} (Fin k)) S),
      IsClosedImmersion l ∧
        l ≫ (AffineSpace.over (ULift.{u} (Fin k)) S).hom = (X.basicOpen (g j)).ι ≫ f ∧
          IsPseudoCoherentFromAfterPushforward l
            ((restrictFunctor (X.basicOpen (g j)).ι).mapDerivedCategory.obj E) m) :
    ∃ (K : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin K)) S),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin K)) S).hom = f ∧
          IsPseudoCoherentFromAfterPushforward i E m := by
  obtain ⟨M, i, hi, hiover⟩ := exists_isClosedImmersion_affineSpace f
  have := hi
  choose y hy using fun j => i.app_surjective ⊤ (isAffineOpen_top _) (g j)
  have hpre : ∀ j, i ⁻¹ᵁ ((AffineSpace (ULift.{u} (Fin M)) S).basicOpen (y j)) =
      X.basicOpen (g j) := by
    intro j
    rw [Scheme.preimage_basicOpen_top]
    exact congrArg X.basicOpen (hy j)
  have hcov : (⨆ j, X.basicOpen (g j)) = ⊤ :=
    (Scheme.isStandardOpenCoverOfSpectrum_iff_iSup_basicOpen_eq_top g).mp hg
  refine ⟨M, i, hi, hiover, ?_⟩
  rw [isPseudoCoherentFromAfterPushforward_iff]
  refine RingedSpace.isPseudoCoherentFrom_of_local_restrict
    (X := (AffineSpace (ULift.{u} (Fin M)) S).toRingedSpace) _ m fun x => ?_
  by_cases hx : x ∈ Set.range i.toLRSHom.toShHom.hom.base
  · obtain ⟨z, rfl⟩ := hx
    have hz : z ∈ (⨆ j, X.basicOpen (g j)) := by
      rw [hcov]
      exact Opens.mem_top z
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hz
    rw [← hpre j] at hj
    refine ⟨(AffineSpace (ULift.{u} (Fin M)) S).basicOpen (y j), hj, ?_⟩
    refine isPseudoCoherentFrom_derivedRestrictModules_of_morphismRestrict i _ E m ?_
    exact isPseudoCoherentFromAfterPushforward_morphismRestrict_basicOpen_over i f hiover (y j)
      (hOb M (y j)) E m (by rw [hpre j]; exact h j)
  · have hopen : IsOpen (Set.range i.toLRSHom.toShHom.hom.base)ᶜ :=
      (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i).isClosed_range.isOpen_compl
    have hbot : (Opens.map i.toLRSHom.toShHom.hom.base).obj
        ⟨(Set.range i.toLRSHom.toShHom.hom.base)ᶜ, hopen⟩ = ⊥ := by
      ext w
      simp
    have hzero := RingedSpace.isZero_derivedRestrict_derivedPushforward_of_preimage_eq_bot
      i.toLRSHom.toShHom ⟨(Set.range i.toLRSHom.toShHom.hom.base)ᶜ, hopen⟩
      (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i) hbot E
    exact ⟨⟨(Set.range i.toLRSHom.toShHom.hom.base)ᶜ, hopen⟩, hx,
      RingedSpace.IsPseudoCoherentFrom.of_isZero hzero m⟩

/-- **Stacks 09VE.** Let `f : X ⟶ S` be a morphism of affine schemes locally of finite type, let
`E` be an object of `D(𝒪_X)` and let the basic opens of `g : Fin n → Γ(X, ⊤)` be a standard affine
open cover of `X`. Then the equivalent conditions of Stacks 09VC hold for every pair
`(X_{gⱼ} ⟶ S, E|_{X_{gⱼ}})` if and only if they hold for the pair `(X ⟶ S, E)`.

This is
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_basicOpen'` with its
hypothesis `hOb` discharged by
`AlgebraicGeometry.Scheme.Modules.pushforwardStructureSheafPseudoCoherentOver_basicOpen`. -/
@[stacks 09VE]
public theorem isPseudoCoherentFrom_some_iff_forall_standardCover {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (E : DerivedCategory X.Modules) (m : ℤ) {n : ℕ} (g : Fin n → Γ(X, ⊤))
    (hg : PrimeSpectrum.IsStandardOpenCoverOfSpectrum g) :
    (∀ j : Fin n, ∃ (k : ℕ) (i : (X.basicOpen (g j)).toScheme ⟶
        AffineSpace (ULift.{u} (Fin k)) S),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin k)) S).hom = (X.basicOpen (g j)).ι ≫ f ∧
          IsPseudoCoherentFromAfterPushforward i
            ((restrictFunctor (X.basicOpen (g j)).ι).mapDerivedCategory.obj E) m) ↔
      (∃ (k : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin k)) S),
        IsClosedImmersion i ∧
          i ≫ (AffineSpace.over (ULift.{u} (Fin k)) S).hom = f ∧
            IsPseudoCoherentFromAfterPushforward i E m) :=
  ⟨exists_isPseudoCoherentFromAfterPushforward_of_forall_basicOpen_over f
      (fun N a => pushforwardStructureSheafPseudoCoherentOver_basicOpen N S a) E m g hg,
    fun h j => exists_isPseudoCoherentFromAfterPushforward_basicOpen_over f
      (fun N a => pushforwardStructureSheafPseudoCoherentOver_basicOpen N S a) E m (g j) h⟩

/-- **Stacks 09VD.** Let `S` be affine, let `V` be a standard open of `S`, let `X` be affine and
`f : X ⟶ V` locally of finite type, let `E` be an object of `D(𝒪_X)` and let `U` be an affine open
of `X`. If the equivalent conditions of Stacks 09VC hold for the pair `(X ⟶ V, E)`, then they hold
for the pair `(U ⟶ S, E|_U)`.

This is
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_affineOpen'` with
its three hypotheses discharged:
`AlgebraicGeometry.Scheme.Modules.pushforwardStructureSheafPseudoCoherentOver_basicOpen` at the
base `S` and at the base `V`, and
`AlgebraicGeometry.Scheme.Modules.pushforwardStructureSheafPseudoCoherentOver_affineSpace` for the
affine spaces over `V` mapping to the affine spaces over `S`. The last of the three is what needs
`V` to be a *standard* open. -/
@[stacks 09VD]
public theorem isPseudoCoherentFromAfterPushforward_restrict {S X : Scheme.{u}}
    [IsAffine S] [IsAffine X] (V : S.affineOpens) (hV : ∃ a : Γ(S, ⊤), V.1 = S.basicOpen a)
    (f : X ⟶ (V.1 : Scheme.{u})) [LocallyOfFiniteType f] [QuasiCompact f]
    (U : X.affineOpens) (E : DerivedCategory X.Modules) (m : ℤ) :
    (∃ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u})),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom = f ∧
          IsPseudoCoherentFromAfterPushforward i E m) →
      (∃ (n : ℕ) (i : (U.1 : Scheme.{u}) ⟶ AffineSpace (ULift.{u} (Fin n)) S),
        IsClosedImmersion i ∧
          i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = U.1.ι ≫ f ≫ V.1.ι ∧
            IsPseudoCoherentFromAfterPushforward i
              ((restrictFunctor U.1.ι).mapDerivedCategory.obj E) m) := by
  obtain ⟨b, hb⟩ := hV
  obtain ⟨V, hVaffine⟩ := V
  subst hb
  intro h
  have hUaff : IsAffine (U.1 : Scheme.{u}) := U.2
  have hVaff : IsAffine (S.basicOpen b : S.Opens).toScheme := hVaffine
  obtain ⟨N, c, hcU, hccov⟩ := exists_fin_basicOpen_le_cover U.1
  have hpre : ∀ j, U.1.ι ⁻¹ᵁ X.basicOpen (c j) =
      (U.1 : Scheme.{u}).basicOpen (U.1.ι.appTop (c j)) :=
    fun j => Scheme.preimage_basicOpen_top U.1.ι (c j)
  have hcov : (⨆ j, (U.1 : Scheme.{u}).basicOpen (U.1.ι.appTop (c j))) = ⊤ :=
    (iSup_congr fun j => hpre j).symm.trans hccov
  refine exists_isPseudoCoherentFromAfterPushforward_of_forall_basicOpen_over
    (U.1.ι ≫ f ≫ (S.basicOpen b : S.Opens).ι)
    (fun K a => pushforwardStructureSheafPseudoCoherentOver_basicOpen K S a) _ m
    (fun j => U.1.ι.appTop (c j))
    ((Scheme.isStandardOpenCoverOfSpectrum_iff_iSup_basicOpen_eq_top _).mpr hcov) fun j => ?_
  obtain ⟨k, l, hl, hlo, hlpc⟩ :=
    exists_isPseudoCoherentFromAfterPushforward_basicOpen_of_affineOpen_over
      ⟨S.basicOpen b, hVaffine⟩ f
      (fun K a => pushforwardStructureSheafPseudoCoherentOver_basicOpen K _ a)
      (fun k => pushforwardStructureSheafPseudoCoherentOver_affineSpace k S b) E m (c j) h
  have := hl
  rw [← hpre j]
  refine ⟨k, (Scheme.Opens.isoOfLE (hcU j)).hom ≫ l, inferInstance, ?_,
    isPseudoCoherentFromAfterPushforward_isoOfLE (hcU j) l E m hlpc⟩
  rw [Category.assoc, hlo, ← Category.assoc, ← Category.assoc,
    Scheme.Opens.isoOfLE_hom_ι (hcU j), Category.assoc, Category.assoc]

end Scheme.Modules

end AlgebraicGeometry

end
