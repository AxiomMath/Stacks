module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SchemeReflect

/-!
# The side condition of Stacks 09VA for affine spaces, and Stacks 09VC

Stacks 09VA transports `m`-pseudo-coherence along a closed immersion `p` whose pushforward of the
structure sheaf is a pseudo-coherent module, and its two halves are proved:
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_pushforward_mapDerivedCategory` and
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_of_pushforward_mapDerivedCategory`. The
proof of Stacks 09VC applies that transport to a closed immersion of finite-dimensional affine
spaces *over* the base, so what it still needs is the side condition there: for
`p : 𝔸ᵃ_S ⟶ 𝔸ᵇ_S` a closed immersion over an affine `S`, the sheaf `p_*𝒪` is pseudo-coherent.

This file proves that side condition and deduces Stacks 09VC.

The algebraic content is
`PseudoCoherence.isModulePseudoCoherentFrom_mvPolynomial_of_surjective`: for a surjection of
`R`-algebras `α : R[x₁, …, x_b] ↠ R[y₁, …, y_a]` the target is an `m`-pseudo-coherent module over
the source, for every `m`. What this file adds is the passage from that statement to the sheaf
`p_*𝒪` on `𝔸ᵇ_S`: the identification of `𝔸ᵃ_S` and `𝔸ᵇ_S` with the spectra of polynomial rings
over `Γ(S, ⊤)`, the recognition of `p` as the spectrum of such an `α`, and the transport of
sheaf-level pseudo-coherence along those identifications.

## Main definitions

* `AlgebraicGeometry.AffineSpace.isoSpecFin`: affine `n`-space over an affine base `S` is the
  spectrum of `Γ(S, ⊤)[x₁, …, x_n]`, with the variables indexed by `Fin n` rather than by
  `ULift (Fin n)`.

## Main results

* `AlgebraicGeometry.AffineSpace.exists_algHom_specMap`: a closed immersion of finite-dimensional
  affine spaces over an affine base is the spectrum of a surjection of polynomial algebras over
  `Γ(S, ⊤)`.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherent_of_forall`: an object of the derived category
  which is `m`-pseudo-coherent for every `m` is pseudo-coherent — one complex serves for all `m`,
  by Stacks 08CC part (2).
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_pushforward_isIso_iff`: sheaf-level
  pseudo-coherence is unchanged by pushing forward along an isomorphism of schemes.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_singleFunctor_pushforward_unit_affineSpace`:
  **the side condition of Stacks 09VA at a closed immersion of finite-dimensional affine spaces
  over an affine base.**
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_fin`: **Stacks 09VC**,
  with no hypotheses left.

## Implementation notes

**The side condition needs `p` to lie over `S`, and is false without it.** The hypothesis `hO` of
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_of_fin` asks for the side
condition at *every* closed immersion `p : 𝔸ᵃ_S ⟶ 𝔸ᵇ_S`, with no compatibility with the structure
morphisms, and that hypothesis cannot be discharged: take `R = k[t₀, t₁, t₂, …]`, let `ψ : R ↠ R`
send `t_{2i}` to `t_i` and `t_{2i+1}` to `0`, and let `φ : R[x] ↠ R` extend `ψ` by `x ↦ 0`. Then
`φ` is surjective, so its spectrum is a closed immersion `𝔸⁰_S ⟶ 𝔸¹_S` for `S = Spec R`, and
`ker φ = (t₁, t₃, t₅, …, x)` stays non-finitely-generated after inverting any element with nonzero
constant term; so `p_*𝒪` is not finitely presented on any neighbourhood of the origin, and is not
a pseudo-coherent module. Such a `p` does not lie over `S`, because `ψ ≠ 𝟙`. The transport
hypothesis of
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_of_transport_fin` *does*
carry the compatibility `p ≫ 𝔸ᵇ_S ↘ S = 𝔸ᵃ_S ↘ S`, which is what makes the induced map of
polynomial rings an algebra map over `Γ(S, ⊤)`; Stacks 09VC is therefore assembled here from that
lemma rather than from `isPseudoCoherentFrom_some_iff_forall_of_fin`, whose two halves of
Stacks 09VA are reused as they stand.

**Why the index type is renamed.** Affine space over a scheme in `Scheme.{u}` is indexed by a type
in `Type u`, so the `n`-dimensional one is `𝔸(ULift (Fin n); S)`, whereas the module-level side
condition is stated for `MvPolynomial (Fin n) R`. The renaming is done once and geometrically, in
`AlgebraicGeometry.AffineSpace.isoSpecFin`, so that no pseudo-coherence statement has to be
transported along a ring isomorphism.

**Why pseudo-coherence in all degrees transports along an isomorphism.** `RingedSpace`-level
pseudo-coherence asks for a *single* complex which is `m`-pseudo-coherent for every `m`, so it
does not follow formally from the degreewise transport
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_pushforward_isIso_iff`. Stacks 08CC part
(2) (`AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_iso`) closes the gap: every
representative of an `m`-pseudo-coherent object is `m`-pseudo-coherent, so one representative,
taken at `m = 0`, serves for all `m`.

The two spellings `AlgebraicGeometry.Scheme.Modules X` and `Stacks.StrictlyPerfect.OXMod
X.toRingedSpace` of the category of `𝒪_X`-modules are the same type, but typeclass synthesis does
not cross between them. The comparison isomorphism in
`isPseudoCoherent_singleFunctor_pushforward_unit_affineSpace` is therefore built by a `have` whose
type is *inferred*, so that it elaborates at the `Scheme.Modules` spelling where the instances are
found, and is then passed as a term to
`AlgebraicGeometry.RingedSpace.IsPseudoCoherent.of_iso`, which checks it at default transparency.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
* [The Stacks Project, Lemma 36.60.9 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [The Stacks Project, Lemma 36.17.1 (08E7)](https://stacks.math.columbia.edu/tag/08E7)
* [The Stacks Project, Lemma 15.82.3 (065H)](https://stacks.math.columbia.edu/tag/065H)
* [The Stacks Project, Lemma 20.46.9 (08CC)](https://stacks.math.columbia.edu/tag/08CC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect MvPolynomial

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

namespace AffineSpace

/-- Renaming the variables of a polynomial ring along `Fin n ≃ ULift (Fin n)`. This is what lets
the `n`-dimensional affine space over a scheme in `Scheme.{u}`, whose index type must live in
`Type u`, be compared with a polynomial ring in `Fin n` variables. -/
public def mvPolynomialFinUliftIso (n : ℕ) (R : CommRingCat.{u}) :
    CommRingCat.of (MvPolynomial (Fin n) R) ≅
      CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) R) :=
  (MvPolynomial.renameEquiv (σ := Fin n) (τ := ULift.{u} (Fin n)) R
    Equiv.ulift.symm).toRingEquiv.toCommRingCatIso

/-- **Affine `n`-space over an affine base is the spectrum of a polynomial ring in `Fin n`
variables.** This is `AlgebraicGeometry.AffineSpace.isoOfIsAffine`, whose polynomial ring is
indexed by the index type `ULift (Fin n)` of the affine space, followed by the renaming
`AlgebraicGeometry.AffineSpace.mvPolynomialFinUliftIso`. -/
public def isoSpecFin (n : ℕ) (S : Scheme.{u}) [IsAffine S] :
    AffineSpace (ULift.{u} (Fin n)) S ≅
      Spec (CommRingCat.of (MvPolynomial (Fin n) Γ(S, ⊤))) :=
  isoOfIsAffine (ULift.{u} (Fin n)) S ≪≫
    { hom := Spec.map (mvPolynomialFinUliftIso n Γ(S, ⊤)).hom
      inv := Spec.map (mvPolynomialFinUliftIso n Γ(S, ⊤)).inv
      hom_inv_id := by rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
      inv_hom_id := by rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id] }

/-- The identification `AlgebraicGeometry.AffineSpace.isoSpecFin` is compatible with the structure
morphisms: it carries the structure morphism of `𝔸(ULift (Fin n); S)` to the spectrum of the
inclusion of constants. -/
public theorem isoSpecFin_inv_over (n : ℕ) (S : Scheme.{u}) [IsAffine S] :
    (isoSpecFin n S).inv ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin n) (R := Γ(S, ⊤)))) ≫
        S.isoSpec.inv := by
  have hC : CommRingCat.ofHom (MvPolynomial.C (σ := ULift.{u} (Fin n)) (R := Γ(S, ⊤))) ≫
      (mvPolynomialFinUliftIso n Γ(S, ⊤)).inv =
      CommRingCat.ofHom (MvPolynomial.C (σ := Fin n) (R := Γ(S, ⊤))) := by
    ext r
    simp [mvPolynomialFinUliftIso]
  rw [isoSpecFin, Iso.trans_inv, Category.assoc, over_hom_eq, isoOfIsAffine_inv_over,
    ← Spec.map_comp_assoc, hC]

/-- **A closed immersion of finite-dimensional affine spaces over an affine base is the spectrum
of a surjection of polynomial algebras.** Let `p : 𝔸ᵃ_S ⟶ 𝔸ᵇ_S` be a closed immersion over an
affine `S`. Read through `AlgebraicGeometry.AffineSpace.isoSpecFin`, it is `Spec α` for a
surjection of `Γ(S, ⊤)`-algebras `α : Γ(S, ⊤)[x₁, …, x_b] ↠ Γ(S, ⊤)[y₁, …, y_a]`.

Surjectivity of `α` is surjectivity on global sections of a closed immersion of affine schemes
(`AlgebraicGeometry.Scheme.Hom.app_surjective`), and that `α` is a morphism of `Γ(S, ⊤)`-algebras
is the hypothesis that `p` lies over `S`, read through
`AlgebraicGeometry.AffineSpace.isoSpecFin_inv_over` and the faithfulness of `Spec`. -/
public theorem exists_algHom_specMap {S : Scheme.{u}} [IsAffine S] {a b : ℕ}
    (p : AffineSpace (ULift.{u} (Fin a)) S ⟶ AffineSpace (ULift.{u} (Fin b)) S)
    [IsClosedImmersion p]
    (hp : p ≫ (AffineSpace.over (ULift.{u} (Fin b)) S).hom =
      (AffineSpace.over (ULift.{u} (Fin a)) S).hom) :
    ∃ α : MvPolynomial (Fin b) Γ(S, ⊤) →ₐ[Γ(S, ⊤)] MvPolynomial (Fin a) Γ(S, ⊤),
      Function.Surjective α ∧
        Spec.map (CommRingCat.ofHom α.toRingHom) =
          (isoSpecFin a S).inv ≫ p ≫ (isoSpecFin b S).hom := by
  generalize hq : (isoSpecFin a S).inv ≫ p ≫ (isoSpecFin b S).hom = q at *
  have hci : IsClosedImmersion q := hq ▸ inferInstance
  have hmap := Spec.map_preimage q
  have key : q ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin b) (R := Γ(S, ⊤)))) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin a) (R := Γ(S, ⊤)))) := by
    rw [← cancel_mono S.isoSpec.inv, ← hq, Category.assoc, Category.assoc, Category.assoc,
      ← isoSpecFin_inv_over b S, ← isoSpecFin_inv_over a S, Iso.hom_inv_id_assoc, hp]
  have hcomm : CommRingCat.ofHom (MvPolynomial.C (σ := Fin b) (R := Γ(S, ⊤))) ≫
      Spec.preimage q = CommRingCat.ofHom (MvPolynomial.C (σ := Fin a) (R := Γ(S, ⊤))) := by
    refine Spec.map_injective ?_
    rw [Spec.map_comp, hmap]
    exact key
  have hsurj : Function.Surjective (CommRingCat.Hom.hom (Spec.preimage q)) := by
    have hnat := Scheme.ΓSpecIso_naturality (Spec.preimage q)
    rw [hmap] at hnat
    have hq : Function.Surjective (CommRingCat.Hom.hom q.appTop) :=
      Scheme.Hom.app_surjective _ ⊤ (isAffineOpen_top _)
    have heq := congrArg (fun f => (CommRingCat.Hom.hom f : _ → _)) hnat
    simp only [CommRingCat.hom_comp, RingHom.coe_comp] at heq
    have hcomp : Function.Surjective
        ((CommRingCat.Hom.hom (Spec.preimage q)) ∘
          (CommRingCat.Hom.hom
            ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin b) Γ(S, ⊤)))).hom))) :=
      heq ▸ ((ConcreteCategory.bijective_of_isIso
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin a) Γ(S, ⊤)))).hom)).2.comp hq)
    exact hcomp.of_comp
  exact ⟨{ CommRingCat.Hom.hom (Spec.preimage q) with
      commutes' := fun r => congrArg (fun f => (CommRingCat.Hom.hom f) r) hcomm },
    hsurj, by rw [CommRingCat.ofHom_hom]; exact hmap⟩

end AffineSpace

namespace RingedSpace

/-- **An object of the derived category of `𝒪_X`-modules which is `m`-pseudo-coherent for every
`m` is pseudo-coherent.** Pseudo-coherence asks for one complex which is `m`-pseudo-coherent for
every `m`, and the complexes supplied degree by degree need not agree; but by Stacks 08CC part (2)
(`AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_iso`) *every* representative of an
`m`-pseudo-coherent object is `m`-pseudo-coherent, so the representative obtained at `m = 0`
serves for all `m`. -/
public theorem isPseudoCoherent_of_forall {X : RingedSpace.{u, u}}
    [HasDerivedCategory.{u + 1} (StrictlyPerfect.OXMod.{u, u} X)]
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X))
    (h : ∀ m : ℤ, IsPseudoCoherentFrom E m) : IsPseudoCoherent E := by
  obtain ⟨K, -, ⟨e⟩⟩ := h 0
  exact ⟨K, fun m => isPseudoCoherentComplexFrom_of_iso E m (h m) K e, ⟨e⟩⟩

end RingedSpace

namespace Scheme.Modules

/-- **Sheaf-level pseudo-coherence is unchanged by pushing forward along an isomorphism of
schemes.** This is the degreewise statement
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_pushforward_isIso_iff` in every degree,
reassembled by `AlgebraicGeometry.RingedSpace.isPseudoCoherent_of_forall`. -/
public theorem isPseudoCoherent_pushforward_isIso_iff {Y Z : Scheme.{u}} (k : Y ⟶ Z) [IsIso k]
    (A : DerivedCategory Y.Modules) :
    RingedSpace.IsPseudoCoherent (X := Z.toRingedSpace)
        ((pushforward k).mapDerivedCategory.obj A) ↔
      RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace) A :=
  ⟨fun h => RingedSpace.isPseudoCoherent_of_forall.{u} _ fun m =>
      (isPseudoCoherentFrom_pushforward_isIso_iff k A m).1 (h.isPseudoCoherentFrom m),
    fun h => RingedSpace.isPseudoCoherent_of_forall.{u} _ fun m =>
      (isPseudoCoherentFrom_pushforward_isIso_iff k A m).2 (h.isPseudoCoherentFrom m)⟩

/-- The pushforward of the structure sheaf along `Spec φ` is the sheaf associated to the target
ring with its scalars restricted along `φ`. This is `AlgebraicGeometry.pushforwardTildeIso`
(Stacks 01I9) at the ring itself, read through `AlgebraicGeometry.tildeSelf`. -/
public def pushforwardUnitTildeIso {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    (pushforward (Spec.map φ)).obj (SheafOfModules.unit (Spec S).ringCatSheaf) ≅
      (tilde.functor R).obj ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S)) :=
  (pushforward (Spec.map φ)).mapIso tildeSelf.symm ≪≫
    (pushforwardTildeIso R S φ).app (ModuleCat.of S S)

/-- **The side condition of Stacks 09VA at the spectrum of a ring map.** If the target ring, with
its scalars restricted along `φ : R ⟶ S`, is an `m`-pseudo-coherent `R`-module for every `m`, then
the pushforward of `𝒪_{Spec S}` along `Spec φ`, placed in degree zero, is a pseudo-coherent object
of `D(𝒪_{Spec R})`.

This is Stacks 08E7 for a module
(`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_singleFunctor_tilde_iff`) applied in every
degree, the pushforward of the structure sheaf having been identified with an associated sheaf by
`AlgebraicGeometry.Scheme.Modules.pushforwardUnitTildeIso`. -/
public theorem isPseudoCoherent_singleFunctor_pushforward_unit_specMap {R S : CommRingCat.{u}}
    (φ : R ⟶ S)
    (h : ∀ m : ℤ, StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S))) m) :
    RingedSpace.IsPseudoCoherent (X := (Spec R).toRingedSpace)
      ((DerivedCategory.singleFunctor (Spec R).Modules 0).obj
        ((pushforward (Spec.map φ)).obj (SheafOfModules.unit (Spec S).ringCatSheaf))) :=
  RingedSpace.isPseudoCoherent_of_forall.{u} _ fun m =>
    ((RingedSpace.isPseudoCoherentFrom_singleFunctor_tilde_iff _ m).2 (h m)).of_iso
      ((DerivedCategory.singleFunctor (Spec R).Modules 0).mapIso
        (pushforwardUnitTildeIso φ)).symm

/-- Transporting the pushforward of a structure sheaf along isomorphisms of the source and of the
target. If `q` is `p` read through isomorphisms `u` of the sources and `v` of the targets, then
`q_*𝒪` pushed forward along `v⁻¹` is `p_*𝒪`.

Only the pushforward of the structure sheaf along the isomorphism `u⁻¹`
(`AlgebraicGeometry.Scheme.Modules.pushforwardUnitIso`) and the functoriality of pushforward are
needed; no equivalence of categories of modules intervenes. -/
public def pushforwardUnitCongrIso {Y Z Y' Z' : Scheme.{u}} (p : Y ⟶ Z) (q : Y' ⟶ Z')
    (u : Y ≅ Y') (v : Z ≅ Z') (h : u.inv ≫ p ≫ v.hom = q) :
    (pushforward v.inv).obj ((pushforward q).obj (SheafOfModules.unit Y'.ringCatSheaf)) ≅
      (pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  (pushforwardComp q v.inv).app _ ≪≫
    (pushforwardCongr (show q ≫ v.inv = u.inv ≫ p by
      rw [← h, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id])).app _ ≪≫
    ((pushforwardComp u.inv p).app _).symm ≪≫
    (pushforward p).mapIso (pushforwardUnitIso u.inv)

/-- **The side condition of Stacks 09VA at a closed immersion of finite-dimensional affine spaces
over an affine base.** Let `S` be an affine scheme and `p : 𝔸ᵃ_S ⟶ 𝔸ᵇ_S` a closed immersion over
`S`. Then `p_*𝒪`, placed in degree zero, is a pseudo-coherent object of `D(𝒪_{𝔸ᵇ_S})`.

`AlgebraicGeometry.AffineSpace.exists_algHom_specMap` writes `p` as the spectrum of a surjection
`α` of polynomial algebras over `Γ(S, ⊤)`;
`PseudoCoherence.isModulePseudoCoherentFrom_mvPolynomial_of_surjective` says that the target of
`α` is an `m`-pseudo-coherent module over its source for every `m`, which is the side condition on
`Spec` of `α` by
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_singleFunctor_pushforward_unit_specMap`; and
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_pushforward_isIso_iff` carries it back to
`𝔸ᵇ_S`.

The hypothesis that `p` lies over `S` is what makes `α` a morphism of `Γ(S, ⊤)`-algebras, and the
conclusion is false without it; see the implementation notes of this file. -/
public theorem isPseudoCoherent_singleFunctor_pushforward_unit_affineSpace {S : Scheme.{u}}
    [IsAffine S] {a b : ℕ}
    (p : AffineSpace (ULift.{u} (Fin a)) S ⟶ AffineSpace (ULift.{u} (Fin b)) S)
    [IsClosedImmersion p]
    (hp : p ≫ (AffineSpace.over (ULift.{u} (Fin b)) S).hom =
      (AffineSpace.over (ULift.{u} (Fin a)) S).hom) :
    RingedSpace.IsPseudoCoherent (X := (AffineSpace (ULift.{u} (Fin b)) S).toRingedSpace)
      ((DerivedCategory.singleFunctor (AffineSpace (ULift.{u} (Fin b)) S).Modules 0).obj
        ((pushforward p).obj
          (SheafOfModules.unit (AffineSpace (ULift.{u} (Fin a)) S).ringCatSheaf))) := by
  obtain ⟨α, hα, hspec⟩ := AffineSpace.exists_algHom_specMap p hp
  have hmod := fun m : ℤ =>
    PseudoCoherence.isModulePseudoCoherentFrom_mvPolynomial_of_surjective α hα m
  have hside := isPseudoCoherent_singleFunctor_pushforward_unit_specMap
    (CommRingCat.ofHom α.toRingHom) hmod
  have e := (Functor.mapDerivedCategorySingleFunctor
        (pushforward (AffineSpace.isoSpecFin b S).inv) 0).app
      ((pushforward (Spec.map (CommRingCat.ofHom α.toRingHom))).obj
        (SheafOfModules.unit (Spec (CommRingCat.of (MvPolynomial (Fin a) Γ(S, ⊤)))).ringCatSheaf))
      ≪≫ (DerivedCategory.singleFunctor
        (AffineSpace (ULift.{u} (Fin b)) S).Modules 0).mapIso
      (pushforwardUnitCongrIso p (Spec.map (CommRingCat.ofHom α.toRingHom))
        (AffineSpace.isoSpecFin a S) (AffineSpace.isoSpecFin b S) hspec.symm)
  exact ((isPseudoCoherent_pushforward_isIso_iff (AffineSpace.isoSpecFin b S).inv _).mpr
    hside).of_iso e

/-- **Stacks 09VC.** Let `f : X ⟶ S` be a morphism of affine schemes locally of finite type, let
`E` be an object of `D(𝒪_X)` and let `m` be an integer. Then `m`-pseudo-coherence of the derived
pushforward of `E` along *some* closed immersion of `X` into a finite-dimensional affine space
over `S` factoring `f` is equivalent to `m`-pseudo-coherence of the derived pushforward along
*every* such closed immersion.

This is
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_of_transport_fin`, whose
transport hypothesis is supplied by the two halves of Stacks 09VA —
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_pushforward_mapDerivedCategory` and
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_of_pushforward_mapDerivedCategory` — and
whose side condition is
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_singleFunctor_pushforward_unit_affineSpace`.
Nothing is assumed. -/
@[stacks 09VC]
public theorem isPseudoCoherentFrom_some_iff_forall_fin {X S : Scheme.{u}} [IsAffine X]
    [IsAffine S] (f : X ⟶ S) [LocallyOfFiniteType f] (E : DerivedCategory X.Modules) (m : ℤ) :
    (∃ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = f ∧
          IsPseudoCoherentFromAfterPushforward i E m) ↔
      (∀ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S),
        IsClosedImmersion i →
          i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = f →
            IsPseudoCoherentFromAfterPushforward i E m) :=
  isPseudoCoherentFrom_some_iff_forall_of_transport_fin f E m fun p _ hp A =>
    ⟨isPseudoCoherentFrom_pushforward_mapDerivedCategory p
        (isPseudoCoherent_singleFunctor_pushforward_unit_affineSpace p hp) m A,
      isPseudoCoherentFrom_of_pushforward_mapDerivedCategory p
        (isPseudoCoherent_singleFunctor_pushforward_unit_affineSpace p hp) m A⟩

end Scheme.Modules

end AlgebraicGeometry

end
