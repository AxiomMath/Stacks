module

public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothAffineDeRhamModel
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeSpreadingOut.FiniteTypeModel
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.PushoutBaseChange
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.RestrictPushforward
public import StacksFrontier.AlgebraicGeometry.Modules.SpecFieldDerivedPullback
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology

/-!
# Finite local freeness of the de Rham cohomology sheaves over `ℚ`, from the Artinian case

Let `f : X ⟶ Y` be a proper smooth morphism of schemes over `ℚ`. The remark [Stacks, Tag 0FMN]
asserts that the de Rham cohomology sheaves `ℋ^q_dR(X/Y)` are finite locally free, and defers the
proof to a future reference; it is Deligne's theorem. This file reduces it to the case of an
Artinian local base: if `ℋ^n_dR(X/A)` is finite locally free for every proper smooth `X` over the
spectrum of an Artinian local `ℚ`-algebra `A`, then it is so over every base over `ℚ`.

The reduction is the standard one, run on the model `RΓ(X, Ω^•_{X/A})` of
`StacksFrontier/AlgebraicGeometry/DeRham/ProperSmoothAffineDeRhamModel.lean`:

* over a Noetherian local `ℚ`-algebra `A` the model is perfect, its base change to every
  `A/𝔪^k` is the model of `X ×_A A/𝔪^k` ([Stacks, Tag 0FM0]), and the cohomology of those models
  is free by the Artinian case; Krull's intersection theorem then makes the cohomology of the
  model free (`StacksDraft.Perfect.free_homology_of_forall_quotient_pow`);
* over a Noetherian `ℚ`-algebra the cohomology modules are finite, and free at every maximal
  ideal by flat base change, hence finite projective;
* over an arbitrary `ℚ`-algebra `A`, the proper smooth `X` comes from a proper smooth scheme over
  a finitely generated `ℤ`-algebra ([Stacks, Tag 01ZM], [Stacks, Tag 0C0C]; the model of
  `AlgebraicGeometry.HodgeSpreadingOut.exists_isPullback_finiteType_properSmooth`), and so, after
  inverting the nonzero integers, from one over a Noetherian `ℚ`-algebra; finite projective
  cohomology commutes with derived base change, so the cohomology modules over `A` are finite
  projective, and the de Rham cohomology sheaves on `Spec A` are finite locally free
  ([Stacks, Tag 05JM]);
* over an arbitrary base over `ℚ` the statement is local, and the de Rham cohomology sheaves
  commute with restriction to open subschemes.

## Main definitions

* `Stacks.DeRhamSmooth.ArtinianDeRhamLocallyFree`: the Artinian case, as a proposition. It is
  the hypothesis of the reduction, to be supplied separately.

## Main results

* `Stacks.DeRhamSmooth.free_homology_affineDeRhamModel_of_isNoetherianRing`: the Noetherian local
  case.
* `Stacks.DeRhamSmooth.finite_projective_homology_affineDeRhamModel_of_isNoetherianRing`: the
  Noetherian case.
* `Stacks.DeRhamSmooth.exists_isPullback_noetherian_algebraRat_properSmooth`: a proper smooth
  scheme over a `ℚ`-algebra comes from one over a Noetherian `ℚ`-algebra.
* `Stacks.DeRhamSmooth.isFiniteLocallyFree_deRhamCohomologySheaf_of_affine_of_algebraRat`: the
  affine case.
* `Stacks.DeRhamSmooth.deRhamCohomologySheafRestrictIso`: `ℋ^n_dR(X_U/U) ≅ ℋ^n_dR(X/Y)|_U` for an
  open immersion `U ⟶ Y`.
* `Stacks.DeRhamSmooth.isLocallyFree_deRhamCohomologySheaf_of_artinian`: **the sentence of
  [Stacks, Tag 0FMN] on finite local freeness, from the Artinian case.**

## Implementation notes

No `@[stacks]` attribute is carried: the Artinian case is a hypothesis here. The derived
categories are those of `CategoryTheory.HasDerivedCategory.standard` at priority `10000`, as in
`StacksFrontier/AlgebraicGeometry/DeRham/ProperSmoothAffineDeRhamModel.lean`; the statements of the
main results mention no derived category.

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
* [Stacks Project, Tag 0FM0](https://stacks.math.columbia.edu/tag/0FM0)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 0C0C](https://stacks.math.columbia.edu/tag/0C0C)
* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.DeRhamDirectImage RingedSpaceModuleAdjunction

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.DeRhamSmooth

/-- **The Artinian case of the finite local freeness of de Rham cohomology over `ℚ`**: for every
Artinian local `ℚ`-algebra `A` and every proper smooth `f : X ⟶ Spec A`, every de Rham cohomology
sheaf `ℋ^n_dR(X/A)` is a finite locally free `𝒪_{Spec A}`-module. Over such a base this says that
`H^n_dR(X/A)` is a free `A`-module of finite rank. -/
def ArtinianDeRhamLocallyFree : Prop :=
  ∀ (A : CommRingCat.{u}) [IsArtinianRing A] [IsLocalRing A] [Algebra ℚ A] (X : Scheme.{u})
    (f : X ⟶ Spec A) [IsProper f] [Smooth f] (n : ℤ),
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (deRhamCohomologySheaf f n)

variable {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)

/-- Being finite and projective transfers along a linear equivalence. -/
private theorem finite_projective_of_linearEquiv {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] (e : M ≃ₗ[R] N)
    (h : Module.Finite R M ∧ Module.Projective R M) :
    Module.Finite R N ∧ Module.Projective R N :=
  have := h.1
  have := h.2
  ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩

/-- **The global sections of a finite locally free quasi-coherent module on `Spec A` are finite
projective** ([Stacks, Tag 05JM]). -/
theorem finite_projective_moduleSpecΓ_of_isFiniteLocallyFree (M : (Spec A).Modules)
    [M.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    Module.Finite A ((moduleSpecΓFunctor (R := A)).obj M) ∧
      Module.Projective A ((moduleSpecΓFunctor (R := A)).obj M) := by
  let N := (moduleSpecΓFunctor (R := A)).obj M
  exact (Module.isFiniteLocallyFree_iff_finite_projective A N).1
    ((Stacks.Modules.tilde_isFiniteLocallyFree_iff_module A N).1
      (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso (asIso M.fromTildeΓ).symm))

/-- **The de Rham cohomology modules are finite projective when the de Rham cohomology sheaves are
finite locally free.** -/
theorem finite_projective_homology_affineDeRhamModel [QuasiCompact f] [QuasiSeparated f] (n : ℤ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (deRhamCohomologySheaf f n)] :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        (affineDeRhamModel f)) ∧
      Module.Projective A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        (affineDeRhamModel f)) := by
  have : (deRhamCohomologySheaf f n).IsQuasicoherent :=
    isQuasicoherent_homology_derivedDeRhamDirectImage f n
  exact finite_projective_of_linearEquiv (affineDeRhamModelHomologyIso f n).toLinearEquiv.symm
    (finite_projective_moduleSpecΓ_of_isFiniteLocallyFree (deRhamCohomologySheaf f n))

/-- The maximal ideal of a local ring is a minimal prime over each of its positive powers. -/
theorem maximalIdeal_mem_minimalPrimes_pow {R : Type*} [CommRing R] [IsLocalRing R] {k : ℕ}
    (hk : 0 < k) : IsLocalRing.maximalIdeal R ∈ (IsLocalRing.maximalIdeal R ^ k).minimalPrimes :=
  ⟨⟨inferInstance, Ideal.pow_le_self hk.ne'⟩, fun _q ⟨hq, hle⟩ _ => hq.le_of_pow_le hle⟩

/-- **The Noetherian local case, from the Artinian one.** Let `A` be a Noetherian local
`ℚ`-algebra and `f : X ⟶ Spec A` proper and smooth. Granted the Artinian case `hArt`, every
cohomology module of the model `RΓ(X, Ω^•_{X/A})` — that is, every `H^n_dR(X/A)` — is a free
`A`-module of finite rank.

The base change of the model to `A/𝔪^k` is the model of `X ×_A A/𝔪^k`
(`Stacks.DeRhamSmooth.affineDeRhamModelBaseChangeIso`), whose cohomology is projective by the
Artinian case; Krull's intersection theorem then gives the conclusion
(`StacksDraft.Perfect.free_homology_of_forall_quotient_pow`). -/
theorem free_homology_affineDeRhamModel_of_isNoetherianRing
    (hArt : ArtinianDeRhamLocallyFree.{u}) [IsNoetherianRing A] [IsLocalRing A] [Algebra ℚ A]
    [IsProper f] [Smooth f] (n : ℤ) :
    Module.Free A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        (affineDeRhamModel f)) ∧
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        (affineDeRhamModel f)) := by
  let m := IsLocalRing.maximalIdeal A
  refine StacksDraft.Perfect.free_homology_of_forall_quotient_pow
    (fun k => CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (Ideal.Quotient.mk (m ^ k)))
    (affineDeRhamModel f) (isPerfect_affineDeRhamModel f) (fun k hk i => ?_) n
  let B : CommRingCat.{u} := CommRingCat.of (A ⧸ m ^ k)
  let φ : A ⟶ B := CommRingCat.ofHom (Ideal.Quotient.mk (m ^ k))
  have : Nontrivial B := Ideal.Quotient.nontrivial_iff.2 fun h =>
    (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self hk.ne'))
  have : IsLocalRing B :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (m ^ k)) Ideal.Quotient.mk_surjective
  have : IsArtinianRing B :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing (m ^ k)
      (maximalIdeal_mem_minimalPrimes_pow hk)
  let : Algebra ℚ B := inferInstanceAs (Algebra ℚ (A ⧸ m ^ k))
  let fk := pullback.snd f (Spec.map φ)
  have := hArt B _ fk i
  obtain ⟨-, hproj⟩ := finite_projective_homology_affineDeRhamModel fk i
  exact Module.Projective.of_equiv ((DerivedCategory.homologyFunctor _ i).mapIso
    (affineDeRhamModelBaseChangeIso f φ)).toLinearEquiv

/-- **The Noetherian case, from the Artinian one.** Let `A` be a Noetherian `ℚ`-algebra and
`f : X ⟶ Spec A` proper and smooth. Granted the Artinian case `hArt`, every `H^n_dR(X/A)` is a
finite projective `A`-module: it is finite because the model is perfect over a Noetherian ring,
and at every maximal ideal `𝔪` its localization is `H^n_dR(X_{A_𝔪}/A_𝔪)` (flat base change and
[Stacks, Tag 0FM0]), which is free by the Noetherian local case. -/
theorem finite_projective_homology_affineDeRhamModel_of_isNoetherianRing
    (hArt : ArtinianDeRhamLocallyFree.{u}) [IsNoetherianRing A] [Algebra ℚ A]
    [IsProper f] [Smooth f] (n : ℤ) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        (affineDeRhamModel f)) ∧
      Module.Projective A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        (affineDeRhamModel f)) := by
  let N := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj (affineDeRhamModel f)
  have hfin : Module.Finite A N := module_finite_homology_affineDeRhamModel f n
  refine ⟨hfin, ?_⟩
  have : Module.FinitePresentation A N := Module.finitePresentation_of_finite A N
  refine Module.projective_of_localization_maximal' (Rₚ := fun P _ => Localization.AtPrime P)
    (Mₚ := fun P _ => TensorProduct A (Localization.AtPrime P) N)
    (fun P _ => TensorProduct.mk A (Localization.AtPrime P) N 1) fun I hI => ?_
  let B : CommRingCat.{u} := CommRingCat.of (Localization.AtPrime I)
  let φ : A ⟶ B := CommRingCat.ofHom (algebraMap A (Localization.AtPrime I))
  let fI := pullback.snd f (Spec.map φ)
  obtain ⟨hfree, -⟩ := free_homology_affineDeRhamModel_of_isNoetherianRing (A := B) fI hArt n
  obtain ⟨e⟩ := StacksDraft.Perfect.nonempty_homology_totalDerivedExtensionScalars_iso_of_flat
    φ.hom (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ I.primeCompl))
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      φ.hom) (affineDeRhamModel f) (isPerfect_affineDeRhamModel f) n
  let e' := ((DerivedCategory.homologyFunctor _ n).mapIso
    (affineDeRhamModelBaseChangeIso f φ) ≪≫ e).toLinearEquiv.trans
      (RingTheory.TorIndependence.baseChangeExtendScalarsLinearEquiv A (Localization.AtPrime I)
        N).symm
  have : Module.Free (Localization.AtPrime I) (TensorProduct A (Localization.AtPrime I) N) :=
    Module.Free.of_equiv e'
  exact Module.Projective.of_free

/-- The rational numbers map to a localization in which the images of the nonzero integers are
inverted. -/
def ratHomOfLocalizationIntegers (R : Type u) [CommRing R] :
    ℚ →+* Localization (Submonoid.map (Int.castRingHom R) (nonZeroDivisors ℤ)) :=
  IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ)
    (g := (algebraMap R (Localization (Submonoid.map (Int.castRingHom R) (nonZeroDivisors ℤ)))).comp
      (Int.castRingHom R))
    fun y => IsLocalization.map_units _
      (⟨Int.castRingHom R y, Submonoid.mem_map.2 ⟨y, y.2, rfl⟩⟩ :
        Submonoid.map (Int.castRingHom R) (nonZeroDivisors ℤ))

/-- **A proper smooth scheme over a `ℚ`-algebra comes from a proper smooth scheme over a
Noetherian `ℚ`-algebra.** For `f : X ⟶ Spec A` proper and smooth with `A` a `ℚ`-algebra there are
a Noetherian ring `R'` with a ring map `ℚ → R'`, a ring map `ψ : R' ⟶ A` and a proper smooth
`h' : Y' ⟶ Spec R'` with `X = Y' ×_{Spec R'} Spec A`. The ring `R'` is a finitely generated
`ℤ`-algebra with the nonzero integers inverted; the model over it is the one of
`AlgebraicGeometry.HodgeSpreadingOut.exists_isPullback_finiteType_properSmooth`
([Stacks, Tag 01ZM] and [Stacks, Tag 0C0C]). -/
theorem exists_isPullback_noetherian_algebraRat_properSmooth [Algebra ℚ A] [IsProper f]
    [Smooth f] :
    ∃ (R' : CommRingCat.{u}) (_ : IsNoetherianRing R') (_ : Algebra ℚ R') (ψ : R' ⟶ A)
      (Y' : Scheme.{u}) (h' : Y' ⟶ Spec R') (q : X ⟶ Y'),
      IsProper h' ∧ Smooth h' ∧ IsPullback q f h' (Spec.map ψ) := by
  obtain ⟨R, _, φ, Y, h, q', _, -, hpr, hsm, hpb⟩ :=
    HodgeSpreadingOut.exists_isPullback_finiteType_properSmooth A f
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  let S : Submonoid R := Submonoid.map (Int.castRingHom R) (nonZeroDivisors ℤ)
  let R' : CommRingCat.{u} := CommRingCat.of (Localization S)
  let ι : CommRingCat.of R ⟶ R' := CommRingCat.ofHom (algebraMap R (Localization S))
  let ψ : R' ⟶ A := CommRingCat.ofHom (IsLocalization.lift (M := S) (S := Localization S)
    (g := φ) fun s => by
      obtain ⟨_, ⟨n, hn, rfl⟩⟩ := s
      simpa using ((Int.cast_ne_zero.2 (mem_nonZeroDivisors_iff_ne_zero.1 hn) :
        (n : ℚ) ≠ 0).isUnit.map (algebraMap ℚ A)))
  have hιψ : ι ≫ ψ = CommRingCat.ofHom φ := by
    ext x
    exact IsLocalization.lift_eq _ x
  have hSpec : Spec.map (CommRingCat.ofHom φ) = Spec.map ψ ≫ Spec.map ι := by
    rw [← hιψ, Spec.map_comp]
  have hright := IsPullback.of_hasPullback h (Spec.map ι)
  let q := pullback.lift q' (f ≫ Spec.map ψ) (by rw [hpb.w, hSpec, Category.assoc])
  have hbig : IsPullback (q ≫ pullback.fst h (Spec.map ι)) f h (Spec.map ψ ≫ Spec.map ι) := by
    rwa [pullback.lift_fst, ← hSpec]
  exact ⟨R', inferInstance, (ratHomOfLocalizationIntegers R).toAlgebra, ψ, _, _, q,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper) hright hpr,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Smooth) hright hsm,
    IsPullback.of_right hbig (pullback.lift_snd _ _ _) hright⟩

/-- **The affine case, from the Artinian one.** Let `A` be a `ℚ`-algebra and `f : X ⟶ Spec A`
proper and smooth. Granted the Artinian case `hArt`, every `H^n_dR(X/A)` is a finite projective
`A`-module. The morphism comes from a proper smooth morphism over a Noetherian `ℚ`-algebra
(`exists_isPullback_noetherian_algebraRat_properSmooth`), whose de Rham cohomology modules are
finite projective by the Noetherian case; finite projective cohomology commutes with derived base
change (`StacksDraft.Perfect.finite_projective_homology_totalDerivedExtensionScalars`), and the
model of `f` is the base change of the model over the Noetherian ring ([Stacks, Tag 0FM0]). -/
theorem finite_projective_homology_affineDeRhamModel_of_algebraRat
    (hArt : ArtinianDeRhamLocallyFree.{u}) [Algebra ℚ A] [IsProper f] [Smooth f] (n : ℤ) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        (affineDeRhamModel f)) ∧
      Module.Projective A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        (affineDeRhamModel f)) := by
  obtain ⟨R', _, _, ψ, Y', h', q, hpr, hsm, hsq⟩ :=
    exists_isPullback_noetherian_algebraRat_properSmooth f
  have hH := fun i => finite_projective_homology_affineDeRhamModel_of_isNoetherianRing h' hArt i
  have : Module.Finite R' ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).obj
      (affineDeRhamModel h')) := (hH n).1
  exact finite_projective_of_linearEquiv ((DerivedCategory.homologyFunctor _ n).mapIso
    (affineDeRhamModelBaseChangeIsoOfIsPullback h' ψ q f hsq)).toLinearEquiv.symm
    (StacksDraft.Perfect.finite_projective_homology_totalDerivedExtensionScalars
      ψ.hom (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} ψ.hom)
      (affineDeRhamModel h') (isPerfect_affineDeRhamModel h') (fun i => (hH i).2) n)

/-- **The affine case of the finite local freeness, from the Artinian one.** For a `ℚ`-algebra `A`
and `f : X ⟶ Spec A` proper and smooth, granted the Artinian case, every de Rham cohomology sheaf
`ℋ^n_dR(X/A)` is a finite locally free `𝒪_{Spec A}`-module ([Stacks, Tag 05JM]). -/
theorem isFiniteLocallyFree_deRhamCohomologySheaf_of_affine_of_algebraRat
    (hArt : ArtinianDeRhamLocallyFree.{u}) [Algebra ℚ A] [IsProper f] [Smooth f] (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (deRhamCohomologySheaf f n) := by
  let N := (moduleSpecΓFunctor (R := A)).obj (deRhamCohomologySheaf f n)
  have : (deRhamCohomologySheaf f n).IsQuasicoherent :=
    isQuasicoherent_homology_derivedDeRhamDirectImage f n
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (tilde ((modulesSpecToSheaf.obj (deRhamCohomologySheaf f n)).presheaf.obj (Opposite.op ⊤))) :=
    (Stacks.Modules.tilde_isFiniteLocallyFree_iff_module A N).2
      ((Module.isFiniteLocallyFree_iff_finite_projective A N).2
        (finite_projective_of_linearEquiv (affineDeRhamModelHomologyIso f n).toLinearEquiv
          (finite_projective_homology_affineDeRhamModel_of_algebraRat f hArt n)))
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
    (asIso (deRhamCohomologySheaf f n).fromTildeΓ)

section Global

variable {Y U : Scheme.{u}}

/-- **The de Rham cohomology sheaves commute with restriction to an open subscheme**: for
`p : X ⟶ Y` proper smooth and an open immersion `g : U ⟶ Y`,
`ℋ^n_dR(X_U/U) ≅ ℋ^n_dR(X/Y)|_U`. The derived direct image commutes with the base change along
`g` ([Stacks, Tag 0FM0]), and along an open immersion the derived pullback is the exact
restriction, which commutes with cohomology. -/
def deRhamCohomologySheafRestrictIso (p : X ⟶ Y) (g : U ⟶ Y) [IsOpenImmersion g] [IsProper p]
    [Smooth p] (n : ℤ) :
    deRhamCohomologySheaf (pullback.snd p g) n ≅
      (Scheme.Modules.restrictFunctor g).obj (deRhamCohomologySheaf p n) :=
  have : PreservesFiniteLimits (modulePullback g.toLRSHom.toShHom) :=
    preservesFiniteLimits_modulePullback_of_isOpenImmersion g
  have : PreservesFiniteColimits (modulePullback g.toLRSHom.toShHom) :=
    preservesFiniteColimits_modulePullback_of_isOpenImmersion g
  (DerivedCategory.homologyFunctor _ n).mapIso
      (DeRhamCohomologyDirectImage.derivedDeRhamDirectImageUnboundedIso (pullback.snd p g) ≪≫
        (deRhamUnboundedBaseChangeIsoOfIsPullback p g _ _ (IsPullback.of_hasPullback p g)).symm ≪≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          g.toLRSHom.toShHom).mapIso
          (DeRhamCohomologyDirectImage.derivedDeRhamDirectImageUnboundedIso p).symm ≪≫
        (SpecField.derivedPullbackMapDerivedIso g.toLRSHom.toShHom).app _) ≪≫
    ((modulePullback g.toLRSHom.toShHom).mapDerivedCategoryHomologyIso n).app _ ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback g).symm.app _

/-- **Stacks Project, Tag 0FMN, finite local freeness, from the Artinian case.** Let
`f : X ⟶ Y` be a proper smooth morphism of schemes, `g : Y ⟶ S`, and let `S` lie over `Spec R`
for a `ℚ`-algebra `R` (for instance `R = ℚ`). Granted the Artinian case `hArt` — the finite local
freeness of `ℋ^n_dR` over the spectrum of every Artinian local `ℚ`-algebra — every de Rham
cohomology sheaf `ℋ^q_dR(X/Y)` is a finite locally free `𝒪_Y`-module.

The statement is local on `Y`, so it is enough to treat `Y = Spec A` affine, which is
`isFiniteLocallyFree_deRhamCohomologySheaf_of_affine_of_algebraRat`: there the proper smooth
`X` comes from a Noetherian `ℚ`-algebra, over which the cohomology modules are finite projective
because their localizations at maximal ideals are free, by the Artinian case and Krull's
intersection theorem. This is Deligne's theorem with its Artinian input isolated; the source
defers the proof to a future reference. -/
theorem isLocallyFree_deRhamCohomologySheaf_of_artinian (hArt : ArtinianDeRhamLocallyFree.{u})
    {S : Scheme.{u}} {R : CommRingCat.{u}} [Algebra ℚ R] (f : X ⟶ Y) (g : Y ⟶ S)
    (σ : S ⟶ Spec R) [IsProper f] [Smooth f] (q : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (deRhamCohomologySheaf f q) := by
  rw [← Scheme.Modules.isFiniteLocallyFree_iff]
  let 𝒰 := Y.affineOpenCover
  refine Scheme.Modules.isFiniteLocallyFree_of_isOpenImmersion_cover 𝒰.f
    𝒰.openCover.iSup_opensRange fun j => ?_
  let ρ : R ⟶ 𝒰.X j := Spec.preimage (𝒰.f j ≫ g ≫ σ)
  let : Algebra ℚ (𝒰.X j) := (ρ.hom.comp (algebraMap ℚ R)).toAlgebra
  exact Scheme.Modules.IsFiniteLocallyFree.of_iso (deRhamCohomologySheafRestrictIso f (𝒰.f j) q)
    ((Scheme.Modules.isFiniteLocallyFree_iff _).2
      (isFiniteLocallyFree_deRhamCohomologySheaf_of_affine_of_algebraRat
        (pullback.snd f (𝒰.f j)) hArt q))

end Global

end Stacks.DeRhamSmooth

end
