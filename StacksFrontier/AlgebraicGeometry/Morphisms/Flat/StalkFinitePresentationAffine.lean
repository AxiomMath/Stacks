module

public import StacksFrontier.Algebra.Module.RingEquivTransport
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.AffineFlatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.StalkFinitePresentation
public import StacksFrontier.RingTheory.Flat.FinitePresentationNearFlatPrime

/-!
# Stacks 05I7 read in an affine chart: the algebra form

Stacks 05I7 says that a finite type quasi-coherent module which is flat over the base at a point
of a morphism locally of finite presentation has a finitely presented stalk there. Its geometric
form is `Stacks.Flatness.finitePresentation_stalk_of_isFlatOverAt`. This file translates it into
the algebra statement that the affine content of Stacks 05IK consumes, namely
`Stacks.Flatness.FinitePresentationLocalizedModuleAtPrimeOfFlat`: for a ring map `R → S` of finite
presentation, a finite `S`-module `M` and a prime `q` of `S` at which `M` is flat over `R`, the
localization `M_q` is a finitely presented `S_q`-module.

The translation is the expected dictionary. The morphism is `Spec` of `algebraMap R S`, which is
locally of finite presentation because the ring map is (`AlgebraicGeometry.HasRingHomProperty`);
the module is `M^~`, which is quasi-coherent and of finite type because `M` is finite
(`AlgebraicGeometry.tilde_isFiniteType_iff`); and flatness over the base at `q` is flatness of
`M_q` over `R` (`AlgebraicGeometry.isFlatOverAt_spec_tilde_iff_flat_localizedModule`). What the
geometric statement returns is finite presentation of the *stalk* of `M^~` over the *stalk* of the
structure sheaf, and both stalks are localizations — of `M` and of `S` at `q` — so
`Module.FinitePresentation.of_isLocalizedModule_of_isLocalization` turns that into the statement
about `LocalizedModule.AtPrime` over `Localization.AtPrime`. That last step is
`AlgebraicGeometry.finitePresentation_localizedModule_of_finitePresentation_stalk_tilde`, the
converse of the computation inside `Stacks.StalkFiniteType.finitePresentation_stalk`.

## Main results

* `AlgebraicGeometry.finitePresentation_localizedModule_of_finitePresentation_stalk_tilde`:
  finite presentation of the stalk of `N^~` over the local ring of `Spec R` gives finite
  presentation of `N_x` over `R_x`.
* `Stacks.Flatness.finitePresentation_localizedModule_atPrime_of_flat`: **the algebra form of
  Stacks 05I7**, for `R`, `S` and `M` in one universe.
* `Stacks.Flatness.finitePresentation_isLocalizedModule_of_flat`: the same with the localization
  of the ring and of the module given as arbitrary models, in arbitrary universes.
* `Stacks.Flatness.existsAwayFlatFinitePresentationOfFlatAtPrime`: the keystone of
  Stacks 38.8, outright.
* `Stacks.Flatness.finitePresentationLocalizedModuleAtPrimeOfFlat`: **the proposition
  `Stacks.Flatness.FinitePresentationLocalizedModuleAtPrimeOfFlat` itself**, at three independent
  universes, which is the one hypothesis of
  `Stacks.Flatness.existsAwayFlatFinitePresentationOfFlatAtPrime_of_finitePresentation_atPrime`.

## Implementation notes

**Universes.** The geometric route is universe-monomorphic: `Spec` of a ring in `Type u` is a
`Scheme.{u}`, `tilde` wants a module in `Type u` over it, and
`Stacks.Flatness.finitePresentation_stalk_of_isFlatOverAt` is stated for `X S : Scheme.{u}`. So
`Stacks.Flatness.finitePresentation_localizedModule_atPrime_of_flat` puts `R`, `S` and `M` in one
universe. The three universes of the `def` are recovered afterwards by lifting the data to
`Type (max u v w)` with `ULift` and reading the conclusion back: because
`Stacks.Flatness.finitePresentation_isLocalizedModule_of_flat` lets the localization be *any*
model in *any* universe, the models chosen upstairs are the original `Localization.AtPrime q` and
`LocalizedModule.AtPrime q M`, so the conclusion needs no transport at all. Only the hypotheses
are transported, by `StacksFrontier/Algebra/Module/RingEquivTransport.lean`.

**Instances on the stalk.** The `𝒪_{Spec R,x}`-module structure on the stalk of `M^~` is not found
by instance search at the spelling `(tilde N).presheaf.stalk x` with `x : PrimeSpectrum R`, so it
is supplied by name, exactly as `Stacks.StalkFiniteType.finitePresentation_stalk_tilde` supplies
it; the hypothesis of
`AlgebraicGeometry.finitePresentation_localizedModule_of_finitePresentation_stalk_tilde` is stated
against that named instance and the geometric statement's anonymous one is accepted for it by
`exact`, the two being definitionally equal.

## References

* [Stacks Project, Tag 05I7](https://stacks.math.columbia.edu/tag/05I7)
* [Stacks Project, Tag 05IK](https://stacks.math.columbia.edu/tag/05IK)
* [Stacks Project, Tag 01PC](https://stacks.math.columbia.edu/tag/01PC)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u u₁ u₂ v w

namespace AlgebraicGeometry

/-- The localization of `N` at a prime `x` is a finitely presented module over the localization of
`R` there as soon as the stalk of `N^~` at `x` is a finitely presented module over the stalk of
the structure sheaf.

Both stalks are localizations — `AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk` for the
ring and `AlgebraicGeometry.tilde.isLocalizedModule_toStalk` for the module — so this is
`Module.FinitePresentation.of_isLocalizedModule_of_isLocalization`. It is the converse of the
computation performed inside `Stacks.StalkFiniteType.finitePresentation_stalk`. -/
public theorem finitePresentation_localizedModule_of_finitePresentation_stalk_tilde
    {R : CommRingCat.{u}} (N : ModuleCat.{u} R) (x : PrimeSpectrum (R : Type u))
    (h : letI : Module (ToType ((Spec R).presheaf.stalk x))
          (ToType ((tilde N).presheaf.stalk x)) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := (Spec R).presheaf) (tilde N).val x
      Module.FinitePresentation (ToType ((Spec R).presheaf.stalk x))
        (ToType ((tilde N).presheaf.stalk x))) :
    Module.FinitePresentation (Localization.AtPrime x.asIdeal)
      (LocalizedModule.AtPrime x.asIdeal (N : Type u)) := by
  let : Module (ToType ((Spec R).presheaf.stalk x)) (ToType ((tilde N).presheaf.stalk x)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := (Spec R).presheaf) (tilde N).val x
  have hfp : Module.FinitePresentation (ToType ((Spec R).presheaf.stalk x))
      (ToType ((tilde N).presheaf.stalk x)) := h
  have : x.asIdeal.IsPrime := x.isPrime
  let : Algebra (R : Type u) (ToType ((Spec R).presheaf.stalk x)) :=
    StructureSheaf.stalkAlgebra R x
  have : IsLocalization.AtPrime (ToType ((Spec R).presheaf.stalk x)) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R x
  let : Module (R : Type u) (ToType ((tilde N).presheaf.stalk x)) :=
    AlgebraicGeometry.tilde.instModuleCarrierCarrierStalkAbPresheaf N x
  have : IsScalarTower (R : Type u) (ToType ((Spec R).presheaf.stalk x))
      (ToType ((tilde N).presheaf.stalk x)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact Module.FinitePresentation.of_isLocalizedModule_of_isLocalization
    (A₁ := ToType ((Spec R).presheaf.stalk x)) x.asIdeal.primeCompl (tilde.toStalk N x).hom
    (LocalizedModule.mkLinearMap x.asIdeal.primeCompl (N : Type u))

end AlgebraicGeometry

namespace Stacks.Flatness

/-- **The algebra form of Stacks Project, Tag 05I7**, for `R`, `S`
and `M` in a single universe. Let `R → S` be of finite presentation, let `M` be a finite
`S`-module and let `q` be a prime of `S` at which `M` is flat over `R`. Then `M_q` is a finitely
presented `S_q`-module.

The proof reads the data on `Spec S` over `Spec R`: the module becomes `M^~`, which is
quasi-coherent and of finite type, flatness over the base at `q` is the hypothesis by
`AlgebraicGeometry.isFlatOverAt_spec_tilde_iff_flat_localizedModule`, and the geometric statement
`Stacks.Flatness.finitePresentation_stalk_of_isFlatOverAt` gives finite presentation of the stalk,
which is the conclusion by
`AlgebraicGeometry.finitePresentation_localizedModule_of_finitePresentation_stalk_tilde`. -/
public theorem finitePresentation_localizedModule_atPrime_of_flat
    (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] (M : Type u) [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] [Module.Finite S M] (q : PrimeSpectrum S)
    (hq : Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)) :
    Module.FinitePresentation (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal M) := by
  let φ : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
  let Mc : ModuleCat.{u} (CommRingCat.of S) := ModuleCat.of S M
  have hφ : φ.hom = algebraMap R S := rfl
  have : LocallyOfFinitePresentation (Spec.map φ) := by
    refine (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr ?_
    rw [hφ]
    exact RingHom.finitePresentation_algebraMap.mpr ‹_›
  have : (tilde Mc).IsFiniteType := (tilde_isFiniteType_iff Mc).2 inferInstance
  exact finitePresentation_localizedModule_of_finitePresentation_stalk_tilde Mc q
    (finitePresentation_stalk_of_isFlatOverAt (Spec.map φ) (tilde Mc) q
      ((isFlatOverAt_spec_tilde_iff_flat_localizedModule φ Mc hφ q).mpr hq))

/-- **The algebra form of Stacks Project, Tag 05I7 at an arbitrary model of the localization.**
With `R`, `S` and `M` in one universe, let `A` be any localization of `S` at `q` and let
`f : M →ₗ[S] N` exhibit any localization of `M` at `q`; both may live in their own universes. If
`N` is flat over `R` then `N` is a finitely presented `A`-module.

The hypothesis is transported to the canonical model by
`IsLocalizedModule.linearEquiv` and the conclusion back by
`Module.FinitePresentation.of_isLocalizedModule_of_isLocalization`. Keeping the model free is what
makes the change of universe in
`Stacks.Flatness.finitePresentationLocalizedModuleAtPrimeOfFlat` cost nothing on the side of the
conclusion. -/
public theorem finitePresentation_isLocalizedModule_of_flat
    (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] (M : Type u) [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] [Module.Finite S M] (q : PrimeSpectrum S)
    {A : Type u₁} [CommRing A] [Algebra S A] [IsLocalization.AtPrime A q.asIdeal]
    {N : Type u₂} [AddCommGroup N] [Module S N] [Module A N] [IsScalarTower S A N] [Module R N]
    [IsScalarTower R S N] (f : M →ₗ[S] N) [IsLocalizedModule q.asIdeal.primeCompl f]
    (hq : Module.Flat R N) : Module.FinitePresentation A N := by
  have hcan : Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) :=
    Module.Flat.of_linearEquiv
      ((IsLocalizedModule.linearEquiv q.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) f).restrictScalars R)
  have := finitePresentation_localizedModule_atPrime_of_flat R S M q hcan
  exact Module.FinitePresentation.of_isLocalizedModule_of_isLocalization
    (A₁ := Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) f

attribute [local instance] ULift.algebra' in
/-- For every ring map `R → S` of finite presentation, every finite `S`-module `M` and every prime
`q` of `S` at which `M` is flat over `R`, the localization `M_q` is a finitely presented
`S_q`-module, with `R`, `S` and `M` in three independent universes. -/
public theorem finitePresentationLocalizedModuleAtPrimeOfFlat :
    FinitePresentationLocalizedModuleAtPrimeOfFlat.{u, v, w} := by
  intro R _ S _ _ _ M _ _ _ _ _ q hq
  let eR : ULift.{max v w} R ≃+* R := ULift.ringEquiv
  let eS : ULift.{max u w} S ≃+* S := ULift.ringEquiv
  let eM : ULift.{max u v} M ≃+ M := (ULift.moduleEquiv (R := S) (M := M)).toAddEquiv
  have hSM : ∀ (s' : ULift.{max u w} S) (m' : ULift.{max u v} M),
      eM (s' • m') = eS s' • eM m' := fun _ _ => rfl
  have halg : ∀ r' : ULift.{max v w} R,
      algebraMap (ULift.{max v w} R) (ULift.{max u w} S) r'
        = eS.symm (algebraMap R S (eR r')) := fun _ => rfl
  have : Algebra.FinitePresentation (ULift.{max v w} R) (ULift.{max u w} S) :=
    Algebra.FinitePresentation.of_ringEquiv eR.symm eS.symm fun r => by
      rw [halg, eR.apply_symm_apply]
  have : Module.Finite (ULift.{max u w} S) (ULift.{max u v} M) :=
    Module.Finite.of_semilinearEquiv eS eM hSM
  have : IsScalarTower (ULift.{max v w} R) (ULift.{max u w} S) (ULift.{max u v} M) :=
    IsScalarTower.of_algebraMap_smul fun r' m' =>
      congrArg ULift.up (IsScalarTower.algebraMap_smul S (eR r') (eM m'))
  let q' : PrimeSpectrum (ULift.{max u w} S) := PrimeSpectrum.comap eS.toRingHom q
  have hp : ∀ s' : ULift.{max u w} S,
      s' ∈ q'.asIdeal.primeCompl ↔ eS s' ∈ q.asIdeal.primeCompl := fun _ => Iff.rfl
  -- the localization of the ring, kept in its original universe
  have : IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) q'.asIdeal :=
    (isLocalizedModule_iff_isLocalization' q'.asIdeal.primeCompl _).mp <|
      IsLocalizedModule.of_ringEquiv eS hp
        (Algebra.linearMap S (Localization.AtPrime q.asIdeal))
        (Algebra.linearMap (ULift.{max u w} S) (Localization.AtPrime q.asIdeal))
        eS.toAddEquiv (AddEquiv.refl _) (fun _ _ => map_mul eS _ _) (fun _ _ => rfl) fun _ => rfl
  -- the localization of the module, kept in its original universe
  have : IsScalarTower (ULift.{max u w} S) (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal M) :=
    IsScalarTower.of_algebraMap_smul fun s' n =>
      IsScalarTower.algebraMap_smul (Localization.AtPrime q.asIdeal) (eS s') n
  let f' : ULift.{max u v} M →ₗ[ULift.{max u w} S] LocalizedModule.AtPrime q.asIdeal M :=
    { toFun := fun m' => LocalizedModule.mkLinearMap q.asIdeal.primeCompl M (eM m')
      map_add' := fun m₁ m₂ => by simp
      map_smul' := fun s' m' => by
        simp only [RingHom.id_apply, hSM]
        exact (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M).map_smul (eS s') (eM m') }
  have : IsLocalizedModule q'.asIdeal.primeCompl f' :=
    IsLocalizedModule.of_ringEquiv eS hp (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) f'
      eM (AddEquiv.refl _) hSM (fun _ _ => rfl) fun _ => rfl
  have : IsScalarTower (ULift.{max v w} R) (ULift.{max u w} S)
      (LocalizedModule.AtPrime q.asIdeal M) :=
    IsScalarTower.of_algebraMap_smul fun r' n => IsScalarTower.algebraMap_smul S (eR r') n
  exact finitePresentation_isLocalizedModule_of_flat (ULift.{max v w} R)
    (ULift.{max u w} S) (ULift.{max u v} M) q' f'
    (Module.Flat.of_semilinearEquiv eR (AddEquiv.refl _) fun _ _ => rfl)

/-- **The affine content of Stacks Project, Tag 05IK.** Composing
`Stacks.Flatness.finitePresentationLocalizedModuleAtPrimeOfFlat` with
`Stacks.Flatness.existsAwayFlatFinitePresentationOfFlatAtPrime_of_finitePresentation_atPrime`
discharges both inputs of that theorem, so
`Stacks.Flatness.ExistsAwayFlatFinitePresentationOfFlatAtPrime` — the keystone of Stacks 38.8 —
holds at three independent universes. At `u = v = w` this is the instantiation `.{u, u, u}` that
most consumers of the keystone use. -/
public theorem existsAwayFlatFinitePresentationOfFlatAtPrime :
    ExistsAwayFlatFinitePresentationOfFlatAtPrime.{u, v, w} :=
  existsAwayFlatFinitePresentationOfFlatAtPrime_of_finitePresentation_atPrime
    finitePresentationLocalizedModuleAtPrimeOfFlat

end Stacks.Flatness

end
