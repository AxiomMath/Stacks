module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.SquareZeroExtensionDerivedHom
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.TwistedInverseImageRestrictionQcqs
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.CoherentCohomologySheaves
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeBoundedComplex
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardAnyModel
public import StacksFrontier.Homology.DerivedCategory.IsZero

/-!
# The twisted inverse image does not commute with restriction to opens

Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated schemes, `V ⊆ Y` a
quasi-compact open with inverse image `U`, and `a`, `a'` the right adjoints of `Rf_*` and
`R(f|_U)_*`. [Stacks, Tag 0A9L] is a canonical map `(j')^*(a(K)) ⟶ a'(K|_V)`
(`Stacks.Duality.OpenImmersion.qcqsTwistedInverseImageRestrictionMap`), and [Stacks, Tag 0A9M]
shows that it is not an isomorphism in general, even for a finite morphism of Noetherian schemes
and an input with coherent cohomology sheaves.

The example is `f : X = Spec B ⟶ Y = Spec A` with `A = k[x][ε]`, `ε² = 0`, `B = A/(ε) = k[x]`,
`V = D(x)` and `K = ⨁ₙ Mₙ[n]` with `Mₙ = A/(ε, xⁿ)`. Every cohomology class of `K` is annihilated
by a power of `x`, so `K|_V = 0` and `a'(K|_V) = 0`. On the other hand `a(K)` is the
sheafification of `RHom(B, K)` ([Stacks, Tag 0A9F]), and `H⁰(RHom(B, K)) = ∏ₙ Mₙ` has an element
annihilated by no power of `x`, so `a(K)|_U ≠ 0`. The module-theoretic half of this is
`StacksFrontier/Algebra/Homology/DerivedCategory/Ext/SquareZeroExtensionDerivedHom.lean`; this file
supplies the dictionary between vanishing on an open of `Spec R` and power torsion, and the
geometric conclusion.

## Main results

* `Stacks.Duality.OpenImmersion.isZero_derivedRestrict_derivedTilde_of_le_basicOpen` and
  `Stacks.Duality.OpenImmersion.exists_pow_smul_eq_zero_of_isZero_derivedRestrict_derivedTilde`:
  `E^~` restricts to zero on `D(r)` exactly when the cohomology of `E` is `r`-power torsion.
* `Stacks.SquareZeroExt.isFinite_specProj` and
  `Stacks.SquareZeroExt.isCoherent_homology_coefficientSumTilde`: `f` is finite and `K` lies in
  `D_Coh(𝒪_Y)`.
* `Stacks.SquareZeroExt.not_isIso_qcqsTwistedInverseImageRestrictionMap_app`: the map of
  [Stacks, Tag 0A9L] is not an isomorphism at `K`, over every field `k`.
* `Stacks.Duality.OpenImmersion.exists_not_isIso_qcqsTwistedInverseImageRestrictionMap_app`:
  **[Stacks, Tag 0A9M]**.

## Implementation notes

The source reads the example as `(j')^*(a(K)) ≠ 0` and `a'(j^*K) = 0`, so no isomorphism can
exist between them; that is the proof here, and it does not go through the criterion
`Stacks.Duality.OpenImmersion.isIso_qcqsTwistedInverseImageRestrictionMap_app_iff`. The right
adjoint `a` is the one of [Stacks, Tag 0A9E] chosen by the 0A9L map; it is identified with
`RHom(B, -)` by
`AlgebraicGeometry.derivedTilde_comp_rightAdjoint_derivedQuasicoherentPushforwardIsoDerivedHom`,
which holds for an arbitrary right adjoint.

## References

* [Stacks Project, Tag 0A9M](https://stacks.math.columbia.edu/tag/0A9M)
* [Stacks Project, Tag 0A9L](https://stacks.math.columbia.edu/tag/0A9L)
* [Stacks Project, Tag 0A9F](https://stacks.math.columbia.edu/tag/0A9F)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Duality.OpenImmersion

/-! ### Sheafified modules restricted to an open of `Spec R` -/

section Tilde

variable {R : CommRingCat.{u}}

/-- **A module which is `r`-power torsion sheafifies to zero on any open inside `D(r)`.** The
stalk of `M^~` at a point `x ∈ D(r)` is the localization `M_x`, and `r` is invertible there. -/
theorem isZero_restrict_tilde_of_le_basicOpen (W : (Spec R).Opens) (r : R)
    (hW : W ≤ PrimeSpectrum.basicOpen r) (M : ModuleCat.{u} R)
    (hM : ∀ m : M, ∃ n : ℕ, r ^ n • m = 0) :
    IsZero ((Scheme.Modules.restrictFunctor W.ι).obj (tilde M)) := by
  refine (Scheme.Modules.isZero_restrict_iff_forall_isZero_stalk W (tilde M)).mpr fun x hx => ?_
  let y : PrimeSpectrum.Top R := x
  let g := (tilde.toStalk M y).hom
  have hg (m : M) : g m = 0 := by
    obtain ⟨n, hn⟩ := hM m
    exact (IsLocalizedModule.eq_zero_iff y.asIdeal.primeCompl g).mpr
      ⟨⟨r ^ n, pow_mem (show r ∈ y.asIdeal.primeCompl from hW hx) n⟩, hn⟩
  refine AddCommGrpCat.isZero_iff_subsingleton.mpr ⟨fun a b => ?_⟩
  have hz (a : (tilde M).presheaf.stalk y) : a = 0 := by
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective y.asIdeal.primeCompl g a
    exact (IsLocalizedModule.mk'_eq_zero (f := g) s).mpr (hg m)
  rw [hz a, hz b]

/-- **A module whose sheafification vanishes on an open containing `D(r)` is `r`-power torsion.**
The sections of `M^~` over `D(r)` are the localization `M[1/r]`, and they vanish. -/
theorem exists_pow_smul_eq_zero_of_isZero_restrict_tilde (W : (Spec R).Opens) (r : R)
    (hW : PrimeSpectrum.basicOpen r ≤ W) (M : ModuleCat.{u} R)
    (hM : IsZero ((Scheme.Modules.restrictFunctor W.ι).obj (tilde M))) (m : M) :
    ∃ n : ℕ, r ^ n • m = 0 := by
  let D : (Spec R).Opens := PrimeSpectrum.basicOpen r
  have hV : W.ι ''ᵁ (W.ι ⁻¹ᵁ D) = D := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hW
  have : (Scheme.Modules.toPresheaf W.toScheme).PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hz : IsZero ((Scheme.Modules.restrictFunctor W.ι).obj (tilde M)).presheaf :=
    (Scheme.Modules.toPresheaf W.toScheme).map_isZero hM
  have ht := ((evaluation (TopologicalSpace.Opens W.toScheme)ᵒᵖ AddCommGrpCat).obj
    (op (W.ι ⁻¹ᵁ D))).map_isZero hz
  have h3 : Subsingleton ((tilde M).presheaf.obj (op D)) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp (ht.of_iso ((tilde M).restrictAppIso W.ι _ ≪≫
      (tilde M).presheaf.mapIso (eqToIso hV.symm).op).symm)
  have h4 : (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom m = 0 := @Subsingleton.elim _ h3 _ _
  obtain ⟨⟨s, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers r) _).mp h4
  exact ⟨n, hn⟩

/-- The cohomology sheaves of `j^*(E^~)`, for `j : W ⟶ Spec R` the inclusion of an open, are the
restrictions of the sheaves associated to the cohomology modules of `E`: restriction is exact and
so is `(-)^~`. -/
def homologyDerivedRestrictDerivedTildeIso (W : (Spec R).Opens)
    (E : DerivedCategory (ModuleCat.{u} R)) (q : ℤ) :
    (DerivedCategory.homologyFunctor W.toScheme.Modules q).obj
        ((derivedRestrict W.ι).obj ((derivedTilde R).obj E).obj) ≅
      (Scheme.Modules.restrictFunctor W.ι).obj
        (tilde ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj E)) :=
  ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategoryHomologyIso q).app _ ≪≫
    (Scheme.Modules.restrictFunctor W.ι).mapIso (homologyDerivedTildeObjIso R E q)

/-- **If every cohomology class of `E` is `r`-power torsion, then `E^~` restricts to zero on every
open inside `D(r)`.** -/
theorem isZero_derivedRestrict_derivedTilde_of_le_basicOpen (W : (Spec R).Opens) (r : R)
    (hW : W ≤ PrimeSpectrum.basicOpen r) (E : DerivedCategory (ModuleCat.{u} R))
    (hE : ∀ (q : ℤ) (m : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj E),
      ∃ n : ℕ, r ^ n • m = 0) :
    IsZero ((derivedRestrict W.ι).obj ((derivedTilde R).obj E).obj) :=
  (DerivedCategory.isZero_iff_forall_isZero_homology _).mpr fun q =>
    (isZero_restrict_tilde_of_le_basicOpen W r hW _ (hE q)).of_iso
      (homologyDerivedRestrictDerivedTildeIso W E q)

/-- **If `E^~` restricts to zero on an open containing `D(r)`, then every cohomology class of `E`
is `r`-power torsion.** -/
theorem exists_pow_smul_eq_zero_of_isZero_derivedRestrict_derivedTilde (W : (Spec R).Opens)
    (r : R) (hW : PrimeSpectrum.basicOpen r ≤ W) (E : DerivedCategory (ModuleCat.{u} R))
    (h : IsZero ((derivedRestrict W.ι).obj ((derivedTilde R).obj E).obj)) (q : ℤ)
    (m : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj E) :
    ∃ n : ℕ, r ^ n • m = 0 :=
  exists_pow_smul_eq_zero_of_isZero_restrict_tilde W r hW _
    (((DerivedCategory.isZero_iff_forall_isZero_homology _).mp h q).of_iso
      (homologyDerivedRestrictDerivedTildeIso W E q).symm) m

end Tilde

end Stacks.Duality.OpenImmersion

/-! ### The example -/

namespace Stacks.SquareZeroExt

open Stacks.Duality Stacks.Duality.OpenImmersion

variable (k : Type u) [Field k]

/-- The projection `A = k[x][ε] ⟶ B = k[x]`, as a morphism of commutative rings. -/
abbrev projHom : CommRingCat.of (sourceRing k) ⟶ CommRingCat.of (Polynomial k) :=
  CommRingCat.ofHom (proj (Polynomial k))

/-- The closed immersion `Spec k[x] ⟶ Spec k[x][ε]` of [Stacks, Tag 0A9M]. -/
abbrev specProj : Spec (CommRingCat.of (Polynomial k)) ⟶ Spec (CommRingCat.of (sourceRing k)) :=
  Spec.map (projHom k)

/-- The principal open `V = D(x)` of `Spec k[x][ε]`. -/
abbrev basicOpenX : (Spec (CommRingCat.of (sourceRing k))).Opens :=
  PrimeSpectrum.basicOpen (TrivSqZeroExt.inl (Polynomial.X : Polynomial k) : sourceRing k)

/-- The principal open `D(x)` of `Spec k[x][ε]` is quasi-compact. -/
instance compactSpace_basicOpenX : CompactSpace (basicOpenX k) :=
  isCompact_iff_compactSpace.mp (PrimeSpectrum.isCompact_basicOpen _)

/-- **The object `K = ⨁ₙ Mₙ[n]` of [Stacks, Tag 0A9M]** in `D_QCoh(𝒪_{Spec A})`, the derived
sheafification of `Stacks.SquareZeroExt.coefficientSum`. -/
abbrev coefficientSumTilde : quasiCoherentDerivedCategory (Spec (CommRingCat.of (sourceRing k))) :=
  (derivedTilde (CommRingCat.of (sourceRing k))).obj (coefficientSum k)

/-- **`K` restricts to zero on `D(x)`**: every cohomology class of `K` is annihilated by a power
of `x`. -/
theorem isZero_restrict_coefficientSumTilde :
    IsZero ((quasiCoherentDerivedRestrict (basicOpenX k).ι
      (isQuasicoherent_homology_derivedRestrict _)).obj (coefficientSumTilde k)) :=
  IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _
    (isZero_derivedRestrict_derivedTilde_of_le_basicOpen _ _ le_rfl _
      (exists_xpow_smul_homology_coefficientSum k))

/-- **The twisted inverse image of `K` does not restrict to zero on `f⁻¹(D(x))`**, for any right
adjoint `a` of `Rf_*`. By [Stacks, Tag 0A9F], `a(K)` is the sheafification of `RHom(B, K)`, and
`H⁰(RHom(B, K)) = ∏ₙ Mₙ` contains an element annihilated by no power of `x`. -/
theorem not_isZero_restrict_rightAdjoint_coefficientSumTilde
    {a : quasiCoherentDerivedCategory (Spec (CommRingCat.of (sourceRing k))) ⥤
      quasiCoherentDerivedCategory (Spec (CommRingCat.of (Polynomial k)))}
    (adj : quasiCoherentDerivedPushforward (specProj k)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ⊣ a) :
    ¬ IsZero ((quasiCoherentDerivedRestrict (specProj k ⁻¹ᵁ basicOpenX k).ι
      (isQuasicoherent_homology_derivedRestrict _)).obj (a.obj (coefficientSumTilde k))) := by
  intro hz
  have adj' : derivedQuasicoherentPushforward (Spec.map (projHom k)) ⊣ a := adj
  obtain ⟨e⟩ := derivedTilde_comp_rightAdjoint_derivedQuasicoherentPushforwardIsoDerivedHom
    (projHom k) adj'
  have hzero : IsZero ((derivedRestrict (specProj k ⁻¹ᵁ basicOpenX k).ι).obj
      ((derivedTilde (CommRingCat.of (Polynomial k))).obj
        ((Dualizing.AnyModel.derivedHom.{u, u, u, u, u} (proj (Polynomial k))).obj
          (coefficientSum k))).obj) :=
    ((ObjectProperty.ι _).map_isZero hz).of_iso
      ((derivedRestrict _).mapIso ((ObjectProperty.ι _).mapIso (e.app (coefficientSum k)))).symm
  obtain ⟨m, hm⟩ := exists_forall_xpow_smul_ne_zero_derivedHom k
  have hle : (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) :
      (Spec (CommRingCat.of (Polynomial k))).Opens) ≤ specProj k ⁻¹ᵁ basicOpenX k := by
    rw [SpecMap_preimage_basicOpen]
    exact le_rfl
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isZero_derivedRestrict_derivedTilde _
    (Polynomial.X : Polynomial k) hle _ hzero 0 m
  exact hm n hn

/-- `Spec k[x] ⟶ Spec k[x][ε]` is a finite morphism: `k[x][ε] ⟶ k[x]` is surjective. -/
theorem isFinite_specProj : IsFinite (specProj k) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.Finite.of_surjective _ fun b =>
    ⟨TrivSqZeroExt.inl b, TrivSqZeroExt.fst_inl (Polynomial k) b⟩)

/-- **`K = ⨁ₙ Mₙ[n]` lies in `D_Coh(𝒪_{Spec A})`**: its cohomology modules are finite over the
Noetherian ring `A = k[x][ε]`. -/
theorem isCoherent_homology_coefficientSumTilde (i : ℤ) :
    ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of (sourceRing k))).Modules i).obj
      (coefficientSumTilde k).obj).IsCoherent :=
  (isCoherent_homologyDerivedTilde_iff (CommRingCat.of (sourceRing k)) inferInstance
    (coefficientSum k) i).mpr (finite_homology_coefficientSum k i)

/-- **The map of [Stacks, Tag 0A9L] is not an isomorphism at `K`**, for
`f : Spec k[x] ⟶ Spec k[x][ε]` and `V = D(x)`. Were it one, `(j')^*(a(K))` would be isomorphic
to `a'(j^*K)`, which is zero because `j^*K` is
(`Stacks.SquareZeroExt.isZero_restrict_coefficientSumTilde`); but `(j')^*(a(K))` is not zero
(`Stacks.SquareZeroExt.not_isZero_restrict_rightAdjoint_coefficientSumTilde`). -/
theorem not_isIso_qcqsTwistedInverseImageRestrictionMap_app :
    ¬ IsIso ((qcqsTwistedInverseImageRestrictionMap (specProj k) (basicOpenX k)).app
      (coefficientSumTilde k)) := by
  intro h
  have := (twistedInverseImageAdjunction (specProj k ∣_ basicOpenX k)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).isRightAdjoint
  exact not_isZero_restrict_rightAdjoint_coefficientSumTilde k
    (twistedInverseImageAdjunction (specProj k)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (((twistedInverseImage (specProj k ∣_ basicOpenX k)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map_isZero
        (isZero_restrict_coefficientSumTilde k)).of_iso
      (asIso ((qcqsTwistedInverseImageRestrictionMap (specProj k) (basicOpenX k)).app
        (coefficientSumTilde k))))

end Stacks.SquareZeroExt

namespace Stacks.Duality.OpenImmersion

open Stacks.SquareZeroExt

/-- **Stacks Project, Tag 0A9M.** There is a finite morphism `f : X ⟶ Y` of Noetherian schemes, a
quasi-compact open `V ⊆ Y` and an object `K` of `D_QCoh(𝒪_Y)` with coherent cohomology sheaves,
such that the map `(j')^*(a(K)) ⟶ a'(K|_V)` of [Stacks, Tag 0A9L]
(`Stacks.Duality.OpenImmersion.qcqsTwistedInverseImageRestrictionMap`) is not an isomorphism.

The witnesses are those of the source, over the field `k = ℚ`: `f : Spec k[x] ⟶ Spec k[x][ε]`
(`Stacks.SquareZeroExt.specProj`), `V = D(x)` (`Stacks.SquareZeroExt.basicOpenX`) and
`K = ⨁ₙ Mₙ[n]` with `Mₙ = k[x][ε]/(ε, xⁿ)` (`Stacks.SquareZeroExt.coefficientSumTilde`). The
same holds over every field, which is
`Stacks.SquareZeroExt.not_isIso_qcqsTwistedInverseImageRestrictionMap_app`. -/
@[stacks 0A9M]
theorem exists_not_isIso_qcqsTwistedInverseImageRestrictionMap_app :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y) (_ : IsFinite f) (_ : IsNoetherian X) (_ : IsNoetherian Y)
      (V : Y.Opens) (_ : CompactSpace V) (K : quasiCoherentDerivedCategory Y),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor Y.Modules i).obj K.obj).IsCoherent) ∧
        ¬ IsIso ((qcqsTwistedInverseImageRestrictionMap f V).app K) :=
  ⟨_, _, specProj (ULift.{u} ℚ), isFinite_specProj _, inferInstance, inferInstance,
    basicOpenX _, inferInstance, coefficientSumTilde _,
    isCoherent_homology_coefficientSumTilde _,
    not_isIso_qcqsTwistedInverseImageRestrictionMap_app _⟩

end Stacks.Duality.OpenImmersion

end
