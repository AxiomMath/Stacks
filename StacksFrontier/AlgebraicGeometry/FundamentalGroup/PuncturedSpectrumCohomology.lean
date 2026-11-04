module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Etale.StructureSheafDerivation
public import StacksFrontier.AlgebraicGeometry.Etale.TopologicalProperties.RelativeFrobenius
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffinePositiveDegree
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FrobeniusAction.Kunz
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.LocallyNoetherian
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.CompleteLocalRing.Regular
public import StacksFrontier.RingTheory.Dualizing.FrobeniusStableTorsion
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldHull
public import StacksFrontier.RingTheory.LocalCohomology.Deps.QuasicoherentAffineVanishing
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.ComplementSheafCohomology
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingFlatIsomorphism
public import StacksFrontier.RingTheory.MvPowerSeries.LeibnizTorsionModule
public import StacksFrontier.RingTheory.MvPowerSeries.Noetherian
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Structure-sheaf cohomology of an étale scheme affine over a punctured spectrum

Let `A` be a regular local ring containing a field, let `U = Spec A ∖ {𝔪}` be the punctured
spectrum, and let `f : V ⟶ Spec A` be étale and quasi-compact and factor as `f = g ≫ U.ι` with
`g : V ⟶ U` affine. Then for every `i > 0` the `A`-module `H ⁱ(V, 𝒪_V)` is a direct sum of
copies of an injective hull of the residue field of `A`.

The factorization through `U` records both hypotheses of the source at once: that the closed
point of `Spec A` is not in the image of `f`, and that the induced morphism to the punctured
spectrum is affine.

## Main definitions

* `Stacks.EtalePuncturedSpectrum.torsionBaseChangeUnitIso` — an `𝔪`-power-torsion module is
  recovered from its flat base change along a map which is an isomorphism modulo `𝔪`.

## Main results

* `Stacks.EtalePuncturedSpectrum.nonempty_structureSheafCohomology_extendScalars` — **flat base
  change for structure-sheaf cohomology over affine bases**: for a cartesian square over
  `Spec φ` with `φ` flat and the structure morphism separated and quasi-compact,
  `B ⊗_A H ⁿ(V, 𝒪_V) ≅ H ⁿ(W, 𝒪_W)` in every degree.
* `Stacks.EtalePuncturedSpectrum.isIPowerTorsion_structureSheafCohomology` — positive-degree
  structure-sheaf cohomology of a scheme quasi-compact over `Spec A` and affine over the
  punctured spectrum is `𝔪`-power torsion.
* `Stacks.EtalePuncturedSpectrum.nonempty_frobenius_structureSheafCohomology_iso` — in
  characteristic `p` that cohomology is its own base change along Frobenius.
* `Stacks.EtalePuncturedSpectrum.exists_directSum_injectiveHull_residueField` —
  **Stacks Project, Tag 0ECB.**

## Implementation notes

The torsion statement is proved by localizing at a finite generating family of `𝔪` rather than
by comparing with local cohomology. For `x ∈ 𝔪` the basic open `D(x)` lies in `U`, so the base
change of `V` along `A → A_x` is affine over `Spec A_x`, hence has no positive-degree
structure-sheaf cohomology; flat base change then makes every element of `H ⁿ(V, 𝒪_V)` killed by
a power of `x`, and a power of `𝔪` kills it because `𝔪` is finitely generated.

Everything is at module universe equal to the universe of the scheme. That is where the two
characteristic-specific inputs — the Frobenius-stable torsion decomposition and the
Leibniz-operator decomposition over a power series ring — and the Čech flat base change all
live simultaneously.

## What is not proved

The isomorphism of the main theorem is not identified with any canonical map, and the index set
of the direct sum is not computed: the source asserts only that such a decomposition exists, and
both the index set and the isomorphism come from choices (a basis in the equicharacteristic-zero
dimension-zero case, a maximal independent family of socle elements in characteristic `p`).

## References

* [Stacks Project, Tag 0ECB](https://stacks.math.columbia.edu/tag/0ECB)
* [Stacks Project, Tag 0EC2](https://stacks.math.columbia.edu/tag/0EC2)
* [Stacks Project, Tag 0EC3](https://stacks.math.columbia.edu/tag/0EC3)
* [Stacks Project, Tag 0EC7](https://stacks.math.columbia.edu/tag/0EC7)
* [Stacks Project, Tag 08Z5](https://stacks.math.columbia.edu/tag/08Z5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.LocalCohomology Stacks.EtaleDerivation
open Stacks.AlgebraicGeometry.SectionsBaseChange
open scoped TensorProduct
open Stacks.Frobenius

universe u

namespace Stacks.EtalePuncturedSpectrum

/-! ### Change of rings across the `Γ`–`Spec` units -/

/-- Composing the two legs of a cartesian square with a monomorphism leaves it cartesian. -/
private theorem isPullback_comp_mono {C : Type*} [Category C] {W X Y Z Z' : C} {fst : W ⟶ X}
    {snd : W ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z} (m : Z ⟶ Z') [Mono m] (h : IsPullback fst snd a b) :
    IsPullback fst snd (a ≫ m) (b ≫ m) := by
  have hw : fst ≫ a ≫ m = snd ≫ b ≫ m := by
    rw [← Category.assoc, h.w, Category.assoc]
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw
    (fun s => h.lift s.fst s.snd ((cancel_mono m).1
      (by simpa only [Category.assoc] using s.condition)))
    (fun s => h.lift_fst _ _ _) (fun s => h.lift_snd _ _ _)
    (fun s u h1 h2 => h.hom_ext (by rw [h1, h.lift_fst]) (by rw [h2, h.lift_snd]))⟩⟩

/-- The unit of the `Γ`–`Spec` adjunction, as a ring isomorphism `A ≃+* Γ(Spec A, ⊤)`. -/
private abbrev gammaEquiv (A : Type u) [CommRing A] : A ≃+* Γ(Spec (.of A), ⊤) :=
  (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv

/-- **Extension of scalars commutes with restriction along ring isomorphisms** making a square
of ring maps commute. This is the comparison of the conjugates `adj₁` and `adj₂` of the two
extension–restriction adjunctions. -/
private def extendRestrictConj {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R']
    [CommRing S'] (a : R ≃+* R') (b : S ≃+* S') (φ : R →+* S) (ψ : R' →+* S')
    (h : φ.comp a.symm.toRingHom = b.symm.toRingHom.comp ψ) :
    ModuleCat.restrictScalars a.toRingHom ⋙ ModuleCat.extendScalars φ ≅
      ModuleCat.extendScalars ψ ⋙ ModuleCat.restrictScalars b.toRingHom := by
  let adj₁ := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv a).toAdjunction.comp
    (ModuleCat.extendRestrictScalarsAdj φ)
  let adj₂ := (ModuleCat.extendRestrictScalarsAdj ψ).comp
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv b).toAdjunction
  exact ((conjugateIsoEquiv adj₁ adj₂).symm
    ((ModuleCat.restrictScalarsComp a.symm.toRingHom φ).symm ≪≫
      eqToIso (congrArg ModuleCat.restrictScalars h) ≪≫
      ModuleCat.restrictScalarsComp ψ b.symm.toRingHom)).symm

/-- **Structure-sheaf cohomology over `A` is cohomology over `Γ(Spec A, ⊤)` read over `A`.**
The structure map of a scheme over `A` factors through the global functions on `Spec A`, so the
restriction of scalars defining the `A`-module structure splits into two. -/
private def structureCohomologyRestrictIso {A : Type u} [CommRing A] {V : Scheme.{u}}
    (f : V ⟶ Spec (.of A)) (n : ℕ) :
    structureSheafCohomology f n ≅
      (ModuleCat.restrictScalars (gammaEquiv A).toRingHom).obj
        ((baseRestrictScalars f).obj
          (((_root_.SheafOfModules.evaluation.{u} V.ringCatSheaf
              (op (⊤ : V.Opens))).rightDerived n).obj
            (SheafOfModules.unit V.ringCatSheaf))) :=
  (ModuleCat.restrictScalarsComp (gammaEquiv A).toRingHom
    (f.appLE ⊤ ⊤ (le_preimage_top f ⊤)).hom).app _

/-! ### Flat base change for structure-sheaf cohomology -/

/-- **Flat base change for structure-sheaf cohomology over affine bases.** For a cartesian
square with horizontal map `Spec φ` for a flat ring map `φ : A →+* B`, and structure morphism
`f : V ⟶ Spec A` separated and quasi-compact, `B ⊗_A H ⁿ(V, 𝒪_V) ≅ H ⁿ(W, 𝒪_W)` as `B`-modules
in every degree.

The isomorphism is not identified with the canonical base change map. -/
theorem nonempty_structureSheafCohomology_extendScalars
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (hφ : RingHom.Flat φ)
    {V W : Scheme.{u}} (f : V ⟶ Spec (.of A)) [IsSeparated f] [QuasiCompact f]
    (f' : W ⟶ Spec (.of B)) (p : W ⟶ V)
    (hsq : IsPullback p f' f (Spec.map (CommRingCat.ofHom φ))) (n : ℕ) :
    Nonempty ((ModuleCat.extendScalars φ).obj (structureSheafCohomology f n) ≅
      structureSheafCohomology f' n) := by
  have : Flat (Spec.map (CommRingCat.ofHom φ)) := Flat.SpecMap_iff.mpr hφ
  have hqc : (SheafOfModules.unit V.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit V
  obtain ⟨e⟩ := nonempty_cohomologyBaseChangeIso hsq (SheafOfModules.unit V.ringCatSheaf) n
  have hsq' : φ.comp (gammaEquiv A).symm.toRingHom =
      (gammaEquiv B).symm.toRingHom.comp
        ((Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤
          (le_preimage_top (Spec.map (CommRingCat.ofHom φ)) ⊤)).hom := by
    ext y
    exact congrArg (fun t : CommRingCat.Hom _ _ => t.hom y)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)).symm
  refine ⟨(ModuleCat.extendScalars φ).mapIso (structureCohomologyRestrictIso f n) ≪≫
    (extendRestrictConj (gammaEquiv A) (gammaEquiv B) φ _ hsq').app _ ≪≫
    (ModuleCat.restrictScalars (gammaEquiv B).toRingHom).mapIso (e ≪≫
      (baseRestrictScalars f').mapIso
        (((_root_.SheafOfModules.evaluation.{u} W.ringCatSheaf
          (op (⊤ : W.Opens))).rightDerived n).mapIso
            (Scheme.Modules.pullbackUnitIso p))) ≪≫
    (structureCohomologyRestrictIso f' n).symm⟩

/-! ### Positive-degree cohomology is `𝔪`-power torsion -/

/-- A module every element of which is killed by a power of each member of a finite family is
power torsion for the ideal that family generates. -/
private theorem isIPowerTorsion_of_forall_pow_smul {A : Type u} [CommRing A]
    {M : Type u} [AddCommGroup M] [Module A M] (s : Finset A)
    (h : ∀ q : M, ∀ x ∈ s, ∃ k : ℕ, x ^ k • q = 0) :
    IsIPowerTorsion A M (Ideal.span (s : Set A)) := by
  intro q
  have hle : Ideal.span (s : Set A) ≤
      Ideal.radical (LinearMap.ker (LinearMap.toSpanSingleton A M q)) := by
    rw [Ideal.span_le]
    intro x hx
    obtain ⟨k, hk⟩ := h q x hx
    exact ⟨k, by simpa only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] using hk⟩
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle
    (Submodule.fg_span s.finite_toSet)
  refine ⟨k + 1, Nat.succ_pos _, fun a ha => ?_⟩
  simpa only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] using
    hk (Ideal.pow_le_pow_right (Nat.le_succ k) ha)

/-- A module whose localization away from `x` vanishes is killed elementwise by powers of `x`. -/
private theorem exists_pow_smul_eq_zero_of_isZero {A : Type u} [CommRing A]
    (x : A) (M : ModuleCat.{u} A)
    (h : IsZero ((ModuleCat.extendScalars (algebraMap A (Localization.Away x))).obj M))
    (q : M) : ∃ k : ℕ, x ^ k • q = 0 := by
  have heq : Module.compHom (Localization.Away x) (algebraMap A (Localization.Away x)) =
      (inferInstance : Module A (Localization.Away x)) := by
    apply Module.ext
    funext r t
    exact (Algebra.smul_def r t).symm
  have hsub : Subsingleton (@TensorProduct A _ (Localization.Away x) (M : Type u) _ _
      (Module.compHom (Localization.Away x) (algebraMap A (Localization.Away x))) _) :=
    ModuleCat.isZero_iff_subsingleton.1 h
  rw [heq] at hsub
  obtain ⟨r, ⟨k, rfl⟩, hrq⟩ := LocalizedModule.subsingleton_iff.1
    (LocalizedModule.equivTensorProduct (Submonoid.powers x) (M : Type u)).toEquiv.subsingleton q
  exact ⟨k, hrq⟩

/-- Positive-degree structure-sheaf cohomology of an affine scheme vanishes. -/
@[sga "1 XI 6.9" "partial", sga "3 XXII 5.9.6" "special case"]
private theorem isZero_structureSheafCohomology_of_isAffine {A : Type u} [CommRing A]
    {W : Scheme.{u}} [IsAffine W] (f' : W ⟶ Spec (.of A)) (n : ℕ) (hn : 0 < n) :
    IsZero (structureSheafCohomology f' n) := by
  have hqc : (SheafOfModules.unit W.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit W
  exact Functor.map_isZero (ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (.of A)).inv ≫ f'.appLE ⊤ ⊤ (by simp)).hom)
    ((Stacks.LocalCohomology.isZero_hgroup_iff_isZero_rightDerived
      W.ringCatSheaf ⊤ n (SheafOfModules.unit W.ringCatSheaf)).1
      (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen W
        (SheafOfModules.unit W.ringCatSheaf) ⊤ (isAffineOpen_top W) n hn))

/-- **Localizing at an element of the ideal kills positive-degree cohomology.** For `x ∈ I` the
basic open `D(x)` lies in `Spec A ∖ V(I)`, so the base change of `V` along `A → A_x` is affine
over `Spec A_x` and its positive-degree structure-sheaf cohomology vanishes; flat base change
transports the vanishing to `A_x ⊗_A H ⁿ(V, 𝒪_V)`. -/
private theorem isZero_extendScalars_away_structureSheafCohomology
    (A : Type u) [CommRing A] (I : Ideal A)
    {V : Scheme.{u}} (f : V ⟶ Spec (.of A)) [QuasiCompact f]
    (g : V ⟶ (complementZeroLocus A I : Scheme)) [IsAffineHom g]
    (hg : g ≫ (complementZeroLocus A I).ι = f)
    (x : A) (hx : x ∈ I) (n : ℕ) (hn : 0 < n) :
    IsZero ((ModuleCat.extendScalars (algebraMap A (Localization.Away x))).obj
      (structureSheafCohomology f n)) := by
  have hsep : IsSeparated f := hg ▸ inferInstance
  have hrange : Set.range (Spec.map (CommRingCat.ofHom
      (algebraMap A (Localization.Away x)))).base ⊆
      Set.range (complementZeroLocus A I).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro y ⟨z, rfl⟩ hmem
    have hxz := (PrimeSpectrum.mem_zeroLocus _ _).1 hmem hx
    exact z.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hxz
      (IsLocalization.map_units (Localization.Away x) ⟨x, Submonoid.mem_powers x⟩))
  set sx := IsOpenImmersion.lift (complementZeroLocus A I).ι
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x)))) hrange
  have hsx : sx ≫ (complementZeroLocus A I).ι =
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x))) :=
    IsOpenImmersion.lift_fac _ _ _
  have hpb0 : IsPullback (pullback.fst g sx) (pullback.snd g sx) g sx :=
    IsPullback.of_hasPullback g sx
  have haff : IsAffineHom (pullback.snd g sx) := MorphismProperty.of_isPullback hpb0 inferInstance
  have : IsAffine (pullback g sx) := inferInstance
  have hpb : IsPullback (pullback.fst g sx) (pullback.snd g sx) f
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x)))) := by
    rw [← hg, ← hsx]
    exact isPullback_comp_mono (complementZeroLocus A I).ι hpb0
  obtain ⟨e⟩ := nonempty_structureSheafCohomology_extendScalars
    (algebraMap A (Localization.Away x))
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers x)))
    f (pullback.snd g sx) (pullback.fst g sx) hpb n
  exact (isZero_structureSheafCohomology_of_isAffine (pullback.snd g sx) n hn).of_iso e

/-- **Positive-degree structure-sheaf cohomology over a punctured spectrum is `𝔪`-power
torsion.** Let `A` be Noetherian local, let `f : V ⟶ Spec A` be quasi-compact and factor through
the punctured spectrum by an affine morphism. Then every element of `H ⁿ(V, 𝒪_V)`, `n > 0`, is
killed by a power of the maximal ideal. -/
theorem isIPowerTorsion_structureSheafCohomology
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {V : Scheme.{u}} (f : V ⟶ Spec (.of A)) [QuasiCompact f]
    (g : V ⟶ (complementZeroLocus A (IsLocalRing.maximalIdeal A) : Scheme)) [IsAffineHom g]
    (hg : g ≫ (complementZeroLocus A (IsLocalRing.maximalIdeal A)).ι = f)
    (n : ℕ) (hn : 0 < n) :
    IsIPowerTorsion A (structureSheafCohomology f n) (IsLocalRing.maximalIdeal A) := by
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (IsLocalRing.maximalIdeal A)
  rw [← hs]
  refine isIPowerTorsion_of_forall_pow_smul s (fun q y hy => ?_)
  refine exists_pow_smul_eq_zero_of_isZero y (structureSheafCohomology f n) ?_ q
  exact isZero_extendScalars_away_structureSheafCohomology A _ f g hg y
    (hs ▸ Ideal.subset_span hy) n hn

/-! ### Characteristic `p`: the cohomology is its own Frobenius base change -/

/-- **Structure-sheaf cohomology of an étale scheme is invariant under Frobenius base change.**
In characteristic `p` the relative Frobenius of an étale scheme is an isomorphism, so the
absolute Frobenius of `V` exhibits `V` as the base change of itself along the Frobenius of
`Spec A`; that Frobenius is flat because `A` is regular, so flat base change applies. -/
theorem nonempty_frobenius_structureSheafCohomology_iso
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (p : ℕ) (hp : p.Prime) (hchar : (p : A) = 0)
    {V : Scheme.{u}} (f : V ⟶ Spec (.of A)) [Etale f] [QuasiCompact f] [IsSeparated f] (n : ℕ) :
    Nonempty ((ModuleCat.extendScalars (frobeniusOfPrime p hp hchar)).obj
      (structureSheafCohomology f n) ≅ structureSheafCohomology f n) := by
  have : Fact p.Prime := ⟨hp⟩
  have hS : IsInCharacteristic (Spec (.of A)) p := by
    show (p : Γ(Spec (.of A), ⊤)) = 0
    rw [← map_natCast (Scheme.ΓSpecIso (.of A)).inv.hom, hchar, map_zero]
  set F := absoluteFrobenius (Spec (.of A)) p hS
  set Fv := absoluteFrobenius V p (isInCharacteristic_of_hom f p hS)
  set X : Over (Spec (.of A)) := Over.mk f
  have : Etale X.hom := inferInstanceAs (Etale f)
  have : IsIso (relativeFrobenius (Spec (.of A)) p hS X) :=
    isIso_relativeFrobenius_of_etale _ p hS X
  have hiso : IsIso (relativeFrobenius (Spec (.of A)) p hS X).left :=
    (Over.forget _).map_isIso _
  have hf : (relativeFrobenius (Spec (.of A)) p hS X).left ≫ pullback.fst f F = Fv :=
    relativeFrobenius_fst _ p hS X
  have hs : (relativeFrobenius (Spec (.of A)) p hS X).left ≫ pullback.snd f F = f :=
    relativeFrobenius_snd _ p hS X
  have sq : IsPullback Fv f f F := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ (asIso (relativeFrobenius (Spec (.of A)) p hS X).left)
      hf hs
    calc Fv ≫ f = ((relativeFrobenius (Spec (.of A)) p hS X).left ≫ pullback.fst f F) ≫ f :=
          congrArg (· ≫ f) hf.symm
      _ = ((relativeFrobenius (Spec (.of A)) p hS X).left ≫ pullback.snd f F) ≫ F := by
          simp only [Category.assoc, pullback.condition]
      _ = f ≫ F := congrArg (· ≫ F) hs
  have he : F = Spec.map (CommRingCat.ofHom (frobeniusOfPrime p hp hchar)) := by
    apply AlgebraicGeometry.ext_of_isAffine
    apply (cancel_mono (Scheme.ΓSpecIso (.of A)).hom).mp
    rw [Scheme.ΓSpecIso_naturality]
    ext y
    show (Scheme.ΓSpecIso (.of A)).hom.hom (F.appTop.hom y) =
      frobeniusOfPrime p hp hchar ((Scheme.ΓSpecIso (.of A)).hom.hom y)
    rw [show F.appTop.hom y = y ^ p from absoluteFrobenius_app_apply _ p hS ⊤ y]
    exact map_pow _ _ _
  have hreg : IsRegularRing A :=
    ((IsLocalRing.isRegularRing_tfae (R := A)).out 1 3).mp (inferInstance : IsRegularLocalRing A)
  exact nonempty_structureSheafCohomology_extendScalars (frobeniusOfPrime p hp hchar)
    ((isRegularRing_iff_frobeniusOfPrime_flat p hp hchar).mp hreg) f f Fv
    (by simpa only [he] using sq) n

/-! ### Characteristic zero: reduction to a power series ring -/

/-- Power torsion passes to a base change along any algebra map, for the extended ideal. -/
private theorem isIPowerTorsion_tensorProduct {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (I : Ideal A) {M : Type u} [AddCommGroup M] [Module A M]
    (h : IsIPowerTorsion A M I) :
    IsIPowerTorsion B (TensorProduct A B M) (I.map (algebraMap A B)) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, Nat.one_pos, fun b _ => smul_zero b⟩
  | tmul b₀ m =>
    obtain ⟨k, hk, hkill⟩ := h m
    have hker : ∀ a ∈ I ^ k,
        algebraMap A B a • (b₀ ⊗ₜ[A] m) = (0 : TensorProduct A B M) := by
      intro a ha
      calc algebraMap A B a • (b₀ ⊗ₜ[A] m)
          = (algebraMap A B a • b₀) ⊗ₜ[A] m := (TensorProduct.smul_tmul' _ _ _).symm
        _ = (a • b₀) ⊗ₜ[A] m := by rw [Algebra.smul_def a b₀, smul_eq_mul]
        _ = b₀ ⊗ₜ[A] (a • m) := TensorProduct.smul_tmul _ _ _
        _ = 0 := by rw [hkill a ha, TensorProduct.tmul_zero]
    have hle : (I ^ k).map (algebraMap A B) ≤
        (LinearMap.ker (LinearMap.toSpanSingleton B (TensorProduct A B M)
          (b₀ ⊗ₜ[A] m)) : Ideal B) :=
      Ideal.map_le_iff_le_comap.2 (fun a ha => hker a ha)
    refine ⟨k, hk, fun c hc => ?_⟩
    rw [← Ideal.map_pow] at hc
    exact hle hc
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨k₁, hk₁, hz₁⟩ := h₁
    obtain ⟨k₂, hk₂, hz₂⟩ := h₂
    refine ⟨max k₁ k₂, lt_of_lt_of_le hk₁ (le_max_left _ _), fun c hc => ?_⟩
    rw [smul_add, hz₁ c (Ideal.pow_le_pow_right (le_max_left k₁ k₂) hc),
      hz₂ c (Ideal.pow_le_pow_right (le_max_right k₁ k₂) hc), add_zero]

/-- Power torsion transports along a linear equivalence. -/
private theorem isIPowerTorsion_of_linearEquiv {R : Type u} [CommRing R] (I : Ideal R)
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (hM : IsIPowerTorsion R M I) : IsIPowerTorsion R N I := by
  intro y
  obtain ⟨m, hm, hkill⟩ := hM (e.symm y)
  refine ⟨m, hm, fun a ha => ?_⟩
  simpa using congrArg e (hkill a ha)

/-- **A regular local ring containing a field of characteristic zero admits a flat local map to a
power series ring over a field, bijective on closed fibres.** The map is the completion followed
by Cohen's structure theorem. -/
private theorem exists_flat_powerSeries_map
    (A k : Type u) [CommRing A] [IsRegularLocalRing A] [Field k] [CharZero k] [Algebra k A] :
    ∃ (K : Type u) (_ : Field K) (_ : CharZero K) (d : ℕ)
      (φ : A →+* MvPowerSeries (Fin d) K),
      φ.Flat ∧ IsLocalHom φ ∧
      (IsLocalRing.maximalIdeal A).map φ =
        IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) K) ∧
      Function.Bijective (Ideal.quotientMap
        ((IsLocalRing.maximalIdeal A).map φ) φ Ideal.le_comap_map) := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  have : IsRegularLocalRing C := isRegularLocalRing_iff_adicCompletion_maximalIdeal.mp
    (inferInstance : IsRegularLocalRing A)
  let _ : Algebra k C := ((algebraMap A C).comp (algebraMap k A)).toAlgebra
  let K := IsLocalRing.ResidueField C
  let a : k →+* K := (IsLocalRing.residue C).comp (algebraMap k C)
  let _ : CharZero K := charZero_of_injective_ringHom a.injective
  let d := Module.finrank K (IsLocalRing.CotangentSpace C)
  obtain ⟨e⟩ := (IsRegularLocalRing.nonempty_ringEquiv_and_algEquiv_mvPowerSeries.{u, u, u}
    C d rfl).1 k
  let φ : A →+* MvPowerSeries (Fin d) K := e.toRingHom.comp (algebraMap A C)
  have : IsLocalHom e.toRingHom := IsLocalHom.of_surjective _ e.surjective
  have : IsLocalHom φ := RingHom.isLocalHom_comp e.toRingHom (algebraMap A C)
  have hm : (IsLocalRing.maximalIdeal A).map φ =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) K) := by
    show (IsLocalRing.maximalIdeal A).map (e.toRingHom.comp (algebraMap A C)) = _
    rw [← Ideal.map_map, ← AdicCompletion.maximalIdeal_eq_map]
    exact IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective
  refine ⟨K, inferInstance, inferInstance, d, φ, ?_, inferInstance, hm, ?_⟩
  · exact (RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian
      (IsLocalRing.maximalIdeal A))).comp (RingHom.Flat.of_bijective e.bijective)
  · have hr : Function.Bijective (IsLocalRing.ResidueField.map φ) := by
      show Function.Bijective (IsLocalRing.ResidueField.map
        (e.toRingHom.comp (algebraMap A C)))
      rw [IsLocalRing.ResidueField.map_comp]
      exact (IsLocalRing.ResidueField.mapEquiv e).bijective.comp
        (AdicCompletion.residueField_map_bijective A)
    have hquot : ∀ (J : Ideal (MvPowerSeries (Fin d) K))
        (hJ : IsLocalRing.maximalIdeal A ≤ J.comap φ),
        J = IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) K) →
        Function.Bijective (Ideal.quotientMap J φ hJ) := by
      rintro J hJ rfl
      exact hr
    exact hquot _ Ideal.le_comap_map hm

/-- The residue field of a power series ring over `k` is `k`, through the constant coefficient. -/
private def powerSeriesResidueFieldIso (k : Type u) [Field k] (d : ℕ) :
    ModuleCat.of (MvPowerSeries (Fin d) k)
      (IsLocalRing.ResidueField (MvPowerSeries (Fin d) k)) ≅
    (ModuleCat.restrictScalars
      (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) k →+* k)).obj
        (ModuleCat.of k k) := by
  let B := MvPowerSeries (Fin d) k
  let c : B →+* k := MvPowerSeries.constantCoeff
  have : IsLocalHom c := IsLocalHom.of_surjective c
    (fun y => ⟨MvPowerSeries.C y, MvPowerSeries.constantCoeff_C y⟩)
  let φ := IsLocalRing.ResidueField.lift c
  let L : IsLocalRing.ResidueField B →ₗ[B]
      (ModuleCat.restrictScalars c).obj (ModuleCat.of k k) :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := by
        intro b y
        change φ (IsLocalRing.residue B b * y) = c b * φ y
        rw [map_mul, IsLocalRing.ResidueField.lift_residue_apply] }
  have hsurj : Function.Surjective L := by
    intro y
    refine ⟨IsLocalRing.residue B (MvPowerSeries.C (show k from y)), ?_⟩
    change (IsLocalRing.ResidueField.lift c)
      (IsLocalRing.residue B (MvPowerSeries.C (show k from y))) = (show k from y)
    rw [IsLocalRing.ResidueField.lift_residue_apply]
    exact MvPowerSeries.constantCoeff_C (show k from y)
  exact (LinearEquiv.ofBijective L ⟨RingHom.injective φ, hsurj⟩).toModuleIso

/-- Precomposing an injective hull with an isomorphism is again an injective hull. -/
private theorem isInjectiveHull_comp_iso {R : Type u} [Ring R]
    {M N E : ModuleCat.{u} R} (e : M ≅ N) (i : N ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) : Module.IsInjectiveHull (e.hom ≫ i) := by
  refine ⟨hi.1, ?_⟩
  have hmk : Subobject.mk (e.hom ≫ i) = Subobject.mk i :=
    Subobject.mk_eq_mk_of_comm _ _ e rfl
  intro P hP
  simpa only [hmk] using hi.2 P hP

/-- **Over a field every module is a direct sum of copies of an injective hull of the residue
field.** An injective hull of the field itself is the field, because an essential extension of a
one-dimensional space over a field is itself, and every module over a field is free. -/
private theorem exists_linearEquiv_directSum_of_injectiveHull_field
    (R : Type u) [Field R] (M : Type u) [AddCommGroup M] [Module R M]
    {K E : ModuleCat.{u} R} (e : R ≃ₗ[R] K) (i : K ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    ∃ J : Type u, Nonempty (M ≃ₗ[R] DirectSum J (fun _ => E)) := by
  classical
  let P := LinearMap.range i.hom
  let eP := LinearEquiv.ofInjective i.hom ((ModuleCat.mono_iff_injective i).mp inferInstance)
  have hmk : Subobject.mk i = Subobject.mk (ModuleCat.ofHom P.subtype) :=
    Subobject.mk_eq_mk_of_comm _ _ eP.toModuleIso (by rfl)
  have hess : Module.IsEssentialMono (ModuleCat.ofHom P.subtype) := by
    intro Q hQ
    simpa only [← hmk] using hi.2 Q hQ
  have hsurj : Function.Surjective i.hom := by
    intro y
    show y ∈ P
    by_cases hy : y = 0
    · exact hy ▸ P.zero_mem
    obtain ⟨r, hr, hne⟩ := (Module.isEssentialMono_subtype_iff P).mp hess y hy
    simpa only [smul_smul, inv_mul_cancel₀ (left_ne_zero_of_smul hne), one_smul] using
      P.smul_mem r⁻¹ hr
  let eE : R ≃ₗ[R] E := e.trans (LinearEquiv.ofBijective i.hom
    ⟨(ModuleCat.mono_iff_injective i).mp inferInstance, hsurj⟩)
  exact ⟨Module.Free.ChooseBasisIndex R M, ⟨(Module.Free.chooseBasis R M).repr.trans
    ((Finsupp.mapRange.linearEquiv eE).trans
      (finsuppLEquivDirectSum R (E : Type u) (Module.Free.ChooseBasisIndex R M)))⟩⟩

/-- **Stacks 0EC2 for the structure sheaf of an étale scheme.** Positive-degree structure-sheaf
cohomology of a quasi-compact étale scheme over a characteristic-zero power series ring, when it
is maximal-ideal-power torsion, is a direct sum of copies of an injective hull of the residue
field: the partial derivatives of the base extend to the cohomology and satisfy the Leibniz
rules. In dimension zero the base is a field and the statement is freeness. -/
private theorem exists_directSum_powerSeries
    (k E : Type u) [Field k] [CharZero k] (d : ℕ)
    [AddCommGroup E] [Module (MvPowerSeries (Fin d) k) E]
    {V : Scheme.{u}} (f : V ⟶ Spec (.of (MvPowerSeries (Fin d) k)))
    [Etale f] [QuasiCompact f] [QuasiSeparated f] (n : ℕ)
    (hT : IsIPowerTorsion (MvPowerSeries (Fin d) k) (structureSheafCohomology f n)
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) k)))
    (i : (ModuleCat.restrictScalars
        (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) k →+* k)).obj
        (ModuleCat.of k k) ⟶ ModuleCat.of (MvPowerSeries (Fin d) k) E)
    [Mono i] (hi : Module.IsInjectiveHull i) :
    ∃ J : Type u, Nonempty (structureSheafCohomology f n ≃ₗ[MvPowerSeries (Fin d) k]
      DirectSum J (fun _ => E)) := by
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · let B := MvPowerSeries (Fin 0) k
    let c := MvPowerSeries.isEmptyEquiv (Fin 0) k
    let _ : Field B := (c.toMulEquiv.isField (Field.toIsField k)).toField
    let e : B ≃ₗ[B] (ModuleCat.restrictScalars
        (MvPowerSeries.constantCoeff : B →+* k)).obj (ModuleCat.of k k) :=
      { __ := c.toAddEquiv
        map_smul' := fun a b => c.map_mul a b }
    exact exists_linearEquiv_directSum_of_injectiveHull_field B
      (structureSheafCohomology f n) e i hi
  · let _ : Algebra ℤ (MvPowerSeries (Fin d) k) := Ring.toIntAlgebra _
    let θ : Fin d → Derivation ℤ (MvPowerSeries (Fin d) k)
        (MvPowerSeries (Fin d) k) := fun j =>
      { toLinearMap := (MvPowerSeries.pderiv k j).toLinearMap.restrictScalars ℤ
        map_one_eq_zero' := (MvPowerSeries.pderiv k j).map_one_eq_zero
        leibniz' := (MvPowerSeries.pderiv k j).leibniz }
    let D : ∀ j, TwistedDerivation f n (θ j) := fun j => etaleCohomologyDerivation f (θ j) n
    exact MvPowerSeries.exists_linearEquiv_directSum_injectiveHull_of_leibniz k d hd
      (structureSheafCohomology f n) E i hi hT
      (fun j => (D j).toAddMonoidHom) (fun j a y => (D j).leibniz a y)

/-- **An `I`-power-torsion module is its own flat base change.** If `R → S` is flat and bijective
modulo a finitely generated ideal `I`, then the unit `M ⟶ S ⊗_R M` of the extension–restriction
adjunction is an isomorphism on `I`-power-torsion modules. -/
def torsionBaseChangeUnitIso (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective (Ideal.quotientMap (I.map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map))
    (M : ModuleCat.{u} R) (hM : IsIPowerTorsion R M I) :
    M ≅ (ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.extendScalars (algebraMap R S)).obj M) := by
  let η := (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit.app M
  have hbij : Function.Bijective η.hom := by
    have h' := (TensorProduct.comm R M S).bijective.comp
      ((IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective R S I hflat).mpr hq M hM)
    change Function.Bijective (fun x => η x)
    simp only [η, ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
    change Function.Bijective (fun x : M =>
      @TensorProduct.tmul R _ S M _ _ (Module.compHom S (algebraMap R S)) _ 1 x)
    have heq : Module.compHom S (algebraMap R S) = (inferInstance : Module R S) := by
      apply Module.ext
      funext r t
      exact (Algebra.smul_def r t).symm
    rw [heq]
    simpa only [Function.comp_def, LinearEquiv.coe_coe, LinearMap.flip_apply,
      TensorProduct.mk_apply, TensorProduct.comm_tmul] using h'
  exact (LinearEquiv.ofBijective η.hom hbij).toModuleIso

/-- Restriction of scalars commutes with finitely supported functions, on the nose. -/
private def restrictScalarsFinsuppIso {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (E : ModuleCat.{u} S) (J : Type u) :
    (ModuleCat.restrictScalars φ).obj (ModuleCat.of S (J →₀ E)) ≅
      ModuleCat.of R (J →₀ (ModuleCat.restrictScalars φ).obj E) := by
  let e : (ModuleCat.restrictScalars φ).obj (ModuleCat.of S (J →₀ E)) ≃ₗ[R]
      (J →₀ (ModuleCat.restrictScalars φ).obj E) :=
    { toFun := fun y => y
      invFun := fun y => y
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact e.toModuleIso

/-- **The equicharacteristic-zero case.** Flat base change to a power series ring over a field
turns the decomposition over that ring into one over `A`: the cohomology is recovered from its
base change because it is `𝔪`-power torsion, and the injective hulls of the two residue fields
correspond by Stacks 08Z5. -/
private theorem exists_directSum_charZero
    (A k E : Type u) [CommRing A] [IsRegularLocalRing A] [Field k] [CharZero k] [Algebra k A]
    [AddCommGroup E] [Module A E]
    {V : Scheme.{u}} (f : V ⟶ Spec (.of A)) [Etale f] [QuasiCompact f] [IsSeparated f] (n : ℕ)
    (hT : IsIPowerTorsion A (structureSheafCohomology f n) (IsLocalRing.maximalIdeal A))
    (i : ModuleCat.of A (IsLocalRing.ResidueField A) ⟶ ModuleCat.of A E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    ∃ J : Type u, Nonempty (structureSheafCohomology f n ≃ₗ[A] DirectSum J (fun _ => E)) := by
  classical
  have : QuasiSeparated f := AlgebraicGeometry.quasiSeparated_of_locallyOfFiniteType f
  obtain ⟨K, hK, hK0, d, φ, hflat, hlocal, hm, hq⟩ := exists_flat_powerSeries_map A k
  let B := MvPowerSeries (Fin d) K
  let _ : Algebra A B := φ.toAlgebra
  have : IsLocalHom (algebraMap A B) := hlocal
  have : IsNoetherianRing B := mvPowerSeries_fin_isNoetherianRing K d
  have hflat' : Module.Flat A B := RingHom.flat_algebraMap_iff.mp hflat
  set q := Spec.map (CommRingCat.ofHom φ)
  have : Etale (pullback.snd f q) := inferInstanceAs (Etale (pullback.snd f q))
  have : QuasiCompact (pullback.snd f q) := inferInstanceAs (QuasiCompact (pullback.snd f q))
  have : QuasiSeparated (pullback.snd f q) :=
    inferInstanceAs (QuasiSeparated (pullback.snd f q))
  obtain ⟨eH⟩ := nonempty_structureSheafCohomology_extendScalars φ hflat f
    (pullback.snd f q) (pullback.fst f q) (IsPullback.of_hasPullback f q) n
  have hT' : IsIPowerTorsion B (structureSheafCohomology (pullback.snd f q) n)
      (IsLocalRing.maximalIdeal B) := by
    rw [← hm]
    exact isIPowerTorsion_of_linearEquiv _ eH.toLinearEquiv
      (isIPowerTorsion_tensorProduct (IsLocalRing.maximalIdeal A) hT)
  obtain ⟨EB, iκ, _, hκ⟩ := Module.exists_isInjectiveHull B
    ((ModuleCat.restrictScalars (MvPowerSeries.constantCoeff : B →+* K)).obj
      (ModuleCat.of K K))
  have hB : Module.IsInjectiveHull ((powerSeriesResidueFieldIso K d).hom ≫ iκ) :=
    isInjectiveHull_comp_iso (powerSeriesResidueFieldIso K d) iκ hκ
  obtain ⟨J, ⟨eJ⟩⟩ := exists_directSum_powerSeries K EB d (pullback.snd f q) n hT' iκ hκ
  obtain ⟨eE, -⟩ := Dualizing.exists_iso_injectiveHull_residueField A B hflat hq i
    ((powerSeriesResidueFieldIso K d).hom ≫ iκ) hi hB
  exact ⟨J, ⟨(torsionBaseChangeUnitIso A B (IsLocalRing.maximalIdeal A) hflat' hq
      (structureSheafCohomology f n) hT ≪≫
    (ModuleCat.restrictScalars φ).mapIso (eH ≪≫ eJ.toModuleIso ≪≫
      (finsuppLEquivDirectSum B (EB : Type u) J).symm.toModuleIso) ≪≫
    restrictScalarsFinsuppIso φ EB J ≪≫
    (Finsupp.mapRange.linearEquiv eE.symm.toLinearEquiv).toModuleIso).toLinearEquiv.trans
      (finsuppLEquivDirectSum A E J)⟩⟩

/-! ### The theorem -/

/-- **Stacks Project, Tag 0ECB.** Let `A` be a regular local ring containing a field `k`, let
`f : V ⟶ Spec A` be étale and quasi-compact, and suppose `f` factors as `g ≫ U.ι` through the
punctured spectrum `U = Spec A ∖ V(𝔪)` with `g` affine. Then for every `i > 0` the `A`-module
`H ⁱ(V, 𝒪_V)` is a direct sum of copies of an injective hull `E` of the residue field of `A`.

The index set and the isomorphism are not determined by the statement. -/
@[stacks 0ECB]
theorem exists_directSum_injectiveHull_residueField
    (A k E : Type u) [CommRing A] [IsRegularLocalRing A] [Field k] [Algebra k A]
    [AddCommGroup E] [Module A E]
    {V : Scheme.{u}} (f : V ⟶ Spec (.of A)) [Etale f] [QuasiCompact f]
    (g : V ⟶ (complementZeroLocus A (IsLocalRing.maximalIdeal A) : Scheme)) [IsAffineHom g]
    (hg : g ≫ (complementZeroLocus A (IsLocalRing.maximalIdeal A)).ι = f)
    (i : ModuleCat.of A (IsLocalRing.ResidueField A) ⟶ ModuleCat.of A E) [Mono i]
    (hi : Module.IsInjectiveHull i) (n : ℕ) (hn : 0 < n) :
    ∃ J : Type u, Nonempty (structureSheafCohomology f n ≃ₗ[A] DirectSum J (fun _ => E)) := by
  classical
  have hsep : IsSeparated f := hg ▸ inferInstance
  have hT := isIPowerTorsion_structureSheafCohomology A f g hg n hn
  rcases CharP.exists' k with hzero | ⟨p, hp, hpk⟩
  · exact exists_directSum_charZero A k E f n hT i hi
  · have hpA : (p : A) = 0 := by
      rw [← map_natCast (algebraMap k A), CharP.cast_eq_zero k p, map_zero]
    obtain ⟨eF⟩ := nonempty_frobenius_structureSheafCohomology_iso A p hp.out hpA f n
    exact Dualizing.isIPowerTorsion_frobeniusStable_exists_equiv_directSum_injectiveHull
      p hp.out A hpA (structureSheafCohomology f n) hT eF E i hi

end Stacks.EtalePuncturedSpectrum

end
