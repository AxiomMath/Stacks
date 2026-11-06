module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffinePowerTorsion
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.MayerVietorisPowerTorsion
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.RestrictionPerfectSupport
public import StacksFrontier.AlgebraicGeometry.InductionPrinciple.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.Approximation.OpenSubscheme
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms out of a perfect complex, killed by a power of a scalar

Let `X` be a quasi-compact quasi-separated scheme, let `a` be a global section of `𝒪_X` and let
`α : E ⟶ E'⟦n⟧` be a morphism of `D_QCoh(𝒪_X)` with `E` perfect and `E'` supported on the closed
subset `T` where `a` vanishes. Then `a ^ k • α = 0` for some `k`.

This is [Stacks, Tag 08EJ]. The proof is the one of the source: the induction principle of
[Stacks, Tag 08DR] over the quasi-compact opens of `X`, with the affine case
`Stacks.PowerTorsion.exists_pow_smul_eq_zero_of_isPerfect_of_cohomologySupportedOn` as its base
case and Mayer--Vietoris for morphisms of the derived category,
`Stacks.PowerTorsion.exists_pow_smul_eq_zero_of_cover`, as its step.

## Main definitions

* `Stacks.PowerTorsion.PowerTorsionProperty`: the statement being induced over, read on a scheme
  `Y` with a ring map `A →+* Γ(Y, 𝒪_Y)` giving the scalars.

## Main results

* `Stacks.PowerTorsion.powerTorsionProperty_of_iso`: the statement transports along an
  isomorphism of schemes.
* `Stacks.PowerTorsion.powerTorsionProperty_of_isAffine`: it holds on a scheme isomorphic to the
  spectrum of its ring of global sections -- the base case.
* `Stacks.PowerTorsion.powerTorsionProperty_sup`: it passes from two opens and their
  intersection to their union -- the inductive step.
* `Stacks.PowerTorsion.exists_pow_smul_eq_zero_of_isPerfect_of_cohomologySupportedOn_qcqs`:
  **[Stacks, Tag 08EJ]**.

## Implementation notes

**What is induced over.** The property `Stacks.PowerTorsion.PowerTorsionProperty` is a statement
about *every* pair of objects of the derived category of the open, not about the restrictions of
one fixed pair: the Mayer--Vietoris step asks that every morphism
`E|_{U ∩ V} ⟶ E'|_{U ∩ V}⟦n - 1⟧` be killed by a power of the scalar, which a statement about
restrictions of a fixed pair does not give. The shift is part of the property for the same
reason, so that the step's hypothesis on the intersection is the property itself read at `n - 1`
and no compatibility of the support condition with shifting is needed there.

**Why the property is quantified over open immersions rather than over opens.** The property is
induced over the opens of `X` in the form "for every scheme `Y` and open immersion `g : Y ⟶ X`
with image the given open, the property holds on `Y`". Stated about `W.toScheme` only, the
inductive step would have to carry it from an open `U` of `X` to the corresponding open of the
scheme `U ⊔ V`, which is a different scheme isomorphic to `U.toScheme`; in the form used here the
step applies the induction hypothesis to the open immersion `(g ⁻¹ᵁ U).ι ≫ g` directly, and the
only transport along an isomorphism left is the one in the base case, where the open is affine
and the statement is known on `Spec Γ(X, W)`.

**The scalars.** The scalar ring is fixed once and for all and reaches each open through a ring
map into its global sections, which is what makes "killed by a power of `a`" the same statement
on `X` and on an open of `X`; this is the design of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/RestrictionBaseRingLinear.lean`. The base case needs
the identification of that `A`-linear structure on `Spec Γ(X, W)` with the one the affine case
is stated in, `AlgebraicGeometry.modulesLinear` over the identity structure morphism; the two
are definitionally equal, and the change of scalar ring from `A` to `Γ(X, W)` along the
restriction map is definitional as well, both because
`AlgebraicGeometry.Scheme.linearOfRingHom` is `CategoryTheory.Linear.ofRingMorphism` of a
composite.

**The two spellings of restriction.** The step is stated in the extension-by-zero spelling
`Stacks.ExtensionByZero.derivedRestriction`; the property is read at Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`. The two are crossed by
`Stacks.DerivedQCoh.derivedJStarIsoDerivedRestrict`.

## References

* [Stacks Project, Lemma 36.10.12 (Tag 08EJ)](https://stacks.math.columbia.edu/tag/08EJ)
* [Stacks Project, Lemma 30.3.2 (Tag 08DR)](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Lemma 20.28.6 (Tag 08BW)](https://stacks.math.columbia.edu/tag/08BW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open ExtensionByZeroModules
open Stacks.SchemeCohomology (ringedSpace)
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Cohomology.PerfectComplexTriangles (mapDerivedCategoryIsoOfNatIso
  mapDerivedCategoryCompIso)
open Stacks.AlgebraicGeometry.TopDegreeBaseChange (specBase)

universe u

namespace Stacks.PowerTorsion

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A]

/-- **The statement [Stacks, Tag 08EJ] makes, read on a scheme `Y` whose scalars come from `A`
through a ring map `φ : A →+* Γ(Y, 𝒪_Y)`.** Every morphism from a perfect object with
quasi-coherent cohomology to a shift of an object with quasi-coherent cohomology supported where
`φ a` vanishes is killed by a power of `a`. -/
def PowerTorsionProperty (A : Type u) [CommRing A] (Y : Scheme.{u}) (φ : A →+* Γ(Y, ⊤))
    (a : A) : Prop :=
  letI : Linear A Y.Modules := Scheme.linearOfRingHom Y A φ
  ∀ E E' : DerivedCategory Y.Modules, IsPerfect (X := ringedSpace Y) E →
    (∀ n : ℤ, ((DerivedCategory.homologyFunctor Y.Modules n).obj E).IsQuasicoherent) →
    (∀ n : ℤ, ((DerivedCategory.homologyFunctor Y.Modules n).obj E').IsQuasicoherent) →
    CohomologySupportedOn Y.ringCatSheaf ((Y.basicOpen (φ a) : Set Y)ᶜ) E' →
    ∀ (n : ℤ) (α : E ⟶ E'⟦n⟧), ∃ k : ℕ, a ^ k • α = 0

/-- Restriction along a morphism and along its inverse compose to the identity on `𝒪`-modules. -/
def restrictFunctorInvCompIso {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    Scheme.Modules.restrictFunctor e.inv ⋙ Scheme.Modules.restrictFunctor e.hom ≅
      𝟭 Y.Modules :=
  (Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
    Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫ Scheme.Modules.restrictFunctorId

/-- The derived form of `Stacks.PowerTorsion.restrictFunctorInvCompIso`. -/
def derivedRestrictInvCompIso {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    (Scheme.Modules.restrictFunctor e.inv).mapDerivedCategory ⋙
        (Scheme.Modules.restrictFunctor e.hom).mapDerivedCategory ≅
      𝟭 (DerivedCategory Y.Modules) :=
  (mapDerivedCategoryCompIso (Scheme.Modules.restrictFunctor e.inv)
      (Scheme.Modules.restrictFunctor e.hom)).symm ≪≫
    mapDerivedCategoryIsoOfNatIso _ _ (restrictFunctorInvCompIso e) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- **The global sections of an isomorphism undo each other.** -/
theorem appTop_hom_comp_appTop_hom {Y Z : Scheme.{u}} (e : Y ≅ Z) (φ : A →+* Γ(Y, ⊤)) :
    (e.hom.appTop).hom.comp ((e.inv.appTop).hom.comp φ) = φ := by
  have h2 : (e.hom.appTop).hom.comp (e.inv.appTop).hom = RingHom.id Γ(Y, ⊤) := by
    have h : Scheme.Hom.appTop (e.hom ≫ e.inv) = Scheme.Hom.appTop (𝟙 Y) :=
      congrArg (fun f : Y ⟶ Y => Scheme.Hom.appTop f) e.hom_inv_id
    rw [Scheme.Hom.comp_appTop] at h
    have := congrArg CommRingCat.Hom.hom h
    simpa using this
  rw [← RingHom.comp_assoc, h2, RingHom.id_comp]

/-- **Restriction along the inverse of an isomorphism is `A`-linear for the structure the
isomorphism transports.** This is `Stacks.DerivedQCoh.derivedRestrict_linear` at `e.hom`, with
the ring map it produces on the target rewritten by
`Stacks.PowerTorsion.appTop_hom_comp_appTop_hom`. -/
theorem derivedRestrict_hom_linear {Y Z : Scheme.{u}} (e : Y ≅ Z) (φ : A →+* Γ(Y, ⊤)) :
    letI : Linear A Y.Modules := Scheme.linearOfRingHom Y A φ
    letI : Linear A Z.Modules := Scheme.linearOfRingHom Z A ((e.inv.appTop).hom.comp φ)
    Functor.Linear A (Scheme.Modules.restrictFunctor e.hom).mapDerivedCategory := by
  let : Linear A Y.Modules := Scheme.linearOfRingHom Y A φ
  let : Linear A Z.Modules := Scheme.linearOfRingHom Z A ((e.inv.appTop).hom.comp φ)
  have hring : Scheme.linearOfRingHom.{u, u} Y A
        ((e.hom.appTop).hom.comp ((e.inv.appTop).hom.comp φ)) =
      Scheme.linearOfRingHom.{u, u} Y A φ :=
    congrArg (Scheme.linearOfRingHom.{u, u} Y A) (appTop_hom_comp_appTop_hom e φ)
  exact hring ▸ Stacks.DerivedQCoh.derivedRestrict_linear e.hom ((e.inv.appTop).hom.comp φ)

/-- **The support of the restriction along the inverse of an isomorphism.** The complement of the
basic open of `φ a` pulls back to the complement of the basic open of its image. -/
theorem preimage_compl_basicOpen {Y Z : Scheme.{u}} (h : Z ⟶ Y) (r : Γ(Y, ⊤)) :
    ⇑h.base ⁻¹' ((Y.basicOpen r : Set Y)ᶜ) =
      ((Z.basicOpen ((h.appTop) r) : Set Z)ᶜ) := by
  rw [Set.preimage_compl]
  congr 1
  exact congrArg (fun W : Z.Opens => (W : Set Z)) (Scheme.preimage_basicOpen h r)

/-- **The statement transports along an isomorphism of schemes.** If it holds on `Z` for the
scalars carried over by `e`, it holds on `Y`.

Restriction along `e.inv` carries the three hypotheses -- perfectness by
`Stacks.DerivedQCoh.isPerfect_derivedRestrict`, quasi-coherence of the cohomology by
`AlgebraicGeometry.isQuasicoherent_homology_restrictFunctor_mapDerivedCategory` and the support
by `Stacks.DerivedQCoh.cohomologySupportedOn_derivedRestrictFunctor` -- and restriction along
`e.hom` carries the conclusion back, by
`Stacks.DerivedQCoh.smul_eq_zero_of_smul_map_eq_zero`. -/
theorem powerTorsionProperty_of_iso {Y Z : Scheme.{u}} (e : Y ≅ Z) (φ : A →+* Γ(Y, ⊤)) (a : A)
    (h : PowerTorsionProperty A Z ((e.inv.appTop).hom.comp φ) a) :
    PowerTorsionProperty A Y φ a := by
  let : Linear A Y.Modules := Scheme.linearOfRingHom Y A φ
  let : Linear A Z.Modules := Scheme.linearOfRingHom Z A ((e.inv.appTop).hom.comp φ)
  let : Functor.Linear A (Scheme.Modules.restrictFunctor e.inv).mapDerivedCategory :=
    Stacks.DerivedQCoh.derivedRestrict_linear e.inv φ
  let : Functor.Linear A (Scheme.Modules.restrictFunctor e.hom).mapDerivedCategory :=
    derivedRestrict_hom_linear e φ
  intro E E' hE hEq hE'q hsupp n α
  set R := (Scheme.Modules.restrictFunctor e.inv).mapDerivedCategory with hRdef
  have hsupp' : CohomologySupportedOn Z.ringCatSheaf
      ((Z.basicOpen ((e.inv.appTop) (φ a)) : Set Z)ᶜ) (R.obj E') := by
    rw [← preimage_compl_basicOpen e.inv (φ a)]
    exact Stacks.DerivedQCoh.cohomologySupportedOn_derivedRestrictFunctor e.inv _ E' hsupp
  obtain ⟨k, hk⟩ := h (R.obj E) (R.obj E')
    (Stacks.DerivedQCoh.isPerfect_derivedRestrict e.inv E hE)
    (fun m => isQuasicoherent_homology_restrictFunctor_mapDerivedCategory e.inv hEq m)
    (fun m => isQuasicoherent_homology_restrictFunctor_mapDerivedCategory e.inv hE'q m)
    hsupp' n (ShiftedHom.map α R)
  refine ⟨k, Stacks.DerivedQCoh.smul_eq_zero_of_smul_map_eq_zero R
    (Scheme.Modules.restrictFunctor e.hom).mapDerivedCategory
    (derivedRestrictInvCompIso e) α (a ^ k) ?_⟩
  have hzero : (a ^ k • R.map α) ≫ (R.commShiftIso n).hom.app E' = 0 := by
    rw [Linear.smul_comp]
    exact hk
  exact (cancel_mono ((R.commShiftIso n).hom.app E')).mp
    (hzero.trans Limits.zero_comp.symm)

/-! ### The base case -/

/-- **The statement on a spectrum, for any ring map into its global sections.** This is
`Stacks.PowerTorsion.exists_pow_smul_eq_zero_of_isPerfect_of_cohomologySupportedOn`, the affine
case of [Stacks, Tag 08EJ], read at the scalar the ring map sends `a` to and with its target
shifted.

The ring map is normalised to a map into `R` followed by the unit of the Gamma--Spec adjunction,
which is possible because that unit is invertible; three identifications are then definitional
and are taken as such. The `A`-linear structure transported along a ring map `A →+* R` acts as
the image of the scalar does, because `AlgebraicGeometry.Scheme.linearOfRingHom` is
`CategoryTheory.Linear.ofRingMorphism` of a composite; the `R`-linear structure of
`AlgebraicGeometry.Scheme.linearOfRingHom` at that unit is `AlgebraicGeometry.modulesLinear`
over the identity structure morphism; and `CommRingCat.of` of the carrier of a commutative ring
object is that object. -/
theorem powerTorsionProperty_spec (R : CommRingCat.{u}) (ψ : A →+* Γ(Spec R, ⊤)) (a : A) :
    PowerTorsionProperty A (Spec R) ψ a := by
  have hid : ((Scheme.ΓSpecIso R).inv.hom).comp ((Scheme.ΓSpecIso R).hom.hom) =
      RingHom.id Γ(Spec R, ⊤) :=
    RingHom.ext fun x => Iso.hom_inv_id_apply (Scheme.ΓSpecIso R) x
  have hψ : ((Scheme.ΓSpecIso R).inv.hom).comp (((Scheme.ΓSpecIso R).hom.hom).comp ψ) = ψ := by
    rw [← RingHom.comp_assoc, hid, RingHom.id_comp]
  rw [← hψ]
  set φ : A →+* R := ((Scheme.ΓSpecIso R).hom.hom).comp ψ with hφ
  let : Linear A (Spec R).Modules :=
    Scheme.linearOfRingHom (Spec R) A (((Scheme.ΓSpecIso R).inv.hom).comp φ)
  let : Linear (R : Type u) (Spec R).Modules := modulesLinear (R : Type u) (specBase (R : Type u))
  intro E E' hE hEq hE'q hsupp n α
  have hb := basicOpen_eq_of_affine (R := R) (φ a)
  have hsupp' : CohomologySupportedOn (Spec R).ringCatSheaf
      (PrimeSpectrum.zeroLocus {φ a}) E' := by
    intro i x hx
    refine hsupp i x ?_
    simp only [Set.mem_compl_iff, not_not, SetLike.mem_coe]
    show x ∈ (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv (φ a))
    rw [hb]
    show x ∈ (PrimeSpectrum.basicOpen (φ a) : Set (PrimeSpectrum R))
    rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
    exact hx
  obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero_of_isPerfect_of_cohomologySupportedOn
    (R : Type u) (φ a) hE hEq (fun m => isQuasicoherent_homology_shift E' hE'q n m)
    (Stacks.DerivedQCoh.cohomologySupportedOn_shift _ E' hsupp' n) α
  refine ⟨k, ?_⟩
  have hbc : a ^ k • α = (φ (a ^ k)) • α := rfl
  rw [hbc, map_pow]
  exact hk

/-- **The statement on a scheme that is an open subscheme of `X` with affine image.** The
isomorphism onto `Spec Γ(X, W)` is
`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq` against
`AlgebraicGeometry.IsAffineOpen.fromSpec`, and the statement crosses it by
`Stacks.PowerTorsion.powerTorsionProperty_of_iso`. The ring map carried along is whatever the
isomorphism produces, which is why
`Stacks.PowerTorsion.powerTorsionProperty_spec` is stated for an arbitrary one. -/
theorem powerTorsionProperty_of_isAffineOpen {X : Scheme.{u}} (φ : A →+* Γ(X, ⊤)) (a : A)
    {W : X.Opens} (hW : IsAffineOpen W) (Y : Scheme.{u}) (g : Y ⟶ X) [IsOpenImmersion g]
    (hg : g.opensRange = W) :
    PowerTorsionProperty A Y ((g.appTop).hom.comp φ) a := by
  have hrange : Set.range g.base = Set.range hW.fromSpec.base := by
    rw [hW.range_fromSpec, ← hg]
    rfl
  exact powerTorsionProperty_of_iso
    (IsOpenImmersion.isoOfRangeEq g hW.fromSpec hrange) _ a
    (powerTorsionProperty_spec Γ(X, W) _ a)

/-! ### The inductive step -/

/-- **The property on an open of `Y`, read in the spelling the Mayer--Vietoris step uses.** The
objects the step hands over are the extension-by-zero restrictions
`Stacks.ExtensionByZero.derivedRestriction`, and the property is about the restriction along
`W.ι`; the two are crossed by `Stacks.DerivedQCoh.derivedJStarIsoDerivedRestrict`, across which
perfectness, quasi-coherence of the cohomology and the support condition are all invariant. -/
theorem exists_pow_smul_eq_zero_restriction {X Y : Scheme.{u}} (φ : A →+* Γ(X, ⊤)) (a : A)
    (g : Y ⟶ X) [IsOpenImmersion g] (W : Y.Opens)
    (hW : PowerTorsionProperty A W.toScheme (((W.ι ≫ g).appTop).hom.comp φ) a)
    (E E' : DerivedCategory Y.Modules)
    (hE : IsPerfect (X := ringedSpace Y) E)
    (hEq : ∀ n : ℤ, ((DerivedCategory.homologyFunctor Y.Modules n).obj E).IsQuasicoherent)
    (hE'q : ∀ n : ℤ, ((DerivedCategory.homologyFunctor Y.Modules n).obj E').IsQuasicoherent)
    (hsupp : CohomologySupportedOn Y.ringCatSheaf
      ((Y.basicOpen (((g.appTop).hom.comp φ) a) : Set Y)ᶜ) E') (m : ℤ)
    (y : (Stacks.ExtensionByZero.derivedRestriction Y.ringCatSheaf W).obj E ⟶
      ((Stacks.ExtensionByZero.derivedRestriction Y.ringCatSheaf W).obj E')⟦m⟧) :
    letI : Linear A (SheafOfModules.{u} (resRing W Y.ringCatSheaf)) :=
      Stacks.DerivedQCoh.linearResRing Y W ((g.appTop).hom.comp φ)
    ∃ k : ℕ, a ^ k • y = 0 := by
  have J : Stacks.ExtensionByZero.derivedRestriction Y.ringCatSheaf W ≅
      (Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory :=
    Stacks.DerivedQCoh.derivedJStarIsoDerivedRestrict Y W
  have hperf : IsPerfect (X := ringedSpace W.toScheme)
      ((Stacks.ExtensionByZero.derivedRestriction Y.ringCatSheaf W).obj E) :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1} (J.app E).symm
      (Stacks.DerivedQCoh.isPerfect_derivedRestrict W.ι E hE)
  have hq : ∀ (K : DerivedCategory Y.Modules),
      (∀ n : ℤ, ((DerivedCategory.homologyFunctor Y.Modules n).obj K).IsQuasicoherent) →
      ∀ n : ℤ, ((DerivedCategory.homologyFunctor W.toScheme.Modules n).obj
        ((Stacks.ExtensionByZero.derivedRestriction Y.ringCatSheaf W).obj K)).IsQuasicoherent := by
    intro K hK n
    exact (SheafOfModules.isQuasicoherent W.toScheme.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor W.toScheme.Modules n).mapIso (J.app K)).symm
      (isQuasicoherent_homology_restrictFunctor_mapDerivedCategory W.ι hK n)
  have hs : CohomologySupportedOn W.toScheme.ringCatSheaf
      ((W.toScheme.basicOpen ((W.ι.appTop) (((g.appTop).hom.comp φ) a)) : Set W.toScheme)ᶜ)
      ((Stacks.ExtensionByZero.derivedRestriction Y.ringCatSheaf W).obj E') := by
    intro i x hx
    refine IsZero.of_iso ?_ ((Scheme.Modules.toPresheaf W.toScheme ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
        ((DerivedCategory.homologyFunctor W.toScheme.Modules i).mapIso (J.app E')))
    refine Stacks.DerivedQCoh.cohomologySupportedOn_derivedRestrictFunctor W.ι _ E' hsupp i x ?_
    rw [Stacks.PowerTorsion.preimage_compl_basicOpen W.ι]
    exact hx
  exact hW _ _ hperf (hq E hEq) (hq E' hE'q) hs m y

/-- **The inductive step of [Stacks, Tag 08EJ].** If the property holds on every open
subscheme of `X` with image `U`, every one with image `V` and every one with image `U ⊓ V`, it
holds on every one with image `U ⊔ V`.

This is `Stacks.PowerTorsion.exists_pow_smul_eq_zero_of_cover`, Mayer--Vietoris for morphisms of
the derived category, applied on the scheme `Y` itself to the two opens `g ⁻¹ᵁ U` and
`g ⁻¹ᵁ V`, which cover it because the image of `g` is `U ⊔ V`. Its three hypotheses are the
induction hypotheses read through
`Stacks.PowerTorsion.exists_pow_smul_eq_zero_restriction` at the three open immersions
`(g ⁻¹ᵁ U).ι ≫ g`, `(g ⁻¹ᵁ V).ι ≫ g` and `((g ⁻¹ᵁ U) ⊓ (g ⁻¹ᵁ V)).ι ≫ g`, whose images are
`U`, `V` and `U ⊓ V`. The hypothesis on the intersection is the property at the degree `n - 1`,
which is why the property carries its shift. -/
theorem powerTorsionProperty_sup {X : Scheme.{u}} (φ : A →+* Γ(X, ⊤)) (a : A) (U V : X.Opens)
    (ihU : ∀ (Y : Scheme.{u}) (g : Y ⟶ X) [IsOpenImmersion g], g.opensRange = U →
      PowerTorsionProperty A Y ((g.appTop).hom.comp φ) a)
    (ihV : ∀ (Y : Scheme.{u}) (g : Y ⟶ X) [IsOpenImmersion g], g.opensRange = V →
      PowerTorsionProperty A Y ((g.appTop).hom.comp φ) a)
    (ihUV : ∀ (Y : Scheme.{u}) (g : Y ⟶ X) [IsOpenImmersion g], g.opensRange = U ⊓ V →
      PowerTorsionProperty A Y ((g.appTop).hom.comp φ) a)
    (Y : Scheme.{u}) (g : Y ⟶ X) [IsOpenImmersion g] (hg : g.opensRange = U ⊔ V) :
    PowerTorsionProperty A Y ((g.appTop).hom.comp φ) a := by
  let : Linear A (SheafOfModules.{u} Y.ringCatSheaf) :=
    Scheme.linearOfRingHom Y A ((g.appTop).hom.comp φ)
  let : Linear A (SheafOfModules.{u} (resRing (g ⁻¹ᵁ U) Y.ringCatSheaf)) :=
    Stacks.DerivedQCoh.linearResRing Y (g ⁻¹ᵁ U) ((g.appTop).hom.comp φ)
  let : Linear A (SheafOfModules.{u} (resRing (g ⁻¹ᵁ V) Y.ringCatSheaf)) :=
    Stacks.DerivedQCoh.linearResRing Y (g ⁻¹ᵁ V) ((g.appTop).hom.comp φ)
  let : Linear A (SheafOfModules.{u} (resRing ((g ⁻¹ᵁ U) ⊓ (g ⁻¹ᵁ V)) Y.ringCatSheaf)) :=
    Stacks.DerivedQCoh.linearResRing Y ((g ⁻¹ᵁ U) ⊓ (g ⁻¹ᵁ V)) ((g.appTop).hom.comp φ)
  let : (Stacks.ExtensionByZero.derivedRestriction Y.ringCatSheaf (g ⁻¹ᵁ U)).Linear A :=
    Stacks.DerivedQCoh.derivedRestriction_linear Y (g ⁻¹ᵁ U) ((g.appTop).hom.comp φ)
  let : (Stacks.ExtensionByZero.derivedRestriction Y.ringCatSheaf (g ⁻¹ᵁ V)).Linear A :=
    Stacks.DerivedQCoh.derivedRestriction_linear Y (g ⁻¹ᵁ V) ((g.appTop).hom.comp φ)
  let : (Stacks.ExtensionByZero.derivedRestriction Y.ringCatSheaf
      ((g ⁻¹ᵁ U) ⊓ (g ⁻¹ᵁ V))).Linear A :=
    Stacks.DerivedQCoh.derivedRestriction_linear Y ((g ⁻¹ᵁ U) ⊓ (g ⁻¹ᵁ V))
      ((g.appTop).hom.comp φ)
  have hinf : (g ⁻¹ᵁ U) ⊓ (g ⁻¹ᵁ V) = g ⁻¹ᵁ (U ⊓ V) := TopologicalSpace.Opens.ext (by simp)
  have hcover : (g ⁻¹ᵁ U) ⊔ (g ⁻¹ᵁ V) = ⊤ := by
    have h1 : (g ⁻¹ᵁ U) ⊔ (g ⁻¹ᵁ V) = g ⁻¹ᵁ (U ⊔ V) := TopologicalSpace.Opens.ext (by simp)
    rw [h1, ← hg, Scheme.Hom.preimage_opensRange]
  have hr : ∀ W ≤ U ⊔ V, ((g ⁻¹ᵁ W).ι ≫ g).opensRange = W := fun W hW => by
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
      Scheme.Hom.image_preimage_eq_opensRange_inf, hg, inf_eq_right.mpr hW]
  have hrUV : (((g ⁻¹ᵁ U) ⊓ (g ⁻¹ᵁ V)).ι ≫ g).opensRange = U ⊓ V := by
    rw [hinf]
    exact hr _ (inf_le_left.trans le_sup_left)
  intro E E' hE hEq hE'q hsupp n α
  refine exists_pow_smul_eq_zero_of_cover Y.ringCatSheaf (g ⁻¹ᵁ U) (g ⁻¹ᵁ V) hcover a E E' n α
    (exists_pow_smul_eq_zero_restriction φ a g (g ⁻¹ᵁ U)
      (ihU _ _ (hr _ le_sup_left)) E E' hE hEq hE'q hsupp n _)
    (exists_pow_smul_eq_zero_restriction φ a g (g ⁻¹ᵁ V)
      (ihV _ _ (hr _ le_sup_right)) E E' hE hEq hE'q hsupp n _)
    (fun y => exists_pow_smul_eq_zero_restriction φ a g ((g ⁻¹ᵁ U) ⊓ (g ⁻¹ᵁ V))
      (ihUV _ _ hrUV) E E' hE hEq hE'q hsupp (n - 1) y)

/-! ### Tag 08EJ -/

/-- **[Stacks, Tag 08EJ] in the form the induction produces it**, for a shifted target and with
the scalars the global sections themselves. This is
`Stacks.AlgebraicGeometry.InductionPrinciple.induction_top`, the clause of [Stacks, Tag 08DR]
about the whole space, applied to the property of an open "the statement holds on every open
subscheme with that image"; its two clauses are
`Stacks.PowerTorsion.powerTorsionProperty_of_isAffineOpen` and
`Stacks.PowerTorsion.powerTorsionProperty_sup`, and the identity of `X` is the open immersion
with image the whole of `X`. -/
theorem powerTorsionProperty_top {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (a : Γ(X, ⊤)) : PowerTorsionProperty Γ(X, ⊤) X (RingHom.id Γ(X, ⊤)) a := by
  have hid : ((Scheme.Hom.appTop (𝟙 X)).hom).comp (RingHom.id Γ(X, ⊤)) =
      RingHom.id Γ(X, ⊤) := by simp
  have key : ∀ (Y : Scheme.{u}) (g : Y ⟶ X) [IsOpenImmersion g], g.opensRange = ⊤ →
      PowerTorsionProperty Γ(X, ⊤) Y ((g.appTop).hom.comp (RingHom.id Γ(X, ⊤))) a := by
    refine Stacks.AlgebraicGeometry.InductionPrinciple.induction_top
      (fun W => ∀ (Y : Scheme.{u}) (g : Y ⟶ X) [IsOpenImmersion g], g.opensRange = W →
        PowerTorsionProperty Γ(X, ⊤) Y ((g.appTop).hom.comp (RingHom.id Γ(X, ⊤))) a) ?_ ?_
    · intro W hW Y g _ hgr
      exact powerTorsionProperty_of_isAffineOpen _ a hW Y g hgr
    · intro U V _ _ hPU hPV hPUV Y g _ hgr
      exact powerTorsionProperty_sup _ a U V hPU hPV hPUV Y g hgr
  have h2 := key X (𝟙 X) (Scheme.Hom.opensRange_of_isIso (𝟙 X))
  rwa [hid] at h2

/-- **[Stacks, Tag 08EJ].** Let `X` be a quasi-compact quasi-separated scheme and let
`f ∈ Γ(X, 𝒪_X)`. Let `α : E ⟶ E'` be a morphism of `D_QCoh(𝒪_X)` such that `E` is perfect and
`E'` is supported on the closed subset `T = V(f)`, that is, the cohomology sheaves of `E'` have
vanishing stalks at every point where `f` does not vanish. Then `f ^ n • α = 0` for some
`n ≥ 0`.

The scalar acts through the `Γ(X, 𝒪_X)`-linear structure
`AlgebraicGeometry.Scheme.linearOfRingHom` of the identity ring map, which is a definition and
not an instance -- a scheme does not determine a base ring -- and so appears as a `letI` in the
statement.

This is `Stacks.PowerTorsion.powerTorsionProperty_top` at the degree `0`, the shift being
undone by the unitor of the shift. -/
@[stacks 08EJ]
theorem exists_pow_smul_eq_zero_of_isPerfect_of_cohomologySupportedOn_qcqs {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (f : Γ(X, ⊤)) (E E' : DerivedCategory X.Modules)
    (hE : IsPerfect (X := ringedSpace X) E)
    (hEq : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj E).IsQuasicoherent)
    (hE'q : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj E').IsQuasicoherent)
    (hsupp : CohomologySupportedOn X.ringCatSheaf ((X.basicOpen f : Set X)ᶜ) E')
    (α : E ⟶ E') :
    letI : Linear Γ(X, ⊤) X.Modules := Scheme.linearOfRingHom X Γ(X, ⊤) (RingHom.id Γ(X, ⊤))
    ∃ k : ℕ, f ^ k • α = 0 := by
  let : Linear Γ(X, ⊤) X.Modules := Scheme.linearOfRingHom X Γ(X, ⊤) (RingHom.id Γ(X, ⊤))
  set u := (shiftFunctorZero (DerivedCategory X.Modules) ℤ).app E' with hu
  obtain ⟨k, hk⟩ := powerTorsionProperty_top f E E' hE hEq hE'q hsupp 0 (α ≫ u.inv)
  refine ⟨k, ?_⟩
  have h0 : (f ^ k • (α ≫ u.inv)) ≫ u.hom = 0 := by rw [hk, Limits.zero_comp]
  rw [Linear.smul_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id] at h0
  exact h0

end Stacks.PowerTorsion

end
