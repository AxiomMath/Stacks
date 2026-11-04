module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsCoefficientChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.ProjectionMapLocalization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.TensorBaseChangeReduction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackMonoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowCanonical
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOnKFlatComplexes
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsTorAmplitude
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 0F1J: from `ℤ/nℤ` to `𝔽_ℓ`

The third paragraph of the proof of [Stacks, Tag 0F1J]: for `F` a single sheaf `𝒢` of
`ℤ/nℤ`-modules, annihilated by some `m ∣ n`, the sequences `0 → 𝒢[ℓ] → 𝒢 → 𝒢/𝒢[ℓ] → 0` reduce
to `𝒢` annihilated by a prime `ℓ ∣ n`, and there

`p⁻¹E ⊗^L_{ℤ/n} (f')⁻¹Rg_*𝒢 = p⁻¹(E ⊗^L_{ℤ/n} 𝔽_ℓ) ⊗^L_{𝔽_ℓ} (f')⁻¹Rg_*𝒢`,

similarly for the other term, which reduces to sheaves of `𝔽_ℓ`-vector spaces.

* **Dévissage** (`forall_of_nsmul_id_eq_zero`): a property of objects of an abelian category,
  true at zero and closed under extensions, holds at every object annihilated by a divisor of
  `n` as soon as it holds at those annihilated by a prime divisor of `n`. For Tag 0F1J the
  property is invertibility of the canonical map at every shift of `𝒢[0]`, closed under
  extensions because both sides are exact functors of `F`
  (`CategoryTheory.NatTrans.isoLocusAtShifts`).
* **Change of coefficients.** A sheaf annihilated by `ℓ` is the restriction of scalars
  `Rc_*𝒢'` of a sheaf `𝒢'` of `𝔽_ℓ`-modules (`exists_coefficientPushforward_iso`), restriction
  of scalars commutes with inverse images (`coefficientPushforwardPullbackToposIso`), and the
  projection map of `h` over `ℤ/n` at `(p⁻¹E, e⁻¹Rc_*𝒢')` is read on the one over `𝔽_ℓ` at
  `(Lc^*p⁻¹E, e⁻¹𝒢') = (p⁻¹Lc^*E, e⁻¹𝒢')` by
  `Stacks.EtaleCohomology.EtaleCoefficients.isIso_projectionMap_coefficientPushforward_of_isIso`.
  `Lc^*E` keeps the Tor amplitude of `E` (`hasTorAmplitudeGE_coefficientPullback_obj`), so the
  case `n = ℓ` (`isIso_tensorBaseChangeMap_of_derivedBaseChangeHolds`) applies.

## Main results

* `exists_coefficientPushforward_iso` — a sheaf of `ℤ/nℤ`-modules annihilated by `ℓ ∣ n` is a
  restriction of scalars.
* `forall_of_nsmul_id_eq_zero` — the dévissage in the torsion order.
* `hasTorAmplitudeGE_coefficientPullback_obj` — change of coefficients preserves Tor amplitude.

The projection formula of the change of coefficients and the assembly of Tag 0F1J for
`ℤ/nℤ`-coefficients are in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsCoefficientProjection`.

## References

* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace Stacks.EtaleCohomology.BaseChangeOverField

/-- **Derived base change for sheaves annihilated by `n` gives it for sheaves annihilated by a
divisor of `n`**: a sheaf annihilated by `m ∣ n` is annihilated by `n`. -/
theorem DerivedBaseChangeHolds.of_dvd {X S : Scheme.{u}} {f : X ⟶ S} {n m : ℤ}
    (hf : DerivedBaseChangeHolds f n) (hmn : m ∣ n) : DerivedBaseChangeHolds f m := by
  intro S' X' T Y s p f' hp g h e sq _ _ F hF
  refine hf s p f' hp g h e sq F fun U x => ?_
  obtain ⟨k, rfl⟩ := hmn
  rw [mul_comm, mul_smul, hF U x, smul_zero]

end Stacks.EtaleCohomology.BaseChangeOverField

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `derivedPullback` (`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/
-- StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/AdjunctionForRingedTopoi.lean:394`) is stated for the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

-- The imports bring `SheafOfModules.hasDerivedCategory`
-- (`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean:155`), the locally small model, which
-- would otherwise be found before `HasDerivedCategory.standard`.

section Helpers

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

/-- **Change of coefficients preserves Tor amplitude**: a K-flat representative with flat terms
vanishing below `a` pulls back to one (Stacks 0G7E), and computes the derived pullback
(Stacks 06YY). -/
theorem hasTorAmplitudeGE_coefficientPullback_obj {X : Scheme.{u}} (E : DerivedModules Λ X)
    (a : ℤ) (hE : HasTorAmplitudeGE Λ E a) :
    HasTorAmplitudeGE Λ' ((coefficientPullback φ X).obj E) a := by
  obtain ⟨K, hKflat, hflat, hzero, ⟨e⟩, hpull⟩ :=
    Stacks.SheafOfModules.exists_pullbackStable_kFlatRepresentative_of_hasTorAmplitudeGE
      (X := (ringedTopos Λ X).toRingedSite) E a hE
  obtain ⟨hpKflat, -⟩ := hpull (ringedTopos Λ' X) (coefficientHom φ X)
    (isMorphismOfSites_coefficientHom φ X)
  have : (coefficientHom φ X).pushforwardTopos.Additive :=
    RingedToposSiteHom.pushforwardTopos_additive _
  have : (coefficientHom φ X).pullbackTopos.Additive :=
    Adjunction.left_adjoint_additive (coefficientHom φ X).pullbackPushforwardAdjunctionTopos
  refine Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeGE_of_kFlatRepresentative
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct (ringedTopos Λ' X).toRingedSite) _
    a ((Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex (coefficientHom φ X)).obj K)
    hpKflat (fun i hi => Functor.map_isZero _ (hzero i hi)) ?_
  exact (Stacks.Sheaves.DerivedPullback.flatPullbackIso (coefficientHom φ X)
    (isMorphismOfSites_coefficientHom φ X) K hKflat hflat).symm ≪≫
      (coefficientPullback φ X).mapIso e

/-- Restriction of scalars of sheaves of modules preserves finite limits. -/
instance preservesFiniteLimits_coefficientHom_pushforwardTopos (Z : Scheme.{u}) :
    PreservesFiniteLimits (coefficientHom φ Z).pushforwardTopos :=
  inferInstanceAs (PreservesFiniteLimits
    (_root_.SheafOfModules.restrictScalars.{u + 1} (coefficientHom φ Z).fSharpRing))

/-- Restriction of scalars of sheaves of modules preserves finite colimits. -/
instance preservesFiniteColimits_coefficientHom_pushforwardTopos (Z : Scheme.{u}) :
    PreservesFiniteColimits (coefficientHom φ Z).pushforwardTopos :=
  inferInstanceAs (PreservesFiniteColimits
    (_root_.SheafOfModules.restrictScalars.{u + 1} (coefficientHom φ Z).fSharpRing))

/-- Restriction of scalars of sheaves of modules is additive. -/
instance additive_coefficientHom_pushforwardTopos (Z : Scheme.{u}) :
    (coefficientHom φ Z).pushforwardTopos.Additive :=
  RingedToposSiteHom.pushforwardTopos_additive _

/-- **The derived restriction of scalars is restriction of scalars applied degreewise**:
restriction of scalars is exact, so the functor it induces on derived categories is a right
derived functor of it, as is `Rc_*`. -/
def coefficientPushforwardIsoMapDerived (Z : Scheme.{u}) :
    coefficientPushforward φ Z ≅ (coefficientHom φ Z).pushforwardTopos.mapDerivedCategory :=
  haveI := Functor.isRightDerivedFunctor_mapDerivedCategory_of_exact
    (coefficientHom φ Z).pushforwardTopos
  Functor.rightDerivedUnique _ _ (derivedPushforwardUnit (coefficientHom φ Z))
    (coefficientHom φ Z).pushforwardTopos.mapDerivedCategoryFactorsh.inv
    (HomotopyCategory.quasiIso (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ' Z).O)) (ComplexShape.up ℤ))

/-- The derived restriction of scalars of a sheaf placed in degree `j` is its restriction of
scalars placed in degree `j`. -/
def coefficientPushforwardSingleIso (Z : Scheme.{u}) (j : ℤ)
    (Q : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ' Z).O)) :
    (coefficientPushforward φ Z).obj ((DerivedCategory.singleFunctor _ j).obj Q) ≅
      (DerivedCategory.singleFunctor _ j).obj ((coefficientHom φ Z).pushforwardTopos.obj Q) :=
  (coefficientPushforwardIsoMapDerived φ Z).app _ ≪≫
    ((coefficientHom φ Z).pushforwardTopos.mapDerivedCategorySingleFunctor j).app Q

/-- Restriction of scalars does not change the underlying abelian sheaf. -/
def etaleToSheafCoefficientPushforwardIso (Z : Scheme.{u}) :
    (coefficientHom φ Z).pushforwardTopos ⋙ etaleToSheaf Λ Z ≅ etaleToSheaf Λ' Z :=
  Iso.refl _

end Helpers

section Single

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The inverse image of a sheaf placed in degree `j` is its inverse image placed in degree
`j`**, for every ring of coefficients: the inverse image of sheaves of `Λ̲`-modules is exact, so
`f⁻¹` is the functor it induces on derived categories. -/
def pullbackObjSingleFunctorObjIsoOfExact {X Y : Scheme.{u}} (f : X ⟶ Y) (j : ℤ)
    (G : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ Y).O)) :
    (pullback Λ f).obj ((DerivedCategory.singleFunctor _ j).obj G) ≅
      (DerivedCategory.singleFunctor _ j).obj ((ringedToposHom Λ f).pullbackTopos.obj G) :=
  (Stacks.Sheaves.DerivedPullback.derivedPullbackIsoMapDerived (ringedToposHom Λ f)).app _ ≪≫
    ((ringedToposHom Λ f).pullbackTopos.mapDerivedCategorySingleFunctor j).app G

end Single

section ZMod

/-- The reduction `ℤ/nℤ ⟶ ℤ/ℓℤ` for `ℓ ∣ n`, on the coefficient rings `ULift (ZMod -)`. -/
def zmodULiftRingHom {n ℓ : ℕ} (hℓ : ℓ ∣ n) :
    ULift.{u + 1} (ZMod n) →+* ULift.{u + 1} (ZMod ℓ) :=
  (ULift.ringEquiv.symm : ZMod ℓ ≃+* ULift.{u + 1} (ZMod ℓ)).toRingHom.comp
    ((ZMod.castHom hℓ (ZMod ℓ)).comp ULift.ringEquiv.toRingHom)

variable {n ℓ : ℕ} (hℓ : ℓ ∣ n)

/-- **Restriction of scalars from `ℤ/ℓ` to `ℤ/n` commutes with inverse images**, on sheaves:
both underlying abelian sheaves are the abelian inverse image, and the underlying abelian sheaf
is fully faithful for `ℤ/nℤ`-coefficients. -/
def coefficientPushforwardPullbackToposIso {Y T : Scheme.{u}} (e : Y ⟶ T)
    (G' : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod ℓ)) T).O)) :
    (coefficientHom (zmodULiftRingHom hℓ) Y).pushforwardTopos.obj
        ((ringedToposHom (ULift.{u + 1} (ZMod ℓ)) e).pullbackTopos.obj G') ≅
      (ringedToposHom (ULift.{u + 1} (ZMod n)) e).pullbackTopos.obj
        ((coefficientHom (zmodULiftRingHom hℓ) T).pushforwardTopos.obj G') :=
  (etaleToSheafZModFullyFaithful n Y).preimageIso
    ((etaleToSheafCoefficientPushforwardIso (zmodULiftRingHom hℓ) Y).app _ ≪≫
      (pullbackEtaleToSheafIso ℓ e).app G' ≪≫
      (smallEtalePullbackAb e).mapIso
        ((etaleToSheafCoefficientPushforwardIso (zmodULiftRingHom hℓ) T).app G').symm ≪≫
      ((pullbackEtaleToSheafIso n e).app _).symm)

/-- **A sheaf of `ℤ/nℤ̲`-modules annihilated by `ℓ ∣ n` is the restriction of scalars of a sheaf
of `ℤ/ℓℤ̲`-modules.** -/
theorem exists_coefficientPushforward_iso {T : Scheme.{u}}
    (G : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod n)) T).O)) (hG : ℓ • 𝟙 G = 0) :
    ∃ G' : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (ringedTopos (ULift.{u + 1} (ZMod ℓ)) T).O),
      Nonempty ((coefficientHom (zmodULiftRingHom hℓ) T).pushforwardTopos.obj G' ≅ G) := by
  have h₁ : ℓ • 𝟙 ((etaleToSheaf (ULift.{u + 1} (ZMod n)) T).obj G) = 0 :=
    nsmul_id_map_eq_zero ℓ _ hG
  obtain ⟨G', ⟨e⟩⟩ := (mem_essImage_etaleToSheaf_iff ℓ T _).2 h₁
  exact ⟨G', ⟨(etaleToSheafZModFullyFaithful n T).preimageIso
    ((etaleToSheafCoefficientPushforwardIso (zmodULiftRingHom hℓ) T).app G' ≪≫ e)⟩⟩

end ZMod

section Devissage

variable {C : Type*} [Category* C] [Abelian C]

/-- **The dévissage of the proof of [Stacks, Tag 0F1J] in the torsion order.** Let `P` be a
property of objects of an abelian category, true at zero objects and closed under extensions. If
`P` holds at every object annihilated by a prime `ℓ ∣ n`, it holds at every object annihilated by
a divisor `m` of `n ≠ 0`: for a prime `ℓ ∣ m`, `0 → G[ℓ] → G → G/G[ℓ] → 0` is short exact,
`G[ℓ]` is annihilated by `ℓ` and `G/G[ℓ]` by `m/ℓ`. -/
@[sga "7 XIII 2.3.1" "partial"]
theorem forall_of_nsmul_id_eq_zero (P : C → Prop) (hzero : ∀ G, IsZero G → P G)
    (hext : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂) (n : ℕ)
    (hn : n ≠ 0) (hprime : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ∀ G : C, ℓ • 𝟙 G = 0 → P G) :
    ∀ m : ℕ, m ∣ n → ∀ G : C, m • 𝟙 G = 0 → P G := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm G hG
  rcases Nat.lt_or_ge m 2 with hlt | hge
  · interval_cases m
    · exact absurd (Nat.eq_zero_of_zero_dvd hm) hn
    · exact hzero G ((IsZero.iff_id_eq_zero G).2 (by simpa using hG))
  · obtain ⟨ℓ, hℓ, hℓm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
    let S := ShortComplex.mk (kernel.ι (ℓ • 𝟙 G)) (cokernel.π (kernel.ι (ℓ • 𝟙 G)))
      (cokernel.condition _)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
    refine hext S hS ?_ ?_
    · refine hprime ℓ hℓ (hℓm.trans hm) _ ?_
      rw [← cancel_mono (kernel.ι (ℓ • 𝟙 G)), Preadditive.nsmul_comp, Category.id_comp,
        zero_comp]
      simpa [Preadditive.comp_nsmul] using kernel.condition (ℓ • 𝟙 G)
    · obtain ⟨k, rfl⟩ := hℓm
      have hk : 0 < k := Nat.pos_of_ne_zero fun h => by simp [h] at hge
      have hkm : k < ℓ * k := by nlinarith [hℓ.two_le]
      refine ih k hkm (dvd_trans (Dvd.intro_left _ rfl) hm) _ ?_
      have hl : (k • 𝟙 G) ≫ (ℓ • 𝟙 G) = 0 := by
        rw [Preadditive.nsmul_comp, Category.id_comp, smul_smul, mul_comm, hG]
      rw [← cancel_epi (cokernel.π (kernel.ι (ℓ • 𝟙 G))), comp_zero, Preadditive.comp_nsmul,
        Category.comp_id, ← Category.id_comp (cokernel.π _), ← Preadditive.nsmul_comp,
        ← kernel.lift_ι (ℓ • 𝟙 G) (k • 𝟙 G) hl, Category.assoc, cokernel.condition, comp_zero]

end Devissage

section Annihilation

/-- Every sheaf of `ℤ/nℤ̲`-modules is annihilated by `n`. -/
theorem nsmul_id_eq_zero_zmod (n : ℕ) {T : Scheme.{u}}
    (G : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod n)) T).O)) : n • 𝟙 G = 0 := by
  have h₁ : n • 𝟙 ((etaleToSheaf (ULift.{u + 1} (ZMod n)) T).obj G) = 0 :=
    (mem_essImage_etaleToSheaf_iff n T _).1 ⟨G, ⟨Iso.refl _⟩⟩
  refine (etaleToSheaf (ULift.{u + 1} (ZMod n)) T).map_injective ?_
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
  exact h₁

end Annihilation

end Stacks.EtaleCohomology.EtaleCoefficients

end
