module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.CoherentMul
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.InverseSections
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.MulIsomorphism
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Descent
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.Basic
public import StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumAffine
import StacksFrontier.RingTheory.Depth.RingEquiv

/-!
# The Picard group of a punctured spectrum and completion

Let `(A, 𝔪)` be a Noetherian local ring of depth at least two, let `A^` be its completion and let
`U`, resp. `U^`, be the punctured spectrum of `A`, resp. `A^`. Then `Pic(U) ⟶ Pic(U^)` is
injective. The proof runs through the corresponding statement for a faithfully flat base change of
a quasi-compact quasi-separated scheme with semilocal ring of global functions: the depth
hypothesis makes `Γ(U, 𝒪_U) = A`, which is local, and `U^` is the base change of `U` along
`Spec(A^) ⟶ Spec(A)`.

## Main definitions

* `Stacks.AlgebraicGeometry.PicardBaseChange.specCompletionMap`: the morphism
  `Spec(A^) ⟶ Spec(A)` induced by completion.
* `Stacks.AlgebraicGeometry.PicardBaseChange.puncturedSpectrumCompletionMap`: the induced
  morphism `U^ ⟶ U` of punctured spectra.
* `Stacks.AlgebraicGeometry.PicardBaseChange.globalSections`: a global section of a sheaf of
  modules, read as a compatible family of sections.

## Main results

* `Stacks.AlgebraicGeometry.PicardBaseChange.nonempty_iso_unit_of_tensorPairing_top` and
  `Stacks.AlgebraicGeometry.PicardBaseChange.isTrivial_of_globalSectionsMulNegOne_eq_one`: an
  invertible module carrying a global section whose product with a global section of the inverse
  tensor power is `1` is trivial.
* `Stacks.AlgebraicGeometry.PicardBaseChange.injective_schemePullbackClass_of_faithfullyFlat`:
  **Stacks 0CDY.** Faithfully flat base change is injective on the Picard group of a
  quasi-compact quasi-separated scheme with semilocal ring of global functions.
* `Stacks.AlgebraicGeometry.PicardBaseChange.isIso_puncturedSpectrum_ι_appTop`: for depth at
  least two the global functions on the punctured spectrum are the ring itself.
* `Stacks.AlgebraicGeometry.PicardBaseChange.isPullback_puncturedSpectrumCompletionMap`: the
  punctured spectrum of `A^` is the base change of the punctured spectrum of `A`.
* `Stacks.AlgebraicGeometry.PicardBaseChange`
  `.injective_schemePullbackClass_puncturedSpectrumCompletionMap`: **Stacks 0F2G.**

## Implementation notes

The Picard group is `Stacks.Picard.ofScheme` and pullback on it is
`Stacks.Picard.schemePullbackClass`, which are written against
`Stacks.SheafOfModules.IsInvertible`, while the three clauses of Tag 0CDX are written against
`AlgebraicGeometry.SheafOfModules.IsInvertible`; the two are exchanged by
`Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`.

Semilocality of the ring of global functions is finiteness of its maximal spectrum, and the
product of a section of `L` with a section of `L^{⊗ -1}` is
`Stacks.SheafOfModules.Invertible.globalSectionsMulNegOne`, Tag 01CU's coherent multiplication at
the exponents `(1, -1)`.

## References

* [Stacks Project, Tag 0F2G](https://stacks.math.columbia.edu/tag/0F2G)
* [Stacks Project, Tag 0CDY](https://stacks.math.columbia.edu/tag/0CDY)
* [Stacks Project, Tag 0CDX](https://stacks.math.columbia.edu/tag/0CDX)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.PicardBaseChange

open Stacks.RingedSpace (structureIsSheaf)
open Stacks.SheafOfModules (tensorPairing unitSection nonvanishingOpen
  mem_nonvanishingLocus_iff bijective_smul_eval_of_le_nonvanishingOpen
  nonempty_iso_unit_of_bijective_smul_on_cover isInvertible_unit isInvertible_tensorSheaf)
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk)
open Stacks.SheafOfModules.Invertible (tensorPower tensorPowerOneIso tensorPowerMulIsoNegOne
  globalSectionsMulNegOne tensorPowerModule tensorPower_isInvertible tensorProductLeftUnitor)
open Stacks.SheafOfModules.TensorSheafification (structureSheaf)
open scoped TensorProduct

/-! ### Trivializing an invertible module by a global section -/

/-- A global section of a sheaf of modules, read as a compatible family of sections. -/
noncomputable def globalSections {X : RingedSpace.{u, u}}
    (M : SheafOfModules.{u} (structureSheafRing X))
    (a : M.val.obj (Opposite.op (⊤ : Opens X.carrier))) : M.val.sections :=
  PresheafOfModules.sectionsMk (fun W => M.val.map (homOfLE (le_top (a := W.unop))).op a)
    fun {W V} f => by
      have h : (homOfLE (le_top (a := W.unop))).op ≫ f = (homOfLE (le_top (a := V.unop))).op :=
        Subsingleton.elim _ _
      exact (M.val.map_comp_apply _ f a).symm.trans (by rw [h])

/-- The family `globalSections M a` takes the value `a` on the whole space. -/
@[simp]
theorem globalSections_eval_top {X : RingedSpace.{u, u}}
    (M : SheafOfModules.{u} (structureSheafRing X))
    (a : M.val.obj (Opposite.op (⊤ : Opens X.carrier))) :
    (globalSections M a).eval (Opposite.op ⊤) = a := by
  change M.val.map (homOfLE (le_top (a := (⊤ : Opens X.carrier)))).op a = a
  rw [Subsingleton.elim (homOfLE (le_top (a := (⊤ : Opens X.carrier)))).op (𝟙 _)]
  exact M.val.map_id_apply _ a

/-- **A global section pairing to the unit section trivializes an invertible module.** By Tag
01CY the section trivializes `L` over its nonvanishing locus, and a global partner pairing to
`1` puts every point of the space in that locus. -/
theorem nonempty_iso_unit_of_tensorPairing_top {X : RingedSpace.{u, u}}
    [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
    {L N : SheafOfModules.{u} (structureSheafRing X)}
    [Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X).property L]
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj (L)).obj
      (N)) ≅ SheafOfModules.unit (structureSheafRing X))
    (a : L.val.obj (Opposite.op (⊤ : Opens X.carrier)))
    (b : N.val.obj (Opposite.op (⊤ : Opens X.carrier)))
    (hab : tensorPairing ψ ⊤ a b = unitSection X ⊤) :
    Nonempty (L ≅ SheafOfModules.unit (structureSheafRing X)) := by
  have hle : ∀ V : Opens X.carrier, V ≤ nonvanishingOpen L (globalSections L a) := by
    intro V x _
    exact (mem_nonvanishingLocus_iff ψ _ x).2
      ⟨⊤, Opens.mem_top x, b, by rwa [globalSections_eval_top]⟩
  exact nonempty_iso_unit_of_bijective_smul_on_cover L (globalSections L a)
    (fun _ : Unit => ⊤) (IsOpenCover.mk iSup_const)
    fun _ V _ => bijective_smul_eval_of_le_nonvanishingOpen L _ V (hle V)

/-- **An invertible module with a global section whose product with a global section of the
inverse tensor power is `1` is trivial.** The product is the coherent multiplication of Tag 01CU
at the exponents `(1, -1)`. -/
theorem isTrivial_of_globalSectionsMulNegOne_eq_one {Y : Scheme.{u}} (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (t : Γ(tensorPowerModule L (-1), ⊤))
    (hst : globalSectionsMulNegOne L s t = 1) :
    AlgebraicGeometry.SheafOfModules.IsTrivial Y.presheaf Y.ringCatSheaf.property L := by
  have hloc : ∀ x : Y.toRingedSpace.carrier, IsLocalRing (ringStalk Y.toRingedSpace x) :=
    Y.isLocalRing
  have hinv1 : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property
      (tensorPower Y.presheaf Y.ringCatSheaf.property L 1) :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      Y.presheaf Y.ringCatSheaf.property _).2
      (tensorPower_isInvertible Y.presheaf Y.ringCatSheaf.property L 1)
  obtain ⟨e⟩ := nonempty_iso_unit_of_tensorPairing_top (X := Y.toRingedSpace)
    (tensorPowerMulIsoNegOne Y.presheaf Y.ringCatSheaf.property L)
    (((tensorPowerOneIso Y.presheaf Y.ringCatSheaf.property L).inv.val.app
      (Opposite.op ⊤)).hom s) t hst
  exact ⟨(tensorPowerOneIso Y.presheaf Y.ringCatSheaf.property L).symm ≪≫ e⟩

/-! ### Invertible modules over a semilocal ring -/

/-- An invertible module over a ring with finitely many maximal ideals is free of rank one. -/
theorem nonempty_linearEquiv_of_invertible_of_finite_maximalSpectrum
    (R : Type u) [CommRing R] [Finite (MaximalSpectrum R)]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Invertible R M] :
    Nonempty (M ≃ₗ[R] R) := by
  rw [← Module.Invertible.free_iff_linearEquiv]
  refine Module.free_of_flat_of_finrank_eq R M 1 fun m => ?_
  let _ := Ideal.Quotient.field m.asIdeal
  exact Module.Invertible.finrank_eq_one ..

/-- A perfect pairing of an invertible module with another module over a ring with finitely many
maximal ideals takes the value `1` on a pure tensor. -/
theorem exists_tmul_eq_one (R : Type u) [CommRing R] [Finite (MaximalSpectrum R)]
    (M N : Type u) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Invertible R M] (e : M ⊗[R] N ≃ₗ[R] R) :
    ∃ (s : M) (t : N), e (s ⊗ₜ[R] t) = 1 := by
  obtain ⟨a⟩ := nonempty_linearEquiv_of_invertible_of_finite_maximalSpectrum R M
  let b : M ⊗[R] N ≃ₗ[R] N :=
    (TensorProduct.congr a (LinearEquiv.refl R N)).trans (TensorProduct.lid R N)
  let c : N ≃ₗ[R] R := b.symm.trans e
  refine ⟨a.symm 1, c.symm 1, ?_⟩
  calc e ((a.symm 1) ⊗ₜ[R] (c.symm 1))
      = c (b ((a.symm 1) ⊗ₜ[R] (c.symm 1))) := congrArg e (b.symm_apply_apply _).symm
    _ = c (c.symm 1) := congrArg c (by simp [b])
    _ = 1 := c.apply_symm_apply 1

/-! ### Triviality in the Picard group -/

/-- The structure sheaf is the neutral element of the Picard group. -/
theorem classOf_unit_eq_zero (X : RingedSpace.{u, u}) :
    Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X)
      (SheafOfModules.unit (structureSheaf X.presheaf (structureIsSheaf X)))
      (isInvertible_unit X.presheaf (structureIsSheaf X)) = 0 := by
  set c := Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X)
    (SheafOfModules.unit (structureSheaf X.presheaf (structureIsSheaf X)))
    (isInvertible_unit X.presheaf (structureIsSheaf X)) with hc
  have hcc : c + c = c := by
    rw [hc, Stacks.SheafOfModules.picardClass_tensorSheaf X.presheaf (structureIsSheaf X) _ _ _ _
      (@isInvertible_tensorSheaf _ _ _ X.presheaf (structureIsSheaf X) _ _ _ _
        (isInvertible_unit X.presheaf (structureIsSheaf X))
        (isInvertible_unit X.presheaf (structureIsSheaf X)))]
    exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
      ⟨tensorProductLeftUnitor X.presheaf (structureIsSheaf X) _⟩
  exact add_eq_left.mp hcc

/-- A Picard class is zero exactly when the invertible module representing it is trivial. -/
theorem classOf_eq_zero_iff_nonempty_iso_unit {X : RingedSpace.{u, u}}
    (L : SheafOfModules.{u} (structureSheaf X.presheaf (structureIsSheaf X)))
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf (structureIsSheaf X) L) :
    Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X) L hL = 0 ↔
      Nonempty (L ≅ SheafOfModules.unit (structureSheaf X.presheaf (structureIsSheaf X))) := by
  rw [← classOf_unit_eq_zero X]
  exact Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _

/-! ### Faithfully flat base change -/

/-- **Stacks Project, Tag 0CDY.** Let `A → B` be faithfully flat and let `X` be a quasi-compact,
quasi-separated scheme over `A` whose ring of global functions is semilocal. Then pullback to the
base change `X_B` is injective on Picard groups. -/
@[stacks 0CDY]
theorem injective_schemePullbackClass_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.FaithfullyFlat)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [CompactSpace X] [QuasiSeparatedSpace X]
    [Finite (MaximalSpectrum Γ(X, ⊤))] :
    Function.Injective (Stacks.Picard.schemePullbackClass
      (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) := by
  set g := pullback.fst f (Spec.map (CommRingCat.ofHom φ))
  intro x y hxy
  have hsub : Stacks.Picard.pullbackClass g.toLRSHom.toShHom (x - y) = 0 := by
    have := (Stacks.Picard.pullbackClassHom g.toLRSHom.toShHom).map_sub x y
    simp only [Stacks.Picard.pullbackClassHom_apply] at this
    rwa [this, sub_eq_zero]
  set L := Stacks.Picard.picardRepresentative X.toRingedSpace (x - y)
  have hLs : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureIsSheaf X.toRingedSpace) L.obj := L.property
  have hpull : Stacks.SheafOfModules.picardClass
      (pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf
      (structureIsSheaf (pullback f (Spec.map (CommRingCat.ofHom φ))).toRingedSpace)
      ((Stacks.RingedSpace.pullbackFunctor g.toLRSHom.toShHom).obj L.obj)
      (Stacks.RingedSpace.modulePullback_isInvertible_of g.toLRSHom.toShHom L.obj hLs) = 0 := by
    rwa [← Stacks.Picard.pullbackClass_classOf g.toLRSHom.toShHom L.obj hLs,
      Stacks.Picard.classOf_picardRepresentative]
  let M : X.Modules := L.obj
  have htrivM : AlgebraicGeometry.SheafOfModules.IsTrivial
      (pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf
      (pullback f (Spec.map (CommRingCat.ofHom φ))).ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj M) :=
    (classOf_eq_zero_iff_nonempty_iso_unit _ _).1 hpull
  have hMa : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      X.ringCatSheaf.property M :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      X.presheaf (structureIsSheaf X.toRingedSpace) L.obj).1 hLs
  obtain ⟨e, he⟩ := exists_mulEquiv_globalSections_of_faithfullyFlat_trivialization
    φ hφ f M htrivM
  have hinvM : Module.Invertible Γ(X, ⊤) Γ(M, ⊤) :=
    invertible_globalSections_of_faithfullyFlat_trivialization φ hφ f M htrivM
  obtain ⟨s, t, hst⟩ := exists_tmul_eq_one Γ(X, ⊤) Γ(M, ⊤)
    Γ(tensorPowerModule M (-1), ⊤) e
  rw [← sub_eq_zero, ← Stacks.Picard.classOf_picardRepresentative X.toRingedSpace (x - y)]
  exact (classOf_eq_zero_iff_nonempty_iso_unit _ _).2
    (isTrivial_of_globalSectionsMulNegOne_eq_one M s t ((he s t).symm.trans hst))

/-! ### The punctured spectrum of a Noetherian local ring and its completion -/

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- The morphism `Spec(A^) ⟶ Spec(A)` induced by the completion of a Noetherian local ring. -/
noncomputable def specCompletionMap :
    Spec (.of (AdicCompletion (maximalIdeal A) A)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion (maximalIdeal A) A)))

/-- A prime of the completion lies over the closed point exactly when it is the closed point. -/
theorem specCompletionMap_eq_closedPoint_iff
    (x : PrimeSpectrum (AdicCompletion (maximalIdeal A) A)) :
    (specCompletionMap A).base x = closedPoint A ↔
      x = closedPoint (AdicCompletion (maximalIdeal A) A) := by
  constructor
  · intro hx
    have hcomap : x.asIdeal.comap (algebraMap A (AdicCompletion (maximalIdeal A) A)) =
        maximalIdeal A := congrArg PrimeSpectrum.asIdeal hx
    refine PrimeSpectrum.ext (le_antisymm (le_maximalIdeal_of_isPrime x.asIdeal) ?_)
    change maximalIdeal (AdicCompletion (maximalIdeal A) A) ≤ x.asIdeal
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.map_le_iff_le_comap.2 hcomap.ge
  · rintro rfl
    refine PrimeSpectrum.ext ?_
    change (maximalIdeal (AdicCompletion (maximalIdeal A) A)).comap
      (algebraMap A (AdicCompletion (maximalIdeal A) A)) = maximalIdeal A
    rw [IsLocalRing.maximalIdeal_comap]

/-- The punctured spectrum of the completion is the preimage of the punctured spectrum. -/
theorem specCompletionMap_preimage_puncturedSpectrum :
    (specCompletionMap A) ⁻¹ᵁ (Stacks.Divisors.puncturedSpectrum A) =
      Stacks.Divisors.puncturedSpectrum (AdicCompletion (maximalIdeal A) A) := by
  refine Opens.ext ?_
  ext x
  change (specCompletionMap A).base x ∈ ({closedPoint A}ᶜ : Set (PrimeSpectrum A)) ↔
    x ∈ ({closedPoint (AdicCompletion (maximalIdeal A) A)}ᶜ :
      Set (PrimeSpectrum (AdicCompletion (maximalIdeal A) A)))
  exact not_congr (specCompletionMap_eq_closedPoint_iff A x)

/-- The morphism `U^ ⟶ U` of punctured spectra induced by the completion. -/
noncomputable def puncturedSpectrumCompletionMap :
    (Stacks.Divisors.puncturedSpectrum (AdicCompletion (maximalIdeal A) A)).toScheme ⟶
      (Stacks.Divisors.puncturedSpectrum A).toScheme :=
  (specCompletionMap A).resLE (Stacks.Divisors.puncturedSpectrum A)
    (Stacks.Divisors.puncturedSpectrum (AdicCompletion (maximalIdeal A) A))
    (specCompletionMap_preimage_puncturedSpectrum A).ge

/-- The punctured spectrum of the completion is the base change of the punctured spectrum along
`Spec(A^) ⟶ Spec(A)`. -/
theorem isPullback_puncturedSpectrumCompletionMap :
    IsPullback (puncturedSpectrumCompletionMap A)
      (Stacks.Divisors.puncturedSpectrum (AdicCompletion (maximalIdeal A) A)).ι
      (Stacks.Divisors.puncturedSpectrum A).ι (specCompletionMap A) := by
  have hpre := specCompletionMap_preimage_puncturedSpectrum A
  refine (isPullback_morphismRestrict (specCompletionMap A)
    (Stacks.Divisors.puncturedSpectrum A)).of_iso
    ((Spec (.of (AdicCompletion (maximalIdeal A) A))).isoOfEq hpre)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ (by simp) (by simp) (by simp)
  refine (cancel_mono (Stacks.Divisors.puncturedSpectrum A).ι).1 ?_
  calc
    (specCompletionMap A ∣_ Stacks.Divisors.puncturedSpectrum A) ≫
          (Stacks.Divisors.puncturedSpectrum A).ι =
        (specCompletionMap A ⁻¹ᵁ Stacks.Divisors.puncturedSpectrum A).ι ≫
          specCompletionMap A :=
      morphismRestrict_ι (specCompletionMap A) (Stacks.Divisors.puncturedSpectrum A)
    _ = ((Spec (.of (AdicCompletion (maximalIdeal A) A))).isoOfEq hpre).hom ≫
          puncturedSpectrumCompletionMap A ≫ (Stacks.Divisors.puncturedSpectrum A).ι := by
      rw [← (Spec (.of (AdicCompletion (maximalIdeal A) A))).isoOfEq_hom_ι hpre,
        Category.assoc]
      exact congrArg _ (Scheme.Hom.resLE_comp_ι (specCompletionMap A) _).symm

/-! ### The global functions on a punctured spectrum -/

/-- The stalk of the structure sheaf of `Spec A` at the closed point of a local ring `A` is `A`
itself. -/
noncomputable def closedPointStalkEquiv :
    A ≃+* (Spec (.of A)).presheaf.stalk (closedPoint A) :=
  ((IsLocalization.atUnits A (maximalIdeal A).primeCompl
    (S := Localization.AtPrime (maximalIdeal A))
    fun _ hx => notMem_maximalIdeal.mp hx).toRingEquiv).trans
    (Spec.stalkIso (.of A) (closedPoint A)).commRingCatIsoToRingEquiv.symm

omit [IsNoetherianRing A] in
/-- The depth of the local ring `A` is the depth of the structure sheaf of `Spec A` at every
closed point. -/
theorem le_depth_stalk_of_isClosed {d : ℕ∞}
    (hdepth : d ≤ Module.depth A (maximalIdeal A) A)
    (y : Spec (.of A)) (hy : IsClosed ({y} : Set (Spec (.of A)))) :
    d ≤ Module.depth ((Spec (.of A)).presheaf.stalk y)
      (maximalIdeal ((Spec (.of A)).presheaf.stalk y))
      ((Spec (.of A)).presheaf.stalk y) := by
  have hm : y.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hy
  obtain rfl : y = closedPoint A := PrimeSpectrum.ext ((isMaximal_iff (R := A)).mp hm)
  have := (Spec (.of A)).isLocalRing (closedPoint A)
  exact hdepth.trans (Module.depth_self_eq_of_ringEquiv (closedPointStalkEquiv A)).le

/-- **The global functions on the punctured spectrum of a Noetherian local ring of depth at least
two are the ring itself.** The restriction map from the global functions on `Spec A` is an
isomorphism. -/
theorem isIso_puncturedSpectrum_ι_appTop
    (hdepth : 2 ≤ Module.depth A (maximalIdeal A) A) :
    IsIso (Stacks.Divisors.puncturedSpectrum A).ι.appTop := by
  obtain ⟨e, he⟩ := exists_iso_spec_sections_punctured_spectrum A (𝟙 (Spec (.of A)))
    (le_depth_stalk_of_isClosed A hdepth)
  have hfac : IsIso (Spec.map ((Spec (.of A)).presheaf.map
      (homOfLE (show 𝟙 (Spec (.of A)) ⁻¹ᵁ
        ⟨({closedPoint A} : Set (PrimeSpectrum A))ᶜ,
          (isClosed_singleton_closedPoint A).isOpen_compl⟩ ≤ ⊤ from le_top)).op)) :=
    @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ e.isIso_hom
      (IsAffine.affine : IsIso (Spec (.of A)).toSpecΓ) he
  have hmap : IsIso ((Spec (.of A)).presheaf.map
      (homOfLE (show Stacks.Divisors.puncturedSpectrum A ≤ ⊤ from le_top)).op) :=
    (ConcreteCategory.isIso_iff_bijective _).2 ((isIso_SpecMap_iff).1 hfac)
  refine @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _
    (Stacks.Divisors.puncturedSpectrum A).topIso.isIso_hom hmap ?_
  let f : (Opposite.op (⊤ : (Spec (.of A)).Opens)) ⟶
      Opposite.op ((Stacks.Divisors.puncturedSpectrum A).ι ''ᵁ
        (⊤ : (Stacks.Divisors.puncturedSpectrum A).toScheme.Opens)) :=
    (homOfLE le_top).op
  let g : Opposite.op ((Stacks.Divisors.puncturedSpectrum A).ι ''ᵁ
      (⊤ : (Stacks.Divisors.puncturedSpectrum A).toScheme.Opens)) ⟶
      Opposite.op (Stacks.Divisors.puncturedSpectrum A) :=
    (eqToHom (Stacks.Divisors.puncturedSpectrum A).ι_image_top.symm).op
  have hfg : f ≫ g = (homOfLE le_top).op := Subsingleton.elim _ _
  simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← hfg]
  convert ((Spec (.of A)).presheaf.map_comp f g).symm using 1
  congr 1

/-- **Stacks Project, Tag 0F2G.** Let `(A, 𝔪)` be a Noetherian local ring of depth at least two,
let `A^` be its completion and let `U`, resp. `U^`, be the punctured spectrum of `A`, resp. `A^`.
Then `Pic(U) ⟶ Pic(U^)` is injective. -/
@[stacks 0F2G]
theorem injective_schemePullbackClass_puncturedSpectrumCompletionMap
    (hdepth : 2 ≤ Module.depth A (maximalIdeal A) A) :
    Function.Injective
      (Stacks.Picard.schemePullbackClass (puncturedSpectrumCompletionMap A)) := by
  have hcompact : CompactSpace (Stacks.Divisors.puncturedSpectrum A).toScheme :=
    isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact
      ((Stacks.Divisors.puncturedSpectrum A).1 : Set (PrimeSpectrum A)))
  have hiso : IsIso ((Scheme.ΓSpecIso (.of A)).inv ≫
      (Stacks.Divisors.puncturedSpectrum A).ι.appTop) :=
    IsIso.comp_isIso' inferInstance (isIso_puncturedSpectrum_ι_appTop A hdepth)
  have hlocal : IsLocalRing Γ((Stacks.Divisors.puncturedSpectrum A).toScheme, ⊤) :=
    (asIso ((Scheme.ΓSpecIso (.of A)).inv ≫
      (Stacks.Divisors.puncturedSpectrum A).ι.appTop)).commRingCatIsoToRingEquiv.isLocalRing
  have hff : (algebraMap A (AdicCompletion (maximalIdeal A) A)).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.2
      (AdicCompletion.faithfullyFlat_of_le_ringJacobson (maximalIdeal A)
        (IsLocalRing.ringJacobson_eq_maximalIdeal A).ge)
  have hbase : Function.Injective (Stacks.Picard.schemePullbackClass
      (pullback.fst (Stacks.Divisors.puncturedSpectrum A).ι (specCompletionMap A))) :=
    injective_schemePullbackClass_of_faithfullyFlat
      (algebraMap A (AdicCompletion (maximalIdeal A) A)) hff
      (Stacks.Divisors.puncturedSpectrum A).ι
  set e := (isPullback_puncturedSpectrumCompletionMap A).isoPullback with he
  have hinj : Function.Injective (Stacks.Picard.schemePullbackClass e.hom) := by
    refine Function.LeftInverse.injective
      (g := Stacks.Picard.schemePullbackClass e.inv) fun z => ?_
    rw [Stacks.Picard.schemePullbackClass_comp, e.inv_hom_id,
      Stacks.Picard.schemePullbackClass_id]
  intro x y hxy
  rw [← (isPullback_puncturedSpectrumCompletionMap A).isoPullback_hom_fst, ← he,
    ← Stacks.Picard.schemePullbackClass_comp, ← Stacks.Picard.schemePullbackClass_comp] at hxy
  exact hbase (hinj hxy)

end Stacks.AlgebraicGeometry.PicardBaseChange

end
