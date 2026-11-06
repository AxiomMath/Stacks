module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.AlgebraicGeometry.AmpleH1Vanishing.SectionsEpi
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.UniformVanishing
public import StacksFrontier.AlgebraicGeometry.ProperCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CoherentFiniteness
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.EulerCharacteristic
public import StacksFrontier.Homology.DerivedCategory.RightDerivedInjectiveModel
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.KTheory.SerreQuotient
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.Assembled

/-!
# The Euler characteristic of a coherent module and its higher direct images

Let `k` be a field, let `f : Y ⟶ X` be a morphism of schemes proper over `k` and let `G` be a
coherent `𝒪_Y`-module. Then `χ(Y, G) = ∑ᵢ (-1)ⁱ χ(X, Rⁱf_*G)`, the sum being over the
nonnegative degrees, as in the definition of the Euler characteristic.

## Main results

* `AlgebraicGeometry.eulerCharacteristic_eq_finsum_higherDirectImage_of_hypotheses`:
  **[Stacks, Tag 0BEK]**, with [Stacks, Tag 02O5] and [Stacks, Tag 02O6] as named hypotheses.

Both hypotheses are theorems of this repository, and
`StacksFrontier.AlgebraicGeometry.Variety.EulerChar.ProperPushforwardUnconditional` discharges them,
giving [Stacks, Tag 0BEK] outright as
`AlgebraicGeometry.eulerCharacteristic_eq_finsum_higherDirectImage`. That is a separate module
because the proof below is carried out against the locally small derived categories of
`StacksFrontier.Homology.DerivedCategory.LocallySmall`, whereas the two witnesses are proved
against `CategoryTheory.HasDerivedCategory.standard` and their files raise it to the front of
instance search; importing them here would re-elaborate the Leray spectral sequence below at the
other derived category.

## Implementation notes

The structure morphisms of `X` and `Y` to the spectrum of the field are explicit, those of `Y`
being the composite `f ≫ g`; properness of `f` and local Noetherianness of `X` are therefore
derived from them rather than assumed. Each `Rⁱf_*G` is coherent only by
[Stacks, Tag 02O5], so its coherence — the instance the Euler characteristic of `Rⁱf_*G`
requires — has to be named in the statement; here it is named by the hypothesis `h02O5`, which
is `AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherent`. The second hypothesis
`h02O6` is `AlgebraicGeometry.CohomologyFiniteDimensionalOverField`, that is
[Stacks, Tag 02O6] over a field base, the shape used by
`StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CoherentFiniteness`; it is what makes the
terms of the second page of the spectral sequence below finite-dimensional.

The route is the source's. The Leray spectral sequence of
`Stacks.Cohomology.LerayCard.leraySpectralSequence` ([Stacks, Tag 01F2]) has
`E₂^{p,q} = H^p(X, R^qf_*G)` and abuts to `H^{p+q}(Y, G)`; the uniform vanishing of
[Stacks, Tag 01XJ], applied to `f` and to `g`, confines the nonzero terms of that page to a
rectangle; and the alternating sum of the classes of the terms of a page in the Grothendieck
group of the finite-dimensional objects is the alternating sum of the classes of the abutment.
That last step is the bookkeeping of [Stacks, Tag 0BDW], carried out here for a spectral
sequence presented by `CategoryTheory.SpectralSequence.AbutsTo` rather than by a filtered
complex, which is the presentation the Leray spectral sequence comes with. Taking dimensions
over `k` is the additive map `KZero → ℤ` obtained from the rank-nullity theorem.

## References

* [Stacks Project, Tag 0BEK](https://stacks.math.columbia.edu/tag/0BEK)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 0BDW](https://stacks.math.columbia.edu/tag/0BDW)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

-- The additivity of the pushforward of modules is a `local instance` in its own file and so is
-- visible but not available to instance search here until re-registered.
attribute [local instance] Stacks.Cohomology.DerivedPushforwardSections.modulePushforwardAdditive

private local instance hasDerivedCategoryModuleCat (R : Type u) [Ring R] :
    HasDerivedCategory (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

private def finiteDimensionalOverFieldProperty (k R : Type u) [Field k] [Ring R]
    (φ : k →+* R) : ObjectProperty (ModuleCat.{u} R) := fun V =>
  Module.Finite k (↑((ModuleCat.restrictScalars.{u} φ).obj V))

private instance finiteDimensionalOverFieldProperty_serre (k R : Type u) [Field k] [Ring R]
    (φ : k →+* R) :
    (finiteDimensionalOverFieldProperty k R φ).IsSerreClass where
  exists_zero := ⟨ModuleCat.of R (Fin 0 → R), ModuleCat.isZero_of_subsingleton _, by
      let F := ModuleCat.restrictScalars.{u} φ
      let M := ↑(F.obj (ModuleCat.of R (Fin 0 → R)))
      have hsub : Subsingleton M := ⟨fun x y => funext fun i => Fin.elim0 i⟩
      let e : (Fin 0 → k) →ₗ[k] M := 0
      exact Module.Finite.of_surjective e fun x => ⟨0, hsub.elim _ _⟩⟩
  prop_of_mono := by
    let F := ModuleCat.restrictScalars.{u} φ
    intro X Y f hf hY
    let : Module.Finite k (↑(F.obj Y)) := hY
    change Module.Finite k (↑(F.obj X))
    exact Module.Finite.of_injective (F.map f).hom
      (ModuleCat.mono_iff_injective f |>.mp hf)
  prop_of_epi := by
    let F := ModuleCat.restrictScalars.{u} φ
    intro X Y f hf hX
    let : Module.Finite k (↑(F.obj X)) := hX
    change Module.Finite k (↑(F.obj Y))
    exact Module.Finite.of_surjective (F.map f).hom
      (ModuleCat.epi_iff_surjective f |>.mp hf)
  prop_X₂_of_shortExact := by
    let F := ModuleCat.restrictScalars.{u} φ
    let : PreservesFiniteLimits F := ⟨fun _ _ _ => ⟨inferInstance⟩⟩
    let : PreservesFiniteColimits F := ⟨fun _ _ _ => ⟨inferInstance⟩⟩
    intro S hS h₁ h₃
    let : Module.Finite k (↑(F.obj S.X₁)) := h₁
    let : Module.Finite k (↑(F.obj S.X₃)) := h₃
    change Module.Finite k (↑(F.obj S.X₂))
    let T := S.map F
    have hT : T.ShortExact := hS.map_of_exact F
    have hex : Function.Exact T.f.hom T.g.hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT.exact
    have hsur : Function.Surjective T.g.hom :=
      (ModuleCat.epi_iff_surjective T.g).mp hT.epi_g
    let : Module.Finite k (↑T.X₁) := h₁
    let : Module.Finite k (↑T.X₃) := h₃
    exact Module.Finite.of_exact hex hsur

private noncomputable def finrankKZeroOverField (k R : Type u) [Field k] [Ring R]
    (φ : k →+* R) :
    KZero (finiteDimensionalOverFieldProperty k R φ).FullSubcategory →+ ℤ := by
  let P := finiteDimensionalOverFieldProperty k R φ
  let F := ModuleCat.restrictScalars.{u} φ
  let rank : P.FullSubcategory → ℤ := fun V =>
    (Module.finrank k (↑(F.obj V.obj)) : ℤ)
  have rank_add : ∀ (S : ShortComplex P.FullSubcategory) (hS : S.ShortExact),
      rank S.X₂ = rank S.X₁ + rank S.X₃ := by
    intro S hS
    let : PreservesFiniteLimits P.ι :=
      P.preservesFiniteLimits_ι_of_isWeakSerreClass
    let : PreservesFiniteColimits P.ι :=
      P.preservesFiniteColimits_ι_of_isWeakSerreClass
    let : PreservesFiniteLimits F := ⟨fun _ _ _ => ⟨inferInstance⟩⟩
    let : PreservesFiniteColimits F := ⟨fun _ _ _ => ⟨inferInstance⟩⟩
    let U := S.map P.ι
    let T := U.map F
    have hU : U.ShortExact := hS.map_of_exact P.ι
    have hT : T.ShortExact := hU.map_of_exact F
    let : Module.Finite k (↑T.X₁) := S.X₁.property
    let : Module.Finite k (↑(F.obj (P.ι.obj S.X₁))) := S.X₁.property
    let : Module.Finite k (↑(F.obj (P.ι.obj S.X₂))) := S.X₂.property
    let : Module.Finite k (↑(F.obj (P.ι.obj S.X₃))) := S.X₃.property
    let : Module.Finite k (↑T.X₃) := S.X₃.property
    have hx : FiniteDimensional k (↑T.X₂) := by
      change FiniteDimensional k (↑(F.obj (P.ι.obj S.X₂)))
      infer_instance
    have hex : Function.Exact T.f.hom T.g.hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT.exact
    have hrange : LinearMap.range T.g.hom = ⊤ :=
      LinearMap.range_eq_top.mpr (ModuleCat.epi_iff_surjective T.g |>.mp hT.epi_g)
    have hker : LinearMap.ker T.g.hom = LinearMap.range T.f.hom :=
      LinearMap.exact_iff.mp hex
    have hinj : Function.Injective T.f.hom :=
      ModuleCat.mono_iff_injective T.f |>.mp hT.mono_f
    have hdim : Module.finrank k (↑T.X₂) =
        Module.finrank k (↑T.X₁) + Module.finrank k (↑T.X₃) := by
      calc
        Module.finrank k (↑T.X₂) = Module.finrank k (LinearMap.range T.g.hom) +
            Module.finrank k (LinearMap.ker T.g.hom) :=
          T.g.hom.finrank_range_add_finrank_ker.symm
        _ = Module.finrank k (↑T.X₃) + Module.finrank k (LinearMap.range T.f.hom) := by
          rw [hrange, hker]
          simp
        _ = Module.finrank k (↑T.X₃) + Module.finrank k (↑T.X₁) := by
          rw [LinearMap.finrank_range_of_inj hinj]
        _ = _ := by omega
    change (Module.finrank k (↑(F.obj (P.ι.obj S.X₂))) : ℤ) =
      (Module.finrank k (↑(F.obj (P.ι.obj S.X₁))) : ℤ) +
        (Module.finrank k (↑(F.obj (P.ι.obj S.X₃))) : ℤ)
    exact_mod_cast hdim
  exact KZero.lift rank rank_add

private lemma finrankKZeroOverField_mk (k R : Type u) [Field k] [Ring R]
    (φ : k →+* R) (A : ModuleCat.{u} R) (hA : Module.Finite k
      (↑((ModuleCat.restrictScalars.{u} φ).obj A))) :
    finrankKZeroOverField k R φ
      (KZero.mk (finiteDimensionalOverFieldProperty k R φ).FullSubcategory ⟨A, hA⟩) =
        (Module.finrank k (↑((ModuleCat.restrictScalars.{u} φ).obj A)) : ℤ) := by
  simp [finrankKZeroOverField, KZero.lift_mk]

/-- A zero module has dimension zero after restricting scalars. -/
private lemma finrank_restrictScalars_eq_zero_of_isZero (k R : Type u) [Field k] [Ring R]
    (φ : k →+* R) {M : ModuleCat.{u} R} (hM : IsZero M) :
    Module.finrank k (↑((ModuleCat.restrictScalars.{u} φ).obj M)) = 0 := by
  have : Subsingleton ↑((ModuleCat.restrictScalars.{u} φ).obj M) := by
    change Subsingleton ↑M
    exact ModuleCat.subsingleton_of_isZero hM
  exact Module.finrank_zero_of_subsingleton

private noncomputable def eulerCl {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsWeakSerreClass] (X : C) : KZero P.FullSubcategory := by
  classical
  exact if h : P X then KZero.mk _ ⟨X, h⟩ else 0

private lemma rightDerivedPlus_map_isZero {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [EnoughInjectives C]
    (M : C) (i : ℤ) (hM : IsZero M) : IsZero ((F.rightDerivedPlus i).obj M) := by
  have : (F.rightDerivedPlus i).Additive := by
    dsimp [Functor.rightDerivedPlus]
    infer_instance
  exact (F.rightDerivedPlus i).map_isZero hM

private noncomputable def cohomologyOverFieldRightDerivedPlusIso
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (F : X.Modules) (n : ℕ) :
    cohomologyOverField k f F n ≅
      (ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).obj
          (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerivedPlus
            (n : ℤ)).obj F) := by
  let r := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom
  let E := SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))
  letI : E.Additive := by
    unfold E SheafOfModules.evaluation
    infer_instance
  change (ModuleCat.restrictScalars r).obj ((E.rightDerived n).obj F) ≅ _
  exact (ModuleCat.restrictScalars r).mapIso
    ((Stacks.DerivedIndexing.rightDerivedIso E n).app F)

private noncomputable def exactDerivedPlusHomologyIso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (E : DerivedCategory.Plus A) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor B n).obj
        (F.rightDerivedFunctorPlus.obj E) ≅
      F.obj ((DerivedCategory.Plus.homologyFunctor A n).obj E) := by
  classical
  let a : ℤ := Classical.choose E.property
  have ha : E.obj.IsGE a := Classical.choose_spec E.property
  letI : E.obj.IsGE a := ha
  have haE : E.IsGE a :=
    (DerivedCategory.TStructure.t.plus.tStructure_isGE_iff
      DerivedCategory.TStructure.t E a).2 ha
  letI : E.IsGE a := haE
  let hres := DerivedCategory.Plus.exists_injective_nonempty_iso E a
  let J := Classical.choose hres
  have hJ := Classical.choose_spec hres
  let hJstrict := Classical.choose hJ
  have heNonempty := Classical.choose_spec hJ
  let e := Classical.choice heNonempty
  letI : J.obj.IsStrictlyGE a := hJstrict
  let L := (InjectiveObject.ι A).mapCochainComplexPlus.obj J
  let N := F.mapCochainComplexPlus.obj L
  let Lq : HomotopyCategory.Plus A := (HomotopyCategory.Plus.quotient A).obj L
  have hunit : IsIso (F.rightDerivedFunctorPlusUnith.app Lq) := by
    have : ∀ i, Injective (Lq.obj.as.X i) := fun _ => inferInstance
    infer_instance
  let eR : F.rightDerivedFunctorPlus.obj E ≅ DerivedCategory.Plus.Q.obj N :=
    F.rightDerivedFunctorPlus.mapIso e.symm ≪≫
      F.rightDerivedFunctorPlus.mapIso (Stacks.InjectiveModel.plusQhIsoPlusQ L).symm ≪≫
      (@asIso _ _ _ _ _ hunit).symm ≪≫ Stacks.InjectiveModel.plusQhIsoPlusQ N
  let H_A := DerivedCategory.Plus.homologyFunctor A n
  let H_B := DerivedCategory.Plus.homologyFunctor B n
  have hA : H_A.obj (DerivedCategory.Plus.Q.obj L) ≅ L.obj.homology n := by
    change (DerivedCategory.homologyFunctor A n).obj
      (DerivedCategory.Q.obj ((CochainComplex.Plus.ι A).obj L)) ≅ _
    exact (DerivedCategory.homologyFunctorFactors A n).app _
  have hB : H_B.obj (DerivedCategory.Plus.Q.obj N) ≅ N.obj.homology n := by
    change (DerivedCategory.homologyFunctor B n).obj
      (DerivedCategory.Q.obj ((CochainComplex.Plus.ι B).obj N)) ≅ _
    exact (DerivedCategory.homologyFunctorFactors B n).app _
  exact H_B.mapIso eR ≪≫ hB ≪≫ ((L.obj.sc n).mapHomologyIso F) ≪≫
    (F.mapIso ((H_A.mapIso e.symm) ≪≫ hA)).symm

private lemma eulerCl_of_prop {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsWeakSerreClass] {X : C} (h : P X) :
    eulerCl P X = KZero.mk _ ⟨X, h⟩ := by
  simp [eulerCl, h]

private lemma eulerCl_inclusion {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsWeakSerreClass] (X : P.FullSubcategory) :
    eulerCl P (P.ι.obj X) = KZero.mk _ X := by
  cases X with
  | mk X hX =>
    simp [eulerCl, hX, KZero.mk]

private lemma eulerCl_eq_zero_of_isZero {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsWeakSerreClass] {X : C} (h : IsZero X) :
    eulerCl P X = 0 := by
  by_cases hX : P X
  · rw [eulerCl_of_prop P hX]
    exact KZero.mk_eq_zero_of_isZero
      ((IsZero.iff_id_eq_zero _).2 (P.ι.map_injective (h.eq_of_src _ _)))
  · simp [eulerCl, hX]

private lemma eulerCl_congr {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsWeakSerreClass] {X Y : C} (e : X ≅ Y) :
    eulerCl P X = eulerCl P Y := by
  by_cases hX : P X
  · have hY : P Y := P.prop_of_iso e hX
    rw [eulerCl_of_prop P hX, eulerCl_of_prop P hY]
    exact KZero.mk_eq_of_iso (P.isoMk e)
  · have hY : ¬ P Y := fun hY => hX (P.prop_of_iso e.symm hY)
    simp [eulerCl, hX, hY]

private abbrev eulerLiftShortComplex {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsWeakSerreClass] (S : ShortComplex C)
    (h₁ : P S.X₁) (h₂ : P S.X₂) (h₃ : P S.X₃) :
    ShortComplex P.FullSubcategory :=
  ShortComplex.mk (X₁ := ⟨S.X₁, h₁⟩) (X₂ := ⟨S.X₂, h₂⟩) (X₃ := ⟨S.X₃, h₃⟩)
    (ObjectProperty.homMk S.f) (ObjectProperty.homMk S.g) (by ext; exact S.zero)

private lemma eulerCl_shortExact {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsWeakSerreClass] {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : P S.X₁) (h₂ : P S.X₂) (h₃ : P S.X₃) :
    eulerCl P S.X₂ = eulerCl P S.X₁ + eulerCl P S.X₃ := by
  have := P.preservesFiniteLimits_ι_of_isWeakSerreClass
  have := P.preservesFiniteColimits_ι_of_isWeakSerreClass
  have := hS.mono_f
  have := hS.epi_g
  have hS' : (eulerLiftShortComplex P S h₁ h₂ h₃).ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [← ShortComplex.exact_map_iff_of_faithful _ P.ι]
      exact hS.exact
    · exact P.ι.mono_of_mono_map (show Mono S.f from inferInstance)
    · exact P.ι.epi_of_epi_map (show Epi S.g from inferInstance)
  rw [eulerCl_of_prop P h₁, eulerCl_of_prop P h₂, eulerCl_of_prop P h₃]
  exact KZero.mk_of_shortExact _ hS'

private lemma eulerCl_homology_add {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsWeakSerreClass] (S : ShortComplex C)
    (h₁ : P S.X₁) (h₂ : P S.X₂) (h₃ : P S.X₃) :
    eulerCl P S.homology + eulerCl P S.X₁ =
      eulerCl P (kernel S.f) + eulerCl P (kernel S.g) := by
  have := P.preservesFiniteLimits_ι_of_isWeakSerreClass
  have := P.preservesFiniteColimits_ι_of_isWeakSerreClass
  set S' := eulerLiftShortComplex P S h₁ h₂ h₃
  have e : S'.map P.ι ≅ S := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [S']) (by simp [S'])
  have eH : P.ι.obj S'.homology ≅ S.homology :=
    (S'.mapHomologyIso P.ι).symm ≪≫ ShortComplex.homologyMapIso e
  have ek₁ : P.ι.obj (kernel S'.f) ≅ kernel S.f :=
    PreservesKernel.iso P.ι S'.f ≪≫ kernel.mapIso _ _ (Iso.refl _) (Iso.refl _) (by simp [S'])
  have ek₂ : P.ι.obj (kernel S'.g) ≅ kernel S.g :=
    PreservesKernel.iso P.ι S'.g ≪≫ kernel.mapIso _ _ (Iso.refl _) (Iso.refl _) (by simp [S'])
  rw [← eulerCl_congr P eH, ← eulerCl_congr P ek₁, ← eulerCl_congr P ek₂,
    eulerCl_inclusion, eulerCl_inclusion, eulerCl_inclusion,
    eulerCl_of_prop P h₁]
  exact KZero.mk_homology_add_mk_X₁ S'

/-- A subobject inclusion `U ≤ V` is the first map of a short exact sequence with cokernel
quotient. -/
private lemma shortExact_ofLE_cokernel {C : Type*} [Category C] [Abelian C] {A : C}
    (U V : Subobject A) (hUV : U ≤ V) :
    (ShortComplex.mk (Subobject.ofLE U V hUV) (cokernel.π (Subobject.ofLE U V hUV))
      (by simp)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance

private lemma eulerCl_subobject_quotient {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsWeakSerreClass] {A : C}
    (U V : Subobject A) (hUV : U ≤ V) (hU : P (U : C)) (hV : P (V : C))
    (hQ : P (cokernel (Subobject.ofLE U V hUV))) :
    eulerCl P (V : C) = eulerCl P (U : C) +
      eulerCl P (cokernel (Subobject.ofLE U V hUV)) :=
  eulerCl_shortExact P (shortExact_ofLE_cokernel U V hUV) hU hV hQ

private lemma prop_subobject_extension {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsWeakSerreClass] {A : C}
    (U V : Subobject A) (hUV : U ≤ V) (hU : P (U : C))
    (hQ : P (cokernel (Subobject.ofLE U V hUV))) : P (V : C) :=
  P.prop_X₂_of_shortExact (shortExact_ofLE_cokernel U V hUV) hU hQ

private lemma sum_range_of_difference {A : Type*} [AddCommGroup A] (f g : ℕ → A)
    (N : ℕ) (h : ∀ j < N, f j = f (j + 1) + g j) :
    ∑ j ∈ Finset.range N, g j = f 0 - f N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih (fun j hj => h j (by omega)), h N (by omega)]
      abel

private lemma eulerCl_abuts_fiber {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsWeakSerreClass] {r₀ : ℤ}
    (E : CohomologicalSpectralSequence C r₀) {H : C} (n : ℤ)
    (F : ℤ → Subobject H) (hF : Antitone F) (a b : ℤ) (hab : a ≤ b)
    (ha : F a = ⊤) (hb : F b = ⊥)
    (hPq : ∀ p, P (cokernel (Subobject.ofLE (F (p + 1)) (F p) (hF (by omega)))))
    (hiso : ∀ p, E.pageInfinity (p, n - p) ≅
      cokernel (Subobject.ofLE (F (p + 1)) (F p) (hF (by omega)))) :
    ∃ _hH : P H, eulerCl P H = ∑ᶠ p : ℤ, eulerCl P (E.pageInfinity (p, n - p)) := by
  have hchain : ∀ i : ℤ, -b ≤ i → i ≤ -a → P (F (-i) : C) := by
    intro i hib hia
    induction i, hib using Int.leInduction with
    | base =>
        have hz : IsZero (F (-(-b)) : C) := by
          rw [show -(-b) = b by omega, hb]
          exact IsZero.of_iso (isZero_zero C) Subobject.botCoeIsoZero
        exact P.prop_of_isZero hz
    | succ m hm ih =>
        let p : ℤ := -(m + 1)
        have hU : P (F (p + 1) : C) := by
          simpa [p] using ih (by omega)
        have hV := prop_subobject_extension P (F (p + 1)) (F p) (hF (by omega))
          hU (hPq p)
        simpa [p] using hV
  have hFa : P (F a : C) := by simpa using hchain (-a) (by omega) (by omega)
  have eTop : (F a : C) ≅ H := by
    rw [ha, Subobject.top_eq_id]
    exact Subobject.underlyingIso (𝟙 H)
  have hH : P H := P.prop_of_iso eTop hFa
  let N : ℕ := (b - a).toNat
  have hN : (N : ℤ) = b - a := Int.toNat_of_nonneg (sub_nonneg.mpr hab)
  let T : Finset ℤ := Finset.image (fun j : ℕ => a + (j : ℤ)) (Finset.range N)
  let qfun : ℤ → KZero P.FullSubcategory := fun p =>
    eulerCl P (E.pageInfinity (p, n - p))
  have hInterval (p : ℤ) (hp : a ≤ p) (hp' : p < b) : p ∈ T :=
    Finset.mem_image.mpr ⟨(p - a).toNat, Finset.mem_range.mpr (by omega), by omega⟩
  have hqzero (p : ℤ) (hp : ¬ (a ≤ p ∧ p < b)) : qfun p = 0 := by
    have hEq : F (p + 1) = F p := by
      refine le_antisymm (hF (by omega)) ?_
      by_cases hleft : p < a
      · exact le_top.trans (ha.ge.trans (hF (by omega)))
      · exact (hF (by omega)).trans (hb.le.trans bot_le)
    have : Epi (Subobject.ofLE (F (p + 1)) (F p) (hF (by omega))) :=
      inferInstanceAs (Epi (Subobject.isoOfEq (F (p + 1)) (F p) hEq).hom)
    exact eulerCl_eq_zero_of_isZero P (IsZero.of_iso (isZero_cokernel_of_epi _) (hiso p))
  have hqSupport : Function.support qfun ⊆ T := fun p hp =>
    of_not_not fun hpt => hp (hqzero p fun hi => hpt (hInterval p hi.1 hi.2))
  have hqSum : ∑ᶠ p : ℤ, qfun p = ∑ j ∈ Finset.range N, qfun (a + (j : ℤ)) := by
    rw [finsum_eq_finsetSum_of_support_subset qfun hqSupport]
    show (∑ p ∈ T, qfun p) = _
    rw [Finset.sum_image (by
      intro x hx y hy hxy
      exact_mod_cast add_left_cancel hxy)]
  let ffun : ℕ → KZero P.FullSubcategory := fun j => eulerCl P (F (a + (j : ℤ)) : C)
  have hstep : ∀ j < N, ffun j = ffun (j + 1) + qfun (a + (j : ℤ)) := by
    intro j hj
    let p : ℤ := a + (j : ℤ)
    have hp : a ≤ p := by simp [p]
    have hp' : p < b := by
      dsimp [p]
      omega
    have hPleft : P (F (p + 1) : C) := by
      simpa using hchain (-(p + 1)) (by omega) (by omega)
    have hPright : P (F p : C) := by
      simpa using hchain (-p) (by omega) (by omega)
    have hrel := eulerCl_subobject_quotient P (F (p + 1)) (F p)
      (hF (by omega))
      hPleft hPright (hPq p)
    have hrel' : eulerCl P (F p : C) = eulerCl P (F (p + 1) : C) + qfun p := by
      dsimp [qfun]
      rw [eulerCl_congr P (hiso p)]
      exact hrel
    simpa [ffun, qfun, p, Nat.cast_add, add_assoc] using hrel'
  have htel := sum_range_of_difference ffun (fun j => qfun (a + (j : ℤ))) N hstep
  have hstart : ffun 0 = eulerCl P H := by
    simpa [ffun] using eulerCl_congr P eTop
  have hend : ffun N = 0 := by
    dsimp [ffun]
    rw [show a + (N : ℤ) = b by omega, hb]
    exact eulerCl_eq_zero_of_isZero P
      (IsZero.of_iso (isZero_zero C) Subobject.botCoeIsoZero)
  rw [← hqSum, hstart, hend] at htel
  exact ⟨hH, by simpa using htel.symm⟩

private lemma eulerProp_homology {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsWeakSerreClass] (S : ShortComplex C)
    (h₁ : P S.X₁) (h₂ : P S.X₂) (h₃ : P S.X₃) : P S.homology := by
  have hc : P S.cycles :=
    P.prop_of_iso (S.cyclesIsKernel.conePointUniqueUpToIso (limit.isLimit _)).symm
      (P.prop_kernel _ h₂ h₃)
  exact P.prop_of_iso ((cokernelIsCokernel _).coconePointUniqueUpToIso S.homologyIsCokernel)
    (P.prop_cokernel _ h₁ hc)

private lemma eulerFinsumComplex {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsWeakSerreClass] (a : ℤ × ℤ) (ha : a.1 + a.2 = 1)
    (X : HomologicalComplex C (ComplexShape.up' a)) (hP : ∀ i, P (X.X i))
    (hfin : {i | ¬ IsZero (X.X i)}.Finite) :
    ∑ᶠ i : ℤ × ℤ, ((i.1 + i.2).negOnePow : ℤ) • eulerCl P (X.X i) =
      ∑ᶠ i : ℤ × ℤ, ((i.1 + i.2).negOnePow : ℤ) • eulerCl P (X.homology i) := by
  set ε : ℤ × ℤ → ℤ := fun i => ((i.1 + i.2).negOnePow : ℤ) with hεdef
  have hε : ∀ i, ε (i - a) = - ε i := by
    intro i
    simp only [hεdef, Prod.fst_sub, Prod.snd_sub]
    rw [show i.1 + i.2 = (i.1 - a.1 + (i.2 - a.2)) + 1 by omega, Int.negOnePow_succ]
    simp
  set k : ℤ × ℤ → KZero P.FullSubcategory := fun i => eulerCl P (kernel (X.d i (i + a)))
  set g : ℤ × ℤ → KZero P.FullSubcategory :=
    fun i => ε i • (k i - eulerCl P (X.X i)) with hgdef
  have hprev : ∀ i, (ComplexShape.up' a).prev i = i - a := fun i =>
    (ComplexShape.up' a).prev_eq' (show i - a + a = i from sub_add_cancel i a)
  have hnext : ∀ i, (ComplexShape.up' a).next i = i + a := fun i =>
    (ComplexShape.up' a).next_eq' rfl
  have key : ∀ i,
      ε i • eulerCl P (X.homology i) - ε i • eulerCl P (X.X i) = g i - g (i - a) := by
    intro i
    have h := eulerCl_homology_add P (X.sc' (i - a) i (i + a)) (hP _) (hP _) (hP _)
    rw [← eulerCl_congr P (X.homologyIsoSc' (i - a) i (i + a) (hprev i) (hnext i))] at h
    have hk : eulerCl P (kernel (X.sc' (i - a) i (i + a)).f) = k (i - a) := by
      show eulerCl P (kernel (X.d (i - a) i)) = eulerCl P (kernel (X.d (i - a) (i - a + a)))
      rw [sub_add_cancel]
    change eulerCl P (X.homology i) + eulerCl P (X.X (i - a)) =
      eulerCl P (kernel (X.sc' (i - a) i (i + a)).f) + k i at h
    rw [hk] at h
    have hh : eulerCl P (X.homology i) =
        k (i - a) + k i - eulerCl P (X.X (i - a)) := eq_sub_of_add_eq h
    simp only [hgdef, hε, hh, smul_sub, smul_add, neg_smul]
    abel
  have hzero : ∀ i, IsZero (X.X i) →
      g i = 0 ∧ eulerCl P (X.X i) = 0 ∧ eulerCl P (X.homology i) = 0 := by
    intro i hi
    have hx := eulerCl_eq_zero_of_isZero P hi
    refine ⟨?_, hx, eulerCl_eq_zero_of_isZero P (ShortComplex.isZero_homology_of_isZero_X₂ _ hi)⟩
    simp only [hgdef, k, hx,
      eulerCl_eq_zero_of_isZero P (IsZero.of_mono (kernel.ι _) hi), sub_zero, smul_zero]
  have hg : (Function.support g).Finite :=
    hfin.subset fun i hi hz => hi (hzero i hz).1
  have hg' : (Function.support fun i => g (i - a)).Finite :=
    (hg.image fun j => j + a).subset fun i hi => ⟨i - a, hi, sub_add_cancel i a⟩
  have h₁ : (Function.support fun i => ε i • eulerCl P (X.homology i)).Finite :=
    hfin.subset fun i hi hz => hi (by simp only [(hzero i hz).2.2, smul_zero])
  have h₂ : (Function.support fun i => ε i • eulerCl P (X.X i)).Finite :=
    hfin.subset fun i hi hz => hi (by simp only [(hzero i hz).2.1, smul_zero])
  have hsum : ∑ᶠ i, (g i - g (i - a)) = 0 := by
    rw [finsum_sub_distrib hg hg', sub_eq_zero]
    exact (finsum_comp_equiv (Equiv.subRight a) (f := g)).symm
  refine (sub_eq_zero.1 ?_).symm
  show ∑ᶠ i, ε i • eulerCl P (X.homology i) -
      ∑ᶠ i, ε i • eulerCl P (X.X i) = 0
  rw [← finsum_sub_distrib h₁ h₂, ← hsum]
  exact finsum_congr key

private lemma eulerPageInduction {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsWeakSerreClass] {r₀ : ℤ}
    (E : CohomologicalSpectralSequence C r₀) (r : ℤ) (hr : r₀ ≤ r)
    (hfin : {pq : ℤ × ℤ | ¬ IsZero ((E.page r hr).X pq)}.Finite)
    (hP : ∀ pq, P ((E.page r hr).X pq)) :
    ∀ s : ℤ, r ≤ s → ∀ hs : r₀ ≤ s,
      (∀ pq, P ((E.page s hs).X pq)) ∧
      {pq : ℤ × ℤ | ¬ IsZero ((E.page s hs).X pq)} ⊆
        {pq : ℤ × ℤ | ¬ IsZero ((E.page r hr).X pq)} ∧
      ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) • eulerCl P ((E.page s hs).X pq) =
        ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) • eulerCl P ((E.page r hr).X pq) := by
  intro s hle
  induction s, hle using Int.leInduction with
  | base => exact fun _ => ⟨hP, subset_rfl, rfl⟩
  | succ m hm ih =>
    intro hs
    have hm0 : r₀ ≤ m := hr.trans hm
    obtain ⟨hPm, hsub, hsum⟩ := ih hm0
    refine ⟨fun pq => P.prop_of_iso (E.iso m (m + 1) pq rfl hm0)
      (eulerProp_homology P ((E.page m hm0).sc pq) (hPm _) (hPm _) (hPm _)),
      fun pq hpq => hsub fun hz => hpq ?_, ?_⟩
    · exact IsZero.of_iso (ShortComplex.isZero_homology_of_isZero_X₂ _ hz)
        (E.iso m (m + 1) pq rfl hm0).symm
    · rw [← hsum, eulerFinsumComplex P _ (by simp) (E.page m hm0) hPm (hfin.subset hsub)]
      exact finsum_congr fun pq => by rw [eulerCl_congr P (E.iso m (m + 1) pq rfl hm0)]

/-- Past some page `s ≥ r`, the infinity page at `pq` is the `s`-th page at `pq`. -/
private lemma exists_pageInfinityIso_page {C : Type*} [Category C] [Abelian C] {r₀ : ℤ}
    (E : CohomologicalSpectralSequence C r₀) (r : ℤ) (hr : r₀ ≤ r) (pq : ℤ × ℤ)
    (hInf : E.HasPageInfinityAt pq) :
    ∃ (s : ℤ) (hs : r₀ ≤ s), r ≤ s ∧ Nonempty (E.pageInfinity pq ≅ (E.page s hs).X pq) := by
  let s := max r (E.rMin pq)
  have : E.HasEdgeMonoAtFrom pq s :=
    ⟨(E.rToMin_LE_rMin pq).trans (le_max_right _ _)⟩
  have : E.HasEdgeEpiAtFrom pq s :=
    ⟨(E.rFromMin_LE_rMin pq).trans (le_max_right _ _)⟩
  exact ⟨s, hr.trans (le_max_left _ _), le_max_left _ _, ⟨E.pageInfinityIso pq s⟩⟩

/-- A vanishing term of the page `E_r` gives a vanishing term of the infinity page. -/
private lemma isZero_pageInfinity_of_isZero_page {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsWeakSerreClass] {r₀ : ℤ}
    (E : CohomologicalSpectralSequence C r₀) (r : ℤ) (hr : r₀ ≤ r)
    (hfin : {pq : ℤ × ℤ | ¬ IsZero ((E.page r hr).X pq)}.Finite)
    (hP : ∀ pq, P ((E.page r hr).X pq)) (pq : ℤ × ℤ) (hInf : E.HasPageInfinityAt pq)
    (hz : IsZero ((E.page r hr).X pq)) : IsZero (E.pageInfinity pq) := by
  obtain ⟨s, hs0, hsr, ⟨e⟩⟩ := exists_pageInfinityIso_page E r hr pq hInf
  have hMin := eulerPageInduction P E r hr hfin hP s hsr hs0
  exact IsZero.of_iso (of_not_not fun hnot => hMin.2.1 hnot hz) e

/-- The graded pieces of an abutment filtration, indexed by `(p, n - p)`. -/
private noncomputable def pageInfinityIsoCokernelOfLE {C : Type*} [Category C] [Abelian C] {r₀ : ℤ}
    (E : CohomologicalSpectralSequence C r₀) {H : ℤ → C} (F : ∀ n, ℤ → Subobject (H n))
    (hF : ∀ n, Antitone (F n))
    (hGraded : ∀ p q : ℤ, Nonempty (E.pageInfinity (p, q) ≅
      cokernel (Subobject.ofLE (F (p + q) (p + 1)) (F (p + q) p) (hF (p + q) (by omega)))))
    (n p : ℤ) : E.pageInfinity (p, n - p) ≅
      cokernel (Subobject.ofLE (F n (p + 1)) (F n p) (hF n (by omega))) := by
  have heq : p + (n - p) = n := by omega
  conv_rhs => rw [← heq]
  exact Classical.choice (hGraded p (n - p))

private lemma eulerAbuts_sum {C : Type*} [Category C] [Abelian C] {r₀ : ℤ}
    (E : CohomologicalSpectralSequence C r₀) (r : ℤ) (hr : r₀ ≤ r)
    (H : ℤ → C) (hAbuts : SpectralSequence.AbutsTo E H)
    (P : ObjectProperty C) [P.IsWeakSerreClass]
    (hfin : {pq : ℤ × ℤ | ¬ IsZero ((E.page r hr).X pq)}.Finite)
    (hP : ∀ pq, P ((E.page r hr).X pq))
    (hDetect : ∀ {A}, P A → eulerCl P A = 0 → IsZero A) :
    {n : ℤ | ¬ IsZero (H n)}.Finite ∧
      ∃ hH : ∀ n, P (H n),
        ∑ᶠ n : ℤ, (n.negOnePow : ℤ) • KZero.mk P.FullSubcategory ⟨H n, hH n⟩ =
          ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) •
            KZero.mk P.FullSubcategory ⟨(E.page r hr).X pq, hP pq⟩ := by
  classical
  obtain ⟨hInf, ⟨F, hF, ⟨hBounds, hGraded⟩⟩⟩ := hAbuts
  let rMin : ℤ × ℤ → ℤ := fun pq => by
    let : E.HasPageInfinityAt pq := hInf pq.1 pq.2
    exact E.rMin pq
  obtain ⟨M, hM⟩ := (hfin.image rMin).bddAbove
  have hN : r ≤ max r M := le_max_left _ _
  have hs : r₀ ≤ max r M := hr.trans hN
  obtain ⟨hPN, hsub, hsum⟩ :=
    eulerPageInduction P E r hr hfin hP (max r M) hN hs
  have hPInf : ∀ pq, P (E.pageInfinity pq) := by
    intro pq
    obtain ⟨s, hs0, hsr, ⟨e⟩⟩ := exists_pageInfinityIso_page E r hr pq (hInf pq.1 pq.2)
    exact P.prop_of_iso e.symm ((eulerPageInduction P E r hr hfin hP s hsr hs0).1 pq)
  have hZeroInf : ∀ pq, IsZero ((E.page r hr).X pq) → IsZero (E.pageInfinity pq) :=
    fun pq => isZero_pageInfinity_of_isZero_page P E r hr hfin hP pq (hInf pq.1 pq.2)
  have hClassIso : ∀ pq,
      eulerCl P (E.pageInfinity pq) = eulerCl P ((E.page (max r M) hs).X pq) := by
    intro pq
    by_cases hz : IsZero ((E.page r hr).X pq)
    · rw [eulerCl_eq_zero_of_isZero P (hZeroInf pq hz),
        eulerCl_eq_zero_of_isZero P (of_not_not fun hnot => hsub hnot hz)]
    · let : E.HasPageInfinityAt pq := hInf pq.1 pq.2
      have hm : rMin pq ≤ max r M :=
        (hM ⟨pq, hz, rfl⟩).trans (le_max_right _ _)
      have : E.HasEdgeMonoAtFrom pq (max r M) :=
        ⟨(E.rToMin_LE_rMin pq).trans hm⟩
      have : E.HasEdgeEpiAtFrom pq (max r M) :=
        ⟨(E.rFromMin_LE_rMin pq).trans hm⟩
      exact eulerCl_congr P (E.pageInfinityIso pq (max r M))
  have hSupportInf : (Function.support fun pq => eulerCl P (E.pageInfinity pq)).Finite :=
    hfin.subset fun pq hpq hzero =>
      hpq (eulerCl_eq_zero_of_isZero P (hZeroInf pq hzero))
  have hIsoGraded := pageInfinityIsoCokernelOfLE E F hF hGraded
  have hfiber (n : ℤ) : ∃ hH : P (H n),
      eulerCl P (H n) = ∑ᶠ p : ℤ, eulerCl P (E.pageInfinity (p, n - p)) := by
    obtain ⟨a, b, hab, ha, hb⟩ := hBounds n
    exact eulerCl_abuts_fiber P E n (F n) (hF n) a b hab ha hb
      (fun p => P.prop_of_iso (hIsoGraded n p) (hPInf (p, n - p))) (hIsoGraded n)
  let hH : ∀ n, P (H n) := fun n => Classical.choose (hfiber n)
  have hHClass (n : ℤ) :
      eulerCl P (H n) = ∑ᶠ p : ℤ, eulerCl P (E.pageInfinity (p, n - p)) :=
    Classical.choose_spec (hfiber n)
  have hfinH : {n : ℤ | ¬ IsZero (H n)}.Finite := by
    apply (hfin.image fun pq : ℤ × ℤ => pq.1 + pq.2).subset
    intro n hn
    by_contra hnS
    have hClassZero : eulerCl P (H n) = 0 := by
      rw [hHClass]
      exact finsum_eq_zero_of_forall_eq_zero fun p => eulerCl_eq_zero_of_isZero P
        (hZeroInf _ (of_not_not fun hmem => hnS ⟨(p, n - p), hmem, by simp⟩))
    exact hn (hDetect (hH n) hClassZero)
  refine ⟨hfinH, hH, ?_⟩
  calc
    ∑ᶠ n : ℤ, (n.negOnePow : ℤ) • KZero.mk P.FullSubcategory ⟨H n, hH n⟩ =
        ∑ᶠ n : ℤ, (n.negOnePow : ℤ) •
          ∑ᶠ p : ℤ, eulerCl P (E.pageInfinity (p, n - p)) := by
      refine finsum_congr fun n => ?_
      rw [← eulerCl_of_prop P (hH n), hHClass]
    _ = ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) •
          eulerCl P (E.pageInfinity pq) :=
        finsum_negOnePow_smul_finsum_eq _ hSupportInf
    _ = ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) •
          eulerCl P ((E.page (max r M) hs).X pq) :=
      finsum_congr fun pq => by rw [hClassIso pq]
    _ = ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) •
          eulerCl P ((E.page r hr).X pq) := hsum
    _ = ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) •
          KZero.mk P.FullSubcategory ⟨(E.page r hr).X pq, hP pq⟩ :=
      finsum_congr fun pq => by rw [eulerCl_of_prop P (hP pq)]

private lemma finsum_int_eq_nat_of_nonneg_support {A : Type*} [AddCommGroup A]
    (f : ℤ → A) (hf : (Function.support f).Finite)
    (hzero : ∀ z < 0, f z = 0) :
    ∑ᶠ z : ℤ, f z = ∑ᶠ n : ℕ, f n := by
  classical
  let S := hf.toFinset
  let T := S.image Int.toNat
  have hS : Function.support f ⊆ (S : Set ℤ) := fun _ hz => (Set.Finite.mem_toFinset hf).2 hz
  have hT : Function.support (fun n : ℕ => f n) ⊆ (T : Set ℕ) := fun n hn =>
    Finset.mem_image.mpr ⟨(n : ℤ), hS hn, by simp⟩
  rw [finsum_eq_sum_of_support_subset (s := S) f hS,
    finsum_eq_sum_of_support_subset (s := T) (fun n : ℕ => f n) hT]
  show (∑ z ∈ S, f z) = ∑ n ∈ S.image Int.toNat, f n
  rw [Finset.sum_image (s := S) (g := Int.toNat)
    (f := fun n : ℕ => f n) (by
    intro x hx y hy hxy
    have := not_lt.1 fun h => (Set.Finite.mem_toFinset hf).1 hx (hzero x h)
    have := not_lt.1 fun h => (Set.Finite.mem_toFinset hf).1 hy (hzero y h)
    omega)]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Int.toNat_of_nonneg (not_lt.1 fun h => (Set.Finite.mem_toFinset hf).1 hz (hzero z h))]

private lemma finsum_int_prod_eq_nat_prod_of_nonneg_support {A : Type*} [AddCommGroup A]
    (f : ℤ × ℤ → A) (hf : (Function.support f).Finite)
    (hzero : ∀ p q, p < 0 ∨ q < 0 → f (p, q) = 0) :
    ∑ᶠ pq : ℤ × ℤ, f pq =
      ∑ᶠ ij : ℕ × ℕ, f ((ij.1 : ℤ), (ij.2 : ℤ)) := by
  let g : ℤ → A := fun p => ∑ᶠ q : ℤ, f (p, q)
  have hgfin : (Function.support g).Finite :=
    (hf.image Prod.fst).subset fun p hp => of_not_not fun hp' =>
      hp (finsum_eq_zero_of_forall_eq_zero fun q => of_not_not fun hq => hp' ⟨(p, q), hq, rfl⟩)
  have hgzero : ∀ p, p < 0 → g p = 0 := fun p hp =>
    finsum_eq_zero_of_forall_eq_zero fun q => hzero p q (Or.inl hp)
  have hrowfin (p : ℤ) : (Function.support fun q : ℤ => f (p, q)).Finite :=
    (hf.image Prod.snd).subset fun q hq => ⟨(p, q), hq, rfl⟩
  let fn : ℕ × ℕ → A := fun ij => f ((ij.1 : ℤ), (ij.2 : ℤ))
  have hfnfin : (Function.support fn).Finite :=
    (hf.preimage (f := fun ij : ℕ × ℕ => ((ij.1 : ℤ), (ij.2 : ℤ))) fun _ _ _ _ h =>
      Prod.ext (Int.ofNat.inj (congrArg Prod.fst h)) (Int.ofNat.inj (congrArg Prod.snd h))).subset
        fun _ h => h
  calc
    ∑ᶠ pq : ℤ × ℤ, f pq = ∑ᶠ p : ℤ, g p := finsum_curry f hf
    _ = ∑ᶠ i : ℕ, g i := finsum_int_eq_nat_of_nonneg_support g hgfin hgzero
    _ = ∑ᶠ i : ℕ, ∑ᶠ j : ℕ, fn (i, j) := by
      refine finsum_congr fun i => ?_
      dsimp [g]
      exact finsum_int_eq_nat_of_nonneg_support (fun q : ℤ => f (i, q))
        (hrowfin i) (fun q hq => hzero i q (Or.inr hq))
    _ = ∑ᶠ ij : ℕ × ℕ, fn ij := (finsum_curry fn hfnfin).symm

/-- The dimension map sends a signed `finsum` of classes of finite-dimensional modules to the
signed `finsum` of their dimensions, if only finitely many of the modules are nonzero. -/
private lemma finrankKZeroOverField_finsum {ι : Type*} (k R : Type u) [Field k] [Ring R]
    (φ : k →+* R) (ε : ι → ℤ) (M : ι → ModuleCat.{u} R)
    (hM : ∀ i, finiteDimensionalOverFieldProperty k R φ (M i))
    (hfin : {i | ¬ IsZero (M i)}.Finite) :
    finrankKZeroOverField k R φ (∑ᶠ i, ε i •
        KZero.mk (finiteDimensionalOverFieldProperty k R φ).FullSubcategory ⟨M i, hM i⟩) =
      ∑ᶠ i, ε i * (Module.finrank k (↑((ModuleCat.restrictScalars.{u} φ).obj (M i))) : ℤ) := by
  set P := finiteDimensionalOverFieldProperty k R φ
  have hz (i : ι) (h : IsZero (M i)) : KZero.mk P.FullSubcategory ⟨M i, hM i⟩ = 0 := by
    rw [← eulerCl_of_prop P (hM i)]
    exact eulerCl_eq_zero_of_isZero P h
  have hsupp : (Function.support fun i => ε i • KZero.mk P.FullSubcategory ⟨M i, hM i⟩).Finite :=
    hfin.subset fun i hi h => hi (by simp only [hz i h, smul_zero])
  rw [AddMonoidHom.map_finsum _ hsupp]
  refine finsum_congr fun i => ?_
  simp only [map_zsmul, zsmul_eq_mul]
  norm_cast

/-- **The spectral-sequence Euler characteristic over a field**, the bookkeeping of
[Stacks, Tag 0BDW] for a spectral sequence presented by its abutment. If finitely many terms of
the page `E_r` of a spectral sequence of `R`-modules are nonzero, each of them is a
finite-dimensional `k`-vector space after restricting scalars along `ρ : k →+* R`, and those in
the negative quadrants vanish, then the abutment has the same properties and
`∑ (-1)ⁿ dim_k H ⁿ = ∑ (-1)^{p + q} dim_k E_r^{p, q}`. -/
private lemma finsum_negOnePow_finrank_eq_of_abutsTo
    (k R : Type u) [Field k] [Ring R] (ρ : k →+* R) {r₀ : ℤ}
    (E : CohomologicalSpectralSequence (ModuleCat.{u} R) r₀) (r : ℤ) (hr : r₀ ≤ r)
    (H : ℤ → ModuleCat.{u} R) (hAbuts : SpectralSequence.AbutsTo E H)
    (hfin : {pq : ℤ × ℤ | ¬ IsZero ((E.page r hr).X pq)}.Finite)
    (hPdim : ∀ pq : ℤ × ℤ,
      Module.Finite k (↑((ModuleCat.restrictScalars.{u} ρ).obj ((E.page r hr).X pq))))
    (hneg : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page r hr).X (p, q))) :
    {n : ℤ | ¬ IsZero (H n)}.Finite ∧
      (∀ n : ℤ, Module.Finite k (↑((ModuleCat.restrictScalars.{u} ρ).obj (H n)))) ∧
      (∀ n < 0, IsZero (H n)) ∧
      ∑ᶠ n : ℤ, (n.negOnePow : ℤ) *
          (Module.finrank k (↑((ModuleCat.restrictScalars.{u} ρ).obj (H n))) : ℤ) =
        ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) *
          (Module.finrank k (↑((ModuleCat.restrictScalars.{u} ρ).obj
            ((E.page r hr).X pq))) : ℤ) := by
  let P := finiteDimensionalOverFieldProperty k R ρ
  have : P.IsWeakSerreClass := by
    dsimp [P]
    infer_instance
  have hDetect : ∀ {A : ModuleCat.{u} R}, P A → eulerCl P A = 0 → IsZero A := by
    intro A hA hz
    let : Module.Finite k (↑((ModuleCat.restrictScalars.{u} ρ).obj A)) := hA
    rw [eulerCl_of_prop P hA] at hz
    have hz' := congrArg (finrankKZeroOverField k R ρ) hz
    have hdimZ : (Module.finrank k (↑((ModuleCat.restrictScalars.{u} ρ).obj A)) : ℤ) = 0 := by
      rw [finrankKZeroOverField_mk k R ρ A hA] at hz'
      simpa only [map_zero] using hz'
    have hdim : Module.finrank k (↑((ModuleCat.restrictScalars.{u} ρ).obj A)) = 0 :=
      Int.ofNat.inj hdimZ
    have hsub : Subsingleton (↑A) := by
      show Subsingleton (↑((ModuleCat.restrictScalars.{u} ρ).obj A))
      exact Module.finrank_zero_iff.mp hdim
    exact ModuleCat.isZero_of_subsingleton A
  obtain ⟨hfinH, hH, hKzero⟩ :=
    @eulerAbuts_sum (ModuleCat R) inferInstance inferInstance r₀ E r hr H
      hAbuts P (inferInstance : P.IsWeakSerreClass) hfin
      hPdim hDetect
  obtain ⟨hInf, ⟨F, hF, ⟨hBounds, hGraded⟩⟩⟩ := hAbuts
  have hZeroInf : ∀ pq, IsZero ((E.page r hr).X pq) → IsZero (E.pageInfinity pq) :=
    fun pq => @isZero_pageInfinity_of_isZero_page (ModuleCat R) inferInstance inferInstance P
      inferInstance r₀ E r hr hfin hPdim pq (hInf pq.1 pq.2)
  have hIsoGraded := pageInfinityIsoCokernelOfLE E F hF hGraded
  have hHneg (n : ℤ) (hn : n < 0) : IsZero (H n) := by
    obtain ⟨a, b, hab, ha, hb⟩ := hBounds n
    have hEuler := @eulerCl_abuts_fiber (ModuleCat R) inferInstance inferInstance P inferInstance
      r₀ E (H n) n (F n) (hF n) a b hab ha hb
      (fun p => P.prop_of_isZero (IsZero.of_iso
        (hZeroInf (p, n - p) (hneg p (n - p) (by omega))) (hIsoGraded n p).symm))
      (hIsoGraded n)
    have hClassZero : eulerCl P (H n) = 0 := by
      rw [Classical.choose_spec hEuler]
      exact finsum_eq_zero_of_forall_eq_zero fun p =>
        eulerCl_eq_zero_of_isZero P (hZeroInf (p, n - p) (hneg p (n - p) (by omega)))
    exact hDetect (hH n) hClassZero
  have hMap := congrArg (finrankKZeroOverField k R ρ) hKzero
  rw [finrankKZeroOverField_finsum k R ρ (fun n : ℤ => (n.negOnePow : ℤ)) H hH hfinH,
    finrankKZeroOverField_finsum k R ρ (fun pq : ℤ × ℤ => ((pq.1 + pq.2).negOnePow : ℤ))
      (fun pq => (E.page r hr).X pq) hPdim hfin] at hMap
  exact ⟨hfinH, hH, hHneg, hMap⟩

/-- The map on global sections of a morphism of schemes is `appLE` at `⊤`. -/
private lemma appTop_eq_appLE_top {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f.appTop = f.appLE ⊤ ⊤ (by simp) := by
  change f.app ⊤ = f.appLE ⊤ ⊤ (by simp)
  rw [Scheme.Hom.app_eq_appLE]
  rfl

/-- **[Stacks, Tag 02O6] over a field base, read on the bounded below right derived functor.**
For a coherent module on a scheme proper over `k`, the degree-`n` cohomology computed by
`CategoryTheory.Functor.rightDerivedPlus` is a finite-dimensional `k`-vector space. -/
private lemma module_finite_restrictScalars_rightDerivedPlus
    (h02O6 : CohomologyFiniteDimensionalOverField.{u}) (k : Type u) [Field k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g] (F : X.Modules) (hF : F.IsCoherent)
    (n : ℕ) :
    Module.Finite k (↑((ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).obj
      (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerivedPlus
        (n : ℤ)).obj F))) := by
  rw [appTop_eq_appLE_top g]
  have : FiniteDimensional k (cohomologyOverField k g F n) := h02O6 k X g inferInstance F hF n
  exact Module.Finite.equiv (cohomologyOverFieldRightDerivedPlusIso k g F n).toLinearEquiv

/-! ### The Leray spectral sequence of a morphism of schemes -/

/-- The second page of the Leray spectral sequence of `f` at a module `G`, as a spectral
sequence of `Γ(X, ⊤)`-modules. -/
private noncomputable def lerayPage {Y X : Scheme.{u}} (f : Y ⟶ X) (G : Y.Modules) :
    E₂CohomologicalSpectralSequence
      (ModuleCat.{u} ↑((structureSheafRing X.toRingedSpace).obj.obj
        (op (⊤ : X.Opens)))) :=
  (Stacks.Cohomology.LerayCard.leraySpectralSequence.{u} f.toLRSHom.toShHom).sequence.obj
    ((DerivedCategory.Plus.singleFunctor
      (ModuleSheaves Y.toRingedSpace) 0).obj G)

/-- The abutment of the Leray spectral sequence of `f` at `G`: the cohomology of `G` on `Y`,
read as a `Γ(X, ⊤)`-module by restriction of scalars along `f`. -/
private noncomputable def lerayAbutment {Y X : Scheme.{u}} (f : Y ⟶ X) (G : Y.Modules)
    (n : ℤ) : ModuleCat.{u} (Γ(X, ⊤) : Type u) :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (Γ(X, ⊤) : Type u)) n).obj
    (((SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))).rightDerivedFunctorPlus ⋙
      (ModuleCat.restrictScalars ((f.appTop).hom :
        (Γ(X, ⊤) : Type u) →+* (Γ(Y, ⊤) : Type u))).rightDerivedFunctorPlus).obj
      ((DerivedCategory.Plus.singleFunctor
        (ModuleSheaves Y.toRingedSpace) 0).obj G))

/-- **The Leray spectral sequence abuts to the cohomology of `Y`.** The convergence clause of
[Stacks, Tag 01F2]. -/
private lemma abutsTo_lerayPage {Y X : Scheme.{u}} (f : Y ⟶ X) (G : Y.Modules) :
    SpectralSequence.AbutsTo (lerayPage f G) (lerayAbutment f G) :=
  (Stacks.Cohomology.LerayCard.leraySpectralSequence.{u} f.toLRSHom.toShHom).abuts
    ((DerivedCategory.Plus.singleFunctor
      (ModuleSheaves Y.toRingedSpace) 0).obj G)

/-- **The second page of the Leray spectral sequence is `Hᵖ(X, Rᵍf_*G)`.** The second-page
clause of [Stacks, Tag 01F2], with `Rᵍf_*G` computed through the ringed-space pushforward
`RingedSpaceModuleAdjunction.modulePushforward`. -/
private noncomputable def lerayPageTwoIsoRaw {Y X : Scheme.{u}} (f : Y ⟶ X) (G : Y.Modules)
    (p q : ℤ) :
    ((lerayPage f G).page 2 (by omega)).X (p, q) ≅
      ((SheafOfModules.evaluation
        (structureSheafRing X.toRingedSpace)
        (op (⊤ : X.Opens))).rightDerivedPlus p).obj
        (((RingedSpaceModuleAdjunction.modulePushforward
            f.toLRSHom.toShHom).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor
            (ModuleSheaves X.toRingedSpace) q).obj
          ((DerivedCategory.Plus.singleFunctor
            (ModuleSheaves Y.toRingedSpace) 0).obj G)) := by
  simpa [lerayPage] using
    ((Stacks.Cohomology.LerayCard.leraySpectralSequence.{u} f.toLRSHom.toShHom).pageTwoIso
      p q).app ((DerivedCategory.Plus.singleFunctor
        (ModuleSheaves Y.toRingedSpace) 0).obj G)

/-- **The second page of the Leray spectral sequence is `Hᵖ(X, Rᵍf_*G)`**, in the vocabulary of
schemes. -/
private noncomputable def lerayPageTwoIso {Y X : Scheme.{u}} (f : Y ⟶ X) (G : Y.Modules)
    (p q : ℤ) :
    ((lerayPage f G).page 2 (by omega)).X (p, q) ≅
      ((SheafOfModules.evaluation
          (structureSheafRing X.toRingedSpace)
          (op (⊤ : X.Opens))).rightDerivedPlus p).obj
        (((Scheme.Modules.pushforward f).rightDerivedPlus q).obj G) :=
  lerayPageTwoIsoRaw f G p q

/-- **The abutment of the Leray spectral sequence is the cohomology of `G` over `k`.** -/
private noncomputable def lerayAbutmentIso (k : Type u) [Field k] {Y X : Scheme.{u}}
    (f : Y ⟶ X) (g : X ⟶ Spec (.of k)) (G : Y.Modules) (n : ℕ) :
    (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).obj
        (lerayAbutment f G (n : ℤ)) ≅ cohomologyOverField k (f ≫ g) G n := by
  let R : Type u := Γ(X, ⊤)
  let ρ : k →+* R := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom
  let α : R →+* (Γ(Y, ⊤) : Type u) := (f.appTop).hom
  let EY := SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))
  have hEYadd : EY.Additive := by
    unfold EY SheafOfModules.evaluation
    infer_instance
  letI := hEYadd
  let S := ModuleCat.restrictScalars α
  let K := (DerivedCategory.Plus.singleFunctor
    (ModuleSheaves Y.toRingedSpace) 0).obj G
  have hHcmp : lerayAbutment f G (n : ℤ) ≅ S.obj ((EY.rightDerivedPlus (n : ℤ)).obj G) := by
    letI : HasDerivedCategory (ModuleCat.{u} (Γ(Y, ⊤) : Type u)) :=
      HasDerivedCategory.standard _
    first
      | exact exactDerivedPlusHomologyIso S (EY.rightDerivedFunctorPlus.obj K) (n : ℤ)
      | apply exactDerivedPlusHomologyIso
  have hmap : α.comp ρ = ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ g).appTop).hom := rfl
  have hrestr : (ModuleCat.restrictScalars.{u} ρ).obj
        (S.obj ((EY.rightDerivedPlus (n : ℤ)).obj G)) ≅
      (ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ g).appTop).hom).obj
        ((EY.rightDerivedPlus (n : ℤ)).obj G) := by
    rw [← hmap]
    exact ((ModuleCat.restrictScalarsComp ρ α).app _).symm
  refine (ModuleCat.restrictScalars.{u} ρ).mapIso hHcmp ≪≫ hrestr ≪≫ ?_
  rw [appTop_eq_appLE_top (f ≫ g)]
  exact (cohomologyOverFieldRightDerivedPlusIso k (f ≫ g) G n).symm

/-! ### The Euler characteristic of the higher direct images -/

/-- **[Stacks, Tag 0BEK], with [Stacks, Tag 02O5] and [Stacks, Tag 02O6] as hypotheses.** Let
`k` be a field, let `f : Y ⟶ X` be a morphism of schemes proper over `k` and let `G` be a
coherent `𝒪_Y`-module. Then `χ(Y, G) = ∑ᵢ (-1)ⁱ χ(X, Rⁱf_*G)`.

Both hypotheses are theorems, and
`AlgebraicGeometry.eulerCharacteristic_eq_finsum_higherDirectImage` is this statement with both
of them discharged. **The tag attribute sits there, not here.** -/
public theorem eulerCharacteristic_eq_finsum_higherDirectImage_of_hypotheses
    (h02O5 : ProperCoherentImage.HigherDirectImageIsCoherent.{u})
    (h02O6 : CohomologyFiniteDimensionalOverField.{u})
    (k : Type u) [Field k] {Y X : Scheme.{u}}
    (f : Y ⟶ X) (g : X ⟶ Spec (.of k))
    [IsProper g] [IsProper (f ≫ g)]
    (G : Y.Modules) [G.IsCoherent] :
    eulerCharacteristic k (f ≫ g) G =
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
        @eulerCharacteristic k _ X g _
          (((Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)).obj G)
          (h02O5 Y X f (LocallyOfFiniteType.isLocallyNoetherian g) (IsProper.of_comp f g) G
            inferInstance i) := by
  let : IsProper f := IsProper.of_comp f g
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  let : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  let R : Type u := Γ(X, ⊤)
  let ρ : k →+* R := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom
  let E := lerayPage f G
  let H := lerayAbutment f G
  have hAbuts : SpectralSequence.AbutsTo E H := abutsTo_lerayPage f G
  let EX := SheafOfModules.evaluation
    (structureSheafRing X.toRingedSpace) (op (⊤ : X.Opens))
  let FqS : ℤ → X.Modules := fun q => ((Scheme.Modules.pushforward f).rightDerivedPlus q).obj G
  let P := finiteDimensionalOverFieldProperty k R ρ
  have : P.IsWeakSerreClass := by
    dsimp [P]
    infer_instance
  have hFcoh : ∀ q : ℤ, 0 ≤ q → (FqS q).IsCoherent := by
    intro q hq
    have hq' : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq
    simpa [FqS, hq'] using (h02O5 Y X f inferInstance inferInstance G inferInstance q.toNat)
  have hpageIso (p q : ℤ) :
      (E.page 2 (by omega)).X (p, q) ≅ (EX.rightDerivedPlus p).obj (FqS q) :=
    lerayPageTwoIso f G p q
  obtain ⟨q₀, hqvan⟩ :=
    Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerivedPlus_pushforward f
  obtain ⟨p₀, hpvan⟩ :=
    Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerivedPlus_pushforward g
  have hpageZero : ∀ p q : ℤ, IsZero (FqS q) → IsZero ((E.page 2 (by omega)).X (p, q)) :=
    fun p q hz => IsZero.of_iso (rightDerivedPlus_map_isZero EX (FqS q) p hz) (hpageIso p q)
  have hglobalZero : ∀ p q : ℤ, 0 ≤ q → p₀ ≤ p →
      IsZero ((EX.rightDerivedPlus p).obj (FqS q)) := by
    intro p q hq hp
    let : (FqS q).IsCoherent := hFcoh q hq
    let : (FqS q).IsQuasicoherent := isQuasicoherent_of_isCoherent (FqS q)
    have hzpush := hpvan p hp (FqS q) inferInstance
    have hzsections : IsZero ((Stacks.Cohomology.AffineBase.moduleGlobalSections
        (Spec (.of k))).obj
          (((Scheme.Modules.pushforward g).rightDerivedPlus p).obj (FqS q))) :=
      (Stacks.Cohomology.AffineBase.moduleGlobalSections (Spec (.of k))).map_isZero hzpush
    have hIso :=
      (Stacks.Cohomology.AffineBase.cohomologyIsoGlobalSectionsRightDerivedPushforward g p).app
        ⟨FqS q, inferInstance⟩
    have hzrestr : IsZero ((ModuleCat.restrictScalars g.appTop.hom).obj
        ((EX.rightDerivedPlus p).obj (FqS q))) := (Iso.isZero_iff hIso).2 hzsections
    have hsub : Subsingleton ((EX.rightDerivedPlus p).obj (FqS q)) := by
      show Subsingleton ((ModuleCat.restrictScalars g.appTop.hom).obj
        ((EX.rightDerivedPlus p).obj (FqS q)))
      exact ModuleCat.subsingleton_of_isZero hzrestr
    exact ModuleCat.isZero_of_subsingleton _
  have hzeroPage : ∀ p q : ℤ, p < 0 ∨ q < 0 ∨ q₀ ≤ q ∨ p₀ ≤ p →
      IsZero ((E.page 2 (by omega)).X (p, q)) := by
    intro p q h
    by_cases hp : p < 0
    · exact IsZero.of_iso
        (Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj EX p hp (FqS q)) (hpageIso p q)
    · by_cases hq : q < 0
      · exact hpageZero p q (Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj
          (Scheme.Modules.pushforward f) q hq G)
      · by_cases hq₀ : q₀ ≤ q
        · exact hpageZero p q (hqvan q hq₀ G inferInstance)
        · have hp₀ : p₀ ≤ p := by
            rcases h with h | h | h | h
            · omega
            · omega
            · exact absurd h hq₀
            · exact h
          exact IsZero.of_iso (hglobalZero p q (by omega) hp₀) (hpageIso p q)
  have hP₂all : ∀ pq : ℤ × ℤ, P ((E.page 2 (by omega)).X pq) := by
    intro pq
    obtain ⟨p, q⟩ := pq
    by_cases hp : 0 ≤ p
    · by_cases hq : 0 ≤ q
      · have hpNat : ((p.toNat : ℕ) : ℤ) = p := Int.toNat_of_nonneg hp
        have htarget : P ((EX.rightDerivedPlus p).obj (FqS q)) := by
          show Module.Finite k (↑((ModuleCat.restrictScalars.{u} ρ).obj
            ((EX.rightDerivedPlus p).obj (FqS q))))
          rw [← hpNat]
          exact module_finite_restrictScalars_rightDerivedPlus h02O6 k g (FqS q)
            (hFcoh q hq) p.toNat
        exact P.prop_of_iso (hpageIso p q).symm htarget
      · exact P.prop_of_isZero (hzeroPage p q (Or.inr (Or.inl (by omega))))
    · exact P.prop_of_isZero (hzeroPage p q (Or.inl (by omega)))
  have hfin : {pq : ℤ × ℤ | ¬ IsZero ((E.page 2 (by omega)).X pq)}.Finite := by
    apply Set.Finite.subset
      ((Set.finite_Icc (0 : ℤ) (p₀ - 1)).prod (Set.finite_Icc (0 : ℤ) (q₀ - 1)))
    intro pq hpq
    simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · by_contra h
      exact hpq (hzeroPage pq.1 pq.2 (Or.inl (by omega)))
    · by_contra h
      exact hpq (hzeroPage pq.1 pq.2 (Or.inr (Or.inr (Or.inr (by omega)))))
    · by_contra h
      exact hpq (hzeroPage pq.1 pq.2 (Or.inr (Or.inl (by omega))))
    · by_contra h
      exact hpq (hzeroPage pq.1 pq.2 (Or.inr (Or.inr (Or.inl (by omega)))))
  obtain ⟨hfinH, hH, hHneg, hRankEuler⟩ :=
    finsum_negOnePow_finrank_eq_of_abutsTo k R ρ E 2 (by omega) H hAbuts hfin hP₂all
      (fun p q h => hzeroPage p q (h.elim Or.inl fun hq => Or.inr (Or.inl hq)))
  have hρg : ρ = ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ ⊤ (by simp)).hom := by
    rw [← appTop_eq_appLE_top g]
  let lhsRank : ℤ → ℤ := fun n => (n.negOnePow : ℤ) *
    (Module.finrank k (↑((ModuleCat.restrictScalars.{u} ρ).obj (H n))) : ℤ)
  have hLrankZero : ∀ n : ℤ, IsZero (H n) → lhsRank n = 0 := by
    intro n hz
    simp [lhsRank, finrank_restrictScalars_eq_zero_of_isZero k R ρ hz]
  have hLfinite : (Function.support lhsRank).Finite := hfinH.subset fun n hn hz =>
    hn (by simp [lhsRank, hLrankZero n hz])
  have hLzero : ∀ n < 0, lhsRank n = 0 := fun n hn => hLrankZero n (hHneg n hn)
  have hLtoNat := finsum_int_eq_nat_of_nonneg_support lhsRank hLfinite hLzero
  have hLcharacteristic : (∑ᶠ n : ℤ, lhsRank n) = eulerCharacteristic k (f ≫ g) G := by
    calc (∑ᶠ n : ℤ, lhsRank n) = ∑ᶠ n : ℕ, lhsRank n := hLtoNat
      _ = eulerCharacteristic k (f ≫ g) G := by
        rw [eulerCharacteristic_eq_finsum]
        refine finsum_congr fun n => ?_
        have hdim : Module.finrank k
              (↑((ModuleCat.restrictScalars.{u} ρ).obj (H (n : ℤ)))) =
            Module.finrank k (cohomologyOverField k (f ≫ g) G n) :=
          LinearEquiv.finrank_eq (lerayAbutmentIso k f g G n).toLinearEquiv
        have hsign : ((n : ℤ).negOnePow : ℤ) = (-1 : ℤ) ^ n := Int.coe_negOnePow_natCast n
        simp [lhsRank, hdim, hsign]
  let rhsRank : ℤ × ℤ → ℤ := fun pq => ((pq.1 + pq.2).negOnePow : ℤ) *
    (Module.finrank k (↑((ModuleCat.restrictScalars.{u} ρ).obj
      ((E.page 2 (by omega)).X pq))) : ℤ)
  have hRrankZero : ∀ pq : ℤ × ℤ, IsZero ((E.page 2 (by omega)).X pq) → rhsRank pq = 0 := by
    intro pq hz
    simp [rhsRank, finrank_restrictScalars_eq_zero_of_isZero k R ρ hz]
  have hRfinite : (Function.support rhsRank).Finite := hfin.subset fun pq hpq hz =>
    hpq (by simp [rhsRank, hRrankZero pq hz])
  have hRzero : ∀ p q : ℤ, p < 0 ∨ q < 0 → rhsRank (p, q) = 0 := fun p q hpq =>
    hRrankZero (p, q) (hzeroPage p q (hpq.elim Or.inl fun hq => Or.inr (Or.inl hq)))
  let rhsSwap : ℤ × ℤ → ℤ := fun qp => rhsRank (qp.2, qp.1)
  have hRswap : (∑ᶠ pq : ℤ × ℤ, rhsRank pq) = ∑ᶠ qp : ℤ × ℤ, rhsSwap qp :=
    (finsum_comp_equiv (Equiv.prodComm ℤ ℤ) (f := rhsRank)).symm
  have hRswapFinite : (Function.support rhsSwap).Finite :=
    (hRfinite.image (fun pq : ℤ × ℤ => (pq.2, pq.1))).subset fun qp hqp =>
      ⟨(qp.2, qp.1), hqp, by simp⟩
  have hRtoNat := finsum_int_prod_eq_nat_prod_of_nonneg_support rhsSwap hRswapFinite
    fun q p hqp => hRzero p q hqp.symm
  have hPageCoh (p q : ℤ) (hp : 0 ≤ p) (_hq : 0 ≤ q) :
      (ModuleCat.restrictScalars.{u} ρ).obj ((E.page 2 (by omega)).X (p, q)) ≅
        cohomologyOverField k g (FqS q) p.toNat := by
    have hpNat : ((p.toNat : ℕ) : ℤ) = p := Int.toNat_of_nonneg hp
    refine (ModuleCat.restrictScalars.{u} ρ).mapIso (hpageIso p q) ≪≫ ?_
    rw [hρg, ← hpNat]
    exact (cohomologyOverFieldRightDerivedPlusIso k g (FqS q) p.toNat).symm
  have hRrankCoh (p q : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
      rhsRank (p, q) = ((p + q).negOnePow : ℤ) *
        (Module.finrank k (cohomologyOverField k g (FqS q) p.toNat) : ℤ) := by
    let : Module.Finite k (↑((ModuleCat.restrictScalars.{u} ρ).obj
      ((E.page 2 (by omega)).X (p, q)))) := hP₂all (p, q)
    have hdim := LinearEquiv.finrank_eq (hPageCoh p q hp hq).toLinearEquiv
    simp [rhsRank, hdim]
  have hRcharacteristic : (∑ᶠ ij : ℕ × ℕ, rhsSwap ((ij.1 : ℤ), (ij.2 : ℤ))) =
      ∑ᶠ q : ℕ, (-1 : ℤ) ^ q *
        @eulerCharacteristic k _ X g _ (FqS (q : ℤ))
          (hFcoh (q : ℤ) (by positivity)) := by
    let rhsNat : ℕ × ℕ → ℤ := fun ij => rhsSwap ((ij.1 : ℤ), (ij.2 : ℤ))
    have hRnatFinite : (Function.support rhsNat).Finite := by
      refine (hRswapFinite.preimage (f := fun ij : ℕ × ℕ =>
        ((ij.1 : ℤ), (ij.2 : ℤ))) ?_).subset fun _ hij => hij
      exact fun _ _ _ _ h =>
        Prod.ext (Int.ofNat.inj (congrArg Prod.fst h)) (Int.ofNat.inj (congrArg Prod.snd h))
    show (∑ᶠ ij : ℕ × ℕ, rhsNat ij) = _
    rw [finsum_curry rhsNat hRnatFinite]
    refine finsum_congr fun q => ?_
    have hq : 0 ≤ (q : ℤ) := by positivity
    let : (FqS (q : ℤ)).IsCoherent := hFcoh (q : ℤ) hq
    show (∑ᶠ b : ℕ, rhsNat (q, b)) =
      (-1 : ℤ) ^ q • ∑ᶠ n : ℕ,
        (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k g (FqS (q : ℤ)) n) : ℤ)
    rw [smul_finsum]
    refine finsum_congr fun p => ?_
    have hp : 0 ≤ (p : ℤ) := by positivity
    have hterm := hRrankCoh p q hp hq
    show rhsRank ((p : ℤ), (q : ℤ)) = _
    rw [hterm]
    simp [Int.negOnePow_add, Int.coe_negOnePow_natCast, add_comm, mul_assoc]
  calc
    eulerCharacteristic k (f ≫ g) G = ∑ᶠ n : ℤ, lhsRank n := hLcharacteristic.symm
    _ = ∑ᶠ pq : ℤ × ℤ, rhsRank pq := hRankEuler
    _ = ∑ᶠ qp : ℤ × ℤ, rhsSwap qp := hRswap
    _ = ∑ᶠ ij : ℕ × ℕ, rhsSwap ((ij.1 : ℤ), (ij.2 : ℤ)) := hRtoNat
    _ = ∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
          @eulerCharacteristic k _ X g _
            (((Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)).obj G)
            (h02O5 Y X f (LocallyOfFiniteType.isLocallyNoetherian g) (IsProper.of_comp f g) G
              inferInstance i) := hRcharacteristic

end AlgebraicGeometry

end
