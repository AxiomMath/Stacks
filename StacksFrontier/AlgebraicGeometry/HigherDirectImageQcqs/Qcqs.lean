module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationIsomorphisms
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.LongExactSequence
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Basic
public import StacksFrontier.AlgebraicGeometry.InductionPrinciple.Basic
import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.RestrictPushforward
public import StacksFrontier.AlgebraicGeometry.QuasicoherentExtension.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.QuasiCoherentExtension
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic

/-!
# Quasi-coherence of the higher direct images along a quasi-compact, quasi-separated morphism

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes and `F` a
quasi-coherent `𝒪_X`-module. [Stacks, Tag 01XJ] asserts that every higher direct image
`R ᵖ f_* F` is quasi-coherent, and this file proves it in every degree.

`Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_higherDirectImage_zero` and
`Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_higherDirectImage_of_neg` discharge
the degrees that need no Mayer--Vietoris argument; what is proved here is the remaining content,
the positive degrees, by the argument of the source: quasi-coherence of `R ᵖ f_* F` is local on
`S`, so one may assume `S` affine, and then one inducts over the quasi-compact opens of `X`
with [Stacks, Tag 08DR], the affine case being [Stacks, Tag 01XC] and the induction step the
relative Mayer--Vietoris long exact sequence of [Stacks, Tag 01EC] together with the closure of
quasi-coherence under kernels, cokernels and extensions ([Stacks, Tag 01IC],
[Stacks, Tag 01IE]).

## Main results

* `Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_higherDirectImage`:
  **[Stacks, Tag 01XJ]**, quasi-coherence of `R ᵖ f_* F` for every integer `p`, with the higher
  direct images taken on the bounded below derived category.
* `Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_rightDerived`: the same for
  Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`.
* `Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_rightDerived_of_isProper`:
  the quasi-coherence clause of **[Stacks, Tag 0EX4]**, which is the previous statement for a
  proper morphism — properness supplies quasi-compactness and quasi-separatedness and is used
  for nothing else.

## Implementation notes

The relative Mayer--Vietoris sequence of [Stacks, Tag 01EC] is stated for morphisms of ringed
spaces, over `SheafOfModules (structureSheafRing X)`, whereas quasi-coherence
is a property of objects of `AlgebraicGeometry.Scheme.Modules`. The two spellings of the
category of modules on a scheme are definitionally equal but not syntactically so, and
`AlgebraicGeometry.Scheme.Modules` is a plain `def` whose `Category` instance has its own `Hom`
field, so type class synthesis transports nothing between them. Every comparison is therefore
made once, by ascribing the scheme-level type to the morphisms of the Mayer--Vietoris sequence
(`a`, `b`, `c`, `d` below), after which the whole argument runs at the scheme-level spelling;
the two steps that consume the sequence, `isQuasicoherent_biprodFunctor_obj` and
`isQuasicoherent_of_exactFour`, are stated there as well. The Mayer--Vietoris induction step is
a theorem of its own rather than a branch of the induction, so that it is elaborated against
its own heartbeat budget.

The two indexings of the higher right derived functors are compared by
`Stacks.DerivedIndexing.rightDerivedIso`, and the derived category instance is the one the
source statements use, `CategoryTheory.HasDerivedCategory.standard`, installed as a local
instance.

## References

* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 01EC](https://stacks.math.columbia.edu/tag/01EC)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.HigherDirectImageQcoh

/-- [Stacks, Tag 08DR] in the shape the induction below uses: the hypotheses are phrased with
`X.affineOpens` rather than with an affineness side condition. -/
private theorem induction_isCompact_open_affine {X : Scheme.{u}} [QuasiSeparatedSpace X]
    {P : X.Opens → Prop} (U : X.Opens) (hU : IsCompact (U : Set X))
    (affine : ∀ U : X.affineOpens, P U)
    (sup : ∀ (U : X.Opens) (_ : IsCompact (U : Set X)) (V : X.affineOpens),
      P U → P V → P (U ⊓ V) → P (U ⊔ V)) :
    P U :=
  Stacks.AlgebraicGeometry.InductionPrinciple.induction_isCompact_open P
    (fun V hV => affine ⟨V, hV⟩)
    (fun V W hV hW hPV hPW hPinter => sup V hV ⟨W, hW⟩ hPV hPW hPinter) U hU

private lemma isQuasicoherent_of_iso {S : Scheme.{u}} (M N : S.Modules) (e : M ≅ N)
    (hM : M.IsQuasicoherent) : N.IsQuasicoherent := by
  let : M.IsQuasicoherent := hM
  exact CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms.of_iso
    (P := SheafOfModules.isQuasicoherent S.ringCatSheaf) e inferInstance

private noncomputable def schemeHigherDirectImageRestrictIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (p : ℕ) :
    Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
        (Scheme.Modules.pushforward (f ∣_ V)).rightDerived p ≅
      (Scheme.Modules.pushforward f).rightDerived p ⋙
        Scheme.Modules.restrictFunctor V.ι := by
  rw [Stacks.LocalCohomology.schemeRestrictFunctor_eq_moduleRestriction X (f ⁻¹ᵁ V),
    Stacks.LocalCohomology.schemeRestrictFunctor_eq_moduleRestriction Y V]
  change Stacks.Cohomology.HigherDirectImage.moduleRestriction X.toRingedSpace (f ⁻¹ᵁ V) ⋙
      (RingedSpaceModuleAdjunction.modulePushforward
        (f ∣_ V).toLRSHom.toShHom).rightDerived p ≅
    (RingedSpaceModuleAdjunction.modulePushforward f.toLRSHom.toShHom).rightDerived p ⋙
      Stacks.Cohomology.HigherDirectImage.moduleRestriction Y.toRingedSpace V
  rw [Stacks.LocalCohomology.ringedRestrictEq f V]
  exact Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso f.toLRSHom.toShHom V p

private noncomputable def schemeRightDerivedPlusRestrictObjIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (p : ℕ) (F : X.Modules) :
    ((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (p : ℤ)).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F) ≅
      (Scheme.Modules.restrictFunctor V.ι).obj
        (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj F) :=
  CategoryTheory.rightDerivedPlusObjIso (Scheme.Modules.pushforward (f ∣_ V))
    ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F) p ≪≫
  (schemeHigherDirectImageRestrictIso f V p).app F ≪≫
  (Scheme.Modules.restrictFunctor V.ι).mapIso
    (CategoryTheory.rightDerivedPlusObjIso (Scheme.Modules.pushforward f) F p).symm

private noncomputable def rightDerivedIsoOfFunctorIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasInjectiveResolutions C] (F G : C ⥤ D) [F.Additive] [G.Additive]
    (e : F ≅ G) (n : ℕ) : F.rightDerived n ≅ G.rightDerived n := by
  let α := NatTrans.rightDerived e.hom n
  let β := NatTrans.rightDerived e.inv n
  refine ⟨α, β, ?_, ?_⟩
  · rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  · rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

private noncomputable def nestedOpenHigherDirectImageIso
    {X S Y Z : Scheme.{u}} (f : X ⟶ S) (j : Y ⟶ X) (i : Z ⟶ Y)
    (M : X.Modules) (n : ℕ) :
    (((Scheme.Modules.pushforward (i ≫ (j ≫ f))).rightDerived n).obj
        ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback j).obj M))) ≅
      (((Scheme.Modules.pushforward ((i ≫ j) ≫ f)).rightDerived n).obj
        ((Scheme.Modules.pullback (i ≫ j)).obj M)) :=
  (rightDerivedIsoOfFunctorIso _ _ (Scheme.Modules.pushforwardCongr (Category.assoc i j f).symm)
      n).app ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback j).obj M)) ≪≫
    ((Scheme.Modules.pushforward ((i ≫ j) ≫ f)).rightDerived n).mapIso
      ((Scheme.Modules.pullbackComp i j).app M)

private lemma pullback_open_isQuasicoherent {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsOpenImmersion i] (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback i).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback i).app M) inferInstance

private lemma shortExact_coker_kernel_of_exact_pairs {C : Type*} [Category C] [Abelian C]
    {A B M D E : C} (a : A ⟶ B) (b : B ⟶ M) (c : M ⟶ D) (d : D ⟶ E)
    (hab : Stacks.Cohomology.RelativeMayerVietoris.MorphismPairExact a b)
    (hbc : Stacks.Cohomology.RelativeMayerVietoris.MorphismPairExact b c)
    (hcd : Stacks.Cohomology.RelativeMayerVietoris.MorphismPairExact c d) :
    (ShortComplex.mk
      (cokernel.desc a b hab.choose)
      (kernel.lift d c hcd.choose)
      (by
        apply (cancel_epi (cokernel.π a)).1
        apply (cancel_mono (kernel.ι d)).1
        simp [Category.assoc, kernel.lift_ι, hbc.choose]) :
      ShortComplex C).ShortExact := by
  obtain ⟨habz, habexact⟩ := hab
  obtain ⟨hbcz, hbcexact⟩ := hbc
  obtain ⟨hcdz, hcdexact⟩ := hcd
  let α := cokernel.desc a b habz
  let β := kernel.lift d c hcdz
  have hzero₁ : α ≫ c = 0 := by
    apply (cancel_epi (cokernel.π a)).1
    simp [α, hbcz]
  let T₀ : ShortComplex C := ShortComplex.mk b c hbcz
  let T₁ : ShortComplex C := ShortComplex.mk α c hzero₁
  let φ : T₀ ⟶ T₁ := ShortComplex.Hom.mk (cokernel.π a) (𝟙 M) (𝟙 D) (by
    simp [T₀, T₁, α]) (by simp [T₀, T₁])
  have hT₁ : T₁.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp hbcexact
  let T₂ : ShortComplex C := ShortComplex.mk α β (by
    apply (cancel_epi (cokernel.π a)).1
    apply (cancel_mono (kernel.ι d)).1
    simp [Category.assoc, α, β, kernel.lift_ι, hbcz])
  let ψ : T₂ ⟶ T₁ := ShortComplex.Hom.mk (𝟙 (cokernel a)) (𝟙 M) (kernel.ι d) (by
    simp [T₁, T₂]) (by simp [T₁, T₂, β])
  have hT₂ : T₂.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mpr hT₁
  have hmono : Mono α := (ShortComplex.mk a b habz).exact_iff_mono_cokernel_desc.mp habexact
  have hepi : Epi β := (ShortComplex.mk c d hcdz).exact_iff_epi_kernel_lift.mp hcdexact
  exact ShortComplex.ShortExact.mk' hT₂ hmono hepi

private lemma isQuasicoherent_biprod {X : Scheme.{u}} [IsAffine X]
    (M N : X.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⊞ N).IsQuasicoherent := by
  let T : ShortComplex X.Modules :=
    ShortComplex.mk (biprod.inl : M ⟶ M ⊞ N) biprod.snd (by simp)
  have hT : T.ShortExact :=
    (ShortComplex.Splitting.ofHasBinaryBiproduct M N).shortExact
  exact Stacks.AlgebraicGeometry.QuasicoherentExtension.isQuasicoherent_middle_of_shortExact T hT

private lemma isQuasicoherent_biprodFunctor_obj {S Y : Scheme.{u}} [IsAffine S]
    (F G : Y.Modules ⥤ S.Modules) (N : Y.Modules)
    (hF : (F.obj N).IsQuasicoherent) (hG : (G.obj N).IsQuasicoherent) :
    ((F ⊞ G).obj N).IsQuasicoherent := by
  let : (F.obj N).IsQuasicoherent := hF
  let : (G.obj N).IsQuasicoherent := hG
  let E : (Y.Modules ⥤ S.Modules) ⥤ S.Modules :=
    (CategoryTheory.evaluation Y.Modules S.Modules).obj N
  have : E.Additive := inferInstance
  have : PreservesFiniteLimits E := inferInstance
  have : PreservesBinaryBiproducts E :=
    preservesBinaryBiproducts_of_preservesBinaryProducts E
  exact isQuasicoherent_of_iso _ _ (E.mapBiprod F G).symm
    (isQuasicoherent_biprod (F.obj N) (G.obj N))

private lemma isQuasicoherent_of_exactFour {S : Scheme.{u}} [IsAffine S]
    {P Q N P' Q' : S.Modules} (a : P ⟶ Q) (b : Q ⟶ N) (c : N ⟶ P') (d : P' ⟶ Q')
    (hab : Stacks.Cohomology.RelativeMayerVietoris.MorphismPairExact a b)
    (hbc : Stacks.Cohomology.RelativeMayerVietoris.MorphismPairExact b c)
    (hcd : Stacks.Cohomology.RelativeMayerVietoris.MorphismPairExact c d)
    (hP : P.IsQuasicoherent) (hQ : Q.IsQuasicoherent)
    (hP' : P'.IsQuasicoherent) (hQ' : Q'.IsQuasicoherent) : N.IsQuasicoherent := by
  let : P.IsQuasicoherent := hP
  let : Q.IsQuasicoherent := hQ
  let : P'.IsQuasicoherent := hP'
  let : Q'.IsQuasicoherent := hQ'
  let : (cokernel a).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel a
  let : (kernel d).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel d
  exact Stacks.AlgebraicGeometry.QuasicoherentExtension.isQuasicoherent_middle_of_shortExact _
    (shortExact_coker_kernel_of_exact_pairs a b c d hab hbc hcd)

private theorem opensRange_comp_preimage {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (W U : X.Opens) (hW : j.opensRange = W) (hUW : U ≤ W) :
    Set.range ((j ⁻¹ᵁ U).ι ≫ j).base = U := by
  show (((j ⁻¹ᵁ U).ι ≫ j).opensRange : Set X) = U
  rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
    Scheme.Hom.image_preimage_eq_opensRange_inf, hW]
  exact inf_eq_right.mpr hUW

open Stacks.Cohomology.Affine.HigherDirectImage in
/-- **The affine case of the induction.** If the image of the open immersion `j` is an affine
open then `j ≫ f` is an affine morphism, and the higher direct images along an affine morphism
are quasi-coherent in every degree: that is [Stacks, Tag 01XC], in the form
`isQuasicoherent_rightDerivedNat_pushforward_of_isAffineHom`. -/
private theorem rightDerived_isQuasicoherent_of_affine_image
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S] (M : X.Modules)
    [M.IsQuasicoherent] {U : X.Opens} (hU : IsAffine U.toScheme)
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (hj : Set.range j.base = U) (n : ℕ) :
    ((((Scheme.Modules.pushforward (j ≫ f)).rightDerived n).obj
      ((Scheme.Modules.pullback j).obj M)).IsQuasicoherent) := by
  have hRange : j.opensRange = U := SetLike.coe_injective hj
  have : IsAffine j.opensRange.toScheme := by simpa [hRange] using hU
  have : IsAffine Y := IsAffine.of_isIso j.isoOpensRange.hom
  have : IsAffineHom (j ≫ f) := by
    apply AlgebraicGeometry.isAffineHom_of_isAffine
  have : ((Scheme.Modules.pullback j).obj M).IsQuasicoherent :=
    pullback_open_isQuasicoherent j M
  exact isQuasicoherent_rightDerivedNat_pushforward_of_isAffineHom
    (j ≫ f) ((Scheme.Modules.pullback j).obj M) n

private def affineTargetOpenProperty {X S : Scheme.{u}} (f : X ⟶ S)
    (M : X.Modules) [M.IsQuasicoherent] (p : ℕ) (U : X.Opens) : Prop :=
  ∀ {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j],
    Set.range j.base = U →
    ∀ n : ℕ, n ≤ p →
      ((((Scheme.Modules.pushforward (j ≫ f)).rightDerived n).obj
        ((Scheme.Modules.pullback j).obj M)).IsQuasicoherent)

private theorem rightDerived_isQuasicoherent_sup_step
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [IsAffine S] (M : X.Modules) [M.IsQuasicoherent] (p : ℕ)
    (U V : X.Opens)
    (hPU : affineTargetOpenProperty f M p U)
    (hPV : affineTargetOpenProperty f M p V)
    (hPinter : affineTargetOpenProperty f M p (U ⊓ V))
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (hRange : Set.range j.base = (U ⊔ V : X.Opens)) (n : ℕ) (hn : n ≤ p)
    (hnpos : 0 < n) :
    (((Scheme.Modules.pushforward (j ≫ f)).rightDerived n).obj
      ((Scheme.Modules.pullback j).obj M)).IsQuasicoherent := by
  let A : Y.Opens := j ⁻¹ᵁ (U : X.Opens)
  let B : Y.Opens := j ⁻¹ᵁ (V : X.Opens)
  let C : Y.Opens := A ⊓ B
  have hcover : A ⊔ B = ⊤ := by
    ext y
    refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
    have hy : j.base y ∈ (U : X.Opens) ⊔ (V : X.Opens) := by
      have hy' : j.base y ∈ Set.range j.base := ⟨y, rfl⟩
      simpa [hRange] using hy'
    simpa [A, B] using hy
  have hintersection : Set.range C.ι.base =
      Set.range A.ι.base ∩ Set.range B.ι.base := by
    ext y
    simp [A, B, C]
  let iA : A.toScheme ⟶ Y := A.ι
  let iB : B.toScheme ⟶ Y := B.ι
  let iC : C.toScheme ⟶ Y := C.ι
  let fY : Y ⟶ S := j ≫ f
  let iAR := iA.toLRSHom.toShHom
  let iBR := iB.toLRSHom.toShHom
  let iCR := iC.toLRSHom.toShHom
  let fYR := fY.toLRSHom.toShHom
  have hcoverR : Set.range iAR.hom.base ∪ Set.range iBR.hom.base = Set.univ := by
    show Set.range iA.base ∪ Set.range iB.base = Set.univ
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    simpa [iA, iB] using congrArg (fun T : Y.Opens => (T : Set Y)) hcover
  have hinterR : Set.range iCR.hom.base = Set.range iAR.hom.base ∩
      Set.range iBR.hom.base := by
    show Set.range iC.base = Set.range iA.base ∩ Set.range iB.base
    simpa [iA, iB, iC] using hintersection
  let : SheafedSpace.IsOpenImmersion iAR := by infer_instance
  let : SheafedSpace.IsOpenImmersion iBR := by infer_instance
  let : SheafedSpace.IsOpenImmersion iCR := by infer_instance
  obtain ⟨MV⟩ := Stacks.Cohomology.RelativeMayerVietoris.relativeMayerVietoris
    fYR iAR iBR iCR hcoverR hinterR
  let MY := (Scheme.Modules.pullback j).obj M
  let n' := n - 1
  have hn' : n' ≤ p := by omega
  let nNext := n' + 1
  have hn'_add : nNext = n := Nat.sub_add_cancel hnpos
  have hnNext : nNext ≤ p := hn'_add.le.trans hn
  have hrangeA : Set.range (iA ≫ j).base = U :=
    opensRange_comp_preimage j (U ⊔ V) U (SetLike.coe_injective hRange) le_sup_left
  have hrangeB : Set.range (iB ≫ j).base = V :=
    opensRange_comp_preimage j (U ⊔ V) V (SetLike.coe_injective hRange) le_sup_right
  have hrangeC : Set.range (iC ≫ j).base = U ⊓ V := by
    have hC : C = j ⁻¹ᵁ (U ⊓ V) := by
      ext y
      simp [A, B, C]
    show Set.range (C.ι ≫ j).base = U ⊓ V
    rw [hC]
    exact opensRange_comp_preimage j (U ⊔ V) (U ⊓ V) (SetLike.coe_injective hRange)
      (inf_le_left.trans le_sup_left)
  have key : ∀ {Z : Scheme.{u}} (i : Z ⟶ Y) [IsOpenImmersion i] (P : X.Opens)
      (hP : affineTargetOpenProperty f M p P) (hr : Set.range (i ≫ j).base = P)
      (m : ℕ) (hm : m ≤ p),
      ((Stacks.Cohomology.RelativeMayerVietoris.restrictedHigherDirectImage
        fYR i.toLRSHom.toShHom m).obj MY).IsQuasicoherent := by
    intro Z i _ P hP hr m hm
    show (((Scheme.Modules.pushforward (i ≫ (j ≫ f))).rightDerived m).obj
      ((Scheme.Modules.pullback i).obj MY)).IsQuasicoherent
    exact isQuasicoherent_of_iso _ _ (nestedOpenHigherDirectImageIso f j i M m).symm
      (hP (i ≫ j) hr m hm)
  let FA : Y.Modules ⥤ S.Modules :=
    Stacks.Cohomology.RelativeMayerVietoris.restrictedHigherDirectImage fYR iAR n'
  let FB : Y.Modules ⥤ S.Modules :=
    Stacks.Cohomology.RelativeMayerVietoris.restrictedHigherDirectImage fYR iBR n'
  let FC : Y.Modules ⥤ S.Modules :=
    Stacks.Cohomology.RelativeMayerVietoris.restrictedHigherDirectImage fYR iCR n'
  let GA : Y.Modules ⥤ S.Modules :=
    Stacks.Cohomology.RelativeMayerVietoris.restrictedHigherDirectImage fYR iAR nNext
  let GB : Y.Modules ⥤ S.Modules :=
    Stacks.Cohomology.RelativeMayerVietoris.restrictedHigherDirectImage fYR iBR nNext
  let GC : Y.Modules ⥤ S.Modules :=
    Stacks.Cohomology.RelativeMayerVietoris.restrictedHigherDirectImage fYR iCR nNext
  let H : Y.Modules ⥤ S.Modules :=
    Stacks.Cohomology.RelativeMayerVietoris.higherDirectImage fYR nNext
  let a : (FA ⊞ FB).obj MY ⟶ FC.obj MY := (MV.toIntersection n').app MY
  let b : FC.obj MY ⟶ H.obj MY := (MV.boundary n').app MY
  let c : H.obj MY ⟶ (GA ⊞ GB).obj MY := (MV.toCover nNext).app MY
  let d : (GA ⊞ GB).obj MY ⟶ GC.obj MY := (MV.toIntersection nNext).app MY
  have hab : Stacks.Cohomology.RelativeMayerVietoris.MorphismPairExact a b :=
    MV.exact_intersection n' MY
  have hbc : Stacks.Cohomology.RelativeMayerVietoris.MorphismPairExact b c :=
    MV.exact_base n' MY
  have hcd : Stacks.Cohomology.RelativeMayerVietoris.MorphismPairExact c d :=
    MV.exact_cover nNext MY
  have hFA : (FA.obj MY).IsQuasicoherent := key iA U hPU hrangeA n' hn'
  have hFB : (FB.obj MY).IsQuasicoherent := key iB V hPV hrangeB n' hn'
  have hFC : (FC.obj MY).IsQuasicoherent := key iC (U ⊓ V) hPinter hrangeC n' hn'
  have hGA : (GA.obj MY).IsQuasicoherent := key iA U hPU hrangeA nNext hnNext
  have hGB : (GB.obj MY).IsQuasicoherent := key iB V hPV hrangeB nNext hnNext
  have hGC : (GC.obj MY).IsQuasicoherent := key iC (U ⊓ V) hPinter hrangeC nNext hnNext
  have hmiddle : (H.obj MY).IsQuasicoherent :=
    isQuasicoherent_of_exactFour a b c d hab hbc hcd
      (isQuasicoherent_biprodFunctor_obj FA FB MY hFA hFB) hFC
      (isQuasicoherent_biprodFunctor_obj GA GB MY hGA hGB) hGC
  rw [← hn'_add]
  show (((Scheme.Modules.pushforward (j ≫ f)).rightDerived nNext).obj
    ((Scheme.Modules.pullback j).obj M)).IsQuasicoherent
  exact hmiddle

private theorem rightDerived_isQuasicoherent_of_qcqs_affineTarget
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [IsAffine S] (M : X.Modules) [M.IsQuasicoherent] (p : ℕ) :
    ((Scheme.Modules.pushforward f).rightDerived p).obj M |>.IsQuasicoherent := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X :=
    AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated f
  have htop : IsCompact (Set.univ : Set X) := isCompact_univ
  have hP : affineTargetOpenProperty f M p ⊤ :=
    induction_isCompact_open_affine (X := X)
    (P := affineTargetOpenProperty f M p) ⊤ htop
    (fun (U : X.affineOpens) {Y} (j : Y ⟶ X) [IsOpenImmersion j]
      (hRange : Set.range j.base = U) (n : ℕ) (hn : n ≤ p) =>
      rightDerived_isQuasicoherent_of_affine_image f M U.2 j hRange n)
    (fun (U : X.Opens) (hU : IsCompact (U : Set X)) (V : X.affineOpens)
      (hPU : affineTargetOpenProperty f M p U)
      (hPV : affineTargetOpenProperty f M p V)
      (hPinter : affineTargetOpenProperty f M p (U ⊓ (V : X.Opens)))
      {Y} (j : Y ⟶ X) [IsOpenImmersion j]
      (hRange : Set.range j.base = U ⊔ V) (n : ℕ) (hn : n ≤ p) => by
      by_cases hn0 : n = 0
      · subst n
        let G := Scheme.Modules.pushforward (j ≫ f)
        have hRangeOpen : IsOpen (Set.range j.base) := by
          rw [hRange]
          exact U.2.union (V : X.Opens).2
        have hRangeCompact : IsCompact (Set.range j.base) := by
          rw [hRange]
          exact hU.union V.2.isCompact
        have : QuasiCompact j := by
          rw [quasiCompact_iff_forall_isAffineOpen]
          intro W hW
          show IsCompact (j.base ⁻¹' (W : Set X))
          apply j.isOpenEmbedding.isEmbedding.isCompact_iff.mpr
          rw [Set.image_preimage_eq_inter_range]
          simpa [Set.inter_comm] using
            (QuasiSeparatedSpace.inter_isCompact _ _ hRangeOpen hRangeCompact
              W.2 hW.isCompact)
        have : QuasiCompact (j ≫ f) := by infer_instance
        have : QuasiSeparated (j ≫ f) := by infer_instance
        have : ((Scheme.Modules.pullback j).obj M).IsQuasicoherent :=
          pullback_open_isQuasicoherent j M
        have hG : (G.obj ((Scheme.Modules.pullback j).obj M)).IsQuasicoherent :=
          AlgebraicGeometry.pushforward_isQuasicoherent (j ≫ f) _
        exact isQuasicoherent_of_iso _ _
          ((Functor.rightDerivedZeroIsoSelf G).app _).symm hG
      · exact rightDerived_isQuasicoherent_sup_step f M p U V hPU hPV hPinter j hRange n
          hn (Nat.pos_of_ne_zero hn0))
  have htopQC := hP (𝟙 X) (by simp) p le_rfl
  exact isQuasicoherent_of_iso _ _
    ((rightDerivedIsoOfFunctorIso _ _ (Scheme.Modules.pushforwardCongr (Category.id_comp f)) p).app
        ((Scheme.Modules.pullback (𝟙 X)).obj M) ≪≫
      ((Scheme.Modules.pushforward f).rightDerived p).mapIso
        ((Scheme.Modules.pullbackId X).app M)) htopQC

/-- **The positive degrees of [Stacks, Tag 01XJ].** Quasi-coherence of `R ⁿ f_* F` is local on
the base, so it may be checked on the affine opens of `S`, where
`rightDerived_isQuasicoherent_of_qcqs_affineTarget` applies to the restricted morphism. -/
private theorem isQuasicoherent_higherDirectImage_of_nat {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F).IsQuasicoherent :=
  AlgebraicGeometry.isQuasicoherent_of_restrict_isAffineOpen _ (fun U hU => by
    let FU := (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F
    have hFU : FU.IsQuasicoherent := by
      show ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F).IsQuasicoherent
      infer_instance
    let : FU.IsQuasicoherent := hFU
    have hLocalNat :
        (((Scheme.Modules.pushforward (f ∣_ U)).rightDerived n).obj FU).IsQuasicoherent := by
      let : IsAffine U.toScheme := hU
      exact rightDerived_isQuasicoherent_of_qcqs_affineTarget (f ∣_ U) FU n
    have hLocalPlus :
        (((Scheme.Modules.pushforward (f ∣_ U)).rightDerivedPlus
          (n : ℤ)).obj FU).IsQuasicoherent :=
      isQuasicoherent_of_iso _ _
        (CategoryTheory.rightDerivedPlusObjIso
          (Scheme.Modules.pushforward (f ∣_ U)) FU n).symm hLocalNat
    exact isQuasicoherent_of_iso _ _ (schemeRightDerivedPlusRestrictObjIso f U n F) hLocalPlus)

/-- **Stacks Project, Tag 01XJ (quasicoherence).** The higher direct images of a
quasi-coherent module under a quasi-compact and quasi-separated morphism of schemes are
quasi-coherent. -/
@[stacks 01XJ "quasicoherence", ega "III 1.4.10" "more general"]
instance isQuasicoherent_higherDirectImage {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] (p : ℤ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsQuasicoherent :=
  isQuasicoherent_higherDirectImage_of_forall_pos f F
    (fun n _ => isQuasicoherent_higherDirectImage_of_nat f F n) p

/-- **[Stacks, Tag 01XJ], quasi-coherence, for Mathlib's `ℕ`-indexed right derived functors.**
The higher direct images of a quasi-coherent module along a quasi-compact and quasi-separated
morphism of schemes are quasi-coherent. -/
instance isQuasicoherent_rightDerived {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerived i).obj F).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) i).app F).symm
    (isQuasicoherent_higherDirectImage f F i)

/-- **Stacks Project, Tag 0EX4 (quasi-coherence).** Higher direct images of a quasi-coherent
module under a proper morphism are quasi-coherent: a proper morphism is quasi-compact and
quasi-separated, and properness is used for nothing else. -/
@[stacks 0EX4 "quasi-coherence"]
instance isQuasicoherent_rightDerived_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerived i).obj F).IsQuasicoherent :=
  isQuasicoherent_rightDerived f F i

end Stacks.AlgebraicGeometry.HigherDirectImageQcoh

end
