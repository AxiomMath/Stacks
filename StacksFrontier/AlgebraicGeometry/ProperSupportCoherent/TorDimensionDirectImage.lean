module

public import StacksFrontier.AlgebraicGeometry.AffineVanishingQuasicoherentComplex
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.MayerVietorisTorDimension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.TorDimensionOpenBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubsetCompact
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Functoriality
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PerfectDirectImage
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeAffineTransport
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBridge
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeOverSheaf
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange

/-!
# The Tor-dimension half of Stacks 08EV

Let `g : Y ⟶ W` be a morphism of schemes and `B` an object of `D(𝒪_Y)` with quasi-coherent
cohomology sheaves and finite Tor dimension over the base (`AlgebraicGeometry.HasTorAmplitudeOver`,
equivalently over `g⁻¹𝒪_W`, by
`AlgebraicGeometry.hasTorAmplitude_derivedScalarRestriction_iff_hasTorAmplitudeOver`). If `W` is
affine and `Y` is quasi-compact and quasi-separated, then `Rg_*B` has finite Tor dimension on `W`.

## Main results

* `AlgebraicGeometry.hasTorAmplitudeOver_restrictFunctor`: Tor amplitude over the base is
  inherited by the restriction to an open subscheme.
* `AlgebraicGeometry.hasTorAmplitude_schemeDerivedPushforward_of_isAffine_of_hasTorAmplitudeOver`:
  the case of a morphism of affine schemes, with the same interval.
* `AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_of_hasTorAmplitudeOver`: the
  case of a quasi-compact quasi-separated source over an affine base.
* `AlgebraicGeometry.locallyHasFiniteTorDimension_derivedPushforward_of_isProperOver`: the
  Tor-dimension half for a morphism locally of finite type to a locally Noetherian scheme and an
  object whose cohomological support is proper over the base.
* [Stacks, Tag 08EV], under exactly the source's hypotheses:
  `Stacks.AlgebraicGeometry.ProperSupportCoherent.isPerfect_derivedPushforward_of_isProperOver_supp`

## Implementation notes

On a morphism of affine schemes the statement is commutative algebra. Up to
`AlgebraicGeometry.Scheme.isoSpec` the morphism is `Spec Γ(Z) ⟶ Spec Γ(W)` and `B` is the
sheafification of a complex `M` of `Γ(Z)`-modules ([Stacks, Tag 06Z0]); Tor amplitude of `M̃` over
the base is Tor amplitude of `M` over `Γ(W)` ([Stacks, Tag 0DHY], in the stalkwise reading
`AlgebraicGeometry.AffineRelativeTorAmplitude.hasTorAmplitudeOver_tildeComplex_iff`); the derived
direct image of `M̃` is the sheafification of `M` read over `Γ(W)` ([Stacks, Tag 0A9F]); and the
Tor amplitude of a sheafified complex is that of the complex ([Stacks, Tag 08E9]). The general
case is the Mayer--Vietoris induction
`AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_of_affine_induction`.

## References

* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
* [Stacks Project, Tag 0DHY](https://stacks.math.columbia.edu/tag/0DHY)
* [Stacks Project, Tag 0A9F](https://stacks.math.columbia.edu/tag/0A9F)
* [Stacks Project, Tag 08E9](https://stacks.math.columbia.edu/tag/08E9)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.TorAmplitude StacksDraft.TorAmplitude
open CategoryTheory.Pretriangulated Stacks.Cohomology.RelativeMayerVietoris
open Stacks.SchemeCohomology (hom)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Tor amplitude over the base is inherited by the restriction to an open subscheme.** For an
open immersion `j : V ⟶ X`, if `E` has Tor amplitude in `[a, b]` over `f : X ⟶ S`, its restriction
to `V` has Tor amplitude in `[a, b]` over `j ≫ f`. -/
theorem hasTorAmplitudeOver_restrictFunctor {V X S : Scheme.{u}} (f : X ⟶ S) (j : V ⟶ X)
    [IsOpenImmersion j] (E : DerivedCategory X.Modules) (a b : ℤ)
    (hE : HasTorAmplitudeOver f E a b) :
    HasTorAmplitudeOver (j ≫ f) ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj E)
      a b :=
  hasTorAmplitudeOver_of_iso ((Scheme.Modules.derivedRestrictIsoDerivedPullback j).app E).symm
    a b (hasTorAmplitudeOver_derivedPullback_of_isOpenImmersion f j E a b hE)

/-- **The Tor-dimension half of [Stacks, Tag 08EV] for a morphism of affine schemes.** Let
`h : Z ⟶ W` be a morphism of affine schemes and `B` an object of `D(𝒪_Z)` with quasi-coherent
cohomology sheaves and Tor amplitude in `[a, b]` over `W`. Then `Rh_*B` has Tor amplitude in
`[a, b]` on `W`. -/
theorem hasTorAmplitude_schemeDerivedPushforward_of_isAffine_of_hasTorAmplitudeOver
    {Z W : Scheme.{u}} [IsAffine Z] [IsAffine W] (h : Z ⟶ W) (B : DerivedCategory Z.Modules)
    (hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor Z.Modules i).obj B).IsQuasicoherent)
    (a b : ℤ) (hB : HasTorAmplitudeOver h B a b) :
    HasTorAmplitude W.toRingedSpace ((schemeDerivedPushforward h).obj B) a b := by
  have hle : (⊤ : Z.Opens) ≤ h ⁻¹ᵁ ⊤ := by simp
  have happ : h.appLE ⊤ ⊤ hle = h.appTop := Stacks.AffineAlgebraEquivalence.appLE_top_top h hle
  let : Algebra Γ(W, ⊤) Γ(Z, ⊤) := h.appTop.hom.toAlgebra
  set B' := (Scheme.Modules.restrictFunctor Z.isoSpec.inv).mapDerivedCategory.obj B
  have hAqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec Γ(Z, ⊤)).Modules i).obj
      B').IsQuasicoherent :=
    isQuasicoherent_homology_restrictFunctor_mapDerivedCategory Z.isoSpec.inv hqc
  obtain ⟨M, ⟨eM⟩⟩ := exists_tildeComplex_iso Γ(Z, ⊤) B' hAqc
  have h₁ : HasTorAmplitudeOver (Spec.map h.appTop) B' a b :=
    hasTorAmplitudeOver_of_iso
      (Scheme.Modules.derivedPullbackObjIsoRestrictFunctor Z.isoSpec.inv B) a b
      ((hasTorAmplitudeOver_specMap_appTop_iff h B a b).2 hB)
  have h₂ : HasTorAmplitudeCanonical Γ(W, ⊤) (DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars (algebraMap Γ(W, ⊤) Γ(Z, ⊤))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)) a b :=
    (AffineRelativeTorAmplitude.hasTorAmplitudeOver_tildeComplex_iff Γ(W, ⊤) Γ(Z, ⊤) M a b).1
      (hasTorAmplitudeOver_of_iso eM a b h₁)
  have h₃ : HasTorAmplitude (Spec Γ(W, ⊤)).toRingedSpace
      ((schemeDerivedPushforward (Spec.map h.appTop)).obj B') a b :=
    FlatOpcycles.hasTorAmplitude_of_iso (X := (Spec Γ(W, ⊤)).toRingedSpace)
      ((hasTorAmplitude_tilde_iff _ a b).2 h₂)
      ((schemeDerivedPushforward (Spec.map h.appTop)).mapIso eM ≪≫
        affinePushforwardTildeDerivedObjIso h.appTop M)
  refine (hasTorAmplitude_restrictFunctor_iso_iff W.isoSpec.symm _ a b).1 ?_
  have hpb := isPullback_isoSpec h hle
  rw [happ] at hpb
  exact FlatOpcycles.hasTorAmplitude_of_iso (X := (Spec Γ(W, ⊤)).toRingedSpace) h₃
    (schemeDerivedPushforwardRestrictOpenIso h W.isoSpec.inv (Spec.map h.appTop)
      Z.isoSpec.inv hpb B)

/-- **The Tor-dimension half of [Stacks, Tag 08EV] over an affine base.** Let `g : Y ⟶ W` be a
morphism of schemes with `W` affine and `Y` quasi-compact and quasi-separated, and let `B` be an
object of `D(𝒪_Y)` with quasi-coherent cohomology sheaves and finite Tor dimension over `W`. Then
`Rg_*B` has finite Tor dimension on `W`. -/
@[sga "5 III 6.3" "special case", sga "6 III 3.7.1" "special case"]
theorem hasFiniteTorDimension_schemeDerivedPushforward_of_hasTorAmplitudeOver
    {Y W : Scheme.{u}} [IsAffine W] [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ W)
    (B : DerivedCategory Y.Modules)
    (hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor Y.Modules i).obj B).IsQuasicoherent)
    (hB : ∃ a b : ℤ, HasTorAmplitudeOver g B a b) :
    HasFiniteTorDimension W.toRingedSpace ((schemeDerivedPushforward g).obj B) :=
  hasFiniteTorDimension_schemeDerivedPushforward_of_affine_induction g
    (fun {Z} jZ B =>
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor Z.Modules i).obj B).IsQuasicoherent) ∧
        ∃ a b : ℤ, HasTorAmplitudeOver (jZ ≫ g) B a b)
    (fun jZ _ O B hB => ⟨isQuasicoherent_homology_restrictFunctor_mapDerivedCategory O.ι hB.1,
      by
        obtain ⟨a, b, hab⟩ := hB.2
        exact ⟨a, b, by
          simpa only [Category.assoc] using hasTorAmplitudeOver_restrictFunctor _ O.ι B a b hab⟩⟩)
    (fun jZ _ B hB => by
      obtain ⟨a, b, hab⟩ := hB.2
      exact ⟨a, b, hasTorAmplitude_schemeDerivedPushforward_of_isAffine_of_hasTorAmplitudeOver
        (jZ ≫ g) B hB.1 a b hab⟩)
    B ⟨hqc, by simpa only [Category.id_comp] using hB⟩

/-! ### Replacing the source by an open containing the cohomological support -/

/-- **The support of a restriction to an open subscheme is the preimage of the support.** For an
open immersion `j`, the support of the restriction of `M` along `j` is the preimage under `j` of
the support of `M`. -/
theorem supp_restrictFunctor {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) :
    SheafOfModules.supp ((Scheme.Modules.restrictFunctor j).obj M) =
      j.base ⁻¹' SheafOfModules.supp M := by
  ext y
  exact ((SheafOfModules.mem_supp_iff_nontrivial_stalk _ y).trans (Equiv.nontrivial_congr
    ((Scheme.Modules.restrictStalkNatIso j y).app M).addCommGroupIsoToAddEquiv.toEquiv)).trans
    (SheafOfModules.mem_supp_iff_nontrivial_stalk M (j.base y)).symm

/-- **A module restricts to zero on an open missing its support.** If no point of the image of the
open immersion `j` lies in the support of `M`, then the restriction of `M` along `j` is zero. -/
theorem isZero_restrictFunctor_of_forall_notMem_supp {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (M : X.Modules) (h : ∀ y : Y, j.base y ∉ SheafOfModules.supp M) :
    IsZero ((Scheme.Modules.restrictFunctor j).obj M) := by
  refine Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty _ ?_
  rw [supp_restrictFunctor]
  exact Set.eq_empty_of_forall_notMem h

/-- **The supports of the cohomology sheaves of a restriction.** The cohomology sheaves of the
restriction of `E` along the open immersion `j` have for supports the preimages of those of `E`.
-/
theorem supp_homology_restrictFunctor_mapDerivedCategory {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (E : DerivedCategory X.Modules) (i : ℤ) :
    SheafOfModules.supp ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj E)) =
      j.base ⁻¹' SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules i).obj E) :=
  (SheafOfModules.supp_eq_of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (Scheme.Modules.restrictFunctor j) i).app E)).trans (supp_restrictFunctor j _)

/-- **An object restricts to zero on an open missing the supports of its cohomology sheaves.**
If no point of the image of the open immersion `j` lies in the support of any cohomology sheaf of
`E`, then the restriction of `E` along `j` is zero. -/
theorem isZero_restrictFunctor_mapDerivedCategory_of_forall_notMem_supp {Y X : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j] (E : DerivedCategory X.Modules)
    (h : ∀ (i : ℤ) (y : Y),
      j.base y ∉ SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules i).obj E)) :
    IsZero ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj E) :=
  Stacks.SmallDerivedCategory.isZero_of_isZero_homologyFunctor_obj _ fun i =>
    (isZero_restrictFunctor_of_forall_notMem_supp j _ (h i)).of_iso
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
        (Scheme.Modules.restrictFunctor j) i).app E)

/-- **The derived direct image only sees an open neighbourhood of the cohomological support.** Let
`f : X ⟶ S` be a morphism of schemes, `T ⊆ X` a closed subset containing the support of every
cohomology sheaf of `E`, and `U` an open of `X` containing `T`. Then
`Rf_*E ≅ R(f|_U)_*(E|_U)`. -/
def schemeDerivedPushforwardIsoOfSuppSubset {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (T : Set X) (hT : IsClosed T) (hTU : T ⊆ U) (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules i).obj E) ⊆ T) :
    (schemeDerivedPushforward f).obj E ≅
      (schemeDerivedPushforward (U.ι ≫ f)).obj
        ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E) := by
  let V : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  have hUV : U ⊔ V = ⊤ := eq_top_iff.2 fun x _ => (em (x ∈ T)).imp (fun hx => hTU hx) id
  have hzero : ∀ O : X.Opens, O ≤ V →
      IsZero ((canonicalRightDerived
        (restrictedPushforwardAlong (hom f) (hom O.ι))).obj E) := fun O hO =>
    haveI : (schemeDerivedPushforward (O.ι ≫ f)).IsRightAdjoint :=
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
        (hom (O.ι ≫ f))).isRightAdjoint
    (((schemeDerivedPushforward (O.ι ≫ f)).map_isZero
      (isZero_restrictFunctor_mapDerivedCategory_of_forall_notMem_supp O.ι E
        fun i y hy => hO y.2 (hE i hy)))).of_iso
      ((restrictedDerivedPushforwardRestrictFunctorIso f O.ι).app E)
  let tri := canonicalPushforwardTriangle (hom f) (hom U.ι) (hom V.ι) (hom (U ⊓ V).ι)
    (range_hom_opensι_union U V hUV) (range_hom_opensι_inter U V) E
  have hT' := canonicalPushforwardTriangle_distinguished (hom f) (hom U.ι) (hom V.ι)
    (hom (U ⊓ V).ι) (range_hom_opensι_union U V hUV) (range_hom_opensι_inter U V) E
  have hobj₁ := canonicalPushforwardTriangle_obj₁ (hom f) (hom U.ι) (hom V.ι)
    (hom (U ⊓ V).ι) (range_hom_opensι_union U V hUV) (range_hom_opensι_inter U V) E
  have hobj₂ := canonicalPushforwardTriangle_obj₂ (hom f) (hom U.ι) (hom V.ι)
    (hom (U ⊓ V).ι) (range_hom_opensι_union U V hUV) (range_hom_opensι_inter U V) E
  have hobj₃ := canonicalPushforwardTriangle_obj₃ (hom f) (hom U.ι) (hom V.ι)
    (hom (U ⊓ V).ι) (range_hom_opensι_union U V hUV) (range_hom_opensι_inter U V) E
  have h₃ : IsZero tri.obj₃ := by
    change IsZero (canonicalPushforwardTriangle _ _ _ _ _ _ E).obj₃
    rw [hobj₃]
    exact hzero _ inf_le_right
  have hiso : IsIso tri.mor₁ := (Triangle.isZero₃_iff_isIso₁ tri hT').1 h₃
  exact eqToIso hobj₁.symm ≪≫ @asIso _ _ _ _ tri.mor₁ hiso ≪≫ eqToIso hobj₂ ≪≫
    (isoBiprodZero (hzero V le_rfl)).symm ≪≫
    (restrictedDerivedPushforwardRestrictFunctorIso f U.ι).app E

/-! ### The Tor-dimension half of Stacks 08EV -/

/-- **A closed subset proper over `S` meets the preimage of an affine open in a compact set.** If
`T` is a closed subset of `X` proper over `S` and `V` is an affine open of `S`, then `T ∩ f⁻¹V` is
compact. -/
theorem isCompact_inter_preimage_of_isProperOver {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (T : Closeds X) (hT : IsProperOver f T) (V : S.affineOpens) :
    IsCompact ((T : Set X) ∩ f.base ⁻¹' (V : S.Opens)) := by
  have hp : IsProper ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ f) := hT
  have hc := QuasiCompact.isCompact_preimage
    (f := (Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ f) _ (V : S.Opens).isOpen
    V.2.isCompact
  have himg := hc.image (Scheme.IdealSheafData.vanishingIdeal T).subschemeι.continuous
  convert himg using 1
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range,
    Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Set.inter_comm]

/-- **A compact subset of a scheme lies in a quasi-compact open.** -/
theorem exists_isCompact_opens_superset {X : Scheme.{u}} {K : Set X} (hK : IsCompact K) :
    ∃ U : X.Opens, IsCompact (U : Set X) ∧ K ⊆ U := by
  classical
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun V : X.affineOpens => ((V : X.Opens) : Set X))
    (fun V => (V : X.Opens).isOpen) (by
      intro x _
      have : x ∈ (⊤ : X.Opens) := trivial
      rw [← iSup_affineOpens_eq_top X] at this
      obtain ⟨V, hV⟩ := Opens.mem_iSup.1 this
      exact Set.mem_iUnion.2 ⟨V, hV⟩)
  refine ⟨⨆ V ∈ t, (V : X.Opens), ?_, ?_⟩
  · simp only [Opens.coe_iSup]
    exact t.isCompact_biUnion fun V _ => V.2.isCompact
  · simpa only [Opens.coe_iSup] using ht

/-- **The Tor-dimension half of [Stacks, Tag 08EV].** Let `S` be a locally Noetherian scheme,
`f : X ⟶ S` locally of finite type and `E` an object of `D(𝒪_X)` with quasi-coherent cohomology
sheaves, all supported on a closed subset `T` proper over `S`, and of finite Tor dimension over
`S`. Then `Rf_*E` is of locally finite Tor dimension on `S`. -/
@[sga "5 III 6.3" "special case"]
theorem locallyHasFiniteTorDimension_derivedPushforward_of_isProperOver
    {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules)
    (hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (T : Closeds X) (hT : IsProperOver f T)
    (hsupp : ∀ i : ℤ,
      SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules i).obj E) ⊆ T)
    (htor : ∃ a b : ℤ, HasTorAmplitudeOver f E a b) :
    LocallyHasFiniteTorDimension S.toRingedSpace ((derivedPushforwardModules f).obj E) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨a, b, hab⟩ := htor
  open Stacks.AlgebraicGeometry.PerfectProperDirectImage in
  refine locallyHasFiniteTorDimension_of_forall_affineOpen_restrictFunctor S _ fun V => ?_
  have : IsAffine (V : S.Opens).toScheme := V.2
  let XV : X.Opens := f ⁻¹ᵁ (V : S.Opens)
  let EV := (Scheme.Modules.restrictFunctor XV.ι).mapDerivedCategory.obj E
  let TV : Set XV.toScheme := XV.ι.base ⁻¹' (T : Set X)
  have hTVc : IsClosed TV := T.isClosed.preimage XV.ι.base.hom.continuous
  have hTVk : IsCompact TV := by
    have hk := XV.ι.isOpenEmbedding.isInducing.isCompact_preimage'
      (isCompact_inter_preimage_of_isProperOver f T hT V) (by
        rw [Scheme.Opens.range_ι]
        exact fun x hx => hx.2)
    convert hk using 1
    ext y
    exact ⟨fun h => ⟨h, (Scheme.Opens.range_ι XV ▸ ⟨y, rfl⟩ : XV.ι.base y ∈ (XV : Set X))⟩,
      fun h => h.1⟩
  obtain ⟨U, hUk, hTU⟩ := exists_isCompact_opens_superset hTVk
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hUk
  have hsuppV : ∀ i : ℤ,
      SheafOfModules.supp ((DerivedCategory.homologyFunctor XV.toScheme.Modules i).obj EV) ⊆
        TV := fun i => by
    rw [supp_homology_restrictFunctor_mapDerivedCategory]
    exact Set.preimage_mono (hsupp i)
  have htorV : HasTorAmplitudeOver (f ∣_ (V : S.Opens)) EV a b :=
    (hasTorAmplitudeOver_comp_iff_of_isOpenImmersion (f ∣_ (V : S.Opens)) (V : S.Opens).ι EV
      a b).1 (by
        rw [morphismRestrict_ι]
        exact hasTorAmplitudeOver_restrictFunctor f XV.ι E a b hab)
  obtain ⟨c, d, hcd⟩ := hasFiniteTorDimension_schemeDerivedPushforward_of_hasTorAmplitudeOver
    (U.ι ≫ f ∣_ (V : S.Opens)) ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj EV)
    (isQuasicoherent_homology_restrictFunctor_mapDerivedCategory U.ι
      (isQuasicoherent_homology_restrictFunctor_mapDerivedCategory XV.ι hqc))
    ⟨a, b, hasTorAmplitudeOver_restrictFunctor _ U.ι EV a b htorV⟩
  exact ⟨c, d, FlatOpcycles.hasTorAmplitude_of_iso
    (X := S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding) hcd
    (schemeDerivedPushforwardRestrictOpensIso f (V : S.Opens) E ≪≫
      schemeDerivedPushforwardIsoOfSuppSubset (f ∣_ (V : S.Opens)) U TV hTVc hTU EV hsuppV)⟩

end AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.ProperSupportCoherent

open _root_.AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- **[Stacks, Tag 08EV].** Let `S` be a Noetherian scheme, `f : X ⟶ S` a morphism locally of
finite type and `E` an object of `D(𝒪_X)` such that

1. `E` is in `D^b_{Coh}(𝒪_X)`: it is bounded, `E ∈ D^{≥ a} ∩ D^{≤ b}`, and its cohomology sheaves
   are coherent;
2. the support of `H^i(E)` is proper over `S` for every `i`;
3. `E` has finite Tor dimension as an object of `D(f⁻¹𝒪_S)`.

Then `Rf_*E` is a perfect object of `D(𝒪_S)`.

`Rf_*` is `AlgebraicGeometry.derivedPushforwardModules`, the total right derived functor of
degreewise pushforward, and clause (3) is Tor dimension over the inverse-image ringed space
`(X, f⁻¹𝒪_S)` for its canonical derived tensor product. As in the source, the proof splits the
conclusion by [Stacks, Tag 08CQ]: pseudo-coherence comes from [Stacks, Tag 08E2] and
[Stacks, Tag 08E8], and locally finite Tor dimension from
`AlgebraicGeometry.locallyHasFiniteTorDimension_derivedPushforward_of_isProperOver`. That second
half follows the source's reduction — one closed subset proper over `S` carrying all the
cohomological support ([Stacks, Tag 0CYR]), and a quasi-compact open neighbourhood of it over each
affine open of `S` — and then replaces the source's appeal to [Stacks, Tag 08EU] and
[Stacks, Tag 08EA] by a Mayer--Vietoris induction from the affine case, where the statement is
commutative algebra. -/
@[stacks 08EV "the source's statement and hypotheses: S Noetherian, f locally of finite type, E \
bounded with coherent cohomology sheaves whose supports are proper over S and of finite Tor \
dimension over f⁻¹𝒪_S for its canonical derived tensor product; Rf_* is the total right derived \
functor of degreewise pushforward. The Tor-dimension half is proved by a Mayer–Vietoris \
induction from the affine case rather than through Tag 08EU and Tag 08EA",
  sga "6 0 3.1" "more general",
  sga "6 0 4.1" "more general",
  sga "6 XIV 2.2" "special case"]
theorem isPerfect_derivedPushforward_of_isProperOver_supp {X S : Scheme.{u}} (f : X ⟶ S)
    [IsNoetherian S] [LocallyOfFiniteType f] (E : DerivedCategory X.Modules)
    (a b : ℤ) (hGE : E.IsGE a) (hLE : E.IsLE b)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent)
    (hsupp : ∀ j : ℤ, IsProperOver f
      ⟨SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules j).obj E),
        @SheafOfModules.isClosed_supp _ _ _ (hcoh j).isFiniteType⟩)
    (htor : Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension
      (RingedSpace.inverseImage S.toRingedSpace f.base)
      ((Scheme.Hom.derivedScalarRestriction f).obj E)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj E) := by
  have hpc := isPseudoCoherent_derivedPushforward_of_isProperOver_supp f E hcoh hsupp
    _root_.AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase
    a b hGE hLE
  obtain ⟨T, hT, hTsupp⟩ := exists_isProperOver_of_eventually_empty f
    (fun j => SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules j).obj E)) a b
    (fun j hj => SheafOfModules.supp_eq_empty_of_isZero (by
      rcases not_and_or.1 hj with h | h
      · exact E.isZero_of_isGE a j (lt_of_not_ge h)
      · exact E.isZero_of_isLE b j (lt_of_not_ge h)))
    (fun j => ⟨_, hsupp j, subset_rfl⟩)
  have hqc : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent :=
    fun j => have := hcoh j; isQuasicoherent_of_isCoherent _
  exact Stacks.Cohomology.TorAmplitude.isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension
    (X := S.toRingedSpace) ((derivedPushforwardModules f).obj E)
    ((Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'
      (X := S.toRingedSpace) ((derivedPushforwardModules f).obj E)).2 hpc)
    (locallyHasFiniteTorDimension_derivedPushforward_of_isProperOver f E hqc T hT hTsupp
      ((hasFiniteTorDimension_derivedScalarRestriction_iff f E).1 htor))

end Stacks.AlgebraicGeometry.ProperSupportCoherent

end
