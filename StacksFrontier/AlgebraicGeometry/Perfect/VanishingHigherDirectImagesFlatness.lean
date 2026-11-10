module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwistedPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.VanishingHigherDirectImagesPerfection
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.LocalTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedPushforwardOpenBase
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedTensorTorAmplitudeOver
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeOpenImmersion
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.TorDimensionDirectImage
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tor amplitude of a derived direct image with the lower bound kept

For `g : Y ⟶ W` with `W` affine and `Y` quasi-compact and quasi-separated, and an object `B` of
`D(𝒪_Y)` with quasi-coherent cohomology and Tor amplitude in `[a, b]` over `W`, the derived
direct image `Rg_*B` has Tor amplitude in `[a, b']` on `W` for some `b'`. The *lower* bound is
carried across `Rg_*` unchanged; only the upper bound is weakened.

`AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_of_hasTorAmplitudeOver` already
proves the same thing with both bounds existentially quantified. That is not enough for
`Stacks.Cohomology.TorAmplitude.FlatOpcycles.isFlat_of_hasTorAmplitude_single`, which turns Tor
amplitude of `N[0]` into flatness of `N` and asks for the lower bound to be exactly the degree `N`
sits in.

## Main results

* `exists_hasTorAmplitude_schemeDerivedPushforward_of_affine_induction`: the Mayer--Vietoris
  induction over a finite affine cover of the source, with the lower bound fixed.
* `exists_hasTorAmplitude_schemeDerivedPushforward_of_hasTorAmplitudeOver`: the Tor-dimension
  half of [Stacks, Tag 08EV] over an affine base, with the lower bound kept.
* `isFlat_of_nonempty_iso`: the flatness clause of [More on Algebra, Tag 0658] at the object the
  proof of [Stacks, Tag 0D4E] applies it to.
* `flatFinitePresentationOfSingleDirectImage`: the input the first conclusion of
  [Stacks, Tag 0D4E] used to be granted, proved.
* `isFiniteLocallyFree_pushforward_of_isZero_higherDirectImage`: **the first conclusion of
  [Stacks, Tag 0D4E]**, `f_* ℱ` is finite locally free, with nothing granted.

## Implementation notes

Both are the corresponding statements of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/PerfectMorphism/MayerVietorisTorDimension.lean` and
`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/TorDimensionDirectImage.lean` with the
interval's lower end pinned instead of quantified, and the proofs are those proofs with the
bookkeeping redone. The two cannot be derived from one another: the existential form loses the
lower bound, and the fixed form does not apply to a family whose lower bounds differ.

What makes the lower bound survive is the arithmetic of [Stacks, Tag 08CJ] (1),
`Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_obj₁`: from `L` in `[α + 1, β + 1]`
and `M` in `[α, β]` it concludes `K` in `[α + 1, β + 1]`. Read at `α = a - 1` this takes `L` in
`[a, β + 1]` and `M` in `[a - 1, β]` to `K` in `[a, β + 1]`, and the hypothesis on `M` is the
inductive bound `[a, b₃]` widened downwards, which costs nothing. Only the upper bound pays, one
step per application, which is why it stays existential.

## References

* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
* [Stacks Project, Tag 08CJ](https://stacks.math.columbia.edu/tag/08CJ)
* [Stacks Project, Tag 08CK](https://stacks.math.columbia.edu/tag/08CK)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open AlgebraicGeometry
open Stacks.SchemeCohomology (hom)
open Stacks.Cohomology.TorAmplitude
open Stacks.Cohomology.RelativeMayerVietoris
open Stacks.Cohomology.DerivedBaseChange (compact_open_immersion_induction_on)
open Stacks.AlgebraicGeometry.PerfectProperDirectImage
  (hasTorAmplitude_restrictModules_iff_restrictFunctor)
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.VanishingHigherDirectImages

attribute [local instance 10000] HasDerivedCategory.standard

-- `HasDerivedCategory` at the spelling of [Stacks, Tag 06YU]: the type is `OXMod X` by `rfl`,
-- but `structureSheafOfRings` is not reducible, so an instance proved at one spelling does not
-- fire at the other. Seated here, as in
-- `StacksFrontier/Topology/Sheaves/Cohomology/TorAmplitude/LocalTorAmplitude.lean`, not restated.
attribute [local instance] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

-- The two declarations after this section are the tag's registration and the `Prop` it used to
-- grant; they are elaborated with the ambient `HasDerivedCategory` instances rather than with
-- `HasDerivedCategory.standard` raised above them, so that their statements are the ones
-- `VanishingHigherDirectImages.lean` and its consumers already carry.
section Raised

/-- **Tor amplitude of a derived direct image with the lower bound fixed, by induction over a
finite affine cover of the source.** Let `g : Y ⟶ W` be a morphism of schemes with `Y`
quasi-compact and quasi-separated, let `a` be an integer, and let `H` be a property of objects of
`D(𝒪_Z)` for the open immersions `jZ : Z ⟶ Y`, inherited by the restriction to an open subscheme.
If `R(jZ ≫ g)_*B` has Tor amplitude in `[a, b]` on `W` for some `b` for every affine `Z` and every
`B` with `H jZ B`, then `Rg_*A` has Tor amplitude in `[a, b']` on `W` for some `b'` for every `A`
with `H (𝟙 Y) A`.

This is `AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_of_affine_induction`
with the lower end of the interval pinned; the module documentation says why the pinning
survives the induction. -/
public theorem exists_hasTorAmplitude_schemeDerivedPushforward_of_affine_induction
    {Y W : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ W) (a : ℤ)
    (H : ∀ {Z : Scheme.{u}}, (Z ⟶ Y) → DerivedCategory Z.Modules → Prop)
    (hres : ∀ {Z : Scheme.{u}} (jZ : Z ⟶ Y) [IsOpenImmersion jZ] (O : Z.Opens)
      (B : DerivedCategory Z.Modules), H jZ B →
        H (O.ι ≫ jZ) ((Scheme.Modules.restrictFunctor O.ι).mapDerivedCategory.obj B))
    (hbase : ∀ {Z : Scheme.{u}} [IsAffine Z] (jZ : Z ⟶ Y) [IsOpenImmersion jZ]
      (B : DerivedCategory Z.Modules), H jZ B →
        ∃ b : ℤ, HasTorAmplitude W.toRingedSpace
          ((schemeDerivedPushforward (jZ ≫ g)).obj B) a b)
    (A : DerivedCategory Y.Modules) (hA : H (𝟙 Y) A) :
    ∃ b : ℤ, HasTorAmplitude W.toRingedSpace ((schemeDerivedPushforward g).obj A) a b := by
  set P : ∀ Z : Scheme.{u}, (Z ⟶ Y) → Prop := fun Z jZ =>
    IsOpenImmersion jZ → ∀ B : DerivedCategory Z.Modules, H jZ B →
      ∃ b : ℤ, HasTorAmplitude W.toRingedSpace
        ((schemeDerivedPushforward (jZ ≫ g)).obj B) a b
  have hP : P Y (𝟙 Y) := by
    refine compact_open_immersion_induction_on P ?_ ?_
    · intro Z _ _ _ jZ _ _ B hB
      exact hbase jZ B hB
    · intro Z _ _ jZ _ U V hUV hPU hPV hPUV _ B hB
      have key : ∀ O : Z.Opens, P O.toScheme (O.ι ≫ jZ) →
          ∃ c : ℤ, HasTorAmplitude W.toRingedSpace
            ((canonicalRightDerived
              (restrictedPushforwardAlong (hom (jZ ≫ g)) (hom O.ι))).obj B) a c := by
        intro O hO
        obtain ⟨c, hc⟩ := hO inferInstance _ (hres jZ O B hB)
        rw [Category.assoc] at hc
        exact ⟨c, FlatOpcycles.hasTorAmplitude_of_iso (X := W.toRingedSpace) hc
          ((restrictedDerivedPushforwardRestrictFunctorIso (jZ ≫ g) O.ι).app B)⟩
      obtain ⟨cU, hcU⟩ := key U hPU
      obtain ⟨cV, hcV⟩ := key V hPV
      obtain ⟨c₃, hc₃⟩ := key (U ⊓ V) hPUV
      have hT := canonicalPushforwardTriangle_distinguished (hom (jZ ≫ g)) (hom U.ι) (hom V.ι)
        (hom (U ⊓ V).ι) (range_hom_opensι_union U V hUV) (range_hom_opensι_inter U V) B
      have hobj₁ := canonicalPushforwardTriangle_obj₁ (hom (jZ ≫ g)) (hom U.ι) (hom V.ι)
        (hom (U ⊓ V).ι) (range_hom_opensι_union U V hUV) (range_hom_opensι_inter U V) B
      have hobj₂ := canonicalPushforwardTriangle_obj₂ (hom (jZ ≫ g)) (hom U.ι) (hom V.ι)
        (hom (U ⊓ V).ι) (range_hom_opensι_union U V hUV) (range_hom_opensι_inter U V) B
      have hobj₃ := canonicalPushforwardTriangle_obj₃ (hom (jZ ≫ g)) (hom U.ι) (hom V.ι)
        (hom (U ⊓ V).ι) (range_hom_opensι_union U V hUV) (range_hom_opensι_inter U V) B
      obtain ⟨c, hc1, hc2, hc3⟩ : ∃ c : ℤ, cU ≤ c ∧ cV ≤ c ∧ c₃ + 1 ≤ c :=
        ⟨max (max cU cV) (c₃ + 1), le_trans (le_max_left _ _) (le_max_left _ _),
          le_trans (le_max_right _ _) (le_max_left _ _), le_max_right _ _⟩
      refine ⟨c, ?_⟩
      have hbi := hasTorAmplitude_biprod.{u, u + 1} (X := W.toRingedSpace) a c _ _
        (FlatOpcycles.hasTorAmplitude_mono.{u, u + 1} hcU le_rfl hc1)
        (FlatOpcycles.hasTorAmplitude_mono.{u, u + 1} hcV le_rfl hc2)
      have hmain := FlatOpcycles.hasTorAmplitude_obj₁.{u, u + 1} (X := W.toRingedSpace) _ hT
        (a - 1) (c - 1)
        (by
          rw [hobj₂]
          exact FlatOpcycles.hasTorAmplitude_mono.{u, u + 1} hbi (by omega) (by omega))
        (by
          rw [hobj₃]
          exact FlatOpcycles.hasTorAmplitude_mono.{u, u + 1} hc₃ (by omega) (by omega))
      rw [hobj₁] at hmain
      exact FlatOpcycles.hasTorAmplitude_mono.{u, u + 1} hmain (by omega) (by omega)
  have hfin := hP inferInstance A hA
  rwa [Category.id_comp] at hfin

/-- **The Tor-dimension half of [Stacks, Tag 08EV] over an affine base, with the lower bound
kept.** Let `g : Y ⟶ W` be a morphism of schemes with `W` affine and `Y` quasi-compact and
quasi-separated, and let `B` be an object of `D(𝒪_Y)` with quasi-coherent cohomology sheaves and
Tor amplitude in `[a, b]` over `W`. Then `Rg_*B` has Tor amplitude in `[a, b']` on `W` for some
`b'`.

This is `AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_of_hasTorAmplitudeOver`
with the lower end of the interval pinned: the induction is run at the property "quasi-coherent
cohomology and Tor amplitude in `[a, b]` over the base", both halves of which restrict to an
open, and the affine case is
`AlgebraicGeometry.hasTorAmplitude_schemeDerivedPushforward_of_isAffine_of_hasTorAmplitudeOver`,
which carries the interval across `Rg_*` unchanged. -/
@[sga "6 III 3.7.1" "partial, special case"]
public theorem exists_hasTorAmplitude_schemeDerivedPushforward_of_hasTorAmplitudeOver
    {Y W : Scheme.{u}} [IsAffine W] [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ W)
    (B : DerivedCategory Y.Modules)
    (hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor Y.Modules i).obj B).IsQuasicoherent)
    (a b : ℤ) (hB : HasTorAmplitudeOver g B a b) :
    ∃ b' : ℤ, HasTorAmplitude W.toRingedSpace ((schemeDerivedPushforward g).obj B) a b' :=
  exists_hasTorAmplitude_schemeDerivedPushforward_of_affine_induction g a
    (fun {Z} jZ B' =>
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor Z.Modules i).obj B').IsQuasicoherent) ∧
        HasTorAmplitudeOver (jZ ≫ g) B' a b)
    (fun jZ _ O B' hB' =>
      ⟨isQuasicoherent_homology_restrictFunctor_mapDerivedCategory O.ι hB'.1, by
        simpa only [Category.assoc] using
          hasTorAmplitudeOver_restrictFunctor (jZ ≫ g) O.ι B' a b hB'.2⟩)
    (fun jZ _ B' hB' =>
      ⟨b, hasTorAmplitude_schemeDerivedPushforward_of_isAffine_of_hasTorAmplitudeOver
        (jZ ≫ g) B' hB'.1 a b hB'.2⟩)
    B ⟨hqc, by simpa only [Category.id_comp] using hB⟩

/-- **The affine-open Tor bound for the derived direct image of a module flat over the base.** Let
`f : X ⟶ S` be of finite presentation, let `ℱ` be a quasi-coherent `𝒪_X`-module flat over `S`, and
let `V ⊆ S` be an affine open. Then `(Rf_* ℱ)|_V` has Tor amplitude in `[0, b]` on `V` for some
`b`.

`f^{-1}V` is quasi-compact, `f` being quasi-compact and `V` affine, and quasi-separated, `f ∣_ V`
being quasi-separated over the affine `V`; `ℱ` in degree `0` has Tor amplitude in `[0, 0]` over
`S` because `ℱ` is flat over `S`
(`AlgebraicGeometry.hasTorAmplitudeOver_of_isFlatOver`), and that restricts to `f^{-1}V`; the
derived direct image over `V` is the restriction of `Rf_* ℱ`
([Stacks, Tag 08FE], `AlgebraicGeometry.schemeDerivedPushforwardRestrictOpensIso`); and
`exists_hasTorAmplitude_schemeDerivedPushforward_of_hasTorAmplitudeOver` carries the lower bound
`0` across the direct image. -/
@[sga "6 III 3.7.1" "partial, special case"]
public theorem exists_hasTorAmplitude_restrict_derivedPushforward_single
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f) (F : X.Modules)
    (hqc : F.IsQuasicoherent) (hflat : IsFlatOver f.toLRSHom.toShHom F) (V : S.affineOpens) :
    ∃ b : ℤ, HasTorAmplitude (S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding)
      ((Scheme.Modules.restrictFunctor (V : S.Opens).ι).mapDerivedCategory.obj
        ((schemeDerivedPushforward f).obj
          (DerivedCategory.Q.obj (ProperFlatBaseChange.singleDegreeComplex F)))) 0 b := by
  have : IsAffine (V : S.Opens).toScheme := V.2
  have : QuasiCompact f := hf.quasiCompact
  have : QuasiSeparated f := hf.quasiSeparated
  have sq := (isPullback_morphismRestrict f (V : S.Opens)).flip
  have : QuasiCompact (f ∣_ (V : S.Opens)) := MorphismProperty.of_isPullback sq hf.quasiCompact
  have : QuasiSeparated (f ∣_ (V : S.Opens)) :=
    MorphismProperty.of_isPullback sq hf.quasiSeparated
  have : CompactSpace (f ⁻¹ᵁ (V : S.Opens)).toScheme :=
    isCompact_iff_compactSpace.mp
      (QuasiCompact.isCompact_preimage (f := f) _ (V : S.Opens).isOpen V.2.isCompact)
  have : QuasiSeparatedSpace (f ⁻¹ᵁ (V : S.Opens)).toScheme :=
    quasiSeparatedSpace_of_quasiSeparated (f ∣_ (V : S.Opens))
  have hEqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj
      (DerivedCategory.Q.obj (ProperFlatBaseChange.singleDegreeComplex F))).IsQuasicoherent :=
    fun i => Stacks.Blowup.isQuasicoherent_homology_Q_single X F hqc i
  have hEtor : HasTorAmplitudeOver f
      (DerivedCategory.Q.obj (ProperFlatBaseChange.singleDegreeComplex F)) 0 0 :=
    hasTorAmplitudeOver_of_isFlatOver f _ 0 0
      (ProperFlatBaseChange.isFlatOver_singleDegreeComplex f F hflat)
  have hEtorV : HasTorAmplitudeOver (f ∣_ (V : S.Opens))
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ (V : S.Opens)).ι).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (ProperFlatBaseChange.singleDegreeComplex F))) 0 0 :=
    (hasTorAmplitudeOver_comp_iff_of_isOpenImmersion (f ∣_ (V : S.Opens)) (V : S.Opens).ι _
      0 0).1 (by
        rw [morphismRestrict_ι]
        exact hasTorAmplitudeOver_restrictFunctor f (f ⁻¹ᵁ (V : S.Opens)).ι _ 0 0 hEtor)
  obtain ⟨b, hb⟩ := exists_hasTorAmplitude_schemeDerivedPushforward_of_hasTorAmplitudeOver
    (f ∣_ (V : S.Opens)) _
    (isQuasicoherent_homology_restrictFunctor_mapDerivedCategory (f ⁻¹ᵁ (V : S.Opens)).ι hEqc)
    0 0 hEtorV
  exact ⟨b, FlatOpcycles.hasTorAmplitude_of_iso
    (X := S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding) hb
    (schemeDerivedPushforwardRestrictOpensIso f (V : S.Opens) _)⟩

/-- **Tor amplitude bounded below at `0` and an object in degrees `≤ 0` give Tor amplitude in
`[0, 0]`.** The derived tensor product is right `t`-exact
(`Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProductFunctor`), so above degree `0` the
vanishing is free. -/
public theorem hasTorAmplitude_zero_zero_of_isLE {Z : RingedSpace.{u, u}}
    (E : Stacks.DerivedTensor.RingedSite.DerivedModules Z.sheaf) [E.IsLE 0] (b : ℤ)
    (h : HasTorAmplitude Z E 0 b) : HasTorAmplitude Z E 0 0 := by
  intro G i hi
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hi
  rcases hi with hi | hi
  · exact h G i (by rw [Set.mem_Icc, not_and_or, not_le, not_le]; exact Or.inl hi)
  · -- The crossing between `StrictlyPerfect.OXMod Z` and the Tag 06YU spelling
    -- `Stacks.DerivedTensor.RingedSite.Modules Z.sheaf` of the same category: instance search
    -- does not cross it, so each instance is bound by a `have` carrying the explicit type.
    have hG : DerivedCategory.IsLE
        (show Stacks.DerivedTensor.RingedSite.DerivedModules Z.sheaf from
          (DerivedCategory.singleFunctor (StrictlyPerfect.OXMod.{u, u} Z) 0).obj G) 0 :=
      (inferInstance : DerivedCategory.IsLE
        ((DerivedCategory.singleFunctor (StrictlyPerfect.OXMod.{u, u} Z) 0).obj G) 0)
    have hle : DerivedCategory.IsLE
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).obj E).obj
          ((DerivedCategory.singleFunctor (StrictlyPerfect.OXMod.{u, u} Z) 0).obj G)) 0 := by
      simpa only [zero_add] using
        Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProductFunctor Z.sheaf E _ 0 0
    exact (DerivedCategory.isLE_iff _ 0).1 hle i hi

/-- **The restriction of a module in degree `0` to an open subscheme lies in degrees `≤ 0`.**
Restriction is exact, so it commutes with the cohomology functors of the derived category
(`StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso`), and the cohomology of
`N[0]` vanishes above degree `0`. -/
public theorem isLE_restrictFunctor_singleFunctor {S : Scheme.{u}} (V : S.Opens)
    (N : S.Modules) :
    ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor S.Modules 0).obj N)).IsLE 0 := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  refine IsZero.of_iso ?_
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (Scheme.Modules.restrictFunctor V.ι) i).app
      ((DerivedCategory.singleFunctor S.Modules 0).obj N))
  exact ((Scheme.Modules.restrictFunctor V.ι).map_isZero
    ((DerivedCategory.isLE_iff ((DerivedCategory.singleFunctor S.Modules 0).obj N) 0).1
      inferInstance i hi))

/-- **The derived direct image of `ℱ` identified with `N` in degree `0`.** The hypothesis of
`FlatFinitePresentationOfSingleDirectImage` is an isomorphism in `D⁺(𝒪_S)`; this reads it in
`D(𝒪_S)`, with `ℱ` in degree `0` spelled as the localization of
`AlgebraicGeometry.ProperFlatBaseChange.singleDegreeComplex`. -/
public theorem nonempty_iso_schemeDerivedPushforward_single {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) (N : S.Modules)
    (hN : Nonempty ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F) ≅
      (DerivedCategory.Plus.singleFunctor S.Modules 0).obj N)) :
    Nonempty ((schemeDerivedPushforward f).obj
        (DerivedCategory.Q.obj (ProperFlatBaseChange.singleDegreeComplex F)) ≅
      (DerivedCategory.singleFunctor S.Modules 0).obj N) := by
  obtain ⟨eN⟩ := hN
  obtain ⟨eb⟩ := Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
    (Scheme.Modules.pushforward f) (derivedPushforwardModules f)
    (derivedPushforwardModulesUnit f)
    (fun I hI => RingedSpace.isIso_derivedPushforwardUnit_app_of_isKInjective _ I hI)
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F) 0 (by
      change ((DerivedCategory.singleFunctor X.Modules 0).obj F).IsGE 0
      infer_instance)
  exact ⟨(schemeDerivedPushforward f).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app F).symm ≪≫ eb ≪≫
    DerivedCategory.Plus.ι.mapIso eN ≪≫
      (DerivedCategory.Plus.singleFunctorιIso S.Modules 0).app N⟩

/-- **`N[0]` has Tor amplitude in `[0, 0]`.** Let `f : X ⟶ S` be of finite presentation and let
`ℱ` be an `𝒪_X`-module of finite presentation, flat over `S`. If `Rf_* ℱ` is isomorphic in
`D⁺(𝒪_S)` to a module `N` placed in degree `0`, then `N[0]` has Tor amplitude in `[0, 0]` on `S`.

Tor amplitude in a fixed interval is local on an open covering of `S`
(`Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_iSup_eq_top`), and the affine opens cover
`S`. On an affine open `V` the lower bound `0` is
`exists_hasTorAmplitude_restrict_derivedPushforward_single` and the upper bound is
`hasTorAmplitude_zero_zero_of_isLE` at `isLE_restrictFunctor_singleFunctor`. -/
@[sga "6 III 3.7.1" "Case N = 0, special case"]
public theorem hasTorAmplitude_singleFunctor_of_nonempty_iso {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : FinitePresentation f) (F : X.Modules) [F.IsFinitePresentation]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (N : S.Modules)
    (hN : Nonempty ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F) ≅
      (DerivedCategory.Plus.singleFunctor S.Modules 0).obj N)) :
    HasTorAmplitude S.toRingedSpace
      ((DerivedCategory.singleFunctor S.Modules 0).obj N) 0 0 := by
  have : QuasiCompact f := hf.quasiCompact
  have : QuasiSeparated f := hf.quasiSeparated
  obtain ⟨e⟩ := nonempty_iso_schemeDerivedPushforward_single f F N hN
  refine hasTorAmplitude_of_iSup_eq_top S.toRingedSpace _ 0 0
    (fun V : S.affineOpens => (V : S.Opens)) (iSup_affineOpens_eq_top S) fun V => ?_
  refine (hasTorAmplitude_restrictModules_iff_restrictFunctor S (V : S.Opens) _ 0 0).2 ?_
  obtain ⟨b, hb⟩ := exists_hasTorAmplitude_restrict_derivedPushforward_single f hf F
    (isQuasicoherent_of_isFinitePresentation F) hflat V
  have : DerivedCategory.IsLE
      (show Stacks.DerivedTensor.RingedSite.DerivedModules
          (S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding).sheaf from
        (Scheme.Modules.restrictFunctor (V : S.Opens).ι).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor S.Modules 0).obj N)) 0 :=
    isLE_restrictFunctor_singleFunctor (V : S.Opens) N
  refine hasTorAmplitude_zero_zero_of_isLE _ b ?_
  exact FlatOpcycles.hasTorAmplitude_of_iso
    (X := S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding) hb
    ((Scheme.Modules.restrictFunctor (V : S.Opens).ι).mapDerivedCategory.mapIso e.symm)

/-- **The flatness clause of [More on Algebra, Tag 0658], at the object the proof of
[Stacks, Tag 0D4E] applies it to.** Under the hypotheses of
`isPerfect_singleFunctor_of_nonempty_iso`, the module `N` is flat.

Unconditional. `N[0]` has Tor amplitude in `[0, 0]` by
`hasTorAmplitude_singleFunctor_of_nonempty_iso`, and a module whose Tor amplitude starts at the
degree it sits in is flat, which is
`Stacks.Cohomology.TorAmplitude.FlatOpcycles.isFlat_of_hasTorAmplitude_single`. -/
public theorem isFlat_of_nonempty_iso {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : FinitePresentation f) (F : X.Modules) [F.IsFinitePresentation]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (N : S.Modules)
    (hN : Nonempty ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F) ≅
      (DerivedCategory.Plus.singleFunctor S.Modules 0).obj N)) :
    _root_.AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := S.sheaf) N :=
  FlatOpcycles.isFlat_of_hasTorAmplitude_single.{u, u + 1} (X := S.toRingedSpace) N 0 0
    (hasTorAmplitude_singleFunctor_of_nonempty_iso f hf F hflat N hN)

end Raised

/-- **`FlatFinitePresentationOfSingleDirectImage`, proved.** The input the first conclusion of
[Stacks, Tag 0D4E] used to be granted: for `f : X ⟶ S` of finite presentation and `ℱ` an
`𝒪_X`-module of finite presentation, flat over `S`, with support proper over `S`, a module `N` on
`S` carrying an isomorphism `Rf_* ℱ ≅ N[0]` in `D⁺(𝒪_S)` is flat and of finite presentation.

This is the perfection half of [Stacks, Tag 0A1H] composed with the algebraic half of
[More on Algebra, Tag 0658]. Flatness is `isFlat_of_nonempty_iso` and finite presentation is
`isFinitePresentation_of_nonempty_iso`. -/
public theorem flatFinitePresentationOfSingleDirectImage :
    FlatFinitePresentationOfSingleDirectImage.{u} := by
  intro X S f hf
  let : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  intro F hfp hflat hsupp N hN
  have := hfp
  exact ⟨isFlat_of_nonempty_iso f hf F hflat N hN,
    isFinitePresentation_of_nonempty_iso f hf F hflat hsupp N hN⟩

/-- **[Stacks, Tag 0D4E], the first conclusion, with nothing granted.** Let `f : X ⟶ S` be a
morphism of schemes of finite presentation and let `ℱ` be an `𝒪_X`-module of finite presentation,
flat over `S`, whose support is proper over `S`. If `R ⁱ f_* ℱ = 0` for all `i > 0`, then `f_* ℱ`
is finite locally free.

The proof is the source's. The degeneration `Rf_* ℱ = (f_* ℱ)[0]` is
`nonempty_iso_singleFunctor_pushforward`; `flatFinitePresentationOfSingleDirectImage` then makes
`f_* ℱ` flat and of finite presentation; and flatness together with finite presentation *is*
finite local freeness, which is [Stacks, Tag 05P2] in the form
`AlgebraicGeometry.flat_finitePresentation_locallyFree_fiberRank_tfae` and is the source's
[Stacks, Tag 00NX] citation. -/
@[ega "III 7.9.10" "partial", sga "7 IX 3.1.3" "more general"]
public theorem isFiniteLocallyFree_pushforward_of_isZero_higherDirectImage
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f) (F : X.Modules)
    [F.IsFinitePresentation] (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (hsupp : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
      ∃ Z : Closeds X, IsProperOver f Z ∧ SheafOfModules.supp F ⊆ (Z : Set X))
    (hvanish : ∀ i : ℤ, 0 < i →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F)) :
    _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := S.ringCatSheaf) ((Scheme.Modules.pushforward f).obj F) :=
  ((Scheme.Modules.flat_finitePresentation_locallyFree_fiberRank_tfae
      ((Scheme.Modules.pushforward f).obj F)).out 1 4).mp
    (flatFinitePresentationOfSingleDirectImage f hf F inferInstance hflat hsupp
      ((Scheme.Modules.pushforward f).obj F)
      (nonempty_iso_singleFunctor_pushforward f F hvanish))

end Stacks.AlgebraicGeometry.VanishingHigherDirectImages

end
