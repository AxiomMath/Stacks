module

public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.MorphismToRelativeProj
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.PulledUniversal
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.SymSectionHom
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.BaseChangeTwist
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.SectionTransport

/-!
# The charts of `r_{L, ψ} : X ⟶ 𝐏(f_* L)` over a member of an open covering of the base

Let `f : X ⟶ S` be quasi-compact and quasi-separated, `L` an invertible `𝒪_X`-module and `V ⊆ S`
an open over which `L|_{f⁻¹V}` is relatively very ample for `f ∣_ V`: there are a quasi-coherent
`𝒪_V`-module `E`, an immersion `i : f⁻¹V ⟶ 𝐏(E)` over `V` and `L|_{f⁻¹V} ≅ i^* 𝒪_{𝐏(E)}(1)`.
This file shows that around every point of `f⁻¹V` the morphism `r_{L, ψ} : X ⟶ 𝐏(f_* L)` of
clause (4) of [Stacks, Tag 01VR] has an immersion as its chart at a degree-one section, and that
the section does not vanish at the point.

This is the step of the proof of (2) ⟹ (4) of Tag 01VR which the source leaves to the reader.
Over an affine open `W' ⊆ V` with image `W ⊆ S`, the immersion `i` restricted to `f⁻¹W` lands in
the chart `Proj Γ(W', Sym E)` of `𝐏(E)`, giving an immersion `h : f⁻¹W ⟶ Proj Γ(W', Sym E)`. The
pulled-back universal family `ψ_h` of [Stacks, Tag 01N9] has `h` as its classified morphism, and
its degree-one values, read in `L` through `L|_{f⁻¹V} ≅ i^* 𝒪(1)`, are sections of `L` over
`f⁻¹W`, i.e. sections of `f_* L` over `W`. This defines a semilinear map
`u : Γ(W', E) ⟶ Γ(W, f_* L)`, hence a graded ring map `φ : Γ(W', Sym E) ⟶ Γ(W, Sym f_* L)`, and the
datum of [Stacks, Tag 01NK] that `ψ` induces over `W`, pulled back along `φ`, is strictly
equivalent to `ψ_h`, the two agreeing in degree one by construction. So its chart at `s` is `h`
restricted, an immersion; and that chart is the chart of `ψ` at `φ(s)` followed by `Spec` of a ring
map, whence the chart of `ψ` at `φ(s)` is an immersion.

## Main results

* `Stacks.Tag01VMVeryAmple.exists_isImmersion_chart_of_member`: the chart statement.

## References

* [Stacks Project, Tag 01VR](https://stacks.math.columbia.edu/tag/01VR)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Graded
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn)
open Stacks.TensorPowers (natTensorPow)
open Stacks.Tag01VMRelativeVeryAmple (symAlgebra)

universe u

namespace Stacks.Tag01VMVeryAmple

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-- Rewriting the morphism inside `appLE` along an equality of morphisms. -/
theorem appLE_eq_of_eq {X Z : Scheme.{u}} {k k' : Z ⟶ X} (hk : k = k') (U : X.Opens)
    (V : Z.Opens) (e : V ≤ k ⁻¹ᵁ U) : k.appLE U V e = k'.appLE U V (hk ▸ e) := by
  subst hk
  rfl

section Values

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] (L : X.Modules)
  [Stacks.Ample.IsInvertibleModule X L] (W : S.Opens)

/-- The round trip of an isomorphism of modules, in the other direction. -/
theorem inv_app_hom_app' {Z : Scheme.{u}} {A B : Z.Modules} (e : A ≅ B) (U : Z.Opens)
    (x : Γ(A, U)) : e.inv.app U (e.hom.app U x) = x :=
  Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app e.symm U x

/-- `restrictPowSection` is injective. -/
theorem restrictPowSection_injective {Y : Scheme.{u}} (M : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y M] (U : Y.Opens) (n : ℕ) :
    Function.Injective
      (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection M U n) := by
  intro x y hxy
  rw [Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection_eq,
    Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection_eq] at hxy
  have h := congrArg (Scheme.Modules.Hom.app
    (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictNatTensorPowIso M U n).inv ⊤)
    hxy
  have h1 := (inv_app_hom_app' _ ⊤ _).symm.trans (h.trans (inv_app_hom_app' _ ⊤ _))
  have h2 := congrArg (Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection U _) h1
  rwa [Stacks.NonvanishingLocusRestrict.sectionOfRestrictGlobalSection_restrictSection,
    Stacks.NonvanishingLocusRestrict.sectionOfRestrictGlobalSection_restrictSection] at h2

/-- A section of `L` over `f⁻¹(W)` read as a section of `f_* L` over `W`. -/
abbrev ofSec (b : Γ(L, f ⁻¹ᵁ W)) : Γ((Scheme.Modules.pushforward f).obj L, W) := b

/-- The value of a section of `L` over `f⁻¹(W)` on the open subscheme `f⁻¹(W)`, in the first
tensor power. -/
def secVal (b : Γ(L, f ⁻¹ᵁ W)) :
    Γ(natTensorPow ((Scheme.Modules.pullback (f ⁻¹ᵁ W).ι).obj L) 1, ⊤) :=
  Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection L (f ⁻¹ᵁ W) 1
    ((Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).inv.app (f ⁻¹ᵁ W) b)

/-- The component of the degree-one element of a section `b` of `f_* L` is the generator image of
`b`. -/
private theorem componentEquiv_genSection (b : Γ(L, f ⁻¹ᵁ W)) :
    (symAlgebra ((Scheme.Modules.pushforward f).obj L)).componentEquiv W 1
        ⟨genSection _ W (ofSec f L W b), genSection_mem _ W (ofSec f L W b)⟩ =
      Scheme.Modules.Hom.app (Scheme.Modules.symmetricAlgebraGen S
        ((Scheme.Modules.pushforward f).obj L)) W (ofSec f L W b) := by
  rw [SheafGradedAlgebra.componentEquiv_apply]
  exact DirectSum.of_eq_same _ _

/-- **The degree-one value of the graded map of clause (4) at the degree-one element of a section
`b` of `L` over `f⁻¹(W)` is `b` read on the open subscheme.** -/
theorem affineDatum_toFun_genSection (b : Γ(L, f ⁻¹ᵁ W)) :
    ((directImageSymPowerMap f L).affineDatum W).toFun 1
        ⟨genSection _ W (ofSec f L W b), genSection_mem _ W (ofSec f L W b)⟩ =
      secVal f L W b := by
  rw [GradedPowerMap.affineDatum_toFun_apply, componentEquiv_genSection,
    directImageSymPowerMap_value_gen]
  rfl

omit [QuasiCompact f] [QuasiSeparated f] in
/-- The map `secVal` is injective. -/
theorem secVal_injective : Function.Injective (secVal f L W) := by
  intro b b' h
  have h2 := restrictPowSection_injective L (f ⁻¹ᵁ W) 1 h
  have h3 := congrArg ((Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).hom.app
    (f ⁻¹ᵁ W)) h2
  rwa [Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app,
    Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app] at h3

omit [QuasiCompact f] [QuasiSeparated f] in
/-- The map `secVal` is surjective. -/
theorem secVal_surjective : Function.Surjective (secVal f L W) := by
  intro t
  obtain ⟨x, hx⟩ := Stacks.QuasiProjectiveCompactification.restrictPowSection_surjective L
    (f ⁻¹ᵁ W) 1 t
  refine ⟨(Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).hom.app (f ⁻¹ᵁ W) x, ?_⟩
  rwa [secVal, inv_app_hom_app']

/-- `secVal` as an equivalence. -/
def secValEquiv : Γ(L, f ⁻¹ᵁ W) ≃
    Γ(natTensorPow ((Scheme.Modules.pullback (f ⁻¹ᵁ W).ι).obj L) 1, ⊤) :=
  Equiv.ofBijective _ ⟨secVal_injective f L W, secVal_surjective f L W⟩

omit [QuasiCompact f] [QuasiSeparated f] in
/-- The map `secVal` is additive. -/
theorem secVal_add (b b' : Γ(L, f ⁻¹ᵁ W)) :
    secVal f L W (b + b') = secVal f L W b + secVal f L W b' := by
  rw [secVal, secVal, secVal, map_add]
  exact Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection_add L _ 1 _ _

omit [QuasiCompact f] [QuasiSeparated f] in
/-- The value `secVal` of `r • b` is the restriction of `r` to the open subscheme times the value
of `b`. -/
theorem secVal_smul (r : Γ(X, f ⁻¹ᵁ W)) (b : Γ(L, f ⁻¹ᵁ W)) :
    secVal f L W (r • b) = (f ⁻¹ᵁ W).toScheme.presheaf.map
          (homOfLE (Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self (f ⁻¹ᵁ W))).op
          ((f ⁻¹ᵁ W).ι.app (f ⁻¹ᵁ W) r) • secVal f L W b := by
  rw [secVal, secVal, Scheme.Modules.Hom.app_smul, restrictPowSection_smul]

omit [QuasiCompact f] [QuasiSeparated f] in
/-- The scalar of `secVal_smul` for a function pulled back from `W`. -/
theorem secVal_smul_app (r : Γ(S, W)) (b : Γ(L, f ⁻¹ᵁ W)) :
    secVal f L W (f.app W r • b) = ((f ⁻¹ᵁ W).ι ≫ f).appLE W ⊤
      (preimage_ι_comp_eq_top f W).ge r • secVal f L W b := by
  rw [secVal_smul]
  congr 1

end Values

section Geometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) {E : V.toScheme.Modules} [E.IsQuasicoherent]
  (i : (f ⁻¹ᵁ V).toScheme ⟶ (relativeProj (symAlgebra E)).scheme)
  (hover : i ≫ (relativeProj (symAlgebra E)).toBase = f ∣_ V)
  {W' : V.toScheme.Opens} (hW' : IsAffineOpen W')

/-- The image `W ⊆ S` of an open `W'` of `V` lies in `V`. -/
theorem image_ι_le (W' : V.toScheme.Opens) : V.ι ''ᵁ W' ≤ V := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

/-- The inclusion `f⁻¹(W) ⊆ f⁻¹(V)`, for `W ⊆ S` the image of an open `W'` of `V`. -/
abbrev memberIncl (W' : V.toScheme.Opens) :
    (f ⁻¹ᵁ (V.ι ''ᵁ W')).toScheme ⟶ (f ⁻¹ᵁ V).toScheme :=
  X.homOfLE (f.preimage_mono (image_ι_le V W'))

include hover in
/-- The immersion `i`, restricted to `f⁻¹(W)`, lands in the chart of `𝐏(E)` over `W'`. -/
theorem range_memberIncl_comp_le :
    Set.range (memberIncl f V W' ≫ i).base ⊆
      Set.range ((relativeProj (symAlgebra E)).chart W' hW').base := by
  rintro _ ⟨y, rfl⟩
  have hrange : Set.range ((relativeProj (symAlgebra E)).chart W' hW').base =
      ((relativeProj (symAlgebra E)).toBase ⁻¹ᵁ W' : Set _) := by
    rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.image_top_eq_opensRange,
      Stacks.AlgebraicGeometry.RelativeProjTwistGlue.chart_image_top]
  rw [hrange]
  change ((relativeProj (symAlgebra E)).toBase) (i (memberIncl f V W' y)) ∈ W'
  rw [← Scheme.Hom.comp_apply, hover]
  obtain ⟨w, hw, hwy⟩ := y.2
  have : V.ι ((f ∣_ V) (memberIncl f V W' y)) = V.ι w := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply,
      ← Scheme.Hom.comp_apply (memberIncl f V W'), Scheme.homOfLE_ι]
    exact hwy.symm
  rwa [V.ι.isOpenEmbedding.injective this]

/-- **The immersion restricted to `f⁻¹(W)`, read into the chart `Proj Γ(W', Sym E)`.** -/
def memberChartMap :
    (f ⁻¹ᵁ (V.ι ''ᵁ W')).toScheme ⟶ AlgebraicGeometry.Proj ((symAlgebra E).grading W') :=
  haveI := Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart
    (relativeProj (symAlgebra E)) W' hW'
  IsOpenImmersion.lift ((relativeProj (symAlgebra E)).chart W' hW') (memberIncl f V W' ≫ i)
    (range_memberIncl_comp_le f V i hover hW')

/-- The map `memberChartMap` followed by the chart of `𝐏(E)` over `W'` is `i` restricted to
`f⁻¹(W)`. -/
theorem memberChartMap_comp_chart :
    memberChartMap f V i hover hW' ≫ (relativeProj (symAlgebra E)).chart W' hW' =
      memberIncl f V W' ≫ i :=
  haveI := Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart
    (relativeProj (symAlgebra E)) W' hW'
  IsOpenImmersion.lift_fac _ _ _

/-- The restricted immersion is an immersion. -/
theorem isImmersion_memberChartMap [IsImmersion i] :
    IsImmersion (memberChartMap f V i hover hW') := by
  have : IsImmersion (memberChartMap f V i hover hW' ≫
      (relativeProj (symAlgebra E)).chart W' hW') := by
    rw [memberChartMap_comp_chart]
    infer_instance
  exact IsImmersion.of_comp _ ((relativeProj (symAlgebra E)).chart W' hW')

/-- The restricted immersion followed by the structure morphism of the chart to `W'`. -/
abbrev memberBaseMap : (f ⁻¹ᵁ (V.ι ''ᵁ W')).toScheme ⟶ W'.toScheme :=
  memberChartMap f V i hover hW' ≫ projInclusionToOpen (symAlgebra E) W' hW'

/-- The structure morphism to `W'`, followed by `W' ⊆ V`, is the restriction of `f`. -/
theorem memberBaseMap_ι :
    memberBaseMap f V i hover hW' ≫ W'.ι = memberIncl f V W' ≫ f ∣_ V := by
  rw [Category.assoc, ← ((relativeProj (symAlgebra E)).chart_isPullback W' hW').w,
    ← Category.assoc, memberChartMap_comp_chart, Category.assoc, hover]

/-- The pullback of the degree-zero part of the chart's graded ring along the restricted
immersion is the pullback along the structure morphism to `W'`. -/
private theorem memberScalar_hom_eq_baseMap :
    (symAlgebra E).toGradedAlgebra.strZero ⟨W', hW'⟩ ≫
      (Scheme.ΓSpecIso (CommRingCat.of ((symAlgebra E).grading W' 0))).inv ≫
        (memberChartMap f V i hover hW' ≫
          AlgebraicGeometry.Proj.toSpecZero ((symAlgebra E).grading W')).appTop =
    W'.topIso.inv ≫ (memberBaseMap f V i hover hW').appTop := by
  let φ0 : Γ(V.toScheme, W') ⟶ CommRingCat.of ((symAlgebra E).grading W' 0) :=
    (symAlgebra E).toGradedAlgebra.strZero ⟨W', hW'⟩
  have e : (memberChartMap f V i hover hW' ≫
      AlgebraicGeometry.Proj.toSpecZero ((symAlgebra E).grading W')) ≫ Spec.map φ0 =
      memberBaseMap f V i hover hW' ≫ hW'.isoSpec.hom := by
    change _ = (memberChartMap f V i hover hW' ≫ (AlgebraicGeometry.Proj.toSpecZero _ ≫
      Spec.map φ0 ≫ hW'.isoSpec.inv)) ≫ hW'.isoSpec.hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change φ0 ≫ _ = _
  clear_value φ0
  calc φ0 ≫ (Scheme.ΓSpecIso (CommRingCat.of ((symAlgebra E).grading W' 0))).inv ≫
        (memberChartMap f V i hover hW' ≫
          AlgebraicGeometry.Proj.toSpecZero ((symAlgebra E).grading W')).appTop
      = (φ0 ≫ (Scheme.ΓSpecIso (CommRingCat.of ((symAlgebra E).grading W' 0))).inv) ≫
        (memberChartMap f V i hover hW' ≫
          AlgebraicGeometry.Proj.toSpecZero ((symAlgebra E).grading W')).appTop :=
        (Category.assoc _ _ _).symm
    _ = ((Scheme.ΓSpecIso Γ(V.toScheme, W')).inv ≫ (Spec.map φ0).appTop) ≫
        (memberChartMap f V i hover hW' ≫
          AlgebraicGeometry.Proj.toSpecZero ((symAlgebra E).grading W')).appTop :=
        congrArg (· ≫ _) (Scheme.ΓSpecIso_inv_naturality φ0)
    _ = (Scheme.ΓSpecIso Γ(V.toScheme, W')).inv ≫
        (memberBaseMap f V i hover hW' ≫ hW'.isoSpec.hom).appTop := by
        rw [Category.assoc, ← Scheme.Hom.comp_appTop, e]
    _ = W'.topIso.inv ≫ (memberBaseMap f V i hover hW').appTop := by
        rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop, ← Category.assoc,
          ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- **On the functions of `W'`, the degree-zero part of the chart's graded ring pulls back along
the restricted immersion to the restriction of `f`.** A function `r` on `W'` is a degree-zero
element of `Γ(W', Sym E)`; read as a function on `Proj Γ(W', Sym E)` through
`Proj ⟶ Spec Γ(W', Sym E)_0`, its pullback to `f⁻¹(W)` is the pullback along `f` of the function
on `W ⊆ S` that `r` corresponds to. -/
theorem memberScalar_hom :
    (symAlgebra E).toGradedAlgebra.strZero ⟨W', hW'⟩ ≫
        (Scheme.ΓSpecIso (CommRingCat.of ((symAlgebra E).grading W' 0))).inv ≫
          (memberChartMap f V i hover hW' ≫
            AlgebraicGeometry.Proj.toSpecZero ((symAlgebra E).grading W')).appTop =
      (V.ι.appIso W').inv ≫ ((f ⁻¹ᵁ (V.ι ''ᵁ W')).ι ≫ f).appLE (V.ι ''ᵁ W') ⊤
        (by rw [Scheme.Hom.comp_preimage]; exact le_of_eq (by simp)) := by
  rw [memberScalar_hom_eq_baseMap]
  have e2 : (f ⁻¹ᵁ (V.ι ''ᵁ W')).ι ≫ f = memberBaseMap f V i hover hW' ≫ W'.ι ≫ V.ι := by
    rw [← Category.assoc, memberBaseMap_ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
      Scheme.homOfLE_ι]
  rw [appLE_eq_of_eq e2, ← Scheme.Hom.appLE_comp_appLE (memberBaseMap f V i hover hW')
      (W'.ι ≫ V.ι) (V.ι ''ᵁ W') ⊤ ⊤ (by simp) le_top,
    ← Scheme.Hom.appLE_comp_appLE W'.ι V.ι (V.ι ''ᵁ W') W' ⊤ (by simp) (by simp),
    ← Category.assoc, ← Category.assoc, Scheme.Hom.appIso_inv_appLE]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.id_comp]
  congr 1
  · simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    congr 1
  · simp only [Scheme.Hom.comp_app, Opens.map_top, Scheme.Hom.appLE, Scheme.Hom.comp_base,
      Opens.map_comp_obj, homOfLE_refl, op_id, Scheme.Opens.toScheme_presheaf_map, unop_id,
      CategoryTheory.Functor.map_id]
    rfl

end Geometry

section Module

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) {E : V.toScheme.Modules} [E.IsQuasicoherent]
  (i : (f ⁻¹ᵁ V).toScheme ⟶ (relativeProj (symAlgebra E)).scheme)
  (hover : i ≫ (relativeProj (symAlgebra E)).toBase = f ∣_ V)
  {W' : V.toScheme.Opens} (hW' : IsAffineOpen W') (L : X.Modules)
  (α : (modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L ≅
    (Scheme.Modules.pullback i).obj (twistOne E))

include hW' in
/-- `Γ(W', Sym E)` is generated in degree one. -/
theorem memberGen :
    Algebra.adjoin ((symAlgebra E).grading W' 0)
      ((symAlgebra E).grading W' 1 : Set ((symAlgebra E).sectionRing W')) = ⊤ :=
  Stacks.Tag01VMRelativeVeryAmple.adjoin_symAlgebra_eq_top E W' hW'

/-- **The module of the pulled-back universal family is the restriction of `L`**, read in its
first tensor power. -/
def memberIso :
    (Scheme.Modules.pullback (toDegreeOpenOne (symAlgebra E) W' (memberGen V hW')
        (memberChartMap f V i hover hW'))).obj
      (Stacks.AlgebraicGeometry.ProjDegreeOpenRepresents.universalTwist
        ((symAlgebra E).grading W') 1) ≅
      natTensorPow ((Scheme.Modules.pullback (f ⁻¹ᵁ (V.ι ''ᵁ W')).ι).obj L) 1 :=
  haveI := Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart
    (relativeProj (symAlgebra E)) W' hW'
  (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (by
      rw [← Category.assoc, Category.comp_id]
      exact toProj_toDegreeOpenOne (symAlgebra E) W' (memberGen V hW')
        (memberChartMap f V i hover hW'))).app _ ≪≫
    (Scheme.Modules.pullback (memberChartMap f V i hover hW')).mapIso
      (twistOneChartIso E W' hW').symm ≪≫
    (Scheme.Modules.pullback (memberChartMap f V i hover hW')).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback
        ((relativeProj (symAlgebra E)).chart W' hW')).app (twistOne E)) ≪≫
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (memberChartMap_comp_chart f V i hover hW')).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback (memberIncl f V W')).mapIso α.symm ≪≫
    (Scheme.Modules.pullbackComp _ _).app L ≪≫
    (Scheme.Modules.pullbackCongr (Scheme.homOfLE_ι _ _)).app L ≪≫
    (Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow _).symm

variable [QuasiCompact f] [QuasiSeparated f] [Stacks.Ample.IsInvertibleModule X L]

/-- The pulled-back universal family on `f⁻¹(W)`. -/
abbrev memberψ :=
  pulledUniversal (symAlgebra E) W' (memberGen V hW') (memberChartMap f V i hover hW')

/-- The degree-one element of `Γ(W', Sym E)` attached to a section of `E`, at the index of the
weight-one Veronese family. -/
abbrev memberGen1 (e : Γ(E, W')) : (symAlgebra E).grading W' (1 * 1) :=
  ⟨genSection E W' e, genSection_mem E W' e⟩

/-- **The section of `L` over `f⁻¹(W)` attached to a section `e` of `E` over `W'`**: the degree-one
value of `ψ_h` at `e`, read in `L` through `memberIso`. -/
def memberSec (e : Γ(E, W')) : Γ(L, f ⁻¹ᵁ (V.ι ''ᵁ W')) :=
  (secValEquiv f L (V.ι ''ᵁ W')).symm
    ((Stacks.AlgebraicGeometry.ProjVeroneseRestrict.powVeroneseIso _ 1 1).hom.app ⊤
      ((Stacks.AmplePullbackPart1.natTensorPowCongr (memberIso f V i hover hW' L α) 1).hom.app ⊤
        ((memberψ f V i hover hW').toFun 1 (memberGen1 V e))))

omit [QuasiCompact f] [QuasiSeparated f] in
/-- The value of `memberSec e` on the open subscheme is the degree-one value of `ψ_h` at `e`, read
through `memberIso`. -/
theorem secVal_memberSec (e : Γ(E, W')) :
    secVal f L (V.ι ''ᵁ W') (memberSec f V i hover hW' L α e) =
      (Stacks.AlgebraicGeometry.ProjVeroneseRestrict.powVeroneseIso _ 1 1).hom.app ⊤
        ((Stacks.AmplePullbackPart1.natTensorPowCongr (memberIso f V i hover hW' L α) 1).hom.app ⊤
          ((memberψ f V i hover hW').toFun 1 (memberGen1 V e))) :=
  (secValEquiv f L (V.ι ''ᵁ W')).apply_symm_apply _

/-- The degree-one element of a scalar multiple. -/
theorem genSection_smul (r : Γ(V.toScheme, W')) (e : Γ(E, W')) :
    genSection E W' (r • e) = genSection E W' e * (symAlgebra E).strHom W' r := by
  rw [mul_comm]
  exact (congrArg (DirectSum.of _ 1)
    (((Scheme.Modules.symmetricAlgebraGen V.toScheme E).val.app (op W')).hom.map_smul r e)).trans
      (SheafGradedAlgebra.strHom_mul_of _ _ r _).symm

omit [QuasiCompact f] [QuasiSeparated f] in
/-- The degree-one values of `ψ_h` are linear for the functions on `W'`, which act on the sections
over `f⁻¹(W)` through the pullback of functions along `f`. -/
theorem memberSec_smul (r : Γ(V.toScheme, W')) (e : Γ(E, W')) :
    memberSec f V i hover hW' L α (r • e) =
      f.app (V.ι ''ᵁ W') ((V.ι.appIso W').inv r) • memberSec f V i hover hW' L α e := by
  apply secVal_injective f L (V.ι ''ᵁ W')
  rw [secVal_smul_app, secVal_memberSec, secVal_memberSec]
  let z : (symAlgebra E).grading W' 0 :=
    ⟨(symAlgebra E).strHom W' r, (symAlgebra E).strHom_mem W' r⟩
  have hmem : genSection E W' (r • e) ∈ (symAlgebra E).grading W' ((1 + 0) * 1) :=
    genSection_mem E W' (r • e)
  have hg := toFun_mul_zeroVeronese (symAlgebra E) W' (memberψ f V i hover hW')
    (memberGen1 V e) z ⟨_, hmem⟩ (genSection_smul V r e)
  have hF : Stacks.AlgebraicGeometry.ProjTripleStructureMorphism.divUnit
      ((memberψ f V i hover hW').toFun 0
      (Stacks.AlgebraicGeometry.ProjTripleStructureMorphism.zeroVeronese _ 1 z)) =
      ((f ⁻¹ᵁ (V.ι ''ᵁ W')).ι ≫ f).appLE (V.ι ''ᵁ W') ⊤
        (preimage_ι_comp_eq_top f (V.ι ''ᵁ W')).ge ((V.ι.appIso W').inv r) := by
    rw [divUnit_pulledUniversal_zero]
    have key := ConcreteCategory.congr_hom (memberScalar_hom f V i hover hW') r
    have hz : (symAlgebra E).toGradedAlgebra.strZero ⟨W', hW'⟩ r = z :=
      Subtype.ext (Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.coe_strZero_apply
        (symAlgebra E).toGradedAlgebra ⟨W', hW'⟩ r)
    simp only [CategoryTheory.comp_apply] at key
    rwa [hz] at key
  have e1 : (memberψ f V i hover hW').toFun 1 (memberGen1 V (r • e)) =
      (memberψ f V i hover hW').toFun (1 + 0) ⟨_, hmem⟩ := rfl
  rw [e1, hg, hF, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]

/-- **The semilinear map `u : Γ(W', E) ⟶ Γ(W, f_* L)`** of the degree-one values of `ψ_h`. -/
def memberU : Γ(E, W') →ₛₗ[(V.ι.appIso W').inv.hom]
    Γ((Scheme.Modules.pushforward f).obj L, V.ι ''ᵁ W') where
  toFun e := ofSec f L _ (memberSec f V i hover hW' L α e)
  map_add' e e' := by
    apply secVal_injective f L (V.ι ''ᵁ W')
    change secVal f L _ (memberSec f V i hover hW' L α (e + e')) =
      secVal f L _ (memberSec f V i hover hW' L α e + memberSec f V i hover hW' L α e')
    rw [secVal_add, secVal_memberSec, secVal_memberSec, secVal_memberSec]
    have : memberGen1 V (e + e') = memberGen1 V e + memberGen1 V e' :=
      Subtype.ext (by
        change DirectSum.of _ 1 _ = DirectSum.of _ 1 _ + DirectSum.of _ 1 _
        exact (congrArg (DirectSum.of _ 1) (map_add _ e e')).trans (map_add _ _ _))
    rw [this, map_add, map_add, map_add]
  map_smul' r e := memberSec_smul f V i hover hW' L α r e

include hW' in
/-- The image of `W'` in `S` is affine. -/
theorem isAffineOpen_image : IsAffineOpen (V.ι ''ᵁ W') :=
  AlgebraicGeometry.IsAffineOpen.image_of_isOpenImmersion hW' V.ι

/-- **The graded ring map `φ : Γ(W', Sym E) ⟶ Γ(W, Sym f_* L)`** induced by `u`. -/
abbrev memberφ :=
  symSectionGradedHom E ((Scheme.Modules.pushforward f).obj L) hW' (isAffineOpen_image V hW')
    (V.ι.appIso W').inv.hom (memberU f V i hover hW' L α)

/-- The datum of [Stacks, Tag 01NK] that `ψ` induces over `W`, pulled back along `φ`. -/
abbrev memberχ :=
  Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.comap (memberφ f V i hover hW' L α)
    ((directImageSymPowerMap f L).affineDatum (V.ι ''ᵁ W'))

/-- The graded map `φ` sends the degree-one element of `e` to that of the section `memberSec e`. -/
private theorem memberφ_genSection (e : Γ(E, W')) :
    (memberφ f V i hover hW' L α) (genSection E W' e) =
      genSection _ (V.ι ''ᵁ W') (ofSec f L _ (memberSec f V i hover hW' L α e)) :=
  symSectionGradedHom_gen _ _ _ _ _ _ e

/-- The degree-one value of the datum of clause (4) at `φ` of the element of `e` is the value of
`memberSec e`. -/
private theorem affineDatum_toFun_memberφ (e : Γ(E, W')) :
    ((directImageSymPowerMap f L).affineDatum (V.ι ''ᵁ W')).toFun (1 * 1)
        ⟨(memberφ f V i hover hW' L α) (genSection E W' e),
          map_mem (memberφ f V i hover hW' L α) (memberGen1 V e).2⟩ =
      secVal f L _ (memberSec f V i hover hW' L α e) := by
  rw [← affineDatum_toFun_genSection]
  exact congrArg _ (Subtype.ext (memberφ_genSection f V i hover hW' L α e))

/-- **The pulled-back datum is strictly equivalent to `ψ_h`.** In degree one this is the
definition of `u`; the other degrees follow by generation in degree one. -/
theorem sectionsEquiv_memberχ :
    Stacks.AlgebraicGeometry.ProjTripleClassifying.SectionsEquiv ((symAlgebra E).grading W')
      (memberψ f V i hover hW')
      (Stacks.AlgebraicGeometry.ProjChartGradedVeronese.veroneseAt ((symAlgebra E).grading W')
        (memberχ f V i hover hW' L α) 1) := by
  refine sectionsEquiv_of_degreeOne (symAlgebra E) W' (memberGen V hW') _ _
    (memberIso f V i hover hW' L α)
    (iSup_nonvanishingOpen_pulledUniversal (symAlgebra E) W' (memberGen V hW') _) fun x => ?_
  obtain ⟨e, he⟩ := exists_eq_genSection_of_mem_grading_one E hW' (x.2 : _ ∈ _)
  obtain rfl : x = memberGen1 V e := Subtype.ext he
  rw [Stacks.AlgebraicGeometry.ProjChartGradedVeronese.veroneseAt_toFun,
    Stacks.AlgebraicGeometry.ProjChartGradedVeronese.veroneseComp_apply _ _ 1 1 _
      (memberGen1 V e) rfl,
    Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.comap_toFun]
  rw [affineDatum_toFun_memberφ, secVal_memberSec]
  exact (inv_app_hom_app' (Stacks.AlgebraicGeometry.ProjVeroneseRestrict.powVeroneseIso
    ((Scheme.Modules.pullback (f ⁻¹ᵁ (V.ι ''ᵁ W')).ι).obj L) 1 1) ⊤
    ((Stacks.AmplePullbackPart1.natTensorPowCongr (memberIso f V i hover hW' L α) 1).hom.app ⊤
      ((memberψ f V i hover hW').toFun 1 (memberGen1 V e)))).symm

/-- **The chart of `ψ` at `φ(s)` is an immersion**, for `s` a degree-one element of `Γ(W', Sym E)`:
the chart of the pulled-back datum at `s` is `h` restricted, an immersion, and it factors through
the chart of `ψ` at `φ(s)`. -/
theorem isImmersion_toSpecAway_memberφ [IsImmersion i] {s : (symAlgebra E).sectionRing W'}
    (hs : s ∈ (symAlgebra E).grading W' 1) :
    IsImmersion ((((directImageSymPowerMap f L).affineDatum (V.ι ''ᵁ W')).homogeneousRatios
      (map_mem (memberφ f V i hover hW' L α) hs) le_rfl).toSpecAway one_pos) := by
  have hc := chartToProj_eq_of_sectionsEquiv (symAlgebra E) W' (memberGen V hW')
    (memberChartMap f V i hover hW') (memberχ f V i hover hW' L α)
    (sectionsEquiv_memberχ f V i hover hW' L α) hs
  have := isImmersion_memberChartMap f V i hover hW'
  have h1 : IsImmersion (((memberχ f V i hover hW' L α).homogeneousRatios hs le_rfl).toSpecAway
      one_pos ≫ AlgebraicGeometry.Proj.awayι ((symAlgebra E).grading W') s hs one_pos) := by
    have : IsImmersion ((memberχ f V i hover hW' L α).chartToProj hs le_rfl one_pos) := by
      rw [hc]
      infer_instance
    exact this
  have h2 : IsImmersion (((memberχ f V i hover hW' L α).homogeneousRatios hs le_rfl).toSpecAway
      one_pos) := IsImmersion.of_comp _ (AlgebraicGeometry.Proj.awayι _ s hs one_pos)
  rw [toSpecAway_comap] at h2
  exact @IsImmersion.of_comp _ _ _ _ _ h2

end Module

/-- Being an immersion, for the chart of a datum of [Stacks, Tag 01NK] at a section, depends only
on the section. -/
theorem isImmersion_toSpecAway_of_eq {R σ : Type u} [CommRing R] [SetLike σ R]
    [AddSubgroupClass σ R] {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {M : T.Modules}
    [Stacks.Ample.IsInvertibleModule T M]
    (D : Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections 𝒜 M)
    {s t : R} (h : s = t) (hs : s ∈ 𝒜 1) (ht : t ∈ 𝒜 1)
    (himm : IsImmersion ((D.homogeneousRatios hs le_rfl).toSpecAway one_pos)) :
    IsImmersion ((D.homogeneousRatios ht le_rfl).toSpecAway one_pos) := by
  subst h
  exact himm

/-! ### Charts of `r_{L, ψ}` near a point over a member of the covering -/

section Core

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] (L : X.Modules)
  [Stacks.Ample.IsInvertibleModule X L]

/-- **Around every point of `f⁻¹(V)`, for `V` an open of `S` over which `L` is relatively very
ample, the morphism `r_{L, ψ} : X ⟶ 𝐏(f_* L)` of clause (4) of [Stacks, Tag 01VR] has an immersion
as its chart at the degree-one element of a section `b` of `f_* L`, and `b` does not vanish at
the point.** -/
theorem exists_isImmersion_chart_of_member (V : S.Opens)
    (hV : IsRelativelyVeryAmple (f ∣_ V) ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L))
    (x : X) (hx : f x ∈ V) :
    ∃ (W : S.Opens) (_ : IsAffineOpen W) (b : Γ(L, f ⁻¹ᵁ W)),
      x ∈ nonvanishingLocusOn L (f ⁻¹ᵁ W) b ∧
      IsImmersion ((((directImageSymPowerMap f L).affineDatum W).homogeneousRatios
        (genSection_mem _ W (ofSec f L W b)) le_rfl).toSpecAway one_pos) := by
  obtain ⟨E, hE, i, him, hover, ⟨α⟩⟩ := hV
  let xV : (f ⁻¹ᵁ V).toScheme := ⟨x, hx⟩
  obtain ⟨_, ⟨W', hW', rfl⟩, hxW', -⟩ :=
    V.toScheme.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ((f ∣_ V) xV))
      isOpen_univ
  have hxW : x ∈ f ⁻¹ᵁ (V.ι ''ᵁ W') := by
    refine ⟨(f ∣_ V) xV, hxW', ?_⟩
    change V.ι ((f ∣_ V) xV) = f x
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι]
    rfl
  let y : (f ⁻¹ᵁ (V.ι ''ᵁ W')).toScheme := ⟨x, hxW⟩
  have hy : y ∈ ⨆ g : (symAlgebra E).grading W' 1, Stacks.NonvanishingOpen.nonvanishingOpen _ _
      (Stacks.AlgebraicGeometry.MorphismToProjUniversal.psiSection _
        (memberψ f V i hover hW') g) := by
    rw [iSup_nonvanishingOpen_pulledUniversal]
    trivial
  obtain ⟨g, hg⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  have hgχ : y ∈ Stacks.NonvanishingOpen.nonvanishingOpen _
      (natTensorPow ((Scheme.Modules.pullback (f ⁻¹ᵁ (V.ι ''ᵁ W')).ι).obj L) 1)
      ((memberχ f V i hover hW' L α).toFun 1 g) := by
    rwa [← nonvanishingOpen_psiSection_eq_of_sectionsEquiv (symAlgebra E) W'
      (sectionsEquiv_memberχ f V i hover hW' L α) g,
      Stacks.AlgebraicGeometry.MorphismToProjUniversal.nonvanishingOpen_psiSection,
      Stacks.AlgebraicGeometry.ProjChartGradedVeronese.nonvanishingOpen_veroneseAt_pow_one] at hg
  obtain ⟨e, he⟩ := exists_eq_genSection_of_mem_grading_one E hW' g.2
  obtain rfl : g = memberGen1 V e := Subtype.ext he
  let b := memberSec f V i hover hW' L α e
  refine ⟨V.ι ''ᵁ W', isAffineOpen_image V hW', b, ?_, ?_⟩
  · have h1 : (memberχ f V i hover hW' L α).toFun 1 (memberGen1 V e) = secVal f L _ b := by
      rw [Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.comap_toFun]
      exact affineDatum_toFun_memberφ f V i hover hW' L α e
    rw [h1, ← affineDatum_toFun_genSection] at hgχ
    have h2 : y ∈ ((directImageSymPowerMap f L).affineDatum (V.ι ''ᵁ W')).nonvanishingOpenAt 1
        ⟨genSection _ _ (ofSec f L _ b), genSection_mem _ _ (ofSec f L _ b)⟩ := hgχ
    rw [GradedPowerMap.nonvanishingOpenAt_affineDatum, componentEquiv_genSection] at h2
    exact (mem_nonvanishingOpenAt_directImageSymPowerMap_iff f L _ (ofSec f L _ b) x).mp h2
  · exact isImmersion_toSpecAway_of_eq _ (memberφ_genSection f V i hover hW' L α e) _ _
      (isImmersion_toSpecAway_memberφ f V i hover hW' L α (memberGen1 V e).2)

end Core

end Stacks.Tag01VMVeryAmple

end
