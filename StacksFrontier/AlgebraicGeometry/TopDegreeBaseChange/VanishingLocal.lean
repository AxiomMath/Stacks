module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.RestrictTarget
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally

/-!
# Top-degree vanishing after base change, reduced to an affine base

[Stacks, Tag 0EX3] fixes the data of `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation` and
asserts, among its conclusions, that the higher direct images along the base-changed morphism
`f'` still vanish above the degree `d`. The source proves this by reducing to the case of an
affine base: a point of `Y'` is covered by an affine open `V` lying over an affine open `U` of
`Y`, the square restricts to a cartesian square over those affines, and vanishing is a local
condition on `Y'`.

This file carries out that reduction. The affine case itself is taken as an explicit hypothesis,
so that the whole conclusion follows once the affine case is available.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_restrict_cover`: a sheaf of
  modules whose restriction to each member of an open cover vanishes is a zero object.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_sections_of_isAffine`: a
  quasi-coherent module on an affine scheme with vanishing global sections is a zero object.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_sections_of_isZero_cohomology_zero`:
  vanishing of `H⁰(X, M)` is vanishing of the module of global sections.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_cohomology_zero_of_isAffine`:
  the two combined — a quasi-coherent module on an affine scheme with vanishing `H⁰` is zero.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_rightDerivedPlus_pushforward_of_affineCase`:
  the vanishing of higher direct images above `d` after an arbitrary base change, granted the
  same statement for cartesian squares both of whose bases are affine.

## Implementation notes

The cover of `Y'` is built by choosing, for each `y' : Y'`, an affine open `U` of `Y` containing
the image of `y'` and then an affine open `V` of `Y'` containing `y'` and contained in `g⁻¹(U)`.
The restricted square is cartesian by `AlgebraicGeometry.Scheme.Hom.isPullback_resLE`, and the
restricted morphism `f ∣_ U` still satisfies the situation's vanishing hypothesis by
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.vanishes_above_morphismRestrict`.

Vanishing is checked on the cover through
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso`, the scheme-level
form of [Stacks, Tag 01E5], and then globalized by `isZero_of_isZero_restrict_cover`, which is
`AlgebraicGeometry.isZero_of_forall_isZero_stalk` read through the stalk comparison
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isZero_stalk_of_isZero_restrict`.

The degree is an integer throughout and is written as a natural number with
`Int.eq_ofNat_of_zero_le`, which is possible because it is bounded below by `d`.

No `@[stacks 0EX3]` attribute is placed: the tag asserts conclusions (a), (b) and (c) about the
situation, and the affine case of the vanishing conclusion is still carried as a hypothesis here.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

/-- **Vanishing of a sheaf of modules is local on the base.** If the restriction of `M` to each
member of an open cover of `S` is a zero object, then `M` is a zero object: the stalk of the
restriction at a point of a member is the stalk of `M`, so every stalk of `M` vanishes. -/
theorem isZero_of_isZero_restrict_cover {S : Scheme.{u}} {ι : Type*} (V : ι → S.Opens)
    (hV : ⨆ i, V i = ⊤) (M : S.Modules)
    (h : ∀ i, IsZero ((Scheme.Modules.restrictFunctor (V i).ι).obj M)) :
    IsZero M := by
  refine AlgebraicGeometry.isZero_of_forall_isZero_stalk M fun x => ?_
  have hx : x ∈ (⨆ i, V i : S.Opens) := by rw [hV]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact SchemeHigherDirectImage.isZero_stalk_of_isZero_restrict (V i) M x hi (h i)

/-- **A quasi-coherent module on an affine scheme with no global sections is zero.** Transporting
along `AlgebraicGeometry.Scheme.isoSpec` puts the module on a spectrum, where quasi-coherence
makes `AlgebraicGeometry.Scheme.Modules.fromTildeΓ` an isomorphism; the target of that
isomorphism is built from the module of global sections, which is zero. -/
theorem isZero_of_isZero_sections_of_isAffine {T : Scheme.{u}} [IsAffine T] (M : T.Modules)
    [M.IsQuasicoherent]
    (hΓ : IsZero ((SheafOfModules.evaluation T.ringCatSheaf (op (⊤ : T.Opens))).obj M)) :
    IsZero M := by
  let e := T.isoSpec
  let M' := (Scheme.Modules.restrictFunctor e.inv).obj M
  have hΓ'carrier : Subsingleton (M'.val.obj (op (⊤ : (Spec Γ(T, ⊤)).Opens))) := by
    dsimp [M', Scheme.Modules.restrictFunctor, SheafOfModules.pushforward,
      PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
      PresheafOfModules.pushforward₀Obj]
    change Subsingleton (M.val.obj (op (e.inv ''ᵁ (⊤ : (Spec Γ(T, ⊤)).Opens))))
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
    exact ModuleCat.isZero_iff_subsingleton.mp hΓ
  have hΓmodule : IsZero
      ((modulesSpecToSheaf.obj M').presheaf.obj (op (⊤ : (Spec Γ(T, ⊤)).Opens))) :=
    ModuleCat.isZero_iff_subsingleton.mpr hΓ'carrier
  have hM' : IsZero M' := IsZero.of_iso
    (Functor.map_isZero (tilde.functor (CommRingCat.of Γ(T, ⊤))) hΓmodule)
    (asIso M'.fromTildeΓ).symm
  exact IsZero.of_iso (Functor.map_isZero (Scheme.Modules.restrictFunctor e.hom) hM')
    (((Scheme.Modules.restrictFunctorCongr e.hom_inv_id).app M ≪≫
      Scheme.Modules.restrictFunctorId.app M).symm ≪≫
      (Scheme.Modules.restrictFunctorComp e.hom e.inv).app M)

/-- **Vanishing of degree-zero cohomology is vanishing of global sections.** Global sections are
left exact, so the zeroth right derived functor computing `H⁰(X, M)` is the global sections
functor itself, and a zero abelian group of sections is a zero module of sections. -/
theorem isZero_sections_of_isZero_cohomology_zero {X : Scheme.{u}} (M : X.Modules)
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ 0 M)) :
    IsZero ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj M) := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))
  let G := forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) AddCommGrpCat
  have : PreservesFiniteLimits (secF X.ringCatSheaf ⊤) := by
    change PreservesFiniteLimits (E ⋙ G)
    infer_instance
  have hΓ : IsZero ((secF X.ringCatSheaf ⊤).obj M) :=
    IsZero.of_iso (h : IsZero (((secF X.ringCatSheaf ⊤).rightDerived 0).obj M))
      ((secF X.ringCatSheaf ⊤).rightDerivedZeroIsoSelf.app M).symm
  change IsZero (G.obj (E.obj M)) at hΓ
  exact ModuleCat.isZero_iff_subsingleton.mpr (AddCommGrpCat.isZero_iff_subsingleton.mp hΓ)

/-- **A quasi-coherent module on an affine scheme with vanishing degree-zero cohomology is
zero.** This is `isZero_sections_of_isZero_cohomology_zero` followed by
`isZero_of_isZero_sections_of_isAffine`. -/
theorem isZero_of_isZero_cohomology_zero_of_isAffine {T : Scheme.{u}} [IsAffine T]
    (M : T.Modules) [M.IsQuasicoherent] (h : IsZero (Hgroup T.ringCatSheaf ⊤ 0 M)) :
    IsZero M :=
  isZero_of_isZero_sections_of_isAffine M (isZero_sections_of_isZero_cohomology_zero M h)

/-- **The vanishing conclusion of [Stacks, Tag 0EX3], reduced to an affine base.** Granted the
same vanishing statement `haffine` for cartesian squares whose two bases are affine, the higher
direct images along the base-changed morphism `f'` of a top-degree base-change situation vanish
above the degree `d`.

Each point `y'` of `Y'` lies in an affine open `V` of `Y'` contained in the preimage of an affine
open `U` of `Y`, and the situation's square restricts to a cartesian square over `U` and `V`. The
restriction `f ∣_ U` still kills higher direct images of quasi-coherent modules above `d`
(`vanishes_above_morphismRestrict`), so `haffine` applies over `V`; the restriction comparison of
[Stacks, Tag 01E5] identifies the result with the restriction to `V` of the higher direct image
along `f'`, and vanishing on the cover is vanishing. -/
theorem isZero_rightDerivedPlus_pushforward_of_affineCase
    (S : TopDegreeBaseChangeSituation.{u})
    (haffine : ∀ {X₀ Y₀ X₁ Y₁ : Scheme.{u}} (f : X₀ ⟶ Y₀) (g' : X₁ ⟶ X₀) (f' : X₁ ⟶ Y₁)
      (g : Y₁ ⟶ Y₀), IsPullback g' f' f g → [IsAffine Y₀] → [IsAffine Y₁] →
      [QuasiCompact f] → [QuasiSeparated f] →
      (∀ j : ℤ, (S.d : ℤ) < j → ∀ G : X₀.Modules, G.IsQuasicoherent →
        IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus j).obj G)) →
      ∀ i : ℤ, (S.d : ℤ) < i → ∀ F₁ : X₁.Modules, F₁.IsQuasicoherent →
        IsZero (((Scheme.Modules.pushforward f').rightDerivedPlus i).obj F₁))
    (i : ℤ) (hi : (S.d : ℤ) < i) (F' : S.X'.Modules) [F'.IsQuasicoherent] :
    IsZero (((Scheme.Modules.pushforward S.f').rightDerivedPlus i).obj F') := by
  have : CompactSpace S.X := S.isCompact_X
  have : QuasiSeparatedSpace S.X := S.isQuasiSeparated_X
  have : CompactSpace S.Y := S.isCompact_Y
  have : QuasiSeparatedSpace S.Y := S.isQuasiSeparated_Y
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ((Int.natCast_nonneg S.d).trans hi.le)
  have hUV (y' : S.Y') : ∃ U : S.Y.Opens, IsAffineOpen U ∧
      ∃ V : S.Y'.Opens, IsAffineOpen V ∧ y' ∈ V ∧ V ≤ S.g ⁻¹ᵁ U := by
    obtain ⟨U, hU, hgU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (x := S.g.base y') (U := ⊤) (by simp)
    obtain ⟨V, hV, hyV, hVU⟩ :=
      exists_isAffineOpen_mem_and_subset (x := y') (U := S.g ⁻¹ᵁ U) hgU
    exact ⟨U, hU, V, hV, hyV, hVU⟩
  choose U hU V hV hyV hVle using hUV
  refine isZero_of_isZero_restrict_cover V
    (eq_top_iff.mpr fun y _ => Opens.mem_iSup.mpr ⟨y, hyV y⟩) _ fun y' => ?_
  let UX := S.f ⁻¹ᵁ U y'
  let UY := S.f' ⁻¹ᵁ V y'
  have hsub : UY ≤ S.g' ⁻¹ᵁ UX := by
    change S.f' ⁻¹ᵁ V y' ≤ S.g' ⁻¹ᵁ (S.f ⁻¹ᵁ U y')
    calc
      _ ≤ S.f' ⁻¹ᵁ (S.g ⁻¹ᵁ U y') := S.f'.preimage_mono (hVle y')
      _ = S.g' ⁻¹ᵁ (S.f ⁻¹ᵁ U y') := by
        simp only [← Scheme.Hom.comp_preimage, S.isPullback.w]
  let fU : (UX : Scheme) ⟶ (U y' : Scheme) := S.f.resLE (U y') UX le_rfl
  let g'V : (UY : Scheme) ⟶ (UX : Scheme) := S.g'.resLE UX UY hsub
  let f'V : (UY : Scheme) ⟶ (V y' : Scheme) := S.f'.resLE (V y') UY le_rfl
  let gV : (V y' : Scheme) ⟶ (U y' : Scheme) := S.g.resLE (U y') (V y') (hVle y')
  have hres : IsPullback g'V f'V fU gV := by
    simpa only [g'V, f'V, fU, gV] using Scheme.Hom.isPullback_resLE S.isPullback
      (US := U y') (UT := V y') (UX := UX) (UY := UY)
      (hUST := hVle y') (hUSX := le_rfl) (hUY := (inf_eq_right.mpr hsub).symm)
  have : IsAffine (U y' : Scheme) := hU y'
  have : IsAffine (V y' : Scheme) := hV y'
  have hfUeq : fU = S.f ∣_ U y' :=
    Scheme.Hom.resLE_eq_morphismRestrict (f := S.f) (U := U y')
  obtain ⟨_, _⟩ : QuasiCompact fU ∧ QuasiSeparated fU := by
    rw [hfUeq]; exact ⟨inferInstance, inferInstance⟩
  have hvanU : ∀ j : ℤ, (S.d : ℤ) < j → ∀ G : (UX : Scheme).Modules, G.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward fU).rightDerivedPlus j).obj G) := by
    intro j hj G hG
    simpa only [fU, ← Scheme.Hom.resLE_eq_morphismRestrict] using
      vanishes_above_morphismRestrict S (U y') (hU y').isCompact j hj G hG
  let Fv := (Scheme.Modules.restrictFunctor (Scheme.Opens.ι UY)).obj F'
  have hz : IsZero
      (((Scheme.Modules.pushforward (S.f' ∣_ V y')).rightDerivedPlus (n : ℤ)).obj Fv) := by
    simpa only [f'V, ← Scheme.Hom.resLE_eq_morphismRestrict] using
      haffine fU g'V f'V gV hres hvanU n hi Fv inferInstance
  exact IsZero.of_iso hz
    (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso S.f' (V y') n F').symm

end Stacks.AlgebraicGeometry.TopDegreeBaseChange
