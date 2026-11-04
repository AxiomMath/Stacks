module

public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.Absolute
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianApproximation.Absolute
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyIdealCoveringQcqs
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyLimit
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyLimitStageNoetherian

/-!
# The substantial direction of Stacks 0F89, at quasi-compact quasi-separated generality

[Stacks, Tag 0F89] states that a scheme `X` carrying

1. a finite affine open covering `X = U 0 ∪ ⋯ ∪ U (m - 1)`, and
2. finite type quasi-coherent ideals `I j ⊆ 𝒪_X` with `V(I j) = X \ U j`

has the resolution property **if and only if** each `I j` is the quotient of a finite locally
free `𝒪_X`-module.  The direction the source calls trivial is
`AlgebraicGeometry.exists_isFiniteLocallyFree_epi_of_isIdealAffineCovering`.  This file proves
the substantial direction, at the generality the source states it — no Noetherian hypothesis.

## Main results

* `AlgebraicGeometry.hasResolutionProperty_of_isLimit_of_isIdealAffineCovering`: the substantial
  direction for a scheme presented as the limit of a cofiltered diagram of Noetherian schemes
  with affine transition morphisms.
* `AlgebraicGeometry.hasResolutionProperty_of_isIdealAffineCovering`: **the substantial
  direction of [Stacks, Tag 0F89]**, for an arbitrary scheme carrying the data (1) and (2).
* `AlgebraicGeometry.hasResolutionProperty_of_coe_support_idealSheafDataOfHom`: the same with the
  sheaves of ideals presented as images of morphisms out of finite locally free modules, which is
  the shape the reduction of [Stacks, Tag 0F8B] to a stage produces.

A named inhabitant of the whole binder list at once is
`AlgebraicGeometry.exists_isIdealAffineCovering_specULiftInt` of
`StacksFrontier/AlgebraicGeometry/Perfect/ResolutionPropertyIdealCoveringWitness.lean`, which is a
separate module because the fact that an affine scheme has the resolution property lives in a
much larger import closure than anything used here.

## The argument

It is the source's.  The data (1) and (2) force `X` to be quasi-compact and quasi-separated
(`AlgebraicGeometry.IsIdealAffineCovering.compactSpace` and
`AlgebraicGeometry.IsIdealAffineCovering.quasiSeparatedSpace`), so absolute Noetherian
approximation ([Stacks, Tag 01ZA],
`AlgebraicGeometry.Scheme.exists_isLimit_affine_locallyOfFiniteType`) writes `X = lim X i` with
every stage of finite type over the integers, hence Noetherian, and every transition morphism
affine.  Along that presentation:

* the affine covering comes from a stage, by Mathlib's
  `AlgebraicGeometry.Scheme.exists_isOpenCover_and_isAffine_of_finite` — this is the source's
  appeal to [Stacks, Tag 01Z6] for affineness of the complementary opens at a late stage;
* each resolution `E j ⟶ I j ⟶ 𝒪_X` descends to a stage, by
  `AlgebraicGeometry.exists_stage_isFiniteLocallyFree_hom_pt_of_isLimit`, which is
  [Stacks, Tag 0B8W] (1) followed by [Stacks, Tag 01ZR] (3);
* the image of the descended morphism cuts out, on the limit, the complement of the member of
  the covering — `AlgebraicGeometry.coe_support_idealSheafDataOfHom_pullback` commutes the
  vanishing locus with the pullback and
  `AlgebraicGeometry.coe_support_idealSheafDataOfHom_of_epi` removes first the descent
  isomorphism and then the given epimorphism `q j`, after which
  `AlgebraicGeometry.idealSheafDataOfHom_idealPow_one` identifies the image of the inclusion of
  `I j` with `I j`;
* [Stacks, Tag 01Z4] (2) (`AlgebraicGeometry.exists_map_preimage_eq_map_preimage`) makes that
  equality of opens hold at a stage, and [Stacks, Tag 01Z4]
  (`AlgebraicGeometry.exists_map_eq_top`) makes the pulled-back covering a covering at a
  further stage;
* there the Noetherian case of the tag applies, in the form
  `AlgebraicGeometry.hasResolutionProperty_of_isNoetherian_of_coe_support_idealSheafDataOfHom`;
* finally the limit is affine over that stage, so
  `AlgebraicGeometry.hasResolutionProperty_of_isLimit` — the immediate direction of
  [Stacks, Tag 0F8B], itself the affine case of [Stacks, Tag 0F88] — transports the resolution
  property back to `X`.

## Implementation notes

Noetherianness of the stages is used exactly where the Noetherian case of the tag is used and
where [Stacks, Tag 01Z4] (2) asks the two compared opens to be quasi-compact; it is not a
hypothesis of the statement, which is the source's, because the stages are produced inside the
proof.

## References

* [Stacks Project, Tag 0F89](https://stacks.math.columbia.edu/tag/0F89)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 01Z6](https://stacks.math.columbia.edu/tag/01Z6)
* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ModuleLimits
open Stacks.AlgebraicGeometry.IdealPowerColimit

universe u

namespace AlgebraicGeometry

/-- The image of a morphism `θ : F ⟶ 𝒪_Y` whose pullback along `f` factors as an isomorphism, an
epimorphism onto a sheaf of ideals `J` and its inclusion cuts out, after pulling back, the open
complement `U` of the vanishing locus of `J`. -/
theorem preimage_compl_support_idealSheafDataOfHom_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Y.Modules) [F.IsQuasicoherent] (θ : F ⟶ structureModule Y) {E : X.Modules}
    [E.IsQuasicoherent] {J : X.IdealSheafData} {U : X.Opens}
    (κ : (Scheme.Modules.pullback f).obj F ≅ E) (q : E ⟶ idealPow J 1) [Epi q]
    (hκ : (Scheme.Modules.pullback f).map θ ≫ (Scheme.Modules.pullbackUnitIso f).hom =
      κ.hom ≫ q ≫ (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple J 1
        (structureModule X)).ι)
    (hJ : (J.support : Set X) = (U : Set X)ᶜ) :
    f ⁻¹ᵁ ((idealSheafDataOfHom F θ).support.compl : Y.Opens) = U := by
  have h1 := coe_support_idealSheafDataOfHom_pullback f F θ
  have h2 := coe_support_idealSheafDataOfHom_of_epi κ.hom _ _ hκ
  have h3 := coe_support_idealSheafDataOfHom_of_epi q
    (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple J 1 (structureModule X)).ι _ rfl
  rw [idealSheafDataOfHom_idealPow_one J, hJ] at h3
  refine TopologicalSpace.Opens.ext ?_
  simp only [TopologicalSpace.Opens.map_coe, TopologicalSpace.Closeds.coe_compl,
    Set.preimage_compl, h1.symm.trans (h2.trans h3), compl_compl]

/-- A Noetherian scheme `Y` has the resolution property as soon as it is covered by affine opens
`W j`, each the preimage under some `g j : Y ⟶ Z j` of the complement of the vanishing locus of
the image of a morphism `θ j` from a finite locally free module to the structure sheaf. -/
theorem hasResolutionProperty_of_isNoetherian_of_preimage_compl_support {Y : Scheme.{u}}
    [IsNoetherian Y] {m : ℕ} {Z : Fin m → Scheme.{u}} (g : ∀ j, Y ⟶ Z j)
    (F : ∀ j, (Z j).Modules) [∀ j, (F j).IsQuasicoherent]
    (hF : ∀ j, SheafOfModules.IsFiniteLocallyFree (R := (Z j).ringCatSheaf) (F j))
    (θ : ∀ j, F j ⟶ structureModule (Z j)) (W : Fin m → Y.Opens)
    (hW : ∀ j, IsAffineOpen (W j)) (hcov : ⨆ j, W j = ⊤)
    (hpre : ∀ j, g j ⁻¹ᵁ ((idealSheafDataOfHom (F j) (θ j)).support.compl : (Z j).Opens) = W j) :
    HasResolutionProperty Y := by
  refine hasResolutionProperty_of_isNoetherian_of_coe_support_idealSheafDataOfHom W
    (fun j => (Scheme.Modules.pullback (g j)).obj (F j))
    (fun j => SheafOfModules.IsFiniteLocallyFree.pullback_scheme (g j) (F j) (hF j))
    (fun j => (Scheme.Modules.pullback (g j)).map (θ j) ≫
      (Scheme.Modules.pullbackUnitIso (g j)).hom)
    (fun _ => inferInstance) hW hcov fun j => ?_
  refine (coe_support_idealSheafDataOfHom_pullback_of_appLE (g j) (F j) (θ j) _
    (structureAppₗ_pullbackSectionHom (g j) (F j) (θ j))).trans ?_
  simpa [TopologicalSpace.Closeds.coe_compl, Set.preimage_compl]
    using congrArg (fun O : Y.Opens => (O : Set Y)ᶜ) (hpre j)

section

variable {K : Type u} [Category.{u} K] [IsCofiltered K] (D : K ⥤ Scheme.{u})
  [∀ {i j : K} (g : i ⟶ j), IsAffineHom (D.map g)] (c : Cone D)

include c in
/-- **The substantial direction of [Stacks, Tag 0F89] along a Noetherian presentation.**  Let
`c` be a limit cone over a cofiltered diagram `D` of Noetherian schemes with affine transition
morphisms.  If the limit carries a finite affine open covering `U` and finite type
quasi-coherent sheaves of ideals `J` cutting out the complements of its members, and each `J j`
is the quotient of a finite locally free module, then the limit has the resolution property. -/
theorem hasResolutionProperty_of_isLimit_of_isIdealAffineCovering (hc : IsLimit c)
    (hN : ∀ i, IsNoetherian (D.obj i)) {m : ℕ} {U : Fin m → c.pt.Opens}
    {J : Fin m → c.pt.IdealSheafData} (h : IsIdealAffineCovering c.pt U J)
    (E : Fin m → c.pt.Modules)
    (hE : ∀ j, SheafOfModules.IsFiniteLocallyFree (R := c.pt.ringCatSheaf) (E j))
    (q : ∀ j, E j ⟶ idealPow (J j) 1) (hq : ∀ j, Epi (q j)) :
    HasResolutionProperty c.pt := by
  classical
  have hcs : ∀ i, CompactSpace (D.obj i) := fun i => (hN i).toCompactSpace
  have hqs : ∀ i, QuasiSeparatedSpace (D.obj i) := fun i =>
    have _ : IsLocallyNoetherian (D.obj i) := (hN i).toIsLocallyNoetherian
    IsLocallyNoetherian.quasiSeparatedSpace
  -- the affine covering of the limit comes from a stage
  obtain ⟨i₀, V, hVcov, hV⟩ :=
    Scheme.exists_isOpenCover_and_isAffine_of_finite D c hc U h.isOpenCover h.isAffineOpen
  -- pulling a quasi-compact open back along `D.map f` and then the cone projection
  have hw {a b : K} (f : a ⟶ b) (O : (D.obj b).Opens) :
      c.π.app a ⁻¹ᵁ D.map f ⁻¹ᵁ O = c.π.app b ⁻¹ᵁ O := by
    rw [← Scheme.Hom.comp_preimage, c.w]
  -- the resolutions descend to stages over `i₀`
  have hEqc : ∀ j, (E j).IsQuasicoherent := fun j =>
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree
      (R := c.pt.ringCatSheaf) (E j)
  choose l e F hF θ κ hκ using fun j : Fin m =>
    exists_stage_isFiniteLocallyFree_hom_pt_of_isLimit D c hc i₀ (E j) (hE j)
      (q j ≫ (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple (J j) 1
        (structureModule c.pt)).ι)
  have hFqc : ∀ j, (F j).IsQuasicoherent := fun j =>
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree
      (R := (D.obj (l j)).ringCatSheaf) (F j)
  -- the vanishing locus of the descended morphism, read on the limit
  -- the two opens at the stage `l j` have the same preimage on the limit
  have hleft : ∀ j, c.π.app (l j) ⁻¹ᵁ
        ((@idealSheafDataOfHom _ (F j) (hFqc j) (θ j)).support.compl : (D.obj (l j)).Opens)
      = c.π.app (l j) ⁻¹ᵁ (D.map (e j) ⁻¹ᵁ V j) := fun j =>
    have := hq j
    (preimage_compl_support_idealSheafDataOfHom_eq _ _ _ (κ j) (q j) (hκ j)
      (h.support_eq j)).trans ((hV j).2.trans (hw (e j) (V j)).symm)
  -- Tag 01Z4 (2): the two quasi-compact opens agree at a stage
  have hcompact (i : K) (O : (D.obj i).Opens) : IsCompact (O : Set (D.obj i)) :=
    have := hN i; NoetherianSpace.isCompact _
  choose k t hk using fun j : Fin m =>
    exists_map_preimage_eq_map_preimage D c hc (hcompact (l j) _) (hcompact (l j) _) (hleft j)
  -- one stage below all of them
  obtain ⟨kk, hkk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image k)
  have r : ∀ j, kk ⟶ k j := fun j =>
    (hkk (Finset.mem_image_of_mem _ (Finset.mem_univ j))).some
  -- Tag 01Z4: the covering becomes a covering at a stage
  have hcovlim : c.π.app kk ⁻¹ᵁ (⨆ j, D.map (r j ≫ t j ≫ e j) ⁻¹ᵁ V j) = ⊤ := by
    rw [Scheme.Hom.preimage_iSup, iSup_congr fun j => hw (r j ≫ t j ≫ e j) (V j),
      ← Scheme.Hom.preimage_iSup, hVcov.iSup_eq_top]
    simp
  obtain ⟨kk', s, hs⟩ :=
    exists_map_eq_top D c hc (⨆ j, D.map (r j ≫ t j ≫ e j) ⁻¹ᵁ V j) hcovlim
  have hpre : ∀ j, D.map (s ≫ r j ≫ t j) ⁻¹ᵁ
        ((@idealSheafDataOfHom _ (F j) (hFqc j) (θ j)).support.compl : (D.obj (l j)).Opens)
      = D.map (s ≫ r j ≫ t j ≫ e j) ⁻¹ᵁ V j := fun j => by
    simp only [D.map_comp, Scheme.Hom.comp_preimage]
    rw [hk j]
  -- the Noetherian case of the tag at the stage `kk'`
  have := hN kk'
  have := hasResolutionProperty_of_isNoetherian_of_preimage_compl_support
    (Z := fun j => D.obj (l j)) (fun j => D.map (s ≫ r j ≫ t j)) F hF θ
    (fun j => D.map (s ≫ r j ≫ t j ≫ e j) ⁻¹ᵁ V j)
    (fun j => (hV j).1.preimage _) (by
      simp only [← hs, Scheme.Hom.preimage_iSup, D.map_comp, Scheme.Hom.comp_preimage]) hpre
  exact hasResolutionProperty_of_isLimit D c hc kk'

end

/-- **The substantial direction of [Stacks, Tag 0F89].**  Let `X` be a scheme with a finite
affine open covering `U` and finite type quasi-coherent sheaves of ideals `I j` whose vanishing
loci are the complements of the `U j`.  If each `I j` is the quotient of a finite locally free
`𝒪_X`-module then `X` has the resolution property.

`X` need not be Noetherian: this is the tag at the generality the source states it.  Together with
`AlgebraicGeometry.exists_isFiniteLocallyFree_epi_of_isIdealAffineCovering`, which is the
direction the source calls trivial, it is the equivalence the tag asserts. -/
@[stacks 0F89 "the substantial direction, at the source's generality: finite-locally-free \
quotients of the ideals give the resolution property"]
theorem hasResolutionProperty_of_isIdealAffineCovering {X : Scheme.{u}} {m : ℕ}
    {U : Fin m → X.Opens} {I : Fin m → X.IdealSheafData} (h : IsIdealAffineCovering X U I)
    (E : Fin m → X.Modules)
    (hE : ∀ j, SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) (E j))
    (q : ∀ j, E j ⟶ idealPow (I j) 1) (hq : ∀ j, Epi (q j)) :
    HasResolutionProperty X := by
  have _ : CompactSpace X := h.compactSpace
  have _ : QuasiSeparatedSpace X := h.quasiSeparatedSpace
  obtain ⟨A, hpre, hne, hdir, D, cπ, haff, hft, hqc, ⟨hlim⟩⟩ :=
    Scheme.exists_isLimit_affine_locallyOfFiniteType X
  let _ : Preorder A := hpre
  let _ : Nonempty A := hne
  let _ : IsDirected A (· ≤ ·) := hdir
  have _ : IsCofiltered Aᵒᵈ := inferInstance
  have _ : ∀ {i j : Aᵒᵈ} (g : i ⟶ j), IsAffineHom (D.map g) := fun g => haff g
  exact hasResolutionProperty_of_isLimit_of_isIdealAffineCovering D (Cone.mk X cπ) hlim
    (fun i => isNoetherian_of_locallyOfFiniteType_terminalFrom _ (hft i) (hqc i)) h E hE q hq

/-- **The substantial direction of [Stacks, Tag 0F89] for morphisms out of finite locally free
modules.**  Let `X` be a scheme with a finite affine open covering `U`, and for each `j` let
`θ j : 𝓔 j ⟶ 𝒪_X` be a morphism out of a finite locally free module whose image is a sheaf of
ideals cutting out the complement of `U j`.  Then `X` has the resolution property.

This is `AlgebraicGeometry.hasResolutionProperty_of_isIdealAffineCovering` restated for the
shape the reduction of [Stacks, Tag 0F8B] to a stage produces its data in — a morphism to the
structure sheaf, with the sheaf of ideals its image.  It is the quasi-compact quasi-separated
counterpart of
`AlgebraicGeometry.hasResolutionProperty_of_isNoetherian_of_coe_support_idealSheafDataOfHom`,
and nothing is reproved: the sheaf of ideals is `AlgebraicGeometry.idealSheafDataOfHom`, of
finite type by `AlgebraicGeometry.isFiniteType_idealSheafDataOfHom`, and the epimorphism onto it
is `AlgebraicGeometry.epi_toIdealPowOfHom`. -/
theorem hasResolutionProperty_of_coe_support_idealSheafDataOfHom {X : Scheme.{u}} {m : ℕ}
    (U : Fin m → X.Opens) (E : Fin m → X.Modules)
    (hE : ∀ j, SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) (E j))
    (θ : ∀ j, E j ⟶ structureModule X) (hqc : ∀ j, (E j).IsQuasicoherent)
    (hU : ∀ j, IsAffineOpen (U j)) (hcov : ⨆ j, U j = ⊤)
    (hsupp : ∀ j,
      (((@idealSheafDataOfHom X (E j) (hqc j) (θ j)).support : Set X)) = ((U j : Set X))ᶜ) :
    HasResolutionProperty X := by
  have hEft : ∀ j, (E j).IsFiniteType := fun j =>
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation
      (E j) (SheafOfModules.IsFiniteLocallyFree.isFinitePresentation (E j) (hE j))).2
  have hft : ∀ j, (@idealSheafDataOfHom X (E j) (hqc j) (θ j)).IsFiniteType := fun j =>
    have _ := hqc j
    have _ := hEft j
    isFiniteType_idealSheafDataOfHom (E j) (θ j)
  exact hasResolutionProperty_of_isIdealAffineCovering
    (isIdealAffineCovering_of_isFiniteType U
      (fun j => @idealSheafDataOfHom X (E j) (hqc j) (θ j)) hU hcov (fun j V => hft j V) hsupp)
    E hE (fun j => @toIdealPowOfHom X (E j) (hqc j) (θ j))
    (fun j => @epi_toIdealPowOfHom X (E j) (hqc j) (θ j))

end AlgebraicGeometry

end
