module

public import StacksFrontier.AlgebraicGeometry.GlobalSections.PushoutSectionCover
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.SpecTarget
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Bijectivity of the comparison map on sections over an arbitrary cover

Mathlib's `AlgebraicGeometry.isIso_pushoutSection_of_iSup_eq` descends bijectivity of the
canonical comparison
`Γ(X, Uₓ) ⊗[Γ(S, Uₛ)] Γ(T, Uₜ) ⟶ Γ(X ×ₛ T, pr₁ ⁻¹ Uₓ ∩ pr₂ ⁻¹ Uₜ)` along a cover of `Uₓ`
carrying `[Finite ι]` on the index of the cover. That finiteness is what forces the
quasi-compactness and quasi-separatedness hypotheses on every consequence Mathlib draws from
it, and it is used in exactly one place: base change along `Γ(S, Uₛ) ⟶ Γ(T, Uₜ)` has to
preserve the limit of the `Pairwise`-indexed diagram of the cover, which Mathlib gets from
`CommRingCat.Under.preservesFiniteLimits_of_flat`.

`CommRingCat.Under.preservesLimits_pushout` supplies that for limits of *every* shape once
`Γ(T, Uₜ)` is flat and finitely presented as a `Γ(S, Uₛ)`-module, so the finiteness of the
index can be traded for finite presentation. This file carries out that trade and draws the
consequence the degree-zero assertion of Stacks Tag 0CKW asks for. Its injectivity counterpart
is `Stacks.Tag0CKW.mono_pushoutSection_of_iSup_eq`.

## Main results

* `Stacks.Tag0CKW.isIso_pushoutSection_of_iSup_eq`: the bijectivity descent, with no
  finiteness hypothesis on the index of the cover.
* `Stacks.Tag0CKW.isIso_pushoutSection_of_isAffineOpen_base`: bijectivity for an *arbitrary*
  open of an arbitrary scheme, obtained by covering it by all of the affine opens it contains.
* `Stacks.Tag0CKW.isIso_globalSectionsBaseChange_of_finiteLocallyFree`: the degree-zero
  assertion of Stacks Tag 0CKW — for a cartesian square over affine bases with the base
  morphism finite locally free, the canonical ring map
  `Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤) ⟶ Γ(X ×_S S', ⊤)` is an isomorphism, with no
  quasi-compactness or quasi-separatedness hypothesis on `X`.

## Implementation notes

The descent proof follows Mathlib's, with `CommRingCat.Under.preservesFiniteLimits_of_flat`
replaced by `CommRingCat.Under.preservesLimits_pushout` and the step `cases nonempty_fintype ι`
— which exists only to produce the `FinCategory (Pairwise ι)` instance that
`PreservesFiniteLimits` needs — deleted.

Mathlib states its lemma under `backward.defeqAttrib.useBackward true` and
`backward.isDefEq.respectTransparency false`. Neither option is used here. Three steps need
help without them, and all three are discharged by naming things rather than by widening a
transparency setting:

* the structure map of the lifted `Under` diagram has to be identified with
  `Scheme.Hom.appLE`, which is `hF₀` — pulled out of the comparison transformation into its own
  hypothesis, since inline the equation it states is not even type-correct at `implicit`
  transparency;
* the naturality of that comparison transformation, which Mathlib leaves to `cat_disch`, needs
  the `@[reassoc]` companions `pushout.inl_desc_assoc`/`pushout.inr_desc_assoc` in the simp
  set: neither they nor `pushout.inl_desc`/`pushout.inr_desc` carries `@[simp]`, so a bare
  `simp` after `pushout.hom_ext` makes no progress at all;
* `IsIso`/`Mono` of the components are produced by `IsIso.comp_isIso'` and `mono_comp'`, the
  explicit-argument forms, because instance search does not look through the `let` binding the
  transformation.

A local `implicit_reducible` attribute on four `Under` combinators (Mathlib tags
`Under.forget` itself) replaces the transparency options.

The second result takes the cover of an arbitrary open `UX` by *all* affine opens contained in
it, exactly as `Stacks.Tag0CKW.mono_pushoutSection_of_isAffineOpen_base` does. What makes the
pairwise hypothesis available is that lemma: an intersection of two affine opens of a scheme
which is not quasi-separated need not be compact, so Mathlib's
`mono_pushoutSection_of_isCompact_of_flat_right` cannot discharge it, while the
arbitrary-open injectivity statement can.

For the last result the two module-theoretic hypotheses are read off the finite local freeness
of `g` by transporting along `Scheme.isoSpec`: `Stacks.Morphisms.IsFiniteLocallyFree` respects
isomorphisms, so it may be moved from `g : S' ⟶ S` to `g ≫ S.isoSpec.hom : S' ⟶ Spec Γ(S, ⊤)`,
where `Stacks.Morphisms.sheafOfModules_isFiniteLocallyFree_iff_module` applies and
`Module.isFiniteLocallyFree_iff` splits the conclusion into finite presentation and flatness.

## References

* [Stacks Project, Tag 0CKW](https://stacks.math.columbia.edu/tag/0CKW)
* [Stacks Project, Tag 059K](https://stacks.math.columbia.edu/tag/059K)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Tag0CKW

attribute [local implicit_reducible] CategoryTheory.Under.lift CategoryTheory.Under.liftCone
  CategoryTheory.Under.pushout CategoryTheory.Under.homMk

variable {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T}
  (H : IsPullback g iY iX f)
  {US : S.Opens} {UT : T.Opens}
  {UX : X.Opens} (hUST : UT ≤ f ⁻¹ᵁ US) (hUSX : UX ≤ iX ⁻¹ᵁ US)
  {UY : Y.Opens} (hUY : UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)

/-- The comparison map of Mathlib's `AlgebraicGeometry.pushoutSection` is bijective after
descent along an arbitrary cover of `Uₓ` on whose members it is bijective and on whose pairwise
intersections it is injective, provided `Γ(T, Uₜ)` is a flat and finitely presented
`Γ(S, Uₛ)`-module. This is `AlgebraicGeometry.isIso_pushoutSection_of_iSup_eq` with the
finiteness of the index traded for finite presentation. -/
lemma isIso_pushoutSection_of_iSup_eq
    {ι : Type u} (VX : ι → X.Opens) (hVU : iSup VX = UX)
    (hV : ∀ i, IsIso (pushoutSection H hUST (show VX i ≤ _ by aesop) rfl))
    (hV' : ∀ i j, Mono (pushoutSection H hUST
      (show VX i ⊓ VX j ≤ _ from inf_le_left.trans (by clear hV; aesop)) rfl))
    (hT : (f.appLE US UT hUST).hom.Flat)
    (hTfp : letI := (f.appLE US UT hUST).hom.toAlgebra
      Module.FinitePresentation ↑Γ(S, US) ↑Γ(T, UT)) :
    IsIso (pushoutSection H hUST hUSX hUY) := by
  classical
  let D := Pairwise.diagram VX
  have h : iSup D.obj = UX := by
    refine le_antisymm (iSup_le_iff.mpr ?_) ?_
    · subst hVU; rintro (i | ⟨i, j⟩); exacts [le_iSup VX _, inf_le_left.trans (le_iSup VX _)]
    · subst hVU; exact iSup_le_iff.mpr fun i ↦ le_iSup D.obj (.single i)
  let c₀ : Cocone D := (colimit.cocone _).extend
    (eqToIso (Y := UX) (by simpa [CompleteLattice.colimit_eq_iSup])).hom
  have hDle : ∀ i : (Pairwise ι)ᵒᵖ, D.obj i.unop ≤ iX ⁻¹ᵁ US := fun i ↦ by
    grw [← hUSX, ← h]; exact le_iSup D.obj i.unop
  let F₀ := Under.lift (D.op ⋙ X.presheaf) ((Functor.const _).map (iX.appLE US UX hUSX) ≫
    ((X.presheaf.mapCone c₀.op).π))
  have hF₀ : ∀ i, (F₀.obj i).hom = iX.appLE US (D.obj i.unop) (hDle i) := fun i ↦ by
    dsimp only [F₀, CategoryTheory.Under.lift]
    simp [Scheme.Hom.appLE_map]
  let F := F₀ ⋙ Under.pushout (f.appLE US UT hUST) ⋙ Under.forget _
  let G : X.Opens ⥤ Y.Opens :=
    { obj U := g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ UT, map h := homOfLE (by gcongr; exact h.le) }
  let αF : F ⟶ D.op ⋙ G.op ⋙ Y.presheaf :=
  { app i := (pushout.congrHom (hF₀ i) rfl).hom ≫
      pushoutSection H hUST (hDle i) rfl
    naturality := by
      intro i j φ
      apply pushout.hom_ext <;>
        simp [F, F₀, CategoryTheory.Under.lift, pushoutSection, pushout.inl_desc,
          pushout.inr_desc, pushout.inl_desc_assoc, pushout.inr_desc_assoc,
          Scheme.Hom.appLE_map] }
  let c : Cone F := (Under.pushout (f.appLE US UT hUST) ⋙ Under.forget _).mapCone
    (Under.liftCone (X.presheaf.mapCone c₀.op) _)
  have : PreservesLimitsOfSize.{u, u} (Under.pushout (f.appLE US UT hUST)) :=
    CommRingCat.Under.preservesLimits_pushout _ hT hTfp
  let hc : IsLimit c :=
    have HX := ((TopCat.Presheaf.isSheaf_iff_isSheafPreservesLimitPairwiseIntersections
      _).mp X.IsSheaf VX).preserves (c := c₀.op)
    have HX := (HX (IsColimit.extendIso _ (colimit.isColimit _)).op).some
    isLimitOfPreserves (Under.pushout _ ⋙ Under.forget _) (Under.isLimitLiftCone _ _ HX)
  let c'₀ : Cocone (D ⋙ G) := (colimit.cocone _).extend
    (eqToIso (Y := UY) (by
      simp only [colimit.cocone_x, CompleteLattice.colimit_eq_iSup]
      eta_expand
      dsimp [G]
      rw [← iSup_inf_eq, ← Scheme.Hom.preimage_iSup, h, hUY])).hom
  let c' : Cone (D.op ⋙ G.op ⋙ Y.presheaf) := Y.presheaf.mapCone c'₀.op
  let hc' : IsLimit c' := by
    let e : D ⋙ G ≅ Pairwise.diagram fun i ↦ g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT :=
      NatIso.ofComponents (fun | .single i => .refl _ | .pair i j => eqToIso (by
        dsimp [D, G, Pairwise.diagram]; rw [Scheme.Hom.preimage_inf, inf_inf_distrib_right]))
    have HX := ((TopCat.Presheaf.isSheaf_iff_isSheafPreservesLimitPairwiseIntersections _).mp
      Y.IsSheaf (fun i ↦ g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT)).preserves
        (c := ((Cocone.precompose e.inv).obj c'₀).op)
    exact (IsLimit.postcomposeHomEquiv (Functor.isoWhiskerRight (NatIso.op e.symm) Y.presheaf) _)
      ((HX ((IsColimit.precomposeInvEquiv e _).symm
        (IsColimit.extendIso _ (colimit.isColimit _))).op).some.ofIsoLimit (Cone.ext (.refl _)))
  have HαF₁ (i : ι) : IsIso (αF.app (.op <| .single i)) :=
    IsIso.comp_isIso' inferInstance (hV i)
  have HαF₂ (i j : ι) : Mono (αF.app (.op <| .pair i j)) :=
    mono_comp' inferInstance (hV' i j)
  let f₁ : c.pt ⟶ c'.pt := hc'.lift ((Cone.postcompose αF).obj c)
  let f₂ : c'.pt ⟶ c.pt := hc.lift ⟨c'.pt, ⟨fun
    | .op (.single i) => c'.π.app _ ≫ inv (αF.app (.op <| .single i))
    | .op (.pair i j) => c'.π.app (.op (.single i)) ≫ inv (αF.app (.op <| .single i)) ≫
        F.map (Quiver.Hom.op <| Pairwise.Hom.left i j), by
    rintro ⟨i⟩ ⟨j⟩ f
    obtain ⟨i | ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩, rfl⟩ :=
      (show Function.Surjective Quiver.Hom.op from Quiver.Hom.opEquiv.surjective) f
    · simp [show Pairwise.Hom.id_single i = 𝟙 (Pairwise.single i) from rfl]
    · simp [show Pairwise.Hom.id_pair i j = 𝟙 (Pairwise.pair i j) from rfl]
    · simp
    · rw [← cancel_mono (αF.app _)]
      simpa using (c'.w (Quiver.Hom.op <| Pairwise.Hom.left i j)).trans
        (c'.w (Quiver.Hom.op <| Pairwise.Hom.right i j)).symm⟩⟩
  let e : c.pt ≅ c'.pt := by
    refine ⟨f₁, f₂, hc.hom_ext ?_, hc'.hom_ext ?_⟩
    · rintro ⟨i | ⟨i, j⟩⟩ <;> simp [f₁, f₂]
    · rintro ⟨i | ⟨i, j⟩⟩
      · simp [f₁, f₂]
      · simpa [f₁, f₂] using c'.w (Quiver.Hom.op <| Pairwise.Hom.left i j)
  convert! e.isIso_hom using 1
  · refine hc'.hom_ext fun i ↦ ?_
    rw [hc'.fac]
    ext1
    · simp [αF, c, Under.liftCone, c', c₀, F₀, CategoryTheory.Under.lift, pushoutSection,
        pushout.inl_desc_assoc, pushout.inl_desc, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
    · simp [αF, c, c', c₀, F₀, CategoryTheory.Under.lift, pushoutSection,
        pushout.inr_desc_assoc, pushout.inr_desc, Scheme.Hom.appLE_map]

/-- **Bijectivity of the comparison map over an arbitrary open, with no compactness
hypothesis.** When `Uₛ` and `Uₜ` are affine and `Γ(T, Uₜ)` is a flat, finitely presented
`Γ(S, Uₛ)`-module, the canonical map
`Γ(X, Uₓ) ⊗[Γ(S, Uₛ)] Γ(T, Uₜ) ⟶ Γ(X ×ₛ T, pr₁ ⁻¹ Uₓ ∩ pr₂ ⁻¹ Uₜ)` is bijective for *every*
open `Uₓ`. Mathlib's `AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`
is the same statement for a quasi-compact and quasi-separated `Uₓ`. -/
lemma isIso_pushoutSection_of_isAffineOpen_base
    (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT)
    (hT : (f.appLE US UT hUST).hom.Flat)
    (hTfp : letI := (f.appLE US UT hUST).hom.toAlgebra
      Module.FinitePresentation ↑Γ(S, US) ↑Γ(T, UT)) :
    IsIso (pushoutSection H hUST hUSX hUY) := by
  refine isIso_pushoutSection_of_iSup_eq H hUST hUSX hUY
    (ι := { V : X.affineOpens // (V : X.Opens) ≤ UX }) (fun V ↦ (V.1 : X.Opens)) ?_ ?_ ?_ hT hTfp
  · refine le_antisymm (iSup_le fun V ↦ V.2) fun x hx ↦ ?_
    obtain ⟨V, hVmem, hxV, hVU⟩ :=
      Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (U := UX) (x := x) hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨V, hVmem⟩, hVU⟩, hxV⟩
  · intro V
    exact isIso_pushoutSection_of_isAffineOpen H hUST
      (show (V.1 : X.Opens) ≤ _ from V.2.trans hUSX) rfl hUS hUT V.1.2
  · intro V W
    exact mono_pushoutSection_of_isAffineOpen_base H hUST
      (show (V.1 : X.Opens) ⊓ (W.1 : X.Opens) ≤ _ from
        inf_le_left.trans (V.2.trans hUSX)) rfl hUS hUT hT hTfp

/-- The restriction map of `AlgebraicGeometry.Scheme.Hom.appLE` from the top open to the top
open is the global-sections map. -/
lemma appLE_top_eq_appTop {A B : Scheme.{u}} (φ : A ⟶ B)
    (e : (⊤ : A.Opens) ≤ φ ⁻¹ᵁ ⊤) : φ.appLE ⊤ ⊤ e = φ.appTop := by
  rw [Scheme.Hom.appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  congr 1

/-- The global-sections ring map of a finite locally free morphism over an affine base is flat
and makes the target's global sections a finitely presented module over the source's: this is
the module-theoretic content of [Stacks, Tag 02KB]. The conclusion is stated for any ring map
`φ` equal to the global-sections map `g.appTop`. -/
@[sga "1 VIII 7.6" "partial"]
lemma flat_and_finitePresentation_of_isFiniteLocallyFree
    {S' S : Scheme.{u}} (g : S' ⟶ S) [IsAffine S]
    [Stacks.Morphisms.IsFiniteLocallyFree g]
    {φ : Γ(S, ⊤) ⟶ Γ(S', ⊤)} (hφ : φ = g.appTop) :
    φ.hom.Flat ∧
      (letI := φ.hom.toAlgebra; Module.FinitePresentation ↑Γ(S, ⊤) ↑Γ(S', ⊤)) := by
  subst hφ
  have hiso : Stacks.Morphisms.IsFiniteLocallyFree (g ≫ S.isoSpec.hom) :=
    MorphismProperty.RespectsIso.postcomp _ S.isoSpec.hom g ‹_›
  have happ : ((Scheme.ΓSpecIso Γ(S, ⊤)).inv ≫ (g ≫ S.isoSpec.hom).appTop) = g.appTop := by
    simp only [Scheme.Hom.comp_appTop, Scheme.isoSpec, asIso_hom, Scheme.toSpecΓ_appTop,
      Iso.inv_hom_id_assoc]
  have hAff : IsAffineHom (g ≫ S.isoSpec.hom) := hiso.toIsAffineHom
  have key := (Stacks.Morphisms.sheafOfModules_isFiniteLocallyFree_iff_module
    (g ≫ S.isoSpec.hom)).mp hiso.toIsFiniteLocallyFree
  rw [happ] at key
  let := g.appTop.hom.toAlgebra
  obtain ⟨hfp, hflat⟩ := (Module.isFiniteLocallyFree_iff ↑Γ(S, ⊤) ↑Γ(S', ⊤)).mp key
  exact ⟨hflat, hfp⟩

/-- **Stacks Project, Tag 0CKW, degree zero for the structure sheaf.** For a cartesian square
```
X' --g'-→ X
|         |
f'        f
↓         ↓
S' --g--→ S
```
with `S` and `S'` affine and `g` finite locally free, the canonical map from the tensor product
of global-function rings to the ring of global functions on the base change,
`Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤) ⟶ Γ(X', ⊤)`, is an isomorphism. **`X` is not required to be
quasi-compact or quasi-separated**.

Mathlib's nearest statement,
`AlgebraicGeometry.isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat`, requires
`X` to be quasi-compact and quasi-separated. -/
@[sga "3 VIB 11.0" "partial", sga "3 VIB 12.2" "(iii), special case"]
theorem isIso_globalSectionsBaseChange_of_finiteLocallyFree
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (h : IsPullback g' f' f g)
    [IsAffine S] [IsAffine S'] [Stacks.Morphisms.IsFiniteLocallyFree g] :
    IsIso (AlgebraicGeometry.pushoutSection h
      (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
      (by simp) (by simp) (by simp)) := by
  have hg := flat_and_finitePresentation_of_isFiniteLocallyFree g (appLE_top_eq_appTop g (by simp))
  refine isIso_pushoutSection_of_isAffineOpen_base h (by simp) (by simp) (by simp)
    (isAffineOpen_top S) (isAffineOpen_top S') ?_ ?_
  exacts [hg.1, hg.2]

/-- The degree-zero case of [Stacks, Tag 0CKW] for the structure sheaf, with the hypotheses
written out: there is no quasi-compactness, quasi-separatedness, finiteness or Noetherian
hypothesis on `X`, and nothing on `g` beyond finite local freeness, which is stated as
affineness of `g` together with finite local freeness of the direct image
`(Scheme.Modules.pushforward g).obj (SheafOfModules.unit _)` of the structure sheaf. -/
example : ∀ {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (h : IsPullback g' f' f g)
    [IsAffine S] [IsAffine S']
    (_ : IsAffineHom g ∧ SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit _))),
    IsIso (AlgebraicGeometry.pushoutSection h
      (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
      (by simp) (by simp) (by simp)) :=
 by
  intro X' X S' S g' f' f g h hS hS' hg
  have := hS
  have := hS'
  have := (Stacks.Morphisms.isFiniteLocallyFree_iff g).mpr hg
  exact isIso_globalSectionsBaseChange_of_finiteLocallyFree g' f' f g h

end Stacks.Tag0CKW

end
