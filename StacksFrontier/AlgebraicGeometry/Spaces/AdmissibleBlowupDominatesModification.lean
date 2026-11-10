module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupExtensionFromOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImagePartialSection
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspaceImage

/-!
# A modification is dominated by an admissible blowup

Let `f : X ⟶ B` be a proper morphism of algebraic spaces over `S` which is an isomorphism over a
quasi-compact open `U` of the quasi-compact and quasi-separated `B`.  Stacks 087G says that some
`U`-admissible blowup `B' ⟶ B` dominates `X`: it factors as `B' ⟶ X ⟶ B`.

The source proves it in one line from Stacks 0GUW, which supplies a `U`-admissible blowup
`b : B' ⟶ B` such that the strict transform `X'` of `X` maps isomorphically to `B'`; then
`B' ≅ X' ⟶ X ×_B B' ⟶ X` is the factorization.  That step is
`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_comp_eq_of_isIso_strictTransform` below, for
an arbitrary subspace `E ⊆ B'` defining the strict transform.

Stacks 0CPI extends a section `s : U ⟶ X` of a proper `f : X ⟶ W`, for opens `U ⊆ W ⊆ Y`, over
a `U`-admissible blowup `b : Y' ⟶ Y`: there is `s' : b⁻¹(W) ⟶ X` with `f ∘ s' = b` and `s'`
equal to `s ∘ b` on `b⁻¹(U)`.  The source's proof replaces `X` by the scheme-theoretic image of
`s` (Stacks 0CP3), applies Stacks 087G there, and extends the blowup of `W` to `Y` by
Stacks 086D; that is
`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_extension_of_isProper_of_section`, which
takes the statement of Stacks 087G as its hypothesis `hdom`.

## Implementation notes

Stacks 0GUW is not in the library.  This module therefore records
no tag: given Stacks 0GUW, Stacks 087G is the composite of Stacks 0GUW with the
first result below, and Stacks 0CPI is the second result applied to that form.

## References

* [Stacks Project, Tag 087G](https://stacks.math.columbia.edu/tag/087G)
* [Stacks Project, Tag 0GUW](https://stacks.math.columbia.edu/tag/0GUW)
* [Stacks Project, Tag 0CPI](https://stacks.math.columbia.edu/tag/0CPI)
* [Stacks Project, Tag 0CP3](https://stacks.math.columbia.edu/tag/0CP3)
* [Stacks Project, Tag 086D](https://stacks.math.columbia.edu/tag/086D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks in presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance (priority := high) hasPullback_presheaf_AdmissibleBlowupDominatesModification
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site is slow
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_AdmissibleBlowupDominatesModification :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- The strict transform `X' ⊆ X ×_A A'` lies over `X` and over `A'` compatibly: its two
projections, followed by `f` and by `b`, agree. -/
theorem strictTransformSpaceι_toSource_comp {A X A' : AlgebraicSpaces B S hS} (f : X ⟶ A)
    (b : A' ⟶ A) (E : Subfunctor A'.1) :
    strictTransformSpaceι B S hS f b E ≫ strictTransformPullbackToSource B S hS f b ≫ f =
      strictTransformSpaceToBlowUp B S hS f b E ≫ b := by
  rw [(AlgebraicSpaces.isPullback_fiberProduct B S hS f b).w, ← Category.assoc]

/-- **A blowup whose strict transform is an isomorphism dominates the source.**  Let
`f : X ⟶ A` be a morphism of algebraic spaces over `S`, `U ⊆ A` an open subspace, and
`b : A' ⟶ A` a `U`-admissible blowup such that the strict transform `X'` of `X` (with respect to
a subspace `E ⊆ A'`) maps isomorphically to `A'`.  Then `b` factors through `f`: the composite
`A' ≅ X' ⟶ X ×_A A' ⟶ X` lies over `A`.

This is the proof of Stacks 087G from the conclusion of Stacks 0GUW. -/
theorem exists_isAdmissibleBlowup_comp_eq_of_isIso_strictTransform {A X : AlgebraicSpaces B S hS}
    (f : X ⟶ A) (U : OpenSubspaces B S hS A.1)
    (h : ∃ (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A), IsAdmissibleBlowup B S hS U b ∧
      ∃ E : Subfunctor A'.1, IsIso (strictTransformSpaceToBlowUp B S hS f b E)) :
    ∃ (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A), IsAdmissibleBlowup B S hS U b ∧
      ∃ g : A' ⟶ X, g ≫ f = b := by
  obtain ⟨A', b, hb, E, hE⟩ := h
  refine ⟨A', b, hb, inv (strictTransformSpaceToBlowUp B S hS f b E) ≫
    strictTransformSpaceι B S hS f b E ≫ strictTransformPullbackToSource B S hS f b, ?_⟩
  rw [Category.assoc, Category.assoc, strictTransformSpaceι_toSource_comp, IsIso.inv_hom_id_assoc]

/-! ### Extending a section over an admissible blowup -/

/-- **Stacks 0CPI, from Stacks 087G.**  Let `U ⊆ W ⊆ Y` be open subspaces, `f : X ⟶ W` a proper
morphism and `s : U ⟶ X` a section of `f` over `U`, with `Y` quasi-compact and quasi-separated
and `U`, `W` quasi-compact.  Then there are a `U`-admissible blowup `b : Y' ⟶ Y` and a morphism
`s' : b⁻¹(W) ⟶ X` with `f ∘ s' = b|_{b⁻¹(W)}` which extends `s`: on `b⁻¹(U)` it is `s ∘ b`.

The hypothesis `hdom` is the statement of Stacks 087G, which the library has from Stacks 0GUW by
`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_comp_eq_of_isIso_strictTransform`.  The
proof is the source's: `X` is replaced by the scheme-theoretic image `Z` of `s`, over which
`Z ⟶ W` is an isomorphism over `U` (Stacks 0CP3); Stacks 087G gives a `U`-admissible blowup
`W' ⟶ W` dominating `Z`, and Stacks 086D extends it to a `U`-admissible blowup of `Y`. -/
theorem exists_isAdmissibleBlowup_extension_of_isProper_of_section
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hdom : ∀ (X A : AlgebraicSpaces B S hS) (f : X ⟶ A) (U : OpenSubspaces B S hS A.1),
      IsQuasiCompactSpace B S hS A.1 → IsAbsolutelyQuasiSeparated B S hS hZ A.1 →
      IsQuasiCompactSpace B S hS U.1.toFunctor → IsProper B S hS f.hom →
      IsIso (pullback.snd f.hom U.1.ι) →
      ∃ (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A), IsAdmissibleBlowup B S hS U b ∧
        ∃ g : A' ⟶ X, g ≫ f = b)
    {X Y : AlgebraicSpaces B S hS} (U W : OpenSubspaces B S hS Y.1) (hUW : U.1 ≤ W.1)
    (f : X ⟶ openSubspace B S hS Y W) (s : openSubspace B S hS Y U ⟶ X)
    (hs : s.hom ≫ f.hom = Subfunctor.homOfLe hUW) (hf : IsProper B S hS f.hom)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (hWqc : IsQuasiCompactSpace B S hS W.1.toFunctor) :
    ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ Y), IsAdmissibleBlowup B S hS U b ∧
      ∃ s' : (W.1.preimage b.hom).toFunctor ⟶ X.1,
        s' ≫ f.hom = W.1.fromPreimage b.hom ∧
          Subfunctor.homOfLe (fun T _ hx => hUW T hx :
              U.1.preimage b.hom ≤ W.1.preimage b.hom) ≫ s' =
            U.1.fromPreimage b.hom ≫ s.hom := by
  classical
  -- `U` as an open subspace of `W`, and its identification with `U`
  let Wsp := openSubspace B S hS Y W
  let U' : OpenSubspaces B S hS Wsp.1 := openSubspaceRestrict B S hS Y W U
  have hUle : U.1 ≤ Subfunctor.range W.1.ι := by rwa [Subfunctor.range_ι]
  have : IsIso (U.1.fromPreimage W.1.ι) := Subfunctor.isIso_fromPreimage_of_le_range _ _ hUle
  set e : U'.1.toFunctor ≅ U.1.toFunctor := asIso (U.1.fromPreimage W.1.ι)
  have heι : e.hom ≫ Subfunctor.homOfLe hUW = U'.1.ι := by
    ext T x
    rfl
  -- the section over `U'`, and the scheme-theoretic image `Z` of it
  set sW : U'.1.toFunctor ⟶ X.1 := e.hom ≫ s.hom
  have hsW : sW ≫ f.hom = U'.1.ι := by
    rw [Category.assoc, hs, heι]
  set Z := schemeTheoreticImageSubfunctor B S hS sW
  have hZcl : IsClosedSubspace B S hS Z := isClosedSubspace_schemeTheoreticImageSubfunctor B S hS
    sW X.2
  set Zsp : AlgebraicSpaces B S hS := ⟨Z.toFunctor, hZcl.1⟩
  set ιZ : Zsp ⟶ X := ObjectProperty.homMk Z.ι
  have hWqs : IsAbsolutelyQuasiSeparated B S hS hZ Wsp.1 :=
    isAbsolutelyQuasiSeparated_subfunctor B S hS hZ hYqs W.1 W.2.1
  have hU'qc : IsQuasiCompactSpace B S hS U'.1.toFunctor :=
    isQuasiCompactSpace_of_iso B S hS e.symm hUqc
  have hfZ : IsProper B S hS (ιZ ≫ f).hom :=
    isProper_comp B S hS hZcl.1 X.2 Wsp.2 Z.ι f.hom
      (isProper_of_isClosedImmersion B S hS hZcl.1 X.2 Z.ι hZcl.2) hf
  -- Stacks 0CP3: `Z ⟶ W` is an isomorphism over `U'`
  have hiso : IsIso (pullback.snd (ιZ ≫ f).hom U'.1.ι) :=
    isIso_pullback_snd_schemeTheoreticImageSubfunctor_comp_of_section B S hS X.2 Wsp.2 f.hom
      hf.1 U'.1 U'.2 (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Wsp.2 hWqs hU'qc _) sW hsW
  -- Stacks 087G for `Z ⟶ W`, and Stacks 086D to extend the blowup of `W` to `Y`
  obtain ⟨W', bW, hbW, g, hg⟩ :=
    hdom Zsp Wsp (ιZ ≫ f) U' hWqc hWqs hU'qc hfZ hiso
  obtain ⟨Y', b, hb, e', hpb⟩ := exists_isAdmissibleBlowup_isPullback' hZ hYqc hYqs U W hUqc hWqc
    bW hbW
  -- the inverse image of `W`, as an algebraic space, maps to `W'`
  set P := W.1.preimage b.hom
  have hPalg : IsAlgebraicSpace B S hS P.toFunctor :=
    (isOpenSubspace_preimage B S hS b.hom W.1 Y.2 Y'.2 W.2).1
  set Psp : AlgebraicSpaces B S hS := ⟨P.toFunctor, hPalg⟩
  set t : Psp ⟶ W' := hpb.lift (ObjectProperty.homMk (W.1.fromPreimage b.hom))
    (ObjectProperty.homMk P.ι) (by
      refine ObjectProperty.hom_ext _ ?_
      exact Subfunctor.fromPreimage_ι W.1 b.hom)
  have ht : (t ≫ bW).hom = W.1.fromPreimage b.hom :=
    congrArg (fun φ : Psp ⟶ Wsp => φ.hom) (hpb.lift_fst _ _ _)
  have htf : (t ≫ g ≫ ιZ ≫ f).hom = W.1.fromPreimage b.hom := by rw [hg, ht]
  refine ⟨Y', b, hb, (t ≫ g ≫ ιZ).hom, by simpa using htf, ?_⟩
  · -- on `b⁻¹(U)` both sides factor through `Z`, and agree after `Z ⟶ W` over `U'`
    have hle : U.1.preimage b.hom ≤ W.1.preimage b.hom := fun T _ hx => hUW T hx
    set j := Subfunctor.homOfLe hle
    set q : (U.1.preimage b.hom).toFunctor ⟶ U'.1.toFunctor := U.1.fromPreimage b.hom ≫ e.inv
    have hqW : q ≫ U'.1.ι = j ≫ W.1.fromPreimage b.hom := by
      refine (cancel_mono W.1.ι).1 ?_
      have h1 : U'.1.ι ≫ W.1.ι = e.hom ≫ U.1.ι := (Subfunctor.fromPreimage_ι U.1 W.1.ι).symm
      simp only [q, j, Category.assoc, h1, Iso.inv_hom_id_assoc, Subfunctor.fromPreimage_ι,
        Subfunctor.homOfLe_ι_assoc]
    have hsZ := toSchemeTheoreticImage_ι B S hS sW
    have key : j ≫ (t ≫ g).hom = q ≫ toSchemeTheoreticImage B S hS sW := by
      have ha : (j ≫ (t ≫ g).hom) ≫ (ιZ ≫ f).hom = q ≫ U'.1.ι := by
        rw [hqW, Category.assoc]
        change j ≫ (t ≫ g ≫ ιZ ≫ f).hom = _
        rw [htf]
      have ha' : (q ≫ toSchemeTheoreticImage B S hS sW) ≫ (ιZ ≫ f).hom = q ≫ U'.1.ι := by
        change q ≫ toSchemeTheoreticImage B S hS sW ≫ Z.ι ≫ f.hom = _
        rw [← Category.assoc (toSchemeTheoreticImage B S hS sW), hsZ, hsW]
      have : Mono (pullback.snd (ιZ ≫ f).hom U'.1.ι) := @IsIso.mono_of_iso _ _ _ _ _ hiso
      have hl : pullback.lift _ q ha = pullback.lift _ q ha' :=
        (cancel_mono (pullback.snd (ιZ ≫ f).hom U'.1.ι)).1
          (by rw [pullback.lift_snd, pullback.lift_snd])
      simpa only [pullback.lift_fst] using congrArg (· ≫ pullback.fst _ _) hl
    change j ≫ (t ≫ g).hom ≫ Z.ι = _
    rw [← Category.assoc, key, Category.assoc, hsZ]
    change (U.1.fromPreimage b.hom ≫ e.inv) ≫ e.hom ≫ s.hom = _
    rw [Category.assoc, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Space

end
