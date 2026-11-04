module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Affine
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Local

/-!
# Affine base change for direct images: the reduction to a square of affine schemes

Let
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
be a cartesian square of schemes with `f` affine, and let `F` be a quasi-coherent
`𝒪_X`-module.  The base-change assertion of Stacks Tag 02KG says that the canonical morphism
`g^* f_* F ⟶ f'_* (g')^* F` is invertible.  **This file reduces that assertion to the case of a
cartesian square all four of whose schemes are affine, and discharges it** using the affine
case `Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_affine`.

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.innerIsPullback`: the square obtained from a
  cartesian square by restricting over an open `V` of `S` and an open `V'` of `S'` lying over
  `V` is again cartesian.
* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_comp_restrictSquare`:
  invertibility of the base-change morphism of the twice-restricted square gives invertibility
  of the base-change morphism of the square obtained by restricting over `V'` only.
* `Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom`:
  **the base-change assertion of Stacks Tag 02KG.**  The base-change morphism of a cartesian
  square whose right-hand morphism is affine is invertible at every quasi-coherent module.

## Route

`S'` is covered by the affine opens lying inside the preimage of an affine open of `S`
(`TopologicalSpace.Opens.IsBasis.isOpenCover_mem_and_le`), and over such a member the
assertion is local on the base by
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_cover`.  The square
obtained by restricting over such a `V'` is pasted in two ways: as the given square followed
by the restriction square of `f'` over `V'`, and as the restriction square of `f` over `V`
followed by the twice-restricted square.  The two pastings differ only in that their
horizontal morphisms are written as `Scheme.Hom.resLE` composed with an inclusion rather than
the other way round, which `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι` identifies; the
base-change morphism is then transported by `isIso_baseChangeNatTrans_congr`, which is
`subst` on those two equalities.

In the second pasting the factor contributed by the restriction square of `f` over `V` is
invertible by
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare`, so only
the twice-restricted square is left.  Its four corners are affine -- `V` and `V'` by the choice
of covering, `f ⁻¹ᵁ V` because `f` is affine, and `f' ⁻¹ᵁ V'` because `f'` is affine, being a
base change of `f` -- it is cartesian by `AlgebraicGeometry.Scheme.Hom.isPullback_resLE`, and
the module on its upper-right corner is quasi-coherent by
`Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback`.  That leaves exactly the
hypotheses of
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_affine`, which
discharges it.  The four affineness facts are passed as named hypotheses rather than by
instance search: `AlgebraicGeometry.IsAffineOpen` is a definition that is not reducible, so
instance search does not see that it is the affineness of the open as a scheme.

## What is not done

**No project tag attribute is attached here.**  The base-change assertion of [Stacks, Tag
02KG] is now proved, with no hypothesis beyond the ones the tag has, as
`isIso_baseChangeNatTrans_of_isAffineHom`; the all-affine case is discharged by
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_affine` in
`Affine.lean`.  Nothing here touches the two other assertions of the tag: quasi-coherence of
the direct image, which is
`Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom`, and
the comparison with the derived direct image, which is not proved anywhere in this
repository.

A subtlety: `Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso`
and `AlgebraicGeometry.pullbackTildeIso` are two independent `leftAdjointUniq` constructions
of the same natural isomorphism, and **only the second carries the normalization against the
adjunction unit**.  The global-sections comparison built on the first,
`Stacks.AlgebraicGeometry.SectionsColimit.sectionsPullbackIso`, therefore cannot serve the
identification of the base-change morphism on global sections; the one that does is
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.pullbackΓIso`, built on the second.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.TwoSquare
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChangeIso

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- The base-change morphism depends on the two horizontal morphisms of the square only through
their values, so an invertibility statement transports along equalities of those morphisms. -/
lemma isIso_baseChangeNatTrans_congr {g'₁ g'₂ : X' ⟶ X} {g₁ g₂ : S' ⟶ S}
    (e' : g'₁ = g'₂) (e : g₁ = g₂) (w₁ : g'₁ ≫ f = f' ≫ g₁) (w₂ : g'₂ ≫ f = f' ≫ g₂)
    (M : X.Modules) (h : IsIso ((AffinePushforward.baseChangeNatTrans w₁).app M)) :
    IsIso ((AffinePushforward.baseChangeNatTrans w₂).app M) := by
  subst e'
  subst e
  exact h

section Inner

/-- The preimage of an open of `S'` lying over an open `V` of `S` lies over the preimage of
`V`. -/
lemma preimage_le_preimage (w : g' ≫ f = f' ≫ g) {V : S.Opens} {V' : S'.Opens}
    (hle : V' ≤ g ⁻¹ᵁ V) :
    f' ⁻¹ᵁ V' ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, w, Scheme.Hom.comp_preimage]
  exact f'.preimage_mono hle

/-- The square obtained from `w` by restricting over an open `V` of `S` and an open `V'` of `S'`
lying over `V`. -/
lemma innerSquare (w : g' ≫ f = f' ≫ g) {V : S.Opens} {V' : S'.Opens}
    (hle : V' ≤ g ⁻¹ᵁ V) :
    g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') (preimage_le_preimage w hle) ≫ (f ∣_ V) =
      (f' ∣_ V') ≫ g.resLE V V' hle := by
  rw [← cancel_mono V.ι]
  simp [w]

/-- The restricted square is again cartesian. -/
lemma innerIsPullback (hw : IsPullback g' f' f g) {V : S.Opens} {V' : S'.Opens}
    (hle : V' ≤ g ⁻¹ᵁ V) :
    IsPullback (g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') (preimage_le_preimage hw.w hle))
      (f' ∣_ V') (f ∣_ V) (g.resLE V V' hle) := by
  have h := Scheme.Hom.isPullback_resLE hw (US := V) (UT := V') (UX := f ⁻¹ᵁ V)
    hle le_rfl (UY := f' ⁻¹ᵁ V')
    (inf_eq_right.mpr (preimage_le_preimage hw.w hle)).symm
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_eq_morphismRestrict] at h
  exact h

end Inner

section Reduce

/-- The base-change morphism of the square obtained from `w` by restricting over an open `V'` of
`S'` is invertible as soon as the base-change morphism of the twice-restricted square over an
open `V` of `S` containing the image of `V'` is. -/
theorem isIso_baseChangeNatTrans_comp_restrictSquare (hw : IsPullback g' f' f g)
    (F : X.Modules) {V : S.Opens} {V' : S'.Opens} (hle : V' ≤ g ⁻¹ᵁ V)
    (H : IsIso ((AffinePushforward.baseChangeNatTrans (innerSquare hw.w hle)).app
      ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F))) :
    IsIso ((AffinePushforward.baseChangeNatTrans
      (comp_square hw.w (AffineBaseChange.restrictSquare f' V'))).app F) := by
  have hB : IsIso ((AffinePushforward.baseChangeNatTrans
      (comp_square (AffineBaseChange.restrictSquare f V) (innerSquare hw.w hle))).app F) := by
    rw [baseChangeNatTrans_comp_square_app (AffineBaseChange.restrictSquare f V)
      (innerSquare hw.w hle)]
    have h₁ : IsIso ((Scheme.Modules.pullbackComp (g.resLE V V' hle) V.ι).inv.app
        ((Scheme.Modules.pushforward f).obj F)) := inferInstance
    have h₂ : IsIso ((Scheme.Modules.pullback (g.resLE V V' hle)).map
        ((AffinePushforward.baseChangeNatTrans
          (AffineBaseChange.restrictSquare f V)).app F)) := by
      have := AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare f V F
      exact Functor.map_isIso _ _
    have h₄ : IsIso ((Scheme.Modules.pushforward (f' ∣_ V')).map
        ((Scheme.Modules.pullbackComp
          (g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') (preimage_le_preimage hw.w hle))
          (f ⁻¹ᵁ V).ι).hom.app F)) := Functor.map_isIso _ _
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁
      (@IsIso.comp_isIso _ _ _ _ _ _ _ h₂ (@IsIso.comp_isIso _ _ _ _ _ _ _ H h₄))
  exact isIso_baseChangeNatTrans_congr
    (Scheme.Hom.resLE_comp_ι g' (preimage_le_preimage hw.w hle))
    (Scheme.Hom.resLE_comp_ι g hle) _ _ F hB

/-- **The base-change assertion of Stacks Tag 02KG.**  The base-change morphism of a cartesian
square of schemes whose right-hand morphism is affine is invertible at every quasi-coherent
module. -/
@[stacks 02KG "affine base change"]
theorem isIso_baseChangeNatTrans_of_isAffineHom (hw : IsPullback g' f' f g) [IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent] :
    IsIso ((AffinePushforward.baseChangeNatTrans hw.w).app F) := by
  have hf' : IsAffineHom f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hw inferInstance
  refine isIso_baseChangeNatTrans_of_cover hw.w F _
    (S'.isBasis_affineOpens.isOpenCover_mem_and_le
      (S.isBasis_affineOpens.isOpenCover.comap g.base.hom)) ?_
  rintro ⟨⟨V', ⟨V, hV⟩⟩, hV', hle⟩
  have hVa : IsAffineOpen V := hV
  have hV'a : IsAffineOpen V' := hV'
  have hqc : ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F).IsQuasicoherent :=
    AffineBaseChange.isQuasicoherent_pullback _ F
  have h1 : IsAffine (f' ⁻¹ᵁ V').toScheme := hV'a.preimage f'
  have h2 : IsAffine (f ⁻¹ᵁ V).toScheme := hVa.preimage f
  have h3 : IsAffine (V' : Scheme.{u}) := hV'a
  have h4 : IsAffine (V : Scheme.{u}) := hVa
  exact isIso_baseChangeNatTrans_comp_restrictSquare hw F hle
    (isIso_baseChangeNatTrans_of_affine (innerIsPullback hw hle) _)

end Reduce

end Stacks.AlgebraicGeometry.AffineBaseChangeIso

end
