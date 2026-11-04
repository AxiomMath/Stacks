module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.BaseChange
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeLocality.Pasting

/-!
# The base-change assertion of Stacks Tag 02KG is local on the base

For a cartesian square of schemes
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
with `f` affine and `𝓕` a quasi-coherent module on `X`, the third assertion of Stacks Tag
02KG says that the canonical base-change morphism `g^* f_* 𝓕 ⟶ f'_* (g')^* 𝓕` is an
isomorphism.  The Stacks Project proves this by saying "the statement is local on `S` and
`S'`, hence we may assume `X = Spec A`, `S = Spec R`, `S' = Spec R'`".  This file carries out
that reduction: it derives the general statement from the case of a cartesian square all of
whose four corners are affine, which is taken here as a hypothesis.

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.isIso_baseChangeNatTrans_of_affineCase`:
  granted the affine case, the canonical base-change morphism of an arbitrary cartesian square
  with affine right-hand morphism is an isomorphism at every quasi-coherent module.
* `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.baseChangeIso_of_affineCase`: the same
  conclusion packaged as the bare isomorphism of modules, in the shape in which the consumers
  of the base-change assertion thread it as a hypothesis.

## Implementation notes

Invertibility of a morphism of sheaves of modules is local on the scheme
(`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`), so it suffices to
restrict the base-change morphism to each member of an open covering of `S'`.  The covering
used is the one produced by `TopologicalSpace.Opens.IsBasis.isOpenCover_mem_and_le` from the
affine opens of `S'` and the preimages of the affine opens of `S`: its members are the affine
opens `W ≤ S'` which lie over some affine open `V ≤ S`.

Over such a pair the square is cut down twice, and both cuts are instances of pasting a square
with a restriction square, handled by
`Stacks.AlgebraicGeometry.AffineBaseChangeLocality.Pasting`:

* pasting the restriction square of `f'` over `W` with the given square produces a square with
  top `(f' ⁻¹ᵁ W).ι ≫ g'` and bottom `W.ι ≫ g`, and
  `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.isIso_map_baseChangeNatTrans_of_vcomp`
  turns its invertibility into the invertibility of the restriction to `W` of the base-change
  morphism, because the restriction square has invertible base-change morphism by
  `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare`;
* the *same* square is also the pasting of the restriction square of `f` over `V` with the
  square of restricted morphisms `f' ⁻¹ᵁ W ⟶ f ⁻¹ᵁ V` over `W ⟶ V`, whose four corners are
  affine: `V` and `W` are affine opens and `f`, `f'` are affine morphisms, so
  `AlgebraicGeometry.IsAffineOpen.preimage` applies.  That square is cartesian by cancelling
  the restriction square of `f` out of the pasted one, so the affine case applies to it.

The two presentations of the pasted square have equal but not syntactically identical top and
bottom morphisms -- `Scheme.Hom.resLE_comp_ι` relates them -- which is what
`Stacks.AlgebraicGeometry.AffineBaseChangeLocality.isIso_baseChangeNatTrans_congr` is for.

The affine case is stated as an explicit hypothesis, with invertibility of the *canonical*
base-change morphism as its conclusion: an abstract isomorphism between the two sides cannot be
glued, so the local statement has to be about the canonical map even though the consumers only
need the resulting isomorphism.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChangeLocality

/-- **The locality step of Stacks Tag 02KG, assertion 3.**  Granted the affine case -- that the
canonical base-change morphism of a cartesian square of *affine* schemes with affine right-hand
morphism is invertible at every quasi-coherent module -- the canonical base-change morphism of
an arbitrary cartesian square with affine right-hand morphism is invertible at every
quasi-coherent module. -/
theorem isIso_baseChangeNatTrans_of_affineCase {X' X S' S : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (h : IsPullback g' f' f g) [IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent]
    (haff : ∀ {Y' Y T' T : Scheme.{u}} [IsAffine Y'] [IsAffine Y] [IsAffine T'] [IsAffine T]
      {q' : Y' ⟶ Y} {p' : Y' ⟶ T'} {p : Y ⟶ T} {q : T' ⟶ T} (hp : IsPullback q' p' p q),
      IsAffineHom p → ∀ G : Y.Modules, G.IsQuasicoherent →
      IsIso ((AffinePushforward.baseChangeNatTrans hp.w).app G)) :
    IsIso ((AffinePushforward.baseChangeNatTrans h.w).app F) := by
  have hf' : IsAffineHom f' := isAffineHom_isStableUnderBaseChange.of_isPullback h inferInstance
  have hU := S'.isBasis_affineOpens.isOpenCover_mem_and_le
    ((S.isBasis_affineOpens).isOpenCover.comap g.base.hom)
  refine AffineBaseChange.isIso_of_isIso_restrict _ _ hU (fun WV ↦ ?_)
  obtain ⟨⟨W₀, V₀⟩, hWaff, hle⟩ := WV
  set W : S'.Opens := W₀ with hWdef
  set V : S.Opens := (V₀ : S.Opens) with hVdef
  have hVa : IsAffineOpen V := V₀.2
  have hWa : IsAffineOpen W := hWaff
  have hgW : W ≤ g ⁻¹ᵁ V := hle
  have hfV : IsAffineOpen (f ⁻¹ᵁ V) := hVa.preimage f
  have hf'W : IsAffineOpen (f' ⁻¹ᵁ W) := hWa.preimage f'
  have iV : IsAffine V.toScheme := hVa
  have iW : IsAffine W.toScheme := hWa
  have ifV : IsAffine (f ⁻¹ᵁ V).toScheme := hfV
  have if'W : IsAffine (f' ⁻¹ᵁ W).toScheme := hf'W
  have hle2 : (f' ⁻¹ᵁ W) ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    have e : (f' ≫ g) ⁻¹ᵁ V = (g' ≫ f) ⁻¹ᵁ V := by rw [h.w]
    simp only [Scheme.Hom.comp_preimage] at e
    rw [← e]
    exact leOfHom ((Opens.map f'.base).map (homOfLE hgW))
  let gV : W.toScheme ⟶ V.toScheme := g.resLE V W hgW
  let t : (f' ⁻¹ᵁ W).toScheme ⟶ (f ⁻¹ᵁ V).toScheme := g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ W) hle2
  have hfVpull : IsPullback (f ⁻¹ᵁ V).ι (f ∣_ V) f V.ι := (isPullback_morphismRestrict f V).flip
  have hf'Wpull : IsPullback (f' ⁻¹ᵁ W).ι (f' ∣_ W) f' W.ι :=
    (isPullback_morphismRestrict f' W).flip
  have hBig : IsPullback ((f' ⁻¹ᵁ W).ι ≫ g') (f' ∣_ W) f (W.ι ≫ g) := hf'Wpull.paste_horiz h
  have htop : t ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ W).ι ≫ g' := Scheme.Hom.resLE_comp_ι g' hle2
  have hbase : gV ≫ V.ι = W.ι ≫ g := Scheme.Hom.resLE_comp_ι g hgW
  have hBig2 : IsPullback (t ≫ (f ⁻¹ᵁ V).ι) (f' ∣_ W) f (gV ≫ V.ι) := by
    rw [htop, hbase]; exact hBig
  have hcomm : t ≫ (f ∣_ V) = (f' ∣_ W) ≫ gV := by
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι, hbase,
      ← Category.assoc, htop, Category.assoc, h.w, ← Category.assoc,
      morphismRestrict_ι_assoc, Category.assoc]
  have hSmall : IsPullback t (f' ∣_ W) (f ∣_ V) gV := hBig2.of_right hcomm hfVpull
  have hfVaff : IsAffineHom (f ∣_ V) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback hfVpull inferInstance
  have hqc : ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F).IsQuasicoherent :=
    AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion (f ⁻¹ᵁ V).ι F
  have hrV := AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare f V F
  have hStep1 : IsIso ((AffinePushforward.baseChangeNatTrans hBig2.w).app F) :=
    isIso_baseChangeNatTrans_vcomp hSmall.w (AffineBaseChange.restrictSquare f V) hBig2.w F
      (Functor.map_isIso _ _)
      (haff hSmall hfVaff ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F) hqc)
  have hStep2 : IsIso ((AffinePushforward.baseChangeNatTrans hBig.w).app F) :=
    isIso_baseChangeNatTrans_congr htop hbase hBig2.w hBig.w F hStep1
  have hStep3 : IsIso ((Scheme.Modules.pullback W.ι).map
      ((AffinePushforward.baseChangeNatTrans h.w).app F)) :=
    isIso_map_baseChangeNatTrans_of_vcomp (AffineBaseChange.restrictSquare f' W) h.w hBig.w F
      (AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare f' W _) hStep2
  have hnat := (Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.naturality
    ((AffinePushforward.baseChangeNatTrans h.w).app F)
  have hr : IsIso ((Scheme.Modules.restrictFunctor W.ι).map
      ((AffinePushforward.baseChangeNatTrans h.w).app F) ≫
      (Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.app _) := by
    rw [hnat]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance hStep3
  exact IsIso.of_isIso_comp_right _
    ((Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.app _)

/-- **Stacks Tag 02KG, assertion 3, reduced to the affine case.**  Granted the affine case,
every cartesian square with affine right-hand morphism identifies the inverse image of a direct
image with the direct image of the inverse image, for every quasi-coherent module.  This is the
shape in which the assertion is threaded as a hypothesis by its consumers, for instance by
`Stacks.AlgebraicGeometry.isUniversallyPureRelative_of_pushforward_isLocallyProjective`. -/
noncomputable def baseChangeIso_of_affineCase
    (haff : ∀ {Y' Y T' T : Scheme.{u}} [IsAffine Y'] [IsAffine Y] [IsAffine T'] [IsAffine T]
      {q' : Y' ⟶ Y} {p' : Y' ⟶ T'} {p : Y ⟶ T} {q : T' ⟶ T} (hp : IsPullback q' p' p q),
      IsAffineHom p → ∀ G : Y.Modules, G.IsQuasicoherent →
      IsIso ((AffinePushforward.baseChangeNatTrans hp.w).app G)) :
    ∀ {Y' Y T' T : Scheme.{u}} (q' : Y' ⟶ Y) (p' : Y' ⟶ T') (p : Y ⟶ T) (q : T' ⟶ T),
      IsPullback q' p' p q → IsAffineHom p → ∀ G : Y.Modules, G.IsQuasicoherent →
      ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pushforward p).obj G) ≅
        (Scheme.Modules.pushforward p').obj ((Scheme.Modules.pullback q').obj G)) := by
  intro Y' Y T' T q' p' p q hp hpaff G hG
  have hpaff' := hpaff
  have hG' := hG
  have : IsIso ((AffinePushforward.baseChangeNatTrans hp.w).app G) :=
    isIso_baseChangeNatTrans_of_affineCase hp G haff
  exact asIso ((AffinePushforward.baseChangeNatTrans hp.w).app G)

end Stacks.AlgebraicGeometry.AffineBaseChangeLocality

end
