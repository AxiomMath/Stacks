module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSmallerBase

/-!
# Quasi-compactness and quasi-separatedness pass to a *larger* base (Stacks 03HE, 03HL, 04SG)

Let `h : W ⟶ S` be a morphism of a big fppf site and let `Λ_h` be the lower-shriek extension
`CategoryTheory.OverShriek.relocalizePresheafFunctor h` of Stacks 03I5 part (2).
`StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSmallerBase` proves that quasi-compactness
(Stacks 03HE) and quasi-separatedness (Stacks 03HL, part (3)) are **reflected** by `Λ_h`, hence
pass from a larger base to a smaller one. This file proves the opposite direction: they are
**preserved**, hence pass from a smaller base to a larger one.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_relocalizeMap` and
  `AlgebraicGeometry.Space.isQuasiSeparated_relocalizeMap`: the lower-shriek extension of a
  quasi-compact, resp. quasi-separated, morphism of algebraic spaces over `W` is one.
* `AlgebraicGeometry.Space.isQuasiCompact_relocalizeToYoneda_comp` and
  `AlgebraicGeometry.Space.isQuasiSeparated_relocalizeToYoneda_comp`: the conditions for the
  structural morphism of a lower-shriek extension pass from `S` to a larger base `S'`.
* `AlgebraicGeometry.Space.isQuasiCompact_spacesOverSmallerBaseFunctor` and
  `AlgebraicGeometry.Space.isQuasiSeparated_spacesOverSmallerBaseFunctor`: **Stacks 03HE** and
  **Stacks 03HL** part (3) for the structural morphism of the image of Stacks 04SG's forward
  functor pass from `S` to a larger base `S'`.

Together with the reflecting direction these are equivalences, but the two directions have
genuinely different proofs and are stated separately rather than combined, so that each can be
used at the base pair it is needed at without carrying the other's hypotheses.

## Implementation notes

The reason this direction is not formally dual is that reading quasi-compactness over the
*larger* base `S'` quantifies over algebraic spaces over `S'`, of which there are more than there
are over `S`, and an arbitrary one of them need not be a lower-shriek extension. The reflecting
direction needs no such thing, which is why
`StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSmallerBase` records only it and records the
converse as needing the essential surjectivity of the equivalence of Stacks 04SG.

**That is not what this direction needs, and the way around it is the affine criterion.** By
`AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace_pullback_affine` — the implication
of Stacks 03KG that Stacks 041L uses — quasi-compactness of a morphism of algebraic spaces may be
tested on base changes along scheme-valued points whose scheme is *affine*, hence along morphisms
from *representable* presheaves. A morphism from a representable presheaf into `Λ_h Y` is a
section of `Λ_h Y`, and a section of a lower-shriek extension carries a factorization of the
structure morphism of its index through `W` (`AlgebraicGeometry.exists_relocalizeChart`). So
every test object that has to be considered *already* comes from the smaller base, for free, and
no essential surjectivity is involved.

With the test object identified, the base change is computed on the smaller base: `Λ_h` preserves
fibre products (`AlgebraicGeometry.relocalizePresheaf_preservesConnectedLimits`), so the pullback
over `S` is the extension of the pullback over `W`, and
`AlgebraicGeometry.Space.isQuasiCompactSpace_relocalizePresheafFunctor_obj` carries
quasi-compactness of that space across. The comparison of the two cartesian squares is
`CategoryTheory.IsPullback.of_iso` along the isomorphism `AlgebraicGeometry.relocalizeBaseHom`
supplies, which is the identity on underlying schemes.

Quasi-separatedness is quasi-compactness of the relative diagonal, and the extension of the
diagonal *is* the diagonal of the extension because the extension preserves fibre products; that
is the same bookkeeping as in `AlgebraicGeometry.Space.isQuasiSeparated_of_relocalizeMap`, read
in the other direction.

The passage to a larger base is then the mirror of the reflecting one, through
`CategoryTheory.OverShriek.relocalizeToYoneda_comp_relocalizeYonedaComp` and
`AlgebraicGeometry.Space.relocalizeToYoneda_eq`, both read through
`CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`.

## References

* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] etale_scheme_respectsIso

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

/-! ### The lower-shriek extension preserves quasi-compactness and quasi-separatedness -/

/-- **The lower-shriek extension of a quasi-compact morphism of algebraic spaces over `W` is
quasi-compact.** By the affine criterion of Stacks 03KG it is enough to test base changes along
morphisms from representable presheaves with affine scheme, and such a morphism into `Λ_h Y` is a
section of `Λ_h Y`, hence carries a factorization of its index through `W`: the test object
already comes from the smaller base. The base change is then the extension of a base change over
`W`, because `Λ_h` preserves fibre products. -/
theorem Space.isQuasiCompact_relocalizeMap {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B W hW X) (hY : IsAlgebraicSpace B W hW Y) (k : X ⟶ Y)
    (hk : Space.IsQuasiCompact B W hW k) :
    Space.IsQuasiCompact B S hS ((OverShriek.relocalizePresheafFunctor h).map k) := by
  have _ : PreservesLimitsOfShape WalkingCospan (OverShriek.relocalizePresheafFunctor h) :=
    relocalizePresheaf_preservesConnectedLimits h
  let XO : AlgebraicSpaces B S hS := ⟨_, isAlgebraicSpace_viewOver B W S hW hS h X hX⟩
  let YO : AlgebraicSpaces B S hS := ⟨_, isAlgebraicSpace_viewOver B W S hW hS h Y hY⟩
  let kO : XO ⟶ YO := ObjectProperty.homMk ((OverShriek.relocalizePresheafFunctor h).map k)
  refine Space.isQuasiCompact_of_isQuasiCompactSpace_pullback_affine B S hS
    XO.property YO.property kO.hom ?_
  intro T hT γ
  obtain ⟨ψ, hψ, a, ha⟩ := exists_relocalizeChart B W S hW hS h T γ
  have hkO : kO.hom = (OverShriek.relocalizePresheafFunctor h).map k := rfl
  let ρ := relocalizedYonedaIso B (B.obj hW) (B.obj hS) h (Over.mk ψ)
  let eI : (OverShriek.relocalizePresheafFunctor h).obj (yoneda.obj (Over.mk ψ)) ≅
      yoneda.obj T :=
    ρ ≪≫ (asIso (yoneda.map (relocalizeBaseHom B W S hW hS h hψ))).symm
  have hγ : γ = eI.inv ≫ (OverShriek.relocalizePresheafFunctor h).map a := by
    rw [ha]
    simp only [eI, ρ, relocalizeChart, Iso.trans_inv, Iso.symm_inv, asIso_hom, Category.assoc]
  have hpb : IsPullback (pullback.fst γ kO.hom ≫ eI.inv) (pullback.snd γ kO.hom)
      ((OverShriek.relocalizePresheafFunctor h).map a)
      ((OverShriek.relocalizePresheafFunctor h).map k) := by
    refine (IsPullback.of_hasPullback γ kO.hom).of_iso (Iso.refl _) eI.symm
      (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simpa using hγ
    · simp [hkO]
  refine Space.isQuasiCompactSpace_of_iso B S hS
    ((PreservesPullback.iso (OverShriek.relocalizePresheafFunctor h) a k).trans
      (hpb.isoIsPullback _ _ (IsPullback.of_hasPullback _ _)).symm) ?_
  refine Space.isQuasiCompactSpace_relocalizePresheafFunctor_obj B W S hW hS h _ ?_
  exact hk (yoneda.obj (Over.mk ψ)) (isAlgebraicSpace_yoneda B W hW (Over.mk ψ))
    (Space.isQuasiCompactSpace_yoneda_of_isAffine B W hW (Over.mk ψ) hT) a

/-- **The lower-shriek extension of a quasi-separated morphism of algebraic spaces over `W` is
quasi-separated.** Quasi-separatedness is quasi-compactness of the relative diagonal, and the
extension of the diagonal is the diagonal of the extension because the extension preserves fibre
products. -/
theorem Space.isQuasiSeparated_relocalizeMap {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B W hW X) (hY : IsAlgebraicSpace B W hW Y) (k : X ⟶ Y)
    (hk : Space.IsQuasiSeparated B W hW k) :
    Space.IsQuasiSeparated B S hS ((OverShriek.relocalizePresheafFunctor h).map k) := by
  have _ : PreservesLimitsOfShape WalkingCospan (OverShriek.relocalizePresheafFunctor h) :=
    relocalizePresheaf_preservesConnectedLimits h
  have hiso : (Space.quasiCompactPresheafProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hdiag : (OverShriek.relocalizePresheafFunctor h).map (pullback.diagonal k) ≫
      (PreservesPullback.iso (OverShriek.relocalizePresheafFunctor h) k k).hom =
        pullback.diagonal ((OverShriek.relocalizePresheafFunctor h).map k) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, PreservesPullback.iso_hom_fst, ← Functor.map_comp,
        pullback.diagonal_fst, CategoryTheory.Functor.map_id]
    · simp only [Category.assoc, PreservesPullback.iso_hom_snd, ← Functor.map_comp,
        pullback.diagonal_snd, CategoryTheory.Functor.map_id]
  have key : Space.IsQuasiCompact B S hS
      ((OverShriek.relocalizePresheafFunctor h).map (pullback.diagonal k)) :=
    Space.isQuasiCompact_relocalizeMap B W S hW hS h hX
      (isAlgebraicSpace_pullback B W hW k k hX hX hY) (pullback.diagonal k) hk
  have h1 : Space.quasiCompactPresheafProperty B S hS
      ((OverShriek.relocalizePresheafFunctor h).map (pullback.diagonal k) ≫
        (PreservesPullback.iso (OverShriek.relocalizePresheafFunctor h) k k).hom) :=
    (MorphismProperty.cancel_right_of_respectsIso _ _ _).2 key
  rw [hdiag] at h1
  exact h1

/-! ### Change of base scheme -/

section ChangeOfBase

variable (S' : Scheme.{u}) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')

/-- A property of morphisms of presheaves respecting isomorphisms passes from the image under
`Λ_g` of the structural morphism over `S` to the structural morphism over `S'`. -/
private theorem relocalizeToYoneda_comp_of_map
    (P : MorphismProperty ((BigFppfOver B S' hS')ᵒᵖ ⥤ Type u)) [P.RespectsIso]
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u)
    (key : P ((OverShriek.relocalizePresheafFunctor g).map (OverShriek.relocalizeToYoneda h F))) :
    P (OverShriek.relocalizeToYoneda (h ≫ g) F) := by
  have h1 : P ((OverShriek.relocalizeCompIso h g F).inv ≫
      (OverShriek.relocalizePresheafFunctor g).map (OverShriek.relocalizeToYoneda h F)) :=
    (MorphismProperty.cancel_left_of_respectsIso _ _ _).2 key
  rw [← OverShriek.relocalizeToYoneda_comp_relocalizeYonedaComp h g F] at h1
  exact (MorphismProperty.cancel_right_of_respectsIso _ _ _).1 h1

/-- A property of morphisms of presheaves respecting isomorphisms passes from the structural
morphism over `S` to the one over `S'` for `spacesOverSmallerBaseFunctor`, as soon as it does for
`relocalizeToYoneda`. -/
private theorem spacesOverSmallerBaseFunctor_of_relocalizeToYoneda
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) [P.RespectsIso]
    (P' : MorphismProperty ((BigFppfOver B S' hS')ᵒᵖ ⥤ Type u)) [P'.RespectsIso]
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B W hW F)
    (hcomp : P (OverShriek.relocalizeToYoneda h F) →
      P' (OverShriek.relocalizeToYoneda (h ≫ g) F))
    (hP : P ((spacesOverSmallerBaseFunctor B W S hW hS h).obj ⟨F, hF⟩).1.hom) :
    P' ((spacesOverSmallerBaseFunctor B W S' hW hS' (h ≫ g)).obj ⟨F, hF⟩).1.hom := by
  refine (MorphismProperty.cancel_left_of_respectsIso P'
    ((spacesOverSmallerBaseFunctorForgetIso B W S' hW hS' (h ≫ g)).inv.app ⟨F, hF⟩) _).1 ?_
  rw [Space.relocalizeToYoneda_eq B W S' hW hS' (h ≫ g) ⟨F, hF⟩]
  refine hcomp ?_
  rw [← Space.relocalizeToYoneda_eq B W S hW hS h ⟨F, hF⟩]
  exact (MorphismProperty.cancel_left_of_respectsIso P
    ((spacesOverSmallerBaseFunctorForgetIso B W S hW hS h).inv.app ⟨F, hF⟩) _).2 hP

/-- **Quasi-compactness of the structural morphism of a lower-shriek extension passes to a larger
base.** The structural morphism over `S'` is the image under `Λ_g` of the structural morphism
over `S`, by `CategoryTheory.OverShriek.relocalizeToYoneda_comp_relocalizeYonedaComp`. -/
theorem Space.isQuasiCompact_relocalizeToYoneda_comp
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B W hW F)
    (hqc : Space.IsQuasiCompact B S hS (OverShriek.relocalizeToYoneda h F)) :
    Space.IsQuasiCompact B S' hS' (OverShriek.relocalizeToYoneda (h ≫ g) F) := by
  have : (Space.quasiCompactPresheafProperty B S' hS').RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact relocalizeToYoneda_comp_of_map B W S hW hS h S' hS' g
    (Space.quasiCompactPresheafProperty B S' hS') F
    (Space.isQuasiCompact_relocalizeMap B S S' hS hS' g
      (isAlgebraicSpace_viewOver B W S hW hS h F hF)
      (isAlgebraicSpace_yoneda B S hS (Over.mk h)) _ hqc)

/-- **Quasi-separatedness of the structural morphism of a lower-shriek extension passes to a
larger base.** -/
theorem Space.isQuasiSeparated_relocalizeToYoneda_comp
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B W hW F)
    (hqs : Space.IsQuasiSeparated B S hS (OverShriek.relocalizeToYoneda h F)) :
    Space.IsQuasiSeparated B S' hS' (OverShriek.relocalizeToYoneda (h ≫ g) F) := by
  have : MorphismProperty.RespectsIso (@Space.IsQuasiSeparated B S' hS') :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := (Space.quasiCompactPresheafProperty B S' hS').diagonal)
  exact relocalizeToYoneda_comp_of_map B W S hW hS h S' hS' g
    (@Space.IsQuasiSeparated B S' hS') F
    (Space.isQuasiSeparated_relocalizeMap B S S' hS hS' g
      (isAlgebraicSpace_viewOver B W S hW hS h F hF)
      (isAlgebraicSpace_yoneda B S hS (Over.mk h)) _ hqs)

/-- **Stacks 03HE for the image of Stacks 04SG's forward functor passes to a larger base.** An
algebraic space over `W`, viewed over `S` along `h` and over `S'` along a factorization `h ≫ g`,
has quasi-compact structural morphism over `S'` as soon as it has one over `S`. -/
theorem Space.isQuasiCompact_spacesOverSmallerBaseFunctor
    (u : B.obj hW ⟶ B.obj hS') (hu : h ≫ g = u)
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B W hW F)
    (hqc : Space.IsQuasiCompact B S hS
      (((spacesOverSmallerBaseFunctor B W S hW hS h).obj ⟨F, hF⟩).1.hom)) :
    Space.IsQuasiCompact B S' hS'
      (((spacesOverSmallerBaseFunctor B W S' hW hS' u).obj ⟨F, hF⟩).1.hom) := by
  subst hu
  have : (Space.quasiCompactPresheafProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : (Space.quasiCompactPresheafProperty B S' hS').RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact spacesOverSmallerBaseFunctor_of_relocalizeToYoneda B W S hW hS h S' hS' g
    (Space.quasiCompactPresheafProperty B S hS) (Space.quasiCompactPresheafProperty B S' hS')
    F hF (Space.isQuasiCompact_relocalizeToYoneda_comp B W S hW hS h S' hS' g F hF) hqc

/-- **Stacks 03HL part (3) for the image of Stacks 04SG's forward functor passes to a larger
base.** -/
theorem Space.isQuasiSeparated_spacesOverSmallerBaseFunctor
    (u : B.obj hW ⟶ B.obj hS') (hu : h ≫ g = u)
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B W hW F)
    (hqs : Space.IsQuasiSeparated B S hS
      (((spacesOverSmallerBaseFunctor B W S hW hS h).obj ⟨F, hF⟩).1.hom)) :
    Space.IsQuasiSeparated B S' hS'
      (((spacesOverSmallerBaseFunctor B W S' hW hS' u).obj ⟨F, hF⟩).1.hom) := by
  subst hu
  have : MorphismProperty.RespectsIso (@Space.IsQuasiSeparated B S hS) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := (Space.quasiCompactPresheafProperty B S hS).diagonal)
  have : MorphismProperty.RespectsIso (@Space.IsQuasiSeparated B S' hS') :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := (Space.quasiCompactPresheafProperty B S' hS').diagonal)
  exact spacesOverSmallerBaseFunctor_of_relocalizeToYoneda B W S hW hS h S' hS' g
    (@Space.IsQuasiSeparated B S hS) (@Space.IsQuasiSeparated B S' hS')
    F hF (Space.isQuasiSeparated_relocalizeToYoneda_comp B W S hW hS h S' hS' g F hF) hqs

end ChangeOfBase

end AlgebraicGeometry

end
