module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings

/-!
# Cartesian squares of algebraic spaces descend along surjective étale morphisms

Let `S` be a scheme and consider a commutative diagram of algebraic spaces over `S` with rows
`A ⟶ C ⟶ E` and `B ⟶ D ⟶ F` and vertical maps `A ⟶ B`, `C ⟶ D` and `E ⟶ F`. Assume that the
square `A, B, C, D` and the outer rectangle `A, B, E, F` — whose horizontal maps are the
composites `A ⟶ C ⟶ E` and `B ⟶ D ⟶ F` — are both cartesian. If `B ⟶ D` is surjective and
étale, then the square `C, D, E, F` is cartesian as well.

The conclusion does not follow from the two hypotheses alone: if `B` is empty then both
hypotheses hold for every choice of `C, D, E, F`. What a surjective étale `B ⟶ D` supplies is
that every section of `D` lifts to `B` after passing to a covering of the big fppf site; the
sheaf condition for the algebraic spaces involved then assembles the resulting local sections
of `C` into a global one.

## Main results

* `AlgebraicGeometry.Space.isPullback_right_of_isPullback_of_surjective_etale`:
  **Stacks 07VZ**.

## Implementation notes

The ambient big fppf site is called `B₀`, leaving `B` for the lower-left algebraic space of
the diagram as in the source. Fibre products of algebraic spaces are presheaf fibre products,
so cartesianness is `CategoryTheory.IsPullback` in the category of presheaves on the site, and
it is checked objectwise by `CategoryTheory.isPullback_of_existsUnique_app`.

## References

* [Stacks Project, Tag 07VZ](https://stacks.math.columbia.edu/tag/07VZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B₀ : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B₀.Contains S)
  {A B C D E F : (BigFppfOver B₀ S hS)ᵒᵖ ⥤ Type u}
  {aC : A ⟶ C} {aB : A ⟶ B} {cD : C ⟶ D} {bD : B ⟶ D}
  {cE : C ⟶ E} {dF : D ⟶ F} {eF : E ⟶ F}

/-- The underlying presheaf of an algebraic space is a sheaf for the topology on the site. -/
private theorem isSheaf_of_isAlgebraicSpace {X : (BigFppfOver B₀ S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B₀ S hS X) :
    Presieve.IsSheaf (BigFppfOver.topology B₀ S hS) X :=
  (isSheaf_iff_isSheaf_of_type _ _).1 hX.isSheaf

/-- Two sections of `C` over the same object of the site which have the same image in `E` and
the same image in `D` are equal, once the square `A, B, C, D` and the outer rectangle
`A, B, E, F` are cartesian and every section of `D` lifts to `B` locally. -/
private theorem sections_eq_of_isPullback_of_isLocallySurjective
    (hC : IsAlgebraicSpace B₀ S hS C)
    (hleft : IsPullback aC aB cD bD)
    (houter : IsPullback (aC ≫ cE) aB eF (bD ≫ dF))
    (hloc : Presheaf.IsLocallySurjective (BigFppfOver.topology B₀ S hS) bD)
    (T : BigFppfOver B₀ S hS) (c₁ c₂ : C.obj (Opposite.op T))
    (hcE : cE.app (Opposite.op T) c₁ = cE.app (Opposite.op T) c₂)
    (hcD : cD.app (Opposite.op T) c₁ = cD.app (Opposite.op T) c₂) :
    c₁ = c₂ := by
  have hR := hloc.imageSieve_mem (J := BigFppfOver.topology B₀ S hS)
    (f := bD) (cD.app (Opposite.op T) c₁)
  refine (isSheaf_of_isAlgebraicSpace B₀ S hS hC _ hR).isSeparatedFor.ext fun Y g hg => ?_
  obtain ⟨β, hβ⟩ := hg
  have h₁ : cD.app (Opposite.op Y) (C.map g.op c₁) = bD.app (Opposite.op Y) β :=
    (NatTrans.naturality_apply cD g.op c₁).trans hβ.symm
  have h₂ : cD.app (Opposite.op Y) (C.map g.op c₂) = bD.app (Opposite.op Y) β := by
    refine (NatTrans.naturality_apply cD g.op c₂).trans ?_
    rw [← hcD]
    exact hβ.symm
  obtain ⟨a₁, ha₁C, ha₁B⟩ :=
    Types.exists_of_isPullback (hleft.app (Opposite.op Y)) _ _ h₁
  obtain ⟨a₂, ha₂C, ha₂B⟩ :=
    Types.exists_of_isPullback (hleft.app (Opposite.op Y)) _ _ h₂
  have hE₁ : cE.app (Opposite.op Y) (aC.app (Opposite.op Y) a₁) =
      cE.app (Opposite.op Y) (aC.app (Opposite.op Y) a₂) := by
    rw [ha₁C, ha₂C, NatTrans.naturality_apply, NatTrans.naturality_apply, hcE]
  have ha : a₁ = a₂ := by
    refine Types.ext_of_isPullback (houter.app (Opposite.op Y)) ?_ ?_
    · simpa only [NatTrans.comp_app, types_comp_apply] using hE₁
    · rw [ha₁B, ha₂B]
  rw [← ha₁C, ← ha₂C, ha]

/-- A section of `E` and a section of `D` over the same object of the site with the same image
in `F` come from a section of `C`, once the square `A, B, C, D` and the outer rectangle
`A, B, E, F` are cartesian and every section of `D` lifts to `B` locally. -/
private theorem exists_section_of_isPullback_of_isLocallySurjective
    (hC : IsAlgebraicSpace B₀ S hS C) (hD : IsAlgebraicSpace B₀ S hS D)
    (hE : IsAlgebraicSpace B₀ S hS E)
    (hleft : IsPullback aC aB cD bD)
    (houter : IsPullback (aC ≫ cE) aB eF (bD ≫ dF))
    (hloc : Presheaf.IsLocallySurjective (BigFppfOver.topology B₀ S hS) bD)
    (T : BigFppfOver B₀ S hS) (e : E.obj (Opposite.op T)) (d : D.obj (Opposite.op T))
    (hed : eF.app (Opposite.op T) e = dF.app (Opposite.op T) d) :
    ∃ c : C.obj (Opposite.op T),
      cE.app (Opposite.op T) c = e ∧ cD.app (Opposite.op T) c = d := by
  classical
  have hR := hloc.imageSieve_mem (J := BigFppfOver.topology B₀ S hS) (f := bD) d
  -- Over every arrow of the sieve along which `d` lifts to `B`, the pair `(e, d)` comes from
  -- a section of `C`, obtained from the cartesian outer rectangle.
  have hlocal : ∀ (Y : BigFppfOver B₀ S hS) (g : Y ⟶ T),
      (Presheaf.imageSieve bD d).arrows g →
      ∃ c : C.obj (Opposite.op Y),
        cE.app (Opposite.op Y) c = E.map g.op e ∧ cD.app (Opposite.op Y) c = D.map g.op d := by
    intro Y g hg
    obtain ⟨β, hβ⟩ := hg
    have hw : eF.app (Opposite.op Y) (E.map g.op e) = (bD ≫ dF).app (Opposite.op Y) β := by
      have h₀ : eF.app (Opposite.op Y) (E.map g.op e) = F.map g.op (dF.app (Opposite.op T) d) := by
        rw [NatTrans.naturality_apply, hed]
      refine h₀.trans ?_
      rw [← NatTrans.naturality_apply dF g.op d, ← hβ]
      simp only [NatTrans.comp_app, types_comp_apply]
    obtain ⟨a, haE, haB⟩ :=
      Types.exists_of_isPullback (houter.app (Opposite.op Y)) (E.map g.op e) β hw
    refine ⟨aC.app (Opposite.op Y) a, ?_, ?_⟩
    · simpa only [NatTrans.comp_app, types_comp_apply] using haE
    · have hwl := congrFun (congrArg (fun m => m.app (Opposite.op Y)) hleft.w) a
      simp only [NatTrans.comp_app, types_comp_apply] at hwl
      rw [hwl, haB, hβ]
  choose cloc hcloc₁ hcloc₂ using hlocal
  -- These local sections are compatible, because their images in `E` and `D` are restrictions.
  have hx : ∀ ⦃Y₁ Y₂ W : BigFppfOver B₀ S hS⦄ (g₁ : W ⟶ Y₁) (g₂ : W ⟶ Y₂)
      ⦃f₁ : Y₁ ⟶ T⦄ ⦃f₂ : Y₂ ⟶ T⦄ (h₁ : (Presheaf.imageSieve bD d).arrows f₁)
      (h₂ : (Presheaf.imageSieve bD d).arrows f₂), g₁ ≫ f₁ = g₂ ≫ f₂ →
      C.map g₁.op (cloc Y₁ f₁ h₁) = C.map g₂.op (cloc Y₂ f₂ h₂) := by
    intro Y₁ Y₂ W g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    refine sections_eq_of_isPullback_of_isLocallySurjective B₀ S hS hC hleft houter hloc W _ _
      ?_ ?_ <;>
    simp only [NatTrans.naturality_apply, hcloc₁, hcloc₂, ← Functor.map_comp_apply, ← op_comp,
      hcomm]
  obtain ⟨c, hc, -⟩ :=
    isSheaf_of_isAlgebraicSpace B₀ S hS hC _ hR (fun _ g hg => cloc _ g hg) hx
  refine ⟨c, ?_, ?_⟩
  · refine (isSheaf_of_isAlgebraicSpace B₀ S hS hE _ hR).isSeparatedFor.ext fun Y g hg => ?_
    rw [← NatTrans.naturality_apply cE g.op, hc g hg]
    exact hcloc₁ Y g hg
  · refine (isSheaf_of_isAlgebraicSpace B₀ S hS hD _ hR).isSeparatedFor.ext fun Y g hg => ?_
    rw [← NatTrans.naturality_apply cD g.op, hc g hg]
    exact hcloc₂ Y g hg

/-- **Stacks 07VZ.** Let `S` be a scheme and let `A, B, C, D, E, F` be algebraic spaces over `S`
sitting in a commutative diagram with rows `A ⟶ C ⟶ E` and `B ⟶ D ⟶ F` and vertical maps
`A ⟶ B`, `C ⟶ D`, `E ⟶ F`. If the square `A, B, C, D` and the outer rectangle `A, B, E, F` are
cartesian and `B ⟶ D` is surjective and étale, then the square `C, D, E, F` is cartesian. -/
@[stacks 07VZ]
theorem isPullback_right_of_isPullback_of_surjective_etale
    (_hA : IsAlgebraicSpace B₀ S hS A) (hB : IsAlgebraicSpace B₀ S hS B)
    (hC : IsAlgebraicSpace B₀ S hS C) (hD : IsAlgebraicSpace B₀ S hS D)
    (hE : IsAlgebraicSpace B₀ S hS E) (_hF : IsAlgebraicSpace B₀ S hS F)
    (hcomm : cE ≫ eF = cD ≫ dF)
    (hleft : IsPullback aC aB cD bD)
    (houter : IsPullback (aC ≫ cE) aB eF (bD ≫ dF))
    (hsurj : IsSurjective B₀ S hS bD) (hetale : IsEtale B₀ S hS bD) :
    IsPullback cE cD eF dF := by
  have hloc : Presheaf.IsLocallySurjective (BigFppfOver.topology B₀ S hS) bD :=
    isLocallySurjective_of_surjective_flat_locallyOfFinitePresentation B₀ S hS hB hD bD hsurj
      (isFlat_of_isEtale B₀ S hS hetale)
      (isLocallyOfFinitePresentation_of_isEtale B₀ S hS hetale)
  refine isPullback_of_existsUnique_app hcomm fun V e d hed => ?_
  obtain ⟨T⟩ := V
  obtain ⟨c, hc₁, hc₂⟩ :=
    exists_section_of_isPullback_of_isLocallySurjective B₀ S hS hC hD hE hleft houter hloc T e d
      hed
  refine ⟨c, ⟨hc₁, hc₂⟩, fun c' hc' => ?_⟩
  exact sections_eq_of_isPullback_of_isLocallySurjective B₀ S hS hC hleft houter hloc T c' c
    (hc'.1.trans hc₁.symm) (hc'.2.trans hc₂.symm)

end AlgebraicGeometry.Space

end
