module

public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange

/-!
# Recognizing a blowup from an open cover of the base

Let `X` be a scheme, `I` a quasi-coherent sheaf of ideals on `X` and `f : Y ⟶ X` a morphism.
This file proves that `f` is the blowing up of `X` in `I` as soon as it is so locally on `X`:
if the base change of `f` along every member of an open cover of `X` is isomorphic, over that
member, to the base change of the blowup morphism, then `f` is isomorphic to the blowup morphism
over `X`.

This is the descent step of the last assertion of Stacks tag 0GTY, where the morphism of the tag
is identified over a quasi-compact open with the blowing up of that open in a glued centre; the
identification is available over each member of a finite cover by affine chart domains, and has
to be assembled.

## Main results

* `AlgebraicGeometry.blowUp_hom_ext`: two morphisms into a blowup over the same morphism to the
  base agree, once the inverse image of the centre along that morphism is an effective Cartier
  divisor.
* `AlgebraicGeometry.isEffectiveCartierDivisor_comap_pullbackHom`: the inverse image of the
  centre along a base change of the blowup morphism is an effective Cartier divisor.
* `AlgebraicGeometry.nonempty_overIso_blowUpToBase_of_openCover`: **the descent statement.**

## Implementation notes

The local isomorphisms are turned into morphisms from the members of the induced cover of `Y` to
the blowup; they agree on overlaps by `AlgebraicGeometry.blowUp_hom_ext`, because the inverse
image of the centre on an overlap is a flat inverse image of the exceptional divisor and hence an
effective Cartier divisor.  `AlgebraicGeometry.Scheme.Cover.glueMorphisms` then produces the
global morphism, and `CategoryTheory.MorphismProperty.of_zeroHypercover_target` for the property
of being an isomorphism — Zariski local on the target — finishes.

The index type of `CategoryTheory.Precoverage.ZeroHypercover.pullback₁` is the index type of the
cover it is formed from, but only up to unfolding a structure projection that this module system
does not expose; so the morphisms and the gluing data are typed over the index type of the
induced cover where the gluing API demands it, and over the index type of the original cover
where the pullback squares are formed, with the two reconciled only by `exact`.

## References

* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Two morphisms into a blowup over the same morphism to the base agree**, as soon as the
inverse image of the centre along that morphism is an effective Cartier divisor: the blowup is
terminal among such morphisms. -/
theorem blowUp_hom_ext {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X)
    (hf : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap f))
    (g h : Y ⟶ blowUp I) (hg : g ≫ blowUpToBase I = f) (hh : h ≫ blowUpToBase I = f) :
    g = h := by
  obtain ⟨hB, ⟨terminal⟩⟩ := Stacks.Blowup.isTerminal_blowUp I
  let Z : Stacks.Blowup.CartierOver I := ⟨Over.mk f, hf⟩
  let B : Stacks.Blowup.CartierOver I := ⟨Over.mk (blowUpToBase I), hB⟩
  let g' : Z ⟶ B := ⟨Over.homMk g hg⟩
  let h' : Z ⟶ B := ⟨Over.homMk h hh⟩
  exact congrArg (fun k : Z ⟶ B => k.hom.left) (terminal.hom_ext g' h')

/-- The inverse image of the centre along a base change of the blowup morphism is an effective
Cartier divisor: the exceptional divisor pulls back along a flat morphism. -/
theorem isEffectiveCartierDivisor_comap_pullbackHom {X : Scheme.{u}} (I : X.IdealSheafData)
    (𝒰 : X.OpenCover) (i : 𝒰.I₀) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (I.comap (pullback.snd (blowUpToBase I) (𝒰.f i) ≫ 𝒰.f i)) := by
  have hp : Flat (pullback.fst (blowUpToBase I) (𝒰.f i)) := inferInstance
  have hP := Stacks.Divisors.isPullbackDefined_of_flat
    (pullback.fst (blowUpToBase I) (𝒰.f i)) (I.comap (blowUpToBase I))
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I)
  rw [← pullback.condition, Scheme.IdealSheafData.comap_comp]
  exact hP

/-- **A morphism to the base which is a blowup locally on the base is the blowup.**  Let `I` be a
quasi-coherent sheaf of ideals on `X` and `f : Y ⟶ X` a morphism whose base change along every
member of an open cover of `X` is isomorphic, over that member, to the corresponding base change
of the blowup of `X` in `I`.  Then `f` is isomorphic to the blowup morphism over `X`.

The local isomorphisms give morphisms from the members of the induced cover of `Y` to the blowup
over `X`; they agree on overlaps because two morphisms into a blowup over the same morphism to
the base agree once the inverse image of the centre is an effective Cartier divisor
(`AlgebraicGeometry.blowUp_hom_ext`), which it is on each overlap, being a flat inverse image of
the exceptional divisor.  So they glue to a morphism `g : Y ⟶ blowUp I` over `X`, and `g` is an
isomorphism because being an isomorphism is Zariski local on the target and the base change of
`g` along each member of the induced cover of the blowup is one of the local isomorphisms. -/
theorem nonempty_overIso_blowUpToBase_of_openCover {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (f : Y ⟶ X) (𝒰 : X.OpenCover)
    (h : ∀ i, Nonempty (Over.mk (pullback.snd f (𝒰.f i)) ≅
      Over.mk (pullback.snd (blowUpToBase I) (𝒰.f i)))) :
    Nonempty (Over.mk f ≅ Over.mk (blowUpToBase I)) := by
  classical
  set e := fun i => Classical.choice (h i) with he
  have heIso (i : 𝒰.I₀) : IsIso (e i).hom.left := by
    show IsIso ((Over.forget _).map (e i).hom)
    infer_instance
  have hew (i : 𝒰.I₀) :
      (e i).hom.left ≫ pullback.snd (blowUpToBase I) (𝒰.f i) = pullback.snd f (𝒰.f i) :=
    (e i).hom.w
  have hmap (i : 𝒰.I₀) : pullback.fst f (𝒰.f i) ≫ f
      = (e i).hom.left ≫ (pullback.snd (blowUpToBase I) (𝒰.f i) ≫ 𝒰.f i) := by
    rw [← Category.assoc, hew i, ← pullback.condition]
  have hCart (i : 𝒰.I₀) : Stacks.Divisors.IsEffectiveCartierDivisor
      (I.comap (pullback.fst f (𝒰.f i) ≫ f)) := by
    have hflat : Flat (e i).hom.left := by
      have := heIso i
      infer_instance
    have hp := Stacks.Divisors.isPullbackDefined_of_flat (e i).hom.left
      (I.comap (pullback.snd (blowUpToBase I) (𝒰.f i) ≫ 𝒰.f i))
      (isEffectiveCartierDivisor_comap_pullbackHom I 𝒰 i)
    rw [hmap i, Scheme.IdealSheafData.comap_comp]
    exact hp
  set gLocal : (i : (𝒰.pullback₁ f).I₀) → (𝒰.pullback₁ f).X i ⟶ blowUp I :=
    fun i => (e i).hom.left ≫ pullback.fst (blowUpToBase I) (𝒰.f i) with hgL
  have hgLocal (i : (𝒰.pullback₁ f).I₀) :
      gLocal i ≫ blowUpToBase I = (𝒰.pullback₁ f).f i ≫ f := by
    show ((e i).hom.left ≫ pullback.fst (blowUpToBase I) (𝒰.f i)) ≫ blowUpToBase I
      = pullback.fst f (𝒰.f i) ≫ f
    rw [hmap i, Category.assoc, pullback.condition]
  have hcompat (i j : (𝒰.pullback₁ f).I₀) :
      pullback.fst ((𝒰.pullback₁ f).f i) ((𝒰.pullback₁ f).f j) ≫ gLocal i
        = pullback.snd ((𝒰.pullback₁ f).f i) ((𝒰.pullback₁ f).f j) ≫ gLocal j := by
    set pi := pullback.fst ((𝒰.pullback₁ f).f i) ((𝒰.pullback₁ f).f j) with hpi
    set pj := pullback.snd ((𝒰.pullback₁ f).f i) ((𝒰.pullback₁ f).f j) with hpj
    have hp := Stacks.Divisors.isPullbackDefined_of_flat pi
      (I.comap ((𝒰.pullback₁ f).f i ≫ f)) (hCart i)
    have hCartOverlap : Stacks.Divisors.IsEffectiveCartierDivisor
        (I.comap ((pi ≫ (𝒰.pullback₁ f).f i) ≫ f)) := by
      simpa only [Category.assoc, Scheme.IdealSheafData.comap_comp] using hp
    refine blowUp_hom_ext I _ hCartOverlap _ _ ?_ ?_
    · rw [Category.assoc, hgLocal i, Category.assoc]
    · rw [Category.assoc, hgLocal j, hpi, hpj, ← Category.assoc, pullback.condition,
        Category.assoc]
  set g := Scheme.Cover.glueMorphisms (𝒰.pullback₁ f) gLocal hcompat with hgdef
  have hι (i : (𝒰.pullback₁ f).I₀) : (𝒰.pullback₁ f).f i ≫ g = gLocal i :=
    Scheme.Cover.ι_glueMorphisms (𝒰.pullback₁ f) gLocal hcompat i
  have hgb : g ≫ blowUpToBase I = f := by
    refine Scheme.Cover.hom_ext (𝒰.pullback₁ f) _ _ fun i => ?_
    rw [← Category.assoc, hι i, hgLocal i]
  have hPB (i : 𝒰.I₀) : IsPullback (pullback.fst f (𝒰.f i)) (e i).hom.left g
      (pullback.fst (blowUpToBase I) (𝒰.f i)) := by
    refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback (blowUpToBase I) (𝒰.f i))
    · show IsPullback (pullback.fst f (𝒰.f i))
        ((e i).hom.left ≫ pullback.snd (blowUpToBase I) (𝒰.f i)) (g ≫ blowUpToBase I) (𝒰.f i)
      rw [hgb, hew i]
      exact IsPullback.of_hasPullback f (𝒰.f i)
    · exact hι i
  have hkey : ∀ i : 𝒰.I₀, MorphismProperty.isomorphisms Scheme
      (pullback.snd g (pullback.fst (blowUpToBase I) (𝒰.f i))) := by
    intro i
    have hi : IsIso ((hPB i).isoPullback.hom ≫
        pullback.snd g (pullback.fst (blowUpToBase I) (𝒰.f i))) := by
      rw [(hPB i).isoPullback_hom_snd]
      exact heIso i
    exact IsIso.of_isIso_comp_left (hPB i).isoPullback.hom _
  have hgIso : IsIso g :=
    MorphismProperty.of_zeroHypercover_target (P := .isomorphisms Scheme)
      (𝒰.pullback₁ (blowUpToBase I)) hkey
  exact ⟨Over.isoMk (asIso g) hgb⟩

end AlgebraicGeometry

end
