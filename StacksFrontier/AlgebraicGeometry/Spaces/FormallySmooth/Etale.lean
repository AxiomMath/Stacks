module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.EtaleIffFormallyEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Unramified
public import Mathlib.CategoryTheory.MorphismProperty.Representable

/-!
# Étale representable transformations are formally étale

An étale representable transformation of set-valued functors on the big fppf site over a
scheme has exactly one lift in every affine square-zero infinitesimal lifting problem.

## Main results

* `AlgebraicGeometry.Space.formallyEtale_of_etale`: an étale representable transformation is
  formally étale.
* `AlgebraicGeometry.Space.formallyEtale_comp_of_etale`: an étale transformation followed by a
  formally étale one is formally étale.
* `AlgebraicGeometry.Space.formallySmooth_of_etale`: an étale representable transformation is
  formally smooth.
* `AlgebraicGeometry.Space.formallySmooth_comp_of_etale`: an étale transformation followed by a
  formally smooth one is formally smooth.

## References

* [Stacks Project, Tag 02HG](https://stacks.math.columbia.edu/tag/02HG)
* [Stacks Project, Tag 02HM](https://stacks.math.columbia.edu/tag/02HM)
* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 049T](https://stacks.math.columbia.edu/tag/049T)
* [Stacks Project, Tag 04AL](https://stacks.math.columbia.edu/tag/04AL)
* [Stacks Project, Tag 04CY](https://stacks.math.columbia.edu/tag/04CY)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

/-- An étale representable transformation on the big fppf site is formally étale. -/
@[stacks 04AL "etale_implies_formally_etale", ega "IV 17.1.3" "(i) open immersion"]
public theorem formallyEtale_of_etale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G)
    (ha : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    FormallyEtale a := by
  intro T T' hT hT' i hi x y hxy
  obtain ⟨P, p, q, hPB, t, htp, hqx, e, he⟩ :=
    exists_representing_scheme_lift_equiv B S hS a ha.1 T T' i x y hxy
  have hpEt : Etale ((BigFppfOver.toScheme B S hS).map p) :=
    ha.2 (g := yonedaEquiv.symm y) (fst := q) (snd := p) hPB
  have hpFormal : _root_.AlgebraicGeometry.FormallyEtale
      ((BigFppfOver.toScheme B S hS).map p) :=
    ((_root_.AlgebraicGeometry.etale_iff_locallyOfFinitePresentation_and_formallyEtale
      ((BigFppfOver.toScheme B S hS).map p)).mp hpEt).2
  set f : (BigFppfOver.toScheme B S hS).obj T ⟶ (BigFppfOver.toScheme B S hS).obj P :=
    (BigFppfOver.toScheme B S hS).map t with hf
  have hcomm : f ≫ (BigFppfOver.toScheme B S hS).map p =
      (BigFppfOver.toScheme B S hS).map i := by rw [hf, ← Functor.map_comp, htp]
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hT
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj T') := hT'
  have hi' : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map i) := hi
  obtain ⟨h, hh, huniq⟩ := hpFormal ((BigFppfOver.toScheme B S hS).map i) hi'
    ((BigFppfOver.toScheme B S hS).map (𝟙 T')) f hcomm
  set hB : (BigFppfOver.forget B S hS).obj T' ⟶ (BigFppfOver.forget B S hS).obj P :=
    B.inclusion.preimage h with hhB
  have hBp : hB ≫ (BigFppfOver.forget B S hS).map p = 𝟙 _ := by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, hhB, B.inclusion.map_preimage]
    simpa using hh.2
  have hOver : hB ≫ P.hom = T'.hom := by
    conv_lhs => rw [← p.w, ← Category.assoc]
    show (hB ≫ (BigFppfOver.forget B S hS).map p) ≫ T'.hom = _
    rw [hBp]
    simp
  set s : T' ⟶ P := Over.homMk hB hOver with hs
  have hs_map : (BigFppfOver.toScheme B S hS).map s = h := by
    show B.inclusion.map hB = h
    rw [hhB, B.inclusion.map_preimage]
  have inj : ∀ {X Y : BigFppfOver B S hS} {u v : X ⟶ Y},
      (BigFppfOver.toScheme B S hS).map u = (BigFppfOver.toScheme B S hS).map v → u = v :=
    fun h => (BigFppfOver.forget B S hS).map_injective (B.inclusion.map_injective h)
  have hsp : s ≫ p = 𝟙 T' :=
    (BigFppfOver.forget B S hS).map_injective hBp
  have hit : i ≫ s = t := inj <| by
    rw [Functor.map_comp, hs_map]
    exact hh.1
  refine ⟨(e.symm ⟨s, hsp, hit⟩).val, (e.symm ⟨s, hsp, hit⟩).property, ?_⟩
  intro z' hz'
  have hs' : (e ⟨z', hz'⟩).val = s := inj <| by
    rw [hs_map]
    refine huniq _ ⟨?_, ?_⟩
    · rw [← Functor.map_comp, (e ⟨z', hz'⟩).property.2]
    · rw [← Functor.map_comp, (e ⟨z', hz'⟩).property.1]
  exact congrArg Subtype.val
    (e.injective ((Subtype.ext hs').trans (e.apply_symm_apply ⟨s, hsp, hit⟩).symm))

/-- An étale transformation followed by a formally étale transformation is formally étale. -/
@[stacks 04CY "compose_formally_etale"]
public theorem formallyEtale_comp_of_etale
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : F ⟶ G} {b : G ⟶ H}
    (ha : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : FormallyEtale b) :
    FormallyEtale (a ≫ b) :=
  formallyEtale_comp (formallyEtale_of_etale B S hS a ha) hb

/-- An étale representable transformation on the big fppf site is formally smooth. -/
@[stacks 04AL "etale_implies_formally_smooth", ega "IV 17.1.3" "(i) open immersion"]
public theorem formallySmooth_of_etale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G)
    (ha : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    FormallySmooth a := fun T T' hT hT' i hi x y hxy =>
  (formallyEtale_of_etale B S hS a ha T T' hT hT' i hi x y hxy).exists

/-- An étale transformation followed by a formally smooth transformation is formally smooth. -/
@[stacks 04CY "compose_formally_smooth"]
public theorem formallySmooth_comp_of_etale
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : F ⟶ G} {b : G ⟶ H}
    (ha : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : FormallySmooth b) :
    FormallySmooth (a ≫ b) :=
  FormallySmooth.comp a b (formallySmooth_of_etale B S hS a ha) hb

end AlgebraicGeometry.Space

end
