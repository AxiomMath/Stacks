module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple

/-!
# Relative ampleness of an invertible module over a scheme

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `L` be an invertible `𝒪_X`-module and assume that `Y` is a scheme. Then `L` is
ample relative to `f` in the sense of algebraic spaces, Stacks 0D31, if and only if `X` is a
scheme and `L` is ample relative to `f` in the sense of schemes, Stacks 01VH. In particular
relative ampleness forces the source to be a scheme as soon as the target is one.

A scheme over the base is an object `U` of `AlgebraicGeometry.BigFppfOver B S hS`, and an
algebraic space *is* a scheme exactly when its underlying presheaf is representable by such an
object, that is when `CategoryTheory.Functor.IsRepresentable` holds for it. An invertible
module on the algebraic space represented by `U` is read on the scheme `U` by
`AlgebraicGeometry.Space.baseChangeModule`, which is the module `𝒪_X`-pullback of Stacks 03LU
followed by restriction to the Zariski site of `U`; that is the module to which Stacks 01VH
applies.

## Main results

* `AlgebraicGeometry.Space.IsRelativelyAmple.isRepresentable`: a morphism of algebraic spaces
  which carries a relatively ample module and whose target is a scheme has a scheme as source.
* `AlgebraicGeometry.Space.IsRelativelyAmple.exists_scheme`: clause (1) of Stacks 0D32 implies
  clause (2).
* `AlgebraicGeometry.Space.isRelativelyAmple_of_exists_scheme`: clause (2) of Stacks 0D32
  implies clause (1).
* `AlgebraicGeometry.Space.isRelativelyAmple_iff_exists_scheme`: the equivalence of the two
  clauses of Stacks 0D32.

## References

* [Stacks Project, Tag 0D32](https://stacks.math.columbia.edu/tag/0D32)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
* [Stacks Project, Tag 03KC](https://stacks.math.columbia.edu/tag/03KC)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- If a module is ample relative to `f : X ⟶ Y` and the algebraic space `Y` is a scheme, then
the algebraic space `X` is a scheme. -/
@[stacks 0D32 "the source is a scheme"]
theorem IsRelativelyAmple.isRepresentable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {L : Modules.{u, u} B S hS X.1 X.2} (h : IsRelativelyAmple B S hS f L)
    [Y.1.IsRepresentable] : X.1.IsRepresentable :=
  Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable f.hom h.1

/-- **Stacks 0D32, clause (1) implies clause (2).** Let `f : X ⟶ Y` be a morphism of algebraic
spaces whose target is the scheme `V`, and let `L` be ample relative to `f` in the sense of
Stacks 0D31. Then `X` is a scheme `U`, and the restriction of `L` to `U` is invertible and ample
relative to the morphism `U ⟶ V` induced by `f`, in the sense of Stacks 01VH. -/
theorem IsRelativelyAmple.exists_scheme {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {L : Modules.{u, u} B S hS X.1 X.2} (h : IsRelativelyAmple B S hS f L)
    (V : BigFppfOver B S hS) (eY : Y.1 ≅ yoneda.obj V) :
    ∃ (U : BigFppfOver B S hS) (eX : yoneda.obj U ≅ X.1)
      (hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS L U eX.hom)),
      @Stacks.RelativeAmple.IsRelativelyAmple _ _
        ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (eX.hom ≫ f.hom ≫ eY.hom)))
        (baseChangeModule B S hS L U eX.hom) hL := by
  have hY : Y.1.IsRepresentable := isRepresentable_of_natIso (yoneda.obj V) eY.symm
  have hX : X.1.IsRepresentable := h.isRepresentable
  refine ⟨X.1.reprX, X.1.reprW, ?_⟩
  have hmapq : yoneda.map (yoneda.preimage (X.1.reprW.hom ≫ f.hom ≫ eY.hom)) =
      X.1.reprW.hom ≫ f.hom ≫ eY.hom := yoneda.map_preimage _
  refine h.2 V X.1.reprX eY.inv X.1.reprW.hom _ (IsPullback.of_horiz_isIso ⟨?_⟩)
  rw [hmapq]
  simp

/-- **Stacks 0D32, clause (2) implies clause (1).** Let `f : X ⟶ Y` be a morphism of algebraic
spaces whose target is the scheme `V`, let `L` be an invertible `𝒪_X`-module, and suppose that
`X` is a scheme `U` over which `L` is invertible and ample relative to the morphism `U ⟶ V`
induced by `f`, in the sense of Stacks 01VH. Then `L` is ample relative to `f` in the sense of
Stacks 0D31. -/
theorem isRelativelyAmple_of_exists_scheme {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (L : Modules.{u, u} B S hS X.1 X.2)
    (hLinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (V : BigFppfOver B S hS) (eY : Y.1 ≅ yoneda.obj V)
    (h : ∃ (U : BigFppfOver B S hS) (eX : yoneda.obj U ≅ X.1)
      (hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS L U eX.hom)),
      @Stacks.RelativeAmple.IsRelativelyAmple _ _
        ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (eX.hom ≫ f.hom ≫ eY.hom)))
        (baseChangeModule B S hS L U eX.hom) hL) :
    IsRelativelyAmple B S hS f L := by
  obtain ⟨U, eX, hL, hamp⟩ := h
  have := hL
  have hmapq : yoneda.map (yoneda.preimage (eX.hom ≫ f.hom ≫ eY.hom)) =
      eX.hom ≫ f.hom ≫ eY.hom := yoneda.map_preimage _
  set q : U ⟶ V := yoneda.preimage (eX.hom ≫ f.hom ≫ eY.hom)
  have hfhom : f.hom = eX.inv ≫ yoneda.map q ≫ eY.inv := by rw [hmapq]; simp
  refine ⟨?_, ?_⟩
  · have hq : yoneda.relativelyRepresentable (yoneda.map q) :=
      Functor.relativelyRepresentable.map yoneda q
    rw [hfhom]
    exact (MorphismProperty.cancel_left_of_respectsIso _ eX.inv _).mpr
      ((MorphismProperty.cancel_right_of_respectsIso _ _ eY.inv).mpr hq)
  · intro T U' g p q' hsq
    have hmapr : yoneda.map (yoneda.preimage (p ≫ eX.inv)) = p ≫ eX.inv := yoneda.map_preimage _
    have hmaps : yoneda.map (yoneda.preimage (g ≫ eY.hom)) = g ≫ eY.hom := yoneda.map_preimage _
    set r : U' ⟶ U := yoneda.preimage (p ≫ eX.inv)
    set s : T ⟶ V := yoneda.preimage (g ≫ eY.hom)
    have hsq₁ : IsPullback (yoneda.map r) (yoneda.map q') (yoneda.map q) (yoneda.map s) :=
      hsq.of_iso (Iso.refl _) eX.symm (Iso.refl _) eY
        (by simp [hmapr]) (by simp) (by rw [hmapq]; simp) (by simp [hmaps])
    have hsq₂ : IsPullback r q' q s :=
      IsPullback.of_map yoneda
        (yoneda.map_injective (by simp only [Functor.map_comp]; exact hsq₁.w)) hsq₁
    have hamp' := Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback
      (hsq₂.map (BigFppfOver.toScheme B S hS)) (baseChangeModule B S hS L U eX.hom) hamp
    obtain ⟨e⟩ := nonempty_baseChangeModule_baseChange_of_isInvertible L hLinv U U' eX.hom r
    have hp : yoneda.map r ≫ eX.hom = p := by rw [hmapr]; simp
    rw [hp] at e
    have hinv : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U')
        (baseChangeModule B S hS L U' p) :=
      Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e.symm
    exact ⟨hinv, (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e.symm).mp hamp'⟩

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over the base, let `L` be
an invertible `𝒪_X`-module, and assume that the algebraic space `Y` is the scheme `V`. The
following are equivalent:

1. `L` is ample relative to `f` in the sense of algebraic spaces, Stacks 0D31;
2. `X` is a scheme `U` and the restriction of `L` to `U` is invertible and ample relative to the
   morphism `U ⟶ V` induced by `f`, in the sense of schemes, Stacks 01VH. -/
@[stacks 0D32]
theorem isRelativelyAmple_iff_exists_scheme {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (L : Modules.{u, u} B S hS X.1 X.2)
    (hLinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (V : BigFppfOver B S hS) (eY : Y.1 ≅ yoneda.obj V) :
    IsRelativelyAmple B S hS f L ↔
      ∃ (U : BigFppfOver B S hS) (eX : yoneda.obj U ≅ X.1)
        (hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
          (baseChangeModule B S hS L U eX.hom)),
        @Stacks.RelativeAmple.IsRelativelyAmple _ _
          ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (eX.hom ≫ f.hom ≫ eY.hom)))
          (baseChangeModule B S hS L U eX.hom) hL :=
  ⟨fun h => h.exists_scheme V eY, isRelativelyAmple_of_exists_scheme f L hLinv V eY⟩

end AlgebraicGeometry.Space

end
