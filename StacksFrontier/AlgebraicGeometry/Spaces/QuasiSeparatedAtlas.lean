module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-separatedness of an algebraic space from a quasi-separated étale atlas

Let `F` be an algebraic space over a scheme `S` and let `q : yoneda.obj U ⟶ F` be a surjective
étale chart whose source is a quasi-separated scheme. If one of the two projections of the
kernel pair `U ×_F U ⟶ U` is quasi-compact, then `F` is quasi-separated over `S`: its diagonal
`F ⟶ F ⨯ F` is quasi-compact after every representable base change.

## Main results

* `AlgebraicGeometry.Space.quasiSeparated_toScheme_map_prod_fst` and
  `AlgebraicGeometry.Space.quasiSeparated_toScheme_map_prod_snd`: a projection of a binary
  product of the big fppf category over `S` is a quasi-separated morphism of schemes as soon as
  the scheme underlying the *other* factor is quasi-separated.
* `AlgebraicGeometry.Space.quasiCompact_toScheme_map_kernelPairToProd`: the morphism
  `U ×_F U ⟶ U ⨯ U` of the site induced by the kernel pair of a chart is quasi-compact as soon
  as one of the two projections `U ×_F U ⟶ U` is.
* `AlgebraicGeometry.Space.isQuasiSeparatedOver_of_etaleAtlas_quasiCompact_projection`: an
  algebraic space with a surjective étale chart by a quasi-separated scheme, one of whose
  kernel-pair projections is quasi-compact, is quasi-separated over `S`.
* `Stacks.Spaces.quasiCompact_of_isPullback_of_surjective_etale`: quasi-compactness of a
  morphism of schemes descends along a surjective étale morphism.
* `Stacks.Spaces.isPullback_of_iso_right` cancels an isomorphism from the right-hand leg of a
  cartesian square, and `Stacks.Spaces.isPullback_diag` exhibits the self-fibre-product of a
  morphism as the fibre product of the diagonal of its target with the square of the morphism.

## Implementation notes

The reduction to the site is `AlgebraicGeometry.Space.presheaf_diag_of_kernelPair`: a
base-change stable, fppf local property of morphisms of schemes holds on every represented base
change of the diagonal of an algebraic space as soon as it holds on the single morphism
`j : U ×_F U ⟶ U ⨯ U` of the site induced by the kernel pair of a surjective étale chart.
Quasi-compactness is such a property, being fpqc local on the target.

The conclusion is quasi-separatedness over `S`. The absolute quasi-separatedness is the same
predicate over the terminal scheme, applied to `AlgebraicGeometry.Space.viewOverIntegers` of the
space.

## References

* [Stacks Project, Tag 07S4](https://stacks.math.columbia.edu/tag/07S4)
* [Stacks Project, Tag 01KU](https://stacks.math.columbia.edu/tag/01KU)
* [Stacks Project, Tag 03GI](https://stacks.math.columbia.edu/tag/03GI)
* [Stacks Project, Tag 02WZ](https://stacks.math.columbia.edu/tag/02WZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.Spaces

open AlgebraicGeometry MorphismProperty

/-- Quasi-compactness descends along a surjective étale morphism of schemes: if the square is
cartesian and `f` is surjective and étale, then `g` is quasi-compact as soon as its base change
`fst` along `f` is. -/
theorem quasiCompact_of_isPullback_of_surjective_etale {X Y Z P : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g)
    (hsurj : Surjective f) (hetale : Etale f) (hfst : QuasiCompact fst) : QuasiCompact g := by
  obtain ⟨hflat, -, hlfp⟩ := AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified.mp hetale
  have : MorphismProperty.RespectsIso (@QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hmem : Presieve.singleton f ∈ Scheme.fppfPrecoverage Z :=
    f.singleton_mem_fppfPrecoverage
  refine (MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd
    (K := Scheme.fppfPrecoverage) hmem).mpr ?_
  intro V g' _ hg'
  cases hg'
  have : HasPullback g f := h.flip.hasPullback
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @QuasiCompact)
      h.flip.isoPullback.hom, h.flip.isoPullback_hom_snd]
  exact hfst

/-- If the square with right-hand leg `i ≫ g` and left-hand leg `snd` is cartesian after
absorbing the isomorphism `i` into `snd`, then it is cartesian as it stands. -/
theorem isPullback_of_iso_right {C : Type u} [Category.{v} C] {P X Y Y' Z : C}
    {fst : P ⟶ X} {snd : P ⟶ Y'} {f : X ⟶ Z} {i : Y' ⟶ Y} [IsIso i] {g : Y ⟶ Z}
    (h : IsPullback fst (snd ≫ i) f g) : IsPullback fst snd f (i ≫ g) :=
  h.of_iso (Iso.refl _) (Iso.refl _) (asIso i).symm (Iso.refl _) (by simp) (by simp)
    (by simp) (by simp)

/-- If `p₁, p₂ : P ⟶ G` exhibit `P` as the fibre product of `q : G ⟶ F` with itself, then `P`
is the fibre product of the diagonal of `F` with the square of `q`. -/
theorem isPullback_diag {C : Type u} [Category.{v} C] {F G : C} (q : G ⟶ F)
    [HasBinaryProduct F F] [HasBinaryProduct G G] {P : C} {p₁ p₂ : P ⟶ G}
    (h : IsPullback p₁ p₂ q q) :
    IsPullback (p₁ ≫ q) (prod.lift p₁ p₂) (diag F) (prod.map q q) := by
  have comm : (p₁ ≫ q) ≫ diag F = prod.lift p₁ p₂ ≫ prod.map q q := by
    refine prod.hom_ext ?_ ?_ <;> simp [h.w]
  have key : ∀ s : PullbackCone (diag F) (prod.map q q),
      (s.snd ≫ prod.fst) ≫ q = (s.snd ≫ prod.snd) ≫ q := by
    intro s
    have h1 := s.condition =≫ prod.fst
    have h2 := s.condition =≫ prod.snd
    simp only [Category.assoc, prod.lift_fst, prod.lift_snd, prod.map_fst, prod.map_snd] at h1 h2
    rw [Category.assoc, Category.assoc, ← h1, ← h2]
  refine ⟨⟨comm⟩, ⟨PullbackCone.IsLimit.mk comm
    (fun s => h.lift (s.snd ≫ prod.fst) (s.snd ≫ prod.snd) (key s)) ?_ ?_ ?_⟩⟩
  · intro s
    have h1 := s.condition =≫ prod.fst
    simp only [Category.assoc, prod.lift_fst, prod.map_fst] at h1
    rw [← Category.assoc, h.lift_fst, Category.assoc]
    simpa using h1.symm
  · intro s
    refine prod.hom_ext ?_ ?_ <;> simp [h.lift_fst, h.lift_snd]
  · intro s m hm₁ hm₂
    refine h.hom_ext ?_ ?_
    · rw [h.lift_fst, ← hm₂]; simp
    · rw [h.lift_snd, ← hm₂]; simp

end Stacks.Spaces

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Quasi-compactness of morphisms of schemes is fppf local on the target -/

/-- Quasi-compactness of a morphism of schemes is fppf local on the target: it is fpqc local on
the target (Stacks 02KQ), and the fppf precoverage is coarser than the fpqc precoverage. -/
@[sga "4 IV 8.5.5" "special case"]
theorem quasiCompact_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage

/-! ### The projections of a binary product of the site -/

/-- The underlying square of a binary product of the big fppf category over `S` is cartesian. -/
private theorem isPullback_prod_left (U V : BigFppfOver B S hS) :
    IsPullback ((prod.fst : U ⨯ V ⟶ U)).left ((prod.snd : U ⨯ V ⟶ V)).left U.hom V.hom :=
  Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk prod.fst prod.snd) (prodIsProd U V)

/-- The first projection of a binary product of the big fppf category over `S` is a
quasi-separated morphism of schemes when the scheme underlying the second factor is
quasi-separated. -/
theorem quasiSeparated_toScheme_map_prod_fst (U V : BigFppfOver B S hS)
    (hV : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj V)) :
    QuasiSeparated ((BigFppfOver.toScheme B S hS).map (prod.fst : U ⨯ V ⟶ U)) := by
  have h := isPullback_prod_left B S hS U V
  have : QuasiSeparatedSpace (B.inclusion.obj V.left) := hV
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated)
    (B.inclusion.map_isPullback h.flip) (QuasiSeparated.of_quasiSeparatedSpace _)

/-- The second projection of a binary product of the big fppf category over `S` is a
quasi-separated morphism of schemes when the scheme underlying the first factor is
quasi-separated. -/
theorem quasiSeparated_toScheme_map_prod_snd (U V : BigFppfOver B S hS)
    (hU : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U)) :
    QuasiSeparated ((BigFppfOver.toScheme B S hS).map (prod.snd : U ⨯ V ⟶ V)) := by
  have h := isPullback_prod_left B S hS U V
  have : QuasiSeparatedSpace (B.inclusion.obj U.left) := hU
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated)
    (B.inclusion.map_isPullback h) (QuasiSeparated.of_quasiSeparatedSpace _)

/-! ### The kernel pair of a chart -/

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}

/-- The chosen represented kernel pair of a representable chart agrees with its pullback in
the presheaf category. -/
def kernelPairYonedaIso {q : yoneda.obj U ⟶ F} (hq : yoneda.relativelyRepresentable q) :
    yoneda.obj (hq.pullback q) ≅ pullback q q :=
  (hq.isPullback' q).isoIsPullback _ _ (IsPullback.of_hasPullback q q)

/-- A property of the first projection of the presheaf pullback of a chart along itself is a
property of the first projection of the chosen represented kernel pair. -/
theorem property_kernelPair_fst (P : MorphismProperty Scheme.{u}) {q : yoneda.obj U ⟶ F}
    (hq : yoneda.relativelyRepresentable q)
    (h : (MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B S hS)))
      (pullback.fst q q)) :
    P ((BigFppfOver.toScheme B S hS).map (hq.fst' q)) :=
  h.property (𝟙 (yoneda.obj U)) (kernelPairYonedaIso B S hS hq).hom (hq.fst' q)
    (IsPullback.of_horiz_isIso ⟨by simp [kernelPairYonedaIso]⟩)

/-- A property of the second projection of the presheaf pullback of a chart along itself is a
property of the second projection of the chosen represented kernel pair. -/
theorem property_kernelPair_snd (P : MorphismProperty Scheme.{u}) {q : yoneda.obj U ⟶ F}
    (hq : yoneda.relativelyRepresentable q)
    (h : (MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B S hS)))
      (pullback.snd q q)) :
    P ((BigFppfOver.toScheme B S hS).map (hq.snd q)) :=
  h.property (𝟙 (yoneda.obj U)) (kernelPairYonedaIso B S hS hq).hom (hq.snd q)
    (IsPullback.of_horiz_isIso ⟨by simp [kernelPairYonedaIso]⟩)

/-- If the source of a chart is a quasi-separated scheme and one of the two projections of its
kernel pair is quasi-compact, then the morphism `U ×_F U ⟶ U ⨯ U` of the site induced by the
kernel pair is quasi-compact. -/
theorem quasiCompact_toScheme_map_kernelPairToProd {q : yoneda.obj U ⟶ F}
    (hq : yoneda.relativelyRepresentable q)
    (hU : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U))
    (hqc : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (pullback.fst q q) ∨
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (pullback.snd q q)) :
    QuasiCompact ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS hq)) := by
  set T := BigFppfOver.toScheme B S hS
  rcases hqc with h | h
  · have := quasiSeparated_toScheme_map_prod_fst B S hS U U hU
    have h₁ : QuasiCompact (T.map (kernelPairToProd B S hS hq ≫ prod.fst)) := by
      simpa only [kernelPairToProd, prod.lift_fst] using property_kernelPair_fst B S hS _ hq h
    rw [T.map_comp] at h₁
    exact QuasiCompact.of_comp _ (T.map (prod.fst : U ⨯ U ⟶ U))
  · have := quasiSeparated_toScheme_map_prod_snd B S hS U U hU
    have h₁ : QuasiCompact (T.map (kernelPairToProd B S hS hq ≫ prod.snd)) := by
      simpa only [kernelPairToProd, prod.lift_snd] using property_kernelPair_snd B S hS _ hq h
    rw [T.map_comp] at h₁
    exact QuasiCompact.of_comp _ (T.map (prod.snd : U ⨯ U ⟶ U))

/-! ### Quasi-separatedness over the base from a quasi-separated étale atlas -/

/-- An algebraic space over `S` which
has a surjective étale chart by a quasi-separated scheme, one of whose kernel-pair projections
is quasi-compact, is quasi-separated over `S`. -/
theorem isQuasiSeparatedOver_of_etaleAtlas_quasiCompact_projection
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (hAtlas : ∃ (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ X),
      QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U) ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) q ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) q ∧
      ((MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (pullback.fst q q) ∨
       (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (pullback.snd q q))) :
    IsQuasiSeparatedOver B S hS X := by
  obtain ⟨U, q, hU, hsurj, hetale, hqc⟩ := hAtlas
  have _ := quasiCompact_isLocalAtTarget_fppf.{u}
  exact presheaf_diag_of_kernelPair B S hS (@QuasiCompact) hX.diagonal_representable
    (hetale.rep.isPullback' q) hsurj hetale
    (quasiCompact_toScheme_map_kernelPairToProd B S hS hetale.rep hU hqc)

end AlgebraicGeometry.Space

end
