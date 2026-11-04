module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.General.Approximation
public import StacksCore.Tactic.StacksAttribute

/-!
# Separating a closed subscheme from a fibre

A closed subscheme of a base change `X ×_S T` of a quasi-compact morphism `f : X ⟶ S`, disjoint
from the fibre over a point `t ∈ T`, is locally contained in a closed subscheme defined already
over an affine base locally of finite presentation over `S`, which remains disjoint from the
corresponding fibre.

## Main results

* `AlgebraicGeometry.exists_affine_locallyFinitePresentation_separation` produces the affine
  neighbourhood of `t`, the affine finitely presented approximation of the base, and the
  separating closed subscheme. This is Tag 05BD.

## Implementation notes

Closed subschemes are expressed by ideal sheaf data, and disjointness from a fibre means that the
distinguished point is not in the image of the support. The comparison morphisms out of the base
change over the open neighbourhood are specified by their projections, and the ideal-sheaf
inequality `I'.comap q ≤ I.comap p` is the scheme-theoretic assertion that the restricted closed
subscheme maps into the one defined over the approximating base.

The proof shrinks to an affine neighbourhood `V` of `t` mapping into an affine open `U` of `S`,
writes the resulting morphism of affine schemes as a cofiltered limit of affine schemes locally of
finite presentation over `U` by
`Stacks.AlgebraicGeometry.Tag05JXGeneral.exists_affine_limit_presentation`, and pushes a compact
open separating the support from the fibre down to a finite stage of that limit by
`Stacks.AlgebraicGeometry.Tag05JXGeneral.exists_open_baseChange_of_isLimit`. The compact open
itself comes from `PrespectralSpace.exists_isCompact_and_isOpen_between` applied to the fibre,
which is compact because `f` is quasi-compact.

## References

* [Stacks Project, Tag 05BD](https://stacks.math.columbia.edu/tag/05BD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.AlgebraicGeometry.Tag05JXGeneral

universe u

namespace AlgebraicGeometry

attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc

/-- **Stacks Project, Tag 05BD.** A closed subscheme of a base change `X ×_S T` avoiding the
fibre of `X ×_S T ⟶ T` over a point `t`, for `f : X ⟶ S` quasi-compact, can be separated from
that fibre already over an affine base locally of finite presentation over `S`: there is an
affine open `V ∋ t`, an affine `T'` locally of finite presentation over `S` with a factorization
of `V ⟶ T` through it, and a closed subscheme of `X ×_S T'` containing the restriction of the
given one and still avoiding the fibre over the image of `t`. -/
@[stacks 05BD]
theorem exists_affine_locallyFinitePresentation_separation
    {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] (g : T ⟶ S)
    (t : T) (I : (pullback f g).IdealSheafData)
    (ht : t ∉ Set.image (pullback.snd f g) I.support.1) :
    ∃ (V : T.affineOpens) (htV : t ∈ V.1)
      (T' : Scheme.{u}) (_ : IsAffine T') (b : T' ⟶ S)
      (_ : LocallyOfFinitePresentation b) (a : V.1.toScheme ⟶ T')
      (_ : V.1.ι ≫ g = a ≫ b)
      (I' : (pullback f b).IdealSheafData)
      (p : pullback f (V.1.ι ≫ g) ⟶ pullback f g)
      (q : pullback f (V.1.ι ≫ g) ⟶ pullback f b),
      (p ≫ pullback.fst f g = pullback.fst f (V.1.ι ≫ g)) ∧
      (p ≫ pullback.snd f g = pullback.snd f (V.1.ι ≫ g) ≫ V.1.ι) ∧
      (q ≫ pullback.fst f b = pullback.fst f (V.1.ι ≫ g)) ∧
      (q ≫ pullback.snd f b = pullback.snd f (V.1.ι ≫ g) ≫ a) ∧
      (a ⟨t, htV⟩ ∉ Set.image (pullback.snd f b) I'.support.1) ∧
      (I'.comap q ≤ I.comap p) := by
  classical
  obtain ⟨U, V, htV, gV, hgV⟩ := exists_affine_neighborhood_lift g t
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine V.1.toScheme := V.2
  obtain ⟨J, _, _, D, c, hc, e, b, hD, hb, he⟩ :=
    exists_affine_limit_presentation gV
  have (j : J) : IsAffine (D.obj j) := hD j
  let bS : D ⟶ (Functor.const J).obj S :=
    { app j := b.app j ≫ U.1.ι
      naturality i j h := by simp }
  have hfac (j : J) : V.1.ι ≫ g = e.hom ≫ c.π.app j ≫ bS.app j := by
    rw [← hgV, he j]
    simp [bS]
  let p := pullback.map f (V.1.ι ≫ g) f g (𝟙 X) V.1.ι (𝟙 S) (by simp) (by simp)
  have hp₂ : p ≫ pullback.snd f g = pullback.snd f (V.1.ι ≫ g) ≫ V.1.ι := by
    simp [p, pullback.map]
  let K := I.comap p
  have hKt : (pullback.snd f (V.1.ι ≫ g)) ⁻¹' {⟨t, htV⟩} ⊆
      (K.support : Set ↑(pullback f (V.1.ι ≫ g)))ᶜ := by
    intro x hx hKx
    refine ht ⟨p x, ?_, ?_⟩
    · simpa [K, Scheme.IdealSheafData.support_comap] using hKx
    · change pullback.snd f (V.1.ι ≫ g) x = ⟨t, htV⟩ at hx
      rw [← Scheme.Hom.comp_apply, hp₂, Scheme.Hom.comp_apply, hx]
      rfl
  obtain ⟨W₀, hWc, hWo, hKW, hWK⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between
      ((pullback.snd f (V.1.ι ≫ g)).isCompact_preimage_singleton ⟨t, htV⟩)
      K.support.2.isOpen_compl hKt
  obtain ⟨j, W', hW'⟩ := exists_open_baseChange_of_isLimit f (V.1.ι ≫ g)
    D c hc e bS hfac ⟨W₀, hWo⟩ hWc
  let a := e.hom ≫ c.π.app j
  have hcomm : V.1.ι ≫ g = a ≫ bS.app j := by simpa [a] using hfac j
  let q := pullback.map f (V.1.ι ≫ g) f (bS.app j) (𝟙 X) a (𝟙 S) (by simp) (by simpa using hcomm)
  have hqpb := isPullback_baseChangeMap f (V.1.ι ≫ g) (bS.app j) a hcomm
  have : IsAffineHom q := MorphismProperty.of_isPullback hqpb.flip inferInstance
  have hclosed : closure (q '' K.support) ⊆ (W' : Set ↑(pullback f (bS.app j)))ᶜ := by
    refine W'.2.isClosed_compl.closure_subset_iff.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ hxW
    exact hWK (hW'.le hxW) hx
  let I' := K.map q
  have havoid : a ⟨t, htV⟩ ∉ Set.image (pullback.snd f (bS.app j)) I'.support.1 := by
    rintro ⟨y, hy, hyt⟩
    obtain ⟨x, hxy, hxt⟩ := Scheme.exists_preimage_of_isPullback hqpb y ⟨t, htV⟩ hyt
    exact hclosed (by simpa [I'] using hy) (by rw [← hxy]; exact hW'.ge (hKW hxt))
  have : LocallyOfFinitePresentation (bS.app j) := by have := hb j; dsimp [bS]; infer_instance
  exact ⟨V, htV, D.obj j, inferInstance, bS.app j, inferInstance, a, hcomm,
    I', p, q, (by simp [p, pullback.map]), hp₂,
    (by simp [q, pullback.map]), (by simp [q, pullback.map]), havoid,
    Scheme.IdealSheafData.le_map_iff_comap_le.mp le_rfl⟩

end AlgebraicGeometry

end
