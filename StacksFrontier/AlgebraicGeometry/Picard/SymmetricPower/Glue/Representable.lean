module

public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.Glue.PushForward
public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.AffineRepresentable

/-!
# Representability of the Hilbert scheme of points (Stacks Tag 0B9A)

**Stacks Tag 0B9A**, over an affine base and for a separated morphism. Let `X ⟶ S` be a separated
morphism of schemes with `S` affine, and assume every `d` points of a fibre of `X ⟶ S` lie in an
affine open of `X`. Then the degree-`d` Hilbert functor of `X` over `S` is representable.

The proof is the one of the source: for an affine open `U ⊆ X` the families supported in `U`
form an open subfunctor `F_U`, identified with the Hilbert functor of `U`
(`Stacks.Hilbert.pushMap`), which is representable by Stacks Tag 0B99
(`Stacks.Hilbert.isRepresentable_hilbPresheaf_of_isAffine`); the hypothesis makes the `F_U`
cover the Hilbert functor (`Stacks.Hilbert.exists_isAffineOpen_supportedIn_of_specField`,
condition (2)(c) of the source), and Stacks Tag 01JJ glues them.

The source states the tag over an arbitrary base and without separatedness; the base change
to an affine base (Stacks Tag 01LG) and the non-separated footnote are not needed for the
application to curves over a field and are not done here.

## Main results

* `AlgebraicGeometry.IsOpenSubfunctorHom.of_isIso`: isomorphisms are open subfunctors.
* `Stacks.Hilbert.isRepresentable_hilbPresheaf_of_affineOpens`: the representability.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.IsOpenSubfunctorHom

/-- **An isomorphism of presheaves is an open subfunctor.** -/
theorem of_isIso {F G : Scheme.{u}ᵒᵖ ⥤ Type u} (ι : G ⟶ F) [IsIso ι] : IsOpenSubfunctorHom ι := by
  have hbij (T) : Function.Bijective (ι.app T) := (isIso_iff_bijective _).mp inferInstance
  exact ⟨fun T => (hbij T).1,
    fun _ _ => ⟨⊤, fun _ _ => ⟨fun _ _ _ => trivial, fun _ => (hbij _).2 _⟩⟩⟩

end AlgebraicGeometry.IsOpenSubfunctorHom

namespace Stacks.Hilbert

variable {S : Scheme.{u}} [IsAffine S] (X : Over S) [IsSeparated X.hom] (d : ℕ)

/-- An open of `X` as an `S`-scheme. -/
abbrev openOver (U : X.left.Opens) : Over S := Over.mk (U.ι ≫ X.hom)

/-- The inclusion of an open of `X`, as a morphism of `S`-schemes. -/
abbrev openInclusion (U : X.left.Opens) : openOver X U ⟶ X := Over.homMk U.ι rfl

/-- The inclusion of an open of `X` is an open immersion. -/
instance (U : X.left.Opens) : IsOpenImmersion (openInclusion X U).left :=
  inferInstanceAs (IsOpenImmersion U.ι)

/-- **Stacks Tag 0B9A, for a separated morphism to an affine base.** If every `d` points of a
fibre of a separated morphism `X ⟶ S` with `S` affine lie in an affine open of `X`, then the
degree-`d` Hilbert functor of `X` over `S` is representable. -/
theorem isRepresentable_hilbPresheaf_of_affineOpens
    (hX : ∀ (s : S) (x : Fin d → X.left), (∀ i, X.hom (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U) :
    (hilbPresheaf X d).IsRepresentable := by
  have rep : ∀ U : X.left.affineOpens, (hilbPresheaf (openOver X U.1) d).IsRepresentable :=
    fun U => by
      have : IsAffine (openOver X U.1).left := U.2
      exact isRepresentable_hilbPresheaf_of_isAffine _ d
  let χ : ∀ U : X.left.affineOpens,
      yoneda.obj (hilbPresheaf (openOver X U.1) d).reprX ⟶ hilbPresheaf X d :=
    fun U => (hilbPresheaf (openOver X U.1) d).reprW.hom ≫ pushMap (openInclusion X U.1) d
  have hχ : ∀ U, IsOpenSubfunctorHom (χ U) := fun U =>
    (IsOpenSubfunctorHom.of_isIso _).comp (isOpenSubfunctor_pushMap _ d)
  refine isRepresentable_of_isOpenSubfunctor (isSheaf_hilbPresheaf X d) χ hχ ?_
  intro T p t
  obtain ⟨s, W⟩ := p
  let g := T.fromSpecResidueField t
  let W' := baseChange X (Over.homMk g rfl : Over.mk (g ≫ s) ⟶ Over.mk s) W
  obtain ⟨U, hU, hsupp⟩ := exists_isAffineOpen_supportedIn_of_specField X d hX
    (T.residueField t) (g ≫ s) W'
  let U' : X.left.affineOpens := ⟨U, hU⟩
  refine ⟨U', ?_⟩
  obtain ⟨V, hV⟩ := (hχ U').locus T ⟨s, W⟩
  refine ⟨V, ?_, (hV _ V.ι).mpr (by rw [Scheme.Opens.range_ι])⟩
  have hin : InImage (χ U') ((hilbPresheaf X d).map g.op ⟨s, W⟩) := by
    have h1 : InImage (pushMap (openInclusion X U) d)
        ((hilbPresheaf X d).map g.op ⟨s, W⟩) := by
      show InImage (pushMap (openInclusion X U) d)
        (⟨g ≫ s, W'⟩ : (hilbPresheaf X d).obj (op (Spec (T.residueField t))))
      rw [inImage_pushMap_iff]
      show ∀ z, _ ∈ (U.ι).opensRange
      rw [Scheme.Opens.opensRange_ι]
      exact hsupp
    obtain ⟨q, hq⟩ := h1
    obtain ⟨c, hc⟩ := ((isIso_iff_bijective
      ((hilbPresheaf (openOver X U'.1) d).reprW.hom.app (op (Spec (T.residueField t))))).mp
        inferInstance).2 q
    refine ⟨c, ?_⟩
    show (pushMap (openInclusion X U) d).app _
      ((hilbPresheaf (openOver X U'.1) d).reprW.hom.app _ c) = _
    rw [hc]
    exact hq
  have := (hV _ g).mp hin
  obtain ⟨pt⟩ : Nonempty (Spec (.of (T.residueField t))) := inferInstance
  have hq : g pt = t := Scheme.fromSpecResidueField_apply _ _
  rw [← hq]
  exact this ⟨pt, rfl⟩

end Stacks.Hilbert

end
