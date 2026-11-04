module

public import Mathlib.Data.List.TFAE
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Diagonal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Local
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Scheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Characterizations of unramifiedness at a point

Let `Y` be a locally Noetherian scheme and `f : X ⟶ Y` a morphism locally of finite type. At a
point `x` of `X`, unramifiedness of `f` is equivalent to the vanishing of the stalk at `x` of the
sheaf of relative differentials, and to the diagonal `Δ_{X/Y}` being a local isomorphism at `x`.

## Main results

* `AlgebraicGeometry.stalkwiseUnramifiedAt_tfae` is the equivalence of those three conditions.
* `AlgebraicGeometry.isOpenImmersion_ι_comp_diagonal_iff` compares the restriction of the diagonal
  of a morphism to an open subscheme of its source with the diagonal of the restricted morphism.
* `AlgebraicGeometry.formallyUnramified_stalkMap_of_comp_ι` passes formal unramifiedness of a
  restriction to an open neighbourhood down to the map of local rings at an interior point.

## Implementation notes

The stalk of the sheaf of relative differentials is the stalk of the abelian-group presheaf
underlying `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`, and its vanishing is expressed
as a `Subsingleton`. The translation into the Kähler differentials of the stalk map is
`Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv`, after which the
equivalence with unramifiedness of the stalk map is `Algebra.formallyUnramified_iff`.

That the diagonal is a local isomorphism at `x` is expressed by asking for an open neighbourhood
`U` of `x` on which `Δ_{X/Y}` restricts to an open immersion. Over such a `U` the restriction
factors as the diagonal of `f|_U` followed by the open immersion `U ×_Y U ⟶ X ×_Y X`, which
reduces the condition to the diagonal of `f|_U` and so to unramifiedness of `f|_U`.

## References

* [Stacks Project, Tag 024P](https://stacks.math.columbia.edu/tag/024P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.RelativeDifferentialStalkMap (relativeDifferentialsStalkKaehlerEquiv)

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The diagonal of a morphism restricts to an open immersion on an open subscheme `U` of its
source exactly when the diagonal of its restriction to `U` is an open immersion: the two differ
by the open immersion `U ×_Y U ⟶ X ×_Y X`. -/
theorem isOpenImmersion_ι_comp_diagonal_iff (f : X ⟶ Y) (U : X.Opens) :
    IsOpenImmersion (U.ι ≫ pullback.diagonal f) ↔
      IsOpenImmersion (pullback.diagonal (U.ι ≫ f)) := by
  have key := pullback.comp_diagonal (U.ι : U.toScheme ⟶ X) f
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [key] at h
    exact MorphismProperty.of_postcomp @IsOpenImmersion (W' := @IsOpenImmersion)
      _ _ inferInstance h
  · have := h
    rw [key]
    infer_instance

/-- If the restriction of `f` to an open neighbourhood of `x` is formally unramified, then the
homomorphism `f` induces on the local rings at `x` is formally unramified. -/
theorem formallyUnramified_stalkMap_of_comp_ι (f : X ⟶ Y) {U : X.Opens} {x : X} (hx : x ∈ U)
    (h : FormallyUnramified (U.ι ≫ f)) : (f.stalkMap x).hom.FormallyUnramified := by
  have := h
  have hiso : IsIso (U.ι.stalkMap (⟨x, hx⟩ : U)) := by
    rw [← Scheme.Opens.stalkIso_inv]
    exact (U.stalkIso (⟨x, hx⟩ : U)).symm.isIso_hom
  have hs := FormallyUnramified.stalkMap (U.ι ≫ f) (⟨x, hx⟩ : U)
  have heq : ((U.ι ≫ f).stalkMap (⟨x, hx⟩ : U)).hom =
      (U.ι.stalkMap (⟨x, hx⟩ : U)).hom.comp (f.stalkMap x).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp U.ι f (⟨x, hx⟩ : U))
  rw [heq] at hs
  exact (@RingHom.RespectsIso.cancel_right_isIso _ RingHom.FormallyUnramified.respectsIso
    _ _ _ (f.stalkMap x) (U.ι.stalkMap (⟨x, hx⟩ : U)) hiso).mp hs

/-- The restriction of a morphism to an affine open on which its sections are unramified over an
affine open of the target is unramified. -/
theorem unramified_resLE_of_algebraUnramified (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)
    (h : letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
      Algebra.Unramified Γ(Y, V) Γ(X, U)) :
    Unramified (f.resLE V U e) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  let Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop := fun
      {R S} _ _ g ↦ let := g.toAlgebra; Algebra.Unramified R S
  let P : MorphismProperty Scheme.{u} := affineLocally Q
  have : HasRingHomProperty P Q := ⟨unramified_ringHom_propertyIsLocal, rfl⟩
  exact (unramified_iff_affineLocally _).mpr
    ((HasRingHomProperty.iff_of_isAffine (P := P)).mpr
      ((unramified_ringHom_propertyIsLocal.respectsIso.arrow_mk_iso_iff
        (arrowResLEAppIso f V U e)).mpr h))

/-- The inclusion of an open subscheme is unramified. -/
theorem unramified_opens_ι (V : Y.Opens) : Unramified V.ι :=
  (unramified_iff_locallyOfFiniteType_and_formallyUnramified _).mpr ⟨inferInstance, inferInstance⟩

/-- A morphism locally of finite type which is unramified at `x` restricts to an unramified
morphism on an open neighbourhood of `x`. -/
theorem exists_unramified_comp_ι_of_unramifiedAt (f : X ⟶ Y) [LocallyOfFiniteType f] {x : X}
    (h : UnramifiedAt f x) : ∃ U : X.Opens, x ∈ U ∧ Unramified (U.ι ≫ f) := by
  obtain ⟨U, hU, hxU, V, hV, e, hun⟩ := h
  refine ⟨U, hxU, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f e]
  exact MorphismProperty.comp_mem @Unramified _ _
    (unramified_resLE_of_algebraUnramified f hU hV e hun) (unramified_opens_ι V)

/-- **Stacks Project, Tag 024P.** Let `Y` be a locally Noetherian scheme, `f : X ⟶ Y` a morphism
locally of finite type and `x` a point of `X`. Then `f` is unramified at `x` if and only if the
stalk at `x` of the sheaf of relative differentials of `f` vanishes, and if and only if the
diagonal `Δ_{X/Y}` is a local isomorphism at `x`. -/
@[stacks 024P "equivalence of conditions (1), (2) and (4)",
  ega "IV 17.4.2" "Y loc. Noetherian, at x", ega "IV 17.4.1" "Y loc. Noeth.; a),b),c)"]
theorem stalkwiseUnramifiedAt_tfae (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
    (x : X) :
    List.TFAE [
      StalkwiseUnramifiedAt f x,
      Subsingleton ((Scheme.Hom.relativeDifferentials f).presheaf.stalk x),
      ∃ U : X.Opens, x ∈ U ∧ IsOpenImmersion (U.ι ≫ pullback.diagonal f)] := by
  classical
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  tfae_have 1 ↔ 2 := by
    rw [show StalkwiseUnramifiedAt f x ↔
        Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) from Iff.rfl,
      Algebra.formallyUnramified_iff]
    exact (Equiv.subsingleton_congr (relativeDifferentialsStalkKaehlerEquiv f x).toEquiv).symm
  tfae_have 1 → 3 := by
    intro h
    obtain ⟨U, hxU, hunr⟩ := exists_unramified_comp_ι_of_unramifiedAt f
      ((unramifiedAt_iff_morphisms_unramifiedAt f x).mp h)
    refine ⟨U, hxU, (isOpenImmersion_ι_comp_diagonal_iff f U).mpr ?_⟩
    have := hunr
    exact Unramified.isOpenImmersion_diagonal (U.ι ≫ f)
  tfae_have 3 → 1 := by
    rintro ⟨U, hxU, hdiag⟩
    have : IsOpenImmersion (pullback.diagonal (U.ι ≫ f)) :=
      (isOpenImmersion_ι_comp_diagonal_iff f U).mp hdiag
    exact RingHom.formallyUnramified_algebraMap.mp
      (formallyUnramified_stalkMap_of_comp_ι f hxU inferInstance)
  tfae_finish

end AlgebraicGeometry

end
