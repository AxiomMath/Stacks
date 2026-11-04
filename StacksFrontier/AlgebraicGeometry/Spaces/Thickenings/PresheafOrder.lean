module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified
public import StacksFrontier.AlgebraicGeometry.Thickenings.KernelGlobalSections

/-!
# The order of a thickening of algebraic spaces, read on scheme base changes

A morphism `i : X ⟶ X'` of algebraic spaces over `S` can be said to be an `n`th-order thickening
in two ways.

* In the convention of Stacks 02YU for properties of morphisms: every base change of `i` to a
  scheme is an `n`th-order thickening of schemes, that is,
  `(MorphismProperty.inverseImage (thickOrder n) (BigFppfOver.toScheme B S hS)).presheaf i.hom`.
* In the convention of Stacks 05ZK: `i` is an isomorphism onto its range
  (`AlgebraicGeometry.Space.IsThickeningHom`) and the range is an `n`th-order thickening of `X'`
  (`AlgebraicGeometry.Space.IsNthOrderThickening`), measured by the defining ideal on the étale
  charts of `X'`.

This file proves that the two agree, for a fixed order and for finite order.

## Main results

All in the namespace `AlgebraicGeometry.Space`:

* `isNthOrderThickening_of_presheaf_thickOrder_ι` and
  `presheaf_thickOrder_ι_of_isNthOrderThickening`: the two directions for the inclusion of a
  subfunctor.
* `presheaf_thickOrder_iff_isThickeningHom_and_isNthOrderThickening`: the equivalence for a
  morphism of algebraic spaces, at a fixed order.
* `exists_presheaf_thickOrder_iff_isThickeningHom_and_isFiniteOrderThickening`: the same for
  finite order.
* `exists_presheaf_thickOrder_of_isFiniteOrderThickening`: a morphism identified with the
  inclusion of a finite-order thickening subspace is a thickening of finite order in the
  convention of Stacks 02YU.

## Implementation notes

From the presheaf form to the subspace form, the defining ideal of the range on an étale chart
`U` is the kernel on global sections of the base change of the inclusion to `U`
(`AlgebraicGeometry.Space.definingIdealAt_eq_ker`), whose `(n+1)`st power vanishes because that
base change is an `n`th-order thickening of schemes.

The other direction must reach base changes to schemes `T ⟶ X'` that are not étale. The inverse
image of an `n`th-order thickening along `T ⟶ X'` is an `n`th-order thickening of `T`, by
Stacks 09ZX (`AlgebraicGeometry.Space.isNthOrderThickening_preimage`), and on the identity chart
of `T` this is an `n`th-order thickening of schemes
(`AlgebraicGeometry.Space.exists_nthOrderThickening_chart_pullback`); pasting it with the
cartesian square of the inverse image gives a base change of the inclusion to `T`.

## References

* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of presheaves all of whose scheme base changes are `n`th-order thickenings is a
closed immersion. -/
private theorem isClosedImmersion_of_presheaf_thickOrder {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {n : ℕ}
    (h : (MorphismProperty.inverseImage (thickOrder.{u} n)
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsClosedImmersion B S hS f :=
  MorphismProperty.relative_monotone
    (P := MorphismProperty.inverseImage (thickOrder.{u} n) (BigFppfOver.toScheme B S hS))
    (P' := MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
    (fun _ _ _ hg => hg.1) _ h

/-- **A subfunctor whose inclusion has `n`th-order thickenings as scheme base changes is an
`n`th-order thickening.** Let `G` be a subfunctor of an algebraic space `X'` which is itself an
algebraic space. If every base change of the inclusion `G ⟶ X'` to a scheme is an `n`th-order
thickening of schemes, then `G` is an `n`th-order thickening of `X'` in the sense of Stacks 05ZK,
part (4). -/
theorem isNthOrderThickening_of_presheaf_thickOrder_ι {X' : AlgebraicSpaces B S hS}
    (G : Subfunctor X'.1) (hG : IsAlgebraicSpace B S hS G.toFunctor) {n : ℕ}
    (h : (MorphismProperty.inverseImage (thickOrder.{u} n)
      (BigFppfOver.toScheme B S hS)).presheaf G.ι) :
    IsNthOrderThickening B S hS n X' G := by
  have hci : IsClosedImmersion B S hS G.ι := isClosedImmersion_of_presheaf_thickOrder B S hS h
  have hsurj : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf G.ι :=
    MorphismProperty.relative_monotone
      (P := MorphismProperty.inverseImage (thickOrder.{u} n) (BigFppfOver.toScheme B S hS))
      (fun _ _ _ hg => ⟨(Stacks.Thickenings.IsNthOrderThickening.isThickening hg).2⟩) _ h
  refine ⟨⟨⟨hG, hci⟩,
    (surjective_iff_pointsMap_surjective B S hS hG X'.2 G.ι hci.rep).1 hsurj⟩, fun U => ?_⟩
  have hn : Stacks.Thickenings.IsNthOrderThickening n
      ((BigFppfOver.toScheme B S hS).map (hci.rep.snd U.1.hom)) :=
    h.property_snd _
  rw [definingIdealAt_eq_ker B S hS X' ⟨G, ⟨hG, hci⟩⟩ U, Scheme.Γ_map_op]
  exact Scheme.ker_appTop_pow_eq_bot _ (by have := hn.1; infer_instance) hn.2

/-- **The inclusion of an `n`th-order thickening has `n`th-order thickenings as scheme base
changes.** If `G` is an `n`th-order thickening of an algebraic space `X'` in the sense of
Stacks 05ZK, part (4), then every base change of the inclusion `G ⟶ X'` to a scheme is an
`n`th-order thickening of schemes.

Along `g : T ⟶ X'` the inverse image of `G` is an `n`th-order thickening of `T` by Stacks 09ZX,
and on the identity chart of `T` it is cut out by an `n`th-order thickening of schemes. -/
theorem presheaf_thickOrder_ι_of_isNthOrderThickening {X' : AlgebraicSpaces B S hS}
    {G : Subfunctor X'.1} {n : ℕ} (hG : IsNthOrderThickening B S hS n X' G) :
    (MorphismProperty.inverseImage (thickOrder.{u} n)
      (BigFppfOver.toScheme B S hS)).presheaf G.ι := by
  refine MorphismProperty.relative.of_exists fun T g => ?_
  let T' : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  have hpre := isNthOrderThickening_preimage B S hS G (ObjectProperty.homMk g : T' ⟶ X') hG
  have hid : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj T)) :=
    (isMultiplicative_presheaf_etale B S hS).id_mem _
  obtain ⟨T₀, j, p, hpb, hj⟩ := exists_nthOrderThickening_chart_pullback B S hS hpre T (𝟙 _) hid
  refine ⟨T₀, p ≫ G.fromPreimage g, j, ?_, hj⟩
  simpa using hpb.paste_horiz (Subfunctor.isPullback_preimage g G)

/-- **Two conventions for an `n`th-order thickening of algebraic spaces agree.** A morphism
`i : X ⟶ X'` of algebraic spaces has `n`th-order thickenings of schemes as all its base changes
to schemes (the convention of Stacks 02YU) if and only if it is an isomorphism onto its range
and that range is an `n`th-order thickening of `X'` (Stacks 05ZK, parts (1) and (4)). -/
theorem presheaf_thickOrder_iff_isThickeningHom_and_isNthOrderThickening
    {X X' : AlgebraicSpaces B S hS} (i : X ⟶ X') (n : ℕ) :
    (MorphismProperty.inverseImage (thickOrder.{u} n)
      (BigFppfOver.toScheme B S hS)).presheaf i.hom ↔
      IsThickeningHom B S hS i ∧
        IsNthOrderThickening B S hS n X' (Subfunctor.range i.hom) := by
  constructor
  · intro h
    have hci : IsClosedImmersion B S hS i.hom := isClosedImmersion_of_presheaf_thickOrder B S hS h
    have : Mono i.hom := mono_of_isClosedImmersion B S hS i.hom hci
    have heq : inv (Subfunctor.toRange i.hom) ≫ i.hom = (Subfunctor.range i.hom).ι :=
      (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι i.hom).symm
    have hι : (MorphismProperty.inverseImage (thickOrder.{u} n)
        (BigFppfOver.toScheme B S hS)).presheaf (Subfunctor.range i.hom).ι :=
      heq ▸ MorphismProperty.RespectsIso.precomp _ (inv (Subfunctor.toRange i.hom)) i.hom h
    have hn := isNthOrderThickening_of_presheaf_thickOrder_ι B S hS (Subfunctor.range i.hom)
      (isAlgebraicSpace_of_iso B S hS (asIso (Subfunctor.toRange i.hom)) X.2) hι
    exact ⟨⟨inferInstance, hn.1⟩, hn⟩
  · rintro ⟨hi, hn⟩
    have := hi.1
    rw [← Subfunctor.toRange_ι i.hom]
    exact MorphismProperty.RespectsIso.precomp _ _ _
      (presheaf_thickOrder_ι_of_isNthOrderThickening B S hS hn)

/-- **Two conventions for a finite-order thickening of algebraic spaces agree.** A morphism
`i : X ⟶ X'` of algebraic spaces has, for one `n`, `n`th-order thickenings of schemes as all its
base changes to schemes if and only if it is an isomorphism onto its range and that range is a
finite-order thickening of `X'` (Stacks 05ZK, parts (1) and (3)). -/
theorem exists_presheaf_thickOrder_iff_isThickeningHom_and_isFiniteOrderThickening
    {X X' : AlgebraicSpaces B S hS} (i : X ⟶ X') :
    (∃ n : ℕ, (MorphismProperty.inverseImage (thickOrder.{u} n)
      (BigFppfOver.toScheme B S hS)).presheaf i.hom) ↔
      IsThickeningHom B S hS i ∧
        IsFiniteOrderThickening B S hS X' (Subfunctor.range i.hom) := by
  simp only [presheaf_thickOrder_iff_isThickeningHom_and_isNthOrderThickening,
    IsFiniteOrderThickening, exists_and_left]

/-- **A morphism identified with a finite-order thickening subspace has finite-order thickenings
as scheme base changes.** Let `G` be a finite-order thickening of an algebraic space `X'`
(Stacks 05ZK, part (3)) and let `i : X ⟶ X'` be the composite of an isomorphism `X ≅ G` with the
inclusion of `G`. Then for some `n` every base change of `i` to a scheme is an `n`th-order
thickening of schemes. -/
theorem exists_presheaf_thickOrder_of_isFiniteOrderThickening {X X' : AlgebraicSpaces B S hS}
    (G : Subfunctor X'.1) (hG : IsFiniteOrderThickening B S hS X' G) (e : X.1 ≅ G.toFunctor)
    (i : X ⟶ X') (hi : e.hom ≫ G.ι = i.hom) :
    ∃ n : ℕ, (MorphismProperty.inverseImage (thickOrder.{u} n)
      (BigFppfOver.toScheme B S hS)).presheaf i.hom := by
  obtain ⟨n, hn⟩ := hG
  exact ⟨n, hi ▸ MorphismProperty.RespectsIso.precomp _ e.hom G.ι
    (presheaf_thickOrder_ι_of_isNthOrderThickening B S hS hn)⟩

end AlgebraicGeometry.Space

end
