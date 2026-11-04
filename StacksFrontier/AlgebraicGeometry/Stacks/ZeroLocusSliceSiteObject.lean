module

public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceSiteObject
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingRegularSequence

/-!
# The slice of Stacks 06MD on a representable chart is a scheme of the site

Let `U₀` be a scheme of the big fppf site of `S`, let `ρ : yoneda.obj U₀ ≅ U` present an
algebraic space `U` over `S` as the functor of points of `U₀`, let `c₁, …, c_r` be global
regular functions on `U` and let `V ⊆ U` be an open subspace in the sense of **Stacks 02YU**,
part (2). The slice that **Stacks 06MD** makes flat and locally of finite presentation over an
algebraic stack is `V(c₁, …, c_r) ∩ V`, the subfunctor
`AlgebraicGeometry.Stack.zeroLocusOnOpen` of `V`. This file shows that slice is itself the
functor of points of an **object of the site**, through a morphism into `U₀` which is a
monomorphism and an immersion of schemes, and of size at most `2 ^ 2 ^ size U₀`.

The chart of **Stacks 06FX**,
`AlgebraicGeometry.Stack.exists_isClosed_smoothChart_size_le_of_isFiniteTypePoint`, is a scheme
of the site, so the hypothesis is met there with `ρ = Iso.refl _`; the size bound is the one
`AlgebraicGeometry.BigFppfSite.contains_sigma_of_forall_size_le` asks of a family of such slices
for its coproduct to lie in the site, and it is the same `2 ^ 2 ^ size U₀` as in
`AlgebraicGeometry.Space.exists_siteObject_iso_mono_of_isOpenSubspace` and in
`AlgebraicGeometry.Stack.exists_siteObject_toScheme_map_eq_size_le`.

## Main results

* `AlgebraicGeometry.Space.exists_siteObject_iso_of_presheaf`: a subfunctor of a representable
  presheaf whose inclusion is representable by a class of morphisms of the site is the functor
  of points of an object of the site, through a morphism of that class.
* `AlgebraicGeometry.Stack.exists_siteObject_iso_mono_zeroLocusOnOpen`: the slice of
  **Stacks 06MD** over a representable chart, as a scheme of the site with a monomorphism into
  the chart.

## Implementation notes

The slice is reached in two steps, one for each half of its construction. The open subspace `V`
is a scheme `V₀` of the site over `U₀` by
`AlgebraicGeometry.Space.exists_siteObject_iso_mono_of_isOpenSubspace`, which also supplies the
comparison isomorphism `yoneda.obj V₀ ≅ V.toFunctor`; and `V(c₁, …, c_r) ∩ V` is a **closed**
subspace of `V` by **Stacks 083Q**
(`AlgebraicGeometry.Stack.isClosedSubspace_zeroLocusOnOpen`), so base-changing its inclusion
along that comparison isomorphism presents it as a scheme `Z₀` of the site over `V₀`.

That second step is the first statement below, which is the argument of
`AlgebraicGeometry.Space.exists_isOpenImmersion_iso_of_isOpenImmersion_ι` with the class of
morphisms of schemes left free: being representable by morphisms of a class is what is used, and
nothing about open immersions. It is stated for a class of morphisms of the *site* rather than
for an inverse image of a class of morphisms of schemes, so that the closed-immersion instance
below reads it at `AlgebraicGeometry.Space.IsClosedImmersion` with no unfolding.

The morphism into `U₀` is the composite `Z₀ ⟶ V₀ ⟶ U₀` of a closed immersion with an open
immersion, hence an immersion of schemes
(`AlgebraicGeometry.IsImmersion.comp`), hence a monomorphism of schemes, hence — the functor to
schemes being faithful — a monomorphism of the site. That monomorphism of schemes is what the
size estimate `AlgebraicGeometry.size_le_of_mono_double_power` consumes, and it is also what
`AlgebraicGeometry.BigFppfSite.contains_of_mono` consumes, so a consumer needing the slice as an
object of the site over `U₀` has it directly. Both factors are returned alongside the composite:
`AlgebraicGeometry.IsPreimmersion` of the composite, which the unramifiedness criterion of
**Stacks 02GF** reads at a slice, follows from the immersion, and the factorisation through `V₀`
is what identifies the slice with the zero scheme of the restricted functions on `V₀`.

No `@[stacks]` attribute is claimed. **Stacks 02YU**, parts (2) and (4) are the definitions of
open and closed subspaces and already sit on `AlgebraicGeometry.Space.IsOpenSubspace` and
`AlgebraicGeometry.Space.IsClosedSubspace`; **Stacks 06MD** sits on
`Stack.exists_openSubspace_isFlat_isLocallyOfFinitePresentation_zeroLocus_of_isRegular`. What
is proved here is the unlabelled consequence of those definitions for a representable
ambient chart, together with the size estimate, which is not part of any source statement.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Theorem 101.21.6 (Tag 06N3)](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A subfunctor of a representable presheaf whose inclusion is representable by a class of
morphisms of the site is the functor of points of an object of the site.** Base-changing the
inclusion along a representing isomorphism `r : yoneda.obj T ≅ F` presents the subfunctor as the
functor of points of an object `V` of the site, through a morphism `V ⟶ T` of the class which
realizes the inclusion.

This is `AlgebraicGeometry.Space.exists_isOpenImmersion_iso_of_isOpenImmersion_ι` with the class
left free; at the class of closed immersions it reads a closed subspace of a representable
algebraic space as a scheme of the site. -/
theorem exists_siteObject_iso_of_presheaf (Q : MorphismProperty (BigFppfOver B S hS))
    {T : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (r : yoneda.obj T ≅ F)
    (W : Subfunctor F) (hW : Q.presheaf W.ι) :
    ∃ (V : BigFppfOver B S hS) (s : V ⟶ T), Q s ∧
      ∃ e : yoneda.obj V ≅ W.toFunctor, e.hom ≫ W.ι = yoneda.map s ≫ r.hom := by
  have hpb := hW.rep.isPullback r.hom
  have _ : IsIso (hW.rep.fst r.hom) := hpb.isIso_fst_of_isIso
  exact ⟨hW.rep.pullback r.hom, hW.rep.snd r.hom, hW.property_snd r.hom,
    asIso (hW.rep.fst r.hom), hpb.w⟩

end Space

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  {r : ℕ}
  (c : Fin r → (SheafOfModules.unit (Space.structureRingSheaf B S hS ⟨U, hU⟩)).sections)

/-- **The slice of Stacks 06MD over a representable chart is a scheme of the site carrying a
monomorphism into the chart.** Let `ρ : yoneda.obj U₀ ≅ U` present the algebraic space `U` as the
functor of points of a scheme `U₀` of the big fppf site of `S`, let `c₁, …, c_r` be global
regular functions on `U` and let `V ⊆ U` be an open subspace in the sense of **Stacks 02YU**,
part (2). Then there are objects `Z₀` and `V₀` of the site and morphisms `z : Z₀ ⟶ V₀`,
`v : V₀ ⟶ U₀` of the site, together with an isomorphism
`e : yoneda.obj Z₀ ≅ V(c₁, …, c_r) ∩ V`, such that the morphism of schemes underlying `z` is a
closed immersion, that underlying `v` is an open immersion, that underlying `z ≫ v` is an
immersion, `z ≫ v` is a monomorphism of the site, `e` carries the inclusion of the slice into
`U` to `z ≫ v` read through `ρ`, and `size Z₀ ≤ 2 ^ 2 ^ size U₀`.

The chart of **Stacks 06FX** is a scheme of the site, so this applies to it with
`ρ = Iso.refl _`. See the module documentation. -/
theorem exists_siteObject_iso_mono_zeroLocusOnOpen {U₀ : BigFppfOver B S hS}
    (ρ : yoneda.obj U₀ ≅ U) {V : Subfunctor U} (hV : Space.IsOpenSubspace B S hS V) :
    ∃ (Z₀ V₀ : BigFppfOver B S hS) (z : Z₀ ⟶ V₀) (v : V₀ ⟶ U₀)
      (e : yoneda.obj Z₀ ≅ (zeroLocusOnOpen B S hS U hU c V).toFunctor),
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map z) ∧
        _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map v) ∧
          _root_.AlgebraicGeometry.IsImmersion
              ((BigFppfOver.toScheme B S hS).map (z ≫ v)) ∧
            Mono (z ≫ v) ∧
              e.hom ≫ (zeroLocusOnOpen B S hS U hU c V).ι ≫ V.ι =
                  yoneda.map (z ≫ v) ≫ ρ.hom ∧
                ((BigFppfOver.toScheme B S hS).obj Z₀).size ≤
                  (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
                    ((BigFppfOver.toScheme B S hS).obj U₀).size := by
  obtain ⟨V₀, v, e, hvoi, -, hve, -⟩ :=
    Space.exists_siteObject_iso_mono_of_isOpenSubspace B S hS ρ hV
  obtain ⟨Z₀, z, hz, e', he'⟩ :=
    Space.exists_siteObject_iso_of_presheaf B S hS
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))
      e (zeroLocusOnOpen B S hS U hU c V)
      (isClosedSubspace_zeroLocusOnOpen B S hS U hU c V hV).2
  have hzci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map z) := hz
  have hvoi' : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map v) := hvoi
  have himm : _root_.AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map (z ≫ v)) := by
    rw [Functor.map_comp]
    infer_instance
  have hmono : Mono ((BigFppfOver.toScheme B S hS).map (z ≫ v)) := inferInstance
  refine ⟨Z₀, V₀, z, v, e', hzci, hvoi', himm,
    (BigFppfOver.toScheme B S hS).mono_of_mono_map hmono, ?_,
    size_le_of_mono_double_power ((BigFppfOver.toScheme B S hS).map (z ≫ v))⟩
  rw [← Category.assoc, he', Category.assoc, hve, Functor.map_comp, Category.assoc]

end Stack

end AlgebraicGeometry

end
