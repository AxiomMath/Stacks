module

public import StacksFrontier.AlgebraicGeometry.Descent.InvariantOpenAlongFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange

/-!
# A thickening of a chart's clopen decomposition along a morphism to a coproduct

Let `W` be an object of the big fppf category over `S` whose underlying scheme is the coproduct
of the underlying schemes of a family `Z i`, let `t : U ⟶ U'` be a first-order thickening of
affine objects of the site, and let `x : U ⟶ W`. Then `x` decomposes `U` into finitely many open
and closed affine pieces, each mapping into a single summand — this is
`AlgebraicGeometry.BigFppfOver.exists_finite_decomposition_of_hom_coproduct` — and that
decomposition *lifts to `U'`*: the homeomorphism of a thickening carries each piece of `U` to an
open and closed piece of `U'`, affine again, over which `t` restricts to a first-order
thickening.

This is the geometric content of the two conditions "on objects" of **Stacks 06CU** and
**Stacks 06D0** for a scheme-valued point assembled out of a family by
`AlgebraicGeometry.Stack.exists_stackMap_comp_iso_of_isColimit`: an affine test object of the
site mapping to the coproduct need not land in one summand, so neither condition can be read off
a single member of the family, and what replaces that is the finite decomposition produced here,
on which the members' conditions can be applied piece by piece.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_thickened_decomposition_of_hom_coproduct`: the lifted
  decomposition, with both families recorded as disjoint open coverings and with the restricted
  first-order thickenings between them.

## Implementation notes

The thickening is used only through
`Stacks.Thickenings.IsThickening.opensCongr`, the order isomorphism between the opens of the two
schemes that the homeomorphism of a thickening induces. The piece of `U'` matching a piece of `U`
is placed in the site by `AlgebraicGeometry.exists_restrict_bigFppfOver` and receives its
morphism from the piece of `U` by
`AlgebraicGeometry.BigFppfOver.existsUnique_lift_of_isOpenImmersion`, the image condition holding
because the piece of `U` is exactly the inverse image of the piece of `U'`.

That the restricted morphism is again a first-order thickening is **Stacks 09ZU**,
`AlgebraicGeometry.isFirstOrderThickening_of_isPullback`: the square over the piece is Cartesian
by `AlgebraicGeometry.exists_isPullback_of_preimage_eq_opensRange`, which produces it for the
open subscheme, read through the isomorphism between that open subscheme and the object of the
site representing it.

Affineness of a piece of `U'` is `AlgebraicGeometry.isAffine_of_isOpenImmersion_of_isClosed_range`
again: its image is closed because the image of the corresponding piece of `U` is, and a
thickening is a homeomorphism. The closedness of the pieces of `U` is where quasi-compactness of
`U` enters, inside
`AlgebraicGeometry.BigFppfOver.exists_finite_decomposition_of_hom_coproduct`.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 06D0](https://stacks.math.columbia.edu/tag/06D0)
* [Stacks Project, Tag 09ZU](https://stacks.math.columbia.edu/tag/09ZU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

namespace AlgebraicGeometry

universe u

/-- A morphism `g : P ⟶ Q` over `f` between open immersions `p` and `q` is Cartesian when
`f ⁻¹ᵁ V` is the image of `p` and `V` the image of `q`. -/
theorem isPullback_of_preimage_eq_opensRange {X Y P Q : Scheme.{u}} (f : X ⟶ Y) (p : P ⟶ X)
    [IsOpenImmersion p] (q : Q ⟶ Y) [IsOpenImmersion q] {V : Y.Opens}
    (hV : f ⁻¹ᵁ V = p.opensRange) (hq : Set.range q = (V : Set Y)) (g : P ⟶ Q)
    (hg : g ≫ q = p ≫ f) : IsPullback g p q f := by
  obtain ⟨ρ, hρ⟩ := exists_isPullback_of_preimage_eq_opensRange f p hV
  have hrange : Set.range V.ι.base = Set.range q.base := V.range_ι.trans hq.symm
  let ι : V.toScheme ≅ Q := IsOpenImmersion.isoOfRangeEq V.ι q hrange
  have hsq : IsPullback (ρ ≫ ι.hom) p q f :=
    hρ.of_iso (Iso.refl _) ι (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simpa only [Iso.refl_hom, Category.comp_id] using
        (IsOpenImmersion.isoOfRangeEq_hom_fac V.ι _ hrange).symm) (by simp)
  rwa [(cancel_mono q).mp (by rw [hg, hsq.w] : g ≫ q = (ρ ≫ ι.hom) ≫ q)]

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A clopen decomposition cut out by a morphism to a coproduct lifts along a thickening.**
Let the underlying scheme of `W` be the coproduct of the underlying schemes of the `Z i` along
`jj i`, let `t : U ⟶ U'` be a first-order thickening of affine objects of the big fppf category
over `S`, and let `x : U ⟶ W`.

Then there are finitely many pieces `Ua a` of `U` and `Ua' a` of `U'`, each affine and each
included by an open immersion, forming disjoint open coverings of `U` and of `U'` respectively,
together with a first-order thickening `ta a : Ua a ⟶ Ua' a` over `t` and a factorization
`w a : Ua a ⟶ Z (k a)` of `x` restricted to `Ua a` through a single summand. -/
theorem BigFppfOver.exists_thickened_decomposition_of_hom_coproduct
    {I : Type u} {Z : I → BigFppfOver B S hS} {W : BigFppfOver B S hS} (jj : ∀ i, Z i ⟶ W)
    (e : (∐ fun i => (BigFppfOver.toScheme B S hS).obj (Z i)) ≅
      (BigFppfOver.toScheme B S hS).obj W)
    (he : ∀ i, Sigma.ι (fun i => (BigFppfOver.toScheme B S hS).obj (Z i)) i ≫ e.hom =
      (BigFppfOver.toScheme B S hS).map (jj i))
    {U U' : BigFppfOver B S hS} (t : U ⟶ U')
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hU' : IsAffine ((BigFppfOver.toScheme B S hS).obj U'))
    (ht : IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map t))
    (x : U ⟶ W) :
    ∃ (σ : Type u) (_ : Finite σ) (k : σ → I)
      (Ua : σ → BigFppfOver B S hS) (Ua' : σ → BigFppfOver B S hS)
      (p : ∀ a, Ua a ⟶ U) (q : ∀ a, Ua' a ⟶ U') (ta : ∀ a, Ua a ⟶ Ua' a)
      (w : ∀ a, Ua a ⟶ Z (k a)),
      (∀ a, IsAffine ((BigFppfOver.toScheme B S hS).obj (Ua a))) ∧
      (∀ a, IsAffine ((BigFppfOver.toScheme B S hS).obj (Ua' a))) ∧
      (∀ a, IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map (ta a))) ∧
      (∀ a, ta a ≫ q a = p a ≫ t) ∧
      (∀ a, w a ≫ jj (k a) = p a ≫ x) ∧
      (∀ a, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (p a))) ∧
      (∀ y : (BigFppfOver.toScheme B S hS).obj U,
        ∃ a, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p a))) ∧
      (Pairwise fun a b => Disjoint (Set.range ((BigFppfOver.toScheme B S hS).map (p a)))
        (Set.range ((BigFppfOver.toScheme B S hS).map (p b)))) ∧
      (∀ a, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (q a))) ∧
      (∀ y : (BigFppfOver.toScheme B S hS).obj U',
        ∃ a, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (q a))) ∧
      (Pairwise fun a b => Disjoint (Set.range ((BigFppfOver.toScheme B S hS).map (q a)))
        (Set.range ((BigFppfOver.toScheme B S hS).map (q b)))) := by
  classical
  have := hU
  have := hU'
  have hci : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map t) := ht.1
  have hthick : IsThickening ((BigFppfOver.toScheme B S hS).map t) := ht.isThickening
  obtain ⟨σ, hσ, k, Ua, p, w, hpimm, hpclosed, hpcov, hpdisj, -, hpfac⟩ :=
    BigFppfOver.exists_finite_decomposition_of_hom_coproduct jj e he U x
  -- The piece of `U'` matching the `a`-th piece of `U` under the homeomorphism of `t`.
  set V : σ → ((BigFppfOver.toScheme B S hS).obj U').Opens := fun a =>
    hthick.opensCongr ((BigFppfOver.toScheme B S hS).map (p a)).opensRange
  have hpreV : ∀ a, (BigFppfOver.toScheme B S hS).map t ⁻¹ᵁ V a =
      ((BigFppfOver.toScheme B S hS).map (p a)).opensRange := fun a =>
    hthick.preimage_opensCongr _
  have hpreVset : ∀ a, (BigFppfOver.toScheme B S hS).map t ⁻¹'
      ((V a : Set ((BigFppfOver.toScheme B S hS).obj U'))) =
      Set.range ((BigFppfOver.toScheme B S hS).map (p a)) := fun a =>
    congrArg (fun O : ((BigFppfOver.toScheme B S hS).obj U).Opens =>
      (O : Set ((BigFppfOver.toScheme B S hS).obj U))) (hpreV a)
  -- Each piece of `U'` is an object of the site.
  choose Ua' q hqimm hqrange _hquniv using fun a : σ => exists_restrict_bigFppfOver U' (V a)
  have hqrangeV : ∀ a, Set.range ((BigFppfOver.toScheme B S hS).map (q a)) =
      (V a : Set ((BigFppfOver.toScheme B S hS).obj U')) := hqrange
  have himq : ∀ a, Set.range ((BigFppfOver.toScheme B S hS).map (q a)) =
      (BigFppfOver.toScheme B S hS).map t ''
        Set.range ((BigFppfOver.toScheme B S hS).map (p a)) := fun a => by
    rw [hqrangeV a, ← hpreVset a, Set.image_preimage_eq _ hthick.2]
  -- The restriction of `t` to the `a`-th piece.
  have hsub : ∀ a, Set.range ((BigFppfOver.toScheme B S hS).map (p a ≫ t)) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map (q a)) := by
    rintro a _ ⟨z, rfl⟩
    rw [himq a, Functor.map_comp]
    exact ⟨(BigFppfOver.toScheme B S hS).map (p a) z, ⟨z, rfl⟩, (Scheme.Hom.comp_apply _ _ z).symm⟩
  choose ta hta _ using fun a : σ =>
    BigFppfOver.existsUnique_lift_of_isOpenImmersion (q a) (hqimm a) (p a ≫ t) (hsub a)
  refine ⟨σ, hσ, k, Ua, Ua', p, q, ta, w, fun a => ?_, fun a => ?_, fun a => ?_,
    fun a => hta a, hpfac, hpimm, hpcov, hpdisj, hqimm, fun y => ?_, fun a b hab => ?_⟩
  · have := hpimm a
    exact isAffine_of_isOpenImmersion_of_isClosed_range
      ((BigFppfOver.toScheme B S hS).map (p a)) (hpclosed a)
  · have := hqimm a
    refine isAffine_of_isOpenImmersion_of_isClosed_range
      ((BigFppfOver.toScheme B S hS).map (q a)) ?_
    rw [himq a]
    exact hthick.isHomeomorph.isClosedMap _ (hpclosed a)
  · have := hpimm a
    have := hqimm a
    -- The square of the `a`-th piece is Cartesian, so the restriction is a first-order thickening.
    exact isFirstOrderThickening_of_isPullback (isPullback_of_preimage_eq_opensRange _ _ _
      (hpreV a) (hqrangeV a) _ (by rw [← Functor.map_comp, hta a, Functor.map_comp])) ht
  · obtain ⟨z, hz⟩ := hthick.2 y
    obtain ⟨a, ha⟩ := hpcov z
    refine ⟨a, ?_⟩
    rw [himq a, ← hz]
    exact ⟨_, ha, rfl⟩
  · refine Set.disjoint_left.mpr fun y hy hy' => ?_
    rw [himq a] at hy
    rw [himq b] at hy'
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨z', hz', hzz⟩ := hy'
    obtain rfl := ((BigFppfOver.toScheme B S hS).map t).isClosedEmbedding.injective hzz
    exact Set.disjoint_left.mp (hpdisj hab) hz hz'

end AlgebraicGeometry

end
