module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteGluingBySize
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingInSite

/-!
# Conditions (1) and (2) of Stacks 03ZQ for finite morphisms, with no hypothesis

`AlgebraicGeometry.Space.isFinite_iff_representable` identifies finiteness of a morphism of
algebraic spaces over `S` with relative representability plus finiteness of the represented base
changes, for a morphism *already known* to be relatively representable. By
`AlgebraicGeometry.Space.isFinite_iff_representable_iff` the whole of the remaining content is the
single implication that a finite morphism of algebraic spaces is relatively representable. This
file proves that implication for a morphism between fppf sheaves, and so states the equivalence
with no representability hypothesis.

The proof is the glueing step. Relative representability has to be checked over an arbitrary
object `U` of the big fppf site, while `AlgebraicGeometry.Space.IsFinite` tests only the *affine*
objects. The fibre product is therefore covered by the base changes over the affine opens of `U`,
and those are representable by the very definition of finiteness; the representing objects are
glued.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isStableUnderBaseChange_openImmersions`: open immersions of the site
  are stable under base change.
* `AlgebraicGeometry.Space.presheaf_openImmersions_yoneda_map`: the image under
  `CategoryTheory.yoneda` of an open immersion of the site is a relatively representable open
  immersion of presheaves.
* `AlgebraicGeometry.Space.sieve_ofArrows_openObjHom_mem_topology` and
  `AlgebraicGeometry.Space.sheafify_iSup_range_yoneda_map_openObjHom`: the affine opens of an
  object of the site cover it, as a sieve and as a family of subfunctors of the presheaf it
  represents.
* `AlgebraicGeometry.Space.relativelyRepresentable_of_isFinite`: **a finite morphism of algebraic
  spaces between fppf sheaves is relatively representable.** This is the implication which
  `AlgebraicGeometry.Space.isFinite_iff_representable_iff` isolates.

## Implementation notes

The glueing theorem used is
`AlgebraicGeometry.Space.isRepresentable_of_locally_covering_of_le_power`, whose hypothesis is a
*uniform* bound `size T ^ ℵ₀` on the index type and on every chart, for a single object `T` of
the site. Taking `T` to be `U` itself, both hypotheses hold: the affine opens
of `U` are bounded by `U.size` by `AlgebraicGeometry.Scheme.mk_affineOpens_le_size`, and each chart
is finite over an open subscheme of `U`, hence bounded by `U.size` through
`AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact` and
`AlgebraicGeometry.Scheme.size_coe_opens_le`. A bound on the *number* of charts is not available
and not needed: the cutoff is a strong prelimit. The older
`AlgebraicGeometry.Space.isRepresentable_of_locally_covering`, whose hypothesis
`#I < B.cutoff.ord.cof` is on the index type, does not apply, since the affine opens of `U` are
bounded only by `B.cutoff`.

This is also the exact point at which the argument does not transpose to the integral case: an
integral morphism is neither locally of finite type nor a monomorphism, so no size bound on the
representing object of an affine base change is available, and
`AlgebraicGeometry.Space.isIntegralHom_iff_representable` keeps its hypothesis.

Both `AlgebraicGeometry.IsAlgebraicSpace` hypotheses are used, through their sheaf clause only:
the fibre product being glued must be a sheaf, and it is formed from the source, the target and a
representable, so both of the first two have to be sheaves. The main lemma is therefore stated
with the two sheaf conditions rather than with the full predicate.

`AlgebraicGeometry.Space.isStableUnderBaseChange_openImmersions` is proved here rather than
assumed: instance search does not find it, because `AlgebraicGeometry.Space.openImmersionOver` is
an inverse image and stability under base change for an inverse image needs the functor to
preserve fibre products. It is exactly what `CategoryTheory.MorphismProperty.relative_map`
consumes to turn an open immersion of the site into a relatively representable open immersion of
presheaves.

Every implicit argument of
`AlgebraicGeometry.Space.isRepresentable_of_locally_covering_of_le_power` is supplied explicitly
at its one use site. Leaving the index type, the covered presheaf and the family of sources to be
inferred from the covering family makes the elaborator spend more than the default heartbeat
budget on a single `isDefEq`; naming them costs nothing and the application is then immediate.

## References

* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 02WR](https://stacks.math.columbia.edu/tag/02WR)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Open immersions of the site -/

/-- **Open immersions of the big fppf site over `S` are stable under base change.** The functor
to schemes preserves fibre products, and open immersions of schemes are stable under base change.

This is not found by instance search: `AlgebraicGeometry.Space.openImmersionOver` is an inverse
image, and an inverse image inherits stability under base change only from a functor which
preserves the fibre products involved. -/
@[ega "IV 2.7.1" "(x)"]
theorem isStableUnderBaseChange_openImmersions :
    (openImmersionOver B S hS).IsStableUnderBaseChange where
  of_isPullback {_ _ _ _ _ _ _ g'} sq hg := by
    have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
    change _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map g')
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (sq.map (BigFppfOver.toScheme B S hS)) hg

/-- **An open immersion of the site represents an open immersion of presheaves.** The image under
`CategoryTheory.yoneda` of an open immersion of the big fppf site over `S` is relatively
representable with open-immersion represented base changes, so it is an admissible member of a
covering family for the glueing theorems. -/
theorem presheaf_openImmersions_yoneda_map {A U : BigFppfOver B S hS} (m : A ⟶ U)
    (hm : openImmersionOver B S hS m) :
    (openImmersionOver B S hS).presheaf (yoneda.map m) := by
  have _ := B.hasPullbacks_schemes
  have _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have _ := isStableUnderBaseChange_openImmersions B S hS
  exact MorphismProperty.relative_map hm

/-! ### The affine opens of an object cover it -/

/-- The inclusion of an affine open of `U` is an open immersion of schemes. -/
private theorem isOpenImmersion_map_openObjHom (U : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj U).affineOpens) :
    _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (openObjHom B S hS U V.1)) := by
  have hoi : _root_.AlgebraicGeometry.IsOpenImmersion (V.1).ι := inferInstance
  rw [toScheme_map_openObjHom]
  exact hoi

/-- **The affine opens of an object of the site generate a covering sieve.** The inclusions
`AlgebraicGeometry.Space.openObjHom` of the affine opens of `U` are open immersions and are
jointly surjective, so they cover `U` for the fppf topology of the site. -/
theorem sieve_ofArrows_openObjHom_mem_topology (U : BigFppfOver B S hS) :
    Sieve.ofArrows (fun V : ((BigFppfOver.toScheme B S hS).obj U).affineOpens =>
        openObj B S hS U V.1) (fun V => openObjHom B S hS U V.1) ∈
      BigFppfOver.topology B S hS U := by
  refine BigFppfOver.sieve_ofArrows_mem_topology_of_jointlySurjective B S hS _ U _
    (fun V => ?_) (fun y => ?_)
  · exact isOpenImmersion_map_openObjHom B S hS U V
  · obtain ⟨V, hV⟩ : ∃ V : ((BigFppfOver.toScheme B S hS).obj U).affineOpens, y ∈ V.1 :=
      TopologicalSpace.Opens.mem_iSup.mp
        (by rw [iSup_affineOpens_eq_top ((BigFppfOver.toScheme B S hS).obj U)]; trivial)
    have hr : y ∈ Set.range (V.1).ι.base := by
      rw [show Set.range (V.1).ι.base = (V.1 : Set _) from (V.1).range_ι]
      exact hV
    refine ⟨V, ?_⟩
    rw [toScheme_map_openObjHom]
    exact hr

/-- **The affine opens of an object cover the presheaf it represents.** The ranges of the
subfunctors cut out by the affine opens of `U` have sheafified supremum all of `yoneda.obj U`:
a morphism to `U` factors through one of the affine opens after restriction along the covering
sieve they generate. This is the covering hypothesis of the glueing step of Stacks 02WR. -/
theorem sheafify_iSup_range_yoneda_map_openObjHom (U : BigFppfOver B S hS) :
    (⨆ V : ((BigFppfOver.toScheme B S hS).obj U).affineOpens,
        Subfunctor.range (yoneda.map (openObjHom B S hS U V.1))).sheafify
      (BigFppfOver.topology B S hS) = ⊤ := by
  rw [eq_top_iff]
  intro W t _
  change (⨆ V : ((BigFppfOver.toScheme B S hS).obj U).affineOpens,
      Subfunctor.range (yoneda.map (openObjHom B S hS U V.1))).sieveOfSection t ∈
    BigFppfOver.topology B S hS (unop W)
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    ((BigFppfOver.topology B S hS).pullback_stable t
      (sieve_ofArrows_openObjHom_mem_topology B S hS U))
  rintro Z g ⟨_, a, _, ⟨V⟩, hfac⟩
  change (yoneda.obj U).map g.op t ∈ _
  rw [Subfunctor.iSup_obj]
  exact Set.mem_iUnion.2 ⟨V, a, hfac⟩

/-! ### Representability of a finite morphism -/

/-- **A finite morphism of algebraic spaces is relatively representable.** For a morphism `f`
between fppf sheaves on the big fppf site over `S`, `AlgebraicGeometry.Space.IsFinite` already
implies `CategoryTheory.Functor.relativelyRepresentable f`, the hypothesis of
`AlgebraicGeometry.Space.isFinite_iff_representable`.

Finiteness represents the base change of `f` over every *affine* object of the site. Over an
arbitrary object `U` the fibre product is covered by its base changes over the affine opens of
`U`, which are representable for that reason; the representing objects are glued by
`AlgebraicGeometry.Space.isRepresentable_of_locally_covering_of_le_power`, whose cardinal
hypotheses hold with `U` itself as the bounding object because each chart is finite over an open
subscheme of `U`. -/
theorem relativelyRepresentable_of_isFinite
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hXs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hYs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hfin : IsFinite B S hS f) :
    yoneda.relativelyRepresentable f := by
  classical
  have _ : (BigFppfOver.topology B S hS).Subcanonical := BigFppfOver.subcanonical B S hS
  have _ := B.hasPullbacks_schemes
  have _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  rw [yoneda_relativelyRepresentable_iff_pullback_representable]
  intro U ξ₀
  set ξ : yoneda.obj U ⟶ Y := yonedaEquiv.symm ξ₀ with hξ
  -- the fibre product, formed in the category of sheaves and read in presheaves
  let Xs : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨X, hXs⟩
  let Ys : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨Y, hYs⟩
  let fs : Xs ⟶ Ys := ⟨f⟩
  let ξs : (BigFppfOver.topology B S hS).yoneda.obj U ⟶ Ys := ⟨ξ⟩
  let H := pullback ξs fs
  let fstH : H.obj ⟶ yoneda.obj U := (pullback.fst ξs fs).hom
  let sndH : H.obj ⟶ X := (pullback.snd ξs fs).hom
  have hH : IsPullback fstH sndH ξ f :=
    (IsPullback.of_hasPullback ξs fs).map
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u))
  -- over an affine open of `U` the fibre product is represented, by a scheme no larger than `U`
  have hdata : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).affineOpens,
      ∃ (Z : BigFppfOver B S hS) (p₀ : yoneda.obj Z ⟶ H.obj)
        (q₀ : yoneda.obj Z ⟶ yoneda.obj (openObj B S hS U V.1)),
        IsPullback p₀ q₀ fstH (yoneda.map (openObjHom B S hS U V.1)) ∧
          ((BigFppfOver.toScheme B S hS).obj Z).size ≤
            ((BigFppfOver.toScheme B S hS).obj U).size ^ ℵ₀ := by
    intro V
    obtain ⟨Z, p, _, _, hfZ, hpb⟩ := hfin (openObj B S hS U V.1) V.2
      (yoneda.map (openObjHom B S hS U V.1) ≫ ξ)
    refine ⟨Z, _, _, hpb.of_right' hH.flip, ?_⟩
    have _ := hfZ
    have _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map p) := inferInstance
    have _ : QuasiCompact ((BigFppfOver.toScheme B S hS).map p) := inferInstance
    exact ((Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact
          ((BigFppfOver.toScheme B S hS).map p)).trans
        (Scheme.size_coe_opens_le ((BigFppfOver.toScheme B S hS).obj U) V.1)).trans
      (Cardinal.self_le_power _ one_le_aleph0)
  choose W p q hp hsize using hdata
  have hopen : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).affineOpens,
      (openImmersionOver B S hS).presheaf (yoneda.map (openObjHom B S hS U V.1)) := by
    intro V
    exact presheaf_openImmersions_yoneda_map B S hS _ (isOpenImmersion_map_openObjHom B S hS U V)
  have hrep : H.obj.IsRepresentable :=
    isRepresentable_of_locally_covering_of_le_power B S hS
      (K := yoneda.obj U)
      (I := ((BigFppfOver.toScheme B S hS).obj U).affineOpens)
      (Ci := fun V => yoneda.obj (openObj B S hS U V.1))
      (fun V => yoneda.map (openObjHom B S hS U V.1))
      (sheafify_iSup_range_yoneda_map_openObjHom B S hS U) hopen H fstH
      (X := W) p q hp (T := (BigFppfOver.toScheme B S hS).obj U) U.left.property
      ((Scheme.mk_affineOpens_le_size _).trans (Cardinal.self_le_power _ one_le_aleph0))
      hsize
  have _ := hrep
  exact isRepresentable_of_natIso H.obj hH.isoPullback


end AlgebraicGeometry.Space

end
