module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineSourceEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.InvariantOpenAlongFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.SubobjectEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct

/-!
# Effective descent from a descended hull and an invariant open

`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale B S hS P` asks for the
representability of the descended fibre product whenever the base change of a morphism of sheaves
along a surjective étale morphism `q : c ⟶ a` of the big fppf site of `S` is representable with
`P`. For a property below the monomorphisms the sheaf-theoretic half of that is discharged once a
candidate for the descended object is produced, by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_exists_isPullback`. This file
produces the candidate from a *hull*: an object `o` over `a` whose base change `v` to `c` receives
the datum as an invariant open immersion.

That is the shape in which effective descent for quasi-affine morphisms is proved. Over an affine
base a quasi-affine morphism `z ⟶ c` is a quasi-compact open immersion into the spectrum of the
global sections of `z`, that affine hull inherits the descent datum through flat base change for
global sections, and descending the hull is effective descent for *affine* morphisms. What is left
after that is a descent of invariant opens, and it is unconditional. So the theorem below
isolates the affine half as the only remaining geometric input: its hypothesis
`AlgebraicGeometry.Space.HasDescendedHull` asks for the hull and for nothing about the open
beyond its invariance.

## Main definitions

* `AlgebraicGeometry.Space.HasDescendedHull`: the hypothesis that every descent datum over an
  affine base, with affine chart, is an invariant open immersion into the base change of some
  object over the base.

## Main results

* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_hasDescendedHull`: for a
  property of morphisms of schemes below the monomorphisms, stable under base change and
  satisfying fppf descent, that hypothesis implies effective descent along the surjective étale
  morphisms of the site.

## Implementation notes

*Where each ingredient enters.* The base and the chart are made affine, and the chart quasi-
compact, by the theorem
`isEffectiveDescentAlongSurjectiveEtale_of_affineBase_affineSource`; the quasi-compactness is
what makes the chart an fpqc covering and so is what the descent of opens needs. The invariant
open is descended to an open `W` of the hull by
`AlgebraicGeometry.exists_opens_isPullback_of_preimage_eq_opensRange`, which is Stacks 03N0. That
open is an object of the site by `AlgebraicGeometry.exists_restrict_bigFppfOver`, and the same
statement's universal property lifts the Cartesian leg from schemes to a morphism of the site —
the image of the datum lands in `W` because the datum *is* the inverse image of `W`. The property
`P` of the descended inclusion is then fppf descent of `P` applied to that Cartesian square,
since an étale surjection is flat, surjective and locally of finite presentation.

*Why the hypothesis mentions no gluing isomorphism.* The datum is presented as a Cartesian square
of presheaves, so the two base changes of the datum to `c ×_a c` are base changes of one morphism
of presheaves along one morphism of presheaves and are canonically isomorphic; the invariance of
the open is therefore an equality of opens of `v ×_o v` rather than a compatibility with a chosen
isomorphism.

## References

* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (P : MorphismProperty Scheme.{u})

/-- **Every descent datum is an invariant open of a descended hull.** For a property `P` of
morphisms of schemes, this says: given a morphism `f : X ⟶ Y` of sheaves on the big fppf site of
`S`, a morphism `h : yoneda.obj a ⟶ Y` with `a` affine, a surjective étale quasi-compact
`q : c ⟶ a` with `c` affine, and a presentation `(m, r)` of `A` as the base change of `f` along
`yoneda.map q ≫ h` with `r` representable with `P`, there are an object `o` of the site over `a`,
its base change `v` to `c`, and an open immersion `ι : z ⟶ v` of the site whose image is
invariant for the two projections of `v ×_o v`, such that `A` is represented by `z` over `c`.

This is the hypothesis which effective descent for quasi-affine morphisms consumes as effective
descent for *affine* morphisms: the hull `o` is the descended spectrum of the global sections of
the datum, and the open `ι` is the datum inside it. The invariance of the image is the only
property of the open which is asked for; descending it is then unconditional. -/
def HasDescendedHull : Prop :=
  ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
    ∀ ⦃a c : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (q : c ⟶ a),
      IsAffine ((BigFppfOver.toScheme B S hS).obj a) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj c) →
      Surjective ((BigFppfOver.toScheme B S hS).map q) →
      Etale ((BigFppfOver.toScheme B S hS).map q) →
      QuasiCompact ((BigFppfOver.toScheme B S hS).map q) →
      ∀ ⦃A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (m : A ⟶ X) (r : A ⟶ yoneda.obj c),
        IsPullback m r f (yoneda.map q ≫ h) →
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r →
        ∃ (o v z : BigFppfOver B S hS) (n : o ⟶ a) (w : v ⟶ c) (t : v ⟶ o) (ι : z ⟶ v)
          (V : ((BigFppfOver.toScheme B S hS).obj v).Opens),
          _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ι) ∧
            Set.range ((BigFppfOver.toScheme B S hS).map ι).base = (V : Set _) ∧
            IsPullback ((BigFppfOver.toScheme B S hS).map w)
              ((BigFppfOver.toScheme B S hS).map t) ((BigFppfOver.toScheme B S hS).map q)
              ((BigFppfOver.toScheme B S hS).map n) ∧
            pullback.fst ((BigFppfOver.toScheme B S hS).map t)
                ((BigFppfOver.toScheme B S hS).map t) ⁻¹ᵁ V =
              pullback.snd ((BigFppfOver.toScheme B S hS).map t)
                ((BigFppfOver.toScheme B S hS).map t) ⁻¹ᵁ V ∧
            ∃ e : A ≅ yoneda.obj z, e.hom ≫ yoneda.map (ι ≫ w) = r

variable {B S hS P}

/-- **The descended invariant open of a hull is a Cartesian candidate.** If `ι : z ⟶ v` is an
open immersion of the site whose image `V` is invariant for the two projections of `v ×_o v`, where
`v` is the base change of `o` along a surjective étale quasi-compact `q : c ⟶ a`, then `z` is the
base change along `q` of an open `b` of `o`. -/
private theorem exists_isPullback_of_invariant_opensRange {a c o v z : BigFppfOver B S hS}
    {q : c ⟶ a} {n : o ⟶ a} {w : v ⟶ c} {t : v ⟶ o} {ι : z ⟶ v}
    {V : ((BigFppfOver.toScheme B S hS).obj v).Opens}
    [Surjective ((BigFppfOver.toScheme B S hS).map q)]
    [Etale ((BigFppfOver.toScheme B S hS).map q)]
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map q)]
    [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ι)]
    (hιrange : Set.range ((BigFppfOver.toScheme B S hS).map ι).base = (V : Set _))
    (sqv : IsPullback ((BigFppfOver.toScheme B S hS).map w)
      ((BigFppfOver.toScheme B S hS).map t) ((BigFppfOver.toScheme B S hS).map q)
      ((BigFppfOver.toScheme B S hS).map n))
    (hinv : pullback.fst ((BigFppfOver.toScheme B S hS).map t)
        ((BigFppfOver.toScheme B S hS).map t) ⁻¹ᵁ V =
      pullback.snd ((BigFppfOver.toScheme B S hS).map t)
        ((BigFppfOver.toScheme B S hS).map t) ⁻¹ᵁ V) :
    ∃ (b : BigFppfOver B S hS) (k : z ⟶ b) (i₀ : b ⟶ o),
      IsPullback ((BigFppfOver.toScheme B S hS).map k)
        ((BigFppfOver.toScheme B S hS).map (ι ≫ w))
        ((BigFppfOver.toScheme B S hS).map (i₀ ≫ n)) ((BigFppfOver.toScheme B S hS).map q) := by
  have hιV : ((BigFppfOver.toScheme B S hS).map ι).opensRange = V :=
    TopologicalSpace.Opens.ext (by rw [Scheme.Hom.coe_opensRange, hιrange])
  rw [← hιV] at hinv
  -- descend the invariant open to an open `W` of the hull
  obtain ⟨W, ⟨hWpre, -⟩, ρ, sqW⟩ :=
    exists_opens_isPullback_of_preimage_eq_opensRange sqv
      ((BigFppfOver.toScheme B S hS).map ι) hinv
  -- the open is an object of the site
  obtain ⟨b, i₀, hi₀open, hi₀range, hi₀lift⟩ := exists_restrict_bigFppfOver o W
  -- the comparison of the object of the site with the open subscheme
  have hrange : Set.range ((BigFppfOver.toScheme B S hS).map i₀).base = Set.range W.ι.base := by
    rw [hi₀range, W.range_ι]
  let eb : (BigFppfOver.toScheme B S hS).obj b ≅ W.toScheme :=
    IsOpenImmersion.isoOfRangeEq ((BigFppfOver.toScheme B S hS).map i₀) W.ι hrange
  have hebfac : eb.hom ≫ W.ι = (BigFppfOver.toScheme B S hS).map i₀ :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange
  -- the datum lands in the open, so its structure morphism factors through the object `b`
  have hsub : Set.range ((BigFppfOver.toScheme B S hS).map (ι ≫ t)) ⊆ (W : Set _) := by
    rintro x ⟨y, rfl⟩
    have hy : ((BigFppfOver.toScheme B S hS).map ι).base y ∈
        ((BigFppfOver.toScheme B S hS).map t) ⁻¹ᵁ W := by
      rw [hWpre]
      exact ⟨y, rfl⟩
    simpa [Functor.map_comp] using hy
  obtain ⟨k, hk⟩ := hi₀lift (ι ≫ t) hsub
  -- the lift agrees with the Cartesian leg produced by the descent of opens
  have hkeb : (BigFppfOver.toScheme B S hS).map k ≫ eb.hom = ρ := by
    refine (cancel_mono W.ι).1 ?_
    rw [Category.assoc, hebfac, ← Functor.map_comp, hk, Functor.map_comp, sqW.w]
  -- the two squares paste to the Cartesian square of the candidate
  have hpaste : IsPullback ρ
      ((BigFppfOver.toScheme B S hS).map ι ≫ (BigFppfOver.toScheme B S hS).map w)
      (W.ι ≫ (BigFppfOver.toScheme B S hS).map n) ((BigFppfOver.toScheme B S hS).map q) :=
    sqW.paste_vert sqv.flip
  have csq : IsPullback ((BigFppfOver.toScheme B S hS).map k)
      ((BigFppfOver.toScheme B S hS).map (ι ≫ w))
      ((BigFppfOver.toScheme B S hS).map (i₀ ≫ n)) ((BigFppfOver.toScheme B S hS).map q) := by
    refine hpaste.of_iso (Iso.refl _) eb.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ (by simp)
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
      rw [← hkeb, Category.assoc, eb.hom_inv_id, Category.comp_id]
    · simp
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, Functor.map_comp]
      rw [← hebfac, Category.assoc, Iso.inv_hom_id_assoc]
  exact ⟨b, k, i₀, csq⟩

/-- **The property of a representing morphism.** If `r : A ⟶ yoneda.obj c` is representable with
`P` and `A` is represented by `z` over `c` through `g : z ⟶ c`, then `g` has `P`. -/
private theorem prop_map_of_iso_hom_comp_yoneda_map [P.IsStableUnderBaseChange]
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z c : BigFppfOver B S hS} {g : z ⟶ c}
    {r : A ⟶ yoneda.obj c} (e : A ≅ yoneda.obj z) (he : e.hom ≫ yoneda.map g = r)
    (hr : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r) :
    P ((BigFppfOver.toScheme B S hS).map g) := by
  have _hri : MorphismProperty.RespectsIso
      (MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B S hS))) :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).respectsIso
  subst he
  exact (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS P g).1
    ((MorphismProperty.cancel_left_of_respectsIso
      (MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B S hS))) e.hom
      (yoneda.map g)).1 hr)

/-- **Effective descent along the surjective étale morphisms of the site, from a descended hull
and a descent of invariant opens.** Let `P` be a property of morphisms of schemes which is below
the monomorphisms, stable under base change and satisfies fppf descent. If every descent datum
over an affine base is an invariant open immersion into the base change of an object over that
base — `AlgebraicGeometry.Space.HasDescendedHull` — then morphisms with `P` descend effectively
along the surjective étale morphisms of the big fppf site of `S`.

The open is cut out of the hull by Stacks 03N0, which is where the quasi-compactness of the chart
is spent, and the resulting open subscheme of the hull is the candidate for the descended object
which `AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_le_monomorphisms`
consumes. -/
theorem isEffectiveDescentAlongSurjectiveEtale_of_hasDescendedHull [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (hPmono : P ≤ MorphismProperty.monomorphisms Scheme.{u})
    (H : HasDescendedHull B S hS P) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS P := by
  have _hPri : MorphismProperty.RespectsIso P :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine isEffectiveDescentAlongSurjectiveEtale_of_affineBase_affineSource ?_
  intro X Y f hX hY a c h q ha hc hqs hqe hqqc A m r sq hr
  obtain ⟨o, v, z, n, w, t, ι, V, hιopen, hιrange, sqv, hinv, e, he⟩ :=
    H f hX hY h q ha hc hqs hqe hqqc m r sq hr
  obtain ⟨b, k, i₀, csq⟩ := exists_isPullback_of_invariant_opensRange hιrange sqv hinv
  have hQq : (@Surjective.{u} ⊓ @Flat ⊓ @LocallyOfFinitePresentation :
      MorphismProperty Scheme.{u}) ((BigFppfOver.toScheme B S hS).map q) :=
    ⟨⟨hqs, inferInstance⟩, inferInstance⟩
  exact presheaf_pullback_snd_of_isPullback_of_le_monomorphisms hPmono hX hY sq hr hqs hqe
    (MorphismProperty.DescendsAlong.of_isPullback csq.flip hQq
      (prop_map_of_iso_hom_comp_yoneda_map e he hr)) csq e he

end AlgebraicGeometry.Space

end
