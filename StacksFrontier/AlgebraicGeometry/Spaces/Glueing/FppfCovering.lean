module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SheafCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SmallSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.KernelPair

/-!
# Recognizing covering sieves and locally surjective maps on a big fppf site

Zariski open coverings are fppf coverings, so a jointly surjective family of open immersions
generates a covering sieve of a big fppf site. Conversely, a point of an object of the slice
over a scheme is in the image of some member of any covering sieve of it.
These facts turn the relative properties `surjective` and `étale` of a representable
transformation of presheaves into local surjectivity for the fppf topology, and back.

## Main results

* `AlgebraicGeometry.Space.open_cover_mem_bigFppf_topology`: a jointly surjective family of
  open immersions generates a covering sieve.
* `AlgebraicGeometry.Space.exists_preimage_of_covering_sieve`: every point of the target of a
  covering sieve is hit by one of its arrows.
* `AlgebraicGeometry.Space.surjective_of_representable_locallySurjective` and
  `AlgebraicGeometry.Space.isLocallySurjective_of_surjective_etale` relate the relative
  properties to local surjectivity.
* `AlgebraicGeometry.Space.open_cover_indexed_by_points` chooses, for every point of an
  object over a presheaf covered by a coproduct of open subfunctors, a summand whose base
  change covers that point.

## Implementation notes

A covering family of the chosen bounded system is recovered from an arbitrary fppf covering
by `AlgebraicGeometry.BigFppfSite.fppf_has_representative`, which only gives a
combinatorially equivalent family; the two have the same associated presieve, which is what
the topology sees. To pass between the site and its slice, the sieve is transported along
`CategoryTheory.Sieve.overEquiv`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u})

/-- A jointly surjective family of open immersions into an object of a big fppf site
generates a covering sieve: it is a Zariski, hence fppf, covering. -/
theorem open_cover_mem_bigFppf_topology {X : Scheme.{u}} (hX : B.Contains X)
    {I : Type u} (Y : I → B.Schemes) (f : ∀ i, Y i ⟶ B.obj hX)
    (hopen : ∀ i, AlgebraicGeometry.IsOpenImmersion (B.inclusion.map (f i)))
    (hsurj : ∀ x : B.inclusion.obj (B.obj hX),
      ∃ i y, (B.inclusion.map (f i)).base y = x) :
    Sieve.generate (Presieve.ofArrows Y f) ∈ B.topology (B.obj hX) := by
  let E₀ : PreZeroHypercover.{u} (B.obj hX) := ⟨I, Y, f⟩
  let E : Covering.{u + 1, u, u + 1} B.Schemes :=
    ⟨B.obj hX, E₀.reindex Equiv.ulift.{u + 1, u}⟩
  have hz : (E.2.map B.inclusion).presieve₀ ∈
      Scheme.zariskiPrecoverage (B.inclusion.obj E.1) := by
    rw [Scheme.ofArrows_mem_precoverage_iff (P := @AlgebraicGeometry.IsOpenImmersion)]
    refine ⟨fun x => ?_, fun i => hopen i.down⟩
    obtain ⟨i, y, hy⟩ := hsurj x
    exact ⟨ULift.up i, y, hy⟩
  have hfp : IsFppfCovering E := by
    rw [IsFppfCovering, Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map]
    exact Scheme.zariskiPrecoverage_le_fppfPrecoverage _ hz
  obtain ⟨⟨X', E'⟩, hE', hEquiv⟩ := B.fppf_has_representative E hfp
  have hpre : E.2.presieve₀ ∈ B.precoverage E.1 := by
    obtain ⟨hX', hComb⟩ := hEquiv
    dsimp only at hX'
    subst X'
    rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb]
    exact ⟨E', rfl, hE'⟩
  simpa only [E, PreZeroHypercover.presieve₀_reindex] using
    (Precoverage.generate_mem_toGrothendieck hpre)

variable (S : Scheme.{u}) (hS : B.Contains S)

/-- A jointly surjective family of open immersions into an object of the big fppf category over
`S` generates a covering sieve for the localized topology. -/
theorem generate_ofArrows_mem_topology_of_openCover {A : BigFppfOver B S hS}
    {I : Type u} (W : I → BigFppfOver B S hS) (j : ∀ i, W i ⟶ A)
    (hopen : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (j i)))
    (hsurj : ∀ x : (BigFppfOver.toScheme B S hS).obj A,
      ∃ (i : I) (y : (BigFppfOver.toScheme B S hS).obj (W i)),
        ((BigFppfOver.toScheme B S hS).map (j i)).base y = x) :
    Sieve.generate (Presieve.ofArrows W j) ∈ BigFppfOver.topology B S hS A := by
  rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate,
    ← Sieve.overEquiv_generate, Sieve.overEquiv_ofArrows]
  exact open_cover_mem_bigFppf_topology B A.left.2 (fun i ↦ (W i).left) (fun i ↦ (j i).left)
    hopen hsurj

/-- Every point of an object of the big fppf category over `S` is in the image of some arrow
of any covering sieve of that object. -/
theorem exists_preimage_of_covering_sieve
    {T : BigFppfOver B S hS} {R : Sieve T}
    (hR : R ∈ BigFppfOver.topology B S hS T)
    (x : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ (V : BigFppfOver B S hS) (a : V ⟶ T), R a ∧
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map a) := by
  obtain ⟨E, hE, hle⟩ := exists_covering_refining_sieve B ((B.topology.mem_over_iff R).1 hR)
  have hEfp : (E.map B.inclusion).presieve₀ ∈
      Scheme.fppfPrecoverage (B.inclusion.obj T.left) := by
    simpa [IsFppfCovering, PreZeroHypercover.presieve₀_map] using
      B.isFppfCovering_of_isCovering hE
  have _ : Scheme.JointlySurjective Scheme.fppfPrecoverage := by
    unfold Scheme.fppfPrecoverage
    infer_instance
  obtain ⟨V, a, ⟨i⟩, hx⟩ := Scheme.JointlySurjective.exists_eq _ hEfp x
  let W : BigFppfOver B S hS := Over.mk (E.f i ≫ T.hom)
  let b : W ⟶ T := Over.homMk (E.f i)
  exact ⟨W, b, (Sieve.overEquiv_iff R (E.f i)).1 (hle _ _ ⟨i⟩), hx⟩

/-- If a section `z` of a representably related presheaf maps to the pullback of `g` along `a`,
then the point `a v` lies in the image of the base change of `g`. -/
private theorem mem_range_snd_of_app_eq
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hrep : yoneda.relativelyRepresentable f) {T V : BigFppfOver B S hS}
    (g : yoneda.obj T ⟶ G) (a : V ⟶ T) (z : F.obj (Opposite.op V))
    (hz : f.app _ z = G.map a.op (yonedaEquiv g)) (v : (BigFppfOver.toScheme B S hS).obj V) :
    (BigFppfOver.toScheme B S hS).map a v ∈
      Set.range ((BigFppfOver.toScheme B S hS).map (hrep.snd g)) := by
  let b : yoneda.obj V ⟶ F := yonedaEquiv.symm z
  have hb : b ≫ f = yoneda.map a ≫ g := by
    apply yonedaEquiv.injective
    simpa [b, yonedaEquiv_comp, yonedaEquiv_naturality] using hz
  refine ⟨((BigFppfOver.toScheme B S hS).map (hrep.lift b a hb)) v, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hrep.lift_snd]

/-- A representable transformation of presheaves on the big fppf site over `S` which is
locally surjective is surjective after every representable base change. -/
theorem surjective_of_representable_locallySurjective
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hrep : yoneda.relativelyRepresentable f)
    (hloc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f := by
  have _ := hloc
  let P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have _ : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  apply MorphismProperty.relative_of_snd (P := P) hrep
  refine fun T g ↦ ⟨fun x ↦ ?_⟩
  obtain ⟨V, a, ⟨z, hz⟩, v, hv⟩ := exists_preimage_of_covering_sieve B S hS
    (Presheaf.imageSieve_mem (BigFppfOver.topology B S hS) f (yonedaEquiv g)) x
  rw [← hv]
  exact mem_range_snd_of_app_eq B S hS hrep g a z hz v

/-- A transformation of presheaves on the big fppf site over `S` which is surjective and
étale after every representable base change is locally surjective. -/
theorem isLocallySurjective_of_surjective_etale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f := by
  refine ⟨fun {T} y => ?_⟩
  let ξ : yoneda.obj T ⟶ G := yonedaEquiv.symm y
  let q := hs.rep.snd ξ
  have hcover : Sieve.generate (Presieve.singleton q) ∈
      BigFppfOver.topology B S hS T := by
    rw [BigFppfOver.topology, B.topology.mem_over_iff, Sieve.overEquiv_generate,
      ← Sieve.arrows_generate_map_eq_functorPushforward, Sieve.generate_sieve,
      Presieve.map_singleton]
    exact singleton_mem_bigFppf_topology B q.left
      (hs.property_snd ξ) (he.property ξ (hs.rep.fst ξ) q (hs.rep.isPullback ξ))
  apply (BigFppfOver.topology B S hS).superset_covering _ hcover
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨⟩
  refine ⟨yonedaEquiv (hs.rep.fst ξ), ?_⟩
  have hw := congrArg yonedaEquiv (hs.rep.isPullback ξ).w
  rw [← yonedaEquiv_naturality ξ q] at hw
  simpa [ξ, yonedaEquiv_comp] using hw

/-- Given a presheaf covered locally surjectively by a coproduct of representable open
subfunctors, every point of an object mapping to the presheaf lies in the image of the base
change of one of the summands. -/
theorem open_cover_jointly_surjective
    {I : Type v}
    (Fi : I → Sheaf (BigFppfOver.topology B S hS) (Type u))
    (G : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, Fi i ⟶ G) (hc : IsColimit (Cofan.mk G ι))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : G.obj ⟶ F)
    (hloc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) g)
    (hrep : ∀ i, yoneda.relativelyRepresentable ((ι i).hom ≫ g))
    {T : BigFppfOver B S hS} (t : yoneda.obj T ⟶ F)
    (x : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ (i : I), x ∈ Set.range ((BigFppfOver.toScheme B S hS).map ((hrep i).snd t)) := by
  let J := BigFppfOver.topology B S hS
  have _ := hloc
  let A : Subfunctor F := ⨆ i, Subfunctor.range ((ι i).hom ≫ g)
  have hA : A.sieveOfSection (yonedaEquiv t) ∈ J T := by
    apply J.transitive (Presheaf.imageSieve_mem J g (yonedaEquiv t))
    rintro V a ⟨z, hz⟩
    obtain ⟨R, hR, hr⟩ := coproduct_locally_factors Fi G ι hc z
    apply J.superset_covering _ hR
    intro W b hb
    obtain ⟨i, w, hw⟩ := hr b hb
    change F.map (b ≫ a).op (yonedaEquiv t) ∈ A.obj (Opposite.op W)
    rw [Subfunctor.iSup_obj]
    apply Set.mem_iUnion.mpr
    refine ⟨i, w, ?_⟩
    change g.app _ ((ι i).hom.app _ w) = _
    rw [hw, NatTrans.naturality_apply, hz, ← Functor.map_comp_apply]
    rfl
  obtain ⟨V, a, ha, z, hz⟩ := exists_preimage_of_covering_sieve B S hS hA x
  change F.map a.op (yonedaEquiv t) ∈ A.obj (Opposite.op V) at ha
  rw [Subfunctor.iSup_obj] at ha
  obtain ⟨i, w, hw⟩ := Set.mem_iUnion.mp ha
  rw [← hz]
  exact ⟨i, mem_range_snd_of_app_eq B S hS (hrep i) t a w hw z⟩

/-- A choice, for every point of an object over the presheaf, of a summand of the covering
coproduct whose base change covers that point. -/
theorem open_cover_indexed_by_points
    {I : Type v}
    (Fi : I → Sheaf (BigFppfOver.topology B S hS) (Type u))
    (G : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, Fi i ⟶ G) (hc : IsColimit (Cofan.mk G ι))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : G.obj ⟶ F)
    (hloc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) g)
    (hrep : ∀ i, yoneda.relativelyRepresentable ((ι i).hom ≫ g))
    (T : BigFppfOver B S hS) (t : yoneda.obj T ⟶ F) :
    ∃ idx : ((BigFppfOver.toScheme B S hS).obj T) → I,
      ∀ x, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map ((hrep (idx x)).snd t)) := by
  choose idx y hy using fun x =>
    open_cover_jointly_surjective B S hS Fi G ι hc g hloc hrep t x
  exact ⟨idx, fun x => ⟨y x, hy x⟩⟩

end AlgebraicGeometry.Space

end
