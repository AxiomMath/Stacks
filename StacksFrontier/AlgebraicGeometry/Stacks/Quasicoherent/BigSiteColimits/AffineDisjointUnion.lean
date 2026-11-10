module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.Localization.InheritedTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv

/-!
# Finite disjoint unions of affine objects

A finite family of affine objects of a category fibred in groupoids over the big fppf site of
schemes over `S` has a disjoint union *inside that category*, over any object the family maps to.
The underlying scheme is the coproduct of the underlying schemes, which is again affine and again
small enough to be an object of the chosen size-bounded category of schemes; the structure morphism
is the morphism the family induces on the coproduct; and the object of the fibred category is a
lift of that morphism along the structure functor, which exists because the functor is fibred in
groupoids.

The disjoint union comes with exactly the data a decomposition statement about the sections of a
presheaf needs: the inclusions of the members are monomorphisms, they generate a covering sieve of
the union, and two members meet only over an object whose empty sieve covers.  The last of these is
the site-level form of disjointness, and it is produced here from the fact that a scheme mapping
into two distinct components of a coproduct is empty, together with the fact that the empty family
is an fppf covering of an empty object.

## Covering families from fppf families

The covering statements rest on one observation about a big fppf site, recorded here as
`AlgebraicGeometry.BigFppfSite.ofArrows_mem_topology`: a family of morphisms *between objects of
the site* whose image in schemes is an fppf covering family generates a covering sieve, with no
cardinality hypothesis on its index type.  The chosen collection of covering families of a big fppf
site is bounded, and the family at hand need not meet that bound; but Stacks 03WX supplies a chosen
family tautologically equivalent to it, whose members therefore factor through members of the given
family, so the sieve the given family generates contains a covering sieve.  This is how the
cardinality bound of `AlgebraicGeometry.BigFppfSite.coveringBound`, which constrains no family
constructed by hand, is kept out of every statement below.

## Main definitions

* `AlgebraicGeometry.FibredSite.FiniteDisjointUnion`: a disjoint union of a family of objects of a
  slice of the associated fppf site, with the inclusions, their monomorphy, the covering condition,
  the site-level disjointness and the affineness of the union.

## Main results

* `AlgebraicGeometry.BigFppfSite.ofArrows_mem_topology`: **a family of morphisms of a big fppf site
  whose image is an fppf covering family generates a covering sieve.**
* `AlgebraicGeometry.BigFppfOver.bot_mem_baseOverTopology`,
  `AlgebraicGeometry.FibredSite.bot_mem_associatedTopology` and
  `AlgebraicGeometry.FibredSite.bot_mem_associatedTopology_over`: **the empty sieve covers an
  object whose underlying scheme is empty**, in the slice and inherited forms. The statement for
  the big fppf site itself is `AlgebraicGeometry.BigFppfSite.bot_mem_topology` in
  `StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties`.
* `AlgebraicGeometry.FibredSite.nonempty_finiteDisjointUnion`: **a finite family of affine objects
  of a slice of the associated fppf site has a disjoint union.**

## Implementation notes

The index type of the family is in the universe of the schemes, because that is what
`AlgebraicGeometry.Scheme.size_sigmaObj_lt` — the size bound for a coproduct of schemes, Stacks
000R (2) — asks for.  A family indexed by `Fin n`, which is what a covering of an affine object is
cut down to, is used at `ULift` of its index type.

The lift of the structure morphism of the coproduct along the structure functor is produced by
`CategoryTheory.Functor.IsFiberedInGroupoids.exists_lift`, and the inclusions of the members by
`CategoryTheory.Functor.IsFiberedInGroupoids.unique_lift`, whose uniqueness clause is also what
makes the inclusions monomorphisms: a morphism of a category fibred in groupoids is determined by
its image and its composite with a fixed morphism.  The equality `p x = D` between the image of the
lift and the coproduct is carried by an `eqToHom`, and never rewritten across a sieve: the covering
sieve of the coproduct is pulled back along that isomorphism instead.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03WX](https://stacks.math.columbia.edu/tag/03WX)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' w v u

namespace CategoryTheory.Sieve

/-- A family of morphisms indexed by an empty type generates the empty sieve. -/
theorem ofArrows_of_isEmpty {C : Type u} [Category.{v} C] {X : C} {I : Type w} [IsEmpty I]
    (Y : I → C) (g : ∀ i, Y i ⟶ X) : Sieve.ofArrows Y g = ⊥ :=
  le_antisymm ((Sieve.generate_le_iff _ _).2 (by rintro Z f ⟨i⟩; exact IsEmpty.elim ‹_› i)) bot_le

end CategoryTheory.Sieve

/-- The empty sieve covers an object of a slice for the slice topology when it covers its source. -/
private theorem bot_mem_over_topology {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {x : C} (W : Over x) (h : (⊥ : Sieve W.left) ∈ J W.left) : (⊥ : Sieve W) ∈ J.over x W := by
  rwa [GrothendieckTopology.mem_over_iff, OrderIso.map_bot]

namespace AlgebraicGeometry.BigFppfSite

/-- **A family of morphisms of a big fppf site whose image in schemes is an fppf covering family
generates a covering sieve.**  No bound on the index type is asked for, although the chosen
covering families of the site are bounded: the sources of the given family are objects of the site
by hypothesis, so Stacks 03WX supplies a chosen covering family tautologically equivalent to it,
each of whose members factors through a member of the given family; the covering sieve that chosen
family generates is therefore contained in the sieve the given family generates. -/
theorem ofArrows_mem_topology (B : BigFppfSite.{u}) (T : B.Schemes)
    {I : Type w} (X : I → B.Schemes) (f : ∀ i, X i ⟶ T)
    (hf : Presieve.ofArrows (fun i => B.inclusion.obj (X i))
        (fun i => B.inclusion.map (f i)) ∈ Scheme.fppfPrecoverage (B.inclusion.obj T)) :
    Sieve.ofArrows X f ∈ B.topology T := by
  obtain ⟨V, hV, htaut⟩ := exists_isCovering_tautologicallyEquivalent_of_sources_iso B T
    ⟨I, fun i => B.inclusion.obj (X i), fun i => B.inclusion.map (f i)⟩ hf
    (fun i => ⟨X i, f i, Iso.refl _, by simp⟩)
  refine B.topology.superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck (R := V.presieve₀) ⟨V, rfl, hV⟩)
  rw [Sieve.generate_le_iff]
  rintro Y g ⟨j⟩
  obtain ⟨β, hβ⟩ := htaut.2
  obtain ⟨e, he⟩ := hβ j
  exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨β j, ObjectProperty.homMk e.hom,
    B.inclusion.map_injective he.symm⟩

end AlgebraicGeometry.BigFppfSite

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A family of morphisms of the big fppf category over `S` whose image in schemes is an fppf
covering family generates a covering sieve** for the localized fppf topology.  The correspondence
between sieves of a slice and sieves of the underlying object reduces this to
`AlgebraicGeometry.BigFppfSite.ofArrows_mem_topology`. -/
theorem ofArrows_mem_baseOverTopology {T : BigFppfOver B S hS} {I : Type w}
    (X : I → BigFppfOver B S hS) (f : ∀ i, X i ⟶ T)
    (hf : Presieve.ofArrows (fun i => (toScheme B S hS).obj (X i))
        (fun i => (toScheme B S hS).map (f i)) ∈
      Scheme.fppfPrecoverage ((toScheme B S hS).obj T)) :
    Sieve.ofArrows X f ∈ baseOverTopology B S hS .fppf T := by
  change Sieve.ofArrows X f ∈ (B.topology.over (B.obj hS)) T
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact B.ofArrows_mem_topology T.left (fun i => (X i).left) (fun i => (f i).left) hf

/-- **The empty sieve covers an object of the big fppf category over `S` whose underlying scheme is
empty.** -/
theorem bot_mem_baseOverTopology (T : BigFppfOver B S hS)
    (hT : IsEmpty ((toScheme B S hS).obj T)) :
    (⊥ : Sieve T) ∈ baseOverTopology B S hS .fppf T := by
  exact bot_mem_over_topology _ T (B.bot_mem_topology T.left hT)

end AlgebraicGeometry.BigFppfOver

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- **A family of morphisms of a category fibred in groupoids whose image generates a covering
sieve generates a covering sieve** for the inherited fppf topology.  Every morphism of a category
fibred in groupoids is strongly cartesian over its image, so the characterisation
`CategoryTheory.Functor.IsInheritedTopology` applies to every family. -/
theorem ofArrows_mem_associatedTopology (hp : p.IsFiberedInGroupoids) {W : 𝒳} {I : Type w'}
    (y : I → 𝒳) (φ : ∀ i, y i ⟶ W)
    (h : Sieve.ofArrows (fun i => p.obj (y i)) (fun i => p.map (φ i)) ∈
      BigFppfOver.baseOverTopology B S hS .fppf (p.obj W)) :
    Sieve.ofArrows y φ ∈ BigFppfOver.associatedTopology B S hS p .fppf W := by
  have hfib : p.IsFibered := hp.isFibered
  exact (Functor.isInheritedTopology_inheritedTopology p
    (BigFppfOver.baseOverTopology B S hS .fppf) y φ
    (fun i => hp.isStronglyCartesian (φ i))).2 h

/-- **The empty sieve covers an object of the associated fppf site whose underlying scheme is
empty.** -/
theorem bot_mem_associatedTopology (hp : p.IsFiberedInGroupoids) (W : 𝒳)
    (hW : IsEmpty ((BigFppfOver.toScheme B S hS).obj (p.obj W))) :
    (⊥ : Sieve W) ∈ BigFppfOver.associatedTopology B S hS p .fppf W := by
  have h := ofArrows_mem_associatedTopology B S hS p hp (W := W)
    (fun i : PEmpty.{1} => (i.elim : 𝒳)) (fun i => i.elim) ?_
  · rwa [Sieve.ofArrows_of_isEmpty] at h
  · rw [Sieve.ofArrows_of_isEmpty]
    exact BigFppfOver.bot_mem_baseOverTopology B S hS (p.obj W) hW

/-- **The empty sieve covers an object of a slice of the associated fppf site whose underlying
scheme is empty.**  This is the hypothesis under which a presheaf of modules has only the zero
section over an object, and so the form in which disjointness of a family of subobjects is
expressed at the level of a site. -/
theorem bot_mem_associatedTopology_over (hp : p.IsFiberedInGroupoids) (x : 𝒳) (W : Over x)
    (hW : IsEmpty ((BigFppfOver.toScheme B S hS).obj (p.obj W.left))) :
    (⊥ : Sieve W) ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) W := by
  exact bot_mem_over_topology _ W (bot_mem_associatedTopology B S hS p hp W.left hW)

/-- A **disjoint union** of a family `Y` of objects of the slice of the associated fppf site at an
object `x`: an object of the slice into which the members include, carrying the three properties a
decomposition statement about sections over it needs — the inclusions are monomorphisms, they
generate a covering sieve, and two distinct members meet only over an object the empty sieve covers
— together with affineness of the union. -/
structure FiniteDisjointUnion (x : 𝒳) {ι : Type u} (Y : ι → Over x) where
  /-- The object of the slice which is the disjoint union of the family. -/
  obj : Over x
  /-- The inclusion of a member of the family into the disjoint union. -/
  incl (i : ι) : Y i ⟶ obj
  /-- Each inclusion is a monomorphism. -/
  mono_incl (i : ι) : Mono (incl i)
  /-- The inclusions generate a covering sieve of the disjoint union. -/
  ofArrows_mem :
    Sieve.ofArrows Y incl ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) obj
  /-- Two distinct members of the family meet only over an object whose empty sieve covers. -/
  bot_mem_of_comp_eq ⦃Z : Over x⦄ ⦃i j : ι⦄ (gi : Z ⟶ Y i) (gj : Z ⟶ Y j) :
    i ≠ j → gi ≫ incl i = gj ≫ incl j →
      (⊥ : Sieve Z) ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) Z
  /-- The disjoint union is an affine object. -/
  isAffine : IsAffineOver B S hS (p.obj obj.left)

/-- **A finite family of affine objects of a slice of the associated fppf site has a disjoint
union.**

The underlying scheme is the coproduct of the underlying schemes of the images of the members.  It
is an object of the chosen size-bounded category of schemes by the bound of Stacks 000R (2) for a
countable coproduct, and it is affine because a finite coproduct of affine schemes is; its
structure morphism to the image of `x` is the one the family induces on the coproduct.  An object
of the fibred category lying over it, with a morphism to `x`, is a lift of that structure morphism,
and the inclusions of the members are the unique lifts of the inclusions of the components of the
coproduct.

The three properties are read off from the corresponding properties of a coproduct of schemes: the
inclusions of the components are open immersions, hence monomorphisms, and a monomorphism of the
base is reflected to a monomorphism of the fibred category by the uniqueness of lifts; they are
jointly surjective, hence an fppf covering family, and
`AlgebraicGeometry.BigFppfSite.ofArrows_mem_topology` makes them a covering family of the site with
no cardinality hypothesis; and a scheme mapping to two distinct components of a coproduct is empty,
whence the empty sieve covers the object it lies under. -/
theorem nonempty_finiteDisjointUnion (hp : p.IsFiberedInGroupoids) (x : 𝒳) {ι : Type u} [Finite ι]
    (Y : ι → Over x) (haff : ∀ i, IsAffineOver B S hS (p.obj (Y i).left)) :
    Nonempty (FiniteDisjointUnion B S hS p x Y) := by
  classical
  set Zb : ι → B.Schemes := fun i => (p.obj (Y i).left).left with hZb
  set Zs : ι → Scheme.{u} := fun i => B.inclusion.obj (Zb i) with hZs
  have hDsize : B.Contains (∐ Zs) :=
    Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof
      Cardinal.mk_le_aleph0 Zs fun i => (Zb i).2
  set Db : B.Schemes := B.obj hDsize with hDb
  set ιb : ∀ i, Zb i ⟶ Db := fun i => ObjectProperty.homMk (Sigma.ι Zs i) with hιb
  set dq : Db ⟶ (p.obj x).left :=
    ObjectProperty.homMk (Sigma.desc fun i => B.inclusion.map (p.map (Y i).hom).left) with hdq
  have hιbdq : ∀ i, ιb i ≫ dq = (p.map (Y i).hom).left := by
    intro i
    apply B.inclusion.map_injective
    simp [hιb, hdq]
  set Dover : BigFppfOver B S hS := Over.mk (dq ≫ (p.obj x).hom) with hDover
  set dmap : Dover ⟶ p.obj x := Over.homMk dq with hdmap
  set ιO : ∀ i, p.obj (Y i).left ⟶ Dover := fun i => Over.homMk (ιb i) (by
    change ιb i ≫ dq ≫ (p.obj x).hom = (p.obj (Y i).left).hom
    rw [← Category.assoc, hιbdq i]
    exact Over.w (p.map (Y i).hom)) with hιO
  have hιOdmap : ∀ i, ιO i ≫ dmap = p.map (Y i).hom := fun i =>
    Over.OverMorphism.ext (by simpa [hιO, hdmap] using hιbdq i)
  obtain ⟨u, ψ, hψ⟩ := hp.exists_lift dmap x rfl
  have := hψ
  have hdom : p.obj u = Dover := IsHomLift.domain_eq p dmap ψ
  set gbase : ∀ i, p.obj (Y i).left ⟶ p.obj u := fun i => ιO i ≫ eqToHom hdom.symm with hgbase
  have hgb : ∀ i, gbase i ≫ p.map ψ = p.map (Y i).hom := by
    intro i
    rw [hgbase, IsHomLift.fac' p dmap ψ]
    simp [hιOdmap i]
  choose γ hγmap hγcomp using fun i => (hp.unique_lift ψ (Y i).hom (gbase i) (hgb i)).exists
  have hmonoιO : ∀ i, Mono (ιO i) := by
    intro i
    have h1 : Mono (B.inclusion.map (ιb i)) := by
      rw [hιb]; exact inferInstanceAs (Mono (Sigma.ι Zs i))
    exact (Over.forget (B.obj hS)).mono_of_mono_map
      (show Mono (ιb i) from B.inclusion.mono_of_mono_map h1)
  have hmonoγ : ∀ i, Mono (γ i) := by
    intro i
    refine ⟨fun {T} a b hab => ?_⟩
    have hgmono : Mono (gbase i) := by
      rw [hgbase]
      have := hmonoιO i
      infer_instance
    have hpab : p.map a = p.map b := by
      refine (cancel_mono (gbase i)).1 ?_
      rw [← hγmap i, ← p.map_comp, ← p.map_comp, hab]
    obtain ⟨c, -, huniq⟩ := hp.unique_lift (γ i) (a ≫ γ i) (p.map a) (by rw [← p.map_comp])
    exact (huniq a ⟨rfl, rfl⟩).trans (huniq b ⟨hpab.symm, hab.symm⟩).symm
  have hfppf : Presieve.ofArrows Zs (fun i => Sigma.ι Zs i) ∈
      Scheme.fppfPrecoverage (∐ Zs) := by
    refine Scheme.zariskiPrecoverage_le_fppfPrecoverage _ ?_
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun z => ?_, fun i => inferInstance⟩
    obtain ⟨⟨i, y⟩, hzy⟩ := (sigmaMk Zs).surjective z
    exact ⟨i, y, by rw [← hzy]; exact (sigmaMk_mk Zs i y).symm⟩
  have hcovD : Sieve.ofArrows (fun i => p.obj (Y i).left) ιO ∈
      BigFppfOver.baseOverTopology B S hS .fppf Dover :=
    BigFppfOver.ofArrows_mem_baseOverTopology B S hS _ _ hfppf
  have hcovU : Sieve.ofArrows (fun i => p.obj (Y i).left) gbase ∈
      BigFppfOver.baseOverTopology B S hS .fppf (p.obj u) := by
    refine (BigFppfOver.baseOverTopology B S hS .fppf).superset_covering ?_
      ((BigFppfOver.baseOverTopology B S hS .fppf).pullback_stable (eqToHom hdom) hcovD)
    intro W h hh
    rw [Sieve.pullback_apply, Sieve.mem_ofArrows_iff] at hh
    obtain ⟨i, b, hb⟩ := hh
    refine (Sieve.mem_ofArrows_iff _ _ _).2 ⟨i, b, ?_⟩
    rw [hgbase, ← Category.assoc, ← hb]
    simp
  set incl : ∀ i, Y i ⟶ Over.mk ψ := fun i => Over.homMk (γ i) (hγcomp i) with hincl
  refine ⟨Over.mk ψ, incl, fun i => (Over.forget x).mono_of_mono_map
    (show Mono (γ i) from hmonoγ i), ?_, ?_, ?_⟩
  · rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    refine ofArrows_mem_associatedTopology B S hS p hp _ _ ?_
    have hmap : ∀ i, p.map (incl i).left = gbase i := fun i => by rw [hincl]; exact hγmap i
    simp only [hmap]
    exact hcovU
  · intro Z i j gi gj hij hcomm
    have h1 : gi.left ≫ γ i = gj.left ≫ γ j := by
      have h0 := congrArg (Over.forget x).map hcomm
      simpa [hincl] using h0
    have h2 : p.map gi.left ≫ gbase i = p.map gj.left ≫ gbase j := by
      rw [← hγmap, ← hγmap, ← p.map_comp, ← p.map_comp, h1]
    have h3 : p.map gi.left ≫ ιO i = p.map gj.left ≫ ιO j := by
      rw [hgbase] at h2
      simp only [← Category.assoc] at h2
      exact (cancel_mono (eqToHom hdom.symm)).1 h2
    refine bot_mem_associatedTopology_over B S hS p hp x Z ?_
    have h4 := congrArg (BigFppfOver.toScheme B S hS).map h3
    rw [Functor.map_comp, Functor.map_comp] at h4
    exact isEmpty_of_commSq_sigmaι_of_ne (g := Zs) ⟨h4⟩ hij
  · change IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj u))
    rw [hdom]
    have haff' : ∀ i, IsAffine (Zs i) := fun i => haff i
    exact (inferInstance : IsAffine (∐ Zs))

end AlgebraicGeometry.FibredSite

end
