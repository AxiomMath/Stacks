module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafLocallySurjective
public import StacksFrontier.CategoryTheory.Sites.Sheafification.LocalRepresentatives
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quotient sheaves of a restricted pre-equivalence relation

Let `j : R ⟶ U ×_S U` be a pre-equivalence relation over `S` and `g : U' ⟶ U` a morphism of
`S`-schemes, and let `j'` be the restriction of `j` along `g`. The second projection of the
pullback defining the restriction is a morphism of pre-relations from `j'` to `j` over `g`,
so it induces a map `U'/R' ⟶ U/R` of quotient sheaves. That map is always injective, and it
is an isomorphism as soon as `g` induces a local surjection on functors of points.

## Main definitions

* `Stacks.Groupoids.restrictQuotientSheafMap` is the induced map `U'/R' ⟶ U/R`.

## Main results

* `Stacks.Groupoids.restrictQuotientSheafMap_mono` is injectivity.
* `Stacks.Groupoids.restrictQuotientSheafMap_isIso` is bijectivity under local
  surjectivity of `g` on functors of points.
* `Stacks.Groupoids.quotientProjection_surjective` and
  `Stacks.Groupoids.quotientPoint_locally_surjective` say that the projection onto the
  quotient presheaf is surjective in each degree and that the projection onto the quotient
  sheaf is locally surjective.

## Implementation notes

The site is presented by an arbitrary functor `F : C ⥤ Over S` into `S`-schemes, so the
statement covers the big and small Zariski, étale, fppf, smooth and syntomic sites at once.
Local surjectivity of the map `h_{U'} ⟶ h_U` of restricted functors of points, in the sense
of `CategoryTheory.Presheaf.IsLocallySurjective`, is the abstract form of the source's
hypothesis that `g` defines a surjection of sheaves; a covering `{g}` is the special case.

Injectivity is proved before sheafification, where the quotients are pointwise, and then
transported by left exactness of sheafification: the map of quotient *presheaves* is injective
in each degree by `Stacks.Groupoids.toQuotientPresheaf_apply_eq_iff_related` applied on both
sides, and `CategoryTheory.presheafToSheaf` preserves monomorphisms. Surjectivity is local
surjectivity of the composite `h_{U'} ⟶ U/R`, which factors both as `h_{U'} ⟶ U'/R' ⟶ U/R`
and as `h_{U'} ⟶ h_U ⟶ U/R`; the projection onto a quotient sheaf is locally surjective
because the projection onto the quotient presheaf is a pointwise epimorphism and
`CategoryTheory.toSheafify` is locally surjective.

## References

* [Stacks Project, Tag 045Z](https://stacks.math.columbia.edu/tag/045Z)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.Groupoids

/-- A point of the restricted relation scheme, assembled from a pair of points of `U'` and a
point of `R` relating their images in `U`. -/
private noncomputable def restrictRelationPoint
    {S : Scheme.{u}} {C : Type v} [Category.{w} C]
    {R U U' : Over S} (j : PreRelation R U) (g : U' ⟶ U)
    (F : C ⥤ Over S)
    {X : C} (a b : F.obj X ⟶ U') (r : F.obj X ⟶ R)
    (hs : r ≫ j.source = a ≫ g) (ht : r ≫ j.target = b ≫ g) :
    F.obj X ⟶ AlgebraicGeometry.PreRelation.restriction j g := by
  refine pullback.lift (prod.lift b a) r ?_
  apply prod.hom_ext <;> simp [Category.assoc, hs, ht]

/-- The projection onto the quotient presheaf is surjective on sections: it is a coequalizer
projection, so it is an epimorphism of presheaves of types. -/
theorem quotientProjection_surjective
    {S : Scheme.{u}} {C : Type v} [Category.{w} C]
    (F : C ⥤ Over S) {R U : Over S} (j : PreRelation R U) (X : Cᵒᵖ) :
    Function.Surjective ((toQuotientPresheaf F j).app X) := by
  have : Epi ((toQuotientPresheaf F j).app X) :=
    (NatTrans.epi_iff_epi_app _).1 coequalizer.π_epi X
  exact surjective_of_epi _

/-- The projection onto the quotient sheaf is locally surjective. -/
alias quotientPoint_locally_surjective := isLocallySurjective_toQuotientSheaf

variable {S : Scheme.{u}} {C : Type v} [Category.{w} C]
variable (J : GrothendieckTopology C) [HasSheafify J (Type u)]
variable (F : C ⥤ Over S) {R U U' : Over S}
variable (j : PreRelation R U) (g : U' ⟶ U)

/-- The map of quotient sheaves induced by restricting a pre-relation along `g`. -/
noncomputable def restrictQuotientSheafMap :
    quotientSheaf J F (AlgebraicGeometry.PreRelation.restrict j g) ⟶ quotientSheaf J F j :=
  quotientSheafMap J F (AlgebraicGeometry.PreRelation.restrict j g) j
    (pullback.snd (prod.map g g) j) g
    (by
      dsimp [AlgebraicGeometry.PreRelation.restrict, PreRelation.source]
      simp only [Category.assoc, ← pullback.condition_assoc]
      simp)
    (by
      dsimp [AlgebraicGeometry.PreRelation.restrict, PreRelation.target]
      simp only [Category.assoc, ← pullback.condition_assoc]
      simp)

/-- The second projection of the restriction of `j` along `g` is compatible with the sources. -/
private alias restrict_snd_source := restrict_pullback_snd_source

/-- The second projection of the restriction of `j` along `g` is compatible with the targets. -/
private alias restrict_snd_target := restrict_pullback_snd_target

/-- **Stacks 045Z, injectivity.** Restricting a pre-equivalence relation induces an injective
map `U'/R' ⟶ U/R` of quotient sheaves. -/
@[stacks 045Z "injectivity", sga "3 IV 4.4.10" "Monomorphism clause"]
theorem restrictQuotientSheafMap_mono (hj : IsPreEquivalenceRelation j) :
    Mono (restrictQuotientSheafMap J F j g) := by
  let j' := AlgebraicGeometry.PreRelation.restrict j g
  let m := quotientPresheafMap F j' j (pullback.snd (prod.map g g) j) g
    (restrict_snd_source j g) (restrict_snd_target j g)
  have hm : Mono m := by
    rw [NatTrans.mono_iff_mono_app]
    intro X
    rw [CategoryTheory.mono_iff_injective]
    intro x y hxy
    obtain ⟨a, rfl⟩ := quotientProjection_surjective F j' X x
    obtain ⟨b, rfl⟩ := quotientProjection_surjective F j' X y
    have hfac : toQuotientPresheaf F j' ≫ m =
        F.op.whiskerLeft (yoneda.map g) ≫ toQuotientPresheaf F j := by
      dsimp [m, quotientPresheafMap, toQuotientPresheaf]
      rw [coequalizer.π_desc]
    have hab : (toQuotientPresheaf F j).app X (a ≫ g) =
        (toQuotientPresheaf F j).app X (b ≫ g) :=
      (congrArg (fun k => k.app X a) hfac).symm.trans
        (hxy.trans (congrArg (fun k => k.app X b) hfac))
    obtain ⟨r, ht, hs⟩ :=
      (toQuotientPresheaf_apply_eq_iff_related F j hj X.unop (a ≫ g) (b ≫ g)).1 hab
    apply (toQuotientPresheaf_apply_eq_iff_related F j'
      (AlgebraicGeometry.PreRelation.isPreEquivalenceRelation_restrict j g hj) X.unop a b).2
    let r' := restrictRelationPoint j g F b a r hs ht
    refine ⟨r', ?_, ?_⟩ <;>
      simp [r', restrictRelationPoint, j', AlgebraicGeometry.PreRelation.restrict,
        PreRelation.source, PreRelation.target]
  change Mono ((presheafToSheaf J (Type u)).map m)
  infer_instance

/-- **Stacks 045Z, bijectivity.** If `g` induces a local surjection on restricted functors of
points, then the induced map `U'/R' ⟶ U/R` of quotient sheaves is an isomorphism. -/
@[stacks 045Z "isomorphism under surjectivity"]
theorem restrictQuotientSheafMap_isIso (hj : IsPreEquivalenceRelation j)
    (hg : Presheaf.IsLocallySurjective J (F.op.whiskerLeft (yoneda.map g))) :
    IsIso (restrictQuotientSheafMap J F j g) := by
  let j' := AlgebraicGeometry.PreRelation.restrict j g
  let p := toQuotientSheaf J F j'
  let q := restrictQuotientSheafMap J F j g
  have hp : Presheaf.IsLocallySurjective J p := quotientPoint_locally_surjective J F j'
  have := quotientPoint_locally_surjective J F j
  have hfac' : p ≫ q.hom =
      F.op.whiskerLeft (yoneda.map g) ≫ toQuotientSheaf J F j := by
    simpa [p, q, restrictQuotientSheafMap] using toQuotientSheaf_comp_quotientSheafMap J F j' j
      (pullback.snd (prod.map g g) j) g (restrict_snd_source j g) (restrict_snd_target j g)
  have hqsurj : Presheaf.IsLocallySurjective J q.hom := by
    rw [← Presheaf.comp_isLocallySurjective_iff J p q.hom, hfac']
    infer_instance
  have : Epi q := (Sheaf.isLocallySurjective_iff_epi q).1 hqsurj
  have : Mono q := restrictQuotientSheafMap_mono J F j g hj
  exact isIso_of_mono_of_epi q

end Stacks.Groupoids

end
