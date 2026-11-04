module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafInjective

/-!
# Bijectivity of the quotient-sheaf map of a restricted groupoid scheme

Let `(U, R, s, t, c)` be a groupoid scheme over `S`, let `g : U' → U` be a morphism and let
`(U', R', s', t', c')` be the restriction of the groupoid along `g`. The induced map of
quotient sheaves `U'/R' → U/R` is always a monomorphism; this file supplies the complementary
surjectivity, and hence the four bijectivity criteria of Groupoids, Lemma **02VH**:

* the *reach map* `U' ×_{g, t} R → U`, sending an arrow whose target lifts along `g` to its
  source, is a surjection of sheaves;
* `g` itself is a surjection of sheaves;
* a single arrow of the site covers `U` and realises the reach map;
* a single arrow of the site covers `U` and realises `g`.

## Main results

* `Stacks.Groupoids.isLocallySurjective_quotientSheafMap_of_factor`: the general surjectivity
  criterion. A morphism of pre-relations induces a locally surjective map of quotient sheaves
  as soon as its map on bases, precomposed with some auxiliary map, agrees in the quotient
  presheaf with a map whose sheafified points-map is locally surjective.
* `Stacks.Groupoids.isLocallySurjective_points_map_of_singleton_cover`: a single arrow of the
  site covering the target and realising a morphism of `S`-schemes makes the induced map of
  functors of points locally surjective.
* `Stacks.Groupoids.isIso_restrictionQuotientMap_of_reach` and
  `Stacks.Groupoids.isIso_restrictionQuotientMap_of_objects`: the two surjectivity criteria of
  Groupoids, Lemma **02VH**.
* `Stacks.Groupoids.isIso_restrictionQuotientMap_of_reach_cover` and
  `Stacks.Groupoids.isIso_restrictionQuotientMap_of_objects_cover`: the same two criteria from
  a singleton covering of the site.

## Implementation notes

The quotient sheaf is the sheafification of a pointwise coequalizer, so surjectivity needs no
local description of sheafification either: it is enough to exhibit *one* locally surjective
map into the target quotient sheaf that factors through the map in question. The factorisation
used is the reach map followed by the projection onto the quotient, which is locally
surjective because the hypothesis makes its first factor so after sheafification and the
coequalizer projection is pointwise surjective. That the factorisation holds at all is the
source's observation that an arrow of `G` identifies its source with its target in `U/R`:
`Stacks.Groupoids.whiskerLeft_reach_toQuotientPresheaf`, which is the coequalizer relation
precomposed with the projection out of the reach pullback.

No comparison of the restricted groupoid with the restriction of the groupoid's pre-relation is
needed, exactly as for the injectivity half: the criterion is applied to the groupoid's own
pre-equivalence relation, with the auxiliary map the first projection of the reach pullback
transported along `AlgebraicGeometry.GroupoidScheme.Restriction.objects_eq`.

The singleton-covering criteria are where fullness of the site functor is used: a section of the
functor of points over an arbitrary object of the site is carried to a map of schemes, which
fullness lifts to the site so that the given covering can be pulled back along it.

Presheaves of sets are taken in the universe of morphisms of `S`-schemes, which for a site
`C : Type v` with `Category.{w} C` must therefore be `max v w`, as it is for the big and small
Zariski, étale, fppf, smooth and syntomic sites of schemes in a fixed universe. The reason is
Mathlib's instance making sheafification locally surjective, which is stated for presheaves
valued in the canonical universe of a site. The two universes of
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf` are left free for the statements that do
not sheafify, which is why this file is divided into sections.

No Stacks tag attribute is placed on anything in this file. Tag **02VH** belongs to Groupoids,
Chapter 39; the declarations are left unregistered here.

## References

* [Stacks Project, Tag 02VH](https://stacks.math.columbia.edu/tag/02VH)
* [Stacks Project, Tag 045Z](https://stacks.math.columbia.edu/tag/045Z)
* [Stacks Project, Tag 02VG](https://stacks.math.columbia.edu/tag/02VG)
* [Stacks Project, Tag 02VB](https://stacks.math.columbia.edu/tag/02VB)
* [Stacks Project, Tag 0232](https://stacks.math.columbia.edu/tag/0232)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.Groupoids

section Presheaves

variable {S : Scheme.{u}} {C : Type v} [Category.{w} C]

/-- The two maps of a pre-relation, precomposed with a common map out of a third scheme, agree
after projection to the quotient presheaf: this is the coequalizer relation, precomposed. -/
theorem whiskerLeft_comp_toQuotientPresheaf_eq (F : C ⥤ Over S) {R U : Over S}
    (j : PreRelation R U) {V : Over S} (a : V ⟶ R) :
    F.op.whiskerLeft (yoneda.map (a ≫ j.source)) ≫ toQuotientPresheaf F j =
      F.op.whiskerLeft (yoneda.map (a ≫ j.target)) ≫ toQuotientPresheaf F j := by
  rw [Functor.map_comp, Functor.map_comp, Functor.whiskerLeft_comp, Functor.whiskerLeft_comp,
    Category.assoc, Category.assoc]
  exact congrArg (fun q => F.op.whiskerLeft (yoneda.map a) ≫ q)
    (coequalizer.condition (sourceMap F j) (targetMap F j))

/-- A morphism of `S`-schemes whose source and target are, up to isomorphism, objects of the
site, and which is realised there by an arrow generating a covering sieve, induces a locally
surjective map on functors of points.

A section over an arbitrary object of the site is carried to a map of schemes into the target;
fullness of the presentation lifts that map to the site, and the given covering pulls back
along the lift. -/
theorem isLocallySurjective_points_map_of_singleton_cover
    (J : GrothendieckTopology C) (F : C ⥤ Over S) (hF : F.Full)
    {V W : Over S} (s : V ⟶ W) (X Y : C) (eX : F.obj X ≅ V) (eY : F.obj Y ≅ W)
    (a : X ⟶ Y) (ha : F.map a ≫ eY.hom = eX.hom ≫ s)
    (hcover : Sieve.generate (Presieve.singleton a) ∈ J Y) :
    Presheaf.IsLocallySurjective J (F.op.whiskerLeft (yoneda.map s)) where
  imageSieve_mem {Z} y := by
    obtain ⟨b, hb⟩ := hF.map_surjective (y ≫ eY.inv)
    refine J.superset_covering ?_ (J.pullback_stable b hcover)
    rintro Q h ⟨T, k, a', ha', hk⟩
    cases ha'
    refine ⟨F.map k ≫ eX.hom, ?_⟩
    show (F.map k ≫ eX.hom) ≫ s = F.map h ≫ y
    rw [Category.assoc, ← ha, ← Category.assoc, ← F.map_comp, hk, F.map_comp, Category.assoc,
      hb, Category.assoc, Iso.inv_hom_id, Category.comp_id]

section Groupoid

variable (G : GroupoidScheme S) {U₀ : Over S} (g : U₀ ⟶ G.objects)

/-- The reach map and the lift of the target, followed by the restricting map, agree after
projection to the quotient presheaf: an arrow of `G` identifies its source with its target. -/
theorem whiskerLeft_reach_toQuotientPresheaf (F : C ⥤ Over S) :
    F.op.whiskerLeft (yoneda.map (pullback.fst g G.target ≫ g)) ≫
        toQuotientPresheaf F (groupoidPreRelation G) =
      F.op.whiskerLeft (yoneda.map (AlgebraicGeometry.GroupoidScheme.restrictionReachMap G g)) ≫
        toQuotientPresheaf F (groupoidPreRelation G) := by
  have hsrc : pullback.snd g G.target ≫ (groupoidPreRelation G).source =
      AlgebraicGeometry.GroupoidScheme.restrictionReachMap G g :=
    congrArg (fun m => pullback.snd g G.target ≫ m)
      (show (groupoidPreRelation G).source = G.source from prod.lift_snd _ _)
  have htgt : pullback.snd g G.target ≫ (groupoidPreRelation G).target =
      pullback.fst g G.target ≫ g := by
    rw [show (groupoidPreRelation G).target = G.target from prod.lift_fst _ _]
    exact pullback.condition.symm
  rw [← hsrc, ← htgt]
  exact (whiskerLeft_comp_toQuotientPresheaf_eq F (groupoidPreRelation G) _).symm

end Groupoid

end Presheaves

section Objects

variable {S : Scheme.{u}} (G : GroupoidScheme S) {U₀ : Over S} (g : U₀ ⟶ G.objects)
  (H : AlgebraicGeometry.GroupoidScheme.Restriction G g)

/-- Transporting the lift of the target out of the reach pullback into the objects of the
restriction and composing with the canonical map on objects recovers the restricting map. -/
theorem reachLift_comp_mapObjects :
    (pullback.fst g G.target ≫ eqToHom H.objects_eq.symm) ≫ H.hom.mapObjects =
      pullback.fst g G.target ≫ g := by
  rw [H.mapObjects_eq, Category.assoc, ← Category.assoc (eqToHom H.objects_eq.symm),
    eqToHom_trans, eqToHom_refl, Category.id_comp]

end Objects

section Sheafify

variable {C : Type v} [Category.{w} C] {S : Scheme.{max v w}}

/-- Sheafification carries local surjectivity: a locally surjective map of presheaves induces
a locally surjective map of sheafifications, because `CategoryTheory.toSheafify` is itself
locally surjective and natural. -/
theorem isLocallySurjective_sheafifyMap (J : GrothendieckTopology C)
    [HasSheafify J (Type (max v w))] {P Q : Cᵒᵖ ⥤ Type (max v w)} (φ : P ⟶ Q)
    (hφ : Presheaf.IsLocallySurjective J φ) :
    Presheaf.IsLocallySurjective J (sheafifyMap J φ) := by
  have := hφ
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
    (toSheafify_naturality J φ).symm

/-- A morphism of `S`-schemes with a section inherits local surjectivity of the sheafified map
on functors of points from the section's composite. -/
theorem isLocallySurjective_sheafifyMap_of_section (J : GrothendieckTopology C)
    [HasSheafify J (Type (max v w))] (F : C ⥤ Over S) {V W X : Over S}
    (σ : W ⟶ V) (s : V ⟶ X) (m : W ⟶ X) (hm : σ ≫ s = m)
    (hmls : Presheaf.IsLocallySurjective J (sheafifyMap J (F.op.whiskerLeft (yoneda.map m)))) :
    Presheaf.IsLocallySurjective J (sheafifyMap J (F.op.whiskerLeft (yoneda.map s))) := by
  have hfac : sheafifyMap J (F.op.whiskerLeft (yoneda.map σ)) ≫
      sheafifyMap J (F.op.whiskerLeft (yoneda.map s)) =
      sheafifyMap J (F.op.whiskerLeft (yoneda.map m)) := by
    rw [← sheafifyMap_comp, ← Functor.whiskerLeft_comp, ← Functor.map_comp, hm]
  have := hmls
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac

/-- The general surjectivity criterion for a map of quotient sheaves. Let `p : V → U` be a map
into the base of the source pre-relation and `q : V → U'` a map into the base of the target
one. If `p` followed by the map on bases agrees with `q` after projection to the target
quotient presheaf, and the sheafified map on functors of points of `q` is locally surjective,
then the induced map of quotient sheaves is locally surjective.

Compare `Stacks.Groupoids.isLocallySurjective_quotientSheafMap`, which is the case `V = U`,
`p = 𝟙 U`. -/
theorem isLocallySurjective_quotientSheafMap_of_factor
    (J : GrothendieckTopology C) [HasSheafify J (Type (max v w))] (F : C ⥤ Over S)
    {R U R' U' : Over S} (j : PreRelation R U) (j' : PreRelation R' U')
    (r : R ⟶ R') (f : U ⟶ U')
    (hs : r ≫ j'.source = j.source ≫ f) (ht : r ≫ j'.target = j.target ≫ f)
    {V : Over S} (p : V ⟶ U) (q : V ⟶ U')
    (hpq : F.op.whiskerLeft (yoneda.map (p ≫ f)) ≫ toQuotientPresheaf F j' =
      F.op.whiskerLeft (yoneda.map q) ≫ toQuotientPresheaf F j')
    (hq : Presheaf.IsLocallySurjective J (sheafifyMap J (F.op.whiskerLeft (yoneda.map q)))) :
    Presheaf.IsLocallySurjective J (quotientSheafMap J F j j' r f hs ht).hom := by
  have hfac : (F.op.whiskerLeft (yoneda.map p) ≫ toQuotientSheaf J F j) ≫
        (quotientSheafMap J F j j' r f hs ht).hom =
      toSheafify J (points F V) ≫
        sheafifyMap J (F.op.whiskerLeft (yoneda.map q) ≫ toQuotientPresheaf F j') := by
    rw [Category.assoc, toQuotientSheaf_comp_quotientSheafMap, ← Category.assoc,
      ← Functor.whiskerLeft_comp, ← Functor.map_comp, toQuotientSheaf, ← Category.assoc,
      hpq, ← toSheafify_naturality]
  have := hq
  have : Presheaf.IsLocallySurjective J (sheafifyMap J (toQuotientPresheaf F j')) :=
    isLocallySurjective_sheafifyMap J _
      (Presheaf.isLocallySurjective_of_surjective J _ (quotientProjection_surjective F j'))
  have : Presheaf.IsLocallySurjective J
      (sheafifyMap J (F.op.whiskerLeft (yoneda.map q) ≫ toQuotientPresheaf F j')) := by
    rw [sheafifyMap_comp]; infer_instance
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac

section Groupoid

variable (G : GroupoidScheme S) {U₀ : Over S} (g : U₀ ⟶ G.objects)
  (H : AlgebraicGeometry.GroupoidScheme.Restriction G g)
  (J : GrothendieckTopology C) [HasSheafify J (Type (max v w))] (F : C ⥤ Over S)

/-- If the reach map is a surjection of sheaves, the map of quotient sheaves `U'/R' → U/R` of a
restricted groupoid scheme is a surjection of sheaves. -/
theorem isLocallySurjective_restrictionQuotientMap_of_reach
    (hreach : Presheaf.IsLocallySurjective J
      (sheafifyMap J (F.op.whiskerLeft
        (yoneda.map (AlgebraicGeometry.GroupoidScheme.restrictionReachMap G g))))) :
    Presheaf.IsLocallySurjective J
      (AlgebraicGeometry.GroupoidScheme.restrictionQuotientMap J F G g H).hom := by
  refine isLocallySurjective_quotientSheafMap_of_factor J F _ _ _ _ _ _
    (pullback.fst g G.target ≫ eqToHom H.objects_eq.symm)
    (AlgebraicGeometry.GroupoidScheme.restrictionReachMap G g) ?_ hreach
  rw [reachLift_comp_mapObjects]
  exact whiskerLeft_reach_toQuotientPresheaf G g F

/-- **Groupoids, Lemma 02VH, bijectivity under surjectivity of the reach map.** Let
`(U, R, s, t, c)` be a groupoid scheme over `S`, let `g : U' → U` be a morphism and let
`(U', R', s', t', c')` be the restriction of the groupoid along `g`. If every object of `U` is
locally the source of an arrow whose target lifts along `g` — that is, if the reach map
`AlgebraicGeometry.GroupoidScheme.restrictionReachMap` defines a surjection of sheaves for `J` —
then the map of quotient sheaves `U'/R' → U/R` is an isomorphism.

Injectivity is `AlgebraicGeometry.GroupoidScheme.mono_restrictionQuotientMap` and holds with no
hypothesis on `g`; the category of sheaves of types is balanced, so the two together give the
isomorphism. -/
theorem isIso_restrictionQuotientMap_of_reach
    (hreach : Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type (max v w))).map
        (F.op.whiskerLeft
          (yoneda.map (AlgebraicGeometry.GroupoidScheme.restrictionReachMap G g))))) :
    IsIso (AlgebraicGeometry.GroupoidScheme.restrictionQuotientMap J F G g H) := by
  have : Mono (AlgebraicGeometry.GroupoidScheme.restrictionQuotientMap J F G g H) :=
    AlgebraicGeometry.GroupoidScheme.mono_restrictionQuotientMap J F G g H
  have : Sheaf.IsLocallySurjective
      (AlgebraicGeometry.GroupoidScheme.restrictionQuotientMap J F G g H) :=
    isLocallySurjective_restrictionQuotientMap_of_reach G g H J F hreach
  have : Epi (AlgebraicGeometry.GroupoidScheme.restrictionQuotientMap J F G g H) := inferInstance
  exact isIso_of_mono_of_epi _

/-- **Groupoids, Lemma 02VH, bijectivity under surjectivity of the restricting map.** If `g`
itself defines a surjection `h_{U'} → h_U` of sheaves for `J`, then the map of quotient sheaves
`U'/R' → U/R` is an isomorphism.

The restricting map is a section of the reach map, by way of the neutral element
(`Stacks.Groupoids.restrictionReachMap_section`), so this is a special case of
`Stacks.Groupoids.isIso_restrictionQuotientMap_of_reach`. -/
theorem isIso_restrictionQuotientMap_of_objects
    (hg : Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type (max v w))).map (F.op.whiskerLeft (yoneda.map g)))) :
    IsIso (AlgebraicGeometry.GroupoidScheme.restrictionQuotientMap J F G g H) :=
  isIso_restrictionQuotientMap_of_reach G g H J F
    (isLocallySurjective_sheafifyMap_of_section J F _ _ _ (restrictionReachMap_section G g) hg)

/-- **Groupoids, Lemma 02VH, bijectivity from a singleton covering by the reach map.** If an
arrow `a` of the site generates a covering sieve of an object presenting `U`, and realises the
reach map on objects presenting its source and target, then the map of quotient sheaves
`U'/R' → U/R` is an isomorphism. -/
theorem isIso_restrictionQuotientMap_of_reach_cover (hF : F.Full)
    (X Y : C) (eX : F.obj X ≅ pullback g G.target) (eY : F.obj Y ≅ G.objects)
    (a : X ⟶ Y)
    (ha : F.map a ≫ eY.hom = eX.hom ≫ AlgebraicGeometry.GroupoidScheme.restrictionReachMap G g)
    (hcover : Sieve.generate (Presieve.singleton a) ∈ J Y) :
    IsIso (AlgebraicGeometry.GroupoidScheme.restrictionQuotientMap J F G g H) :=
  isIso_restrictionQuotientMap_of_reach G g H J F
    (isLocallySurjective_sheafifyMap J _
      (isLocallySurjective_points_map_of_singleton_cover J F hF _ X Y eX eY a ha hcover))

/-- **Groupoids, Lemma 02VH, bijectivity from a singleton covering by the restricting map.** If
an arrow `a` of the site generates a covering sieve of an object presenting `U`, and realises
`g` on objects presenting `U'` and `U`, then the map of quotient sheaves `U'/R' → U/R` is an
isomorphism. -/
theorem isIso_restrictionQuotientMap_of_objects_cover (hF : F.Full)
    (X Y : C) (eX : F.obj X ≅ U₀) (eY : F.obj Y ≅ G.objects)
    (a : X ⟶ Y) (ha : F.map a ≫ eY.hom = eX.hom ≫ g)
    (hcover : Sieve.generate (Presieve.singleton a) ∈ J Y) :
    IsIso (AlgebraicGeometry.GroupoidScheme.restrictionQuotientMap J F G g H) :=
  isIso_restrictionQuotientMap_of_objects G g H J F
    (isLocallySurjective_sheafifyMap J _
      (isLocallySurjective_points_map_of_singleton_cover J F hF _ X Y eX eY a ha hcover))

end Groupoid

end Sheafify

end Stacks.Groupoids

end
