module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf

/-!
# Local surjectivity of the maps out of and between quotient sheaves

The quotient sheaf `U/R` of a pre-relation is the sheafification of a pointwise coequalizer,
so the canonical projection from the functor of points of `U` is a surjection of sheaves. This
file records that, and draws the consequence for a morphism of pre-relations: if the induced
map on the functors of points of the two bases is a surjection of sheaves, then so is the
induced map of quotient sheaves.

Specialised to the restriction `j' : R' → U' ×_S U'` of a pre-relation `j : R → U ×_S U`
along `g : U' → U`, this is the second half of Groupoids, Lemma **045Z**: *if `g` defines a
surjection `h_{U'} → h_U` of sheaves in the `τ`-topology, then `U'/R' → U/R` is surjective.*
The first half of that lemma — injectivity of `U'/R' → U/R`, which holds with no hypothesis on
`g` — is **not** proved here; see the implementation notes.

## Main results

* `Stacks.Groupoids.isLocallySurjective_quotientSheafMap`: a morphism of pre-relations whose
  map on the functors of points of the bases is locally surjective induces a locally
  surjective map of quotient sheaves, and `Stacks.Groupoids.epi_quotientSheafMap` records
  that such a map is an epimorphism of sheaves.
* `Stacks.Groupoids.isLocallySurjective_quotientSheafMap_restrict`: the surjectivity half of
  Groupoids, Lemma **045Z**, for the restriction of a pre-relation along `g`.

## Implementation notes

The argument is the source's own, and it is formal. The projection onto the quotient sheaf is
locally surjective for *any* topology by
`Stacks.Groupoids.isLocallySurjective_toQuotientSheaf`, and local surjectivity is stable under
composition and is inherited by the second factor of a locally surjective composite. The square
`Stacks.Groupoids.toQuotientSheaf_comp_quotientSheafMap` turns the hypothesis on the bases into
the conclusion by exactly that last step.

Presheaves of sets are taken in `Type u`, the universe of morphisms of `S`-schemes, and the
site at `C : Type u` with `Category.{u} C`; the big and small Zariski, étale, fppf, smooth and
syntomic sites of schemes in universe `u` all satisfy this, so no site of interest is
excluded.

**The injectivity half of 045Z is not here, and it is not a short step.** It rests on Groupoids,
Lemma **045Y** — that two `T`-valued points of `U` agree in `(U/R)(T)` exactly when they are
`τ`-locally related by `R` — and nothing in this development describes a *section* of a quotient
sheaf: `StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf` proves only the universal property.
Supplying 045Y needs a local description of `toSheafify` applied to a pointwise coequalizer of
presheaves of types, which is absent here and in Mathlib. The surjectivity half proved below is
independent of it, which is why it can be separated out at all.

The hypothesis is taken as local surjectivity of the map on functors of points, which is the
source's primary formulation ("if `g` defines a surjection `h_{U'} → h_U` of sheaves in the
`τ`-topology"). The source's parenthetical sufficient condition — that `{g : U' → U}` be a
`τ`-covering, by Sites, Lemma **00WT** — is not discharged here, because it needs the comparison
between coverings of the site of schemes and the Grothendieck topology `J`, which is a property
of the presentation `F` and not of the quotient-sheaf construction.

No Stacks tag attribute is placed on anything in this file, for 045Z or for 02VG or 02VF.
Tag **045Z** belongs to Groupoids, Chapter 39; the declarations are left unregistered here —
and in any case only one of that tag's two conclusions is proved here, so the tag would not
be earned by this file alone.

## References

* [Stacks Project, Tag 045Z](https://stacks.math.columbia.edu/tag/045Z)
* [Stacks Project, Tag 045Y](https://stacks.math.columbia.edu/tag/045Y)
* [Stacks Project, Tag 02VG](https://stacks.math.columbia.edu/tag/02VG)
* [Stacks Project, Tag 02V8](https://stacks.math.columbia.edu/tag/02V8)
* [Stacks Project, Tag 00WT](https://stacks.math.columbia.edu/tag/00WT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids

variable {S : Scheme.{u}} {C : Type u} [Category.{u} C]

/-- A morphism of pre-relations whose map on the functors of points of the bases is a
surjection of sheaves induces a surjection of quotient sheaves. -/
theorem isLocallySurjective_quotientSheafMap (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) {R U R' U' : Over S}
    (j : PreRelation R U) (j' : PreRelation R' U') (r : R ⟶ R') (f : U ⟶ U')
    (hs : r ≫ j'.source = j.source ≫ f) (ht : r ≫ j'.target = j.target ≫ f)
    (hf : Presheaf.IsLocallySurjective J (F.op.whiskerLeft (yoneda.map f))) :
    Presheaf.IsLocallySurjective J (quotientSheafMap J F j j' r f hs ht).hom := by
  have := hf
  have := isLocallySurjective_toQuotientSheaf J F j'
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
    (toQuotientSheaf_comp_quotientSheafMap J F j j' r f hs ht)

/-- A morphism of pre-relations whose map on the functors of points of the bases is a
surjection of sheaves induces an epimorphism of quotient sheaves. -/
theorem epi_quotientSheafMap (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) {R U R' U' : Over S}
    (j : PreRelation R U) (j' : PreRelation R' U') (r : R ⟶ R') (f : U ⟶ U')
    (hs : r ≫ j'.source = j.source ≫ f) (ht : r ≫ j'.target = j.target ≫ f)
    (hf : Presheaf.IsLocallySurjective J (F.op.whiskerLeft (yoneda.map f))) :
    Epi (quotientSheafMap J F j j' r f hs ht) := by
  have : Sheaf.IsLocallySurjective (quotientSheafMap J F j j' r f hs ht) :=
    isLocallySurjective_quotientSheafMap J F j j' r f hs ht hf
  infer_instance

section Restrict

variable {R U U' : Over S} (j : PreRelation R U) (g : U' ⟶ U)

/-- The second projection out of the restriction of a pre-relation along `g` is a morphism of
pre-relations over `g`, on source maps. -/
theorem restrict_pullback_snd_source :
    pullback.snd (prod.map g g) j ≫ j.source =
      (AlgebraicGeometry.PreRelation.restrict j g).source ≫ g := by
  dsimp only [PreRelation.source, AlgebraicGeometry.PreRelation.restrict]
  rw [← Category.assoc, ← pullback.condition, Category.assoc, prod.map_snd, Category.assoc]

/-- The second projection out of the restriction of a pre-relation along `g` is a morphism of
pre-relations over `g`, on target maps. -/
theorem restrict_pullback_snd_target :
    pullback.snd (prod.map g g) j ≫ j.target =
      (AlgebraicGeometry.PreRelation.restrict j g).target ≫ g := by
  dsimp only [PreRelation.target, AlgebraicGeometry.PreRelation.restrict]
  rw [← Category.assoc, ← pullback.condition, Category.assoc, prod.map_fst, Category.assoc]

/-- **Groupoids, Lemma 045Z, surjectivity.** Let `j : R → U ×_S U` be a pre-relation and
`g : U' → U` a morphism, and let `j'` be the restriction of `j` to `U'`. If `g` defines a
surjection `h_{U'} → h_U` of sheaves for the topology `J`, then the induced map of quotient
sheaves `U'/R' → U/R` is a surjection of sheaves.

This is one of that lemma's two conclusions; injectivity of the same map is not proved here. -/
theorem isLocallySurjective_quotientSheafMap_restrict (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S)
    (hg : Presheaf.IsLocallySurjective J (F.op.whiskerLeft (yoneda.map g))) :
    Presheaf.IsLocallySurjective J
      (quotientSheafMap J F (AlgebraicGeometry.PreRelation.restrict j g) j
        (pullback.snd (prod.map g g) j) g
        (restrict_pullback_snd_source j g) (restrict_pullback_snd_target j g)).hom :=
  isLocallySurjective_quotientSheafMap J F _ _ _ _ _ _ hg

/-- **Groupoids, Lemma 045Z, surjectivity**, as an epimorphism of sheaves. -/
theorem epi_quotientSheafMap_restrict (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S)
    (hg : Presheaf.IsLocallySurjective J (F.op.whiskerLeft (yoneda.map g))) :
    Epi (quotientSheafMap J F (AlgebraicGeometry.PreRelation.restrict j g) j
      (pullback.snd (prod.map g g) j) g
      (restrict_pullback_snd_source j g) (restrict_pullback_snd_target j g)) :=
  epi_quotientSheafMap J F _ _ _ _ _ _ hg

end Restrict

end Stacks.Groupoids

end
