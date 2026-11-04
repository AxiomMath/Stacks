module

public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.RestrictionUnivLE
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The degree-zero comparison along a subset, in a coefficient universe of its own

For a sheaf `F` on `X` and a subset `Z ⊆ X`, the canonical map

`colim_{U ⊇ Z open} F(U) ⟶ Γ(Z, F|_Z)`

is `Stacks.Topology.subsetSectionsMap`, and it is stated only with the coefficient universe
pinned to the universe of the space: its variable block is `{C : Type u} [Category.{v} C]` with
`{X : TopCat.{v}}`. At the shape the derived clause of [Stacks, Tag 0DCU] has — spaces
in `TopCat.{u}`, coefficients `AddCommGrpCat.{max (u + 1) v}` — it cannot be written:

```
Application type mismatch: The argument F has type
  TopCat.Sheaf.{u, max (u+1) v, max (u+2) (v+1)} AddCommGrpCat.{max (u+1) v} X
but is expected to have type
  TopCat.Sheaf.{u, u, ?u} ?m X
```

This file states the map at independent universes, and proves it invertible for a quasi-compact
`Z` whose distinct points are separated by disjoint opens of `X`. It is built from the unit of the
inverse-image/direct-image adjunction of the *site-level* `Functor.sheafPullback`, which has no
universe constraint, rather than from `TopCat.Sheaf.pullback`, which has.

## Main definitions

All in the namespace `Stacks.Topology`.

* `neighborhoodSectionsUnivLE`: the diagram `U ↦ F(U)` over the open neighbourhoods of `Z`, which
  are cofiltered.
* `subsetUnit`: the unit of the inverse-image/direct-image adjunction along the inclusion of `Z`.
* `ambientSectionUnivLE`: the canonical map `F(U) ⟶ (F|_Z)(V)` for `V ≤ i^{-1} U`, which is
  `Stacks.Topology.ambientSection` with the coefficients freed.
* `subsetSectionsMapUnivLE`: **the degree-zero comparison itself**, the map out of the colimit
  induced by those, which is `Stacks.Topology.subsetSectionsMap` with the coefficients freed.
* `presheafRestrictionUnivLE`, `preAmbientSectionUnivLE`, `preSubsetSectionsMapUnivLE`: the same
  three constructions before sheafification, on the left Kan extension of `F` along
  `(Opens.map i).op`.
* `sheafifyRestrictionIso`: the identification of the abstract inverse image used by
  `restrictionFunctorUnivLE` with the constructed one, `sheafToPresheaf ⋙ lan ⋙ presheafToSheaf`.
* `ambientDiagram`, `preAmbientCocone`, `isColimitPreAmbientCocone`: the filtered-colimit
  description of the presheaf inverse image at an open `V` of `Z`, over the opens `U` of `X` with
  `V ≤ i^{-1}U`.
* `sheafRestrictionUnivLE`: the sheafification of the presheaf inverse image, as a sheaf on `Z`.

## Main results

* `subsetPushforward_map_comp_res`: the morphism part of
  `(Opens.map i).sheafPushforwardContinuous`, composed with a restriction of `F|_Z`, is a single
  restriction of `F|_Z`. This is the lemma that makes the cocone below provable without `erw`;
  see the implementation note.
* `ambientSectionUnivLE_map`: restricting an ambient section to a smaller open of `X` does not
  change the section it induces on an open of `Z` inside both inverse images. This is
  `Stacks.Topology.ambientSection_map` with the coefficients freed, and it is the naturality of
  the cocone defining the comparison.
* `subsetSectionsMapUnivLE_ι`: the defining property of the comparison on the colimit cone.
* `subsetUnit_app_comp_sheafifyRestrictionIso` and
  `ambientSectionUnivLE_comp_sheafifyRestrictionIso`: the opaque unit of the abstract inverse
  image, followed by `sheafifyRestrictionIso`, is the explicit left-Kan-extension unit followed by
  `CategoryTheory.toSheafify`.
* `subsetSectionsMapUnivLE_comp_sheafifyRestrictionIso`: hence the degree-zero comparison is the
  presheaf-level comparison followed by sheafification.
* `isIso_subsetSectionsMapUnivLE_iff`: **the reduction the invertibility proof needs.** The
  comparison is invertible exactly when sheafification is bijective on the global sections of the
  presheaf inverse image — a statement in which `toSheafify` occurs explicitly, so that its local
  injectivity and local surjectivity (available at these universes; see below) apply.
* `exists_preAmbientSectionUnivLE` and `exists_restrict_eq_of_preAmbientSectionUnivLE_eq`: joint
  surjectivity and the equality criterion of that filtered colimit. These are the passage between
  an element of the presheaf inverse image at `V` and a section of `F` on an ambient `U` with
  `V ≤ i^{-1}U`, and they are the only interface the invertibility proof needs to the Kan
  extension.
* `injective_preSubsetSectionsMapUnivLE_toSheafify` and
  `surjective_preSubsetSectionsMapUnivLE_toSheafify`: the two halves, from local injectivity and
  local surjectivity of `toSheafify` together with the two stalk-free theorems of
  `CompactSubset/CompactSections.lean`.
* `isIso_subsetSectionsMapUnivLE`: **the degree-zero half of [Stacks, Tag 09V3] at a coefficient
  universe independent of the space.** The comparison is an isomorphism for `Z` quasi-compact with
  its distinct points separated by disjoint opens of `X`.
* `isIso_subsetSectionsMap_of_univLE`: nothing is weakened — at `t := s` the above is the
  library's `Stacks.Topology.isIso_subsetSectionsMap`, for the library's own comparison map.

## Implementation notes

Both the mechanical obstruction and the mathematical one recorded here in earlier rounds are
resolved; what follows records how, because both readings of the route were at one point wrong.

*The mechanical obstruction, and its fix.* A composite `F(U) ⟶ (i_* (F|_Z))(U) ⟶ (F|_Z)(V)`
type-checks, because `((Opens.map i).sheafPushforwardContinuous _ _ _).obj G` has `.obj.obj (op
U)` definitionally equal to `G.obj.obj (op ((Opens.map i).obj U))`; but the two spellings are not
syntactically equal and `Functor.sheafPushforwardContinuous` does not reduce at `instances`
transparency, so `rw` and `simp` cannot find even `Category.assoc` or `Category.comp_id` inside
such a composite — the rewrite is rejected with "the target expression is not type-correct under
the `implicit` transparency level". `erw` and
`set_option backward.isDefEq.respectTransparency false` are both avoided here. The
fix used here needs neither: `subsetPushforward_map_comp_res` is proved by `change` (which checks
definitional equality at *default* transparency, where `ObjectProperty.lift` does unfold) and
every associativity step of `ambientSectionUnivLE_map` is the term `Category.assoc _ _ _` rather
than a rewrite, so no tactic ever has to key-match inside the opaque composite. The same applies
to the `Sheaf`-versus-`TopCat.Sheaf` instance mismatch lower down, where the device is the
abstract `comp_cancel_mid`.

*The mathematical obstruction.* The pinned proof of invertibility
(`CompactSubset/SubsetSectionsOfCoeff.lean`) runs on stalks, and Mathlib's
`TopCat.Presheaf.stalk` is declared for `X : TopCat.{v}` with `[Category.{v} C]`, so neither it
nor `TopCat.Presheaf.germ`, `TopCat.Presheaf.germ_eq`, `TopCat.Presheaf.stalkPullbackIso` nor
`Stacks.Topology.ambientStalkHom` exists at the shape above. What *is* already available there is
the stalk-free half of `CompactSubset/CompactSections.lean` —
`exists_opens_restrict_eq_of_locallyEqOn` and
`exists_opens_glue_of_isCompact_of_pairwiseSeparated`, whose coefficient and space universes are
independent by design, exactly so that they would survive this generalisation. So both halves of
the argument survive and only the passage between "equal germs at a point" and "agree on a
neighbourhood of that point" does not.

That passage does **not** require porting stalk theory, and it is not pinned. Germs are needed
only to say that a section of the sheafification is locally in the image of the presheaf and that
two sections with the same image agree locally, and those two statements are
`CategoryTheory.Presheaf.IsLocallySurjective` and `CategoryTheory.Presheaf.IsLocallyInjective` of
`CategoryTheory.toSheafify`. Mathlib's *named* instances for those
(`Presheaf.isLocallyInjective_toSheafify`, `Presheaf.isLocallySurjective_toSheafify` and their
primed concrete-category variants, `Mathlib/CategoryTheory/Sites/LocallyInjective.lean` and
`Mathlib/CategoryTheory/Sites/LocallySurjective.lean`) are indeed pinned to `Type (max u v)` — they
go through the plus construction. But `CategoryTheory/Sites/LocallyBijective.lean` derives both from
`GrothendieckTopology.W_toSheafify` under `[J.WEqualsLocallyBijective A]` alone, at *fully
independent* universes, and that hypothesis is already available at mixed universes:
`Stacks.SheafOfModules.coefficientLocallyBijective`
(`CategoryTheory/Sites/Modules/GrothendieckAbelian.lean`) supplies
`J.WEqualsLocallyBijective AddCommGrpCat.{t}` for any site dominated by `t`. Probed at this
file's own variable block, all three of
`WEqualsLocallyBijective (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{t}`,
`IsLocallyInjective _ (toSheafify _ P)` and `IsLocallySurjective _ (toSheafify _ P)` are found by
instance search. So the germ-free route is open.

Using it needed a bridge from the comparison above to the *constructed* pullback, because
`Functor.sheafPullback` is `(sheafPushforwardContinuous).leftAdjoint`, an abstract left adjoint
whose unit is opaque, whereas `toSheafify` lives on
`Functor.sheafPullbackConstruction.sheafPullback = sheafToPresheaf ⋙ lan ⋙ presheafToSheaf`. That
bridge is `sheafifyRestrictionIso` and the three lemmas after it: the two are identified by
Mathlib's `sheafPullbackIso`, which is *by definition* an `Adjunction.leftAdjointUniq`, so
`Adjunction.unit_leftAdjointUniq_hom_app` transports the unit and
`Adjunction.map_restrictFullyFaithful_unit_app` unfolds the constructed one into
left-Kan-extension unit followed by `toSheafify`. The outcome is
`isIso_subsetSectionsMapUnivLE_iff`.

*The degree-zero isomorphism.* What that reduction leaves is bijectivity of `toSheafify` at `⊤`
on `presheafRestrictionUnivLE F Z`. Injectivity is local injectivity of `toSheafify` followed by
`exists_opens_restrict_eq_of_locallyEqOn`; surjectivity is local surjectivity followed by
`exists_opens_glue_of_isCompact_of_pairwiseSeparated` — both of those two already stated at
independent universes. Each half passes between an element of
`(presheafRestrictionUnivLE F Z).obj (op V)` and a section of `F` on an open `U` of `X` with
`V ≤ i^{-1}U`, which is the filtered-colimit description of the left Kan extension
(`Functor.isPointwiseLeftKanExtension`) over `CostructuredArrow (Opens.map i).op (op V)`; at
`V = ⊤` that index category is the `(OpenNhdsSet Z)ᵒᵖ` of `preSubsetSectionsMapUnivLE` itself.
Two facts about it are all that is used downstream, `exists_preAmbientSectionUnivLE` and
`exists_restrict_eq_of_preAmbientSectionUnivLE_eq`, so the colimit is not exposed further.

Surjectivity needs its local representatives chosen more carefully than local surjectivity alone
supplies them. The sieve gives, for each point `z` of `Z`, an open `W` of `Z` containing `z` and a
representative of `σ|_W`, which `exists_preAmbientSectionUnivLE` turns into a section of `F` on an
open `N` of `X` with `W ≤ i^{-1}N`; but the compatibility hypothesis of the gluing theorem asks
about points of `Z` lying in `N`, and such a point need not lie in `W`. The fix is
`exists_ambient_repr_toSheafify`: replace `N` by its intersection with an open of `X` cutting out
`W` (`exists_opensMap_subsetInclusion_eq`), so that the inverse image of the chosen open is `W` on
the nose. Compatibility is then local injectivity of `toSheafify` on `W p ⊓ W q`.

The three universe gaps this run had to bridge are all of one shape: a Mathlib instance stated at
the coefficient universe where the index category lives in the universe of the space. Each is
closed by a dominance transport — `preservesFilteredColimitsOfSize_of_univLE` for the forgetful
functor, and the ambient `UnivLE.{s, t}` for the limits and preservation hypotheses of
`TopCat.Sheaf.eq_of_locally_eq'` and of the two theorems of `CompactSections.lean`.

These declarations carry no tag. Stacks 0DCU has eight claim-sites and the covering set of the
tag is not complete until all of them are in the library; clause 8 is still unproved.

## References

* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

namespace Stacks.Topology

universe t s

noncomputable section

/-- Two consecutive restrictions of a presheaf on a preorder compose to the single restriction. -/
private theorem map_op_comp_map_op {C : Type*} [Category* C] {P : Type*} [Preorder P]
    (G : Pᵒᵖ ⥤ C) {A B D : P} (f : A ⟶ B) (g : D ⟶ A) (e : D ⟶ B) :
    G.map f.op ≫ G.map g.op = G.map e.op := by
  rw [← G.map_comp]
  exact congrArg _ (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

variable {X : TopCat.{s}} [UnivLE.{s, t}] (F : X.Sheaf AddCommGrpCat.{t}) (Z : Set X)

/-- Sections of an abelian sheaf over the open neighbourhoods of a subset, at a coefficient
universe independent of the space. This is `Stacks.Topology.neighborhoodSections` with the
coefficients freed. -/
abbrev neighborhoodSectionsUnivLE : (OpenNhdsSet Z)ᵒᵖ ⥤ AddCommGrpCat.{t} :=
  (openNhdsSetInclusion Z).op ⋙ F.presheaf

/-- The unit of the inverse-image/direct-image adjunction along the inclusion of `Z`, at a
coefficient universe independent of the space. -/
abbrev subsetUnit :
    F ⟶ ((Opens.map (Stacks.subsetInclusion X Z)).sheafPushforwardContinuous AddCommGrpCat.{t}
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (TopCat.of Z))).obj ((restrictionFunctorUnivLE.{t} X Z).obj F) :=
  (((Opens.map (Stacks.subsetInclusion X Z)).sheafAdjunctionContinuous AddCommGrpCat.{t}
    (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology (TopCat.of Z))).unit).app F

/-- **The canonical map from a section of `F` on an open `U` of `X` to a section of `F|_Z` on an
open `V` of `Z` contained in `i^{-1} U`**, at a coefficient universe independent of the space.
This is `Stacks.Topology.ambientSection` with the coefficients freed; it is the component of the
adjunction unit followed by a restriction. -/
def ambientSectionUnivLE {U : Opens X} {V : Opens (TopCat.of Z)}
    (h : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U) :
    F.presheaf.obj (op U) ⟶ ((restrictionFunctorUnivLE.{t} X Z).obj F).presheaf.obj (op V) :=
  (subsetUnit.{t} F Z).hom.app (op U) ≫
    ((restrictionFunctorUnivLE.{t} X Z).obj F).presheaf.map (homOfLE h).op

/-- **Restricting along the direct image of the inclusion, then down to an open of `Z`, is a
single restriction.** This is the identity `rw` and `simp` cannot find: the source of the first
factor is `((Opens.map i).sheafPushforwardContinuous _ _ _).obj (F|_Z)` applied at `op U`, which
is definitionally — but not syntactically — `(F|_Z)(i^{-1}U)`, and
`Functor.sheafPushforwardContinuous` does not unfold at `instances` transparency. `show` checks
definitional equality at default transparency, where `ObjectProperty.lift` does unfold, so the
goal can be restated in the spelling where both factors are maps of `(F|_Z)` and then closed by
functoriality. -/
theorem subsetPushforward_map_comp_res {U U' : Opens X} {V : Opens (TopCat.of Z)}
    (m : U' ⟶ U) (h : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U')
    (h' : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U) :
    (((Opens.map (Stacks.subsetInclusion X Z)).sheafPushforwardContinuous AddCommGrpCat.{t}
          (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology (TopCat.of Z))).obj
        ((restrictionFunctorUnivLE.{t} X Z).obj F)).obj.map m.op ≫
        ((restrictionFunctorUnivLE.{t} X Z).obj F).presheaf.map (homOfLE h).op =
      ((restrictionFunctorUnivLE.{t} X Z).obj F).presheaf.map (homOfLE h').op := by
  exact map_op_comp_map_op ((restrictionFunctorUnivLE.{t} X Z).obj F).presheaf
    ((Opens.map (Stacks.subsetInclusion X Z)).map m) (homOfLE h) (homOfLE h')

/-- **Restricting a section of `F` to a smaller open of `X` does not change the section it induces
on an open of `Z` inside both inverse images.** This is `Stacks.Topology.ambientSection_map` with
the coefficient universe freed, and it is the naturality of the cocone defining
`subsetSectionsMapUnivLE`.

Every step is a term rather than a rewrite: the middle object of the composite is the opaque
`sheafPushforwardContinuous` spelling, so `rw [Category.assoc]` fails on it (see the module's
implementation notes), while `Category.assoc _ _ _` applied as a term elaborates against the goal
at default transparency and succeeds. -/
theorem ambientSectionUnivLE_map {U U' : Opens X} {V : Opens (TopCat.of Z)}
    (m : U' ⟶ U) (h : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U')
    (h' : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U) :
    F.presheaf.map m.op ≫ ambientSectionUnivLE.{t} F Z h
      = ambientSectionUnivLE.{t} F Z h' :=
  (Category.assoc (F.presheaf.map m.op) ((subsetUnit.{t} F Z).hom.app (op U'))
      (((restrictionFunctorUnivLE.{t} X Z).obj F).presheaf.map (homOfLE h).op)).symm.trans
    ((congrArg (· ≫ ((restrictionFunctorUnivLE.{t} X Z).obj F).presheaf.map (homOfLE h).op)
        ((subsetUnit.{t} F Z).hom.naturality m.op)).trans
      ((Category.assoc _ _ _).trans
        (congrArg ((subsetUnit.{t} F Z).hom.app (op U) ≫ ·)
          (subsetPushforward_map_comp_res.{t} F Z m h h'))))

/-- **The degree-zero comparison of [Stacks, Tag 09V3], at a coefficient universe independent of
the space.** The canonical map `colim_{U ⊇ Z open} F(U) ⟶ Γ(Z, F|_Z)`. This is
`Stacks.Topology.subsetSectionsMap` with the coefficients freed; its invertibility for a
quasi-compact separated `Z` is the content of the degree-zero half of that tag and is *not* proved
here — see the module's implementation notes for the route and for what it still needs. -/
def subsetSectionsMapUnivLE :
    colimit (neighborhoodSectionsUnivLE.{t} F Z) ⟶
      ((restrictionFunctorUnivLE.{t} X Z).obj F).presheaf.obj (op ⊤) :=
  colimit.desc (neighborhoodSectionsUnivLE.{t} F Z)
    { pt := ((restrictionFunctorUnivLE.{t} X Z).obj F).presheaf.obj (op ⊤)
      ι :=
        { app := fun U ↦ ambientSectionUnivLE.{t} F Z (top_le_map_openNhdsSet U.unop)
          naturality := fun _ _ a ↦
            (ambientSectionUnivLE_map.{t} F Z ((openNhdsSetInclusion Z).map a.unop) _ _).trans
              (Category.comp_id _).symm } }

/-- The defining property of the comparison: on the component of the colimit cone at an open
neighbourhood `U` of `Z` it is the ambient-section map of `U`. -/
theorem subsetSectionsMapUnivLE_ι (U : (OpenNhdsSet Z)ᵒᵖ) :
    colimit.ι (neighborhoodSectionsUnivLE.{t} F Z) U ≫ subsetSectionsMapUnivLE.{t} F Z =
      ambientSectionUnivLE.{t} F Z (top_le_map_openNhdsSet U.unop) :=
  colimit.ι_desc _ _

section Constructed

/-- **The inverse image of `F` along the inclusion of `Z` as a presheaf**, before sheafification:
the left Kan extension of `F` along `(Opens.map i).op`. -/
abbrev presheafRestrictionUnivLE : (Opens (TopCat.of Z))ᵒᵖ ⥤ AddCommGrpCat.{t} :=
  (Opens.map (Stacks.subsetInclusion X Z)).op.lan.obj F.presheaf

/-- The unit of the left-Kan-extension adjunction at `F`, the presheaf-level analogue of
`subsetUnit`. -/
abbrev presheafRestrictionUnit :
    F.presheaf ⟶ (Opens.map (Stacks.subsetInclusion X Z)).op ⋙
      presheafRestrictionUnivLE.{t} F Z :=
  ((Opens.map (Stacks.subsetInclusion X Z)).op.lanAdjunction
    AddCommGrpCat.{t}).unit.app F.presheaf

/-- `ambientSectionUnivLE` before sheafification: the canonical map from a section of `F` on an
open `U` of `X` to a section of the *presheaf* inverse image on an open `V ≤ i^{-1} U` of `Z`. -/
def preAmbientSectionUnivLE {U : Opens X} {V : Opens (TopCat.of Z)}
    (h : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U) :
    F.presheaf.obj (op U) ⟶ (presheafRestrictionUnivLE.{t} F Z).obj (op V) :=
  (presheafRestrictionUnit.{t} F Z).app (op U) ≫
    (presheafRestrictionUnivLE.{t} F Z).map (homOfLE h).op

/-- `ambientSectionUnivLE_map` before sheafification. -/
theorem preAmbientSectionUnivLE_map {U U' : Opens X} {V : Opens (TopCat.of Z)}
    (m : U' ⟶ U) (h : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U')
    (h' : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U) :
    F.presheaf.map m.op ≫ preAmbientSectionUnivLE.{t} F Z h
      = preAmbientSectionUnivLE.{t} F Z h' := by
  have hres : ((Opens.map (Stacks.subsetInclusion X Z)).op ⋙
        presheafRestrictionUnivLE.{t} F Z).map m.op ≫
      (presheafRestrictionUnivLE.{t} F Z).map (homOfLE h).op =
      (presheafRestrictionUnivLE.{t} F Z).map (homOfLE h').op := by
    exact map_op_comp_map_op (presheafRestrictionUnivLE.{t} F Z)
      ((Opens.map (Stacks.subsetInclusion X Z)).map m) (homOfLE h) (homOfLE h')
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (presheafRestrictionUnivLE.{t} F Z).map (homOfLE h).op)
        ((presheafRestrictionUnit.{t} F Z).naturality m.op)).trans
      ((Category.assoc _ _ _).trans
        (congrArg ((presheafRestrictionUnit.{t} F Z).app (op U) ≫ ·) hres)))

/-- **The degree-zero comparison before sheafification**, `colim_{U ⊇ Z} F(U) ⟶ (i^{pre,-1}F)(⊤)`.
-/
def preSubsetSectionsMapUnivLE :
    colimit (neighborhoodSectionsUnivLE.{t} F Z) ⟶
      (presheafRestrictionUnivLE.{t} F Z).obj (op ⊤) :=
  colimit.desc (neighborhoodSectionsUnivLE.{t} F Z)
    { pt := (presheafRestrictionUnivLE.{t} F Z).obj (op ⊤)
      ι :=
        { app := fun U ↦ preAmbientSectionUnivLE.{t} F Z (top_le_map_openNhdsSet U.unop)
          naturality := fun _ _ a ↦
            (preAmbientSectionUnivLE_map.{t} F Z ((openNhdsSetInclusion Z).map a.unop) _ _).trans
              (Category.comp_id _).symm } }

/-- The comparison `preSubsetSectionsMapUnivLE` restricted to the sections over an open
neighbourhood `U` of `Z` is the induced section `preAmbientSectionUnivLE` over `U`. -/
theorem preSubsetSectionsMapUnivLE_ι (U : (OpenNhdsSet Z)ᵒᵖ) :
    colimit.ι (neighborhoodSectionsUnivLE.{t} F Z) U ≫ preSubsetSectionsMapUnivLE.{t} F Z =
      preAmbientSectionUnivLE.{t} F Z (top_le_map_openNhdsSet U.unop) :=
  colimit.ι_desc _ _

/-- **The abstract inverse image is the constructed one.** `restrictionFunctorUnivLE` is
`Functor.sheafPullback`, the abstract left adjoint of the direct image, whose unit is opaque;
`Functor.sheafPullbackConstruction.sheafPullback` is `sheafToPresheaf ⋙ lan ⋙ presheafToSheaf`,
where `CategoryTheory.toSheafify` and its local bijectivity live. This is Mathlib's
`sheafPullbackIso`, an `Adjunction.leftAdjointUniq`, evaluated at `F`. -/
def sheafifyRestrictionIso :
    (restrictionFunctorUnivLE.{t} X Z).obj F ≅
      (Functor.sheafPullbackConstruction.sheafPullback
        (Opens.map (Stacks.subsetInclusion X Z)) AddCommGrpCat.{t}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of Z))).obj F :=
  (Functor.sheafPullbackConstruction.sheafPullbackIso
    (Opens.map (Stacks.subsetInclusion X Z)) AddCommGrpCat.{t}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of Z))).app F

/-- The component of `sheafifyRestrictionIso` at each open `V` of `Z` is an isomorphism. -/
instance isIso_sheafifyRestrictionIso_app (V : Opens (TopCat.of Z)) :
    IsIso ((sheafifyRestrictionIso.{t} F Z).hom.hom.app (op V)) :=
  have : IsIso (sheafifyRestrictionIso.{t} F Z).hom.hom :=
    ⟨(sheafifyRestrictionIso.{t} F Z).inv.hom,
      congrArg (fun g ↦ g.hom) (sheafifyRestrictionIso.{t} F Z).hom_inv_id,
      congrArg (fun g ↦ g.hom) (sheafifyRestrictionIso.{t} F Z).inv_hom_id⟩
  inferInstance

/-- **The two units agree across `sheafifyRestrictionIso`.** The opaque unit of the abstract
adjunction, followed by the identification, is the explicit composite of the left-Kan-extension
unit with `toSheafify`. This is `Adjunction.unit_leftAdjointUniq_hom_app` for the identification
and `Adjunction.map_restrictFullyFaithful_unit_app` together with the unit of a composed
adjunction for the explicit side. -/
theorem subsetUnit_app_comp_sheafifyRestrictionIso (U : Opens X) :
    (subsetUnit.{t} F Z).hom.app (op U) ≫
        (sheafifyRestrictionIso.{t} F Z).hom.hom.app
          (op ((Opens.map (Stacks.subsetInclusion X Z)).obj U)) =
      (presheafRestrictionUnit.{t} F Z).app (op U) ≫
        (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
          (presheafRestrictionUnivLE.{t} F Z)).app
          (op ((Opens.map (Stacks.subsetInclusion X Z)).obj U)) := by
  have h2 := Adjunction.map_restrictFullyFaithful_unit_app
    (L := Functor.sheafPullbackConstruction.sheafPullback
      (Opens.map (Stacks.subsetInclusion X Z)) AddCommGrpCat.{t}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of Z)))
    (R := (Opens.map (Stacks.subsetInclusion X Z)).sheafPushforwardContinuous AddCommGrpCat.{t}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of Z)))
    (((Opens.map (Stacks.subsetInclusion X Z)).op.lanAdjunction AddCommGrpCat.{t}).comp
      (sheafificationAdjunction (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{t}))
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{t})
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _) F
  simp only [Iso.refl_hom, NatTrans.id_app] at h2
  refine Eq.trans ?_ (congrArg (fun g ↦ g.app (op U)) h2)
  exact congrArg (fun g ↦ g.hom.app (op U))
    (Adjunction.unit_leftAdjointUniq_hom_app
      ((Opens.map (Stacks.subsetInclusion X Z)).sheafAdjunctionContinuous AddCommGrpCat.{t}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of Z)))
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map (Stacks.subsetInclusion X Z)) AddCommGrpCat.{t}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of Z))) F)

/-- **The ambient-section map is the presheaf-level one followed by sheafification.** -/
theorem ambientSectionUnivLE_comp_sheafifyRestrictionIso {U : Opens X}
    {V : Opens (TopCat.of Z)} (h : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U) :
    ambientSectionUnivLE.{t} F Z h ≫ (sheafifyRestrictionIso.{t} F Z).hom.hom.app (op V) =
      preAmbientSectionUnivLE.{t} F Z h ≫
        (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
          (presheafRestrictionUnivLE.{t} F Z)).app (op V) :=
  (Category.assoc _ _ _).trans
    ((congrArg ((subsetUnit.{t} F Z).hom.app (op U) ≫ ·)
        ((sheafifyRestrictionIso.{t} F Z).hom.hom.naturality (homOfLE h).op)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) (subsetUnit_app_comp_sheafifyRestrictionIso.{t} F Z U)).trans
          ((Category.assoc _ _ _).trans
            ((congrArg ((presheafRestrictionUnit.{t} F Z).app (op U) ≫ ·)
              ((toSheafify (Opens.grothendieckTopology (TopCat.of Z))
                (presheafRestrictionUnivLE.{t} F Z)).naturality
                  (homOfLE h).op).symm).trans (Category.assoc _ _ _).symm)))))

/-- **The degree-zero comparison is the presheaf-level comparison followed by sheafification.** -/
theorem subsetSectionsMapUnivLE_comp_sheafifyRestrictionIso :
    subsetSectionsMapUnivLE.{t} F Z ≫
        (sheafifyRestrictionIso.{t} F Z).hom.hom.app (op ⊤) =
      preSubsetSectionsMapUnivLE.{t} F Z ≫
        (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
          (presheafRestrictionUnivLE.{t} F Z)).app (op ⊤) := by
  refine colimit.hom_ext fun U ↦ ?_
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (sheafifyRestrictionIso.{t} F Z).hom.hom.app (op ⊤))
      (subsetSectionsMapUnivLE_ι.{t} F Z U))).trans
    ((ambientSectionUnivLE_comp_sheafifyRestrictionIso.{t} F Z
      (top_le_map_openNhdsSet U.unop)).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
          (presheafRestrictionUnivLE.{t} F Z)).app (op ⊤))
        (preSubsetSectionsMapUnivLE_ι.{t} F Z U))).symm)

/-- **The degree-zero comparison of [Stacks, Tag 09V3] at mixed universes is invertible exactly
when sheafification is bijective on the global sections of the presheaf inverse image.** This is
the reduction the invertibility proof needs: on the right-hand side `toSheafify` appears
explicitly, and `CategoryTheory.Presheaf.IsLocallyInjective` and
`CategoryTheory.Presheaf.IsLocallySurjective` of it are available at these universes from
`Stacks.SheafOfModules.coefficientLocallyBijective` through
`CategoryTheory/Sites/LocallyBijective.lean` — no stalks and no germs. -/
theorem isIso_subsetSectionsMapUnivLE_iff :
    IsIso (subsetSectionsMapUnivLE.{t} F Z) ↔
      IsIso (preSubsetSectionsMapUnivLE.{t} F Z ≫
        (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
          (presheafRestrictionUnivLE.{t} F Z)).app (op ⊤)) := by
  rw [← subsetSectionsMapUnivLE_comp_sheafifyRestrictionIso]
  have he := isIso_sheafifyRestrictionIso_app.{t} F Z (⊤ : Opens (TopCat.of Z))
  exact ⟨fun h ↦ IsIso.comp_isIso' h he, fun h ↦
    @IsIso.of_isIso_comp_right _ _ _ _ _ (subsetSectionsMapUnivLE.{t} F Z)
      ((sheafifyRestrictionIso.{t} F Z).hom.hom.app (op ⊤)) he h⟩

end Constructed

section Invertibility

/-- The forgetful functor of abelian groups preserves filtered colimits indexed by a category in
the universe of the space. Mathlib's instance is stated at the universe of the coefficients, which
is not the universe the index categories below live in; the two are reconciled by the dominance
hypothesis. Not an instance, because its conclusion is the key of Mathlib's own and the search
would loop through it. -/
private theorem preservesFilteredColimits_forget_univLE :
    PreservesFilteredColimitsOfSize.{s, s} (CategoryTheory.forget AddCommGrpCat.{t}) :=
  preservesFilteredColimitsOfSize_of_univLE.{t, t, s, s} _

/-- **The index category of the colimit computing the presheaf inverse image at `V` is filtered**:
its objects are the opens `U` of `X` with `V ≤ i^{-1}U`, ordered by reverse inclusion, and any two
are refined by their intersection.

Mathlib proves `RepresentablyFlat (Opens.map f)`
(`Mathlib/Topology/Sheaves/SheafCondition/Sites.lean`), from which this would follow, but that
instance sits in a section whose variables include a presheaf `F : Y.Presheaf C`, so the
auto-included `F` becomes an argument that instance search cannot synthesize and the instance is
never found; the library's `Stacks.PullbackModel.representablyFlat_opensMap` exists for the same
reason. It is `private` here so as not to add a third public name for one fact: the interface this
file exports is `exists_preAmbientSectionUnivLE` and
`exists_restrict_eq_of_preAmbientSectionUnivLE_eq`. -/
private instance isFiltered_costructuredArrow_subsetInclusion (V : Opens (TopCat.of Z)) :
    IsFiltered (CostructuredArrow (Opens.map (Stacks.subsetInclusion X Z)).op (op V)) where
  cocone_objs g g' :=
    ⟨CostructuredArrow.mk (Y := op (g.left.unop ⊓ g'.left.unop))
      (homOfLE (fun z hz ↦ ⟨g.hom.unop.le hz, g'.hom.unop.le hz⟩)).op,
      CostructuredArrow.homMk (homOfLE inf_le_left).op (Subsingleton.elim _ _),
      CostructuredArrow.homMk (homOfLE inf_le_right).op (Subsingleton.elim _ _), trivial⟩
  cocone_maps _ g' _ _ :=
    ⟨g', 𝟙 _, by congr 1; exact CostructuredArrow.hom_ext _ _ (Subsingleton.elim _ _)⟩
  nonempty := ⟨CostructuredArrow.mk (Y := op (⊤ : Opens X)) (homOfLE le_top).op⟩

/-- The diagram whose filtered colimit is the presheaf inverse image at `V`: a section of `F` on
an open `U` of `X` with `V ≤ i^{-1}U`. -/
abbrev ambientDiagram (V : Opens (TopCat.of Z)) :
    CostructuredArrow (Opens.map (Stacks.subsetInclusion X Z)).op (op V) ⥤ AddCommGrpCat.{t} :=
  CostructuredArrow.proj (Opens.map (Stacks.subsetInclusion X Z)).op (op V) ⋙ F.presheaf

/-- The cocone on `ambientDiagram` whose vertex is the presheaf inverse image at `V` and whose
legs are the pre-ambient-section maps. This is the cocone of the pointwise left Kan extension. -/
def preAmbientCocone (V : Opens (TopCat.of Z)) : Cocone (ambientDiagram.{t} F Z V) :=
  Functor.LeftExtension.coconeAt
    (Functor.LeftExtension.mk _
      ((Opens.map (Stacks.subsetInclusion X Z)).op.leftKanExtensionUnit F.presheaf)) (op V)

/-- **The filtered-colimit description of the presheaf inverse image.** This is
`Functor.isPointwiseLeftKanExtension` for the left Kan extension along `(Opens.map i).op`. -/
def isColimitPreAmbientCocone (V : Opens (TopCat.of Z)) :
    IsColimit (preAmbientCocone.{t} F Z V) :=
  (Opens.map (Stacks.subsetInclusion X Z)).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit
    F.presheaf (op V)

/-- The legs of the colimit cocone are the pre-ambient-section maps. -/
theorem preAmbientCocone_ι_app (V : Opens (TopCat.of Z))
    (g : CostructuredArrow (Opens.map (Stacks.subsetInclusion X Z)).op (op V)) :
    (preAmbientCocone.{t} F Z V).ι.app g = preAmbientSectionUnivLE.{t} F Z g.hom.unop.le :=
  congrArg (fun m ↦ _ ≫ (presheafRestrictionUnivLE.{t} F Z).map m)
    (Quiver.Hom.unop_inj (Subsingleton.elim g.hom.unop (homOfLE g.hom.unop.le)))

/-- Restricting an induced section of the presheaf inverse image to a smaller open of `Z` is the
section induced on that open. -/
theorem preAmbientSectionUnivLE_res {U : Opens X} {V V' : Opens (TopCat.of Z)}
    (k : V' ⟶ V) (h : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U) :
    preAmbientSectionUnivLE.{t} F Z h ≫ (presheafRestrictionUnivLE.{t} F Z).map k.op =
      preAmbientSectionUnivLE.{t} F Z (k.le.trans h) :=
  (Category.assoc _ _ _).trans
    (congrArg ((presheafRestrictionUnit.{t} F Z).app (op U) ≫ ·)
      (map_op_comp_map_op (presheafRestrictionUnivLE.{t} F Z) (homOfLE h) k _))

/-- `preAmbientSectionUnivLE_res` on elements. -/
theorem preAmbientSectionUnivLE_res_apply {U : Opens X} {V V' : Opens (TopCat.of Z)}
    (k : V' ⟶ V) (h : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U)
    (a : ToType (F.presheaf.obj (op U))) :
    (presheafRestrictionUnivLE.{t} F Z).map k.op (preAmbientSectionUnivLE.{t} F Z h a) =
      preAmbientSectionUnivLE.{t} F Z (k.le.trans h) a :=
  (ConcreteCategory.comp_apply _ _ a).symm.trans
    (ConcreteCategory.congr_hom (preAmbientSectionUnivLE_res.{t} F Z k h) a)

/-- `preAmbientSectionUnivLE_map` on elements. -/
theorem preAmbientSectionUnivLE_map_apply {U U' : Opens X} {V : Opens (TopCat.of Z)}
    (m : U' ⟶ U) (h : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U')
    (h' : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U)
    (a : ToType (F.presheaf.obj (op U))) :
    preAmbientSectionUnivLE.{t} F Z h (F.presheaf.map m.op a) =
      preAmbientSectionUnivLE.{t} F Z h' a :=
  (ConcreteCategory.comp_apply _ _ a).symm.trans
    (ConcreteCategory.congr_hom (preAmbientSectionUnivLE_map.{t} F Z m h h') a)

/-- **Every section of the presheaf inverse image on an open of `Z` is induced by a section of `F`
on an open of `X`.** This is joint surjectivity of the filtered colimit above. -/
theorem exists_preAmbientSectionUnivLE (V : Opens (TopCat.of Z))
    (x : ToType ((presheafRestrictionUnivLE.{t} F Z).obj (op V))) :
    ∃ (U : Opens X) (h : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U)
      (a : ToType (F.presheaf.obj (op U))), preAmbientSectionUnivLE.{t} F Z h a = x := by
  have := preservesFilteredColimits_forget_univLE.{t, s}
  obtain ⟨g, a, ha⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{t})
      (isColimitPreAmbientCocone.{t} F Z V)) x
  exact ⟨g.left.unop, g.hom.unop.le, a,
    (ConcreteCategory.congr_hom (preAmbientCocone_ι_app.{t} F Z V g) a).symm.trans ha⟩

/-- **Two sections of `F` inducing the same section of the presheaf inverse image on `V` already
agree on a smaller open of `X` whose inverse image still contains `V`.** This is the equality
criterion in the filtered colimit above.

Both cocone legs are supplied with their `CostructuredArrow` spelled out: left to unification, the
higher-order problem of matching `preAmbientSectionUnivLE F Z ?g.hom.unop.le` against a given
proof of `V ≤ i^{-1}U` exhausts the heartbeat budget. -/
theorem exists_restrict_eq_of_preAmbientSectionUnivLE_eq {U U' : Opens X}
    {V : Opens (TopCat.of Z)} (h : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U)
    (h' : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U')
    (a : ToType (F.presheaf.obj (op U))) (a' : ToType (F.presheaf.obj (op U')))
    (he : preAmbientSectionUnivLE.{t} F Z h a = preAmbientSectionUnivLE.{t} F Z h' a') :
    ∃ (W : Opens X) (_ : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj W)
      (m : W ⟶ U) (m' : W ⟶ U'),
      F.presheaf.map m.op a = F.presheaf.map m'.op a' := by
  have := preservesFilteredColimits_forget_univLE.{t, s}
  have hc := isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{t})
    (isColimitPreAmbientCocone.{t} F Z V)
  have e1 := ConcreteCategory.congr_hom (preAmbientCocone_ι_app.{t} F Z V
    (CostructuredArrow.mk (Y := op U) (homOfLE h).op)) a
  have e2 := ConcreteCategory.congr_hom (preAmbientCocone_ι_app.{t} F Z V
    (CostructuredArrow.mk (Y := op U') (homOfLE h').op)) a'
  have key : ((CategoryTheory.forget AddCommGrpCat.{t}).mapCocone
        (preAmbientCocone.{t} F Z V)).ι.app
        (CostructuredArrow.mk (Y := op U) (homOfLE h).op) a =
      ((CategoryTheory.forget AddCommGrpCat.{t}).mapCocone
        (preAmbientCocone.{t} F Z V)).ι.app
        (CostructuredArrow.mk (Y := op U') (homOfLE h').op) a' :=
    e1.trans (he.trans e2.symm)
  obtain ⟨k, f, f', hff⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hc).mp key
  exact ⟨k.left.unop, k.hom.unop.le, f.left.unop, f'.left.unop, hff⟩

omit [UnivLE.{s, t}] in
/-- Every open of `Z` is the inverse image of an open of `X`, the subspace topology being
induced. This is the shrinking step that turns a local representative of a section of the
sheafification into one whose inverse image is exactly the open it is a representative on. -/
theorem exists_opensMap_subsetInclusion_eq (W : Opens (TopCat.of Z)) :
    ∃ O : Opens X, (Opens.map (Stacks.subsetInclusion X Z)).obj O = W := by
  obtain ⟨O, hO, hWO⟩ := isOpen_induced_iff.mp W.2
  exact ⟨⟨O, hO⟩, Opens.ext hWO⟩

/-- Every element of the colimit over the open neighbourhoods of `Z` is represented by a section
of `F` on one of them. -/
theorem exists_colimit_ι_neighborhoodSectionsUnivLE
    (α : ToType (colimit (neighborhoodSectionsUnivLE.{t} F Z))) :
    ∃ (U : (OpenNhdsSet Z)ᵒᵖ) (s : ToType ((neighborhoodSectionsUnivLE.{t} F Z).obj U)),
      colimit.ι (neighborhoodSectionsUnivLE.{t} F Z) U s = α := by
  have := preservesFilteredColimits_forget_univLE.{t, s}
  obtain ⟨U, s, e⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{t}) (colimit.isColimit _)) α
  exact ⟨U, s, e⟩

/-- A section on a neighbourhood of `Z` and its restriction to a smaller one represent the same
element of the colimit. -/
theorem colimit_ι_neighborhoodSectionsUnivLE_map {U : (OpenNhdsSet Z)ᵒᵖ} {V : OpenNhdsSet Z}
    (a : V ⟶ U.unop) (s : ToType ((neighborhoodSectionsUnivLE.{t} F Z).obj U)) :
    colimit.ι (neighborhoodSectionsUnivLE.{t} F Z) (op V)
        (F.presheaf.map ((openNhdsSetInclusion Z).map a).op s) =
      colimit.ι (neighborhoodSectionsUnivLE.{t} F Z) U s :=
  (ConcreteCategory.comp_apply _ _ s).symm.trans
    (ConcreteCategory.congr_hom (colimit.w (neighborhoodSectionsUnivLE.{t} F Z) a.op) s)

/-- The presheaf-level comparison followed by sheafification, on the colimit cone. -/
theorem preSubsetSectionsMapUnivLE_toSheafify_ι (U : (OpenNhdsSet Z)ᵒᵖ)
    (s : ToType ((neighborhoodSectionsUnivLE.{t} F Z).obj U)) :
    (preSubsetSectionsMapUnivLE.{t} F Z ≫
        (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
          (presheafRestrictionUnivLE.{t} F Z)).app (op ⊤))
        (colimit.ι (neighborhoodSectionsUnivLE.{t} F Z) U s) =
      (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
        (presheafRestrictionUnivLE.{t} F Z)).app (op ⊤)
        (preAmbientSectionUnivLE.{t} F Z (top_le_map_openNhdsSet U.unop) s) :=
  (ConcreteCategory.comp_apply _ _ s).symm.trans
    (ConcreteCategory.congr_hom
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
          (presheafRestrictionUnivLE.{t} F Z)).app (op ⊤))
          (preSubsetSectionsMapUnivLE_ι.{t} F Z U))) s)

/-- **Two sections of `F` with the same image under `toSheafify` agree near every point.** If the
induced sections of the presheaf inverse image on `V` become equal in the sheafification, then
near each point of `V` they are restrictions of one section on an open of `X`. -/
private theorem exists_restrict_eq_of_toSheafify_eq {U U' : Opens X} {V : Opens (TopCat.of Z)}
    (h : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U)
    (h' : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U')
    (a : ToType (F.presheaf.obj (op U))) (a' : ToType (F.presheaf.obj (op U')))
    (he : (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
        (presheafRestrictionUnivLE.{t} F Z)).app (op V) (preAmbientSectionUnivLE.{t} F Z h a) =
      (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
        (presheafRestrictionUnivLE.{t} F Z)).app (op V) (preAmbientSectionUnivLE.{t} F Z h' a'))
    (z : TopCat.of Z) (hz : z ∈ V) :
    ∃ (N : Opens X) (_ : (z : X) ∈ N) (m : N ⟶ U) (m' : N ⟶ U'),
      F.presheaf.map m.op a = F.presheaf.map m'.op a' := by
  obtain ⟨W, f, hf, hzW⟩ := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology (TopCat.of Z))
    (toSheafify (Opens.grothendieckTopology (TopCat.of Z)) (presheafRestrictionUnivLE.{t} F Z))
    _ _ he z hz
  obtain ⟨N, hN, m, m', hmm⟩ := exists_restrict_eq_of_preAmbientSectionUnivLE_eq.{t} F Z _ _ a a'
    ((preAmbientSectionUnivLE_res_apply.{t} F Z f h a).symm.trans
      (hf.trans (preAmbientSectionUnivLE_res_apply.{t} F Z f h' a')))
  exact ⟨N, hN hzW, m, m', hmm⟩

/-- **Injectivity of the degree-zero comparison, for an arbitrary subset of an arbitrary space.**
Local injectivity of `toSheafify` turns the hypothesis into an agreement of `s` and `t` near every
point of `Z`, and `exists_opens_restrict_eq_of_locallyEqOn` glues those into an agreement on a
single neighbourhood of `Z`. No compactness and no separation. -/
theorem injective_preSubsetSectionsMapUnivLE_toSheafify :
    Function.Injective (preSubsetSectionsMapUnivLE.{t} F Z ≫
      (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
        (presheafRestrictionUnivLE.{t} F Z)).app (op ⊤)) := by
  intro α β hαβ
  obtain ⟨i, s, rfl⟩ := exists_colimit_ι_neighborhoodSectionsUnivLE.{t} F Z α
  obtain ⟨j, u, rfl⟩ := exists_colimit_ι_neighborhoodSectionsUnivLE.{t} F Z β
  rw [preSubsetSectionsMapUnivLE_toSheafify_ι, preSubsetSectionsMapUnivLE_toSheafify_ι] at hαβ
  have hloc : ∀ x ∈ Z, ∃ (N : Opens X) (_ : x ∈ N) (iNU : N ⟶ i.unop.obj) (iNV : N ⟶ j.unop.obj),
      F.presheaf.map iNU.op s = F.presheaf.map iNV.op u := fun x hx ↦
    exists_restrict_eq_of_toSheafify_eq.{t} F Z _ _ s u hαβ ⟨x, hx⟩ (Opens.mem_top _)
  obtain ⟨A, hZA, iAi, iAj, hA⟩ := exists_opens_restrict_eq_of_locallyEqOn F s u hloc
  have hAi : (⟨A, hZA⟩ : OpenNhdsSet Z) ⟶ i.unop := ObjectProperty.homMk iAi
  have hAj : (⟨A, hZA⟩ : OpenNhdsSet Z) ⟶ j.unop := ObjectProperty.homMk iAj
  rw [← colimit_ι_neighborhoodSectionsUnivLE_map.{t} F Z hAi s,
    ← colimit_ι_neighborhoodSectionsUnivLE_map.{t} F Z hAj u]
  refine congrArg (colimit.ι (neighborhoodSectionsUnivLE.{t} F Z)
    (op (⟨A, hZA⟩ : OpenNhdsSet Z))) ?_
  rw [Subsingleton.elim ((openNhdsSetInclusion Z).map hAi) iAi,
    Subsingleton.elim ((openNhdsSetInclusion Z).map hAj) iAj]
  exact hA

/-- The sheafification of the presheaf inverse image, as a sheaf on `Z`. Naming it is what makes
the sheaf axiom available for the surjectivity argument: `CategoryTheory.sheafify` is only a
presheaf, while `TopCat.Sheaf.eq_of_locally_eq'` asks for a `TopCat.Sheaf`. -/
@[ega "0 3.7.1" "special case"]
def sheafRestrictionUnivLE : (TopCat.of Z).Sheaf AddCommGrpCat.{t} :=
  (presheafToSheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{t}).obj
    (presheafRestrictionUnivLE.{t} F Z)

/-- The underlying presheaf of `sheafRestrictionUnivLE` is the sheafification of the presheaf
inverse image `presheafRestrictionUnivLE`. -/
theorem sheafRestrictionUnivLE_presheaf :
    (sheafRestrictionUnivLE.{t} F Z).presheaf =
      CategoryTheory.sheafify (Opens.grothendieckTopology (TopCat.of Z))
        (presheafRestrictionUnivLE.{t} F Z) := rfl

/-- **An ambient section representing a section of the sheafification on an open of `Z` represents
it on every smaller open.** This is the one step the surjectivity argument performs repeatedly,
and isolating it is what keeps that argument short.

The open `W₀` carrying the prescribed section is a parameter rather than `⊤`: the softness
argument of `CompactSubset/FlasqueSoftUnivLE.lean` runs this step on an open neighbourhood of a
closed subset of `Z`, and the `⊤` case is the one used below. -/
theorem toSheafify_preAmbientSectionUnivLE_restrict {W₀ W W' : Opens (TopCat.of Z)}
    {M : Opens X} (hWM : W ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj M)
    (a : ToType (F.presheaf.obj (op M)))
    (σ : ToType ((sheafRestrictionUnivLE.{t} F Z).presheaf.obj (op W₀))) (g : W ⟶ W₀)
    (ha : (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
        (presheafRestrictionUnivLE.{t} F Z)).app (op W)
        (preAmbientSectionUnivLE.{t} F Z hWM a) =
      (sheafRestrictionUnivLE.{t} F Z).presheaf.map g.op σ)
    (k : W' ⟶ W) (g' : W' ⟶ W₀) :
    (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
        (presheafRestrictionUnivLE.{t} F Z)).app (op W')
        (preAmbientSectionUnivLE.{t} F Z (k.le.trans hWM) a) =
      (sheafRestrictionUnivLE.{t} F Z).presheaf.map g'.op σ :=
  ((congrArg _ (preAmbientSectionUnivLE_res_apply.{t} F Z k hWM a).symm).trans
    (NatTrans.naturality_apply (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
      (presheafRestrictionUnivLE.{t} F Z)) k.op _)).trans
    ((congrArg _ ha).trans
      (map_op_comp_apply (sheafRestrictionUnivLE.{t} F Z).presheaf k g g' σ))

/-- **Near every point of an open `W₀` of `Z`, a section of the sheafification over `W₀` is
induced by a section of `F` on an open `M` of `X` whose inverse image is exactly the open on which
the two agree.**

Local surjectivity of `toSheafify` supplies an open `W ≤ W₀` of `Z` and a representative there,
and `exists_preAmbientSectionUnivLE` turns that representative into a section of `F` on an open
`N` of `X` with `W ≤ i^{-1}N`. Intersecting `N` with an open of `X` cutting out `W` makes the
inverse image equal to `W`, which is what the compatibility step of the gluing needs: it has to
know that a point of `Z` lying in `M` lies in `W`.

`W₀` is a parameter rather than `⊤` for the reason recorded at
`toSheafify_preAmbientSectionUnivLE_restrict`. -/
theorem exists_ambient_repr_toSheafify {W₀ : Opens (TopCat.of Z)}
    (σ : ToType ((sheafRestrictionUnivLE.{t} F Z).presheaf.obj (op W₀))) (z : TopCat.of Z)
    (hz : z ∈ W₀) :
    ∃ (M : Opens X) (W : Opens (TopCat.of Z)) (_ : z ∈ W) (hWW₀ : W ≤ W₀)
      (hWM : W ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj M)
      (_ : (Opens.map (Stacks.subsetInclusion X Z)).obj M ≤ W)
      (a : ToType (F.presheaf.obj (op M))),
      (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
          (presheafRestrictionUnivLE.{t} F Z)).app (op W)
          (preAmbientSectionUnivLE.{t} F Z hWM a) =
        (sheafRestrictionUnivLE.{t} F Z).presheaf.map (homOfLE hWW₀).op σ := by
  obtain ⟨W, f, ⟨x, hx⟩, hzW⟩ := Presheaf.imageSieve_mem
    (Opens.grothendieckTopology (TopCat.of Z))
    (toSheafify (Opens.grothendieckTopology (TopCat.of Z)) (presheafRestrictionUnivLE.{t} F Z))
    σ z hz
  obtain ⟨N, hWN, a, ha⟩ := exists_preAmbientSectionUnivLE.{t} F Z W x
  obtain ⟨O, hOW⟩ := exists_opensMap_subsetInclusion_eq Z W
  refine ⟨N ⊓ O, W, hzW, f.le, fun y hy ↦ ⟨hWN hy, le_of_eq hOW.symm hy⟩,
    fun y hy ↦ le_of_eq hOW hy.2,
    F.presheaf.map (homOfLE (inf_le_left : N ⊓ O ≤ N)).op a, ?_⟩
  refine (congrArg _ ((preAmbientSectionUnivLE_map_apply.{t} F Z
    (homOfLE (inf_le_left : N ⊓ O ≤ N)) _ hWN a).trans ha)).trans (hx.trans ?_)
  exact congrArg (fun g : W ⟶ W₀ ↦
    (sheafRestrictionUnivLE.{t} F Z).presheaf.map g.op σ) (Subsingleton.elim f _)

/-- **Surjectivity of the degree-zero comparison** for a quasi-compact subset whose distinct
points are separated by disjoint opens of the ambient space.

The chosen local representatives are pairwise compatible near every point of `Z` by local
injectivity of `toSheafify`, so `exists_opens_glue_of_isCompact_of_pairwiseSeparated` shrinks the
cover and glues them to a section of `F` on an open neighbourhood of `Z`. That the glued section
induces the prescribed one is checked on the cover by the sheaf axiom for the sheafification. -/
theorem surjective_preSubsetSectionsMapUnivLE_toSheafify (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B) :
    Function.Surjective (preSubsetSectionsMapUnivLE.{t} F Z ≫
      (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
        (presheafRestrictionUnivLE.{t} F Z)).app (op ⊤)) := by
  classical
  intro σ
  choose M W hzW hWtop hWM hMW a ha using fun z : TopCat.of Z ↦
    exists_ambient_repr_toSheafify.{t} F Z σ z (Opens.mem_top z)
  have hcover : Z ⊆ ⋃ z : Z, (M z : Set X) := fun w hw ↦
    Set.mem_iUnion.2 ⟨⟨w, hw⟩, hWM ⟨w, hw⟩ (hzW ⟨w, hw⟩)⟩
  have hcompat : ∀ p q : Z, ∀ w ∈ Z ∩ (M p : Set X) ∩ (M q : Set X),
      ∃ (R : Opens X) (_ : w ∈ R) (iRp : R ⟶ M p) (iRq : R ⟶ M q),
        F.presheaf.map iRp.op (a p) = F.presheaf.map iRq.op (a q) := by
    intro p q w hw
    have hzp : (⟨w, hw.1.1⟩ : TopCat.of Z) ∈ W p := hMW p hw.1.2
    have hzq : (⟨w, hw.1.1⟩ : TopCat.of Z) ∈ W q := hMW q hw.2
    have hkp : W p ⊓ W q ⟶ W p := homOfLE inf_le_left
    have hkq : W p ⊓ W q ⟶ W q := homOfLE inf_le_right
    have hep := toSheafify_preAmbientSectionUnivLE_restrict.{t} F Z (hWM p) (a p) σ
      (homOfLE (hWtop p)) (ha p) hkp (homOfLE le_top)
    have heq := toSheafify_preAmbientSectionUnivLE_restrict.{t} F Z (hWM q) (a q) σ
      (homOfLE (hWtop q)) (ha q) hkq (homOfLE le_top)
    exact exists_restrict_eq_of_toSheafify_eq.{t} F Z _ _ (a p) (a q)
      (hep.trans (Eq.trans
        (congrArg (fun g : W p ⊓ W q ⟶ ⊤ ↦
          (sheafRestrictionUnivLE.{t} F Z).presheaf.map g.op σ) (Subsingleton.elim _ _))
        heq.symm)) ⟨w, hw.1.1⟩ ⟨hzp, hzq⟩
  obtain ⟨V, iVM, hZV, c, hc⟩ :=
    exists_opens_glue_of_isCompact_of_pairwiseSeparated F hZ hSep M a hcover hcompat
  refine ⟨colimit.ι (neighborhoodSectionsUnivLE.{t} F Z)
    (op (⟨⨆ z, V z, hZV⟩ : OpenNhdsSet Z)) c,
    (preSubsetSectionsMapUnivLE_toSheafify_ι.{t} F Z
      (op (⟨⨆ z, V z, hZV⟩ : OpenNhdsSet Z)) c).trans ?_⟩
  refine (sheafRestrictionUnivLE.{t} F Z).eq_of_locally_eq'
    (fun z : Z ↦ (Opens.map (Stacks.subsetInclusion X Z)).obj (V z)) ⊤
    (fun _ ↦ homOfLE le_top) (fun y _ ↦ ?_) _ _ fun z ↦ ?_
  · obtain ⟨z, hz⟩ := Opens.mem_iSup.1 (hZV y.2)
    exact Opens.mem_iSup.2 ⟨z, hz⟩
  · have hQV : (Opens.map (Stacks.subsetInclusion X Z)).obj (V z) ≤
        (Opens.map (Stacks.subsetInclusion X Z)).obj (V z) := le_rfl
    have hQW : (Opens.map (Stacks.subsetInclusion X Z)).obj (V z) ⟶ W z :=
      homOfLE (fun y hy ↦ hMW z ((iVM z).le hy))
    refine Eq.trans ?_ (toSheafify_preAmbientSectionUnivLE_restrict.{t} F Z
      (hWM z) (a z) σ (homOfLE (hWtop z)) (ha z) hQW (homOfLE le_top))
    refine (NatTrans.naturality_apply (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
      (presheafRestrictionUnivLE.{t} F Z)) (homOfLE (le_top :
        (Opens.map (Stacks.subsetInclusion X Z)).obj (V z) ≤ ⊤)).op _).symm.trans
      (congrArg _ ?_)
    refine (preAmbientSectionUnivLE_res_apply.{t} F Z (homOfLE (le_top :
      (Opens.map (Stacks.subsetInclusion X Z)).obj (V z) ≤ ⊤)) _ c).trans ?_
    exact (preAmbientSectionUnivLE_map_apply.{t} F Z (Opens.leSupr V z) hQV
      (fun y hy ↦ (Opens.leSupr V z).le hy) c).symm.trans
      ((congrArg (preAmbientSectionUnivLE.{t} F Z hQV) (hc z)).trans
        (preAmbientSectionUnivLE_map_apply.{t} F Z (iVM z) hQV (hQW.le.trans (hWM z)) (a z)))

/-- **Sheafification is bijective on the global sections of the presheaf inverse image**, for `Z`
quasi-compact with its distinct points separated by disjoint opens of `X`. This is the single
statement `isIso_subsetSectionsMapUnivLE_iff` reduces the degree-zero isomorphism to. -/
theorem isIso_preSubsetSectionsMapUnivLE_toSheafify (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B) :
    IsIso (preSubsetSectionsMapUnivLE.{t} F Z ≫
      (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
        (presheafRestrictionUnivLE.{t} F Z)).app (op ⊤)) := by
  suffices IsIso ((CategoryTheory.forget AddCommGrpCat.{t}).map
      (preSubsetSectionsMapUnivLE.{t} F Z ≫
        (toSheafify (Opens.grothendieckTopology (TopCat.of Z))
          (presheafRestrictionUnivLE.{t} F Z)).app (op ⊤))) from
    isIso_of_reflects_iso _ (CategoryTheory.forget AddCommGrpCat.{t})
  rw [isIso_iff_bijective]
  exact ⟨injective_preSubsetSectionsMapUnivLE_toSheafify.{t} F Z,
    surjective_preSubsetSectionsMapUnivLE_toSheafify.{t} F Z hZ hSep⟩

/-- **The degree-zero comparison of [Stacks, Tag 09V3] at a coefficient universe independent of
the space is an isomorphism**: for a quasi-compact subset `Z` whose distinct points have disjoint
open neighbourhoods in `X`, the canonical map from the sections of `F` on the open neighbourhoods
of `Z` to the global sections of the restriction of `F` to `Z` is invertible. -/
theorem isIso_subsetSectionsMapUnivLE (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B) :
    IsIso (subsetSectionsMapUnivLE.{t} F Z) :=
  (isIso_subsetSectionsMapUnivLE_iff.{t} F Z).mpr
    (isIso_preSubsetSectionsMapUnivLE_toSheafify.{t} F Z hZ hSep)

end Invertibility

end

section NoWeakening

/-- Pure associativity, isolated as a lemma about an abstract category. The identification below
is this identity applied to a four-fold composite one of whose inner factors is cancelled by the
postcomposed isomorphism; stating it abstractly is what makes it provable, because in the concrete
goal `rw` and `simp` cannot reassociate — the two spellings `TopCat.Sheaf C X` and
`Sheaf (Opens.grothendieckTopology X) C` carry different `Category` instances, so the composite is
not type-correct at `implicit` transparency and every keyed rewrite is refused. Applying a term
instead type-checks at default transparency, where they agree. -/
private theorem comp_cancel_mid {C : Type*} [Category* C] {A B D E G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ G) (e : G ⟶ E) (hde : d ≫ e = 𝟙 E) :
    (a ≫ b ≫ c ≫ d) ≫ e = (a ≫ b) ≫ c := by
  rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, hde, Category.comp_id]

noncomputable section

variable {X : TopCat.{s}} (F : X.Sheaf AddCommGrpCat.{s}) (Z : Set X)

/-- The presheaf inverse image of this file is the library's `inverseImagePresheaf`. -/
theorem presheafRestrictionUnivLE_eq :
    presheafRestrictionUnivLE.{s} F Z = inverseImagePresheaf (Stacks.subsetInclusion X Z) F :=
  rfl

/-- The left-Kan-extension unit of this file is the one the library's `ambientSection` uses. -/
theorem presheafRestrictionUnit_eq :
    presheafRestrictionUnit.{s} F Z = (Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{s}
      (Stacks.subsetInclusion X Z)).unit.app F.presheaf :=
  rfl

/-- The identification of the abstract and constructed inverse images is the library's
`sheafPullbackPresheafIso`. -/
theorem sheafifyRestrictionIso_hom_app (V : Opens (TopCat.of Z)) :
    (sheafifyRestrictionIso.{s} F Z).hom.hom.app (op V)
      = (sheafPullbackPresheafIso (Stacks.subsetInclusion X Z) F).hom.app (op V) :=
  rfl

/-- **Nothing is weakened: at `t := s` the ambient-section map of this file is the library's
`Stacks.Topology.ambientSection`.** The two are built along different routes — this file takes the
unit of the *sheaf-level* adjunction `Functor.sheafAdjunctionContinuous`, which has no universe
constraint, while `ambientSection` takes the presheaf-level unit followed by `toSheafify` and
Mathlib's `sheafPullbackPresheafIso` — so this is not `rfl`. It is the bridge
`ambientSectionUnivLE_comp_sheafifyRestrictionIso` with the iso cancelled. -/
theorem ambientSectionUnivLE_eq_ambientSection {U : Opens X} {V : Opens (TopCat.of Z)}
    (h : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U) :
    ambientSectionUnivLE.{s} F Z h = ambientSection (Stacks.subsetInclusion X Z) F h := by
  have he := isIso_sheafifyRestrictionIso_app.{s} F Z V
  refine (cancel_mono ((sheafifyRestrictionIso.{s} F Z).hom.hom.app (op V))).mp ?_
  refine (ambientSectionUnivLE_comp_sheafifyRestrictionIso.{s} F Z h).trans
    (Eq.trans ?_ (congrArg (ambientSection (Stacks.subsetInclusion X Z) F h ≫ ·)
      (sheafifyRestrictionIso_hom_app.{s} F Z V).symm))
  exact (comp_cancel_mid _ _ _ _ _
    ((sheafPullbackPresheafIso (Stacks.subsetInclusion X Z) F).inv_hom_id_app (op V))).symm

/-- **Nothing is weakened: at `t := s` the degree-zero comparison of this file is the library's
`Stacks.Topology.subsetSectionsMap`.** The two colimits are the same diagram — the index category
and `neighborhoodSections` are coefficient-universe independent already — and the cocone legs
agree by `ambientSectionUnivLE_eq_ambientSection`. -/
theorem subsetSectionsMapUnivLE_eq_subsetSectionsMap :
    subsetSectionsMapUnivLE.{s} F Z = subsetSectionsMap F Z := by
  refine colimit.hom_ext fun U ↦ ?_
  have h2 : colimit.ι (neighborhoodSections F Z) U ≫ subsetSectionsMap F Z =
      ambientSection (Stacks.subsetInclusion X Z) F (top_le_map_openNhdsSet U.unop) :=
    colimit.ι_desc _ _
  exact (subsetSectionsMapUnivLE_ι.{s} F Z U).trans
    ((ambientSectionUnivLE_eq_ambientSection.{s} F Z (top_le_map_openNhdsSet U.unop)).trans
      h2.symm)

/-- **Nothing is weakened: at `t := s` the invertibility proved here is the library's
`Stacks.Topology.isIso_subsetSectionsMap`.** The general theorem is transported along the equality
of the two comparison maps, so what is proved is invertibility of the library's own map and not of
something merely isomorphic to it. -/
theorem isIso_subsetSectionsMap_of_univLE (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B) :
    IsIso (subsetSectionsMap F Z) :=
  subsetSectionsMapUnivLE_eq_subsetSectionsMap.{s} F Z ▸
    isIso_subsetSectionsMapUnivLE.{s} F Z hZ hSep

end

end NoWeakening

end Stacks.Topology

end
