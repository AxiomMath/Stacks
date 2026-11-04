module

public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Sheaf
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction

/-!
# Base change commutes with the fppf quotient sheaf

Changing the base of a slice from `S` to `S'` along `g : S' ⟶ S` restricts presheaves along
`CategoryTheory.Over.map g`. Restriction is already known to be the *right* adjoint of the
lower-shriek extension, so it preserves limits. It is also a *left* adjoint: `Over.map g` has
the right adjoint `Over.pullback g` on a category with fibre products, and precomposition along
the two members of an adjoint pair is again an adjoint pair. So base change of presheaves
preserves colimits too.

The consequence recorded here is that base change commutes with the quotient sheaf `U/R` of
**Stacks 044J**: the restriction of `U/R` to the smaller base, together with the restriction of
the quotient projection, has the universal property of the quotient of the restricted relation,
and is therefore *the* quotient of the restricted relation. This is the step of the proof of
**Stacks 0F9U** which says that the glueing functor of **Stacks 0F9N** applied to a quotient
`T/W` is the triple of the quotients of the components: the three component functors of that
functor are pinned by `BeauvilleLaszlo.Space.GlueingFunctorSpec` to the three base changes along
`U → X`, `U' → X` and `X' → X`, so the statement below applies to each leg of the square.

## Main results

* `CategoryTheory.OverShriek.relocalizeRestrictPullbackAdjunction`: restriction of presheaves
  along `CategoryTheory.Over.map g` is left adjoint to restriction along
  `CategoryTheory.Over.pullback g`.
* `CategoryTheory.OverShriek.preservesColimitsOfSize_relocalizeRestrict` and
  `CategoryTheory.OverShriek.preservesColimits_relocalizeRestrict`: base change of presheaves
  therefore preserves colimits.
* `AlgebraicGeometry.Space.existsUnique_desc_relocalizeRestrict_quotientSheaf`: base change
  commutes with the quotient sheaf — the restricted quotient projection is universal among
  morphisms to a sheaf which identify the two endpoints of every arrow of the restricted
  relation.
* `AlgebraicGeometry.Space.exists_iso_relocalizeRestrict_quotientSheaf`: consequently the
  restriction of `U/R` *is* any sheaf over the smaller base with that same universal property,
  by an isomorphism carrying one projection to the other.
* `AlgebraicGeometry.Space.existsUnique_desc_baseChange_quotientSheaf`: the universal property
  read on the base-change functor of algebraic spaces which the glueing functor of Stacks 0F9N
  is built from.
* `BeauvilleLaszlo.Space.glueingDataIsoOfComponents`: three component isomorphisms compatible
  with the two structure arrows assemble into an isomorphism of cartesian glueing triples, which
  is what turns the three leg-by-leg comparisons into one isomorphism of triples.

## Implementation notes

The quotient sheaf is a coequalizer of presheaves followed by a sheafification, and restriction
is not known here to commute with sheafification. Both steps are avoided: the universal property
is transported across the adjunction instead. A morphism out of the restricted quotient is, by
the adjunction, a morphism out of `U/R` into the restriction along `Over.pullback g` of the
target — which is a sheaf because `Over.pullback g` is a continuous functor of the two slice
sites (Stacks 09W9), so Stacks 044J applies to it — and the invariance hypothesis transports by
naturality of the adjunction in its left variable. No sheaf condition on `R` or on `U` is needed,
and no condition on the pre-relation: nothing here uses that the relation is an equivalence
relation, or flat, or locally of finite presentation. Those hypotheses enter Stacks 0F9U only
through Bootstrap 04S6 (`AlgebraicGeometry.Space.bootstrap04S6QuotientSheaf`), which is what
makes the quotient an algebraic space, not through this comparison.

The conclusions are stated for morphisms of *presheaves*, which is no weaker: a morphism between
the underlying presheaves of two fppf sheaves is a morphism of fppf sheaves.

## References

* [Stacks Project, Tag 044J](https://stacks.math.columbia.edu/tag/044J)
* [Stacks Project, Tag 09W9](https://stacks.math.columbia.edu/tag/09W9)
* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9U](https://stacks.math.columbia.edu/tag/0F9U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.OverShriek

universe w w' v u

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {U V : C} (f : V ⟶ U)

/-- **Restriction of presheaves along `CategoryTheory.Over.map f` is a left adjoint**, its right
adjoint being restriction along `CategoryTheory.Over.pullback f`.

Both functors are precomposition, and precomposition along the two members of an adjoint pair is
again an adjoint pair; the pair here is `CategoryTheory.Over.mapPullbackAdj f`. -/
def relocalizeRestrictPullbackAdjunction :
    relocalizeRestrict f ⊣
      (Functor.whiskeringLeft (Over U)ᵒᵖ (Over V)ᵒᵖ (Type v)).obj (Over.pullback f).op :=
  Functor.whiskeringLeftAdjunctionOfAdjunction (Type v) (Over.mapPullbackAdj f)

/-- Restriction of presheaves along `CategoryTheory.Over.map f` is a left adjoint. -/
instance relocalizeRestrict_isLeftAdjoint : (relocalizeRestrict f).IsLeftAdjoint :=
  ⟨_, ⟨relocalizeRestrictPullbackAdjunction f⟩⟩

/-- **Base change of presheaves preserves colimits**, at every universe. -/
lemma preservesColimitsOfSize_relocalizeRestrict :
    PreservesColimitsOfSize.{w, w'} (relocalizeRestrict f) :=
  (relocalizeRestrictPullbackAdjunction f).leftAdjoint_preservesColimits

/-- **Base change of presheaves preserves colimits.** In particular it takes a coequalizer of
presheaves over `U` to the coequalizer of their base changes over `V`. -/
instance preservesColimits_relocalizeRestrict :
    PreservesColimits (relocalizeRestrict f) :=
  preservesColimitsOfSize_relocalizeRestrict f

end CategoryTheory.OverShriek

namespace AlgebraicGeometry.Space

universe u

variable {site : BigFppfSite.{u}} {S S' : Scheme.{u}}
  {hS : site.Contains S} {hS' : site.Contains S'}
  (g : site.obj hS' ⟶ site.obj hS)

/-- The right adjoint of base change: restriction along `CategoryTheory.Over.pullback g`, which
sends a presheaf `A` over the smaller base to `T ↦ A (T ×_S S')`. -/
abbrev relocalizePullback :
    (BigFppfOver site S' hS')ᵒᵖ ⥤ Type u → ((BigFppfOver site S hS)ᵒᵖ ⥤ Type u) :=
  fun A => ((Functor.whiskeringLeft (BigFppfOver site S hS)ᵒᵖ (BigFppfOver site S' hS')ᵒᵖ
    (Type u)).obj (Over.pullback g).op).obj A

/-- **The right adjoint of base change preserves fppf sheaves**: `Over.pullback g` is a
continuous functor of the two slice sites, because an fppf covering stays an fppf covering after
base change (Stacks 09W9). -/
theorem isSheaf_relocalizePullback {A : (BigFppfOver site S' hS')ᵒᵖ ⥤ Type u}
    (hA : Presheaf.IsSheaf (BigFppfOver.topology site S' hS') A) :
    Presheaf.IsSheaf (BigFppfOver.topology site S hS) (relocalizePullback g A) :=
  (((Over.pullback g).sheafPushforwardContinuous (Type u)
    (BigFppfOver.topology site S hS) (BigFppfOver.topology site S' hS')).obj ⟨A, hA⟩).property

variable {Z : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u} {R U : Over Z}
  [HasSheafify (BigFppfOver.topology site S hS) (Type u)]

/-- **Base change commutes with the quotient sheaf.** The restriction of `U/R` along
`g : S' ⟶ S`, together with the restriction of the quotient projection, has the universal
property of the quotient of the restricted relation: a morphism from the restriction of `U` to a
sheaf over `S'` which identifies the two endpoints of every arrow of the restricted relation
factors uniquely through it.

This is the step of the proof of **Stacks 0F9U** which identifies the glueing triple of
**Stacks 0F9N** attached to a quotient `T/W` with the triple of the quotients of the components:
each of the three component functors is a base change, so each component is the quotient of the
restricted relation. -/
theorem existsUnique_desc_relocalizeRestrict_quotientSheaf (j : PreRelation R U)
    {A : (BigFppfOver site S' hS')ᵒᵖ ⥤ Type u}
    (hA : Presheaf.IsSheaf (BigFppfOver.topology site S' hS') A)
    (k : (OverShriek.relocalizeRestrict g).obj U.left ⟶ A)
    (hk : (OverShriek.relocalizeRestrict g).map j.target.left ≫ k =
      (OverShriek.relocalizeRestrict g).map j.source.left ≫ k) :
    ∃! d : (OverShriek.relocalizeRestrict g).obj (quotientSheaf j).obj ⟶ A,
      (OverShriek.relocalizeRestrict g).map (toQuotientSheaf j) ≫ d = k := by
  have adj := OverShriek.relocalizeRestrictPullbackAdjunction g (C := site.Schemes)
  -- the transpose of `k`: a morphism out of `U` into a sheaf, invariant under `j`
  set m : U.left ⟶ relocalizePullback g A := adj.homEquiv U.left A k with hm
  have hmInv : j.target.left ≫ m = j.source.left ≫ m := by
    rw [hm, ← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left, hk]
  set Asheaf : Sheaf (BigFppfOver.topology site S hS) (Type u) :=
    baseSheaf (isSheaf_relocalizePullback g hA) with hAsheaf
  set D : quotientSheaf j ⟶ Asheaf := quotientSheafDesc j Asheaf m hmInv with hD
  refine ⟨adj.homEquiv (quotientSheaf j).obj A |>.symm D.hom, ?_, ?_⟩
  · refine (adj.homEquiv U.left A).injective ?_
    rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply, hD]
    exact toQuotientSheaf_quotientSheafDesc j Asheaf m hmInv
  · intro d' hd'
    refine (adj.homEquiv (quotientSheaf j).obj A).injective ?_
    rw [Equiv.apply_symm_apply, hD]
    refine congrArg (fun z : quotientSheaf j ⟶ Asheaf => z.hom) ?_
    refine quotientSheafDesc_unique j Asheaf m hmInv ⟨adj.homEquiv _ A d'⟩ ?_
    rw [← adj.homEquiv_naturality_left, hd', hm]

/-- If `p ≫ a = q` and `q ≫ b = p`, and every `y` with `p ≫ y = p` equals a fixed `d`,
then `a ≫ b = 𝟙`. -/
private theorem comp_eq_id_of_unique {C : Type*} [Category C] {X Y Z : C} (p : X ⟶ Y)
    (q : X ⟶ Z) (a : Y ⟶ Z) (b : Z ⟶ Y) (ha : p ≫ a = q) (hb : q ≫ b = p) {d : Y ⟶ Y}
    (huniq : ∀ y : Y ⟶ Y, p ≫ y = p → y = d) : a ≫ b = 𝟙 Y :=
  (huniq _ (by rw [← Category.assoc, ha, hb])).trans (huniq _ (Category.comp_id _)).symm

/-- **The restriction of `U/R` is the quotient of the restricted relation.** Any fppf sheaf `Q`
over the smaller base equipped with a projection out of the restriction of `U` which equalizes
the restricted relation and is universal for that property is isomorphic to the restriction of
`U/R`, by an isomorphism carrying the restricted quotient projection to that projection.

In the proof of **Stacks 0F9U** this is applied to each of the three components `V`, `V'`, `Y'`
of the glueing triple: each is presented as a quotient of the corresponding restriction of `T`
by the corresponding restriction of `W`, and the isomorphism it produces is the component of the
comparison with `G.functor.obj (T/W)`. -/
theorem exists_iso_relocalizeRestrict_quotientSheaf (j : PreRelation R U)
    {Q : (BigFppfOver site S' hS')ᵒᵖ ⥤ Type u}
    (hQ : Presheaf.IsSheaf (BigFppfOver.topology site S' hS') Q)
    (π : (OverShriek.relocalizeRestrict g).obj U.left ⟶ Q)
    (hπ : (OverShriek.relocalizeRestrict g).map j.target.left ≫ π =
      (OverShriek.relocalizeRestrict g).map j.source.left ≫ π)
    (huniv : ∀ {A : (BigFppfOver site S' hS')ᵒᵖ ⥤ Type u},
      Presheaf.IsSheaf (BigFppfOver.topology site S' hS') A →
      ∀ k : (OverShriek.relocalizeRestrict g).obj U.left ⟶ A,
        (OverShriek.relocalizeRestrict g).map j.target.left ≫ k =
          (OverShriek.relocalizeRestrict g).map j.source.left ≫ k →
        ∃! d : Q ⟶ A, π ≫ d = k) :
    ∃ e : (OverShriek.relocalizeRestrict g).obj (quotientSheaf j).obj ≅ Q,
      (OverShriek.relocalizeRestrict g).map (toQuotientSheaf j) ≫ e.hom = π := by
  have hQuot : Presheaf.IsSheaf (BigFppfOver.topology site S' hS')
      ((OverShriek.relocalizeRestrict g).obj (quotientSheaf j).obj) :=
    isSheaf_relocalizeRestrict site S' S hS' hS g _ (quotientSheaf j).property
  have hπQuot : (OverShriek.relocalizeRestrict g).map j.target.left ≫
      (OverShriek.relocalizeRestrict g).map (toQuotientSheaf j) =
      (OverShriek.relocalizeRestrict g).map j.source.left ≫
        (OverShriek.relocalizeRestrict g).map (toQuotientSheaf j) := by
    rw [← Functor.map_comp, ← Functor.map_comp, target_toQuotientSheaf_eq_source]
  obtain ⟨a, ha, -⟩ := existsUnique_desc_relocalizeRestrict_quotientSheaf g j hQ π hπ
  obtain ⟨b, hb, -⟩ := huniv hQuot
    ((OverShriek.relocalizeRestrict g).map (toQuotientSheaf j)) hπQuot
  obtain ⟨_, -, hPuniq⟩ := existsUnique_desc_relocalizeRestrict_quotientSheaf g j hQuot
    ((OverShriek.relocalizeRestrict g).map (toQuotientSheaf j)) hπQuot
  obtain ⟨_, -, hQuniq⟩ := huniv hQ π hπ
  exact ⟨⟨a, b, comp_eq_id_of_unique _ _ _ _ ha hb hPuniq,
    comp_eq_id_of_unique _ _ _ _ hb ha hQuniq⟩, ha⟩

/-- **Base change commutes with the quotient sheaf**, read on the base-change functor of
algebraic spaces which the glueing functor of **Stacks 0F9N** is built from. The three component
functors pinned by `BeauvilleLaszlo.Space.GlueingFunctorSpec` are three instances of
`BeauvilleLaszlo.Space.baseChange`, so this is the universal property of each component of
`G.functor.obj (T/W)`. -/
theorem existsUnique_desc_baseChange_quotientSheaf (j : PreRelation R U)
    (halg : IsAlgebraicSpace site S hS (quotientSheaf j).obj)
    {A : (BigFppfOver site S' hS')ᵒᵖ ⥤ Type u}
    (hA : Presheaf.IsSheaf (BigFppfOver.topology site S' hS') A)
    (k : (OverShriek.relocalizeRestrict g).obj U.left ⟶ A)
    (hk : (OverShriek.relocalizeRestrict g).map j.target.left ≫ k =
      (OverShriek.relocalizeRestrict g).map j.source.left ≫ k) :
    ∃! d : ((BeauvilleLaszlo.Space.baseChange site S' S hS' hS g).obj
        ⟨(quotientSheaf j).obj, halg⟩).obj ⟶ A,
      (OverShriek.relocalizeRestrict g).map (toQuotientSheaf j) ≫ d = k :=
  existsUnique_desc_relocalizeRestrict_quotientSheaf g j hA k hk

end AlgebraicGeometry.Space

open AlgebraicGeometry

namespace BeauvilleLaszlo.Space

universe u

variable (B : BigFppfSite.{u}) (U' U X' : Scheme.{u}) (hU' : B.Contains U')
  (hU : B.Contains U) (hX' : B.Contains X')
  (gU : B.obj hU' ⟶ B.obj hU) (gX' : B.obj hU' ⟶ B.obj hX')

/-- Three component isomorphisms `eU'`, `eU` and `eX'` between two cartesian glueing triples,
compatible with the two structure arrows (the squares `wU` and `wX'`), assemble into an
isomorphism of the triples.

For *uniqueness* of a morphism of triples the component over `U'` is redundant, because the
structure arrow of the target is invertible; it is not redundant here — an isomorphism has to be
exhibited on it, and the two compatibilities `wU` and `wX'` are the squares of the two structure
arrows. -/
def glueingDataIsoOfComponents {D E : GlueingData B U' U X' hU' hU hX' gU gX'}
    (eU' : (overU' B U' U X' hU' hU hX' gU gX').obj D ≅
      (overU' B U' U X' hU' hU hX' gU gX').obj E)
    (eU : (overU B U' U X' hU' hU hX' gU gX').obj D ≅
      (overU B U' U X' hU' hU hX' gU gX').obj E)
    (eX' : (overX' B U' U X' hU' hU hX' gU gX').obj D ≅
      (overX' B U' U X' hU' hU hX' gU gX').obj E)
    (wU : eU'.hom ≫ E.obj.left.hom =
      D.obj.left.hom ≫ (baseChange B U' U hU' hU gU).map eU.hom)
    (wX' : eU'.hom ≫ E.obj.hom =
      D.obj.hom ≫ (baseChange B U' X' hU' hX' gX').map eX'.hom) :
    D ≅ E :=
  ObjectProperty.isoMk _ (Comma.isoMk (Comma.isoMk eU' eU wU) eX' wX')

/-- The component over `U'` of `glueingDataIsoOfComponents` is `eU'`. -/
@[simp]
theorem overU'_map_glueingDataIsoOfComponents_hom
    {D E : GlueingData B U' U X' hU' hU hX' gU gX'}
    (eU' : (overU' B U' U X' hU' hU hX' gU gX').obj D ≅
      (overU' B U' U X' hU' hU hX' gU gX').obj E)
    (eU : (overU B U' U X' hU' hU hX' gU gX').obj D ≅
      (overU B U' U X' hU' hU hX' gU gX').obj E)
    (eX' : (overX' B U' U X' hU' hU hX' gU gX').obj D ≅
      (overX' B U' U X' hU' hU hX' gU gX').obj E)
    (wU : eU'.hom ≫ E.obj.left.hom =
      D.obj.left.hom ≫ (baseChange B U' U hU' hU gU).map eU.hom)
    (wX' : eU'.hom ≫ E.obj.hom =
      D.obj.hom ≫ (baseChange B U' X' hU' hX' gX').map eX'.hom) :
    (overU' B U' U X' hU' hU hX' gU gX').map
        (glueingDataIsoOfComponents B U' U X' hU' hU hX' gU gX' eU' eU eX' wU wX').hom =
      eU'.hom :=
  rfl

/-- The component over `U` of `glueingDataIsoOfComponents` is `eU`. -/
@[simp]
theorem overU_map_glueingDataIsoOfComponents_hom
    {D E : GlueingData B U' U X' hU' hU hX' gU gX'}
    (eU' : (overU' B U' U X' hU' hU hX' gU gX').obj D ≅
      (overU' B U' U X' hU' hU hX' gU gX').obj E)
    (eU : (overU B U' U X' hU' hU hX' gU gX').obj D ≅
      (overU B U' U X' hU' hU hX' gU gX').obj E)
    (eX' : (overX' B U' U X' hU' hU hX' gU gX').obj D ≅
      (overX' B U' U X' hU' hU hX' gU gX').obj E)
    (wU : eU'.hom ≫ E.obj.left.hom =
      D.obj.left.hom ≫ (baseChange B U' U hU' hU gU).map eU.hom)
    (wX' : eU'.hom ≫ E.obj.hom =
      D.obj.hom ≫ (baseChange B U' X' hU' hX' gX').map eX'.hom) :
    (overU B U' U X' hU' hU hX' gU gX').map
        (glueingDataIsoOfComponents B U' U X' hU' hU hX' gU gX' eU' eU eX' wU wX').hom =
      eU.hom :=
  rfl

/-- The component over `X'` of `glueingDataIsoOfComponents` is `eX'`. -/
@[simp]
theorem overX'_map_glueingDataIsoOfComponents_hom
    {D E : GlueingData B U' U X' hU' hU hX' gU gX'}
    (eU' : (overU' B U' U X' hU' hU hX' gU gX').obj D ≅
      (overU' B U' U X' hU' hU hX' gU gX').obj E)
    (eU : (overU B U' U X' hU' hU hX' gU gX').obj D ≅
      (overU B U' U X' hU' hU hX' gU gX').obj E)
    (eX' : (overX' B U' U X' hU' hU hX' gU gX').obj D ≅
      (overX' B U' U X' hU' hU hX' gU gX').obj E)
    (wU : eU'.hom ≫ E.obj.left.hom =
      D.obj.left.hom ≫ (baseChange B U' U hU' hU gU).map eU.hom)
    (wX' : eU'.hom ≫ E.obj.hom =
      D.obj.hom ≫ (baseChange B U' X' hU' hX' gX').map eX'.hom) :
    (overX' B U' U X' hU' hU hX' gU gX').map
        (glueingDataIsoOfComponents B U' U X' hU' hU hX' gU gX' eU' eU eX' wU wX').hom =
      eX'.hom :=
  rfl

end BeauvilleLaszlo.Space

end
