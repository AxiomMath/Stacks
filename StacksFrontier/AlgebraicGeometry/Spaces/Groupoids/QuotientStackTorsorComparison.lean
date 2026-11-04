module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ActionGroupoidPointwisePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorStackUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TrivialTorsorRightTranslation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PseudoTorsors
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackEquivalence
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ReverseEffective
public import StacksFrontier.CategoryTheory.Sites.Stackification.ComparisonEquivalence

/-!
# The pointwise comparison of the quotient stack with the stack of torsors

Let `G` be a group algebraic space over an algebraic space `B` over a scheme `S` of a big fppf
site, acting on an algebraic space `X` over `B`.  The quotient stack `[X/G]` is the
stackification of the pointwise groupoid fibration of the action groupoid, and `[[X/G]]` is the
category of fppf `G`-torsors with a `G`-equivariant map to `X`.  This file builds the comparison
`F_p` out of the pointwise fibration and proves the three properties of Stacks 02ZN that make
the stack of torsors a stackification of it.

## Main definitions

* `AlgebraicGeometry.Space.actionPointwiseComparison`: the comparison functor `F_p`, sending an
  `X`-valued point to its trivial torsor with equivariant map and a pointwise arrow `(f, g)` to
  the right translation by `g⁻¹`.

## Main results

* `AlgebraicGeometry.Space.actionPointwiseComparison_comp_projection`: `F_p` lies strictly over
  the big fppf site.
* `AlgebraicGeometry.Space.trivialTorsorRightProduct_injective`,
  `AlgebraicGeometry.Space.unit_comp_trivialTorsorRightTranslation` and
  `AlgebraicGeometry.Space.trivialTorsorWithMapHom_ext`: the section `g` is determined by the
  right translation it induces, the unit section of `G_U` followed by right translation and the
  projection to `G` is `g⁻¹`, and a morphism of `[[X/G]]` out of a trivial torsor is determined
  by its base morphism and its value on the unit section.
* `AlgebraicGeometry.Space.exists_actionPointwiseMorphism`: a `G`-point carrying one `X`-valued
  point to another is the group element of a pointwise arrow.
* `AlgebraicGeometry.Space.actionPointwiseComparison_faithful` and
  `AlgebraicGeometry.Space.actionPointwiseComparison_full`: `F_p` is fully faithful.
* `AlgebraicGeometry.Space.actionPointwiseComparison_morPresheafMap_isIso` and
  `AlgebraicGeometry.Space.actionPointwiseComparison_locallyBijective`: clause (1) of
  Stacks 02ZN for `F_p`, which is immediate from full faithfulness.
* `AlgebraicGeometry.Space.torsorObj_isLocallySurjective` and
  `AlgebraicGeometry.Space.torsorWithMap_mem_essImage_of_isTrivial`: the structure morphism of
  an fppf torsor is locally surjective, and an object of `[[X/G]]` whose torsor is trivial is in
  the essential image of `F_p`.
* `AlgebraicGeometry.Space.actionPointwiseComparison_exists_covering_essImage` and
  `AlgebraicGeometry.Space.actionPointwiseComparison_locallyEssImage`: clause (2) of
  Stacks 02ZN for `F_p`: every object of `[[X/G]]` is, locally on its base, in the essential
  image of `F_p`.

## Implementation notes

The library's `[[X/G]]` is a concrete category, so the comparison is defined directly: no
transport along an abstract identification of the morphism types intervenes, and the two fields
of the functor are `AlgebraicGeometry.Space.trivialTorsorWithMap` and
`AlgebraicGeometry.Space.trivialTorsorWithMapHom`, whose hypotheses are literally
`AlgebraicGeometry.Space.actionPointwise_group_compat` and
`AlgebraicGeometry.Space.actionPointwise_action`.  Functoriality is
`AlgebraicGeometry.Space.trivialTorsorRightTranslation_id` and
`AlgebraicGeometry.Space.trivialTorsorRightTranslation_comp` read through
`AlgebraicGeometry.Space.actionPointwiseGroupElement_id` and
`AlgebraicGeometry.Space.actionPointwiseGroupElement_comp`, morphisms of `[[X/G]]` being
extensional in the underlying morphism of torsors.

Faithfulness and fullness both rest on the unit section of the trivial torsor: a morphism out of
a trivial torsor is determined by its value there
(`AlgebraicGeometry.Space.trivialTorsorWithMapHom_ext`), and the value of the equivariant map
there is the point the torsor came from
(`AlgebraicGeometry.Space.trivialTorsorMap_unit`).  Faithfulness then reduces to injectivity of
`AlgebraicGeometry.Space.trivialTorsorRightProduct` in the section, which is cancellation in the
group of morphisms into `G` over `B`; fullness reconstructs the section from the value of a given
morphism on the unit section and produces the pointwise arrow with
`AlgebraicGeometry.Space.exists_actionPointwiseMorphism`.

The local essential image uses that the structure morphism of an fppf torsor is locally
surjective —
`AlgebraicGeometry.Space.isLocallySurjective_of_fppfCovering_sections`, applied to the covering
family in the definition of an fppf torsor — so that on the image sieve of a point of the base
the restricted torsor has a section, hence is trivial, hence in the essential image.  That a
morphism of `[[X/G]]` lying over an identity is an isomorphism is read off the stack property of
`AlgebraicGeometry.Space.TorsorWithMap.projection`, which is a theorem and not a hypothesis.

Both clauses of Stacks 02ZN are stated for `F_p` composed with a fully faithful functor `L`
raising the universe of the morphisms, and not for `F_p` itself.  That is forced: the morphism
presheaves of Stacks 042V are formed for two categories over the site with a common hom universe,
and the pointwise action groupoid has morphisms one universe below those of `[[X/G]]`, so the
statement does not even typecheck for `F_p` alone.  `L` is the universe lift the stackification
of Stacks 02ZN is formed along, so nothing is lost; the mathematical content of clause (2) is in
`AlgebraicGeometry.Space.actionPointwiseComparison_exists_covering_essImage`, which is
universe-agnostic.

Several proofs here meet the two spellings of the total space of a trivial torsor — the slice
object `(pullbackGroup hB G U b).obj.X` carrying the group structure and the bare fibre product
`CategoryTheory.Limits.pullback G.obj.X.hom b` — which agree definitionally but not at the
transparency at which `rw` and `simp only` match.  As in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/GroupSpaces/TrivialTorsorRightTranslation.lean`,
every morphism whose declared type mixes the two is generalised to a variable carrying the
equations that characterise it, the rewriting is done there, and the public statement is
discharged from that form by definitional unfolding; the `raw` private lemmas below are those
generalisations.

Two pieces of bookkeeping are rebuilt here because they are `private` where they are used.
`AlgebraicGeometry.Space.actionPointwiseArrow` and its endpoint equations transport a point of
`G ×_B X` along the equalities identifying the object and arrow spaces of the chosen action
groupoid, and producing a pointwise arrow from a point needs those transports in the opposite
direction; `app_cast_of_heq` below is the lemma that applying a morphism of presheaves commutes
with such a transport, which is also `private` in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/ActionGroupoidPointwisePoints.lean`.  Likewise
`regularAction_hom_eq`, that a morphism of modules out of the left regular action is determined
by its value on the unit, is stated here for the first time in the tree.

## References

* [Stacks Project, Tag 04WM](https://stacks.math.columbia.edu/tag/04WM)
* [Stacks Project, Situation 04WL](https://stacks.math.columbia.edu/tag/04WL)
* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 0370](https://stacks.math.columbia.edu/tag/0370)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space

-- Reading the base and the fibre of an object of the Grothendieck construction of a presheaf of
-- groupoids means seeing through the pseudofunctor it is presented by; the chain is definitional,
-- and these are the definitions along it.
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.Functor.toPseudofunctor' CategoryTheory.pseudofunctorOfIsLocallyDiscrete
  Quiver.Hom.toLoc CategoryTheory.Grpd.forgetToCat CategoryTheory.Grpd.of
-- The underlying object of a monoid object regarded as a module over itself is the monoid object
-- again, by one unfolding and one projection of a constructor.  A trivialisation of a
-- pseudo-torsor is an isomorphism out of that module, so every component of one is read along
-- this chain.
attribute [local implicit_reducible] CategoryTheory.Mod.regular

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (hB : IsAlgebraicSpace 𝒞 S hS B)
  (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B) [ModObj G.obj.X X]
  (hX : IsAlgebraicSpace 𝒞 S hS X.left)

/-! ### The comparison functor -/

/-- **Stacks 04WM**, the comparison functor `F_p` out of the pointwise action groupoid: an
`X`-valued point goes to the trivial torsor with its equivariant map `h ↦ h · x`, and a pointwise
arrow `(f, g)` to the right translation `(h, u) ↦ (h · g(u)⁻¹, f(u))`. -/
def actionPointwiseComparison :
    (actionPointwiseCategory hB G X hX).obj ⥤ TorsorWithMap hB G X where
  obj A := trivialTorsorWithMap hB G X A.base (actionPointwiseValue hB G X hX A)
  map {A A'} f :=
    trivialTorsorWithMapHom hB G X (actionPointwiseValue hB G X hX A)
      (actionPointwiseValue hB G X hX A') f.base
      (actionPointwiseGroupElement hB G X hX f)
      (actionPointwise_group_compat hB G X hX f)
      (actionPointwise_action hB G X hX f)
  map_id A := by
    refine TorsorWithMap.Hom.ext X (TorsorObj.Hom.ext rfl ?_)
    exact trivialTorsorRightTranslation_id hB G _ _ _
      ((actionPointwiseGroupElement_id hB G X hX A).trans (Category.assoc _ _ _).symm)
  map_comp {A A' A''} f g := by
    refine TorsorWithMap.Hom.ext X (TorsorObj.Hom.ext rfl ?_)
    exact trivialTorsorRightTranslation_comp hB G _ _ _ f.base g.base
      (actionPointwise_base_compat hB G X hX f) (actionPointwise_base_compat hB G X hX g)
      _ _ _ _ _ _ (actionPointwiseGroupElement_comp hB G X hX f g)

/-- The comparison functor lies strictly over the big fppf site: the base of the trivial torsor
attached to a point is the object the point is defined on. -/
theorem actionPointwiseComparison_comp_projection :
    actionPointwiseComparison hB G X hX ⋙ TorsorWithMap.projection hB G X =
      (actionPointwiseCategory hB G X hX).p :=
  rfl

/-! ### Morphisms out of a trivial torsor are determined by the unit section -/

section Unit

variable {U U' : BigFppfOver 𝒞 S hS}

/-- The pairing `(𝟙, 1)` of the identity of `G_U` with the unit section, read as a morphism of
bare fibre products. -/
private def rawUnitDiag (b : yoneda.obj U ⟶ B) :
    pullback G.obj.X.hom b ⟶
      pullback (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) :=
  (CartesianMonoidalCategory.lift (𝟙 (pullbackGroup hB G U b).obj.X)
    (1 : (pullbackGroup hB G U b).obj.X ⟶ (pullbackGroup hB G U b).obj.X)).left

private theorem rawUnitDiag_comp_snd (b : yoneda.obj U ⟶ B) :
    rawUnitDiag hB G b ≫
        pullback.snd (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) =
      pullback.snd G.obj.X.hom b ≫ (η[(pullbackGroup hB G U b).obj.X]).left :=
  congrArg Over.Hom.left
    (CartesianMonoidalCategory.lift_snd (𝟙 (pullbackGroup hB G U b).obj.X)
      (1 : (pullbackGroup hB G U b).obj.X ⟶ (pullbackGroup hB G U b).obj.X))

private theorem rawUnitDiag_comp_mul (b : yoneda.obj U ⟶ B) :
    rawUnitDiag hB G b ≫ (μ[(pullbackGroup hB G U b).obj.X]).left =
      𝟙 (pullback G.obj.X.hom b) :=
  congrArg Over.Hom.left (mul_one (𝟙 (pullbackGroup hB G U b).obj.X))

/-- The unit section of `G_U`, followed by the morphism `h ↦ h · g⁻¹`, is the inverse of the
section `g`. -/
private theorem unit_comp_trivialTorsorRightProduct (b : yoneda.obj U ⟶ B)
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b) :
    (η[(pullbackGroup hB G U b).obj.X]).left ≫ trivialTorsorRightProduct hB G b g hg =
      g ≫ (ι[G.obj.X]).left := by
  let P := (pullbackGroup hB G U b).obj.X
  let UB : Over B := Over.mk b
  let PB : Over B := Over.mk (pullback.snd G.obj.X.hom b ≫ b)
  let p : PB ⟶ UB := Over.homMk (pullback.snd G.obj.X.hom b) rfl
  let g₀ : UB ⟶ G.obj.X := Over.homMk g hg
  let π : PB ⟶ G.obj.X := Over.homMk (pullback.fst G.obj.X.hom b) pullback.condition
  have hew : (η[P]).left ≫ pullback.snd G.obj.X.hom b = 𝟙 (yoneda.obj U) := (η[P]).w
  let e : UB ⟶ PB := Over.homMk (η[P]).left
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ b) hew).trans (Category.id_comp b)))
  have hep : e ≫ p = 𝟙 UB := Over.OverMorphism.ext hew
  have heπ : e ≫ π = 1 :=
    Over.OverMorphism.ext (pullbackGroup_unit_left_comp_fst hB G U b)
  change (e ≫ (π * (p ≫ g₀)⁻¹)).left = g₀⁻¹.left
  rw [MonObj.comp_mul, GrpObj.comp_inv, heπ, ← Category.assoc, hep, Category.id_comp, one_mul]

/-- The morphism `h ↦ h · g⁻¹` of `G_U` determines the section `g`: two sections of `G` over `b`
inducing the same right translation agree. -/
theorem trivialTorsorRightProduct_injective (b : yoneda.obj U ⟶ B)
    (g h : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b)
    (hh : h ≫ G.obj.X.hom = b)
    (heq : trivialTorsorRightProduct hB G b g hg = trivialTorsorRightProduct hB G b h hh) :
    g = h := by
  let g₀ : Over.mk b ⟶ G.obj.X := Over.homMk g hg
  let h₀ : Over.mk b ⟶ G.obj.X := Over.homMk h hh
  have hinv : g₀⁻¹ = h₀⁻¹ := Over.OverMorphism.ext <|
    (unit_comp_trivialTorsorRightProduct hB G b g hg).symm.trans
      ((congrArg _ heq).trans (unit_comp_trivialTorsorRightProduct hB G b h hh))
  exact congrArg Over.Hom.left (inv_inj.mp hinv)

/-- The unit section of `G_U`, followed by right translation and the projection to `G`, is the
inverse of the section `g`. -/
theorem unit_comp_trivialTorsorRightTranslation (b : yoneda.obj U ⟶ B)
    (b' : yoneda.obj U' ⟶ B) (f : U ⟶ U') (hb : b = yoneda.map f ≫ b')
    (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = b) :
    (η[(pullbackGroup hB G U b).obj.X]).left ≫
        trivialTorsorRightTranslation hB G b b' f hb g hg ≫
          pullback.fst G.obj.X.hom b' = g ≫ (ι[G.obj.X]).left :=
  (congrArg ((η[(pullbackGroup hB G U b).obj.X]).left ≫ ·) (pullback.lift_fst _ _ _)).trans
    (unit_comp_trivialTorsorRightProduct hB G b g hg)

/-- `AlgebraicGeometry.Space.trivialTorsorWithMapHom_ext` with every morphism whose declared
type mixes the two spellings of the total space of a trivial torsor replaced by a variable
carrying the equations that characterise it: the multiplication `M`, the pairing `Δ` with the
unit, the unit section `E`, the base change `K` of the acting group, and the two base changes
`Dg`, `Dg'` of the actions.  All the rewriting happens here, where the spellings do not mix. -/
private theorem rawTrivialTorsorHom_ext (b : yoneda.obj U ⟶ B) (b' : yoneda.obj U' ⟶ B)
    (t t' K : pullback G.obj.X.hom b ⟶ pullback G.obj.X.hom b')
    (Dg Dg' : pullback (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ⟶
      pullback (pullback.snd G.obj.X.hom b') (pullback.snd G.obj.X.hom b'))
    (M : pullback (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ⟶
      pullback G.obj.X.hom b)
    (M' : pullback (pullback.snd G.obj.X.hom b') (pullback.snd G.obj.X.hom b') ⟶
      pullback G.obj.X.hom b')
    (Δ : pullback G.obj.X.hom b ⟶
      pullback (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b))
    (E : yoneda.obj U ⟶ pullback G.obj.X.hom b)
    (hΔM : Δ ≫ M = 𝟙 (pullback G.obj.X.hom b))
    (hΔsnd : Δ ≫ pullback.snd (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) =
      pullback.snd G.obj.X.hom b ≫ E)
    (hDfst : Dg ≫ pullback.fst (pullback.snd G.obj.X.hom b') (pullback.snd G.obj.X.hom b') =
      pullback.fst (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ≫ K)
    (hDsnd : Dg ≫ pullback.snd (pullback.snd G.obj.X.hom b') (pullback.snd G.obj.X.hom b') =
      pullback.snd (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ≫ t)
    (hD'fst : Dg' ≫ pullback.fst (pullback.snd G.obj.X.hom b') (pullback.snd G.obj.X.hom b') =
      pullback.fst (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ≫ K)
    (hD'snd : Dg' ≫ pullback.snd (pullback.snd G.obj.X.hom b') (pullback.snd G.obj.X.hom b') =
      pullback.snd (pullback.snd G.obj.X.hom b) (pullback.snd G.obj.X.hom b) ≫ t')
    (hmul : M ≫ t = Dg ≫ M') (hmul' : M ≫ t' = Dg' ≫ M')
    (he : E ≫ t = E ≫ t') : t = t' := by
  have hD : Δ ≫ Dg = Δ ≫ Dg' := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hDfst, hD'fst]
    · rw [Category.assoc, Category.assoc, hDsnd, hD'snd, ← Category.assoc, ← Category.assoc,
        hΔsnd, Category.assoc, Category.assoc, he]
  calc t = Δ ≫ M ≫ t := by rw [← Category.assoc, hΔM, Category.id_comp]
    _ = Δ ≫ M ≫ t' := by rw [hmul, ← Category.assoc, hD, Category.assoc, hmul']
    _ = t' := by rw [← Category.assoc, hΔM, Category.id_comp]

/-- A morphism of `[[X/G]]` out of a trivial torsor is determined by its base morphism together
with the value of its morphism of total spaces on the unit section: equivariance recovers the
whole morphism from that value. -/
theorem trivialTorsorWithMapHom_ext {x : yoneda.obj U ⟶ X.left} {x' : yoneda.obj U' ⟶ X.left}
    (m n : trivialTorsorWithMap hB G X U x ⟶ trivialTorsorWithMap hB G X U' x')
    (hb : m.toHom.f = n.toHom.f)
    (he : (η[(pullbackGroup hB G U (x ≫ X.hom)).obj.X]).left ≫ m.toHom.g =
      (η[(pullbackGroup hB G U (x ≫ X.hom)).obj.X]).left ≫ n.toHom.g) :
    m = n := by
  refine TorsorWithMap.Hom.ext X (TorsorObj.Hom.ext hb ?_)
  have hgbc : groupBaseChange n.toHom.f n.toHom.comp_b =
      groupBaseChange m.toHom.f m.toHom.comp_b := by
    refine pullback.hom_ext ?_ ?_
    · rw [groupBaseChange_fst, groupBaseChange_fst]
    · rw [groupBaseChange_snd, groupBaseChange_snd, hb]
  have hD'fst : actionBaseChange n.toHom.f n.toHom.comp_b n.toHom.g
          n.toHom.isPullback.w.symm ≫
        pullback.fst (pullback.snd G.obj.X.hom (trivialTorsorWithMap hB G X U' x').b)
          (trivialTorsorWithMap hB G X U' x').total.hom =
      pullback.fst (pullback.snd G.obj.X.hom (trivialTorsorWithMap hB G X U x).b)
          (trivialTorsorWithMap hB G X U x).total.hom ≫
        groupBaseChange m.toHom.f m.toHom.comp_b := by
    rw [actionBaseChange_fst, hgbc]
  exact rawTrivialTorsorHom_ext hB G (x ≫ X.hom) (x' ≫ X.hom) m.toHom.g n.toHom.g
    (groupBaseChange m.toHom.f m.toHom.comp_b)
    (actionBaseChange m.toHom.f m.toHom.comp_b m.toHom.g m.toHom.isPullback.w.symm)
    (actionBaseChange n.toHom.f n.toHom.comp_b n.toHom.g n.toHom.isPullback.w.symm)
    (μ[(pullbackGroup hB G U (x ≫ X.hom)).obj.X]).left
    (μ[(pullbackGroup hB G U' (x' ≫ X.hom)).obj.X]).left
    (rawUnitDiag hB G (x ≫ X.hom))
    (η[(pullbackGroup hB G U (x ≫ X.hom)).obj.X]).left
    (rawUnitDiag_comp_mul hB G (x ≫ X.hom)) (rawUnitDiag_comp_snd hB G (x ≫ X.hom))
    (actionBaseChange_fst m.toHom.f m.toHom.comp_b m.toHom.g m.toHom.isPullback.w.symm)
    (actionBaseChange_snd m.toHom.f m.toHom.comp_b m.toHom.g m.toHom.isPullback.w.symm)
    hD'fst
    (actionBaseChange_snd n.toHom.f n.toHom.comp_b n.toHom.g n.toHom.isPullback.w.symm)
    m.toHom.smul_comp n.toHom.smul_comp he

end Unit

/-! ### Producing a pointwise arrow from a group element -/

section CastHelper

universe u₁ v₁

/-- Applying a morphism of presheaves commutes with transporting its argument along an equality
of the presheaves involved.  This is the transport lemma of the pointwise layer, needed here in
the opposite direction: there a pointwise arrow is read as a point of `G ×_B X`, here a point of
`G ×_B X` is turned into a pointwise arrow. -/
private theorem app_cast_of_heq {D : Type u₁} [Category.{v₁} D]
    {F F' H H' : D ⥤ Type u} (hF : F = F') (hH : H = H')
    {φ : F ⟶ H} {φ' : F' ⟶ H'} (hφ : HEq φ φ') (T : D) (a : F.obj T) :
    φ'.app T (cast (congrArg (fun K : D ⥤ Type u => K.obj T) hF) a) =
      cast (congrArg (fun K : D ⥤ Type u => K.obj T) hH) (φ.app T a) := by
  subst F'
  subst H'
  cases eq_of_heq hφ
  rfl

end CastHelper

/-- Every `G`-point over the point of an object of the pointwise action groupoid which carries
that point to the restriction of the point of another object comes from a pointwise arrow: the
pair `(f, g)` is a point of `G ×_B X` with the prescribed endpoints, hence an arrow of the
action groupoid. -/
theorem exists_actionPointwiseMorphism
    {A A' : (actionPointwiseCategory hB G X hX).obj}
    (f : A.base ⟶ A'.base) (g : yoneda.obj A.base ⟶ G.obj.X.left)
    (hg : g ≫ G.obj.X.hom = actionPointwiseValue hB G X hX A ≫ X.hom)
    (ha : pullback.lift g (actionPointwiseValue hB G X hX A) hg ≫ (γ[G.obj.X,X]).left =
      yoneda.map f ≫ actionPointwiseValue hB G X hX A') :
    ∃ k : A ⟶ A', k.base = f ∧ actionPointwiseGroupElement hB G X hX k = g := by
  let D := groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX
  let E := D.groupoid.toGroupoidInFunctors
  let r : (G.obj.X ⊗ X).left.obj (op A.base) :=
    yonedaEquiv (pullback.lift g (actionPointwiseValue hB G X hX A) hg)
  let r' := cast (congrArg (fun Y : AlgebraicSpaces 𝒞 S hS => Y.obj.obj (op A.base))
    D.arrows_eq).symm r
  have hr' : cast (congrArg (fun Y : AlgebraicSpaces 𝒞 S hS => Y.obj.obj (op A.base))
      D.arrows_eq) r' = r := (cast_cast _ _ _).trans (cast_eq _ _)
  have hvA : yonedaEquiv (actionPointwiseValue hB G X hX A) =
      cast (congrArg (fun Y : AlgebraicSpaces 𝒞 S hS => Y.obj.obj (op A.base))
        D.objects_eq) A.fiber := Equiv.apply_symm_apply _ _
  have hvA' : yonedaEquiv (actionPointwiseValue hB G X hX A') =
      cast (congrArg (fun Y : AlgebraicSpaces 𝒞 S hS => Y.obj.obj (op A'.base))
        D.objects_eq) A'.fiber := Equiv.apply_symm_apply _ _
  have hs : E.source.app (op A.base) r' = A.fiber := by
    refine (Equiv.cast (congrArg (fun Y : AlgebraicSpaces 𝒞 S hS => Y.obj.obj (op A.base))
      D.objects_eq)).injective ?_
    have key : (pullback.snd G.obj.X.hom X.hom).app (op A.base)
        (yonedaEquiv (pullback.lift g (actionPointwiseValue hB G X hX A) hg)) =
          yonedaEquiv (actionPointwiseValue hB G X hX A) := by
      rw [← yonedaEquiv_comp, pullback.lift_snd]
    exact (app_cast_of_heq (congrArg (fun Y => Y.obj) D.arrows_eq)
      (congrArg (fun Y => Y.obj) D.objects_eq) D.source_eq (op A.base) r').symm.trans
      ((congrArg ((pullback.snd G.obj.X.hom X.hom).app (op A.base)) hr').trans
        (key.trans hvA))
  have ht : E.target.app (op A.base) r' = E.objects.map f.op A'.fiber := by
    refine (Equiv.cast (congrArg (fun Y : AlgebraicSpaces 𝒞 S hS => Y.obj.obj (op A.base))
      D.objects_eq)).injective ?_
    have key : (γ[G.obj.X, X]).left.app (op A.base)
        (yonedaEquiv (pullback.lift g (actionPointwiseValue hB G X hX A) hg)) =
          X.left.map f.op (yonedaEquiv (actionPointwiseValue hB G X hX A')) := by
      rw [← yonedaEquiv_comp, ha, ← yonedaEquiv_naturality]
    refine (app_cast_of_heq (congrArg (fun Y => Y.obj) D.arrows_eq)
      (congrArg (fun Y => Y.obj) D.objects_eq) D.target_eq (op A.base) r').symm.trans
      ((congrArg ((γ[G.obj.X, X]).left.app (op A.base)) hr').trans ?_)
    refine key.trans ?_
    rw [hvA']
    exact (Deformation.cast_functor_map (congrArg (fun Y => Y.obj) D.objects_eq)
      f.op A'.fiber).symm
  let k : A ⟶ A' :=
    { base := f
      fiber := (E.evaluationArrowEquiv (op A.base) A.fiber
        ((E.objects.map (op f)) A'.fiber)).symm ⟨r', hs, ht⟩ }
  have hk : actionPointwiseArrow hB G X hX k = r :=
    Eq.trans (congrArg (cast (congrArg
      (fun Y : AlgebraicSpaces 𝒞 S hS => Y.obj.obj (op A.base)) D.arrows_eq))
      (congrArg Subtype.val (Equiv.apply_symm_apply
        (E.evaluationArrowEquiv (op A.base) A.fiber ((E.objects.map (op f)) A'.fiber))
        ⟨r', hs, ht⟩))) hr'
  have hge : ∀ {A₁ A₂ : (actionPointwiseCategory hB G X hX).obj} (k : A₁ ⟶ A₂),
      yonedaEquiv (actionPointwiseGroupElement hB G X hX k) =
        (pullback.fst G.obj.X.hom X.hom).app (op A₁.base)
          (actionPointwiseArrow hB G X hX k) :=
    fun _ => Equiv.apply_symm_apply _ _
  have hfin : (pullback.fst G.obj.X.hom X.hom).app (op A.base)
      (yonedaEquiv (pullback.lift g (actionPointwiseValue hB G X hX A) hg)) =
      yonedaEquiv g := by
    rw [← yonedaEquiv_comp, pullback.lift_fst]
  exact ⟨k, rfl, yonedaEquiv.injective ((hge _).trans
      ((congrArg (fun z => (pullback.fst G.obj.X.hom X.hom).app (op A.base) z) hk).trans
        hfin))⟩

/-! ### Full faithfulness -/

/-- **Stacks 04WM.** The comparison functor is faithful: a pointwise arrow is determined by its
base morphism and its group element, and the group element is determined by the right
translation it induces. -/
theorem actionPointwiseComparison_faithful :
    (actionPointwiseComparison hB G X hX).Faithful where
  map_injective {A A'} f g hfg := by
    have hfst : ∀ {A₁ A₂ : (actionPointwiseCategory hB G X hX).obj} (k : A₁ ⟶ A₂),
        ((actionPointwiseComparison hB G X hX).map k).toHom.g ≫
            pullback.fst G.obj.X.hom (actionPointwiseValue hB G X hX A₂ ≫ X.hom) =
          trivialTorsorRightProduct hB G (actionPointwiseValue hB G X hX A₁ ≫ X.hom)
            (actionPointwiseGroupElement hB G X hX k)
            (actionPointwise_group_compat hB G X hX k) :=
      fun _ => pullback.lift_fst _ _ _
    refine actionPointwiseMorphism_ext hB G X hX f g (congrArg (fun m => m.toHom.f) hfg) ?_
    refine trivialTorsorRightProduct_injective hB G
      (actionPointwiseValue hB G X hX A ≫ X.hom)
      (actionPointwiseGroupElement hB G X hX f) (actionPointwiseGroupElement hB G X hX g)
      (actionPointwise_group_compat hB G X hX f) (actionPointwise_group_compat hB G X hX g) ?_
    exact (hfst f).symm.trans
      ((congrArg (· ≫ pullback.fst G.obj.X.hom
        (actionPointwiseValue hB G X hX A' ≫ X.hom))
        (congrArg (fun m => m.toHom.g) hfg)).trans (hfst g))

section Full

variable {U U' : BigFppfOver 𝒞 S hS}

/-- The group-theoretic content of fullness, in the bare fibre-product spelling: a point `z` of
the trivial torsor attached to `x'` lying over `f` and carrying the equivariant map to `x`
exhibits `x` as `a · (f ∘ x')` for the `G`-point `a` underlying `z`, so that `a⁻¹` carries `x` to
the restriction of `x'`. -/
private theorem rawUnitAction (x : yoneda.obj U ⟶ X.left) (x' : yoneda.obj U' ⟶ X.left)
    (f : U ⟶ U') (z : yoneda.obj U ⟶ pullback G.obj.X.hom (x' ≫ X.hom))
    (hzs : z ≫ pullback.snd G.obj.X.hom (x' ≫ X.hom) = yoneda.map f)
    (ha : (z ≫ pullback.fst G.obj.X.hom (x' ≫ X.hom)) ≫ G.obj.X.hom = x ≫ X.hom)
    (hzm : z ≫ trivialTorsorMap hB G X U' x' = x)
    (hg : ((z ≫ pullback.fst G.obj.X.hom (x' ≫ X.hom)) ≫ (ι[G.obj.X]).left) ≫ G.obj.X.hom =
      x ≫ X.hom) :
    pullback.lift ((z ≫ pullback.fst G.obj.X.hom (x' ≫ X.hom)) ≫ (ι[G.obj.X]).left) x hg ≫
        (γ[G.obj.X, X]).left = yoneda.map f ≫ x' := by
  let UB : Over B := Over.mk (x ≫ X.hom)
  let a₀ : UB ⟶ G.obj.X := Over.homMk (z ≫ pullback.fst G.obj.X.hom (x' ≫ X.hom)) ha
  let x₀ : UB ⟶ X := Over.homMk x rfl
  have hx₁w : (yoneda.map f ≫ x') ≫ X.hom = x ≫ X.hom := by
    rwa [Category.assoc, ← hzs, Category.assoc, ← pullback.condition, ← Category.assoc]
  let x₁ : UB ⟶ X := Over.homMk (yoneda.map f ≫ x') hx₁w
  have hc' : pullback.fst G.obj.X.hom (x' ≫ X.hom) ≫ G.obj.X.hom =
      (pullback.snd G.obj.X.hom (x' ≫ X.hom) ≫ x') ≫ X.hom := by
    simpa only [Category.assoc] using
      pullback.condition (f := G.obj.X.hom) (g := x' ≫ X.hom)
  have hmap' : trivialTorsorMap hB G X U' x' =
      pullback.lift (pullback.fst G.obj.X.hom (x' ≫ X.hom))
        (pullback.snd G.obj.X.hom (x' ≫ X.hom) ≫ x') hc' ≫ (γ[G.obj.X, X]).left := rfl
  have hAfst : (CartesianMonoidalCategory.lift a₀ x₁).left ≫
      pullback.fst G.obj.X.hom X.hom = z ≫ pullback.fst G.obj.X.hom (x' ≫ X.hom) :=
    congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst a₀ x₁)
  have hAsnd : (CartesianMonoidalCategory.lift a₀ x₁).left ≫
      pullback.snd G.obj.X.hom X.hom = yoneda.map f ≫ x' :=
    congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd a₀ x₁)
  have hlift : z ≫ pullback.lift (pullback.fst G.obj.X.hom (x' ≫ X.hom))
        (pullback.snd G.obj.X.hom (x' ≫ X.hom) ≫ x') hc' =
      (CartesianMonoidalCategory.lift a₀ x₁).left := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, hAfst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hzs, hAsnd]
  have hx : a₀ • x₁ = x₀ := by
    refine Over.OverMorphism.ext ?_
    show (CartesianMonoidalCategory.lift a₀ x₁).left ≫ (γ[G.obj.X, X]).left = x
    rwa [← hlift, Category.assoc, ← hmap']
  have hBfst : (CartesianMonoidalCategory.lift a₀⁻¹ x₀).left ≫
      pullback.fst G.obj.X.hom X.hom =
      (z ≫ pullback.fst G.obj.X.hom (x' ≫ X.hom)) ≫ (ι[G.obj.X]).left :=
    congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst a₀⁻¹ x₀)
  have hBsnd : (CartesianMonoidalCategory.lift a₀⁻¹ x₀).left ≫
      pullback.snd G.obj.X.hom X.hom = x :=
    congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd a₀⁻¹ x₀)
  have hliftg : pullback.lift ((z ≫ pullback.fst G.obj.X.hom (x' ≫ X.hom)) ≫
        (ι[G.obj.X]).left) x hg = (CartesianMonoidalCategory.lift a₀⁻¹ x₀).left := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, hBfst]
    · rw [pullback.lift_snd, hBsnd]
  rw [hliftg]
  show (a₀⁻¹ • x₀ : UB ⟶ X).left = x₁.left
  rw [← hx, inv_smul_smul]

/-- The data fullness produces, in the bare fibre-product spelling: from the value `E ≫ t` on the
unit section of a morphism `t` of trivial torsors over `f` compatible with the equivariant maps,
the `G`-point `g` carrying `x` to the restriction of `x'`, together with the two composites of
`E ≫ t` with the projections. -/
private theorem rawFullData (x : yoneda.obj U ⟶ X.left) (x' : yoneda.obj U' ⟶ X.left)
    (f : U ⟶ U') (E : yoneda.obj U ⟶ pullback G.obj.X.hom (x ≫ X.hom))
    (t : pullback G.obj.X.hom (x ≫ X.hom) ⟶ pullback G.obj.X.hom (x' ≫ X.hom))
    (hE : E ≫ pullback.snd G.obj.X.hom (x ≫ X.hom) = 𝟙 (yoneda.obj U))
    (ht : t ≫ pullback.snd G.obj.X.hom (x' ≫ X.hom) =
      pullback.snd G.obj.X.hom (x ≫ X.hom) ≫ yoneda.map f)
    (hcb : yoneda.map f ≫ x' ≫ X.hom = x ≫ X.hom)
    (htm : t ≫ trivialTorsorMap hB G X U' x' = trivialTorsorMap hB G X U x)
    (hEm : E ≫ trivialTorsorMap hB G X U x = x) :
    ∃ (g : yoneda.obj U ⟶ G.obj.X.left) (hg : g ≫ G.obj.X.hom = x ≫ X.hom),
      pullback.lift g x hg ≫ (γ[G.obj.X, X]).left = yoneda.map f ≫ x' ∧
        g ≫ (ι[G.obj.X]).left =
          (E ≫ t) ≫ pullback.fst G.obj.X.hom (x' ≫ X.hom) ∧
        (E ≫ t) ≫ pullback.snd G.obj.X.hom (x' ≫ X.hom) = yoneda.map f := by
  have hzs : (E ≫ t) ≫ pullback.snd G.obj.X.hom (x' ≫ X.hom) = yoneda.map f := by
    rw [Category.assoc, ht, ← Category.assoc, hE, Category.id_comp]
  have ha : ((E ≫ t) ≫ pullback.fst G.obj.X.hom (x' ≫ X.hom)) ≫ G.obj.X.hom =
      x ≫ X.hom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hzs, hcb]
  have hzm : (E ≫ t) ≫ trivialTorsorMap hB G X U' x' = x := by
    rw [Category.assoc, htm, hEm]
  have hg : (((E ≫ t) ≫ pullback.fst G.obj.X.hom (x' ≫ X.hom)) ≫ (ι[G.obj.X]).left) ≫
      G.obj.X.hom = x ≫ X.hom := by
    rw [Category.assoc, (ι[G.obj.X]).w, ha]
  refine ⟨_, hg, rawUnitAction hB G X x x' f (E ≫ t) hzs ha hzm hg, ?_, hzs⟩
  let UB : Over B := Over.mk (x ≫ X.hom)
  let a₀ : UB ⟶ G.obj.X :=
    Over.homMk ((E ≫ t) ≫ pullback.fst G.obj.X.hom (x' ≫ X.hom)) ha
  exact congrArg Over.Hom.left (inv_inv a₀)

/-- **Stacks 04WM.** The comparison functor is full: a morphism of `[[X/G]]` between trivial
torsors determines, through its value on the unit section, a `G`-point carrying one of the two
`X`-valued points to the other, and that `G`-point is the group element of a pointwise arrow
mapping to the given morphism. -/
theorem actionPointwiseComparison_full : (actionPointwiseComparison hB G X hX).Full where
  map_surjective {A A'} m := by
    obtain ⟨g, hg, hact, hinv, hsnd⟩ := rawFullData hB G X
      (actionPointwiseValue hB G X hX A) (actionPointwiseValue hB G X hX A') m.toHom.f
      (η[(pullbackGroup hB G A.base
        (actionPointwiseValue hB G X hX A ≫ X.hom)).obj.X]).left m.toHom.g
      (η[(pullbackGroup hB G A.base
        (actionPointwiseValue hB G X hX A ≫ X.hom)).obj.X]).w
      m.toHom.isPullback.w m.toHom.comp_b m.comp_map
      (trivialTorsorMap_unit hB G X A.base (actionPointwiseValue hB G X hX A))
    obtain ⟨k, hk, hkg⟩ := exists_actionPointwiseMorphism hB G X hX m.toHom.f g hg hact
    have hTsnd : ((actionPointwiseComparison hB G X hX).map k).toHom.g ≫
        pullback.snd G.obj.X.hom (actionPointwiseValue hB G X hX A' ≫ X.hom) =
          pullback.snd G.obj.X.hom (actionPointwiseValue hB G X hX A ≫ X.hom) ≫
            yoneda.map k.base :=
      pullback.lift_snd _ _ _
    have h₀ : ((η[(pullbackGroup hB G A.base
            (actionPointwiseValue hB G X hX A ≫ X.hom)).obj.X]).left ≫
          ((actionPointwiseComparison hB G X hX).map k).toHom.g) ≫
            pullback.fst G.obj.X.hom (actionPointwiseValue hB G X hX A' ≫ X.hom) =
        ((η[(pullbackGroup hB G A.base
            (actionPointwiseValue hB G X hX A ≫ X.hom)).obj.X]).left ≫ m.toHom.g) ≫
          pullback.fst G.obj.X.hom (actionPointwiseValue hB G X hX A' ≫ X.hom) :=
      (Category.assoc _ _ _).trans
        ((unit_comp_trivialTorsorRightTranslation hB G
            (actionPointwiseValue hB G X hX A ≫ X.hom)
            (actionPointwiseValue hB G X hX A' ≫ X.hom) k.base
            (actionPointwise_base_compat hB G X hX k)
            (actionPointwiseGroupElement hB G X hX k)
            (actionPointwise_group_compat hB G X hX k)).trans
          ((congrArg (· ≫ (ι[G.obj.X]).left) hkg).trans hinv))
    have h₁ : ((η[(pullbackGroup hB G A.base
            (actionPointwiseValue hB G X hX A ≫ X.hom)).obj.X]).left ≫
          ((actionPointwiseComparison hB G X hX).map k).toHom.g) ≫
            pullback.snd G.obj.X.hom (actionPointwiseValue hB G X hX A' ≫ X.hom) =
        ((η[(pullbackGroup hB G A.base
            (actionPointwiseValue hB G X hX A ≫ X.hom)).obj.X]).left ≫ m.toHom.g) ≫
          pullback.snd G.obj.X.hom (actionPointwiseValue hB G X hX A' ≫ X.hom) :=
      ((Category.assoc _ _ _).trans
        ((congrArg ((η[(pullbackGroup hB G A.base
              (actionPointwiseValue hB G X hX A ≫ X.hom)).obj.X]).left ≫ ·) hTsnd).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ yoneda.map k.base)
                (η[(pullbackGroup hB G A.base
                  (actionPointwiseValue hB G X hX A ≫ X.hom)).obj.X]).w).trans
              ((Category.id_comp _).trans (congrArg yoneda.map hk)))))).trans hsnd.symm
    exact ⟨k, trivialTorsorWithMapHom_ext hB G X _ m hk (pullback.hom_ext h₀ h₁)⟩

end Full

/-! ### Clause (1) of Stacks 02ZN -/

section MorPresheaf

universe u₂

variable {𝒮 : Type u₂} [Category.{u + 1} 𝒮] {p : 𝒮 ⥤ BigFppfOver 𝒞 S hS} [p.IsFibered]
  [(TorsorWithMap.projection hB G X).IsFibered]

/-- **Clause (1) of Stacks 02ZN for `F_p`**: the map of morphism presheaves induced by `F_p` is
an isomorphism.  `F_p` is fully faithful, and a fully faithful 1-morphism induces a fully
faithful functor on every fibre, so the comparison is an isomorphism rather than merely a local
one.

The morphism presheaves of Stacks 042V are formed for two categories over the site with a common
hom universe, while the pointwise action groupoid has morphisms one universe below those of
`[[X/G]]`; so `F_p` is composed with a fully faithful functor `L` raising them, which is how it
enters the comparison of stackifications. -/
theorem actionPointwiseComparison_morPresheafMap_isIso
    (L : 𝒮 ⥤ (actionPointwiseCategory hB G X hX).obj) [L.Full] [L.Faithful]
    (hF : p.IsFibredOneMorphism (TorsorWithMap.projection hB G X)
      (L ⋙ actionPointwiseComparison hB G X hX))
    (U : BigFppfOver 𝒞 S hS) (x y : p.Fiber U) :
    IsIso (hF.morPresheafMap x y) :=
  have := actionPointwiseComparison_full hB G X hX
  have := actionPointwiseComparison_faithful hB G X hX
  Comma.isIso_morPresheafMap_of_fullyFaithful hF x y

/-- **Clause (1) of Stacks 02ZN for `F_p`**, in the shape the comparison of two stackifications
consumes: the map of morphism presheaves is locally injective and locally surjective, being an
isomorphism. -/
theorem actionPointwiseComparison_locallyBijective
    (L : 𝒮 ⥤ (actionPointwiseCategory hB G X hX).obj) [L.Full] [L.Faithful]
    (hF : p.IsFibredOneMorphism (TorsorWithMap.projection hB G X)
      (L ⋙ actionPointwiseComparison hB G X hX))
    (U : BigFppfOver 𝒞 S hS) (x y : p.Fiber U) :
    Presheaf.IsLocallyInjective ((BigFppfOver.topology 𝒞 S hS).over U)
        (hF.morPresheafMap x y) ∧
      Presheaf.IsLocallySurjective ((BigFppfOver.topology 𝒞 S hS).over U)
        (hF.morPresheafMap x y) :=
  have := actionPointwiseComparison_morPresheafMap_isIso hB G X hX L hF U x y
  ⟨inferInstance, inferInstance⟩

end MorPresheaf

/-! ### Local surjectivity of the structure morphism of a torsor -/

/-- The structure morphism of an fppf `G`-torsor is locally surjective for the fppf topology: it
has sections after the fppf covering of its base that trivialises the torsor, and an object whose
structure morphism has a section after an fppf covering has sections locally. -/
theorem torsorObj_isLocallySurjective (T : TorsorObj hB G) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology 𝒞 S hS) T.total.hom := by
  obtain ⟨I, Bi, fi, -, hcover, hsec⟩ := T.isFppfTorsor.2
  exact isLocallySurjective_of_fppfCovering_sections 𝒞 S hS T.U T.total Bi fi hcover hsec

/-! ### The essential image of the comparison functor -/

section EssImage

universe u₁ v₁

/-- A morphism of modules out of the left regular action of a group object on itself is
determined by its value on the unit: it is `h ↦ h · m` for `m` that value. -/
private theorem regularAction_hom_eq {C : Type u₁} [Category.{v₁} C]
    [CartesianMonoidalCategory C] (H M : C) [GrpObj H] [ModObj H M]
    (f : H ⟶ M) (hf : letI := ModObj.regular H; IsModHom H f) :
    f = CartesianMonoidalCategory.lift (𝟙 H)
      (CartesianMonoidalCategory.toUnit H ≫ η[H] ≫ f) ≫ γ[H, M] := by
  let := ModObj.regular H
  let := hf
  have h := IsModHom.map_smul f (𝟙 H) (1 : H ⟶ H)
  change ((𝟙 H) * 1) ≫ f =
    CartesianMonoidalCategory.lift (𝟙 H) ((1 : H ⟶ H) ≫ f) ≫ γ[H, M] at h
  rw [mul_one, Category.id_comp] at h
  simpa only [CategoryTheory.Hom.one_def, Category.assoc] using h

end EssImage

/-- The morphism of `[[X/G]]` out of a trivial torsor supplied by a trivialisation of the
underlying torsor.  All the data of the object of `[[X/G]]` are variables, so that the equation
identifying its morphism to `B` with `x ≫ X.hom` can be substituted: the two spellings of the
total space of the trivial torsor agree only after that substitution. -/
private theorem exists_trivialTorsorWithMapHom_of_trivialisation
    (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ B)
    (P : Over (yoneda.obj U)) (hP : IsAlgebraicSpace 𝒞 S hS P.left)
    (act : ModObj (pullbackGroup hB G U b).obj.X P)
    (hTor : @IsFppfTorsor 𝒞 S hS (yoneda.obj U) (isAlgebraicSpace_yoneda 𝒞 S hS U)
      (pullbackGroup hB G U b).obj.X P _ act (pullbackGroup hB G U b).property hP)
    (φ : P.left ⟶ X.left) (hφ : φ ≫ X.hom = P.hom ≫ b)
    (hsm : (γ[(pullbackGroup hB G U b).obj.X,P]).left ≫ φ =
      actionComparison X ⟨U, b, P, hP, act, hTor⟩ φ hφ ≫ (γ[G.obj.X,X]).left)
    (z : (pullbackGroup hB G U b).obj.X ⟶ P) (hziso : IsIso z.left)
    (hzmod : letI := ModObj.regular (pullbackGroup hB G U b).obj.X
      IsModHom (pullbackGroup hB G U b).obj.X z)
    (x : yoneda.obj U ⟶ X.left) (hb : x ≫ X.hom = b)
    (hc : pullback.fst G.obj.X.hom b ≫ G.obj.X.hom =
      ((pullbackGroup hB G U b).obj.X.hom ≫ x) ≫ X.hom)
    (heq : z.left ≫ φ = pullback.lift (pullback.fst G.obj.X.hom b)
      ((pullbackGroup hB G U b).obj.X.hom ≫ x) hc ≫ (γ[G.obj.X,X]).left) :
    ∃ n : trivialTorsorWithMap hB G X U x ⟶
        ({ toTorsorObj := ⟨U, b, P, hP, act, hTor⟩, map := φ, map_over := hφ,
            smul_map := hsm } : TorsorWithMap hB G X), n.toHom.f = 𝟙 U := by
  subst hb
  have hpb : IsPullback z.left (pullbackGroup hB G U (x ≫ X.hom)).obj.X.hom P.hom
      (yoneda.map (𝟙 U)) :=
    IsPullback.of_horiz_isIso ⟨((Over.w z).trans (Category.comp_id _).symm).trans
      (congrArg ((pullbackGroup hB G U (x ≫ X.hom)).obj.X.hom ≫ ·) (yoneda.map_id U).symm)⟩
  have hcb : yoneda.map (𝟙 U) ≫ x ≫ X.hom = x ≫ X.hom :=
    (congrArg (· ≫ x ≫ X.hom) (yoneda.map_id U)).trans (Category.id_comp (x ≫ X.hom))
  have hgid : groupBaseChange (T := trivialTorsorObj hB G U (x ≫ X.hom))
      (T' := ⟨U, x ≫ X.hom, P, hP, act, hTor⟩) (𝟙 U) hcb =
      𝟙 (pullback G.obj.X.hom (x ≫ X.hom)) := by
    refine pullback.hom_ext ?_ ?_
    · exact (groupBaseChange_fst (T := trivialTorsorObj hB G U (x ≫ X.hom))
        (T' := ⟨U, x ≫ X.hom, P, hP, act, hTor⟩) (𝟙 U) hcb).trans
        (Category.id_comp _).symm
    · exact (groupBaseChange_snd (T := trivialTorsorObj hB G U (x ≫ X.hom))
          (T' := ⟨U, x ≫ X.hom, P, hP, act, hTor⟩) (𝟙 U) hcb).trans
        ((congrArg (pullback.snd G.obj.X.hom (x ≫ X.hom) ≫ ·) (yoneda.map_id U)).trans
          ((Category.comp_id _).trans (Category.id_comp _).symm))
  have hwfst : ((pullbackGroup hB G U (x ≫ X.hom)).obj.X ◁ z).left ≫
        pullback.fst (pullback.snd G.obj.X.hom (x ≫ X.hom)) P.hom =
      actionBaseChange (T := trivialTorsorObj hB G U (x ≫ X.hom))
          (T' := ⟨U, x ≫ X.hom, P, hP, act, hTor⟩) (𝟙 U) hcb z.left hpb.w.symm ≫
        pullback.fst (pullback.snd G.obj.X.hom (x ≫ X.hom)) P.hom :=
    (Over.whiskerLeft_left_fst (R := (pullbackGroup hB G U (x ≫ X.hom)).obj.X) z).trans
      (((Category.comp_id _).symm.trans
        (congrArg (pullback.fst (pullback.snd G.obj.X.hom (x ≫ X.hom))
          (pullback.snd G.obj.X.hom (x ≫ X.hom)) ≫ ·) hgid.symm)).trans
        (actionBaseChange_fst (T := trivialTorsorObj hB G U (x ≫ X.hom))
          (T' := ⟨U, x ≫ X.hom, P, hP, act, hTor⟩) (𝟙 U) hcb z.left hpb.w.symm).symm)
  have hwsnd : ((pullbackGroup hB G U (x ≫ X.hom)).obj.X ◁ z).left ≫
        pullback.snd (pullback.snd G.obj.X.hom (x ≫ X.hom)) P.hom =
      actionBaseChange (T := trivialTorsorObj hB G U (x ≫ X.hom))
          (T' := ⟨U, x ≫ X.hom, P, hP, act, hTor⟩) (𝟙 U) hcb z.left hpb.w.symm ≫
        pullback.snd (pullback.snd G.obj.X.hom (x ≫ X.hom)) P.hom :=
    (Over.whiskerLeft_left_snd (R := (pullbackGroup hB G U (x ≫ X.hom)).obj.X) z).trans
      (actionBaseChange_snd (T := trivialTorsorObj hB G U (x ≫ X.hom))
        (T' := ⟨U, x ≫ X.hom, P, hP, act, hTor⟩) (𝟙 U) hcb z.left hpb.w.symm).symm
  exact ⟨⟨{ f := 𝟙 U
            comp_b := hcb
            g := z.left
            isPullback := hpb
            smul_comp := (congrArg Over.Hom.left hzmod.smul_hom).trans
              (congrArg (· ≫ (γ[(pullbackGroup hB G U (x ≫ X.hom)).obj.X, P]).left)
                (pullback.hom_ext hwfst hwsnd)) }, heq⟩, rfl⟩

/-- A trivialisation `z` of the torsor of an object of `[[X/G]]` intertwines its equivariant map
with the action of `G` on the point `x` that `z` assigns to the unit section. -/
private theorem trivialisation_comp_map_eq (A : TorsorWithMap hB G X)
    (z : A.toTorsorObj.group ⟶ A.total)
    (hz : letI := ModObj.regular A.toTorsorObj.group
      IsModHom A.toTorsorObj.group z)
    (x : yoneda.obj A.U ⟶ X.left)
    (hxdef : x = (η[A.toTorsorObj.group]).left ≫ z.left ≫ A.map)
    (hc : pullback.fst G.obj.X.hom A.b ≫ G.obj.X.hom =
      (A.toTorsorObj.group.hom ≫ x) ≫ X.hom) :
    z.left ≫ A.map =
      pullback.lift (pullback.fst G.obj.X.hom A.b) (A.toTorsorObj.group.hom ≫ x) hc ≫
        (γ[G.obj.X, X]).left := by
  let l := CartesianMonoidalCategory.lift (𝟙 A.toTorsorObj.group)
    (CartesianMonoidalCategory.toUnit A.toTorsorObj.group ≫ η[A.toTorsorObj.group] ≫ z)
  have hlfst : l.left ≫ pullback.fst (pullback.snd G.obj.X.hom A.b) A.total.hom =
      𝟙 A.toTorsorObj.group.left :=
    congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst _ _)
  have hlsnd : l.left ≫ pullback.snd (pullback.snd G.obj.X.hom A.b) A.total.hom =
      A.toTorsorObj.group.hom ≫ (η[A.toTorsorObj.group]).left ≫ z.left :=
    congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd _ _)
  have h₀ : (l.left ≫ actionComparison X A.toTorsorObj A.map A.map_over) ≫
          pullback.fst G.obj.X.hom X.hom =
      pullback.lift (pullback.fst G.obj.X.hom A.b) (A.toTorsorObj.group.hom ≫ x) hc ≫
        pullback.fst G.obj.X.hom X.hom :=
    (Category.assoc _ _ _).trans
      ((congrArg (l.left ≫ ·) (actionComparison_fst X A.toTorsorObj A.map A.map_over)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ pullback.fst G.obj.X.hom A.b) hlfst).trans
            ((Category.id_comp _).trans (pullback.lift_fst _ _ _).symm))))
  have h₁ : (l.left ≫ actionComparison X A.toTorsorObj A.map A.map_over) ≫
          pullback.snd G.obj.X.hom X.hom =
      pullback.lift (pullback.fst G.obj.X.hom A.b) (A.toTorsorObj.group.hom ≫ x) hc ≫
        pullback.snd G.obj.X.hom X.hom :=
    (Category.assoc _ _ _).trans
      ((congrArg (l.left ≫ ·) (actionComparison_snd X A.toTorsorObj A.map A.map_over)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ A.map) hlsnd).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (A.toTorsorObj.group.hom ≫ ·)
                  ((Category.assoc _ _ _).trans hxdef.symm)).trans
                (pullback.lift_snd _ _ _).symm)))))
  conv_lhs => rw [regularAction_hom_eq A.toTorsorObj.group A.total z hz]
  rw [Over.comp_left, Category.assoc, A.smul_map]
  -- The last two steps are a term: the tensor product of the slice category is a chosen pullback
  -- whose cone is not exposed here, so the source of the comparison morphism has two spellings
  -- that only term elaboration identifies, and `rw` declines to build a motive over them.
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (γ[G.obj.X, X]).left) (pullback.hom_ext h₀ h₁))

/-- **Stacks 04WM.** An object of `[[X/G]]` whose underlying torsor is a trivial pseudo-torsor is
in the essential image of the comparison functor: a trivialisation `z` of the torsor carries the
unit section to a point `x` of `X`, the equivariant map becomes `h ↦ h · x`, so `z` is a morphism
of `[[X/G]]` from the trivial torsor attached to `x`, and it lies over an identity of the site,
hence is an isomorphism because the projection of `[[X/G]]` is fibred in groupoids. -/
theorem torsorWithMap_mem_essImage_of_isTrivial (A : TorsorWithMap hB G X)
    (hA : IsTrivialPseudoTorsor A.toTorsorObj.group A.toTorsorObj.total) :
    (actionPointwiseComparison hB G X hX).essImage A := by
  obtain ⟨e⟩ := hA
  have hz : let := ModObj.regular A.toTorsorObj.group
      IsModHom A.toTorsorObj.group e.hom.hom := inferInstance
  obtain ⟨x, hxdef⟩ : ∃ x : yoneda.obj A.U ⟶ X.left,
      x = (η[A.toTorsorObj.group]).left ≫ e.hom.hom.left ≫ A.map := ⟨_, rfl⟩
  have hzw : e.hom.hom.left ≫ A.total.hom = A.toTorsorObj.group.hom := Over.w e.hom.hom
  have hew : (η[A.toTorsorObj.group]).left ≫ A.toTorsorObj.group.hom =
      𝟙 (yoneda.obj A.U) := Over.w (η[A.toTorsorObj.group])
  have hb : x ≫ X.hom = A.b := by
    rw [hxdef, Category.assoc, Category.assoc, A.map_over,
      ← Category.assoc e.hom.hom.left, hzw, ← Category.assoc, hew, Category.id_comp]
  have hc : pullback.fst G.obj.X.hom A.b ≫ G.obj.X.hom =
      (A.toTorsorObj.group.hom ≫ x) ≫ X.hom := by
    rw [Category.assoc, hb]
    exact pullback.condition
  have hziso : IsIso e.hom.hom.left := by
    have : IsIso e.hom.hom := (Mod.forget _).map_isIso e.hom
    exact (Over.forget _).map_isIso e.hom.hom
  obtain ⟨n, hn⟩ := exists_trivialTorsorWithMapHom_of_trivialisation hB G X A.U A.b
    A.total A.isAlgebraicSpace A.action A.isFppfTorsor A.map A.map_over A.smul_map
    e.hom.hom hziso hz x hb hc (trivialisation_comp_map_eq hB G X A e.hom.hom hz x hxdef hc)
  -- Every morphism lifts its own image, and `hn` says that image is the identity; the transport is
  -- a term rather than `rw`, which would ask the unifier of the motive to see through the
  -- projection of `[[X/G]]`.
  have hnlift : (TorsorWithMap.projection hB G X).IsHomLift (𝟙 A.U) n :=
    hn ▸ CategoryTheory.IsHomLift.map (TorsorWithMap.projection hB G X) n
  have := (TorsorWithMap.projection_isFiberedInGroupoids (hB := hB) (G := G) X
    (torsorProjection_isFiberedInGroupoids hB G)).isStronglyCartesian_homLift (𝟙 A.U) n
  have hniso : IsIso n :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso
      (TorsorWithMap.projection hB G X) (𝟙 A.U) n
  refine ⟨actionPointwiseObject hB G X hX A.U x, ⟨?_⟩⟩
  refine Iso.trans (eqToIso ?_) (asIso n)
  show trivialTorsorWithMap hB G X A.U
    (actionPointwiseValue hB G X hX (actionPointwiseObject hB G X hX A.U x)) =
      trivialTorsorWithMap hB G X A.U x
  rw [actionPointwiseValue_actionPointwiseObject]

/-! ### Clause (2) of Stacks 02ZN -/

/-- **Clause (2) of Stacks 02ZN for `F_p`, on underlying objects.** Every object of `[[X/G]]` is,
on a covering sieve of its base, in the essential image of `F_p`: the covering is the image sieve
of the structure morphism of the torsor at the tautological point of the base, the restriction of
the torsor along a member of that sieve has a section, hence is a trivial pseudo-torsor, hence in
the essential image. -/
theorem actionPointwiseComparison_exists_covering_essImage
    [(TorsorWithMap.projection hB G X).IsFibered]
    (U : BigFppfOver 𝒞 S hS) (y : (TorsorWithMap.projection hB G X).Fiber U) :
    ∃ R ∈ BigFppfOver.topology 𝒞 S hS U,
      ∀ ⦃V : BigFppfOver 𝒞 S hS⦄ ⦃f : V ⟶ U⦄, R.arrows f →
        (actionPointwiseComparison hB G X hX).essImage
          (Functor.pullbackFiber (TorsorWithMap.projection hB G X) y f).val := by
  have hA : y.val.U = U := y.property
  refine ⟨Presheaf.imageSieve y.val.total.hom (eqToHom hA.symm : U ⟶ y.val.U),
    (torsorObj_isLocallySurjective hB G y.val.toTorsorObj).imageSieve_mem _, ?_⟩
  rintro V f ⟨s, hs⟩
  have hsx : yonedaEquiv.symm s ≫ y.val.total.hom =
      yoneda.map (f ≫ eqToHom hA.symm) :=
    yonedaEquiv.injective <| by rwa [yonedaEquiv_comp, Equiv.apply_symm_apply]
  have hC : (Functor.pullbackFiber (TorsorWithMap.projection hB G X) y f).val.U = V :=
    (Functor.pullbackFiber (TorsorWithMap.projection hB G X) y f).property
  have ht : (Functor.IsPreFibered.pullbackMap y.property f).toHom.f =
      eqToHom hC ≫ f ≫ eqToHom hA.symm :=
    IsHomLift.fac' (TorsorWithMap.projection hB G X) f
      (Functor.IsPreFibered.pullbackMap y.property f)
  have hsx' : (yoneda.map (eqToHom hC) ≫ yonedaEquiv.symm s) ≫ y.val.total.hom =
      𝟙 _ ≫ yoneda.map (Functor.IsPreFibered.pullbackMap y.property f).toHom.f := by
    rw [Category.assoc, hsx, Category.id_comp, ht, ← CategoryTheory.Functor.map_comp]
  have hsec : Nonempty (𝟙_ (Over (yoneda.obj
      (Functor.pullbackFiber (TorsorWithMap.projection hB G X) y f).val.U)) ⟶
      (Functor.pullbackFiber (TorsorWithMap.projection hB G X) y f).val.total) :=
    ⟨Over.homMk ((Functor.IsPreFibered.pullbackMap y.property f).toHom.isPullback.lift
      (yoneda.map (eqToHom hC) ≫ yonedaEquiv.symm s) (𝟙 _) hsx')
      ((Functor.IsPreFibered.pullbackMap y.property f).toHom.isPullback.lift_snd _ _ hsx')⟩
  exact torsorWithMap_mem_essImage_of_isTrivial hB G X hX
    (Functor.pullbackFiber (TorsorWithMap.projection hB G X) y f).val
    ((AlgebraicGeometry.isTrivial_iff_exists_globalSection
      (Functor.pullbackFiber (TorsorWithMap.projection hB G X) y f).val.toTorsorObj.group
      (Functor.pullbackFiber (TorsorWithMap.projection hB G X) y f).val.total
      (Functor.pullbackFiber (TorsorWithMap.projection hB G X) y f).val.isFppfTorsor.1).2 hsec)

section LocallyEssImage

universe u₃

/-- **Clause (2) of Stacks 02ZN for `F_p`**, in the shape the comparison of two stackifications
consumes.  As for clause (1), the morphism out of the pointwise action groupoid is `F_p` composed
with a functor `L` raising the universe of the morphisms; `L` is assumed surjective on objects,
which is all that is needed to transport the essential image. -/
theorem actionPointwiseComparison_locallyEssImage {𝒮 : Type u₃} [Category.{u + 1} 𝒮]
    {p : 𝒮 ⥤ BigFppfOver 𝒞 S hS} [p.IsFibered]
    [(TorsorWithMap.projection hB G X).IsFibered]
    (hp : p.IsFiberedInGroupoids)
    (L : 𝒮 ⥤ (actionPointwiseCategory hB G X hX).obj)
    (hLobj : ∀ A : (actionPointwiseCategory hB G X hX).obj, ∃ a : 𝒮, L.obj a = A)
    (hcomp : (L ⋙ actionPointwiseComparison hB G X hX) ⋙
      TorsorWithMap.projection hB G X = p)
    (U : BigFppfOver 𝒞 S hS) (y : (TorsorWithMap.projection hB G X).Fiber U) :
    ∃ R ∈ BigFppfOver.topology 𝒞 S hS U,
      ∀ ⦃V : BigFppfOver 𝒞 S hS⦄ ⦃f : V ⟶ U⦄, R.arrows f →
        (Functor.fiberFunctorOfCompEq hcomp V).essImage
          (Functor.pullbackFiber (TorsorWithMap.projection hB G X) y f) := by
  obtain ⟨R, hR, h⟩ := actionPointwiseComparison_exists_covering_essImage hB G X hX U y
  refine ⟨R, hR, fun {V} {f} hf => ?_⟩
  refine Functor.Stackification.essImage_fiberFunctor_of_essImage hp hcomp _ ?_
  obtain ⟨a, ⟨i⟩⟩ := h hf
  obtain ⟨a', ha'⟩ := hLobj a
  exact ⟨a', ⟨eqToIso (congrArg (actionPointwiseComparison hB G X hX).obj ha') ≪≫ i⟩⟩

end LocallyEssImage

end AlgebraicGeometry.Space

end
