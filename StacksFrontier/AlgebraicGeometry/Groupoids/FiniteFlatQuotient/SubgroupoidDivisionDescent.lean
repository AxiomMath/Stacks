module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.CanonicalDatum
public import StacksFrontier.AlgebraicGeometry.Descent.SeparatedQuasiFiniteSchemeDescent
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.SubgroupoidDivision
public import StacksFrontier.AlgebraicGeometry.Groupoids.FullyFaithfulRestriction
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Evaluation
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Comp
import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescentData
import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescentTransport
import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.DescendedOperations
import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations

/-!
# Division of a groupoid scheme by a finite locally free subgroupoid

Let `(U, R, s, t, c)` be a groupoid scheme over `S` and let `(U, P, s|_P, t|_P, c|_P)` be a
subgroupoid on the same object scheme whose source and target maps are finite locally free and
whose pre-relation `j|_P = (t|_P, s|_P)` is a monomorphism. If `U` is affine and the pre-relation
`j = (t, s)` of the ambient groupoid is separated, locally of finite type and locally
quasi-finite, then `U/P` is representable by an affine scheme `Ū`, the quotient morphism
`U ⟶ Ū` is finite locally free and surjective, `P` is the kernel pair `U ×_Ū U`, and the ambient
groupoid `R` is the restriction of a groupoid scheme on `Ū`.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.Division` records the affine quotient, the quotient map and
  the descended groupoid together with their canonical properties.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_division` constructs a division of the groupoid, which
  is all four conclusions of Tag 04S4 at once.

## Implementation notes

The first three conclusions are Tag 03BM applied to the subgroupoid, whose hypotheses are
supplied by `AlgebraicGeometry.isAffine_arrows_of_isFiniteLocallyFree_source` and
`AlgebraicGeometry.isEquivalenceRelation_of_mono_groupoidPreRelation`: the quotient is
`AlgebraicGeometry.quotientOver`, the spectrum of the ring of invariant functions, so affineness
of `Ū` is immediate from `AlgebraicGeometry.quotientOver_left`. That the quotient is `U/P` is
recorded as the coequalizer universal property among fppf sheaves rather than as an isomorphism
of sheaves, which is what `Division.quotient_universal` says; it is deduced from the kernel-pair
square `AlgebraicGeometry.isPullback_objectsToInvariantSpectrum` together with the quotient map
generating a covering sieve, by the sheaf condition for the one-member covering.

The fourth conclusion is descent of `R` along `U ×_S U ⟶ Ū ×_S Ū`. The descent datum is built
from the *conjugation transport* of the arrows of `R`: given an arrow of `R` over a pair of
generalized points of `U` and a second pair with the same image in `Ū`, the unique arrows of `P`
joining the pairs conjugate the given arrow to one over the second pair. That the conjugates
compose, invert and respect identities is `conjugation_operation_relations`, and these are
exactly the data a gluing isomorphism satisfying the cocycle condition needs, packaged as
`AlgebraicGeometry.DescentTransport`. The datum is effective by Tag 02W8 in its scheme form,
`AlgebraicGeometry.DescentData.isFamilyEffective_of_forall_isSeparated_of_locallyQuasiFinite`,
whose hypotheses are the separatedness, local finite type and local quasi-finiteness assumed of
`j`. The descended groupoid structure maps are then obtained from the effective-epimorphism
descent of the quotient map, and the groupoid axioms are verified after passing to a covering on
which arrows of `Ū` lift to arrows of `R`, which is `AlgebraicGeometry.exists_local_lifts`.

Full faithfulness of the evaluation functor of `R ⟶ Ū`-groupoid on every test scheme is the
form in which the final conclusion is stated: it says precisely that `R` is the restriction of
the descended groupoid along `U ⟶ Ū`, since the restriction of a groupoid along a morphism of
object schemes is the groupoid whose arrows form the fibre product, and a cartesian square on
arrows is full faithfulness on generalized points.

## References

* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids

universe u

namespace AlgebraicGeometry.GroupoidScheme

private noncomputable def kernelPairArrow {S : Scheme.{u}} (H : GroupoidScheme S)
    {Q : Over S} (q : H.objects ⟶ Q) (hq : IsPullback H.target H.source q q)
    {T : Over S} (x y : H.Evaluation T) (w : x ≫ q = y ≫ q) : x ⟶ y where
  arrow := hq.lift y x w.symm
  source_eq := hq.lift_snd _ _ _
  target_eq := hq.lift_fst _ _ _

/-- The generalized arrow of the arrow scheme underlying an arrow of the groupoid of
generalized points.

This is `Stacks.Groupoids.GroupoidScheme.EvaluationHom.arrow`, but with the argument taken at
the hom type of the groupoid of generalized points rather than at the structure type the
groupoid instance unfolds to. Spelling it this way keeps the terms below type-correct without
unfolding that instance, which is what lets the rewrites be plain `rw`s. -/
private def homArrow {S : Scheme.{u}} {G : GroupoidScheme S} {T : Over S}
    {x y : G.Evaluation T} (a : x ⟶ y) : T ⟶ G.arrows :=
  GroupoidScheme.EvaluationHom.arrow a

private lemma homArrow_source {S : Scheme.{u}} {G : GroupoidScheme S} {T : Over S}
    {x y : G.Evaluation T} (a : x ⟶ y) : homArrow a ≫ G.source = x :=
  GroupoidScheme.EvaluationHom.source_eq a

private lemma homArrow_target {S : Scheme.{u}} {G : GroupoidScheme S} {T : Over S}
    {x y : G.Evaluation T} (a : x ⟶ y) : homArrow a ≫ G.target = y :=
  GroupoidScheme.EvaluationHom.target_eq a

/-- An arrow of the groupoid of generalized points, from a generalized arrow with prescribed
source and target. The companion of `homArrow`, taking its value at the hom type. -/
private def pointHom {S : Scheme.{u}} {G : GroupoidScheme S} {T : Over S}
    (x y : G.Evaluation T) (r : T ⟶ G.arrows) (hs : r ≫ G.source = x)
    (ht : r ≫ G.target = y) : x ⟶ y :=
  ⟨r, hs, ht⟩

@[simp]
private lemma homArrow_pointHom {S : Scheme.{u}} {G : GroupoidScheme S} {T : Over S}
    (x y : G.Evaluation T) (r : T ⟶ G.arrows) (hs : r ≫ G.source = x)
    (ht : r ≫ G.target = y) : homArrow (pointHom x y r hs ht) = r := rfl

private lemma kernelPair_hom_ext {S : Scheme.{u}} (H : GroupoidScheme S)
    {Q : Over S} (q : H.objects ⟶ Q) (hq : IsPullback H.target H.source q q)
    {T : Over S} {x y : H.Evaluation T} (a b : x ⟶ y) : a = b :=
  GroupoidScheme.EvaluationHom.ext <| hq.hom_ext (a.target_eq.trans b.target_eq.symm)
    (a.source_eq.trans b.source_eq.symm)

private noncomputable def kernelPairIso {S : Scheme.{u}} (H : GroupoidScheme S)
    {Q : Over S} (q : H.objects ⟶ Q) (hq : IsPullback H.target H.source q q)
    {T : Over S} (x y : H.Evaluation T) (w : x ≫ q = y ≫ q) : x ≅ y :=
  (Groupoid.isoEquivHom x y).symm (kernelPairArrow H q hq x y w)

private lemma kernelPairIso_refl {S : Scheme.{u}} (H : GroupoidScheme S)
    {Q : Over S} (q : H.objects ⟶ Q) (hq : IsPullback H.target H.source q q)
    {T : Over S} (x : H.Evaluation T) :
    kernelPairIso H q hq x x rfl = Iso.refl x :=
  Iso.ext (kernelPair_hom_ext H q hq _ _)

private lemma kernelPairIso_trans {S : Scheme.{u}} (H : GroupoidScheme S)
    {Q : Over S} (q : H.objects ⟶ Q) (hq : IsPullback H.target H.source q q)
    {T : Over S} (x y z : H.Evaluation T)
    (w : x ≫ q = y ≫ q) (w' : y ≫ q = z ≫ q) :
    kernelPairIso H q hq x z (w.trans w') =
      kernelPairIso H q hq x y w ≪≫ kernelPairIso H q hq y z w' :=
  Iso.ext (kernelPair_hom_ext H q hq _ _)

private noncomputable def conjugationEquiv {S : Scheme.{u}} {G H : GroupoidScheme S}
    (i : GroupoidScheme.Hom H G) {Q : Over S} (q : H.objects ⟶ Q)
    (hq : IsPullback H.target H.source q q) {T : Over S}
    (x y x' y' : H.Evaluation T) (hx : x ≫ q = x' ≫ q) (hy : y ≫ q = y' ≫ q) :
    ((i.evaluation T).obj x ⟶ (i.evaluation T).obj y) ≃
      ((i.evaluation T).obj x' ⟶ (i.evaluation T).obj y') :=
  Iso.homCongr ((i.evaluation T).mapIso (kernelPairIso H q hq x x' hx))
    ((i.evaluation T).mapIso (kernelPairIso H q hq y y' hy))

private lemma conjugationEquiv_refl {S : Scheme.{u}} {G H : GroupoidScheme S}
    (i : GroupoidScheme.Hom H G) {Q : Over S} (q : H.objects ⟶ Q)
    (hq : IsPullback H.target H.source q q) {T : Over S}
    (x y : H.Evaluation T) (a : (i.evaluation T).obj x ⟶ (i.evaluation T).obj y) :
    conjugationEquiv i q hq x y x y rfl rfl a = a := by
  simp [conjugationEquiv, kernelPairIso_refl]

private lemma conjugationEquiv_comp {S : Scheme.{u}} {G H : GroupoidScheme S}
    (i : GroupoidScheme.Hom H G) {Q : Over S} (q : H.objects ⟶ Q)
    (hq : IsPullback H.target H.source q q) {T : Over S}
    (x y z x' y' z' : H.Evaluation T)
    (hx : x ≫ q = x' ≫ q) (hy : y ≫ q = y' ≫ q) (hz : z ≫ q = z' ≫ q)
    (a : (i.evaluation T).obj x ⟶ (i.evaluation T).obj y)
    (b : (i.evaluation T).obj y ⟶ (i.evaluation T).obj z) :
    conjugationEquiv i q hq x z x' z' hx hz (a ≫ b) =
      conjugationEquiv i q hq x y x' y' hx hy a ≫
        conjugationEquiv i q hq y z y' z' hy hz b :=
  Iso.homCongr_comp _ _ _ _ _

private lemma conjugationEquiv_trans {S : Scheme.{u}} {G H : GroupoidScheme S}
    (i : GroupoidScheme.Hom H G) {Q : Over S} (q : H.objects ⟶ Q)
    (hq : IsPullback H.target H.source q q) {T : Over S}
    (x y x' y' x'' y'' : H.Evaluation T)
    (hx : x ≫ q = x' ≫ q) (hy : y ≫ q = y' ≫ q)
    (hx' : x' ≫ q = x'' ≫ q) (hy' : y' ≫ q = y'' ≫ q)
    (a : (i.evaluation T).obj x ⟶ (i.evaluation T).obj y) :
    conjugationEquiv i q hq x' y' x'' y'' hx' hy'
        (conjugationEquiv i q hq x y x' y' hx hy a) =
      conjugationEquiv i q hq x y x'' y'' (hx.trans hx') (hy.trans hy') a := by
  dsimp only [conjugationEquiv]
  rw [kernelPairIso_trans H q hq x x' x'' hx hx',
    kernelPairIso_trans H q hq y y' y'' hy hy']
  simp [Iso.homCongr_apply, Category.assoc]

@[simp]
private lemma homArrow_kernelPairArrow {S : Scheme.{u}} (H : GroupoidScheme S)
    {Q : Over S} (q : H.objects ⟶ Q) (hq : IsPullback H.target H.source q q)
    {T : Over S} (x y : H.Evaluation T) (w : x ≫ q = y ≫ q) :
    homArrow (kernelPairArrow H q hq x y w) = hq.lift y x w.symm := rfl

/-- The connecting arrow of the kernel pair is natural in the test scheme. -/
private lemma isPullback_lift_precomp {S : Scheme.{u}} (H : GroupoidScheme S)
    {Q : Over S} (q : H.objects ⟶ Q) (hq : IsPullback H.target H.source q q)
    {T T' : Over S} (g : T' ⟶ T) (a b : T ⟶ H.objects) (w : a ≫ q = b ≫ q) :
    g ≫ hq.lift a b w = hq.lift (g ≫ a) (g ≫ b)
      (by simpa only [Category.assoc] using congrArg (g ≫ ·) w) := by
  apply hq.hom_ext <;> simp

private lemma compose_precomp {S : Scheme.{u}} (G : GroupoidScheme S)
    {T T' : Over S} (f : T' ⟶ T) (a b : T ⟶ G.arrows)
    (w : a ≫ G.source = b ≫ G.target) :
    f ≫ G.compose a b w = G.compose (f ≫ a) (f ≫ b)
      (by simpa only [Category.assoc] using congrArg (f ≫ ·) w) := by
  dsimp only [GroupoidScheme.compose]
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]

private lemma homArrow_comp {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over S} {x y z : G.Evaluation T} (a : x ⟶ y) (b : y ⟶ z) :
    homArrow (a ≫ b) =
      G.compose (homArrow b) (homArrow a)
        ((homArrow_source b).trans (homArrow_target a).symm) := rfl

private lemma homArrow_inv {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over S} {x y : G.Evaluation T} (a : x ⟶ y) :
    homArrow (Groupoid.inv a) = homArrow a ≫ G.inverse := rfl

private lemma homArrow_map {S : Scheme.{u}} {G H : GroupoidScheme S}
    (i : GroupoidScheme.Hom H G) {T : Over S} {x y : H.Evaluation T} (a : x ⟶ y) :
    homArrow ((i.evaluation T).map a) = homArrow a ≫ i.mapArrows := rfl

/-- Conjugation, written out: it is composition with the two connecting arrows of the kernel
pair. The right-hand side mentions only arrows of the groupoid of generalized points, so it is
the form in which conjugation can be rewritten under a `homArrow`. -/
private lemma conjugationEquiv_apply {S : Scheme.{u}} {G H : GroupoidScheme S}
    (i : GroupoidScheme.Hom H G) {Q : Over S} (q : H.objects ⟶ Q)
    (hq : IsPullback H.target H.source q q) {T : Over S}
    (x y x' y' : H.Evaluation T) (hx : x ≫ q = x' ≫ q) (hy : y ≫ q = y' ≫ q)
    (a : (i.evaluation T).obj x ⟶ (i.evaluation T).obj y) :
    conjugationEquiv i q hq x y x' y' hx hy a =
      (i.evaluation T).map (Groupoid.inv (kernelPairArrow H q hq x x' hx)) ≫ a ≫
        (i.evaluation T).map (kernelPairArrow H q hq y y' hy) := by
  simp only [conjugationEquiv, Iso.homCongr_apply, kernelPairIso, Functor.mapIso_hom,
    Functor.mapIso_inv, Groupoid.isoEquivHom_symm_apply_hom,
    Groupoid.isoEquivHom_symm_apply_inv, ← Groupoid.inv_eq_inv]

private noncomputable def conjugateArrow {S : Scheme.{u}} {G H : GroupoidScheme S}
    (i : GroupoidScheme.Hom H G) {Q : Over S} (q : H.objects ⟶ Q)
    (hq : IsPullback H.target H.source q q) {T : Over S}
    (x y x' y' : H.Evaluation T) (hx : x ≫ q = x' ≫ q) (hy : y ≫ q = y' ≫ q)
    (r : T ⟶ G.arrows) (hs : r ≫ G.source = x ≫ i.mapObjects)
    (ht : r ≫ G.target = y ≫ i.mapObjects) : T ⟶ G.arrows :=
  homArrow (conjugationEquiv i q hq x y x' y' hx hy
    (pointHom ((i.evaluation T).obj x) ((i.evaluation T).obj y) r hs ht))

private lemma conjugateArrow_source {S : Scheme.{u}} {G H : GroupoidScheme S}
    (i : GroupoidScheme.Hom H G) {Q : Over S} (q : H.objects ⟶ Q)
    (hq : IsPullback H.target H.source q q) {T : Over S}
    (x y x' y' : H.Evaluation T) (hx : x ≫ q = x' ≫ q) (hy : y ≫ q = y' ≫ q)
    (r : T ⟶ G.arrows) (hs : r ≫ G.source = x ≫ i.mapObjects)
    (ht : r ≫ G.target = y ≫ i.mapObjects) :
    conjugateArrow i q hq x y x' y' hx hy r hs ht ≫ G.source = x' ≫ i.mapObjects :=
  (conjugationEquiv i q hq x y x' y' hx hy ⟨r, hs, ht⟩).source_eq

private lemma conjugateArrow_target {S : Scheme.{u}} {G H : GroupoidScheme S}
    (i : GroupoidScheme.Hom H G) {Q : Over S} (q : H.objects ⟶ Q)
    (hq : IsPullback H.target H.source q q) {T : Over S}
    (x y x' y' : H.Evaluation T) (hx : x ≫ q = x' ≫ q) (hy : y ≫ q = y' ≫ q)
    (r : T ⟶ G.arrows) (hs : r ≫ G.source = x ≫ i.mapObjects)
    (ht : r ≫ G.target = y ≫ i.mapObjects) :
    conjugateArrow i q hq x y x' y' hx hy r hs ht ≫ G.target = y' ≫ i.mapObjects :=
  (conjugationEquiv i q hq x y x' y' hx hy ⟨r, hs, ht⟩).target_eq

private lemma conjugateArrow_precomp {S : Scheme.{u}} {G H : GroupoidScheme S}
    (i : GroupoidScheme.Hom H G) {Q : Over S} (q : H.objects ⟶ Q)
    (hq : IsPullback H.target H.source q q) {T T' : Over S} (f : T' ⟶ T)
    (x y x' y' : H.Evaluation T) (hx : x ≫ q = x' ≫ q) (hy : y ≫ q = y' ≫ q)
    (r : T ⟶ G.arrows) (hs : r ≫ G.source = x ≫ i.mapObjects)
    (ht : r ≫ G.target = y ≫ i.mapObjects)
    (hx' : (f ≫ x) ≫ q = (f ≫ x') ≫ q)
    (hy' : (f ≫ y) ≫ q = (f ≫ y') ≫ q)
    (hs' : (f ≫ r) ≫ G.source = (f ≫ x) ≫ i.mapObjects)
    (ht' : (f ≫ r) ≫ G.target = (f ≫ y) ≫ i.mapObjects) :
    f ≫ conjugateArrow i q hq x y x' y' hx hy r hs ht =
      conjugateArrow i q hq (f ≫ x) (f ≫ y) (f ≫ x') (f ≫ y') hx' hy'
        (f ≫ r) hs' ht' := by
  dsimp only [conjugateArrow]
  rw [conjugationEquiv_apply, conjugationEquiv_apply]
  simp only [homArrow_comp, homArrow_map, homArrow_inv, homArrow_pointHom,
    homArrow_kernelPairArrow, compose_precomp, ← Category.assoc,
    isPullback_lift_precomp]

private lemma finiteLocallyFree_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    Stacks.Morphisms.IsFiniteLocallyFree f :=
  (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

/-- The underlying morphism of `prod.map f g` in `Over S` is the induced map of fibre products,
up to the identifications of the products with fibre products. -/
private lemma prod_map_left_eq {S : Scheme.{u}} {X X' Y Y' : Over S} (f : X ⟶ X') (g : Y ⟶ Y') :
    (prod.map f g).left = (Over.prodLeftIsoPullback X Y).hom ≫
      pullback.map X.hom Y.hom X'.hom Y'.hom f.left g.left (𝟙 S) (by simp) (by simp) ≫
        (Over.prodLeftIsoPullback X' Y').inv := by
  apply (cancel_mono (Over.prodLeftIsoPullback X' Y').hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.map, pullback.lift_fst,
      Over.prodLeftIsoPullback_hom_fst, Over.prodLeftIsoPullback_hom_fst_assoc,
      ← Over.comp_left, prod.map_fst]
  · simp only [Category.assoc, pullback.map, pullback.lift_snd,
      Over.prodLeftIsoPullback_hom_snd, Over.prodLeftIsoPullback_hom_snd_assoc,
      ← Over.comp_left, prod.map_snd]

private lemma finiteLocallyFree_prod_map {S : Scheme.{u}} {X X' Y Y' : Over S}
    (f : X ⟶ X') (g : Y ⟶ Y')
    [Stacks.Morphisms.IsFiniteLocallyFree f.left] [Stacks.Morphisms.IsFiniteLocallyFree g.left] :
    Stacks.Morphisms.IsFiniteLocallyFree (prod.map f g).left := by
  let P : MorphismProperty Scheme.{u} := fun _ _ h ↦ Stacks.Morphisms.IsFiniteLocallyFree h
  let : P.IsStableUnderComposition := ⟨fun f g hf hg ↦
    @Stacks.Morphisms.isFiniteLocallyFree_comp _ _ _ f g hf hg⟩
  let p := pullback.map X.hom Y.hom X'.hom Y'.hom f.left g.left (𝟙 S)
    (by simp) (by simp)
  have hp : Stacks.Morphisms.IsFiniteLocallyFree p :=
    MorphismProperty.pullbackMap (P := P) inferInstance inferInstance (Over.w f).symm
      (Over.w g).symm
  rw [prod_map_left_eq]
  let := hp
  let := finiteLocallyFree_of_isIso (Over.prodLeftIsoPullback X Y).hom
  let := finiteLocallyFree_of_isIso (Over.prodLeftIsoPullback X' Y').inv
  exact Stacks.Morphisms.isFiniteLocallyFree_comp _ _

private lemma singleton_fppf_of_finiteLocallyFree {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Stacks.Morphisms.IsFiniteLocallyFree f] [Surjective f] :
    Sieve.generate (Presieve.singleton f) ∈ Scheme.fppfTopology Y := by
  have := Stacks.Morphisms.IsFiniteLocallyFree.flat f
  have := Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation f
  exact Precoverage.generate_mem_toGrothendieck f.singleton_mem_fppfPrecoverage

private lemma kernelPair_transport {S : Scheme.{u}} (H : GroupoidScheme S)
    {V : Over S} (h : H.objects = V) {Q : Over S} (q : H.objects ⟶ Q)
    (hq : IsPullback H.target H.source q q) :
    IsPullback (H.target ≫ eqToHom h) (H.source ≫ eqToHom h)
      (eqToHom h.symm ≫ q) (eqToHom h.symm ≫ q) := by
  cases h
  simpa using hq

private lemma quotient_universal_of_kernelPair {S : Scheme.{u}}
    (J : GrothendieckTopology (Over S)) [J.Subcanonical]
    {R U M : Over S} (r₁ r₂ : R ⟶ U) (f : U ⟶ M)
    (hf : r₁ ≫ f = r₂ ≫ f)
    (hcover : Sieve.generate (Presieve.singleton f) ∈ J M)
    (hkernel : IsIso (pullback.lift r₁ r₂ hf)) :
    ∀ (F : Sheaf J (Type u)) (a : J.yoneda.obj U ⟶ F),
      J.yoneda.map r₁ ≫ a = J.yoneda.map r₂ ≫ a →
      ∃! b : J.yoneda.obj M ⟶ F, J.yoneda.map f ≫ b = a := by
  intro F a ha
  have hF : Presieve.IsSheaf J F.obj :=
    (CategoryTheory.isSheaf_iff_isSheaf_of_type J F.obj).mp F.property
  have hSF : Presieve.IsSheafFor F.obj (Presieve.singleton f) :=
    hF.isSheafFor (Presieve.singleton f) hcover
  let x : F.obj.obj (op U) := J.yonedaEquiv a
  have hrel : F.obj.map r₁.op x = F.obj.map r₂.op x := by
    simp only [x, J.yonedaEquiv_naturality, ha]
  have hcompatible : ∀ {Z : Over S} (p₁ p₂ : Z ⟶ U),
      p₁ ≫ f = p₂ ≫ f → F.obj.map p₁.op x = F.obj.map p₂.op x := by
    intro Z p₁ p₂ hp
    let : IsIso (pullback.lift r₁ r₂ hf) := hkernel
    let e : R ≅ pullback f f := asIso (pullback.lift r₁ r₂ hf)
    have hfst : e.hom ≫ pullback.fst f f = r₁ := by
      simp [e]
    have hsnd : e.hom ≫ pullback.snd f f = r₂ := by
      simp [e]
    have hef : e.inv ≫ r₁ = pullback.fst f f := by rw [← hfst, Iso.inv_hom_id_assoc]
    have hes : e.inv ≫ r₂ = pullback.snd f f := by rw [← hsnd, Iso.inv_hom_id_assoc]
    let l : Z ⟶ R := pullback.lift p₁ p₂ hp ≫ e.inv
    have hl₁ : l ≫ r₁ = p₁ := by
      dsimp [l]
      rw [Category.assoc, hef, pullback.lift_fst]
    have hl₂ : l ≫ r₂ = p₂ := by
      dsimp [l]
      rw [Category.assoc, hes, pullback.lift_snd]
    calc
      F.obj.map p₁.op x = F.obj.map (l ≫ r₁).op x := by rw [hl₁]
      _ = F.obj.map l.op (F.obj.map r₁.op x) := by
        rw [op_comp, Functor.map_comp_apply]
      _ = F.obj.map l.op (F.obj.map r₂.op x) := by rw [hrel]
      _ = F.obj.map (l ≫ r₂).op x := by
        have hcomp : F.obj.map (l ≫ r₂).op = F.obj.map r₂.op ≫ F.obj.map l.op := by
          rw [op_comp, F.obj.map_comp]
        exact (congrArg (fun g => g x) hcomp).symm
      _ = F.obj.map p₂.op x := by rw [hl₂]
  obtain ⟨y, hy, hyuniq⟩ :=
    (Presieve.isSheafFor_singleton.mp hSF) x hcompatible
  let b : J.yoneda.obj M ⟶ F := J.yonedaEquiv.symm y
  have hb : J.yoneda.map f ≫ b = a := by
    apply J.yonedaEquiv.injective
    rw [← J.yonedaEquiv_naturality]
    simpa [b] using hy
  refine ⟨b, hb, ?_⟩
  intro b' hb'
  apply J.yonedaEquiv.injective
  calc
    J.yonedaEquiv b' = y :=
      hyuniq (J.yonedaEquiv b') (by simp only [J.yonedaEquiv_naturality, hb', x])
    _ = J.yonedaEquiv b := by simp [b]

private noncomputable def canonicalProjection {B X : Scheme.{u}} (f : X ⟶ B)
    (Y : Over B) :
    (Over.map f).obj (((canonicalFamilyDescentFunctor
      (fun _ : Unit ↦ f)).functor.obj Y).obj ()) ⟶ Y :=
  (Over.map f).map (eqToHom ((canonicalFamilyDescentFunctor
    (fun _ : Unit ↦ f)).obj Y ())) ≫
    Over.homMk (pullback.fst Y.hom f) pullback.condition

private lemma canonicalProjection_gluing {B X : Scheme.{u}} (f : X ⟶ B)
    (Y : Over B) :
    let D := (canonicalFamilyDescentFunctor (fun _ : Unit ↦ f)).functor.obj Y
    (D.gluing () ()).hom.left ≫ prod.snd ≫ canonicalProjection f Y =
      prod.fst ≫ canonicalProjection f Y := by
  dsimp only
  apply Over.OverMorphism.ext
  have h := (canonicalFamilyDescentFunctor (fun _ : Unit ↦ f)).gluing Y () ()
  let D := (canonicalFamilyDescentFunctor (fun _ : Unit ↦ f)).functor.obj Y
  have h' := congrArg (fun k ↦
    (Over.prodLeftIsoPullback ((Over.map f).obj (D.obj ())) (Over.mk f)).hom ≫ k) h
  dsimp only [D] at h'
  simp only [AlgebraicGeometry.DescentData.gluingPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Over.forget_map, Category.assoc, Iso.hom_inv_id_assoc] at h'
  change _ ≫ (Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj _)).hom ≫
      pullback.snd (Over.mk f).hom ((Over.map f).obj _).hom ≫ _ =
    (Over.prodLeftIsoPullback ((Over.map f).obj _) (Over.mk f)).hom ≫
      pullback.fst ((Over.map f).obj _).hom (Over.mk f).hom ≫ _ at h'
  rw [Over.prodLeftIsoPullback_hom_snd_assoc,
    Over.prodLeftIsoPullback_hom_fst_assoc] at h'
  exact h'

private noncomputable def effectiveProjection {B X : Scheme.{u}} (f : X ⟶ B)
    (W : Over X) (d : DescentTransport (AlgebraicGeometry.structureMap f W))
    (Y : Over B)
    (e : (canonicalFamilyDescentFunctor (fun _ : Unit ↦ f)).functor.obj Y ≅
      transportDescentData f W d) : (Over.map f).obj W ⟶ Y :=
  (Over.map f).map (e.inv.hom ()) ≫ canonicalProjection f Y

private lemma effectiveProjection_move {B X : Scheme.{u}} (f : X ⟶ B)
    (W : Over X) (d : DescentTransport (AlgebraicGeometry.structureMap f W))
    (Y : Over B)
    (e : (canonicalFamilyDescentFunctor (fun _ : Unit ↦ f)).functor.obj Y ≅
      transportDescentData f W d) {T : Over B}
    (a : T ⟶ (Over.map f).obj W) (b : T ⟶ Over.mk f) :
    d.move a b ≫ effectiveProjection f W d Y e = a ≫ effectiveProjection f W d Y e := by
  have h := congrArg (fun k ↦ prod.lift a b ≫ k ≫ prod.snd ≫ canonicalProjection f Y)
    (e.inv.comm () ())
  change prod.lift a b ≫
      prod.map ((Over.map f).map (e.inv.hom ())) (𝟙 _) ≫
      (((canonicalFamilyDescentFunctor (fun _ : Unit ↦ f)).functor.obj Y).gluing
        () ()).hom.left ≫ prod.snd ≫ canonicalProjection f Y =
    prod.lift a b ≫ (transportGluing d).hom ≫
      prod.map (𝟙 _) ((Over.map f).map (e.inv.hom ())) ≫
      prod.snd ≫ canonicalProjection f Y at h
  simpa [Category.assoc, canonicalProjection_gluing, transportGluing,
    d.naturality, reassoc_of% d.naturality, effectiveProjection] using h.symm

private lemma effectiveProjection_isPullback {B X : Scheme.{u}} (f : X ⟶ B)
    (W : Over X) (d : DescentTransport (AlgebraicGeometry.structureMap f W))
    (Y : Over B)
    (e : (canonicalFamilyDescentFunctor (fun _ : Unit ↦ f)).functor.obj Y ≅
      transportDescentData f W d) :
    IsPullback (effectiveProjection f W d Y e).left W.hom Y.hom f := by
  let k : W ≅ (Over.pullback f).obj Y :=
    (AlgebraicGeometry.DescentData.evaluation ()).mapIso e.symm ≪≫
      eqToIso ((canonicalFamilyDescentFunctor (fun _ : Unit ↦ f)).obj Y ())
  apply IsPullback.of_iso_pullback ⟨Over.w (effectiveProjection f W d Y e)⟩
    ((Over.forget X).mapIso k)
  · rfl
  · exact Over.w k.hom


private noncomputable def subgroupoidConjugate {S : Scheme.{u}}
    {G H : GroupoidScheme S} (i : GroupoidScheme.Hom H G)
    (e : H.objects ≅ G.objects) (hi : i.mapObjects = e.hom)
    {Q : Over S} (q : H.objects ⟶ Q) (hq : IsPullback H.target H.source q q)
    {T : Over S} (r : T ⟶ G.arrows) (x y : T ⟶ H.objects)
    (hx : r ≫ G.source ≫ e.inv ≫ q = x ≫ q)
    (hy : r ≫ G.target ≫ e.inv ≫ q = y ≫ q) : T ⟶ G.arrows :=
  conjugateArrow i q hq (r ≫ G.source ≫ e.inv) (r ≫ G.target ≫ e.inv) x y
    (by simpa only [Category.assoc] using hx) (by simpa only [Category.assoc] using hy)
    r (by simp [hi]) (by simp [hi])

private lemma subgroupoidConjugate_source {S : Scheme.{u}}
    {G H : GroupoidScheme S} (i : GroupoidScheme.Hom H G)
    (e : H.objects ≅ G.objects) (hi : i.mapObjects = e.hom)
    {Q : Over S} (q : H.objects ⟶ Q) (hq : IsPullback H.target H.source q q)
    {T : Over S} (r : T ⟶ G.arrows) (x y : T ⟶ H.objects)
    (hx : r ≫ G.source ≫ e.inv ≫ q = x ≫ q)
    (hy : r ≫ G.target ≫ e.inv ≫ q = y ≫ q) :
    subgroupoidConjugate i e hi q hq r x y hx hy ≫ G.source ≫ e.inv = x := by
  rw [← Category.assoc, subgroupoidConjugate, conjugateArrow_source, hi]
  simp

private lemma subgroupoidConjugate_target {S : Scheme.{u}}
    {G H : GroupoidScheme S} (i : GroupoidScheme.Hom H G)
    (e : H.objects ≅ G.objects) (hi : i.mapObjects = e.hom)
    {Q : Over S} (q : H.objects ⟶ Q) (hq : IsPullback H.target H.source q q)
    {T : Over S} (r : T ⟶ G.arrows) (x y : T ⟶ H.objects)
    (hx : r ≫ G.source ≫ e.inv ≫ q = x ≫ q)
    (hy : r ≫ G.target ≫ e.inv ≫ q = y ≫ q) :
    subgroupoidConjugate i e hi q hq r x y hx hy ≫ G.target ≫ e.inv = y := by
  rw [← Category.assoc, subgroupoidConjugate, conjugateArrow_target, hi]
  simp

private lemma subgroupoidConjugate_refl {S : Scheme.{u}}
    {G H : GroupoidScheme S} (i : GroupoidScheme.Hom H G)
    (e : H.objects ≅ G.objects) (hi : i.mapObjects = e.hom)
    {Q : Over S} (q : H.objects ⟶ Q) (hq : IsPullback H.target H.source q q)
    {T : Over S} (r : T ⟶ G.arrows) :
    subgroupoidConjugate i e hi q hq r (r ≫ G.source ≫ e.inv)
      (r ≫ G.target ≫ e.inv) (by simp) (by simp) = r :=
  congrArg GroupoidScheme.EvaluationHom.arrow
    (conjugationEquiv_refl i q hq (r ≫ G.source ≫ e.inv) (r ≫ G.target ≫ e.inv)
      ⟨r, by change r ≫ G.source = (r ≫ G.source ≫ e.inv) ≫ i.mapObjects; simp [hi],
        by change r ≫ G.target = (r ≫ G.target ≫ e.inv) ≫ i.mapObjects; simp [hi]⟩)

private lemma subgroupoidConjugate_precomp {S : Scheme.{u}}
    {G H : GroupoidScheme S} (i : GroupoidScheme.Hom H G)
    (e : H.objects ≅ G.objects) (hi : i.mapObjects = e.hom)
    {Q : Over S} (q : H.objects ⟶ Q) (hq : IsPullback H.target H.source q q)
    {T T' : Over S} (f : T' ⟶ T) (r : T ⟶ G.arrows) (x y : T ⟶ H.objects)
    (hx : r ≫ G.source ≫ e.inv ≫ q = x ≫ q)
    (hy : r ≫ G.target ≫ e.inv ≫ q = y ≫ q)
    (hx' : (f ≫ r) ≫ G.source ≫ e.inv ≫ q = (f ≫ x) ≫ q)
    (hy' : (f ≫ r) ≫ G.target ≫ e.inv ≫ q = (f ≫ y) ≫ q) :
    f ≫ subgroupoidConjugate i e hi q hq r x y hx hy =
      subgroupoidConjugate i e hi q hq (f ≫ r) (f ≫ x) (f ≫ y) hx' hy' := by
  dsimp only [subgroupoidConjugate]
  simpa only [Category.assoc] using conjugateArrow_precomp i q hq f
    (r ≫ G.source ≫ e.inv) (r ≫ G.target ≫ e.inv) x y
    (by simpa only [Category.assoc] using hx) (by simpa only [Category.assoc] using hy)
    r (by simp [hi]) (by simp [hi])
    (by simpa only [Category.assoc] using hx')
    (by simpa only [Category.assoc] using hy') (by simp [hi]) (by simp [hi])

private lemma conjugateArrow_trans {S : Scheme.{u}} {G H : GroupoidScheme S}
    (i : GroupoidScheme.Hom H G) {Q : Over S} (q : H.objects ⟶ Q)
    (hq : IsPullback H.target H.source q q) {T : Over S}
    (x y x' y' x'' y'' : H.Evaluation T)
    (hx : x ≫ q = x' ≫ q) (hy : y ≫ q = y' ≫ q)
    (hx' : x' ≫ q = x'' ≫ q) (hy' : y' ≫ q = y'' ≫ q)
    (r : T ⟶ G.arrows) (hs : r ≫ G.source = x ≫ i.mapObjects)
    (ht : r ≫ G.target = y ≫ i.mapObjects) (hs' ht') :
    conjugateArrow i q hq x' y' x'' y'' hx' hy'
      (conjugateArrow i q hq x y x' y' hx hy r hs ht) hs' ht' =
    conjugateArrow i q hq x y x'' y'' (hx.trans hx') (hy.trans hy') r hs ht :=
  congrArg GroupoidScheme.EvaluationHom.arrow
    (conjugationEquiv_trans i q hq x y x' y' x'' y'' hx hy hx' hy' ⟨r, hs, ht⟩)

private lemma subgroupoidConjugate_trans {S : Scheme.{u}}
    {G H : GroupoidScheme S} (i : GroupoidScheme.Hom H G)
    (e : H.objects ≅ G.objects) (hi : i.mapObjects = e.hom)
    {Q : Over S} (q : H.objects ⟶ Q) (hq : IsPullback H.target H.source q q)
    {T : Over S} (r : T ⟶ G.arrows) (x y x' y' : T ⟶ H.objects)
    (hx : r ≫ G.source ≫ e.inv ≫ q = x ≫ q)
    (hy : r ≫ G.target ≫ e.inv ≫ q = y ≫ q)
    (hx' : x ≫ q = x' ≫ q) (hy' : y ≫ q = y' ≫ q) (hx'' hy'') :
    subgroupoidConjugate i e hi q hq
      (subgroupoidConjugate i e hi q hq r x y hx hy) x' y' hx'' hy'' =
      subgroupoidConjugate i e hi q hq r x' y' (hx.trans hx') (hy.trans hy') := by
  rw [subgroupoidConjugate]
  simp only [subgroupoidConjugate_source, subgroupoidConjugate_target]
  unfold subgroupoidConjugate
  exact conjugateArrow_trans i q hq _ _ _ _ _ _ _ _ hx' hy' r _ _ _ _

private noncomputable abbrev subgroupoidArrowBase {S : Scheme.{u}}
    (G H : GroupoidScheme S) (e : H.objects ≅ G.objects) :=
  prod.lift (G.target ≫ e.inv) (G.source ≫ e.inv)

private noncomputable def subgroupoidMove {S : Scheme.{u}}
    {G H : GroupoidScheme S} (i : GroupoidScheme.Hom H G)
    (e : H.objects ≅ G.objects) (hi : i.mapObjects = e.hom)
    {Q : Over S} (q : H.objects ⟶ Q) (hq : IsPullback H.target H.source q q)
    {T : Over (Q ⨯ Q)}
    (a : T ⟶ Over.mk (subgroupoidArrowBase G H e ≫ prod.map q q))
    (b : T ⟶ Over.mk (prod.map q q)) :
    T ⟶ Over.mk (subgroupoidArrowBase G H e ≫ prod.map q q) := by
  have w : a.left ≫ subgroupoidArrowBase G H e ≫ prod.map q q =
      b.left ≫ prod.map q q := (Over.w a).trans (Over.w b).symm
  have hx : a.left ≫ G.source ≫ e.inv ≫ q = (b.left ≫ prod.snd) ≫ q := by
    simpa [Category.assoc] using congrArg (· ≫ prod.snd) w
  have hy : a.left ≫ G.target ≫ e.inv ≫ q = (b.left ≫ prod.fst) ≫ q := by
    simpa [Category.assoc] using congrArg (· ≫ prod.fst) w
  refine Over.homMk (subgroupoidConjugate i e hi q hq a.left
    (b.left ≫ prod.snd) (b.left ≫ prod.fst) hx hy) ?_
  have hb : subgroupoidConjugate i e hi q hq a.left
      (b.left ≫ prod.snd) (b.left ≫ prod.fst) hx hy ≫
      subgroupoidArrowBase G H e = b.left := by
    apply prod.hom_ext
    · simp [subgroupoidConjugate_target]
    · simp [subgroupoidConjugate_source]
  change _ ≫ (subgroupoidArrowBase G H e ≫ prod.map q q) = T.hom
  rw [← Category.assoc, hb]
  exact Over.w b

private noncomputable def subgroupoidTransport {S : Scheme.{u}}
    {G H : GroupoidScheme S} (i : GroupoidScheme.Hom H G)
    (e : H.objects ≅ G.objects) (hi : i.mapObjects = e.hom)
    {Q : Over S} (q : H.objects ⟶ Q) (hq : IsPullback H.target H.source q q) :
    DescentTransport (Over.homMk (subgroupoidArrowBase G H e) :
      Over.mk (subgroupoidArrowBase G H e ≫ prod.map q q) ⟶ Over.mk (prod.map q q)) where
  move := subgroupoidMove i e hi q hq
  base a b := by
    apply Over.OverMorphism.ext
    apply prod.hom_ext
    · simp [subgroupoidMove, subgroupoidConjugate_target]
    · simp [subgroupoidMove, subgroupoidConjugate_source]
  refl a := by
    apply Over.OverMorphism.ext
    simpa [subgroupoidMove] using subgroupoidConjugate_refl i e hi q hq a.left
  trans a b c := by
    apply Over.OverMorphism.ext
    have w := (Over.w a).trans (Over.w b).symm
    have w' := (Over.w b).trans (Over.w c).symm
    have hx : (b.left ≫ prod.snd) ≫ q = (c.left ≫ prod.snd) ≫ q := by
      simpa using congrArg (· ≫ prod.snd) w'
    have hy : (b.left ≫ prod.fst) ≫ q = (c.left ≫ prod.fst) ≫ q := by
      simpa using congrArg (· ≫ prod.fst) w'
    dsimp [subgroupoidMove, Over.homMk, CostructuredArrow.homMk]
    refine subgroupoidConjugate_trans i e hi q hq a.left _ _ _ _
      (by simpa [Category.assoc] using congrArg (· ≫ prod.snd) w)
      (by simpa [Category.assoc] using congrArg (· ≫ prod.fst) w) hx hy ?_ ?_
    · simpa only [Category.assoc, reassoc_of% subgroupoidConjugate_source] using hx
    · simpa only [Category.assoc, reassoc_of% subgroupoidConjugate_target] using hy
  naturality f a b := by
    apply Over.OverMorphism.ext
    have w := (Over.w a).trans (Over.w b).symm
    have hx := congrArg (· ≫ prod.snd) w
    have hy := congrArg (· ≫ prod.fst) w
    dsimp [subgroupoidMove, Over.homMk, CostructuredArrow.homMk]
    apply subgroupoidConjugate_precomp i e hi q hq
    · simpa [Category.assoc] using hx
    · simpa [Category.assoc] using hy
    · simpa [Category.assoc] using congrArg (f.left ≫ ·) hx
    · simpa [Category.assoc] using congrArg (f.left ≫ ·) hy

private lemma exists_effectiveTransport {S : Scheme.{u}} {R X B : Over S}
    (p : R ⟶ X) (f : X ⟶ B)
    (d : DescentTransport (Over.homMk p : Over.mk (p ≫ f) ⟶ Over.mk f))
    (hcover : Presieve.ofArrows (fun _ : Unit ↦ X.left) (fun _ ↦ f.left) ∈
      Scheme.fppfPrecoverage B.left)
    [IsSeparated p.left] [LocallyOfFiniteType p.left] [LocallyQuasiFinite p.left] :
    ∃ (Y : Over S) (j : Y ⟶ B) (r : R ⟶ Y), IsPullback r p j f ∧
      ∀ {T : Over B} (a : T ⟶ Over.mk (p ≫ f)) (b : T ⟶ Over.mk f),
        (d.move a b).left ≫ r = a.left ≫ r := by
  let E := Over.iteratedSliceEquiv B
  let d' : DescentTransport (AlgebraicGeometry.structureMap f.left (Over.mk p.left)) :=
    d.mapRightAdjoint E.symm.toAdjunction
  let D := transportDescentData f.left (Over.mk p.left) d'
  obtain ⟨Y, ⟨e⟩⟩ :=
    AlgebraicGeometry.DescentData.isFamilyEffective_of_forall_isSeparated_of_locallyQuasiFinite
      (fun _ : Unit ↦ f.left) hcover D
      (fun _ ↦ show IsSeparated p.left from inferInstance)
      (fun _ ↦ show LocallyQuasiFinite p.left from inferInstance)
      (fun _ ↦ show LocallyOfFiniteType p.left from inferInstance)
  let z := effectiveProjection f.left (Over.mk p.left) d' Y e
  let r : R ⟶ (Over.map B.hom).obj Y := Over.homMk z.left (by
    change z.left ≫ Y.hom ≫ B.hom = R.hom
    rw [← Category.assoc, Over.w z]
    change (p.left ≫ f.left) ≫ B.hom = R.hom
    rw [Category.assoc, Over.w f, Over.w p])
  let j : (Over.map B.hom).obj Y ⟶ B := Over.homMk Y.hom
  refine ⟨_, j, r, ?_, ?_⟩
  · apply IsPullback.of_map (Over.forget S) _
    · exact effectiveProjection_isPullback f.left (Over.mk p.left) d' Y e
    · apply Over.OverMorphism.ext
      exact Over.w z
  · intro T a b
    have h := effectiveProjection_move f.left (Over.mk p.left) d' Y e
      (E.functor.map a) (E.functor.map b)
    have hmap := DescentTransport.mapRightAdjoint_move_map E.symm.toAdjunction d a b
    change d'.move (E.functor.map a) (E.functor.map b) = E.functor.map (d.move a b) at hmap
    rw [hmap] at h
    apply Over.OverMorphism.ext
    exact congrArg (fun k : E.functor.obj T ⟶ Y ↦ k.left) h


private lemma conjugationEquiv_id {S : Scheme.{u}} {G H : GroupoidScheme S}
    (i : GroupoidScheme.Hom H G) {Q : Over S} (q : H.objects ⟶ Q)
    (hq : IsPullback H.target H.source q q) {T : Over S}
    (x y : H.Evaluation T) (h : x ≫ q = y ≫ q) :
    conjugationEquiv i q hq x x y y h h (𝟙 _) = 𝟙 _ := by
  simp [conjugationEquiv, Iso.homCongr_apply]

private lemma conjugationEquiv_inv {S : Scheme.{u}} {G H : GroupoidScheme S}
    (i : GroupoidScheme.Hom H G) {Q : Over S} (q : H.objects ⟶ Q)
    (hq : IsPullback H.target H.source q q) {T : Over S}
    (x y x' y' : H.Evaluation T) (hx : x ≫ q = x' ≫ q) (hy : y ≫ q = y' ≫ q)
    (a : (i.evaluation T).obj x ⟶ (i.evaluation T).obj y) :
    conjugationEquiv i q hq y x y' x' hy hx (Groupoid.inv a) =
      Groupoid.inv (conjugationEquiv i q hq x y x' y' hx hy a) := by
  simp [conjugationEquiv, Iso.homCongr_apply, Groupoid.inv_eq_inv]

private noncomputable def evaluatedArrow {S : Scheme.{u}} {G H : GroupoidScheme S}
    (i : GroupoidScheme.Hom H G) (e : H.objects ≅ G.objects) (hi : i.mapObjects = e.hom)
    {T : Over S} (r : T ⟶ G.arrows) {x y : H.Evaluation T}
    (hx : r ≫ G.source ≫ e.inv = x) (hy : r ≫ G.target ≫ e.inv = y) :
    (i.evaluation T).obj x ⟶ (i.evaluation T).obj y where
  arrow := r
  source_eq := by change r ≫ G.source = x ≫ i.mapObjects; simp [← hx, hi]
  target_eq := by change r ≫ G.target = y ≫ i.mapObjects; simp [← hy, hi]

private lemma conjugation_operation_relations {S : Scheme.{u}} {G H : GroupoidScheme S}
    (i : GroupoidScheme.Hom H G) (e : H.objects ≅ G.objects) (hi : i.mapObjects = e.hom)
    {Q A : Over S} (q : H.objects ⟶ Q) (hq : IsPullback H.target H.source q q)
    (r : G.arrows ⟶ A) (s t : A ⟶ Q)
    (hp : IsPullback r (prod.lift G.target G.source) (prod.lift t s)
      (prod.map (e.inv ≫ q) (e.inv ≫ q)))
    (htransport : ∀ {T : Over S} (x y x' y' : H.Evaluation T)
      (hx : x ≫ q = x' ≫ q) (hy : y ≫ q = y' ≫ q)
      (a : (i.evaluation T).obj x ⟶ (i.evaluation T).obj y),
      (conjugationEquiv i q hq x y x' y' hx hy a).arrow ≫ r = a.arrow ≫ r) :
    (∀ {T : Over S} (x y : T ⟶ G.objects), x ≫ (e.inv ≫ q) = y ≫ (e.inv ≫ q) →
      x ≫ G.identity ≫ r = y ≫ G.identity ≫ r) ∧
    (∀ {T : Over S} (a b : T ⟶ G.arrows), a ≫ r = b ≫ r →
      a ≫ G.inverse ≫ r = b ≫ G.inverse ≫ r) ∧
    (∀ {T : Over S} (a b c d : T ⟶ G.arrows)
      (w : a ≫ G.source = b ≫ G.target) (w' : c ≫ G.source = d ≫ G.target),
      a ≫ r = c ≫ r → b ≫ r = d ≫ r → G.compose a b w ≫ r = G.compose c d w' ≫ r) := by
  have hs : r ≫ s = G.source ≫ e.inv ≫ q := by simpa using congrArg (· ≫ prod.snd) hp.w
  have ht : r ≫ t = G.target ≫ e.inv ≫ q := by simpa using congrArg (· ≫ prod.fst) hp.w
  have hqs {T : Over S} (a b : T ⟶ G.arrows) (h : a ≫ r = b ≫ r) :
      (a ≫ G.source ≫ e.inv) ≫ q = (b ≫ G.source ≫ e.inv) ≫ q := by
    simpa [Category.assoc, hs] using congrArg (· ≫ s) h
  have hqt {T : Over S} (a b : T ⟶ G.arrows) (h : a ≫ r = b ≫ r) :
      (a ≫ G.target ≫ e.inv) ≫ q = (b ≫ G.target ≫ e.inv) ≫ q := by
    simpa [Category.assoc, ht] using congrArg (· ≫ t) h
  refine ⟨?_, ?_, ?_⟩
  · intro T x y hxy
    have hw : (x ≫ e.inv) ≫ q = (y ≫ e.inv) ≫ q := by simpa only [Category.assoc] using hxy
    have h := htransport (x ≫ e.inv) (x ≫ e.inv) (y ≫ e.inv) (y ≫ e.inv) hw hw (𝟙 _)
    rw [conjugationEquiv_id] at h
    change (((y ≫ e.inv) ≫ i.mapObjects) ≫ G.identity) ≫ r =
      (((x ≫ e.inv) ≫ i.mapObjects) ≫ G.identity) ≫ r at h
    simpa [hi, Category.assoc] using h.symm
  · intro T a b hab
    let aa := evaluatedArrow i e hi a rfl rfl
    let bb := evaluatedArrow i e hi b rfl rfl
    have hx := hqs a b hab
    have hy := hqt a b hab
    have hc : conjugationEquiv i q hq _ _ _ _ hx hy aa = bb :=
      evaluationHom_eq_of_image_eq hp _ _ ((htransport _ _ _ _ hx hy aa).trans hab)
    have h := htransport _ _ _ _ hy hx (Groupoid.inv aa)
    rw [conjugationEquiv_inv, hc] at h
    change (b ≫ G.inverse) ≫ r = (a ≫ G.inverse) ≫ r at h
    simpa only [Category.assoc] using h.symm
  · intro T a b c d w w' hac hbd
    let aa := evaluatedArrow i e hi a rfl rfl
    let cc := evaluatedArrow i e hi c rfl rfl
    let bb := evaluatedArrow i e hi b (y := a ≫ G.source ≫ e.inv) rfl (by simp [← w])
    let dd := evaluatedArrow i e hi d (y := c ≫ G.source ≫ e.inv) rfl (by simp [← w'])
    have hx := hqs b d hbd
    have hy := hqs a c hac
    have hz := hqt a c hac
    have hA : conjugationEquiv i q hq _ _ _ _ hy hz aa = cc :=
      evaluationHom_eq_of_image_eq hp _ _ ((htransport _ _ _ _ hy hz aa).trans hac)
    have hB : conjugationEquiv i q hq _ _ _ _ hx hy bb = dd :=
      evaluationHom_eq_of_image_eq hp _ _ ((htransport _ _ _ _ hx hy bb).trans hbd)
    have h := htransport _ _ _ _ hx hz (bb ≫ aa)
    rw [conjugationEquiv_comp i q hq _ _ _ _ _ _ hx hy hz bb aa, hA, hB] at h
    exact h.symm


attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc

/-- The descended operations of `G` along `q` form a groupoid scheme `K` on `Q`, and `q, r` form a
morphism `G ⟶ K` that is fully faithful on generalized points. If moreover `i : H ⟶ G` is a
subgroupoid on the same object scheme whose pre-relation is the kernel pair of `q` and whose
arrows go to identities of `K`, then `H` is exactly the part of `G` over the identity of `K`. -/
private lemma DescendedOperations.exists_groupoid_isPullback_identity
    {S : Scheme.{u}} {G : GroupoidScheme S}
    {Q A : Over S} {q : G.objects ⟶ Q} {r : G.arrows ⟶ A} {s t : A ⟶ Q}
    (D : DescendedOperations G q r s t)
    (hp : IsPullback r (prod.lift G.target G.source) (prod.lift t s) (prod.map q q))
    {J : GrothendieckTopology (Over S)} [J.Subcanonical] (hq : SingletonCover J q)
    {H : GroupoidScheme S} (i : GroupoidScheme.Hom H G) [IsIso i.mapObjects]
    (hqH : IsPullback H.target H.source (i.mapObjects ≫ q) (i.mapObjects ≫ q))
    (hwH : i.mapArrows ≫ r = (H.source ≫ i.mapObjects ≫ q) ≫ D.identity) :
    ∃ (K : GroupoidScheme S) (he : K.objects = Q) (F : GroupoidScheme.Hom G K),
      F.mapObjects = q ≫ eqToHom he.symm ∧
        (∀ T : Over S, Nonempty (F.evaluation T).FullyFaithful) ∧
        IsPullback i.mapArrows (H.source ≫ i.mapObjects ≫ F.mapObjects)
          F.mapArrows K.identity := by
  have hs : r ≫ s = G.source ≫ q := by simpa using congrArg (· ≫ prod.snd) hp.w
  have ht : r ≫ t = G.target ≫ q := by simpa using congrArg (· ≫ prod.fst) hp.w
  obtain ⟨hids, hidt, hinvs, hinvt, hcs, hct⟩ := D.structure_maps hp hq
  have hinvmap {T : Over S} (f : T ⟶ G.arrows) :
      (f ≫ G.inverse) ≫ r = (f ≫ r) ≫ D.inverse := by
    simp [Category.assoc, D.inverse_map]
  have hleft : ∀ (T : Over S) (a : T ⟶ A)
      (w : (a ≫ t ≫ D.identity) ≫ s = a ≫ t),
      pullback.lift (a ≫ t ≫ D.identity) a w ≫ D.comp = a := by
    intro T a w
    obtain ⟨W, p, f, hp', hf⟩ := exists_local_arrow hp hq a
    let : EffectiveEpi p := hp'.effectiveEpi
    have hfi : (f ≫ G.target ≫ G.identity) ≫ r = p ≫ a ≫ t ≫ D.identity := by
      simp only [Category.assoc, ← D.identity_map, ← reassoc_of% ht, ← reassoc_of% hf]
    have wf : (f ≫ G.target ≫ G.identity) ≫ G.source = f ≫ G.target := by
      simp [Category.assoc, G.source_identity]
    apply (cancel_epi p).mp
    rw [D.local_comp p _ a (f ≫ G.target ≫ G.identity) f w wf hfi hf]
    simpa only [GroupoidScheme.compose, G.left_identity] using hf
  have hright : ∀ (T : Over S) (a : T ⟶ A)
      (w : a ≫ s = (a ≫ s ≫ D.identity) ≫ t),
      pullback.lift a (a ≫ s ≫ D.identity) w ≫ D.comp = a := by
    intro T a w
    obtain ⟨W, p, f, hp', hf⟩ := exists_local_arrow hp hq a
    let : EffectiveEpi p := hp'.effectiveEpi
    have hfi : (f ≫ G.source ≫ G.identity) ≫ r = p ≫ a ≫ s ≫ D.identity := by
      simp only [Category.assoc, ← D.identity_map, ← reassoc_of% hs, ← reassoc_of% hf]
    have wf : f ≫ G.source = (f ≫ G.source ≫ G.identity) ≫ G.target := by
      simp [Category.assoc, G.target_identity]
    apply (cancel_epi p).mp
    rw [D.local_comp p a _ f (f ≫ G.source ≫ G.identity) w wf hf hfi]
    simpa only [GroupoidScheme.compose, G.right_identity] using hf
  have hleftinv : ∀ (T : Over S) (a : T ⟶ A)
      (w : (a ≫ D.inverse) ≫ s = a ≫ t),
      pullback.lift (a ≫ D.inverse) a w ≫ D.comp = a ≫ s ≫ D.identity := by
    intro T a w
    obtain ⟨W, p, f, hp', hf⟩ := exists_local_arrow hp hq a
    let : EffectiveEpi p := hp'.effectiveEpi
    have hfi : (f ≫ G.inverse) ≫ r = p ≫ a ≫ D.inverse := by rw [hinvmap, hf, Category.assoc]
    have wf : (f ≫ G.inverse) ≫ G.source = f ≫ G.target := by
      simp [Category.assoc, G.source_inverse]
    apply (cancel_epi p).mp
    rw [D.local_comp p _ a (f ≫ G.inverse) f w wf hfi hf]
    simp only [GroupoidScheme.compose, G.left_inverse]
    simp only [Category.assoc, ← D.identity_map, ← reassoc_of% hs, ← reassoc_of% hf]
  have hrightinv : ∀ (T : Over S) (a : T ⟶ A)
      (w : a ≫ s = (a ≫ D.inverse) ≫ t),
      pullback.lift a (a ≫ D.inverse) w ≫ D.comp = a ≫ t ≫ D.identity := by
    intro T a w
    obtain ⟨W, p, f, hp', hf⟩ := exists_local_arrow hp hq a
    let : EffectiveEpi p := hp'.effectiveEpi
    have hfi : (f ≫ G.inverse) ≫ r = p ≫ a ≫ D.inverse := by rw [hinvmap, hf, Category.assoc]
    have wf : f ≫ G.source = (f ≫ G.inverse) ≫ G.target := by
      simp [Category.assoc, G.target_inverse]
    apply (cancel_epi p).mp
    rw [D.local_comp p a _ f (f ≫ G.inverse) w wf hf hfi]
    simp only [GroupoidScheme.compose, G.right_inverse]
    simp only [Category.assoc, ← D.identity_map, ← reassoc_of% ht, ← reassoc_of% hf]
  have hassoc : ∀ (T : Over S) (a b c : T ⟶ A)
      (wab : a ≫ s = b ≫ t) (wbc : b ≫ s = c ≫ t)
      (w₁ : (pullback.lift a b wab ≫ D.comp) ≫ s = c ≫ t)
      (w₂ : a ≫ s = (pullback.lift b c wbc ≫ D.comp) ≫ t),
      pullback.lift (pullback.lift a b wab ≫ D.comp) c w₁ ≫ D.comp =
        pullback.lift a (pullback.lift b c wbc ≫ D.comp) w₂ ≫ D.comp := by
    intro T a b c wab wbc w₁ w₂
    obtain ⟨W, p, f, g, h, hp', wfg, wgh, hf, hg, hh⟩ := exists_local_triple hp hq a b c wab wbc
    let : EffectiveEpi p := hp'.effectiveEpi
    have hfg := (D.local_comp p a b f g wab wfg hf hg).symm
    have hgh := (D.local_comp p b c g h wbc wgh hg hh).symm
    have wfgh : G.compose f g wfg ≫ G.source = h ≫ G.target := by
      simpa [GroupoidScheme.compose, Category.assoc, G.source_comp] using wgh
    have wfgh' : f ≫ G.source = G.compose g h wgh ≫ G.target := by
      simpa [GroupoidScheme.compose, Category.assoc, G.target_comp] using wfg
    apply (cancel_epi p).mp
    rw [D.local_comp p _ c (G.compose f g wfg) h w₁ wfgh hfg hh,
      D.local_comp p a _ f (G.compose g h wgh) w₂ wfgh' hf hgh]
    exact congrArg (· ≫ r) (G.assoc W f g h wfg wgh wfgh wfgh')
  let K : GroupoidScheme S :=
    { objects := Q, arrows := A, source := s, target := t,
      comp := D.comp, identity := D.identity, inverse := D.inverse,
      source_identity := hids, target_identity := hidt,
      source_inverse := hinvs, target_inverse := hinvt,
      source_comp := hcs, target_comp := hct,
      left_identity := hleft, right_identity := hright,
      left_inverse := hleftinv, right_inverse := hrightinv, assoc := hassoc }
  let F : GroupoidScheme.Hom G K :=
    { mapObjects := q, mapArrows := r, map_source := hs, map_target := ht,
      map_identity := D.identity_map, map_comp := fun _ ↦ D.comp_map }
  exact ⟨K, rfl, F, by simp [F], fun T ↦ evaluation_fullyFaithful_of_isPullback F hp T,
    Stacks.Groupoids.GroupoidScheme.isPullback_identity_of_isPullback_restriction F i hp hqH hwH⟩


private lemma surjective_prod_map {S : Scheme.{u}} {X X' Y Y' : Over S}
    (f : X ⟶ X') (g : Y ⟶ Y') [Surjective f.left] [Surjective g.left] :
    Surjective (prod.map f g).left := by
  let : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) :=
    ⟨fun _ _ hf hg ↦ by
      let := hf
      let := hg
      infer_instance⟩
  let p := pullback.map X.hom Y.hom X'.hom Y'.hom f.left g.left (𝟙 S)
    (by simp) (by simp)
  have hp : Surjective p := MorphismProperty.pullbackMap
    (P := @Surjective) inferInstance inferInstance (Over.w f).symm (Over.w g).symm
  rw [prod_map_left_eq]
  let := hp
  infer_instance

private lemma singletonCover_of_isIso {C : Type*} [Category C]
    (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y) [IsIso f] : SingletonCover J f := by
  rw [SingletonCover, ← Sieve.generateSingleton_eq]
  simp

private lemma exists_groupoid_division {S : Scheme.{u}} {G H : GroupoidScheme S}
    (i : GroupoidScheme.Hom H G) (e : H.objects ≅ G.objects) (hi : i.mapObjects = e.hom)
    {Q : Over S} (q : H.objects ⟶ Q) (hq : IsPullback H.target H.source q q)
    [Stacks.Morphisms.IsFiniteLocallyFree q.left] [Surjective q.left]
    (hqcover : SingletonCover (Scheme.fppfTopology.over S) q)
    [IsSeparated (prod.lift G.target G.source).left]
    [LocallyOfFiniteType (prod.lift G.target G.source).left]
    [LocallyQuasiFinite (prod.lift G.target G.source).left] :
    ∃ (K : GroupoidScheme S) (he : K.objects = Q) (F : GroupoidScheme.Hom G K),
      F.mapObjects = (e.inv ≫ q) ≫ eqToHom he.symm ∧
        (∀ T : Over S, Nonempty (F.evaluation T).FullyFaithful) ∧
        IsPullback i.mapArrows (H.source ≫ q ≫ eqToHom he.symm)
          F.mapArrows K.identity := by
  let p := subgroupoidArrowBase G H e
  let f := prod.map q q
  have hp_eq : p = prod.lift G.target G.source ≫ prod.map e.inv e.inv := by
    apply prod.hom_ext <;> simp [p]
  have : IsIso (prod.map e.inv e.inv).left :=
    (Over.forget S).map_isIso (prod.map e.inv e.inv)
  have : IsSeparated p.left := by rw [hp_eq]; change IsSeparated (_ ≫ _); infer_instance
  have : LocallyOfFiniteType p.left := by
    rw [hp_eq]
    change LocallyOfFiniteType (_ ≫ _)
    infer_instance
  have : LocallyQuasiFinite p.left := by
    rw [hp_eq]
    change LocallyQuasiFinite (_ ≫ _)
    infer_instance
  have : Stacks.Morphisms.IsFiniteLocallyFree f.left := finiteLocallyFree_prod_map q q
  have : Surjective f.left := surjective_prod_map q q
  have := Stacks.Morphisms.IsFiniteLocallyFree.flat f.left
  have := Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation f.left
  have hfcover : Presieve.ofArrows (fun _ : Unit ↦ (H.objects ⨯ H.objects).left)
      (fun _ ↦ f.left) ∈ Scheme.fppfPrecoverage (Q ⨯ Q).left := by
    simpa only [Presieve.ofArrows_pUnit] using f.left.singleton_mem_fppfPrecoverage
  obtain ⟨A, j, r, hpb, hr⟩ := exists_effectiveTransport p f
    (subgroupoidTransport i e hi q hq) hfcover
  let sb := j ≫ prod.snd
  let tb := j ≫ prod.fst
  have hp' : IsPullback r (prod.lift G.target G.source) (prod.lift tb sb)
      (prod.map (e.inv ≫ q) (e.inv ≫ q)) := by
    have he' : j = prod.lift tb sb := by apply prod.hom_ext <;> simp [tb, sb]
    exact hpb.of_iso (Iso.refl _) (Iso.refl _) (prod.mapIso e e) (Iso.refl _)
      (by simp) (by apply prod.hom_ext <;> simp [p]) (by simp [he'])
      (by apply prod.hom_ext <;> simp [f])
  have hconj {T : Over S} (a : T ⟶ G.arrows) (x y : T ⟶ H.objects)
      (hx : a ≫ G.source ≫ e.inv ≫ q = x ≫ q)
      (hy : a ≫ G.target ≫ e.inv ≫ q = y ≫ q) :
      subgroupoidConjugate i e hi q hq a x y hx hy ≫ r = a ≫ r := by
    let T' : Over (Q ⨯ Q) := Over.mk (a ≫ p ≫ f)
    let aa : T' ⟶ Over.mk (p ≫ f) := Over.homMk a
    let bb : T' ⟶ Over.mk f := Over.homMk (prod.lift y x) (by
      apply prod.hom_ext <;> simp [T', p, f, Category.assoc, hx, hy])
    have h := hr aa bb
    simpa [subgroupoidTransport, subgroupoidMove, aa, bb] using h
  have htransport {T : Over S} (x y x' y' : H.Evaluation T)
      (hx : x ≫ q = x' ≫ q) (hy : y ≫ q = y' ≫ q)
      (a : (i.evaluation T).obj x ⟶ (i.evaluation T).obj y) :
      (conjugationEquiv i q hq x y x' y' hx hy a).arrow ≫ r = a.arrow ≫ r := by
    rcases a with ⟨a, has, hat⟩
    have hsx : a ≫ G.source ≫ e.inv = x := by
      rw [← Category.assoc, has]
      change (x ≫ i.mapObjects) ≫ e.inv = x
      simp [hi]
    have hty : a ≫ G.target ≫ e.inv = y := by
      rw [← Category.assoc, hat]
      change (y ≫ i.mapObjects) ≫ e.inv = y
      simp [hi]
    subst x
    subst y
    exact hconj a x' y'
      (by simpa only [Category.assoc] using hx)
      (by simpa only [Category.assoc] using hy)
  -- The subgroupoid's arrows become identities after descent.  Conjugating the identity at
  -- `x` by the unique arrow of the subgroupoid from `x` to `y` -- unique because the
  -- subgroupoid is the kernel pair of `q` -- produces the arrow of the subgroupoid itself, and
  -- conjugate arrows have the same image under `r`.
  have hcore : i.mapArrows ≫ r = H.source ≫ i.mapObjects ≫ G.identity ≫ r := by
    have hss : (H.source : H.Evaluation H.arrows) ≫ q = (H.source : H.Evaluation H.arrows) ≫ q :=
      rfl
    have hst : (H.source : H.Evaluation H.arrows) ≫ q = (H.target : H.Evaluation H.arrows) ≫ q :=
      hq.w.symm
    have h := htransport (H.source : H.Evaluation H.arrows) H.source H.source H.target hss hst
      (𝟙 ((i.evaluation H.arrows).obj (H.source : H.Evaluation H.arrows)))
    rw [conjugationEquiv_apply] at h
    have hidinv : Groupoid.inv
        (kernelPairArrow H q hq (H.source : H.Evaluation H.arrows) H.source hss) = 𝟙 _ :=
      kernelPair_hom_ext H q hq _ _
    have hkp : kernelPairArrow H q hq (H.source : H.Evaluation H.arrows) H.target hst =
        pointHom (H.source : H.Evaluation H.arrows) H.target (𝟙 H.arrows)
          (Category.id_comp _) (Category.id_comp _) :=
      kernelPair_hom_ext H q hq _ _
    rw [hidinv, hkp] at h
    simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
    have h₂ : (𝟙 H.arrows ≫ i.mapArrows) ≫ r =
        ((H.source ≫ i.mapObjects) ≫ G.identity) ≫ r := h
    simpa only [Category.id_comp, Category.assoc] using h₂
  obtain ⟨hident, hinv, hcomp⟩ := conjugation_operation_relations i e hi q hq r sb tb hp' htransport
  have hq' := (singletonCover_of_isIso (Scheme.fppfTopology.over S) e.inv).comp hqcover
  obtain ⟨D⟩ := exists_descendedOperations (e.inv ≫ q) r sb tb hp' hq' hident hinv hcomp
  have : IsIso i.mapObjects := by rw [hi]; infer_instance
  have hmapq : i.mapObjects ≫ e.inv ≫ q = q := by
    rw [hi, ← Category.assoc, e.hom_inv_id, Category.id_comp]
  have hqH : IsPullback H.target H.source (i.mapObjects ≫ e.inv ≫ q)
      (i.mapObjects ≫ e.inv ≫ q) := by
    simpa only [hmapq] using hq
  have hwH : i.mapArrows ≫ r =
      (H.source ≫ i.mapObjects ≫ e.inv ≫ q) ≫ D.identity := by
    rw [hcore]
    calc H.source ≫ i.mapObjects ≫ G.identity ≫ r
        = H.source ≫ i.mapObjects ≫ (e.inv ≫ q) ≫ D.identity := by rw [D.identity_map]
      _ = (H.source ≫ i.mapObjects ≫ e.inv ≫ q) ≫ D.identity := by
          simp only [Category.assoc]
  obtain ⟨K, he, F, hFobj, hFF, hFid⟩ :=
    DescendedOperations.exists_groupoid_isPullback_identity D hp' hq' i hqH hwH
  refine ⟨K, he, F, hFobj, hFF, ?_⟩
  have hFq : i.mapObjects ≫ F.mapObjects = q ≫ eqToHom he.symm := by
    rw [hFobj, ← Category.assoc, hmapq]
  simpa only [hFq] using hFid

/-- The canonical data obtained by dividing a groupoid scheme by a finite locally free
subgroupoid equivalence relation. -/
structure Division {S : Scheme.{u}} (G H : GroupoidScheme S)
    (i : GroupoidScheme.Hom H G) (hobj : H.objects = G.objects) where
  /-- The affine quotient of the object scheme. -/
  quotient : Over S
  quotient_affine : IsAffine quotient.left
  /-- The quotient morphism. -/
  projection : G.objects ⟶ quotient
  projection_finiteLocallyFree : Stacks.Morphisms.IsFiniteLocallyFree projection.left
  projection_surjective : Surjective projection.left
  /-- The quotient map identifies arrows of the subgroupoid. -/
  projection_eq : H.source ≫ eqToHom hobj ≫ projection =
    H.target ≫ eqToHom hobj ≫ projection
  /-- The quotient represents the fppf sheaf quotient: it is the coequalizer of
  source and target among fppf sheaves. -/
  quotient_universal :
    ∀ (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
      (a : (Scheme.fppfTopology.over S).yoneda.obj H.objects ⟶ F),
      ((Scheme.fppfTopology.over S).yoneda.map H.source ≫ a =
        (Scheme.fppfTopology.over S).yoneda.map H.target ≫ a) →
      ∃! b : (Scheme.fppfTopology.over S).yoneda.obj quotient ⟶ F,
        (Scheme.fppfTopology.over S).yoneda.map
          (eqToHom hobj ≫ projection) ≫ b = a
  /-- The subgroupoid is the kernel pair of the quotient map. -/
  subgroupoid_isPullback :
    IsPullback (H.target ≫ eqToHom hobj) (H.source ≫ eqToHom hobj)
      projection projection
  /-- The descended groupoid on the quotient. -/
  descended : GroupoidScheme S
  descended_objects : descended.objects = quotient
  /-- The original groupoid maps to the descended groupoid. -/
  descend : GroupoidScheme.Hom G descended
  descend_objects : descend.mapObjects = projection ≫ eqToHom descended_objects.symm
  /-- The original groupoid is the restriction of the descended groupoid. -/
  descend_fullyFaithful : ∀ T : Over S, Nonempty (descend.evaluation T).FullyFaithful
  /-- The subgroupoid is exactly the part of the ambient arrow scheme which lies over the
  identity of the descended groupoid. -/
  descend_isPullback_identity :
    IsPullback i.mapArrows (H.source ≫ eqToHom hobj ≫ descend.mapObjects)
      descend.mapArrows descended.identity

/-- A finite locally free subgroupoid equivalence relation on an affine scheme can be
divided out, and a separated locally quasi-finite ambient groupoid descends to the quotient. -/
@[stacks 04S4 "all four conclusions: the affine quotient Ū = U/P as the fppf-sheaf \
coequalizer, its finite locally free surjective quotient map, the kernel-pair square \
P = U ×_Ū U, and the descent of the ambient groupoid R to a groupoid on Ū of which it \
is the restriction"]
theorem exists_division {S : Scheme.{u}} (G H : GroupoidScheme S)
    (i : GroupoidScheme.Hom H G) (hobj : H.objects = G.objects)
    (hiobj : i.mapObjects = eqToHom hobj)
    [Mono i.mapArrows]
    [Stacks.Morphisms.IsFiniteLocallyFree H.source.left]
    [Stacks.Morphisms.IsFiniteLocallyFree H.target.left]
    [Mono (prod.lift H.target H.source)]
    [IsAffine G.objects.left]
    [IsSeparated (prod.lift G.target G.source).left]
    [LocallyOfFiniteType (prod.lift G.target G.source).left]
    [LocallyQuasiFinite (prod.lift G.target G.source).left] :
    Nonempty (Division G H i hobj) := by
  classical
  let : IsAffine H.objects.left := by
    rw [hobj]
    infer_instance
  let : IsAffine H.arrows.left :=
    AlgebraicGeometry.isAffine_arrows_of_isFiniteLocallyFree_source H
  let : Mono (groupoidPreRelation H) := inferInstanceAs (Mono (prod.lift H.target H.source))
  let : IsEquivalenceRelation H.target H.source :=
    AlgebraicGeometry.isEquivalenceRelation_of_mono_groupoidPreRelation H
  let Q := quotientOver H
  let π : G.objects ⟶ Q := eqToHom hobj.symm ≫ quotientProjection H
  let : IsIso ((eqToHom hobj.symm).left) := by
    change IsIso ((Over.forget S).map (eqToHom hobj.symm))
    exact Functor.map_isIso (Over.forget S) (eqToHom hobj.symm)
  let : Stacks.Morphisms.IsFiniteLocallyFree (eqToHom hobj.symm).left :=
    finiteLocallyFree_of_isIso (eqToHom hobj.symm).left
  let : Stacks.Morphisms.IsFiniteLocallyFree (quotientProjection H).left := by
    rw [quotientProjection_left]
    exact objectsToInvariantSpectrum_isFiniteLocallyFree H
  have hπ : Stacks.Morphisms.IsFiniteLocallyFree π.left := by
    change Stacks.Morphisms.IsFiniteLocallyFree
      ((eqToHom hobj.symm).left ≫ (quotientProjection H).left)
    exact inferInstance
  let qH := quotientProjection H
  have hqHcomm : H.target ≫ qH = H.source ≫ qH := by
    apply Over.OverMorphism.ext
    change H.target.left ≫ objectsToInvariantSpectrum H =
      H.source.left ≫ objectsToInvariantSpectrum H
    exact (isPullback_objectsToInvariantSpectrum H).w
  have hqHpb : IsPullback H.target H.source qH qH :=
    (isPullback_objectsToInvariantSpectrum H).of_map (Over.forget S) hqHcomm
  have hk' : IsIso (pullback.lift H.target H.source hqHcomm) := by
    let e := hqHpb.isoIsPullback H.objects H.objects (IsPullback.of_hasPullback qH qH)
    have he : e.hom = pullback.lift H.target H.source hqHcomm := by
      apply pullback.hom_ext <;> simp [e]
    rw [← he]
    infer_instance
  let : Surjective qH.left := by
    change Surjective (objectsToInvariantSpectrum H)
    exact (surjective_iff _).2 (surjective_objectsToInvariantSpectrum H)
  have hqHcover : Sieve.generate (Presieve.singleton qH) ∈
      (Scheme.fppfTopology.over S) Q := by
    rw [GrothendieckTopology.mem_over_iff]
    change Sieve.functorPushforward (Over.forget S)
      (Sieve.generate (Presieve.singleton qH)) ∈ Scheme.fppfTopology Q.left
    rw [← Sieve.generate_map_eq_functorPushforward, Presieve.map_singleton]
    exact singleton_fppf_of_finiteLocallyFree qH.left
  have hquotientUniversal := quotient_universal_of_kernelPair
    (Scheme.fppfTopology.over S) H.target H.source qH hqHcomm hqHcover hk'
  have hqHproj : eqToHom hobj ≫ π = qH := by
    dsimp [π, qH]
    simp
  have hqHcover' : SingletonCover (Scheme.fppfTopology.over S) qH := by
    simpa only [SingletonCover, ← Sieve.generateSingleton_eq] using hqHcover
  obtain ⟨K, he, F, hF, hFF, hFid⟩ := exists_groupoid_division i (eqToIso hobj) hiobj
    qH hqHpb hqHcover'
  refine ⟨⟨Q, ?_, π, hπ, ?_, ?_, ?_, ?_, K, he, F, ?_, hFF, ?_⟩⟩
  · change IsAffine (quotientOver H).left
    rw [quotientOver_left]
    infer_instance
  · change Surjective ((eqToHom hobj.symm).left ≫ qH.left)
    infer_instance
  · apply Over.OverMorphism.ext
    -- The quotient map coequalizes the source and target of the subgroupoid.
    have hpull := isPullback_objectsToInvariantSpectrum H
    simpa [π, Q, Category.assoc, quotientProjection_left] using hpull.w.symm
  · intro F a ha
    obtain ⟨b, hb, huniq⟩ := hquotientUniversal F a ha.symm
    refine ⟨b, ?_, ?_⟩
    · simpa [hqHproj] using hb
    · intro b' hb'
      apply huniq
      simpa [hqHproj] using hb'
  · simpa [π, Q] using kernelPair_transport H hobj (quotientProjection H) hqHpb
  · simpa only [π, qH, eqToIso.inv] using hF
  · have hobjq : eqToHom hobj ≫ F.mapObjects = qH ≫ eqToHom he.symm := by
      rw [hF]
      simp [eqToIso.inv]
    simpa only [hobjq] using hFid

/-- A property respecting isomorphisms which holds for the quotient morphism holds for the map
on objects of the descent morphism, the two differing by the identification of the quotient with
the object scheme of the descended groupoid. -/
theorem Division.property_descend_mapObjects (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {S : Scheme.{u}} {G H : GroupoidScheme S} {i : GroupoidScheme.Hom H G}
    {hobj : H.objects = G.objects} (D : Division G H i hobj)
    (h : P D.projection.left) : P D.descend.mapObjects.left := by
  have he : D.descend.mapObjects.left =
      D.projection.left ≫ (eqToHom D.descended_objects.symm).left := by
    rw [D.descend_objects, Over.comp_left]
  let : IsIso (eqToHom D.descended_objects.symm).left :=
    (Over.forget S).map_isIso (eqToHom D.descended_objects.symm)
  rw [he, P.cancel_right_of_respectsIso]
  exact h

/-- The map on objects of the descent morphism is surjective. -/
theorem Division.surjective_descend_mapObjects {S : Scheme.{u}} {G H : GroupoidScheme S}
    {i : GroupoidScheme.Hom H G} {hobj : H.objects = G.objects} (D : Division G H i hobj) :
    Surjective D.descend.mapObjects.left :=
  D.property_descend_mapObjects (@Surjective) D.projection_surjective

/-- The map on objects of the descent morphism is flat, the quotient morphism being finite
locally free. -/
theorem Division.flat_descend_mapObjects {S : Scheme.{u}} {G H : GroupoidScheme S}
    {i : GroupoidScheme.Hom H G} {hobj : H.objects = G.objects} (D : Division G H i hobj) :
    Flat D.descend.mapObjects.left :=
  let : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  D.property_descend_mapObjects (@Flat)
    (@Stacks.Morphisms.IsFiniteLocallyFree.flat _ _ D.projection.left
      D.projection_finiteLocallyFree)

/-- The map on objects of the descent morphism is locally of finite presentation, the quotient
morphism being finite locally free. -/
theorem Division.locallyOfFinitePresentation_descend_mapObjects {S : Scheme.{u}}
    {G H : GroupoidScheme S} {i : GroupoidScheme.Hom H G} {hobj : H.objects = G.objects}
    (D : Division G H i hobj) : LocallyOfFinitePresentation D.descend.mapObjects.left :=
  let : MorphismProperty.RespectsIso
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  D.property_descend_mapObjects (@LocallyOfFinitePresentation)
    (@Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation _ _ D.projection.left
      D.projection_finiteLocallyFree)

/-- The map on objects of the descent morphism is quasi-compact, the quotient morphism being
finite. -/
theorem Division.quasiCompact_descend_mapObjects {S : Scheme.{u}} {G H : GroupoidScheme S}
    {i : GroupoidScheme.Hom H G} {hobj : H.objects = G.objects} (D : Division G H i hobj) :
    QuasiCompact D.descend.mapObjects.left :=
  let : MorphismProperty.RespectsIso (@QuasiCompact : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let : IsFinite D.projection.left :=
    @Stacks.Morphisms.IsFiniteLocallyFree.isFinite _ _ D.projection.left
      D.projection_finiteLocallyFree
  D.property_descend_mapObjects (@QuasiCompact) inferInstance

/-- **The identity of the quotient groupoid is an open immersion.**  If the arrow scheme of the
subgroupoid being divided out is an open subscheme of the ambient arrow scheme, then the identity
of the groupoid on the quotient is an open immersion.

The subgroupoid is the part of the ambient arrow scheme lying over the identity of the descended
groupoid, by `AlgebraicGeometry.GroupoidScheme.Division.descend_isPullback_identity`, and being
an open immersion descends along the surjective flat quasi-compact map on arrows. -/
theorem Division.isOpenImmersion_descended_identity {S : Scheme.{u}}
    {G H : GroupoidScheme S} {i : GroupoidScheme.Hom H G} {hobj : H.objects = G.objects}
    (D : Division G H i hobj) [IsOpenImmersion i.mapArrows.left] :
    IsOpenImmersion D.descended.identity.left := by
  let := D.surjective_descend_mapObjects
  let := D.flat_descend_mapObjects
  let := D.quasiCompact_descend_mapObjects
  exact Stacks.Groupoids.GroupoidScheme.isOpenImmersion_identity_of_isPullback_identity
    D.descend i D.descend_fullyFaithful D.descend_isPullback_identity

end AlgebraicGeometry.GroupoidScheme
