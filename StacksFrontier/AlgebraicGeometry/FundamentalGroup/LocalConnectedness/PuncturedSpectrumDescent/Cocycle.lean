module

public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.PuncturedSpectrumDescent.Gluing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Diagonal
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.SingleMorphismAction

/-!
# Descent data from gluing data on the literal fibre products

## Main definitions

* `AlgebraicGeometry.DescentDatum.ofPullbackIso`: the descent datum relative to `f` given by an
  isomorphism `V ×_S T₀ ≅ T₀ ×_S V` of the literal fibre products lying over `T₀ ×_S T₀` and
  satisfying the cocycle condition `(v · x) · y = v · y` on generalized points.
* `AlgebraicGeometry.DescentDatum.ofGluingIsoPullbackFstSnd`: the descent datum with gluing
  isomorphism `AlgebraicGeometry.gluingIsoPullbackFstSnd`.

## Main results

* `AlgebraicGeometry.eq_of_comp_eq_of_denseRange`: two morphisms over `B` into a scheme unramified
  and separated over `B` which agree on a dense subset of the source are equal.
* `AlgebraicGeometry.DescentDatum.actPullbackLaw_gluingIsoPullbackFstSnd`: the cocycle condition
  for `AlgebraicGeometry.gluingIsoPullbackFstSnd`.

## References

* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
* [Stacks Project, Tag 02GE](https://stacks.math.columbia.edu/tag/02GE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Stacks.Divisors
open Stacks.FundamentalGroup

universe u

namespace AlgebraicGeometry

/-! ### Agreement on a dense subset -/

/-- Let `p : Y ⟶ B` be unramified and separated and let `g, h : Z ⟶ Y` be two morphisms over `B`.
If `g` and `h` agree after precomposition with a morphism `k` whose image is dense in `Z`, then
`g = h`. -/
theorem eq_of_comp_eq_of_denseRange {B Y Z Z' : Scheme.{u}} (p : Y ⟶ B)
    [Unramified p] [IsSeparated p] (g h : Z ⟶ Y) (hp : g ≫ p = h ≫ p)
    (k : Z' ⟶ Z) (hk : DenseRange k.base) (hgh : k ≫ g = k ≫ h) : g = h := by
  have hdiag : IsClosed (Set.range (pullback.diagonal p).base) :=
    (pullback.diagonal p).isClosedEmbedding.isClosed_range
  have hfac : k ≫ pullback.lift g h hp = (k ≫ g) ≫ pullback.diagonal p := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
    · simp only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id]
      exact hgh.symm
  have hcl : IsClosed ((pullback.lift g h hp).base ⁻¹'
      Set.range (pullback.diagonal p).base) :=
    hdiag.preimage (pullback.lift g h hp).base.hom.continuous
  have hdense : Set.range k.base ⊆ (pullback.lift g h hp).base ⁻¹'
      Set.range (pullback.diagonal p).base := by
    rintro _ ⟨z, rfl⟩
    exact ⟨(k ≫ g).base z, by simpa using (congrArg (fun m => m.base z) hfac).symm⟩
  have huniv : (pullback.lift g h hp).base ⁻¹'
      Set.range (pullback.diagonal p).base = Set.univ := by
    refine Set.univ_subset_iff.mp ?_
    rw [← hk.closure_eq]
    exact hcl.closure_subset_iff.mpr hdense
  have hsub : Set.range (pullback.lift g h hp).base ⊆
      Set.range (pullback.diagonal p).base := Set.preimage_eq_univ_iff.mp huniv
  obtain ⟨l, hl⟩ : ∃ l : Z ⟶ Y, l ≫ pullback.diagonal p = pullback.lift g h hp :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hsub⟩
  have key : ∀ π : pullback p p ⟶ Y, pullback.diagonal p ≫ π = 𝟙 Y →
      pullback.lift g h hp ≫ π = l := fun π hπ => by
    rw [← hl, Category.assoc, hπ, Category.comp_id]
  exact ((pullback.lift_fst g h hp).symm.trans (key _ (pullback.diagonal_fst p))).trans
    ((pullback.lift_snd g h hp).symm.trans (key _ (pullback.diagonal_snd p))).symm

/-! ### Descent data from gluing data on the literal fibre products -/

namespace DescentDatum

variable {T₀ S : Scheme.{u}} {f : T₀ ⟶ S} (V : Over T₀)

/-- The comparison isomorphism identifying the underlying scheme of the product `V ×_S T₀`,
taken in `Over S`, with the literal fibre product of schemes. -/
abbrev prodIsoPullbackSrc :
    ((Over.map f).obj V ⨯ Over.mk f).left ≅ pullback (V.hom ≫ f) f :=
  Over.prodLeftIsoPullback ((Over.map f).obj V) (Over.mk f)

/-- The comparison isomorphism identifying the underlying scheme of the product `T₀ ×_S V`,
taken in `Over S`, with the literal fibre product of schemes. -/
abbrev prodIsoPullbackTgt :
    (Over.mk f ⨯ (Over.map f).obj V).left ≅ pullback f (V.hom ≫ f) :=
  Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj V)

/-- The source comparison isomorphism carries the first projection of the fibre product to the
first projection of the product. -/
lemma prodIsoPullbackSrc_hom_fst :
    (prodIsoPullbackSrc V).hom ≫ pullback.fst (V.hom ≫ f) f =
      Over.Hom.left (prod.fst : (Over.map f).obj V ⨯ Over.mk f ⟶ (Over.map f).obj V) :=
  Over.prodLeftIsoPullback_hom_fst _ _

/-- The source comparison isomorphism carries the second projection of the fibre product to the
second projection of the product. -/
lemma prodIsoPullbackSrc_hom_snd :
    (prodIsoPullbackSrc V).hom ≫ pullback.snd (V.hom ≫ f) f =
      Over.Hom.left (prod.snd : (Over.map f).obj V ⨯ Over.mk f ⟶ Over.mk f) :=
  Over.prodLeftIsoPullback_hom_snd _ _

/-- The target comparison isomorphism carries the first projection of the product to the first
projection of the fibre product. -/
lemma prodIsoPullbackTgt_inv_fst :
    (prodIsoPullbackTgt V).inv ≫
      Over.Hom.left (prod.fst : Over.mk f ⨯ (Over.map f).obj V ⟶ Over.mk f) =
      pullback.fst f (V.hom ≫ f) :=
  Over.prodLeftIsoPullback_inv_fst _ _

/-- The target comparison isomorphism carries the second projection of the product to the second
projection of the fibre product. -/
lemma prodIsoPullbackTgt_inv_snd :
    (prodIsoPullbackTgt V).inv ≫
      Over.Hom.left (prod.snd : Over.mk f ⨯ (Over.map f).obj V ⟶ (Over.map f).obj V) =
      pullback.snd f (V.hom ≫ f) :=
  Over.prodLeftIsoPullback_inv_snd _ _

/-- The morphism between the products `V ×_S T₀ ⟶ T₀ ×_S V` taken in `Over S` given by a morphism
of the literal fibre products which carries the projection to `T₀` of the second factor to the
composite of the projection of the first factor with the structure map of `V`. -/
def gluingHomOfPullbackHom (e : pullback (V.hom ≫ f) f ⟶ pullback f (V.hom ≫ f))
    (he₁ : e ≫ pullback.fst f (V.hom ≫ f) = pullback.fst (V.hom ≫ f) f ≫ V.hom) :
    (Over.map f).obj V ⨯ Over.mk f ⟶ Over.mk f ⨯ (Over.map f).obj V :=
  Over.homMk ((prodIsoPullbackSrc V).hom ≫ e ≫ (prodIsoPullbackTgt V).inv) (by
    have hP2 : Over.Hom.left (prod.fst : Over.mk f ⨯ (Over.map f).obj V ⟶ Over.mk f) ≫ f
        = (Over.mk f ⨯ (Over.map f).obj V).hom := Over.w prod.fst
    have hP1 : Over.Hom.left (prod.fst : (Over.map f).obj V ⨯ Over.mk f ⟶
          (Over.map f).obj V) ≫ (V.hom ≫ f)
        = ((Over.map f).obj V ⨯ Over.mk f).hom := Over.w prod.fst
    rw [← hP2, ← hP1]
    simp only [Category.assoc]
    rw [← Category.assoc ((prodIsoPullbackTgt V).inv), prodIsoPullbackTgt_inv_fst,
      ← Category.assoc e, he₁]
    simp only [Category.assoc]
    rw [← Category.assoc ((prodIsoPullbackSrc V).hom), prodIsoPullbackSrc_hom_fst])

variable (e : pullback (V.hom ≫ f) f ⟶ pullback f (V.hom ≫ f))
  (he₁ : e ≫ pullback.fst f (V.hom ≫ f) = pullback.fst (V.hom ≫ f) f ≫ V.hom)

/-- The underlying morphism of schemes of the candidate gluing map built from pullback data is
the given one, conjugated by the two comparison isomorphisms. -/
lemma gluingHomOfPullbackHom_left :
    Over.Hom.left (gluingHomOfPullbackHom V e he₁) =
      (prodIsoPullbackSrc V).hom ≫ e ≫ (prodIsoPullbackTgt V).inv := rfl

/-- The candidate gluing map built from pullback data preserves the first component of the
pairwise base, which is the first of the two conditions saying that it lies over `T₀ ×_S T₀`. -/
lemma gluingHomOfPullbackHom_comp_fst :
    gluingHomOfPullbackHom V e he₁ ≫ prod.fst = prod.fst ≫ structureMap f V := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, gluingHomOfPullbackHom_left, Category.assoc,
    prodIsoPullbackTgt_inv_fst]
  rw [he₁, ← Category.assoc ((prodIsoPullbackSrc V).hom), prodIsoPullbackSrc_hom_fst]
  rfl

/-- The candidate gluing map built from pullback data preserves the second component of the
pairwise base, which is the second of the two conditions saying that it lies over
`T₀ ×_S T₀`. -/
lemma gluingHomOfPullbackHom_comp_snd_structureMap
    (he₂ : e ≫ pullback.snd f (V.hom ≫ f) ≫ V.hom = pullback.snd (V.hom ≫ f) f) :
    gluingHomOfPullbackHom V e he₁ ≫ prod.snd ≫ structureMap f V = prod.snd := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, gluingHomOfPullbackHom_left, Category.assoc]
  rw [show Over.Hom.left (structureMap f V) = V.hom from rfl,
    ← Category.assoc ((prodIsoPullbackTgt V).inv), prodIsoPullbackTgt_inv_snd, he₂,
    prodIsoPullbackSrc_hom_snd]

/-- The action of a point `x` of `T₀` on a point `v` of `V` determined by a morphism `e` of the
literal fibre products: the `V`-component of `e (v, x)`. -/
def actPullback {Z : Scheme.{u}} (v : Z ⟶ V.left) (x : Z ⟶ T₀)
    (h : v ≫ V.hom ≫ f = x ≫ f) : Z ⟶ V.left :=
  pullback.lift v x h ≫ e ≫ pullback.snd f (V.hom ≫ f)

/-- A pair of generalized points of a product in `Over S` is a pair of generalized points of the
literal fibre product. -/
lemma left_prodLift_comp_prodIsoPullbackSrc {Z : Over S}
    (v : Z ⟶ (Over.map f).obj V) (x : Z ⟶ Over.mk f) :
    Over.Hom.left (prod.lift v x) ≫ (prodIsoPullbackSrc V).hom =
      pullback.lift v.left x.left ((Over.w v).trans (Over.w x).symm) := by
  apply pullback.hom_ext
  · rw [Category.assoc, prodIsoPullbackSrc_hom_fst, ← Over.comp_left, prod.lift_fst]
    exact (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, prodIsoPullbackSrc_hom_snd, ← Over.comp_left, prod.lift_snd]
    exact (pullback.lift_snd _ _ _).symm

/-- The action `AlgebraicGeometry.gluingAction` of
`AlgebraicGeometry.DescentDatum.gluingHomOfPullbackHom` is
`AlgebraicGeometry.DescentDatum.actPullback`. -/
lemma left_gluingAction_gluingHomOfPullbackHom {Z : Over S}
    (v : Z ⟶ (Over.map f).obj V) (x : Z ⟶ Over.mk f) :
    Over.Hom.left (gluingAction V (gluingHomOfPullbackHom V e he₁) v x) =
      actPullback V e v.left x.left ((Over.w v).trans (Over.w x).symm) := by
  simp only [gluingAction, actPullback, Over.comp_left, gluingHomOfPullbackHom_left,
    Category.assoc, prodIsoPullbackTgt_inv_snd]
  rw [← Category.assoc (Over.Hom.left (prod.lift v x)),
    left_prodLift_comp_prodIsoPullbackSrc V v x]
  rfl

/-- The point produced by the action lies over the acting point of `T₀`. -/
lemma actPullback_comp_hom
    (he₂ : e ≫ pullback.snd f (V.hom ≫ f) ≫ V.hom = pullback.snd (V.hom ≫ f) f)
    {Z : Scheme.{u}} (v : Z ⟶ V.left) (x : Z ⟶ T₀) (h : v ≫ V.hom ≫ f = x ≫ f) :
    actPullback V e v x h ≫ V.hom = x := by
  rw [actPullback, Category.assoc, Category.assoc, he₂, pullback.lift_snd]

/-- The action depends on its two points only through their values, not through the proof that
they lie over the same point of `S`. -/
lemma actPullback_congr {Z : Scheme.{u}} {v v' : Z ⟶ V.left} {x x' : Z ⟶ T₀}
    (hv : v = v') (hx : x = x') (h : v ≫ V.hom ≫ f = x ≫ f)
    (h' : v' ≫ V.hom ≫ f = x' ≫ f) :
    actPullback V e v x h = actPullback V e v' x' h' := by
  subst hv; subst hx; rfl

/-- The action commutes with change of test scheme. -/
lemma comp_actPullback {Z Z' : Scheme.{u}} (k : Z' ⟶ Z) (v : Z ⟶ V.left) (x : Z ⟶ T₀)
    (h : v ≫ V.hom ≫ f = x ≫ f) (h' : (k ≫ v) ≫ V.hom ≫ f = (k ≫ x) ≫ f) :
    k ≫ actPullback V e v x h = actPullback V e (k ≫ v) (k ≫ x) h' := by
  have hk : k ≫ pullback.lift v x h = pullback.lift (k ≫ v) (k ≫ x) h' := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
  rw [actPullback, actPullback, ← Category.assoc, hk]

/-- The point produced by the action lies over the second acting point as soon as the two acting
points lie over the same point of `S`. -/
lemma actPullback_comp_hom_comp
    (he₂ : e ≫ pullback.snd f (V.hom ≫ f) ≫ V.hom = pullback.snd (V.hom ≫ f) f)
    {Z : Scheme.{u}} (v : Z ⟶ V.left) (x y : Z ⟶ T₀)
    (hv : v ≫ V.hom ≫ f = x ≫ f) (hw : x ≫ f = y ≫ f) :
    actPullback V e v x hv ≫ V.hom ≫ f = y ≫ f := by
  rw [← Category.assoc, actPullback_comp_hom V e he₂, hw]

/-- If acting twice and acting once agree for the images of three points under `k`, then the two
sides of the action law for the original three points agree after composition with `k`. -/
lemma comp_actPullback_act_act {Z Z' : Scheme.{u}} (k : Z' ⟶ Z) (v : Z ⟶ V.left) (x y : Z ⟶ T₀)
    (hv : v ≫ V.hom ≫ f = x ≫ f) (hw : x ≫ f = y ≫ f)
    (hvx : actPullback V e v x hv ≫ V.hom ≫ f = y ≫ f)
    (hv' : (k ≫ v) ≫ V.hom ≫ f = (k ≫ x) ≫ f) (hw' : (k ≫ x) ≫ f = (k ≫ y) ≫ f)
    (hvx' : actPullback V e (k ≫ v) (k ≫ x) hv' ≫ V.hom ≫ f = (k ≫ y) ≫ f)
    (hlaw : actPullback V e (actPullback V e (k ≫ v) (k ≫ x) hv') (k ≫ y) hvx'
      = actPullback V e (k ≫ v) (k ≫ y) (hv'.trans hw')) :
    k ≫ actPullback V e (actPullback V e v x hv) y hvx
      = k ≫ actPullback V e v y (hv.trans hw) := by
  have hinner : k ≫ actPullback V e v x hv = actPullback V e (k ≫ v) (k ≫ x) hv' :=
    comp_actPullback V e k v x hv hv'
  rw [comp_actPullback V e k _ _ hvx (by rw [hinner]; exact hvx'),
    comp_actPullback V e k v y (hv.trans hw) (hv'.trans hw'),
    actPullback_congr V e hinner rfl _ hvx']
  exact hlaw

/-- The scheme carrying the universal triple of a point of `V` and two points of `T₀` lying over
one point of `S`, namely `V ×_S T₀ ×_S T₀`. -/
def tripleObj : Scheme.{u} := pullback (pullback.snd (V.hom ≫ f) f ≫ f) f

/-- The projection of `AlgebraicGeometry.DescentDatum.tripleObj` to `V ×_S T₀`. -/
def tripleFst : tripleObj V (f := f) ⟶ pullback (V.hom ≫ f) f :=
  pullback.fst (pullback.snd (V.hom ≫ f) f ≫ f) f

/-- The second universal point of `T₀` on `AlgebraicGeometry.DescentDatum.tripleObj`. -/
def tripleY : tripleObj V (f := f) ⟶ T₀ :=
  pullback.snd (pullback.snd (V.hom ≫ f) f ≫ f) f

/-- The universal point of `V` on `AlgebraicGeometry.DescentDatum.tripleObj`. -/
def tripleV : tripleObj V (f := f) ⟶ V.left :=
  tripleFst V ≫ pullback.fst (V.hom ≫ f) f

/-- The first universal point of `T₀` on `AlgebraicGeometry.DescentDatum.tripleObj`. -/
def tripleX : tripleObj V (f := f) ⟶ T₀ :=
  tripleFst V ≫ pullback.snd (V.hom ≫ f) f

/-- The triple product is flat over the base as soon as `V` and `f` are. -/
instance flat_tripleY_comp [Flat f] [Flat V.hom] : Flat (tripleY V (f := f) ≫ f) :=
  inferInstanceAs (Flat (pullback.snd (pullback.snd (V.hom ≫ f) f ≫ f) f ≫ f))

/-- The second universal point of `T₀` is flat as soon as `V` and `f` are. -/
instance flat_tripleY [Flat f] [Flat V.hom] : Flat (tripleY V (f := f)) :=
  inferInstanceAs (Flat (pullback.snd (pullback.snd (V.hom ≫ f) f ≫ f) f))

/-- The morphism to `AlgebraicGeometry.DescentDatum.tripleObj` defined by a point of `V` and two
points of `T₀` lying over one point of `S`. -/
def tripleLift {Z : Scheme.{u}} (v : Z ⟶ V.left) (x y : Z ⟶ T₀)
    (hv : v ≫ V.hom ≫ f = x ≫ f) (hw : x ≫ f = y ≫ f) : Z ⟶ tripleObj V (f := f) :=
  pullback.lift (pullback.lift v x hv) y (by rw [← Category.assoc, pullback.lift_snd]; exact hw)

/-- The universal triple projects to the pair of its first two points. -/
lemma tripleLift_comp_tripleFst {Z : Scheme.{u}} (v : Z ⟶ V.left) (x y : Z ⟶ T₀)
    (hv : v ≫ V.hom ≫ f = x ≫ f) (hw : x ≫ f = y ≫ f) :
    tripleLift V v x y hv hw ≫ tripleFst V (f := f) = pullback.lift v x hv :=
  pullback.lift_fst _ _ _

/-- The universal triple has first component the given point of `V`. -/
lemma tripleLift_comp_tripleV {Z : Scheme.{u}} (v : Z ⟶ V.left) (x y : Z ⟶ T₀)
    (hv : v ≫ V.hom ≫ f = x ≫ f) (hw : x ≫ f = y ≫ f) :
    tripleLift V v x y hv hw ≫ tripleV V (f := f) = v := by
  rw [tripleV, ← Category.assoc, tripleLift_comp_tripleFst, pullback.lift_fst]

/-- The universal triple has second component the first given point of `T₀`. -/
lemma tripleLift_comp_tripleX {Z : Scheme.{u}} (v : Z ⟶ V.left) (x y : Z ⟶ T₀)
    (hv : v ≫ V.hom ≫ f = x ≫ f) (hw : x ≫ f = y ≫ f) :
    tripleLift V v x y hv hw ≫ tripleX V (f := f) = x := by
  rw [tripleX, ← Category.assoc, tripleLift_comp_tripleFst, pullback.lift_snd]

/-- The universal triple has third component the second given point of `T₀`. -/
lemma tripleLift_comp_tripleY {Z : Scheme.{u}} (v : Z ⟶ V.left) (x y : Z ⟶ T₀)
    (hv : v ≫ V.hom ≫ f = x ≫ f) (hw : x ≫ f = y ≫ f) :
    tripleLift V v x y hv hw ≫ tripleY V (f := f) = y :=
  pullback.lift_snd _ _ _

/-- The universal point of `V` and the first universal point of `T₀` lie over one point of `S`. -/
lemma tripleV_comp : tripleV V (f := f) ≫ V.hom ≫ f = tripleX V (f := f) ≫ f := by
  rw [tripleV, tripleX, Category.assoc, pullback.condition, ← Category.assoc]

/-- The two universal points of `T₀` lie over one point of `S`. -/
lemma tripleX_comp : tripleX V (f := f) ≫ f = tripleY V (f := f) ≫ f := by
  rw [tripleX, Category.assoc]
  exact pullback.condition

/-- The cocycle condition as the action law `(v · x) · y = v · y` on generalized points. -/
def ActPullbackLaw : Prop :=
  ∀ {Z : Scheme.{u}} (v : Z ⟶ V.left) (x y : Z ⟶ T₀)
    (hv : v ≫ V.hom ≫ f = x ≫ f) (hw : x ≫ f = y ≫ f)
    (hvx : actPullback V e v x hv ≫ V.hom ≫ f = y ≫ f),
      actPullback V e (actPullback V e v x hv) y hvx = actPullback V e v y (hv.trans hw)

/-- The action law holds as soon as it holds for the universal triple on
`AlgebraicGeometry.DescentDatum.tripleObj`. -/
theorem actPullbackLaw_of_universal
    (he₂ : e ≫ pullback.snd f (V.hom ≫ f) ≫ V.hom = pullback.snd (V.hom ≫ f) f)
    (huniv : actPullback V e
        (actPullback V e (tripleV V (f := f)) (tripleX V (f := f)) (tripleV_comp V))
        (tripleY V (f := f))
        (actPullback_comp_hom_comp V e he₂ _ _ _ (tripleV_comp V) (tripleX_comp V)) =
      actPullback V e (tripleV V (f := f)) (tripleY V (f := f))
        ((tripleV_comp V).trans (tripleX_comp V))) :
    ActPullbackLaw V e := by
  intro Z v x y hv hw hvx
  have hkv : tripleLift V v x y hv hw ≫ tripleV V (f := f) = v :=
    tripleLift_comp_tripleV V v x y hv hw
  have hkx : tripleLift V v x y hv hw ≫ tripleX V (f := f) = x :=
    tripleLift_comp_tripleX V v x y hv hw
  have hky : tripleLift V v x y hv hw ≫ tripleY V (f := f) = y :=
    tripleLift_comp_tripleY V v x y hv hw
  have hinner : tripleLift V v x y hv hw ≫
      actPullback V e (tripleV V (f := f)) (tripleX V (f := f)) (tripleV_comp V)
      = actPullback V e v x hv := by
    rw [comp_actPullback V e _ _ _ (tripleV_comp V) (by rw [hkv, hkx]; exact hv)]
    exact actPullback_congr V e hkv hkx _ hv
  calc actPullback V e (actPullback V e v x hv) y hvx
      = tripleLift V v x y hv hw ≫ actPullback V e
          (actPullback V e (tripleV V (f := f)) (tripleX V (f := f)) (tripleV_comp V))
          (tripleY V (f := f))
          (actPullback_comp_hom_comp V e he₂ _ _ _ (tripleV_comp V) (tripleX_comp V)) := by
        rw [comp_actPullback V e _ _ _ _ (by rw [hinner, hky]; exact hvx)]
        exact (actPullback_congr V e hinner hky _ _).symm
    _ = tripleLift V v x y hv hw ≫ actPullback V e (tripleV V (f := f))
          (tripleY V (f := f)) ((tripleV_comp V).trans (tripleX_comp V)) := by rw [huniv]
    _ = actPullback V e v y (hv.trans hw) := by
        rw [comp_actPullback V e _ _ _ _ (by rw [hkv, hky]; exact hv.trans hw)]
        exact actPullback_congr V e hkv hky _ _

/-- For `V` unramified and separated over `T₀`, an instance of the action law holds as soon as it
holds after precomposition with a morphism of dense image. -/
theorem actPullback_eq_of_denseRange [Unramified V.hom] [IsSeparated V.hom]
    (he₂ : e ≫ pullback.snd f (V.hom ≫ f) ≫ V.hom = pullback.snd (V.hom ≫ f) f)
    {Z : Scheme.{u}} (v : Z ⟶ V.left) (x y : Z ⟶ T₀)
    (hv : v ≫ V.hom ≫ f = x ≫ f) (hw : x ≫ f = y ≫ f)
    (hvx : actPullback V e v x hv ≫ V.hom ≫ f = y ≫ f)
    {Z' : Scheme.{u}} (k : Z' ⟶ Z) (hk : DenseRange k.base)
    (hagree : k ≫ actPullback V e (actPullback V e v x hv) y hvx =
      k ≫ actPullback V e v y (hv.trans hw)) :
    actPullback V e (actPullback V e v x hv) y hvx = actPullback V e v y (hv.trans hw) := by
  refine eq_of_comp_eq_of_denseRange V.hom _ _ ?_ k hk hagree
  rw [actPullback_comp_hom V e he₂, actPullback_comp_hom V e he₂]

/-- `AlgebraicGeometry.DescentDatum.gluingHomOfPullbackHom` for an isomorphism of the literal fibre
products. -/
def gluingIsoOfPullbackIso (i : pullback (V.hom ≫ f) f ≅ pullback f (V.hom ≫ f))
    (hi₁ : i.hom ≫ pullback.fst f (V.hom ≫ f) = pullback.fst (V.hom ≫ f) f ≫ V.hom) :
    (Over.map f).obj V ⨯ Over.mk f ≅ Over.mk f ⨯ (Over.map f).obj V :=
  Over.isoMk ((prodIsoPullbackSrc V) ≪≫ i ≪≫ (prodIsoPullbackTgt V).symm)
    (Over.w (gluingHomOfPullbackHom V i.hom hi₁))

/-- The gluing isomorphism built from a pullback-form isomorphism has the expected underlying
morphism. -/
lemma gluingIsoOfPullbackIso_hom
    (i : pullback (V.hom ≫ f) f ≅ pullback f (V.hom ≫ f))
    (hi₁ : i.hom ≫ pullback.fst f (V.hom ≫ f) = pullback.fst (V.hom ≫ f) f ≫ V.hom) :
    (gluingIsoOfPullbackIso V i hi₁).hom = gluingHomOfPullbackHom V i.hom hi₁ := rfl

/-- **A descent datum from gluing data on the literal fibre products.** Let `f : T₀ ⟶ S` be a
morphism of schemes and `V` a scheme over `T₀`. Given an isomorphism

```
i : V ×_S T₀ ≅ T₀ ×_S V
```

of schemes which lies over `T₀ ×_S T₀` — that is, which carries the two projections to `T₀` to each
other, `hi₁` and `hi₂` — and which satisfies the cocycle condition in the form
`(v · x) · y = v · y` for generalized points, this is the descent datum relative to `f` with
underlying scheme `V` and that gluing isomorphism. -/
def ofPullbackIso
    (i : pullback (V.hom ≫ f) f ≅ pullback f (V.hom ≫ f))
    (hi₁ : i.hom ≫ pullback.fst f (V.hom ≫ f) = pullback.fst (V.hom ≫ f) f ≫ V.hom)
    (hi₂ : i.hom ≫ pullback.snd f (V.hom ≫ f) ≫ V.hom = pullback.snd (V.hom ≫ f) f)
    (hcoc : ActPullbackLaw V i.hom) :
    DescentDatum f := by
  have h1 := gluingHomOfPullbackHom_comp_fst V i.hom hi₁
  have h2 := gluingHomOfPullbackHom_comp_snd_structureMap V i.hom hi₁ hi₂
  refine mk' V (Over.isoMk (gluingIsoOfPullbackIso V i hi₁) ?_) ?_
  · apply prod.hom_ext
    · simpa only [gluingIsoOfPullbackIso_hom, Over.mk_hom, Category.assoc, prod.map_fst,
        Category.comp_id] using h1
    · simpa only [gluingIsoOfPullbackIso_hom, Over.mk_hom, Category.assoc, prod.map_snd,
        Category.comp_id] using h2
  · refine (cocycle_iff_gluingAction_act_act V _ h1 h2).mpr ?_
    intro Z v x y
    apply Over.OverMorphism.ext
    have hvx : actPullback V i.hom v.left x.left
          ((Over.w v).trans (Over.w x).symm) ≫ V.hom ≫ f = y.left ≫ f := by
      rw [← Category.assoc, actPullback_comp_hom V i.hom hi₂]
      exact (Over.w x).trans (Over.w y).symm
    rw [left_gluingAction_gluingHomOfPullbackHom V i.hom hi₁
        (gluingAction V (gluingHomOfPullbackHom V i.hom hi₁) v x) y,
      left_gluingAction_gluingHomOfPullbackHom V i.hom hi₁ v y]
    refine Eq.trans (actPullback_congr V i.hom
      (left_gluingAction_gluingHomOfPullbackHom V i.hom hi₁ v x) rfl _ hvx) ?_
    exact hcoc v.left x.left y.left _ ((Over.w x).trans (Over.w y).symm) hvx

/-- The scheme underlying the descent datum built from pullback-form gluing data is the given
one. -/
lemma ofPullbackIso_over
    (i : pullback (V.hom ≫ f) f ≅ pullback f (V.hom ≫ f))
    (hi₁ : i.hom ≫ pullback.fst f (V.hom ≫ f) = pullback.fst (V.hom ≫ f) f ≫ V.hom)
    (hi₂ : i.hom ≫ pullback.snd f (V.hom ≫ f) ≫ V.hom = pullback.snd (V.hom ≫ f) f)
    (hcoc : ActPullbackLaw V i.hom) :
    (ofPullbackIso V i hi₁ hi₂ hcoc).over = V := rfl

/-- Conjugating a morphism of the literal fibre products by the two comparison isomorphisms and
back gives the morphism again. -/
lemma prodIsoPullback_conjugate_cancel :
    (prodIsoPullbackSrc V).inv ≫ ((prodIsoPullbackSrc V).hom ≫ e ≫
      (prodIsoPullbackTgt V).inv) ≫ (prodIsoPullbackTgt V).hom = e := by
  simp

/-- The gluing isomorphism of the descent datum built from pullback-form gluing data, read on the
literal fibre products, is the given one. -/
lemma ofPullbackIso_gluingPullbackIso_hom
    (i : pullback (V.hom ≫ f) f ≅ pullback f (V.hom ≫ f))
    (hi₁ : i.hom ≫ pullback.fst f (V.hom ≫ f) = pullback.fst (V.hom ≫ f) f ≫ V.hom)
    (hi₂ : i.hom ≫ pullback.snd f (V.hom ≫ f) ≫ V.hom = pullback.snd (V.hom ≫ f) f)
    (hcoc : ActPullbackLaw V i.hom) :
    ((ofPullbackIso V i hi₁ hi₂ hcoc).gluingPullbackIso () ()).hom = i.hom :=
  (rfl : ((ofPullbackIso V i hi₁ hi₂ hcoc).gluingPullbackIso () ()).hom =
      (prodIsoPullbackSrc V).inv ≫ ((prodIsoPullbackSrc V).hom ≫ i.hom ≫
        (prodIsoPullbackTgt V).inv) ≫ (prodIsoPullbackTgt V).hom).trans
    (prodIsoPullback_conjugate_cancel V i.hom)

end DescentDatum

/-! ### The cocycle condition for the gluing isomorphism -/

namespace DescentDatum

variable {T₀ B : Scheme.{u}} (f : T₀ ⟶ B) (Y : FiniteEtaleOver T₀)
  (φ : (finiteEtaleBaseChange (pullback.fst f f)).obj Y ≅
    (finiteEtaleBaseChange (pullback.snd f f)).obj Y)

/-- The underlying morphism of schemes of `AlgebraicGeometry.DescentDatum.fstSndLeftIso`. -/
lemma fstSndLeftIso_hom : (fstSndLeftIso f Y φ).hom = φ.hom.left := rfl

/-- For the gluing isomorphism in pullback form, acting by a point `x` of `T₀` on a point `v` of
`Y` is applying `φ` to the point of the base change given by `v` and the point `(v ≫ Y.hom, x)` of
`T₀ ×_B T₀`. -/
lemma actPullback_gluingPullbackIsoOfFstSndIso {Z : Scheme.{u}} (v : Z ⟶ Y.left) (x : Z ⟶ T₀)
    (hv : v ≫ Y.hom ≫ f = x ≫ f) (hv' : (v ≫ Y.hom) ≫ f = x ≫ f)
    (hvp : v ≫ Y.hom = pullback.lift (v ≫ Y.hom) x hv' ≫ pullback.fst f f) :
    actPullback (Over.mk Y.hom) (gluingPullbackIsoOfFstSndIso f Y φ).hom v x hv =
      finiteEtaleBaseChangeLift (pullback.fst f f) Y v
          (pullback.lift (v ≫ Y.hom) x hv') hvp ≫
        φ.hom.left ≫ finiteEtaleBaseChangeProj (pullback.snd f f) Y := by
  have hA : (pullbackSymmetry Y.hom (pullback.snd f f)).hom ≫
      (pullbackLeftPullbackSndIso f f Y.hom).hom ≫ pullback.snd f (Y.hom ≫ f) =
      pullback.fst Y.hom (pullback.snd f f) := by
    rw [pullbackLeftPullbackSndIso_hom_snd, pullbackSymmetry_hom_comp_snd]
  have hB : pullback.lift v x hv ≫ (pullbackRightPullbackFstIso f f Y.hom).inv =
      pullback.lift v (pullback.lift (v ≫ Y.hom) x hv') hvp := by
    refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_)
    · simp [pullback.lift_fst]
    · simp [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd]
    · simp [pullback.lift_snd]
  have key : pullback.lift v x hv ≫ (gluingPullbackIsoOfFstSndIso f Y φ).hom ≫
        pullback.snd f (Y.hom ≫ f) =
      pullback.lift v (pullback.lift (v ≫ Y.hom) x hv') hvp ≫ (fstSndLeftIso f Y φ).hom ≫
        pullback.fst Y.hom (pullback.snd f f) := by
    rw [gluingPullbackIsoOfFstSndIso_hom]
    slice_lhs 1 2 => rw [hB]
    slice_lhs 3 5 => rw [hA]
  exact key


variable {T₀ B : Scheme.{u}} (f : T₀ ⟶ B) (U : B.Opens) (Y : FiniteEtaleOver T₀)
  (V : FiniteEtaleOver U.toScheme)
  (ε : (finiteEtaleBaseChange (f ⁻¹ᵁ U).ι).obj Y ≅ (finiteEtaleBaseChange (f ∣_ U)).obj V)
  (hff : (finiteEtaleBaseChange ((pullback.fst f f ≫ f) ⁻¹ᵁ U).ι).FullyFaithful)

/-- For the gluing isomorphism `AlgebraicGeometry.gluingIsoPullbackFstSnd`, the action of a point
of `T₀` on a point of `Y`, when the acting pair lies over `U`, is transport to `V` along `ε` over
the first component followed by transport back over the second. -/
lemma actPullback_gluingIsoPullbackFstSnd {Z : Scheme.{u}} (u : Z ⟶ Y.left) (x : Z ⟶ T₀)
    (hu : u ≫ Y.hom ≫ f = x ≫ f) (hu' : (u ≫ Y.hom) ≫ f = x ≫ f)
    (w : Z ⟶ ((pullback.fst f f ≫ f) ⁻¹ᵁ U).toScheme)
    (hw : w ≫ ((pullback.fst f f ≫ f) ⁻¹ᵁ U).ι = pullback.lift (u ≫ Y.hom) x hu')
    (hu₁ : u ≫ Y.hom = (w ≫ resFstPreimage f U) ≫ (f ⁻¹ᵁ U).ι)
    (hp : transportPoint ε u (w ≫ resFstPreimage f U) hu₁ ≫ V.hom
      = (w ≫ resSndPreimage f U) ≫ (f ∣_ U)) :
    actPullback (Over.mk Y.hom)
        (gluingPullbackIsoOfFstSndIso f Y (gluingIsoPullbackFstSnd f U Y V ε hff)).hom
        u x hu =
      transportPointSymm ε (transportPoint ε u (w ≫ resFstPreimage f U) hu₁)
        (w ≫ resSndPreimage f U) hp := by
  have hvp : u ≫ Y.hom = pullback.lift (u ≫ Y.hom) x hu' ≫ pullback.fst f f :=
    (pullback.lift_fst _ _ _).symm
  have hvw : u ≫ Y.hom
      = (w ≫ ((pullback.fst f f ≫ f) ⁻¹ᵁ U).ι) ≫ pullback.fst f f := by
    rw [hw]; exact hvp
  rw [actPullback_gluingPullbackIsoOfFstSndIso f Y _ u x hu hu' hvp,
    finiteEtaleBaseChangeLift_congr (pullback.fst f f) Y u hw.symm hvp hvw]
  exact gluingIsoOfFullyFaithful_hom_left_proj ((pullback.fst f f ≫ f) ⁻¹ᵁ U).ι
    (pullback.fst f f) (pullback.snd f f) (f ⁻¹ᵁ U).ι (f ∣_ U) (resFstPreimage f U)
    (resSndPreimage f U) (resFstPreimage_comp_ι f U) (resSndPreimage_comp_ι f U)
    (resFstPreimage_comp_morphismRestrict f U) Y V ε hff u w hvw hu₁ hp

/-- The action law for the gluing isomorphism `AlgebraicGeometry.gluingIsoPullbackFstSnd`, for a
triple whose three pairs all lie in the preimage of `U` (the hypotheses `h₁₂`, `h₂₃`, `h₁₃`). -/
lemma actPullback_act_act_of_le {Z : Scheme.{u}} (u : Z ⟶ Y.left) (x y : Z ⟶ T₀)
    (hu : u ≫ Y.hom ≫ f = x ≫ f) (hxy : x ≫ f = y ≫ f)
    (hu' : (u ≫ Y.hom) ≫ f = x ≫ f) (hy' : (u ≫ Y.hom) ≫ f = y ≫ f)
    (hvx : actPullback (Over.mk Y.hom)
      (gluingPullbackIsoOfFstSndIso f Y (gluingIsoPullbackFstSnd f U Y V ε hff)).hom u x hu ≫
      (Over.mk Y.hom).hom ≫ f = y ≫ f)
    (w₁₂ w₂₃ w₁₃ : Z ⟶ ((pullback.fst f f ≫ f) ⁻¹ᵁ U).toScheme)
    (h₁₂ : w₁₂ ≫ ((pullback.fst f f ≫ f) ⁻¹ᵁ U).ι = pullback.lift (u ≫ Y.hom) x hu')
    (h₂₃ : w₂₃ ≫ ((pullback.fst f f ≫ f) ⁻¹ᵁ U).ι = pullback.lift x y hxy)
    (h₁₃ : w₁₃ ≫ ((pullback.fst f f ≫ f) ⁻¹ᵁ U).ι = pullback.lift (u ≫ Y.hom) y hy') :
    actPullback (Over.mk Y.hom)
        (gluingPullbackIsoOfFstSndIso f Y (gluingIsoPullbackFstSnd f U Y V ε hff)).hom
        (actPullback (Over.mk Y.hom)
          (gluingPullbackIsoOfFstSndIso f Y (gluingIsoPullbackFstSnd f U Y V ε hff)).hom
          u x hu) y hvx =
      actPullback (Over.mk Y.hom)
        (gluingPullbackIsoOfFstSndIso f Y (gluingIsoPullbackFstSnd f U Y V ε hff)).hom
        u y (hu.trans hxy) := by
  have he₂ := gluingPullbackIsoOfFstSndIso_hom_snd f Y (gluingIsoPullbackFstSnd f U Y V ε hff)
  have hz₁ : w₁₃ ≫ resFstPreimage f U = w₁₂ ≫ resFstPreimage f U := by
    refine comp_eq_of_comp_ι_eq (resFstPreimage_comp_ι f U) (resFstPreimage_comp_ι f U) w₁₃ w₁₂ ?_
    rw [← Category.assoc, ← Category.assoc, h₁₂, h₁₃, pullback.lift_fst, pullback.lift_fst]
  have hz₂ : w₂₃ ≫ resFstPreimage f U = w₁₂ ≫ resSndPreimage f U := by
    refine comp_eq_of_comp_ι_eq (resFstPreimage_comp_ι f U) (resSndPreimage_comp_ι f U) w₂₃ w₁₂ ?_
    rw [← Category.assoc, ← Category.assoc, h₁₂, h₂₃, pullback.lift_fst, pullback.lift_snd]
  have hz₃ : w₁₃ ≫ resSndPreimage f U = w₂₃ ≫ resSndPreimage f U := by
    refine comp_eq_of_comp_ι_eq (resSndPreimage_comp_ι f U) (resSndPreimage_comp_ι f U) w₁₃ w₂₃ ?_
    rw [← Category.assoc, ← Category.assoc, h₂₃, h₁₃, pullback.lift_snd, pullback.lift_snd]
  have hbase : ∀ (w : Z ⟶ ((pullback.fst f f ≫ f) ⁻¹ᵁ U).toScheme) (p : Z ⟶ T₀)
      {c : pullback f f ⟶ T₀} {ρ : ((pullback.fst f f ≫ f) ⁻¹ᵁ U).toScheme ⟶ (f ⁻¹ᵁ U).toScheme},
      ((pullback.fst f f ≫ f) ⁻¹ᵁ U).ι ≫ c = ρ ≫ (f ⁻¹ᵁ U).ι →
      w ≫ ((pullback.fst f f ≫ f) ⁻¹ᵁ U).ι ≫ c = p → p = (w ≫ ρ) ≫ (f ⁻¹ᵁ U).ι := by
    intro w p c ρ hc hp
    rw [hc] at hp
    rw [← hp, Category.assoc]
  have hu₁₂ : u ≫ Y.hom = (w₁₂ ≫ resFstPreimage f U) ≫ (f ⁻¹ᵁ U).ι :=
    hbase w₁₂ _ (resFstPreimage_comp_ι f U) (by rw [← Category.assoc, h₁₂, pullback.lift_fst])
  have hu₁₃ : u ≫ Y.hom = (w₁₃ ≫ resFstPreimage f U) ≫ (f ⁻¹ᵁ U).ι :=
    hbase w₁₃ _ (resFstPreimage_comp_ι f U) (by rw [← Category.assoc, h₁₃, pullback.lift_fst])
  have hx₁₂ : x = (w₁₂ ≫ resSndPreimage f U) ≫ (f ⁻¹ᵁ U).ι :=
    hbase w₁₂ _ (resSndPreimage_comp_ι f U) (by rw [← Category.assoc, h₁₂, pullback.lift_snd])
  have hx₂₃ : x = (w₂₃ ≫ resFstPreimage f U) ≫ (f ⁻¹ᵁ U).ι :=
    hbase w₂₃ _ (resFstPreimage_comp_ι f U) (by rw [← Category.assoc, h₂₃, pullback.lift_fst])
  have hy₂₃ : y = (w₂₃ ≫ resSndPreimage f U) ≫ (f ⁻¹ᵁ U).ι :=
    hbase w₂₃ _ (resSndPreimage_comp_ι f U) (by rw [← Category.assoc, h₂₃, pullback.lift_snd])
  have hy₁₃ : y = (w₁₃ ≫ resSndPreimage f U) ≫ (f ⁻¹ᵁ U).ι :=
    hbase w₁₃ _ (resSndPreimage_comp_ι f U) (by rw [← Category.assoc, h₁₃, pullback.lift_snd])
  have hp : ∀ (z : Z ⟶ Y.left) (w : Z ⟶ ((pullback.fst f f ≫ f) ⁻¹ᵁ U).toScheme)
      (h : z ≫ Y.hom = (w ≫ resFstPreimage f U) ≫ (f ⁻¹ᵁ U).ι),
      transportPoint ε z (w ≫ resFstPreimage f U) h ≫ V.hom
        = (w ≫ resSndPreimage f U) ≫ (f ∣_ U) := fun z w h => by
    rw [transportPoint_comp_hom, Category.assoc, Category.assoc,
      resFstPreimage_comp_morphismRestrict f U]
  have hp₁₂ := hp u w₁₂ hu₁₂
  have hinner := actPullback_gluingIsoPullbackFstSnd f U Y V ε hff u x hu hu' w₁₂ h₁₂ hu₁₂ hp₁₂
  have hact : actPullback (Over.mk Y.hom)
      (gluingPullbackIsoOfFstSndIso f Y (gluingIsoPullbackFstSnd f U Y V ε hff)).hom u x hu ≫
      Y.hom = x := actPullback_comp_hom (Over.mk Y.hom) _ he₂ u x hu
  have hout' : (actPullback (Over.mk Y.hom)
      (gluingPullbackIsoOfFstSndIso f Y (gluingIsoPullbackFstSnd f U Y V ε hff)).hom u x hu ≫
      Y.hom) ≫ f = y ≫ f := by rw [hact]; exact hxy
  have hw₂₃ : w₂₃ ≫ ((pullback.fst f f ≫ f) ⁻¹ᵁ U).ι =
      pullback.lift (actPullback (Over.mk Y.hom)
        (gluingPullbackIsoOfFstSndIso f Y (gluingIsoPullbackFstSnd f U Y V ε hff)).hom
        u x hu ≫ Y.hom) y hout' := by
    rw [h₂₃]
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, pullback.lift_fst, hact]
    · rw [pullback.lift_snd, pullback.lift_snd]
  have houter₁ : actPullback (Over.mk Y.hom)
      (gluingPullbackIsoOfFstSndIso f Y (gluingIsoPullbackFstSnd f U Y V ε hff)).hom u x hu ≫
      Y.hom = (w₂₃ ≫ resFstPreimage f U) ≫ (f ⁻¹ᵁ U).ι := by rw [hact, hx₂₃]
  rw [actPullback_gluingIsoPullbackFstSnd f U Y V ε hff _ y hvx hout' w₂₃ hw₂₃ houter₁
      (hp _ w₂₃ houter₁),
    actPullback_gluingIsoPullbackFstSnd f U Y V ε hff u y (hu.trans hxy) hy' w₁₃ h₁₃ hu₁₃
      (hp u w₁₃ hu₁₃)]
  refine transportPointSymm_congr ε ?_ hz₃.symm _ _
  rw [transportPoint_congr ε hinner hz₂ houter₁ (transportPointSymm_comp_hom ε _ _ hp₁₂),
    transportPoint_transportPointSymm]
  exact transportPoint_congr ε rfl hz₁.symm _ _

/-- **The cocycle condition for `AlgebraicGeometry.gluingIsoPullbackFstSnd`.** If `Y` is unramified
and separated over `T₀` and the preimage of `U` in the triple product is dense, the gluing
isomorphism in pullback form satisfies the action law `(v · x) · y = v · y`. -/
theorem actPullbackLaw_gluingIsoPullbackFstSnd [Unramified Y.hom] [IsSeparated Y.hom]
    (hdense : DenseRange
      (((tripleY (Over.mk Y.hom) (f := f) ≫ f) ⁻¹ᵁ U).ι).base) :
    ActPullbackLaw (Over.mk Y.hom)
      (gluingPullbackIsoOfFstSndIso f Y (gluingIsoPullbackFstSnd f U Y V ε hff)).hom := by
  have : Unramified (Over.mk Y.hom).hom := inferInstanceAs (Unramified Y.hom)
  have : IsSeparated (Over.mk Y.hom).hom := inferInstanceAs (IsSeparated Y.hom)
  have he₂ := gluingPullbackIsoOfFstSndIso_hom_snd f Y (gluingIsoPullbackFstSnd f U Y V ε hff)
  apply actPullbackLaw_of_universal (Over.mk Y.hom)
    (gluingPullbackIsoOfFstSndIso f Y (gluingIsoPullbackFstSnd f U Y V ε hff)).hom he₂
  refine actPullback_eq_of_denseRange (Over.mk Y.hom) _ he₂ (tripleV (Over.mk Y.hom) (f := f))
    (tripleX (Over.mk Y.hom) (f := f)) (tripleY (Over.mk Y.hom) (f := f))
    (tripleV_comp (Over.mk Y.hom)) (tripleX_comp (Over.mk Y.hom)) _ _ hdense ?_
  have hσ' : (tripleV (Over.mk Y.hom) (f := f) ≫ Y.hom) ≫ f
      = tripleX (Over.mk Y.hom) (f := f) ≫ f := by
    rw [Category.assoc]; exact tripleV_comp (Over.mk Y.hom)
  have hρ' : (tripleV (Over.mk Y.hom) (f := f) ≫ Y.hom) ≫ f
      = tripleY (Over.mk Y.hom) (f := f) ≫ f :=
    hσ'.trans (tripleX_comp (Over.mk Y.hom))
  have hlift : ∀ (a b : tripleObj (Over.mk Y.hom) (f := f) ⟶ T₀) (h : a ≫ f = b ≫ f),
      a ≫ f = tripleY (Over.mk Y.hom) (f := f) ≫ f →
      pullback.lift a b h ≫ (pullback.fst f f ≫ f) = tripleY (Over.mk Y.hom) (f := f) ≫ f :=
    fun a b h h' => by rw [← Category.assoc, pullback.lift_fst]; exact h'
  have hu : (((tripleY (Over.mk Y.hom) (f := f) ≫ f) ⁻¹ᵁ U).ι ≫
        tripleV (Over.mk Y.hom) (f := f)) ≫ (Over.mk Y.hom).hom ≫ f
      = (((tripleY (Over.mk Y.hom) (f := f) ≫ f) ⁻¹ᵁ U).ι ≫
        tripleX (Over.mk Y.hom) (f := f)) ≫ f := by
    rw [Category.assoc, tripleV_comp (Over.mk Y.hom), ← Category.assoc]
  have hxy : (((tripleY (Over.mk Y.hom) (f := f) ≫ f) ⁻¹ᵁ U).ι ≫
        tripleX (Over.mk Y.hom) (f := f)) ≫ f
      = (((tripleY (Over.mk Y.hom) (f := f) ≫ f) ⁻¹ᵁ U).ι ≫
        tripleY (Over.mk Y.hom) (f := f)) ≫ f := by
    rw [Category.assoc, tripleX_comp (Over.mk Y.hom), ← Category.assoc]
  refine comp_actPullback_act_act (Over.mk Y.hom)
    (gluingPullbackIsoOfFstSndIso f Y (gluingIsoPullbackFstSnd f U Y V ε hff)).hom
    ((tripleY (Over.mk Y.hom) (f := f) ≫ f) ⁻¹ᵁ U).ι (tripleV (Over.mk Y.hom) (f := f))
    (tripleX (Over.mk Y.hom) (f := f)) (tripleY (Over.mk Y.hom) (f := f))
    (tripleV_comp (Over.mk Y.hom)) (tripleX_comp (Over.mk Y.hom)) _ hu hxy
    (actPullback_comp_hom_comp (Over.mk Y.hom) _ he₂ _ _ _ hu hxy) ?_
  have hu' : ((((tripleY (Over.mk Y.hom) (f := f) ≫ f) ⁻¹ᵁ U).ι ≫
        tripleV (Over.mk Y.hom) (f := f)) ≫ Y.hom) ≫ f
      = (((tripleY (Over.mk Y.hom) (f := f) ≫ f) ⁻¹ᵁ U).ι ≫
        tripleX (Over.mk Y.hom) (f := f)) ≫ f := (Category.assoc _ _ _).trans hu
  refine actPullback_act_act_of_le f U Y V ε hff _ _ _ _ hxy hu' (hu'.trans hxy)
    (actPullback_comp_hom_comp (Over.mk Y.hom) _ he₂ _ _ _ hu hxy)
    (Scheme.Hom.resLE _ _ _
      (le_of_eq (preimage_preimage_of_comp_eq (hlift _ _ hσ' hρ') U).symm))
    (Scheme.Hom.resLE _ _ _ (le_of_eq (preimage_preimage_of_comp_eq
      (hlift _ _ (tripleX_comp (Over.mk Y.hom)) (tripleX_comp (Over.mk Y.hom))) U).symm))
    (Scheme.Hom.resLE _ _ _
      (le_of_eq (preimage_preimage_of_comp_eq (hlift _ _ hρ' hρ') U).symm)) ?_ ?_ ?_
  all_goals
    rw [Scheme.Hom.resLE_comp_ι]
    refine pullback.hom_ext ?_ ?_ <;> simp [pullback.lift_fst, pullback.lift_snd]

/-- The descent datum relative to `f` with scheme `Y` and gluing isomorphism
`AlgebraicGeometry.gluingIsoPullbackFstSnd`, read in pullback form. -/
def ofGluingIsoPullbackFstSnd [Unramified Y.hom] [IsSeparated Y.hom]
    (hdense : DenseRange
      (((tripleY (Over.mk Y.hom) (f := f) ≫ f) ⁻¹ᵁ U).ι).base) :
    DescentDatum f :=
  ofPullbackIso (Over.mk Y.hom)
    (gluingPullbackIsoOfFstSndIso f Y (gluingIsoPullbackFstSnd f U Y V ε hff))
    (gluingPullbackIsoOfFstSndIso_hom_fst f Y (gluingIsoPullbackFstSnd f U Y V ε hff))
    (gluingPullbackIsoOfFstSndIso_hom_snd f Y (gluingIsoPullbackFstSnd f U Y V ε hff))
    (actPullbackLaw_gluingIsoPullbackFstSnd f U Y V ε hff hdense)

/-- The scheme underlying `AlgebraicGeometry.DescentDatum.ofGluingIsoPullbackFstSnd` is `Y`. -/
lemma ofGluingIsoPullbackFstSnd_over [Unramified Y.hom] [IsSeparated Y.hom]
    (hdense : DenseRange
      (((tripleY (Over.mk Y.hom) (f := f) ≫ f) ⁻¹ᵁ U).ι).base) :
    (ofGluingIsoPullbackFstSnd f U Y V ε hff hdense).over = Over.mk Y.hom := rfl

/-- The gluing isomorphism of `AlgebraicGeometry.DescentDatum.ofGluingIsoPullbackFstSnd`, read on
the literal fibre products, is `AlgebraicGeometry.DescentDatum.gluingPullbackIsoOfFstSndIso`. -/
lemma ofGluingIsoPullbackFstSnd_gluingPullbackIso_hom [Unramified Y.hom] [IsSeparated Y.hom]
    (hdense : DenseRange
      (((tripleY (Over.mk Y.hom) (f := f) ≫ f) ⁻¹ᵁ U).ι).base) :
    ((ofGluingIsoPullbackFstSnd f U Y V ε hff hdense).gluingPullbackIso () ()).hom =
      (gluingPullbackIsoOfFstSndIso f Y (gluingIsoPullbackFstSnd f U Y V ε hff)).hom :=
  ofPullbackIso_gluingPullbackIso_hom (Over.mk Y.hom) _ _ _ _

end DescentDatum

end AlgebraicGeometry

end
