module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescentTransport
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.ArrowDescentEffective
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.DescendedOperations
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.FiniteFlatQuotientAffine
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Comp
public import StacksCore.Tactic.StacksAttribute

/-!
# Dividing a groupoid scheme by a finite locally free subgroupoid

Let `(U, R, s, t, c)` be a groupoid scheme over `S` and let `(U, P, s|_P, t|_P, c|_P)` be a
subgroupoid with `s|_P` and `t|_P` finite locally free, with `j|_P = (t|_P, s|_P) : P ⟶ U ×_S U`
a monomorphism, and with `U` affine. Then `U/P` is representable by an affine scheme `Ū`, the
quotient morphism `U ⟶ Ū` is finite locally free and surjective, and `P = U ×_Ū U`. If moreover
`j : R ⟶ U ×_S U` is separated and locally quasi-finite, then `R` is the restriction of a
groupoid scheme on `Ū` along `U ⟶ Ū`. This is Tag 04S4.

The first three conclusions are Tag 03BM, once the hypotheses of Tag 04S4 are seen to give those
of Tag 03BM: the arrow scheme of `P` is affine because `s|_P` is finite locally free over an
affine scheme, and `(t|_P, s|_P)` is an equivalence relation because `j|_P` is a monomorphism
and the groupoid laws already make the induced relation on generalized points an equivalence.

The last conclusion follows the source. The identification `P = U ×_Ū U` makes the arrows of
`P` a system of quotient arrows `[a, b]` for `U ⟶ Ū` inside `R`, and the twist
`r ↦ [a, t r] ∘ r ∘ [s r, b]` is a descent datum for `R` over `U ×_S U` relative to the finite
locally free surjection `U ×_S U ⟶ Ū ×_S Ū`. It is effective by Tag 02W8, which produces `R̄`
over `Ū ×_S Ū` with `R = (U ×_S U) ×_{Ū ×_S Ū} R̄`. Two arrows of `R` have the same image in
`R̄` exactly when they differ by twisting, so the identity, the inverse and the composition of
`R` are invariant, and they descend along the fppf covering `U ⟶ Ū` to a groupoid structure on
`(Ū, R̄)` of which `R` is the restriction.

## Main definitions

* `AlgebraicGeometry.GroupoidQuotientArrows.ofSubgroupoid`: the system of quotient arrows that
  a subgroupoid supplies when its arrows are the kernel pair of a morphism out of the objects.
* `AlgebraicGeometry.GroupoidQuotientArrows.arrowTransport`: the twist, as a descent transport
  for the arrow scheme over `U ×_S U` along `U ×_S U ⟶ Ū ×_S Ū`; this is the descent datum `φ`
  of the source.

## Main results

* `AlgebraicGeometry.isAffine_arrows_of_isFiniteLocallyFree_source`: the arrow scheme of a
  groupoid scheme with affine object scheme and finite locally free source map is affine.
* `AlgebraicGeometry.isEquivalenceRelation_of_mono_groupoidPreRelation`: the target and the
  source of a groupoid scheme form an internal equivalence relation as soon as the pre-relation
  they induce is a monomorphism.
* `AlgebraicGeometry.GroupoidQuotientArrows.exists_evaluationMk_eq` and
  `AlgebraicGeometry.GroupoidQuotientArrows.comp_eq_of_evaluationMk_eq`: two arrows have the
  same image in the descended arrow scheme exactly when they differ by twisting.
* `AlgebraicGeometry.GroupoidQuotientArrows.exists_groupoid_division`: a groupoid scheme with a
  system of quotient arrows for a finite locally free surjection `U ⟶ Ū`, whose `j` is
  separated, locally quasi-finite and locally of finite type, is the restriction of a groupoid
  scheme on `Ū`.
* `AlgebraicGeometry.exists_finiteFlatQuotient_isAffine_of_mono_groupoidPreRelation`: **Tag
  04S4**, all four conclusions.

## Implementation notes

The subgroupoid is a morphism of groupoid schemes `i : P ⟶ R` which is an isomorphism on
objects. The source's condition that `P ⟶ R` be a monomorphism is not assumed: it follows from
`j|_P` being one, and the proof does not use it.

The first three conclusions are packaged as `Stacks.Groupoids.FiniteFlatQuotient` together with
affineness of its quotient scheme, which is the shape Tag 03BM is recorded in by
`AlgebraicGeometry.affineFiniteFlatQuotient`: the quotient scheme is the spectrum of the ring of
invariant functions, so affineness of `Ū` is immediate from `AlgebraicGeometry.quotientOver_left`.
Surjectivity of `U ⟶ Ū`, which the source does not state, is part of that structure.

The descent of the arrow scheme is `AlgebraicGeometry.exists_effectiveTransport`, which is
Tag 02W8 (`AlgebraicGeometry.DescentDatum.isEffective_of_isSeparated_of_locallyQuasiFinite`)
for a descent datum given on generalized points; the covering `U ×_S U ⟶ Ū ×_S Ū` is
surjective, flat and quasi-compact by `AlgebraicGeometry.surjective_pairCover`,
`AlgebraicGeometry.flat_pairCover` and `AlgebraicGeometry.quasiCompact_pairCover`. Tag 02W8
asks `j` to be locally of finite type as well, which is part of the source's notion of a locally
quasi-finite morphism (Tag 01TD) and a separate class here.

The structure morphisms are descended by `AlgebraicGeometry.exists_descendedOperations` and
assembled into a groupoid by `AlgebraicGeometry.DescendedOperations.exists_groupoid`, in the
fppf topology on schemes over `S`, which is subcanonical, so that singleton fppf coverings are
effective epimorphisms. The restriction is expressed by a morphism of groupoid schemes `G ⟶ K`
which is the quotient morphism on objects and whose square of arrow schemes over the pairs of
objects is cartesian; there is no category of groupoid schemes in this library in which to state
it as an isomorphism with a restricted groupoid.

## References

* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 0232](https://stacks.math.columbia.edu/tag/0232)
* [Stacks Project, Tag 022P](https://stacks.math.columbia.edu/tag/022P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids Stacks.Morphisms

noncomputable section

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- The arrow scheme of a groupoid scheme whose object scheme is affine and whose source map is
finite locally free is affine: a finite locally free morphism is affine, and a scheme affine over
an affine scheme is affine. -/
alias isAffine_arrows_of_isFiniteLocallyFree_source := arrows_isAffine

/-- **The target and the source of a groupoid scheme form an internal equivalence relation as
soon as the pre-relation they induce is a monomorphism.** The groupoid laws already make the
relation induced on the generalized points of every test scheme an equivalence relation, by Tag
0232, so monicity of `j = (t, s)` is the only thing left to ask for. -/
theorem isEquivalenceRelation_of_mono_groupoidPreRelation (G : GroupoidScheme S)
    [Mono (groupoidPreRelation G)] : IsEquivalenceRelation G.target G.source :=
  (isEquivalenceRelation_iff_mono_prodLift G.target G.source).2
    ⟨inferInstance, groupoidPreRelation_isPreEquivalenceRelation G⟩

namespace GroupoidQuotientArrows

/-! ### The quotient arrows of a subgroupoid whose arrows are a kernel pair -/

section Subgroupoid

variable {G H : GroupoidScheme S} (i : GroupoidScheme.Hom H G) [IsIso i.mapObjects]
  {Ub : Over S} {q : H.objects ⟶ Ub} (hq : IsPullback H.target H.source q q)

/-- The arrow of the subgroupoid from `y` to `x`, for two generalized points of the objects of
the ambient groupoid with the same image in the quotient. -/
def subgroupoidArrow {T : Over S} (x y : T ⟶ G.objects)
    (h : x ≫ inv i.mapObjects ≫ q = y ≫ inv i.mapObjects ≫ q) : T ⟶ H.arrows :=
  hq.lift (x ≫ inv i.mapObjects) (y ≫ inv i.mapObjects) (by simpa only [Category.assoc] using h)

/-- The target of the subgroupoid arrow from `y` to `x` is `x`. -/
@[simp]
lemma subgroupoidArrow_target {T : Over S} (x y : T ⟶ G.objects)
    (h : x ≫ inv i.mapObjects ≫ q = y ≫ inv i.mapObjects ≫ q) :
    subgroupoidArrow i hq x y h ≫ H.target = x ≫ inv i.mapObjects :=
  hq.lift_fst _ _ _

/-- The source of the subgroupoid arrow from `y` to `x` is `y`. -/
@[simp]
lemma subgroupoidArrow_source {T : Over S} (x y : T ⟶ G.objects)
    (h : x ≫ inv i.mapObjects ≫ q = y ≫ inv i.mapObjects ≫ q) :
    subgroupoidArrow i hq x y h ≫ H.source = y ≫ inv i.mapObjects :=
  hq.lift_snd _ _ _

/-- The subgroupoid arrow from `y` to `x` is the pullback along `(x, y)` of the subgroupoid arrow
between the two projections of the fibre product `U ×_Ū U`. -/
lemma lift_subgroupoidArrow {T : Over S} (x y : T ⟶ G.objects)
    (h : x ≫ inv i.mapObjects ≫ q = y ≫ inv i.mapObjects ≫ q) :
    pullback.lift x y h ≫ subgroupoidArrow i hq (pullback.fst _ _) (pullback.snd _ _)
        pullback.condition = subgroupoidArrow i hq x y h :=
  hq.hom_ext (by simp only [Category.assoc, subgroupoidArrow_target, pullback.lift_fst_assoc])
    (by simp only [Category.assoc, subgroupoidArrow_source, pullback.lift_snd_assoc])

/-- The arrows of the subgroupoid compose as the pairs of points they join. -/
lemma compose_subgroupoidArrow {T : Over S} (x y z : T ⟶ G.objects)
    (hxy : x ≫ inv i.mapObjects ≫ q = y ≫ inv i.mapObjects ≫ q)
    (hyz : y ≫ inv i.mapObjects ≫ q = z ≫ inv i.mapObjects ≫ q)
    (w : subgroupoidArrow i hq x y hxy ≫ H.source = subgroupoidArrow i hq y z hyz ≫ H.target) :
    H.compose (subgroupoidArrow i hq x y hxy) (subgroupoidArrow i hq y z hyz) w =
      subgroupoidArrow i hq x z (hxy.trans hyz) :=
  hq.hom_ext (by simp [groupoidCompose_target]) (by simp [groupoidCompose_source])

/-- **The quotient arrows a subgroupoid supplies.** If the arrows of a groupoid scheme `H`
mapping to `G` by a morphism which is an isomorphism on objects form the kernel pair of
`q : U ⟶ Ū`, then the image in `G` of the arrow of `H` joining two points of `U` with the same
image in `Ū` is a system of quotient arrows for `U ⟶ Ū`. -/
def ofSubgroupoid : GroupoidQuotientArrows G (inv i.mapObjects ≫ q) where
  hom := subgroupoidArrow i hq (pullback.fst _ _) (pullback.snd _ _) pullback.condition ≫
    i.mapArrows
  hom_target := by
    rw [Category.assoc, i.map_target, ← Category.assoc, subgroupoidArrow_target,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  hom_source := by
    rw [Category.assoc, i.map_source, ← Category.assoc, subgroupoidArrow_source,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  hom_comp := by
    intro T a b c hab hbc
    have e : ∀ (x y : T ⟶ G.objects)
        (h : x ≫ inv i.mapObjects ≫ q = y ≫ inv i.mapObjects ≫ q),
        pullback.lift x y h ≫ subgroupoidArrow i hq (pullback.fst _ _) (pullback.snd _ _)
            pullback.condition ≫ i.mapArrows = subgroupoidArrow i hq x y h ≫ i.mapArrows :=
      fun x y h ↦ by rw [← Category.assoc, lift_subgroupoidArrow]
    have w : subgroupoidArrow i hq a b hab ≫ H.source =
        subgroupoidArrow i hq b c hbc ≫ H.target := by simp
    have w' : (subgroupoidArrow i hq a b hab ≫ i.mapArrows) ≫ G.source =
        (subgroupoidArrow i hq b c hbc ≫ i.mapArrows) ≫ G.target := by
      rw [Category.assoc, Category.assoc, i.map_source, i.map_target, ← Category.assoc,
        ← Category.assoc, w]
    calc _ = G.compose (subgroupoidArrow i hq a b hab ≫ i.mapArrows)
          (subgroupoidArrow i hq b c hbc ≫ i.mapArrows) w' :=
          groupoidCompose_arrow_eq _ _ _ _ _ _ (e a b hab) (e b c hbc)
      _ = H.compose (subgroupoidArrow i hq a b hab) (subgroupoidArrow i hq b c hbc) w ≫
          i.mapArrows := (i.map_comp T _ _ w w').symm
      _ = subgroupoidArrow i hq a c (hab.trans hbc) ≫ i.mapArrows := by
          rw [compose_subgroupoidArrow]
      _ = _ := (e a c (hab.trans hbc)).symm

end Subgroupoid

/-! ### The twist as a descent transport along `U ×_S U ⟶ Ū ×_S Ū` -/

section Transport

variable {G : GroupoidScheme S} {Ub : Over S} {q : G.objects ⟶ Ub}
  (K : GroupoidQuotientArrows G q)

section Points

variable {T : Over (Ub ⨯ Ub)} (a : T ⟶ Over.mk (groupoidPreRelation G ≫ prod.map q q))
  (b : T ⟶ Over.mk (prod.map q q))

/-- For an arrow `a` and a pair of points `b` over the same point of `Ū ×_S Ū`, the first point
of `b` and the target of `a` have the same image in `Ū`. -/
lemma transport_target : (b.left ≫ prod.fst) ≫ q = (a.left ≫ G.target) ≫ q := by
  simpa only [Over.mk_hom, Category.assoc, prod.map_fst, groupoidPreRelation,
    prod.lift_fst_assoc] using (congrArg (· ≫ (prod.fst : (Ub ⨯ Ub : Over S) ⟶ Ub))
      ((Over.w a).trans (Over.w b).symm)).symm

/-- For an arrow `a` and a pair of points `b` over the same point of `Ū ×_S Ū`, the source of `a`
and the second point of `b` have the same image in `Ū`. -/
lemma transport_source : (a.left ≫ G.source) ≫ q = (b.left ≫ prod.snd) ≫ q := by
  simpa only [Over.mk_hom, Category.assoc, prod.map_snd, groupoidPreRelation,
    prod.lift_snd_assoc] using congrArg (· ≫ (prod.snd : (Ub ⨯ Ub : Over S) ⟶ Ub))
      ((Over.w a).trans (Over.w b).symm)

/-- The arrow underlying `a`, twisted onto the pair of points `b`. -/
def transportHom : T.left ⟶ G.arrows :=
  K.twistHom a.left rfl rfl (transport_target a b) (transport_source a b)

/-- The twisted arrow joins the pair of points `b`: its image under `j = (t, s)` is `b`. -/
lemma transportHom_preRelation : K.transportHom a b ≫ groupoidPreRelation G = b.left := by
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, prod.lift_fst, transportHom, twistHom_target]
  · rw [Category.assoc, prod.lift_snd, transportHom, twistHom_source]

end Points

/-- **The twist, as a descent transport** for the arrow scheme over `U ×_S U` relative to
`U ×_S U ⟶ Ū ×_S Ū`: an arrow `r` and a point `(a, b)` of `U ×_S U` over the same point of
`Ū ×_S Ū` go to `[a, t r] ∘ r ∘ [s r, b]`.  This is the descent datum `φ` of the source. -/
def arrowTransport : DescentTransport (Over.homMk (groupoidPreRelation G) :
    Over.mk (groupoidPreRelation G ≫ prod.map q q) ⟶ Over.mk (prod.map q q)) where
  move a b := Over.homMk (K.transportHom a b) (by
    simp only [Over.mk_hom]
    rw [← Category.assoc, K.transportHom_preRelation]
    exact Over.w b)
  base a b := Over.OverMorphism.ext (K.transportHom_preRelation a b)
  refl a := Over.OverMorphism.ext (by
    simp only [Over.homMk_left, transportHom]
    apply K.twistHom_self <;> simp [groupoidPreRelation])
  trans a b c := Over.OverMorphism.ext
    (K.twistHom_twistHom a.left rfl rfl _ _ rfl rfl _ _ _ _)
  naturality f a b := Over.OverMorphism.ext
    (K.twistHom_pre a.left rfl rfl _ _ f.left rfl rfl _ _ (Category.assoc _ _ _)
      (Category.assoc _ _ _) (Category.assoc _ _ _) (Category.assoc _ _ _))

/-- A morphism out of the arrow scheme invariant for the transport is invariant for every
twist. -/
lemma twistHom_comp_of_transport {A : Over S} {r : G.arrows ⟶ A}
    (hr : ∀ {T : Over (Ub ⨯ Ub)} (a : T ⟶ Over.mk (groupoidPreRelation G ≫ prod.map q q))
      (b : T ⟶ Over.mk (prod.map q q)), (K.arrowTransport.move a b).left ≫ r = a.left ≫ r)
    {T : Over S} (f : T ⟶ G.arrows) {x y a b : T ⟶ G.objects} (hx : f ≫ G.source = x)
    (hy : f ≫ G.target = y) (ha : a ≫ q = y ≫ q) (hb : x ≫ q = b ≫ q) :
    K.twistHom f hx hy ha hb ≫ r = f ≫ r := by
  subst hx hy
  let T' : Over (Ub ⨯ Ub) := Over.mk (f ≫ groupoidPreRelation G ≫ prod.map q q)
  let aa : T' ⟶ Over.mk (groupoidPreRelation G ≫ prod.map q q) := Over.homMk f
  let bb : T' ⟶ Over.mk (prod.map q q) := Over.homMk (prod.lift a b) (by
    refine prod.hom_ext ?_ ?_
    · simpa only [T', Over.mk_hom, Category.assoc, prod.map_fst, prod.lift_fst_assoc,
        groupoidPreRelation] using ha
    · simpa only [T', Over.mk_hom, Category.assoc, prod.map_snd, prod.lift_snd_assoc,
        groupoidPreRelation] using hb.symm)
  have e : K.twistHom f rfl rfl ha hb =
      K.twistHom aa.left rfl rfl (transport_target aa bb) (transport_source aa bb) :=
    K.twistHom_congr _ _ _ _ _ _ _ _ rfl (by simp [bb]) (by simp [bb])
  rw [e]
  exact hr aa bb

end Transport

/-! ### Invariance of the descended arrow scheme under the groupoid operations -/

section Invariance

variable {G : GroupoidScheme S} {Ub : Over S} {q : G.objects ⟶ Ub}
  (K : GroupoidQuotientArrows G q) {A : Over S} {r : G.arrows ⟶ A} {j : A ⟶ Ub ⨯ Ub}
  (hp : IsPullback r (groupoidPreRelation G) j (prod.map q q))
  (hr : ∀ {T : Over S} (f : T ⟶ G.arrows) {x y a b : T ⟶ G.objects}
    (hx : f ≫ G.source = x) (hy : f ≫ G.target = y) (ha : a ≫ q = y ≫ q)
    (hb : x ≫ q = b ≫ q), K.twistHom f hx hy ha hb ≫ r = f ≫ r)
include hp

omit hp in
/-- The identity arrow at a point `x` evaluates to the identity of `x`. -/
lemma evaluationMk_identity {T : Over S} (x : T ⟶ G.objects)
    (h₁ : (x ≫ G.identity) ≫ G.source = x) (h₂ : (x ≫ G.identity) ≫ G.target = x) :
    evaluationMk (x ≫ G.identity) h₁ h₂ = 𝟙 (evalObj x) :=
  GroupoidScheme.EvaluationHom.ext rfl

omit hp in
/-- The inverse of an arrow evaluates to the inverse of its evaluation. -/
lemma evaluationMk_inverse {T : Over S} (f : T ⟶ G.arrows) {x y : T ⟶ G.objects}
    (hx : f ≫ G.source = x) (hy : f ≫ G.target = y)
    (hx' : (f ≫ G.inverse) ≫ G.source = y) (hy' : (f ≫ G.inverse) ≫ G.target = x) :
    evaluationMk (f ≫ G.inverse) hx' hy' = inv (evaluationMk f hx hy) := by
  rw [← Groupoid.inv_eq_inv]
  rfl

omit hp in
/-- The composition of two arrows evaluates to the composition of their evaluations. -/
lemma evaluationMk_compose {T : Over S} (f g : T ⟶ G.arrows) (w : f ≫ G.source = g ≫ G.target)
    {x m y : T ⟶ G.objects} (hgx : g ≫ G.source = x) (hgm : g ≫ G.target = m)
    (hfm : f ≫ G.source = m) (hfy : f ≫ G.target = y)
    (hx : G.compose f g w ≫ G.source = x) (hy : G.compose f g w ≫ G.target = y) :
    evaluationMk (G.compose f g w) hx hy = evaluationMk g hgx hgm ≫ evaluationMk f hfm hfy :=
  GroupoidScheme.EvaluationHom.ext rfl

omit hp in
/-- The inverse of the quotient arrow from `b` to `a` is the quotient arrow from `a` to `b`. -/
lemma inv_rel {T : Over S} {a b : T ⟶ G.objects} (h : a ≫ q = b ≫ q) :
    inv (K.rel h) = K.rel h.symm := by
  apply IsIso.inv_eq_of_hom_inv_id
  rw [K.rel_comp, K.rel_refl]

/-- The second projection of the descended arrow scheme lifts the source map along `q`. -/
lemma source_comp_eq : r ≫ j ≫ prod.snd = G.source ≫ q := by
  simpa [groupoidPreRelation] using congrArg (· ≫ prod.snd) hp.w

/-- The first projection of the descended arrow scheme lifts the target map along `q`. -/
lemma target_comp_eq : r ≫ j ≫ prod.fst = G.target ≫ q := by
  simpa [groupoidPreRelation] using congrArg (· ≫ prod.fst) hp.w

include hr in
/-- **Two arrows with the same image differ by twisting.** -/
lemma exists_evaluationMk_eq {T : Over S} {f g : T ⟶ G.arrows} (h : f ≫ r = g ≫ r)
    {x y x' y' : T ⟶ G.objects} (hx : f ≫ G.source = x) (hy : f ≫ G.target = y)
    (hx' : g ≫ G.source = x') (hy' : g ≫ G.target = y') :
    ∃ (h₁ : x ≫ q = x' ≫ q) (h₂ : y' ≫ q = y ≫ q),
      evaluationMk g hx' hy' = K.rel h₁ ≫ evaluationMk f hx hy ≫ K.rel h₂ := by
  have key : ∀ (p : Ub ⨯ Ub ⟶ Ub) (c : G.arrows ⟶ G.objects) {u v : T ⟶ G.objects},
      r ≫ j ≫ p = c ≫ q → f ≫ c = u → g ≫ c = v → u ≫ q = v ≫ q := by
    rintro p c u v hc rfl rfl
    rw [Category.assoc, Category.assoc, ← hc, reassoc_of% h]
  have h₁ := key _ _ (source_comp_eq hp) hx hx'
  have h₂ := (key _ _ (target_comp_eq hp) hy hy').symm
  refine ⟨h₁, h₂, ?_⟩
  apply GroupoidScheme.EvaluationHom.ext
  show g = K.twistHom f hx hy h₂ h₁
  apply hp.hom_ext
  · rw [hr, h]
  · refine prod.hom_ext ?_ ?_
    · simp only [groupoidPreRelation, Category.assoc, prod.lift_fst, hy', twistHom_target]
    · simp only [groupoidPreRelation, Category.assoc, prod.lift_snd, hx', twistHom_source]

omit hp in
include hr in
/-- **Two arrows differing by twisting have the same image.** -/
lemma comp_eq_of_evaluationMk_eq {T : Over S} {f g : T ⟶ G.arrows}
    {x y x' y' : T ⟶ G.objects} (hx : f ≫ G.source = x) (hy : f ≫ G.target = y)
    (hx' : g ≫ G.source = x') (hy' : g ≫ G.target = y') (h₁ : x ≫ q = x' ≫ q)
    (h₂ : y' ≫ q = y ≫ q)
    (h : evaluationMk g hx' hy' = K.rel h₁ ≫ evaluationMk f hx hy ≫ K.rel h₂) :
    g ≫ r = f ≫ r := by
  rw [show g = K.twistHom f hx hy h₂ h₁ from congrArg GroupoidScheme.EvaluationHom.arrow h, hr]

omit hp in
include hr in
/-- The identity descends: two identity arrows at points with the same image in `Ū` have the
same image. -/
lemma identity_comp_eq {T : Over S} (x y : T ⟶ G.objects) (hxy : x ≫ q = y ≫ q) :
    x ≫ G.identity ≫ r = y ≫ G.identity ≫ r := by
  have hs : ∀ z : T ⟶ G.objects, (z ≫ G.identity) ≫ G.source = z := fun z ↦ by
    rw [Category.assoc, G.source_identity, Category.comp_id]
  have ht : ∀ z : T ⟶ G.objects, (z ≫ G.identity) ≫ G.target = z := fun z ↦ by
    rw [Category.assoc, G.target_identity, Category.comp_id]
  have h := K.comp_eq_of_evaluationMk_eq hr (hs x) (ht x) (hs y) (ht y) hxy hxy.symm (by
    rw [evaluationMk_identity, evaluationMk_identity, Category.id_comp, K.rel_comp, K.rel_refl])
  simpa only [Category.assoc] using h.symm

include hr in
/-- The inverse descends. -/
lemma inverse_comp_eq {T : Over S} (a b : T ⟶ G.arrows) (h : a ≫ r = b ≫ r) :
    a ≫ G.inverse ≫ r = b ≫ G.inverse ≫ r := by
  obtain ⟨h₁, h₂, he⟩ := K.exists_evaluationMk_eq hp hr h rfl rfl rfl rfl
  have hs : ∀ c : T ⟶ G.arrows, (c ≫ G.inverse) ≫ G.source = c ≫ G.target := fun c ↦ by
    rw [Category.assoc, G.source_inverse]
  have ht : ∀ c : T ⟶ G.arrows, (c ≫ G.inverse) ≫ G.target = c ≫ G.source := fun c ↦ by
    rw [Category.assoc, G.target_inverse]
  have h' := K.comp_eq_of_evaluationMk_eq hr (hs a) (ht a) (hs b) (ht b) h₂.symm h₁.symm (by
    rw [evaluationMk_inverse b rfl rfl, evaluationMk_inverse a rfl rfl, he, IsIso.inv_comp,
      IsIso.inv_comp, K.inv_rel, K.inv_rel, Category.assoc])
  simpa only [Category.assoc] using h'.symm

include hr in
/-- The composition descends. -/
lemma compose_comp_eq {T : Over S} (a b c d : T ⟶ G.arrows) (w : a ≫ G.source = b ≫ G.target)
    (w' : c ≫ G.source = d ≫ G.target) (hac : a ≫ r = c ≫ r) (hbd : b ≫ r = d ≫ r) :
    G.compose a b w ≫ r = G.compose c d w' ≫ r := by
  obtain ⟨h₁, h₂, hca⟩ := K.exists_evaluationMk_eq hp hr hac rfl rfl rfl rfl
  obtain ⟨h₃, h₄, hdb⟩ := K.exists_evaluationMk_eq hp hr hbd rfl w.symm rfl w'.symm
  exact (K.comp_eq_of_evaluationMk_eq hr (groupoidCompose_source G a b w)
    (groupoidCompose_target G a b w) (groupoidCompose_source G c d w')
    (groupoidCompose_target G c d w') h₃ h₂ (by
      rw [evaluationMk_compose c d w' rfl w'.symm rfl rfl, hca, hdb,
        evaluationMk_compose a b w rfl w.symm rfl rfl]
      simp only [Category.assoc]
      rw [← Category.assoc (K.rel h₄), K.rel_comp, K.rel_refl, Category.id_comp])).symm

end Invariance

/-! ### The groupoid on the quotient -/

/-- A finite locally free surjection generates a covering sieve of the fppf topology on
schemes over `S`. -/
lemma singletonCover_fppf {X Y : Over S} (f : X ⟶ Y) [IsFiniteLocallyFree f.left]
    [Surjective f.left] : SingletonCover (Scheme.fppfTopology.over S) f := by
  have := IsFiniteLocallyFree.flat f.left
  have := IsFiniteLocallyFree.locallyOfFinitePresentation f.left
  rw [SingletonCover, ← Sieve.generateSingleton_eq, GrothendieckTopology.mem_over_iff]
  show Sieve.functorPushforward (Over.forget S) (Sieve.generate (Presieve.singleton f)) ∈
    Scheme.fppfTopology Y.left
  rw [← Sieve.generate_map_eq_functorPushforward, Presieve.map_singleton]
  exact Precoverage.generate_mem_toGrothendieck f.left.singleton_mem_fppfPrecoverage

/-- **The groupoid descends along a finite locally free quotient of its objects.** Let
`q : U ⟶ Ū` be surjective and finite locally free, with a system of quotient arrows, and let
`j = (t, s) : R ⟶ U ×_S U` be separated, locally quasi-finite and locally of finite type.  Then
there is a groupoid scheme on `Ū` and a morphism from `G` to it, equal to `q` on objects, whose
square of arrow schemes over the pairs of objects is cartesian: `G` is the restriction of the
groupoid on `Ū` along `q`, and in particular it is fully faithful on the generalized points of
every test scheme.

The arrow scheme descends by Tag 02W8 along `U ×_S U ⟶ Ū ×_S Ū` with the descent datum
`AlgebraicGeometry.GroupoidQuotientArrows.arrowTransport`, and the structure morphisms descend
by `AlgebraicGeometry.exists_descendedOperations`. -/
theorem exists_groupoid_division {G : GroupoidScheme S} {Ub : Over S} {q : G.objects ⟶ Ub}
    (K : GroupoidQuotientArrows G q) [Surjective q.left] [IsFiniteLocallyFree q.left]
    [IsSeparated (groupoidPreRelation G).left] [LocallyQuasiFinite (groupoidPreRelation G).left]
    [LocallyOfFiniteType (groupoidPreRelation G).left] :
    ∃ (K' : GroupoidScheme S) (he : K'.objects = Ub) (F : GroupoidScheme.Hom G K'),
      F.mapObjects = q ≫ eqToHom he.symm ∧
        IsPullback F.mapArrows (groupoidPreRelation G) (groupoidPreRelation K')
          (prod.map F.mapObjects F.mapObjects) ∧
        ∀ T : Over S, Nonempty (F.evaluation T).FullyFaithful := by
  obtain ⟨A, j, r, hp, hr⟩ :=
    exists_effectiveTransport (groupoidPreRelation G) (prod.map q q) K.arrowTransport
  have hj : prod.lift (j ≫ prod.fst) (j ≫ prod.snd) = j := by
    refine prod.hom_ext ?_ ?_ <;> simp
  have hp' : IsPullback r (prod.lift G.target G.source)
      (prod.lift (j ≫ prod.fst) (j ≫ prod.snd)) (prod.map q q) := by
    rwa [hj]
  have hq := singletonCover_fppf q
  obtain ⟨D⟩ := exists_descendedOperations q r (j ≫ prod.snd) (j ≫ prod.fst) hp' hq
    (K.identity_comp_eq (K.twistHom_comp_of_transport hr))
    (K.inverse_comp_eq hp (K.twistHom_comp_of_transport hr))
    (K.compose_comp_eq hp (K.twistHom_comp_of_transport hr))
  exact D.exists_groupoid hp' hq

end GroupoidQuotientArrows

/-- **Stacks Project, Tag 04S4.** Let `(U, R, s, t, c)` be a groupoid scheme `G` over `S` and
let `(U, P, s|_P, t|_P, c|_P)` be a groupoid scheme `H` mapping to it by a morphism `i` which is
an isomorphism on objects, such that

1. `s|_P, t|_P : P ⟶ U` are finite locally free,
2. `j|_P = (t|_P, s|_P) : P ⟶ U ×_S U` is a monomorphism,
3. `U` is affine, and
4. `j = (t, s) : R ⟶ U ×_S U` is separated and locally quasi-finite (locally of finite type
   with finite fibres; the finite type half is a separate class here).

Then `U/P` is representable by an affine scheme `Ū`, the quotient morphism `U ⟶ Ū` is finite
locally free (and surjective), and `P = U ×_Ū U`; these are the fields of
`Stacks.Groupoids.FiniteFlatQuotient` together with affineness of its quotient scheme.
Moreover `R` is the restriction of a groupoid scheme on `Ū` along the quotient morphism: there
is a groupoid scheme `K` with object scheme `Ū` and a morphism `G ⟶ K` which is the quotient
morphism on objects and whose square of arrow schemes over the pairs of objects is cartesian,
`R = (U ×_S U) ×_{Ū ×_S Ū} R̄`; equivalently, it is fully faithful on the generalized points of
every test scheme.

The source asks in addition that `P ⟶ R` be a monomorphism; this follows from the other
hypotheses (`j ∘ i = (i × i) ∘ j|_P` is a monomorphism) and is not used. -/
@[stacks 04S4, sga "3 V 4.1" "special case"]
theorem exists_finiteFlatQuotient_isAffine_of_mono_groupoidPreRelation (G H : GroupoidScheme S)
    (i : GroupoidScheme.Hom H G) [IsIso i.mapObjects]
    [IsFiniteLocallyFree H.source.left] [IsFiniteLocallyFree H.target.left]
    [Mono (groupoidPreRelation H)] [IsAffine G.objects.left]
    [IsSeparated (groupoidPreRelation G).left] [LocallyQuasiFinite (groupoidPreRelation G).left]
    [LocallyOfFiniteType (groupoidPreRelation G).left] :
    ∃ Q : FiniteFlatQuotient H, IsAffine Q.space.left ∧
      ∃ (K : GroupoidScheme S) (he : K.objects = Q.space) (F : GroupoidScheme.Hom G K),
        F.mapObjects = (inv i.mapObjects ≫ Q.quotientMap) ≫ eqToHom he.symm ∧
          IsPullback F.mapArrows (groupoidPreRelation G) (groupoidPreRelation K)
            (prod.map F.mapObjects F.mapObjects) ∧
          ∀ T : Over S, Nonempty (F.evaluation T).FullyFaithful := by
  have : IsIso i.mapObjects.left := (Over.forget S).map_isIso i.mapObjects
  have : IsAffine H.objects.left := IsAffine.of_isIso i.mapObjects.left
  have _ : IsAffine H.arrows.left := isAffine_arrows_of_isFiniteLocallyFree_source H
  have _ : IsEquivalenceRelation H.target H.source :=
    isEquivalenceRelation_of_mono_groupoidPreRelation H
  have hQ : IsAffine (quotientOver H).left := by
    rw [quotientOver_left]
    infer_instance
  let Q : FiniteFlatQuotient H := affineFiniteFlatQuotient H
  refine ⟨Q, hQ, ?_⟩
  have := Q.finiteLocallyFree
  have := Q.surjective
  have : IsIso (inv i.mapObjects).left := (Over.forget S).map_isIso (inv i.mapObjects)
  have : IsFiniteLocallyFree (inv i.mapObjects).left :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
      ⟨inferInstance, inferInstance, inferInstance⟩
  have : IsFiniteLocallyFree (inv i.mapObjects ≫ Q.quotientMap).left :=
    isFiniteLocallyFree_comp (inv i.mapObjects).left Q.quotientMap.left
  have : Surjective (inv i.mapObjects ≫ Q.quotientMap).left := by
    rw [Over.comp_left]
    infer_instance
  exact (GroupoidQuotientArrows.ofSubgroupoid i Q.kernelPair).exists_groupoid_division

end AlgebraicGeometry

end

end
