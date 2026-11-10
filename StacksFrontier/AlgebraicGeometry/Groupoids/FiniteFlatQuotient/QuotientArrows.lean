module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Compose
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Evaluation

/-!
# Arrows of a groupoid scheme indexed by a kernel pair of its object scheme

Let `G = (U, R, s, t, c)` be a groupoid scheme over `S` and let `q : U ⟶ Ū` be a morphism.
A *system of quotient arrows* for `q` is a morphism `U ×_Ū U ⟶ R` whose target and source are
the two projections and whose values compose: for generalized points `a, b, c` of `U` with the
same image in `Ū` the arrows `[a, b] : b ⟶ a` and `[b, c] : c ⟶ b` compose to `[a, c]`.

This is the structure which the finite locally free subgroupoid of Tag 04S4 provides on the
quotient of its object scheme, and it is the only input the descent of the ambient arrow scheme
along `U ×_S U ⟶ Ū ×_S Ū` uses.  The construction that descent needs is the *twist*
`r ↦ [a, t r] ∘ r ∘ [s r, b]`, which moves an arrow of `R` to the arrow with prescribed source
`b` and target `a` in the same fibres of `q`; the two laws it obeys are that twisting an arrow
by its own source and target does nothing, and that twisting twice is twisting once.  Those are
exactly the normalization and the cocycle condition of the descent datum built from it.

## Main definitions

* `AlgebraicGeometry.GroupoidQuotientArrows` is the structure described above.
* `AlgebraicGeometry.GroupoidQuotientArrows.rel` is the arrow `[a, b]`, as a morphism of the
  groupoid of generalized points.
* `AlgebraicGeometry.GroupoidQuotientArrows.twistHom` is the twist described above.

## Main results

* `AlgebraicGeometry.GroupoidQuotientArrows.rel_comp`, `..._refl` and
  `AlgebraicGeometry.GroupoidQuotientArrows.relHom_pre`: the three rules the arrows `[a, b]`
  obey.
* `AlgebraicGeometry.GroupoidQuotientArrows.twistHom_self` and
  `AlgebraicGeometry.GroupoidQuotientArrows.twistHom_twistHom`: the two laws of the twist.

## Implementation notes

The composition law is stated on generalized points because the witness that two points of `U`
agree over `Ū` appears in the type of the lift into `U ×_Ū U`, so the composable pairs do not
form a scheme-level fibre product that avoids naming the test object.  The calculus is then
carried out in the groupoid `Stacks.Groupoids.GroupoidScheme.Evaluation` of generalized points,
where associativity and the identity laws are those of a category, and the results are read back
as identities between morphisms into the arrow scheme.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

noncomputable section

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- A generalized point of the object scheme, as an object of the groupoid of generalized
points of a groupoid scheme. -/
abbrev evalObj {G : GroupoidScheme S} {T : Over S} (x : T ⟶ G.objects) : G.Evaluation T := x

/-- A generalized arrow with prescribed source and target, as a morphism of the groupoid of
generalized points of a groupoid scheme. -/
def evaluationMk {G : GroupoidScheme S} {T : Over S} (r : T ⟶ G.arrows)
    {x y : T ⟶ G.objects} (hx : r ≫ G.source = x) (hy : r ≫ G.target = y) :
    evalObj x ⟶ evalObj y where
  arrow := r
  source_eq := hx
  target_eq := hy

@[simp]
lemma evaluationMk_arrow {G : GroupoidScheme S} {T : Over S} (r : T ⟶ G.arrows)
    {x y : T ⟶ G.objects} (hx : r ≫ G.source = x) (hy : r ≫ G.target = y) :
    (evaluationMk r hx hy).arrow = r := rfl

/-- A morphism of the groupoid of generalized points is rebuilt from its arrow. -/
lemma evaluationMk_self {G : GroupoidScheme S} {T : Over S} {x y : T ⟶ G.objects}
    (g : evalObj x ⟶ evalObj y) (hx : g.arrow ≫ G.source = x) (hy : g.arrow ≫ G.target = y) :
    evaluationMk g.arrow hx hy = g := rfl

/-- A system of arrows of `G` indexed by the kernel pair of a morphism `q` out of the object
scheme: a morphism `U ×_Ū U ⟶ R` whose target and source are the two projections and whose
values are closed under composition. -/
structure GroupoidQuotientArrows (G : GroupoidScheme S) {Ub : Over S}
    (q : G.objects ⟶ Ub) where
  /-- The arrow attached to a pair of points of `U` with the same image in `Ū`. -/
  hom : pullback q q ⟶ G.arrows
  /-- Its target is the first point of the pair. -/
  hom_target : hom ≫ G.target = pullback.fst q q
  /-- Its source is the second point of the pair. -/
  hom_source : hom ≫ G.source = pullback.snd q q
  /-- The attached arrows compose. -/
  hom_comp : ∀ {T : Over S} (a b c : T ⟶ G.objects) (hab : a ≫ q = b ≫ q)
      (hbc : b ≫ q = c ≫ q),
    G.compose (pullback.lift a b hab ≫ hom) (pullback.lift b c hbc ≫ hom)
        (by
          rw [Category.assoc, hom_source, Category.assoc, hom_target,
            pullback.lift_snd, pullback.lift_fst]) =
      pullback.lift a c (hab.trans hbc) ≫ hom

namespace GroupoidQuotientArrows

variable {G : GroupoidScheme S} {Ub : Over S} {q : G.objects ⟶ Ub}
  (K : GroupoidQuotientArrows G q)

section Arrows

variable {T : Over S}

/-- The arrow `[a, b] : b ⟶ a` attached to a pair of generalized points of `U` agreeing over
`Ū`, as a morphism into the arrow scheme. -/
def relHom {a b : T ⟶ G.objects} (h : a ≫ q = b ≫ q) : T ⟶ G.arrows :=
  pullback.lift a b h ≫ K.hom

@[simp]
lemma relHom_target {a b : T ⟶ G.objects} (h : a ≫ q = b ≫ q) :
    K.relHom h ≫ G.target = a := by
  rw [relHom, Category.assoc, K.hom_target, pullback.lift_fst]

@[simp]
lemma relHom_source {a b : T ⟶ G.objects} (h : a ≫ q = b ≫ q) :
    K.relHom h ≫ G.source = b := by
  rw [relHom, Category.assoc, K.hom_source, pullback.lift_snd]

/-- The arrow `[a, b]`, as a morphism of the groupoid of generalized points of `G` over `T`. -/
def rel {a b : T ⟶ G.objects} (h : a ≫ q = b ≫ q) : evalObj b ⟶ evalObj a :=
  evaluationMk (K.relHom h) (K.relHom_source h) (K.relHom_target h)

@[simp]
lemma rel_arrow {a b : T ⟶ G.objects} (h : a ≫ q = b ≫ q) :
    (K.rel h).arrow = K.relHom h := rfl

/-- **The attached arrows compose.** -/
lemma rel_comp {a b c : T ⟶ G.objects} (hab : a ≫ q = b ≫ q) (hbc : b ≫ q = c ≫ q) :
    K.rel hbc ≫ K.rel hab = K.rel (hab.trans hbc) := by
  apply GroupoidScheme.EvaluationHom.ext
  exact K.hom_comp a b c hab hbc

/-- **The arrow attached to a pair of equal points is the identity.** -/
lemma rel_refl {a : T ⟶ G.objects} (h : a ≫ q = a ≫ q) : K.rel h = 𝟙 (evalObj a) := by
  rw [← cancel_mono (K.rel h), Category.id_comp]
  exact K.rel_comp h h

/-- The attached arrows commute with change of test object. -/
lemma relHom_pre {T' : Over S} (k : T' ⟶ T) {a b : T ⟶ G.objects} (h : a ≫ q = b ≫ q)
    (h' : (k ≫ a) ≫ q = (k ≫ b) ≫ q) : k ≫ K.relHom h = K.relHom h' := by
  simp only [relHom, ← Category.assoc]
  congr 1
  refine pullback.hom_ext ?_ ?_ <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]

end Arrows

section Twist

variable {T : Over S} (r : T ⟶ G.arrows) {x y a b : T ⟶ G.objects}
  (hx : r ≫ G.source = x) (hy : r ≫ G.target = y)
  (ha : a ≫ q = y ≫ q) (hb : x ≫ q = b ≫ q)

/-- **The twist of a generalized arrow.** For `r : x ⟶ y` an arrow of `G` and `a`, `b` points of
`U` lying over the same points of `Ū` as `y` and `x`, the arrow `[a, y] ∘ r ∘ [x, b] : b ⟶ a`. -/
def twist : evalObj b ⟶ evalObj a :=
  K.rel hb ≫ evaluationMk r hx hy ≫ K.rel ha

/-- The twist, as a morphism into the arrow scheme. -/
def twistHom : T ⟶ G.arrows := (K.twist r hx hy ha hb).arrow

@[simp]
lemma twistHom_source : K.twistHom r hx hy ha hb ≫ G.source = b :=
  (K.twist r hx hy ha hb).source_eq

@[simp]
lemma twistHom_target : K.twistHom r hx hy ha hb ≫ G.target = a :=
  (K.twist r hx hy ha hb).target_eq

/-- The twist is recovered from the morphism into the arrow scheme that it is. -/
lemma evaluationMk_twistHom (hx' : K.twistHom r hx hy ha hb ≫ G.source = b)
    (hy' : K.twistHom r hx hy ha hb ≫ G.target = a) :
    evaluationMk (K.twistHom r hx hy ha hb) hx' hy' = K.twist r hx hy ha hb := rfl

/-- The twist, written out as an iterated composition of generalized arrows. -/
lemma twistHom_eq (w₁ : K.relHom ha ≫ G.source = r ≫ G.target)
    (w₂ : G.compose (K.relHom ha) r w₁ ≫ G.source = K.relHom hb ≫ G.target) :
    K.twistHom r hx hy ha hb = G.compose (G.compose (K.relHom ha) r w₁) (K.relHom hb) w₂ := rfl

/-- The twist depends only on the arrow and on the two points of `U` it is twisted onto. -/
lemma twistHom_congr {r₁ r₂ : T ⟶ G.arrows} {x₁ y₁ a₁ b₁ x₂ y₂ a₂ b₂ : T ⟶ G.objects}
    (hx₁ : r₁ ≫ G.source = x₁) (hy₁ : r₁ ≫ G.target = y₁) (ha₁ : a₁ ≫ q = y₁ ≫ q)
    (hb₁ : x₁ ≫ q = b₁ ≫ q) (hx₂ : r₂ ≫ G.source = x₂) (hy₂ : r₂ ≫ G.target = y₂)
    (ha₂ : a₂ ≫ q = y₂ ≫ q) (hb₂ : x₂ ≫ q = b₂ ≫ q)
    (hr : r₁ = r₂) (haa : a₁ = a₂) (hbb : b₁ = b₂) :
    K.twistHom r₁ hx₁ hy₁ ha₁ hb₁ = K.twistHom r₂ hx₂ hy₂ ha₂ hb₂ := by
  subst hr; subst haa; subst hbb; subst hx₁; subst hy₁; subst hx₂; subst hy₂; rfl

/-- **Twisting an arrow by its own source and target does nothing.** -/
lemma twistHom_self (hay : a = y) (hbx : b = x) : K.twistHom r hx hy ha hb = r := by
  subst hay; subst hbx
  rw [twistHom, twist, K.rel_refl ha, K.rel_refl hb, Category.comp_id, Category.id_comp,
    evaluationMk_arrow]

/-- **Twisting twice is twisting once.** -/
lemma twistHom_twistHom {x₂ y₂ a₂ b₂ : T ⟶ G.objects}
    (hx₂ : K.twistHom r hx hy ha hb ≫ G.source = x₂)
    (hy₂ : K.twistHom r hx hy ha hb ≫ G.target = y₂)
    (ha₂ : a₂ ≫ q = y₂ ≫ q) (hb₂ : x₂ ≫ q = b₂ ≫ q)
    (ha₃ : a₂ ≫ q = y ≫ q) (hb₃ : x ≫ q = b₂ ≫ q) :
    K.twistHom (K.twistHom r hx hy ha hb) hx₂ hy₂ ha₂ hb₂ = K.twistHom r hx hy ha₃ hb₃ := by
  obtain rfl : x₂ = b := hx₂.symm.trans (K.twistHom_source r hx hy ha hb)
  obtain rfl : y₂ = a := hy₂.symm.trans (K.twistHom_target r hx hy ha hb)
  refine congrArg GroupoidScheme.EvaluationHom.arrow ?_
  change K.rel hb₂ ≫ evaluationMk (K.twistHom r hx hy ha hb) hx₂ hy₂ ≫ K.rel ha₂ =
    K.twist r hx hy ha₃ hb₃
  rw [K.evaluationMk_twistHom r hx hy ha hb hx₂ hy₂, twist, twist,
    ← K.rel_comp ha₂ ha, ← K.rel_comp hb hb₂]
  simp only [Category.assoc]

/-- The twist commutes with change of test object. -/
lemma twistHom_pre {T' : Over S} (k : T' ⟶ T) {x' y' a' b' : T' ⟶ G.objects}
    (hx' : (k ≫ r) ≫ G.source = x') (hy' : (k ≫ r) ≫ G.target = y')
    (ha' : a' ≫ q = y' ≫ q) (hb' : x' ≫ q = b' ≫ q)
    (hxx : x' = k ≫ x) (hyy : y' = k ≫ y) (haa : a' = k ≫ a) (hbb : b' = k ≫ b) :
    k ≫ K.twistHom r hx hy ha hb = K.twistHom (k ≫ r) hx' hy' ha' hb' := by
  subst hxx; subst hyy; subst haa; subst hbb
  have eq : ∀ {T : Over S} (r : T ⟶ G.arrows) {x y a b : T ⟶ G.objects}
      (hx : r ≫ G.source = x) (hy : r ≫ G.target = y) (ha : a ≫ q = y ≫ q) (hb : x ≫ q = b ≫ q),
      K.twistHom r hx hy ha hb = G.compose (G.compose (K.relHom ha) r (by rw [K.relHom_source, hy]))
        (K.relHom hb) (by rw [groupoidCompose_source, hx, K.relHom_target]) :=
    by intros; rfl
  rw [eq, eq, groupoidCompose_pre]
  refine groupoidCompose_arrow_eq _ _ _ _ _ _ ?_ (K.relHom_pre k hb hb')
  rw [groupoidCompose_pre]
  exact groupoidCompose_arrow_eq _ _ _ _ _ _ (K.relHom_pre k ha ha') rfl

end Twist

end GroupoidQuotientArrows

end AlgebraicGeometry

end

end
