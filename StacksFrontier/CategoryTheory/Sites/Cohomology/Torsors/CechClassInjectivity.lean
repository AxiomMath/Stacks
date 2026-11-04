module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.LocalTriviality
import StacksCore.Tactic.StacksAttribute

/-!
# The Čech class determines the torsor

Let `(C, J)` be a site, let `G` be an abelian sheaf on it, let `U` be an object of `C` and let
`𝒰 = {U_i → U}` be a covering family of `U`. A torsor under `G|_U` with a section over every
member of the family has a Čech class in `Ȟ¹(𝒰, G)`, the class of the cocycle of differences
of the local sections (`Stacks.Cohomology.Torsors.cechClass`). This file proves that the class
determines the torsor: it vanishes exactly on the trivial torsor, and two torsors with the same
class are isomorphic. Equivalently, the isomorphism classes of torsors which are trivial over
every member of `𝒰` embed into `Ȟ¹(𝒰, G)`.

The two ingredients are the freedom to change the local sections by a Čech `0`-cochain, which
changes the transition cochain by the coboundary of that cochain, and a comparison morphism
built out of two families of local sections whose transition cochains agree *on the nose*.

## Main definitions

* `Stacks.Cohomology.Torsors.actCochain`: the family of local sections obtained by letting a
  Čech `0`-cochain act on a given family.
* `Stacks.Cohomology.Torsors.compareValue`: the value over an object `W` of `C/U` of the
  comparison map attached to two families of local sections, computed from a morphism from `W`
  to a member of the covering family.
* `Stacks.Cohomology.Torsors.compareMap`: the glued comparison map.

## Main results

* `Stacks.Cohomology.Torsors.transitionCochain_actCochain` and
  `Stacks.Cohomology.Torsors.exists_transitionCochain_add`: letting a Čech `0`-cochain act on a
  family of local sections adds its coboundary to the transition cochain, so every Čech
  coboundary is realized by a change of the local sections.
* `Stacks.Cohomology.Torsors.isTrivial_iff_cechClass_eq_zero`: a torsor with a section over
  every member of a covering family is trivial exactly when its Čech class vanishes.
* `Stacks.Cohomology.Torsors.isIsomorphic_of_transitionCochain_eq`: two torsors whose
  transition cochains agree are isomorphic.
* `Stacks.Cohomology.Torsors.isIsomorphic_of_cls_transitionCocycle_eq` and
  `Stacks.Cohomology.Torsors.cechClass_injective`: two torsors with cohomologous transition
  cocycles are isomorphic, that is, the Čech class is injective on the isomorphism classes of
  torsors locally trivial on the family.

## Implementation notes

A degree-zero Čech cochain of `𝒰` is a family of sections of `G` over the *one-member* iterated
fibre products `∏ᶜ (fun _ : Fin 1 ↦ U_i)`, not over the members themselves, so letting such a
cochain act on a family of local sections transports its values along the diagonal
`Stacks.Cohomology.Torsors.unaryLift`, which is inverse to the projection of a one-member
product.

The comparison morphism is built by gluing. Over an object `W` of `C/U` equipped with a
morphism `g` to a member `U_i`, two families of local sections determine a map `F(W) → F'(W)`:
take the difference of the given section with `s_i|_W` and let it act on `s'_i|_W`. Equality of
the two transition cochains says exactly that the result does not depend on `(i, g)`, by the
transitivity of differences of sections; the objects of `C/U` admitting such a `g` form a
covering sieve of every object, and the sheaf condition for `F'` on that sieve glues the local
recipes into a single section. The glued map is natural and equivariant because both properties
may be checked after restricting to that sieve, where the recipe is explicit, and an equivariant
morphism of torsors is automatically an isomorphism
(`Stacks.Cohomology.Torsors.torsorHom_isIso`).

What is *not* proved here is the converse direction, that every Čech class comes from a torsor:
that needs a torsor built from a prescribed cocycle, which is effective descent for torsors and
raises the universe of the sections of the glued torsor, as in
`SheafOfGroups.Torsors.projection_effectiveDescent`. Consequently the comparison map
`Ȟ¹(𝒰, G) → H¹(U, G)` itself is not available here, only the injection in the other direction.

## References

* [Stacks Project, Tag 0A6G](https://stacks.math.columbia.edu/tag/0A6G)
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 03AI](https://stacks.math.columbia.edu/tag/03AI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe h t w v u

namespace Stacks.Cohomology.Torsors

open Stacks.CechSite

/-! ### Changing the local sections by a Čech `0`-cochain -/

section Correction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
  (E : PreZeroHypercover.{w} U) (G : Sheaf J AddCommGrpCat.{t})
  [HasProducts.{w} AddCommGrpCat.{t}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})]

/-- The diagonal morphism from a member of the covering family to the one-member iterated
fibre product of that member. -/
def unaryLift (i : E.I₀) : Over.mk (E.f i) ⟶ (∏ᶜ fun _ : Fin 1 ↦ Over.mk (E.f i)) :=
  Pi.lift fun _ ↦ 𝟙 _

omit [HasProducts.{w} AddCommGrpCat.{t}] [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- The diagonal of a one-member product is a section of each of its projections. -/
lemma unaryLift_comp_π (i : E.I₀) (j : Fin 1) :
    unaryLift E i ≫ Pi.π (fun _ : Fin 1 ↦ Over.mk (E.f i)) j = 𝟙 _ :=
  Pi.lift_π _ _

omit [HasProducts.{w} AddCommGrpCat.{t}] [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- The diagonal of a one-member product is a retraction of each of its projections: a
one-member product has a single projection, which is therefore an isomorphism. -/
lemma π_comp_unaryLift (i : E.I₀) (j : Fin 1) :
    Pi.π (fun _ : Fin 1 ↦ Over.mk (E.f i)) j ≫ unaryLift E i = 𝟙 _ := by
  refine Pi.hom_ext _ _ fun m ↦ ?_
  rw [Category.assoc, unaryLift_comp_π, Category.comp_id, Category.id_comp]
  exact congrArg (Pi.π (fun _ : Fin 1 ↦ Over.mk (E.f i))) (Subsingleton.elim j m)

/-- The family of local sections obtained by letting a Čech `0`-cochain act on a given family:
over the member `U_i` the cochain is evaluated at the constant tuple `i` and transported along
the diagonal of the one-member fibre product. -/
def actCochain (F : AbelianTorsor (G.over U))
    (s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i)))) (τ : cechCochain E G.obj 0) (i : E.I₀) :
    F.1.presheaf.obj (op (Over.mk (E.f i))) :=
  F.1.act _ (Multiplicative.ofAdd (G.obj.map (unaryLift E i).left.op (τ fun _ ↦ i))) (s i)

omit [HasProducts.{w} AddCommGrpCat.{t}] in
/-- The cochain of differences between a family of local sections and its modification by a
Čech `0`-cochain is that cochain. -/
lemma sectionDifferenceCochain_actCochain (F : AbelianTorsor (G.over U))
    (s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i)))) (τ : cechCochain E G.obj 0) :
    sectionDifferenceCochain E G F (actCochain E G F s τ) s = τ := by
  funext l
  obtain ⟨i, rfl⟩ : ∃ i, l = fun _ : Fin 1 ↦ i :=
    ⟨l 0, funext fun j ↦ congrArg l (Subsingleton.elim (α := Fin 1) j 0)⟩
  have hnat := F.1.naturality (Pi.π (fun _ : Fin 1 ↦ Over.mk (E.f i)) 0).op
    (Multiplicative.ofAdd (G.obj.map (unaryLift E i).left.op (τ fun _ ↦ i))) (s i)
  have hid : (Pi.π (fun _ : Fin 1 ↦ Over.mk (E.f i)) 0).left ≫ (unaryLift E i).left =
      𝟙 (∏ᶜ fun _ : Fin 1 ↦ Over.mk (E.f i)).left := by
    rw [← Over.comp_left, π_comp_unaryLift, Over.id_left]
  have hcomp : G.obj.map (Pi.π (fun _ : Fin 1 ↦ Over.mk (E.f i)) 0).left.op
      (G.obj.map (unaryLift E i).left.op (τ fun _ ↦ i)) = τ fun _ : Fin 1 ↦ i := by
    rw [← Functor.map_comp_apply, ← op_comp, hid, op_id, CategoryTheory.Functor.map_id]
    rfl
  refine torsorDifference_eq_of_act (G.over U) F _ _ _ _ (Eq.trans ?_ hnat.symm)
  exact congrArg (fun γ ↦ F.1.act _ (Multiplicative.ofAdd γ)
    (F.1.presheaf.map (Pi.π (fun _ : Fin 1 ↦ Over.mk (E.f i)) 0).op (s i))) hcomp.symm

/-- **Every Čech coboundary is realized by a change of the local sections.** Letting a Čech
`0`-cochain act on a family of local sections adds its coboundary to the transition cochain. -/
lemma transitionCochain_actCochain (F : AbelianTorsor (G.over U))
    (s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i)))) (τ : cechCochain E G.obj 0) :
    transitionCochain E G F (actCochain E G F s τ) =
      transitionCochain E G F s + cechDifferential E G.obj 0 τ := by
  have h := cechDifferential_sectionDifferenceCochain E G F (actCochain E G F s τ) s
  rw [sectionDifferenceCochain_actCochain] at h
  rw [h]
  abel

/-- A family of local sections whose transition cochain differs from the given one by a
prescribed Čech coboundary. -/
lemma exists_transitionCochain_add (F : AbelianTorsor (G.over U))
    (s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i)))) (τ : cechCochain E G.obj 0) :
    ∃ s' : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i))),
      transitionCochain E G F s' = transitionCochain E G F s + cechDifferential E G.obj 0 τ :=
  ⟨actCochain E G F s τ, transitionCochain_actCochain E G F s τ⟩

/-- **A torsor with vanishing Čech class is trivial.** For a covering family, the Čech class of
a torsor with a section over every member vanishes exactly when the torsor is trivial: the class
vanishes when the transition cocycle is a Čech coboundary, and subtracting that coboundary from
the local sections makes the transition cochain vanish on the nose. -/
@[stacks 0A6G "variant: the Čech class vanishes exactly on the trivial torsor; \
the tag is Stacks.CechSite.cechH1ToSliceH_injective_and_range_eq", ega "IV 16.5.15" "special case"]
theorem isTrivial_iff_cechClass_eq_zero (hE : E.sieve₀ ∈ J U) (F : AbelianTorsor (G.over U))
    (hs : ∀ i, Nonempty (F.1.presheaf.obj (op (Over.mk (E.f i))))) :
    F.1.IsTrivial ↔
      cechClass E G ⟨Quotient.mk (torsorSetoid (G.over U)) F, ⟨F, rfl, hs⟩⟩ = 0 := by
  classical
  refine ⟨fun hT ↦ cechClass_eq_zero_of_isTrivial E G F hT hs, fun hzero ↦ ?_⟩
  obtain ⟨s⟩ := Classical.nonempty_pi.2 hs
  rw [cechClass_mk E G F hs s, cls_eq_zero_iff] at hzero
  obtain ⟨τ, hτ⟩ := hzero
  refine isTrivial_of_transitionCochain_eq_zero E G hE F (actCochain E G F s (-τ)) ?_
  rw [transitionCochain_actCochain, map_neg, hτ]
  exact add_neg_cancel _

end Correction

/-- Restricting twice along `r` and `g` is restricting along `r ≫ g`. -/
private theorem map_map_op {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type*) {X Y Z : C}
    (r : Y ⟶ X) (g : X ⟶ Z) (x : P.obj (op Z)) :
    P.map r.op (P.map g.op x) = P.map (r ≫ g).op x := by
  rw [← Functor.map_comp_apply, ← op_comp]

/-! ### The comparison morphism attached to two families of local sections -/

section Comparison

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
  (E : PreZeroHypercover.{w} U) (G : Sheaf J AddCommGrpCat.{t})
  [HasProducts.{w} AddCommGrpCat.{t}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})]
  (F F' : AbelianTorsor (G.over U))
  (s : ∀ i, F.1.presheaf.obj (op (Over.mk (E.f i))))
  (s' : ∀ i, F'.1.presheaf.obj (op (Over.mk (E.f i))))

omit [HasProducts.{w} AddCommGrpCat.{t}] [HasSheafify (J.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- Restricting the action of a section of the coefficient sheaf, in additive form. -/
lemma map_act_ofAdd (T : AbelianTorsor (G.over U)) {W V : Over U} (r : V ⟶ W)
    (d : (G.over U).obj.obj (op W)) (y : T.1.presheaf.obj (op W)) :
    T.1.presheaf.map r.op (T.1.act (op W) (Multiplicative.ofAdd d) y) =
      T.1.act (op V) (Multiplicative.ofAdd ((G.over U).obj.map r.op d))
        (T.1.presheaf.map r.op y) :=
  T.1.naturality r.op _ y

omit [HasProducts.{w} AddCommGrpCat.{t}] in
/-- The restriction of the transition cochain along an arbitrary morphism into a twofold
iterated fibre product is the difference of the two restricted local sections. -/
lemma map_transitionCochain_comp (T : AbelianTorsor (G.over U))
    (σ : ∀ i, T.1.presheaf.obj (op (Over.mk (E.f i)))) (k : Fin 2 → E.I₀) {W : Over U}
    (u : W ⟶ (∏ᶜ fun m ↦ Over.mk (E.f (k m)))) :
    G.obj.map u.left.op (transitionCochain E G T σ k) =
      torsorDifference (G.over U) T (op W)
        (T.1.presheaf.map (u ≫ Pi.π (fun m ↦ Over.mk (E.f (k m))) 1).op (σ (k 1)))
        (T.1.presheaf.map (u ≫ Pi.π (fun m ↦ Over.mk (E.f (k m))) 0).op (σ (k 0))) := by
  rw [← map_sectionRestriction_comp E G T σ k 1 u, ← map_sectionRestriction_comp E G T σ k 0 u]
  exact torsorDifference_naturality (G.over U) T u.op _ _

omit [HasProducts.{w} AddCommGrpCat.{t}] in
/-- **Two families of local sections with the same transition cochain have the same
differences.** For any pair of morphisms from an object of `C/U` to members of the covering
family, the difference of the two restricted sections of `F` is the difference of the two
restricted sections of `F'`. -/
lemma torsorDifference_map_eq_of_transitionCochain_eq
    (h : transitionCochain E G F s = transitionCochain E G F' s')
    {W : Over U} (k : Fin 2 → E.I₀) (a : W ⟶ Over.mk (E.f (k 0)))
    (b : W ⟶ Over.mk (E.f (k 1))) :
    torsorDifference (G.over U) F (op W) (F.1.presheaf.map b.op (s (k 1)))
        (F.1.presheaf.map a.op (s (k 0))) =
      torsorDifference (G.over U) F' (op W) (F'.1.presheaf.map b.op (s' (k 1)))
        (F'.1.presheaf.map a.op (s' (k 0))) := by
  let u : W ⟶ (∏ᶜ fun m ↦ Over.mk (E.f (k m))) :=
    Pi.lift (fun m ↦ match m with | 0 => a | 1 => b)
  have h0 : u ≫ Pi.π (fun m ↦ Over.mk (E.f (k m))) 0 = a := Pi.lift_π _ _
  have h1 : u ≫ Pi.π (fun m ↦ Over.mk (E.f (k m))) 1 = b := Pi.lift_π _ _
  have e := map_transitionCochain_comp E G F s k u
  have e' := map_transitionCochain_comp E G F' s' k u
  rw [h0, h1] at e e'
  rw [← e, ← e', h]

/-- The value over `W` of the comparison map attached to the two families of local sections,
computed from a morphism `g` from `W` to a member of the covering family: the difference of the
given section with the restriction of `s_i` acts on the restriction of `s'_i`. -/
def compareValue {W : Over U} (x : F.1.presheaf.obj (op W)) {i : E.I₀}
    (g : W ⟶ Over.mk (E.f i)) : F'.1.presheaf.obj (op W) :=
  F'.1.act (op W)
    (Multiplicative.ofAdd
      (torsorDifference (G.over U) F (op W) x (F.1.presheaf.map g.op (s i))))
    (F'.1.presheaf.map g.op (s' i))

omit [HasProducts.{w} AddCommGrpCat.{t}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))] in
/-- The comparison value is compatible with restriction. -/
lemma map_compareValue {W V : Over U} (r : V ⟶ W) (x : F.1.presheaf.obj (op W)) {i : E.I₀}
    (g : W ⟶ Over.mk (E.f i)) :
    F'.1.presheaf.map r.op (compareValue E G F F' s s' x g) =
      compareValue E G F F' s s' (F.1.presheaf.map r.op x) (r ≫ g) := by
  simp only [compareValue]
  rw [map_act_ofAdd G F' r, torsorDifference_naturality (G.over U) F r.op, map_map_op,
    map_map_op]

omit [HasProducts.{w} AddCommGrpCat.{t}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))] in
/-- The comparison value is equivariant. -/
lemma compareValue_act {W : Over U} (d : (G.over U).obj.obj (op W))
    (x : F.1.presheaf.obj (op W)) {i : E.I₀} (g : W ⟶ Over.mk (E.f i)) :
    compareValue E G F F' s s' (F.1.act (op W) (Multiplicative.ofAdd d) x) g =
      F'.1.act (op W) (Multiplicative.ofAdd d) (compareValue E G F F' s s' x g) := by
  simp only [compareValue]
  rw [torsorDifference_act_left, act_ofAdd_add]

omit [HasProducts.{w} AddCommGrpCat.{t}] in
/-- **The comparison value does not depend on the chosen morphism to a member.** This is the
whole force of the hypothesis that the two transition cochains agree. -/
lemma compareValue_congr (h : transitionCochain E G F s = transitionCochain E G F' s')
    {W : Over U} (x : F.1.presheaf.obj (op W)) {i j : E.I₀} (a : W ⟶ Over.mk (E.f i))
    (b : W ⟶ Over.mk (E.f j)) :
    compareValue E G F F' s s' x a = compareValue E G F F' s s' x b := by
  have hc : torsorDifference (G.over U) F (op W) (F.1.presheaf.map b.op (s j))
        (F.1.presheaf.map a.op (s i)) =
      torsorDifference (G.over U) F' (op W) (F'.1.presheaf.map b.op (s' j))
        (F'.1.presheaf.map a.op (s' i)) :=
    torsorDifference_map_eq_of_transitionCochain_eq E G F F' s s' h ![i, j] a b
  have hB' : F'.1.act (op W) (Multiplicative.ofAdd
        (torsorDifference (G.over U) F' (op W) (F'.1.presheaf.map b.op (s' j))
          (F'.1.presheaf.map a.op (s' i)))) (F'.1.presheaf.map a.op (s' i)) =
      F'.1.presheaf.map b.op (s' j) :=
    torsorDifference_act (G.over U) F' (op W) _ _
  have hd : torsorDifference (G.over U) F (op W) x (F.1.presheaf.map a.op (s i)) =
      torsorDifference (G.over U) F (op W) x (F.1.presheaf.map b.op (s j)) +
        torsorDifference (G.over U) F (op W) (F.1.presheaf.map b.op (s j))
          (F.1.presheaf.map a.op (s i)) :=
    torsorDifference_trans (G.over U) F (op W) x _ _
  simp only [compareValue]
  rw [hd, hc, act_ofAdd_add, hB']

/-- The sieve of the objects of `C/U` which admit a morphism to a member of the covering
family. -/
def memberSieve (W : Over U) : Sieve W where
  arrows := fun {V} _ ↦ ∃ i : E.I₀, Nonempty (V ⟶ Over.mk (E.f i))
  downward_closed := fun ⟨i, hi⟩ q ↦ ⟨i, hi.map (fun g ↦ q ≫ g)⟩

omit [HasProducts.{w} AddCommGrpCat.{t}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  [HasSheafify (J.over U) AddCommGrpCat.{t}] [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- For a covering family, every object of `C/U` is covered by objects admitting a morphism to
a member of the family. -/
lemma memberSieve_mem (hE : E.sieve₀ ∈ J U) (W : Over U) :
    memberSieve E W ∈ (J.over U) W := by
  refine (J.over U).superset_covering ?_
    ((J.over U).pullback_stable (Over.mkIdTerminal.from W)
      (J.overEquiv_symm_mem_over (Over.mk (𝟙 U)) E.sieve₀ hE))
  intro V r hr
  exact exists_hom_over_member E (r ≫ Over.mkIdTerminal.from W) hr

/-- A section of `F'` over `W` is *the comparison* of a section `x` of `F` over `W` when it
restricts to the comparison value over every object of `C/U` above `W` admitting a morphism to
a member of the covering family. -/
def IsComparison {W : Over U} (x : F.1.presheaf.obj (op W)) (y : F'.1.presheaf.obj (op W)) :
    Prop :=
  ∀ ⦃V : Over U⦄ (r : V ⟶ W) {i : E.I₀} (g : V ⟶ Over.mk (E.f i)),
    F'.1.presheaf.map r.op y = compareValue E G F F' s s' (F.1.presheaf.map r.op x) g

omit [HasProducts.{w} AddCommGrpCat.{t}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  [HasSheafify (J.over U) AddCommGrpCat.{t}] [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{t})] in
/-- The comparison of a section is unique: two of them agree on a covering sieve. -/
lemma isComparison_unique (hE : E.sieve₀ ∈ J U) {W : Over U} (x : F.1.presheaf.obj (op W))
    {y y' : F'.1.presheaf.obj (op W)} (hy : IsComparison E G F F' s s' x y)
    (hy' : IsComparison E G F F' s s' x y') : y = y' := by
  refine ((isSheaf_iff_isSheaf_of_type (J.over U) F'.1.presheaf).1 F'.1.isSheaf
      (memberSieve E W) (memberSieve_mem E hE W)).isSeparatedFor
    (fun V r _ ↦ F'.1.presheaf.map r.op y) y y' (fun V r hr ↦ rfl) ?_
  rintro V r ⟨i, ⟨g⟩⟩
  exact (hy' r g).trans (hy r g).symm

omit [HasProducts.{w} AddCommGrpCat.{t}] in
/-- **The comparison of a section exists**: the comparison values over the objects above `W`
admitting a morphism to a member of the family form a compatible family, which the sheaf
condition for `F'` amalgamates. -/
lemma exists_isComparison (hE : E.sieve₀ ∈ J U)
    (h : transitionCochain E G F s = transitionCochain E G F' s') {W : Over U}
    (x : F.1.presheaf.obj (op W)) : ∃ y, IsComparison E G F F' s s' x y := by
  classical
  let fam : Presieve.FamilyOfElements F'.1.presheaf (memberSieve E W).arrows :=
    fun V r hr ↦ compareValue E G F F' s s' (F.1.presheaf.map r.op x)
      (Classical.choice (Classical.choose_spec hr))
  have hval : ∀ {V : Over U} (r : V ⟶ W) (hr : (memberSieve E W).arrows r) (i : E.I₀)
      (g : V ⟶ Over.mk (E.f i)),
      fam r hr = compareValue E G F F' s s' (F.1.presheaf.map r.op x) g :=
    fun r hr _ g ↦ compareValue_congr E G F F' s s' h (F.1.presheaf.map r.op x) _ g
  have hcompat : fam.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    obtain ⟨i₁, ⟨a₁⟩⟩ := id h₁
    obtain ⟨i₂, ⟨a₂⟩⟩ := id h₂
    rw [hval f₁ h₁ i₁ a₁, hval f₂ h₂ i₂ a₂, map_compareValue, map_compareValue, map_map_op,
      map_map_op, hcomm]
    exact compareValue_congr E G F F' s s' h _ _ _
  obtain ⟨y, hy, -⟩ := (isSheaf_iff_isSheaf_of_type (J.over U) F'.1.presheaf).1 F'.1.isSheaf
    (memberSieve E W) (memberSieve_mem E hE W) fam hcompat
  refine ⟨y, fun V r i g ↦ ?_⟩
  exact (hy r ⟨i, ⟨g⟩⟩).trans (hval r ⟨i, ⟨g⟩⟩ i g)

/-- The comparison map attached to two families of local sections with the same transition
cochain, over an object of `C/U`. -/
def compareMap (hE : E.sieve₀ ∈ J U)
    (h : transitionCochain E G F s = transitionCochain E G F' s') {W : Over U}
    (x : F.1.presheaf.obj (op W)) : F'.1.presheaf.obj (op W) :=
  Classical.choose (exists_isComparison E G F F' s s' hE h x)

omit [HasProducts.{w} AddCommGrpCat.{t}] in
/-- The image of a section under the comparison map is the comparison of that section. -/
lemma compareMap_spec (hE : E.sieve₀ ∈ J U)
    (h : transitionCochain E G F s = transitionCochain E G F' s') {W : Over U}
    (x : F.1.presheaf.obj (op W)) :
    IsComparison E G F F' s s' x (compareMap E G F F' s s' hE h x) :=
  Classical.choose_spec (exists_isComparison E G F F' s s' hE h x)

omit [HasProducts.{w} AddCommGrpCat.{t}] in
/-- The comparison map is compatible with restriction. -/
lemma map_compareMap (hE : E.sieve₀ ∈ J U)
    (h : transitionCochain E G F s = transitionCochain E G F' s') {W V : Over U} (r : V ⟶ W)
    (x : F.1.presheaf.obj (op W)) :
    F'.1.presheaf.map r.op (compareMap E G F F' s s' hE h x) =
      compareMap E G F F' s s' hE h (F.1.presheaf.map r.op x) := by
  refine isComparison_unique E G F F' s s' hE (F.1.presheaf.map r.op x) ?_
    (compareMap_spec E G F F' s s' hE h (F.1.presheaf.map r.op x))
  intro V' q i g
  rw [map_map_op, map_map_op]
  exact compareMap_spec E G F F' s s' hE h x (q ≫ r) g

omit [HasProducts.{w} AddCommGrpCat.{t}] in
/-- The comparison map is equivariant. -/
lemma compareMap_act (hE : E.sieve₀ ∈ J U)
    (h : transitionCochain E G F s = transitionCochain E G F' s') {W : Over U}
    (d : (G.over U).obj.obj (op W)) (x : F.1.presheaf.obj (op W)) :
    compareMap E G F F' s s' hE h (F.1.act (op W) (Multiplicative.ofAdd d) x) =
      F'.1.act (op W) (Multiplicative.ofAdd d) (compareMap E G F F' s s' hE h x) := by
  refine isComparison_unique E G F F' s s' hE _
    (compareMap_spec E G F F' s s' hE h (F.1.act (op W) (Multiplicative.ofAdd d) x)) ?_
  intro V r i g
  rw [map_act_ofAdd G F' r, map_act_ofAdd G F r,
    compareMap_spec E G F F' s s' hE h x r g, compareValue_act]

omit [HasProducts.{w} AddCommGrpCat.{t}] in
/-- **Two families of local sections with the same transition cochain exhibit the two torsors
as isomorphic.** The glued comparison map is an equivariant morphism of torsors, hence an
isomorphism. -/
lemma isIsomorphic_of_transitionCochain_eq (hE : E.sieve₀ ∈ J U)
    (h : transitionCochain E G F s = transitionCochain E G F' s') :
    AbelianTorsor.IsIsomorphic F F' := by
  let e : F.1.Hom F'.1 :=
    { hom :=
        { app := fun W ↦ ↾(fun x ↦ compareMap E G F F' s s' hE h (W := W.unop) x)
          naturality := by
            intro W W' f
            ext x
            exact (map_compareMap E G F F' s s' hE h f.unop x).symm }
      map_act := fun W γ z ↦ compareMap_act E G F F' s s' hE h (Multiplicative.toAdd γ) z }
  exact ⟨e, torsorHom_isIso (G.over U) F F' e⟩

/-- **The Čech class determines the torsor.** Two torsors with sections over every member of a
covering family whose transition cocycles are cohomologous are isomorphic: the Čech coboundary
is absorbed into a change of the local sections of the second torsor, and the two families then
glue to an isomorphism. The packaged form of this clause of Stacks 0A6G is
`Stacks.Cohomology.Torsors.cechClass_injective`, which carries its tag. -/
@[ega "IV 16.5.15" "special case"]
theorem isIsomorphic_of_cls_transitionCocycle_eq (hE : E.sieve₀ ∈ J U)
    (h : cls E G.obj (transitionCocycle E G F s) = cls E G.obj (transitionCocycle E G F' s')) :
    AbelianTorsor.IsIsomorphic F F' := by
  obtain ⟨τ, hτ⟩ := (mem_coboundaries1_iff E G.obj _).1 (QuotientAddGroup.eq_iff_sub_mem.1 h)
  have hτ' : cechDifferential E G.obj 0 τ =
      transitionCochain E G F s - transitionCochain E G F' s' := hτ
  refine isIsomorphic_of_transitionCochain_eq E G F F' s (actCochain E G F' s' τ) hE ?_
  rw [transitionCochain_actCochain, hτ']
  abel

/-- **The Čech class is injective on the locally trivial isomorphism classes.** Under the
bijection of Stacks 03AJ between isomorphism classes of torsors and first cohomology, this is
the injectivity of the identification of `Ȟ¹(𝒰, G)` with the isomorphism classes of torsors
which are trivial over every member of `𝒰`. -/
@[stacks 0A6G "variant: injectivity of the Čech class map; \
the tag is Stacks.CechSite.cechH1ToSliceH_injective_and_range_eq", ega "IV 16.5.15" "partial"]
theorem cechClass_injective (hE : E.sieve₀ ∈ J U) :
    Function.Injective (cechClass E G) := by
  classical
  intro c c' hcc
  obtain ⟨T, hT, hs⟩ := c.2
  obtain ⟨T', hT', hs'⟩ := c'.2
  have hc : c = ⟨Quotient.mk (torsorSetoid (G.over U)) T, ⟨T, rfl, hs⟩⟩ := Subtype.ext hT.symm
  have hc' : c' = ⟨Quotient.mk (torsorSetoid (G.over U)) T', ⟨T', rfl, hs'⟩⟩ :=
    Subtype.ext hT'.symm
  obtain ⟨σ⟩ := Classical.nonempty_pi.2 hs
  obtain ⟨σ'⟩ := Classical.nonempty_pi.2 hs'
  rw [hc, hc'] at hcc ⊢
  rw [cechClass_mk E G T hs σ, cechClass_mk E G T' hs' σ'] at hcc
  exact Subtype.ext (Quotient.sound
    (isIsomorphic_of_cls_transitionCocycle_eq E G T T' σ σ' hE hcc))

end Comparison

end Stacks.Cohomology.Torsors

end
