module

public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginSpecTransition
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DescentDataProjection

/-!
# A semilinear involution is a descent datum, and what effectivity would give

Let `g : T ⟶ S` be a morphism whose self-product splits as `T ×_S T = T ⨿ T`, the first
projection being the identity on both summands and the second being `1 ⨿ s` for an involution
`s` of `T` over `S`; the covering `{Spec k' ⟶ Spec k}` of Stacks 03FN is such a morphism.  Let
`p : V ⟶ T` be a scheme over `T` and let `τ` be a *semilinear involution* of `V`: an
endomorphism with `τ ≫ τ = 1` lying over `s`, that is `τ ≫ p = p ≫ s`.

`AlgebraicGeometry.exists_pullbackIso_of_semilinear` already turns `τ` into a candidate gluing
isomorphism `Θ : V ×_S T ≅ T ×_S V` over `T ×_S T`.  What this file adds is **the cocycle
condition**, and with it the descent datum itself.  The cocycle condition cannot be obtained
from `AlgebraicGeometry.exists_transition_of_pullbackIso`, whose extensionality hypothesis fails
for the twisted doubled origin; it is instead checked summandwise, on the splitting of the
triple product `(V ×_S T) ×_S T` into four copies of `V`, where it becomes the four identities
`1 ∘ 1 = 1`, `τ ∘ 1 = τ`, `1 ∘ τ = τ` and `τ ∘ τ = 1`.  The last of these is exactly where the
hypothesis that `τ` is an involution is used.

## Main results

* `AlgebraicGeometry.splitAction_diagonal` and `AlgebraicGeometry.splitAction_twisted`: the two
  summandwise readings of the action of the gluing isomorphism of a semilinear involution.
* `AlgebraicGeometry.cocycle_of_semilinear`: **the cocycle condition for the gluing isomorphism
  of a semilinear involution**, stated for a candidate gluing morphism of the `Over S` products
  whose action is read off the splitting.
* `AlgebraicGeometry.exists_descentDatum_not_isEffective_of_semilinear`: **a semilinear
  involution of `V` admitting no descended scheme is a descent datum relative to `g` which is
  not effective.**  The hypothesis is the geometric input: there is no scheme `W₀` over `S`
  together with an isomorphism `T ×_S W₀ ≅ V` over `T` for which the projection to `W₀` is
  `τ`-invariant.

## Implementation notes

**Why the universal generalized point.** The cocycle condition is a diagram on the
left-associated triple product in `Over S`, and
`AlgebraicGeometry.cocycle_iff_gluingAction_act_act` rewrites it as the law `(v · x) · y = v · y`
on generalized points.  That law for an arbitrary test object follows from its instance at the
universal generalized point of the triple product — the three projections — by
`AlgebraicGeometry.comp_gluingAction`, and only at the universal point is the test object a
disjoint union of four copies of `V`, which is what makes the law checkable.

**The splitting of the triple product.** Both factors are split by one lemma,
`AlgebraicGeometry.isPullback_baseChange_split_of_isPullback`, applied twice: once to
`p : V ⟶ T`, giving `V ×_S T = V ⨿ V`, and once to the second projection `V ×_S T ⟶ T`, giving
`(V ×_S T) ×_S T = (V ×_S T) ⨿ (V ×_S T)`.  Comparing each with the `Over S` product, whose two
legs are a fibre square by `CategoryTheory.Over.isPullback_of_binaryFan_isLimit`, gives the two
comparison isomorphisms, and `CategoryTheory.IsPullback.isoIsPullback` is what compares them.

**How the action is read off.** `AlgebraicGeometry.exists_pullbackIso_of_semilinear` supplies
the `V`-component of `Θ` on each summand: the identity on the summand where the point of `T`
agrees with the one under `V`, and `τ` on the twisted summand.  `splitAction_diagonal` and
`splitAction_twisted` are those two readings in the form the summandwise check consumes: a
generalized point of `V ×_S T` whose components are `c` and `c ≫ p` acts as `c`, and one whose
components are `c` and `c ≫ p ≫ s` acts as `c ≫ τ`.

**Why every comparison isomorphism is quantified over.** The isomorphisms comparing the `Over S`
products with the literal fibre products are taken as parameters, together with the equations
identifying their legs, rather than being named inside the statements: both
`CategoryTheory.Over.prodLeftIsoPullback` and `CategoryTheory.IsPullback.isoPullback` have types
mentioning the structure morphism of an object of `Over S`, which is only definitionally the
composite the fibre products below are stated with, and a rewrite cannot see through that.

## References

* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
* [Stacks Project, Tag 03FN](https://stacks.math.columbia.edu/tag/03FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {S T V : Scheme.{u}} {g : T ⟶ S} {s : T ⟶ T} {p : V ⟶ T} {τ : V ⟶ V}

/-- A generalized point of `V ×_S T` over `c : X ⟶ V` lying in the summand `j` of the splitting
`ε : V ⨿ V ≅ V ×_S T` acts as `c ≫ r`, where `r` is the action `α` on that summand. -/
private theorem comp_action_of_split (ε : V ⨿ V ≅ pullback (p ≫ g) g)
    (hεf : ε.hom ≫ pullback.fst (p ≫ g) g = coprod.desc (𝟙 V) (𝟙 V))
    (hεs : ε.hom ≫ pullback.snd (p ≫ g) g = coprod.desc p (p ≫ s))
    {α : pullback (p ≫ g) g ⟶ V} {j : V ⟶ V ⨿ V} {a : V ⟶ T} {r : V ⟶ V}
    (hj : j ≫ coprod.desc (𝟙 V) (𝟙 V) = 𝟙 V) (hja : j ≫ coprod.desc p (p ≫ s) = a)
    (hjα : j ≫ coprod.desc (𝟙 V) τ = r) (hα : ε.hom ≫ α = coprod.desc (𝟙 V) τ)
    {X : Scheme.{u}} (t : X ⟶ pullback (p ≫ g) g) (c : X ⟶ V)
    (hf : t ≫ pullback.fst (p ≫ g) g = c) (hs : t ≫ pullback.snd (p ≫ g) g = c ≫ a) :
    t ≫ α = c ≫ r := by
  have ht : t = c ≫ j ≫ ε.hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [hf, Category.assoc, Category.assoc, hεf, hj, Category.comp_id]
    · rw [hs, Category.assoc, Category.assoc, hεs, hja]
  rw [ht, Category.assoc, Category.assoc, hα, hjα]

/-- **The diagonal summand of the split base change acts trivially.** A generalized point of
`V ×_S T` whose component in `V` is `c` and whose component in `T` is the one under `c` lies in
the diagonal summand of the splitting `ε : V ⨿ V ≅ V ×_S T`, where the action `α` of the gluing
isomorphism of a semilinear involution is the identity. -/
theorem splitAction_diagonal (ε : V ⨿ V ≅ pullback (p ≫ g) g)
    (hεf : ε.hom ≫ pullback.fst (p ≫ g) g = coprod.desc (𝟙 V) (𝟙 V))
    (hεs : ε.hom ≫ pullback.snd (p ≫ g) g = coprod.desc p (p ≫ s))
    {α : pullback (p ≫ g) g ⟶ V} (hα : ε.hom ≫ α = coprod.desc (𝟙 V) τ)
    {X : Scheme.{u}} (t : X ⟶ pullback (p ≫ g) g) (c : X ⟶ V)
    (hf : t ≫ pullback.fst (p ≫ g) g = c) (hs : t ≫ pullback.snd (p ≫ g) g = c ≫ p) :
    t ≫ α = c := by
  exact (comp_action_of_split ε hεf hεs (coprod.inl_desc _ _)
    (coprod.inl_desc _ _) (coprod.inl_desc _ _) hα t c
    hf hs).trans (Category.comp_id c)

/-- **The twisted summand of the split base change acts by the involution.** A generalized point
of `V ×_S T` whose component in `V` is `c` and whose component in `T` is the twist by `s` of the
one under `c` lies in the twisted summand of the splitting `ε : V ⨿ V ≅ V ×_S T`, where the
action `α` of the gluing isomorphism of a semilinear involution is `τ`. -/
theorem splitAction_twisted (ε : V ⨿ V ≅ pullback (p ≫ g) g)
    (hεf : ε.hom ≫ pullback.fst (p ≫ g) g = coprod.desc (𝟙 V) (𝟙 V))
    (hεs : ε.hom ≫ pullback.snd (p ≫ g) g = coprod.desc p (p ≫ s))
    {α : pullback (p ≫ g) g ⟶ V} (hα : ε.hom ≫ α = coprod.desc (𝟙 V) τ)
    {X : Scheme.{u}} (t : X ⟶ pullback (p ≫ g) g) (c : X ⟶ V)
    (hf : t ≫ pullback.fst (p ≫ g) g = c) (hs : t ≫ pullback.snd (p ≫ g) g = c ≫ p ≫ s) :
    t ≫ α = c ≫ τ := by
  exact comp_action_of_split ε hεf hεs (coprod.inr_desc _ _)
    (coprod.inr_desc _ _) (coprod.inr_desc _ _) hα t c hf hs

/-- The splitting of the base change of `p'` along `g` compares with any fibre square of
`p' ≫ g` and `g`. -/
private theorem exists_split_iso {V' P : Scheme.{u}} {p' : V' ⟶ T} {f₁ : P ⟶ V'} {f₂ : P ⟶ T}
    (hsplit : IsPullback (coprod.desc (𝟙 T) (𝟙 T)) (coprod.desc (𝟙 T) s) g g)
    (H : IsPullback f₁ f₂ (p' ≫ g) g) :
    ∃ E : V' ⨿ V' ≅ P, E.hom ≫ f₁ = coprod.desc (𝟙 V') (𝟙 V') ∧
      E.hom ≫ f₂ = coprod.desc p' (p' ≫ s) :=
  have h := isPullback_baseChange_split_of_isPullback hsplit p'
  ⟨h.isoIsPullback _ _ H, h.isoIsPullback_hom_fst _ _ H, h.isoIsPullback_hom_snd _ _ H⟩

/-- **The cocycle condition for the gluing isomorphism of a semilinear involution.** Let
`g : T ⟶ S` be a morphism whose self-product splits as `T ⨿ T` with second projection `1 ⨿ s`,
let `τ` be an involution of `V` lying over the involution `s`, and let `φ` be a candidate gluing
morphism of the `Over S` products which lies over `T ×_S T` (`h1`, `h2`) and whose action on
generalized points is given by a morphism `α : V ×_S T ⟶ V` (`hAct`) restricting to the identity
on the first summand of the splitting `ε : V ⨿ V ≅ V ×_S T` and to `τ` on the second (`hα`).
Then `φ` satisfies the cocycle condition on the triple product. -/
theorem cocycle_of_semilinear (ε : V ⨿ V ≅ pullback (p ≫ g) g)
    (hεf : ε.hom ≫ pullback.fst (p ≫ g) g = coprod.desc (𝟙 V) (𝟙 V))
    (hεs : ε.hom ≫ pullback.snd (p ≫ g) g = coprod.desc p (p ≫ s))
    (hsplit : IsPullback (coprod.desc (𝟙 T) (𝟙 T)) (coprod.desc (𝟙 T) s) g g)
    (hss : s ≫ s = 𝟙 T) (hττ : τ ≫ τ = 𝟙 V) (hτ : τ ≫ p = p ≫ s)
    (φ : (Over.map g).obj (Over.mk p) ⨯ Over.mk g ⟶ Over.mk g ⨯ (Over.map g).obj (Over.mk p))
    (h1 : φ ≫ prod.fst = prod.fst ≫ structureMap g (Over.mk p))
    (h2 : φ ≫ prod.snd ≫ structureMap g (Over.mk p) = prod.snd)
    (k : ((Over.map g).obj (Over.mk p) ⨯ Over.mk g).left ≅ pullback (p ≫ g) g)
    (hk1 : k.hom ≫ pullback.fst (p ≫ g) g =
      (prod.fst : (Over.map g).obj (Over.mk p) ⨯ Over.mk g ⟶ _).left)
    (hk2 : k.hom ≫ pullback.snd (p ≫ g) g =
      (prod.snd : (Over.map g).obj (Over.mk p) ⨯ Over.mk g ⟶ _).left)
    {α : pullback (p ≫ g) g ⟶ V} (hα : ε.hom ≫ α = coprod.desc (𝟙 V) τ)
    (hAct : ∀ {Z : Over S} (v : Z ⟶ (Over.map g).obj (Over.mk p)) (x : Z ⟶ Over.mk g),
      (gluingAction (Over.mk p) φ v x).left = ((prod.lift v x).left ≫ k.hom) ≫ α) :
    prod.map φ (𝟙 (Over.mk g)) ≫ prodMapLastTwo φ = prodMapFirstThird φ := by
  have hkey : τ ≫ p ≫ s = p := by
    rw [← Category.assoc, hτ, Category.assoc, hss, Category.comp_id]
  have hLfst : ∀ {Z : Over S} (v : Z ⟶ (Over.map g).obj (Over.mk p)) (x : Z ⟶ Over.mk g),
      ((prod.lift v x).left ≫ k.hom) ≫ pullback.fst (p ≫ g) g = v.left := by
    intro Z v x
    rw [Category.assoc, hk1, ← Over.comp_left, prod.lift_fst]
  have hLsnd : ∀ {Z : Over S} (v : Z ⟶ (Over.map g).obj (Over.mk p)) (x : Z ⟶ Over.mk g),
      ((prod.lift v x).left ≫ k.hom) ≫ pullback.snd (p ≫ g) g = x.left := by
    intro Z v x
    rw [Category.assoc, hk2, ← Over.comp_left, prod.lift_snd]
  -- the double and triple `Over S` products, as fibre squares
  have H₁ : IsPullback (prod.fst : (Over.map g).obj (Over.mk p) ⨯ Over.mk g ⟶ _).left
      (prod.snd : (Over.map g).obj (Over.mk p) ⨯ Over.mk g ⟶ _).left (p ≫ g) g := by
    have h := Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (prod.fst : (Over.map g).obj (Over.mk p) ⨯ Over.mk g ⟶ _) prod.snd)
      (prodIsProd ((Over.map g).obj (Over.mk p)) (Over.mk g))
    exact h
  have H₂ : IsPullback
      (prod.fst : ((Over.map g).obj (Over.mk p) ⨯ Over.mk g) ⨯ Over.mk g ⟶ _).left
      (prod.snd : ((Over.map g).obj (Over.mk p) ⨯ Over.mk g) ⨯ Over.mk g ⟶ _).left
      ((prod.snd : (Over.map g).obj (Over.mk p) ⨯ Over.mk g ⟶ _).left ≫ g) g := by
    have h := Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk
        (prod.fst : ((Over.map g).obj (Over.mk p) ⨯ Over.mk g) ⨯ Over.mk g ⟶ _) prod.snd)
      (prodIsProd ((Over.map g).obj (Over.mk p) ⨯ Over.mk g) (Over.mk g))
    rwa [← Over.w (prod.snd : (Over.map g).obj (Over.mk p) ⨯ Over.mk g ⟶ Over.mk g)] at h
  obtain ⟨E₁, hE₁u, hE₁w⟩ := exists_split_iso (V' := V) (p' := p) hsplit H₁
  obtain ⟨E₂, hE₂f, hE₂s⟩ := exists_split_iso hsplit H₂
  have hE₁k : E₁.hom ≫ k.hom = ε.hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hk1, hE₁u, hεf]
    · rw [Category.assoc, hk2, hE₁w, hεs]
  -- reassociated forms of the facts above, for use inside a longer composite
  have hE₁u' : ∀ {X : Scheme.{u}} (z : V ⟶ X),
      E₁.hom ≫ (prod.fst : (Over.map g).obj (Over.mk p) ⨯ Over.mk g ⟶ _).left ≫ z =
        coprod.desc (𝟙 V) (𝟙 V) ≫ z := fun z => by rw [← Category.assoc, hE₁u]
  have hE₁w' : ∀ {X : Scheme.{u}} (z : T ⟶ X),
      E₁.hom ≫ (prod.snd : (Over.map g).obj (Over.mk p) ⨯ Over.mk g ⟶ _).left ≫ z =
        coprod.desc p (p ≫ s) ≫ z := fun z => by rw [← Category.assoc, hE₁w]
  have hE₁k' : ∀ {X : Scheme.{u}} (z : pullback (p ≫ g) g ⟶ X),
      E₁.hom ≫ k.hom ≫ z = ε.hom ≫ z := fun z => by rw [← Category.assoc, hE₁k]
  have hE₂f' : ∀ {X : Scheme.{u}}
      (z : ((Over.map g).obj (Over.mk p) ⨯ Over.mk g).left ⟶ X),
      E₂.hom ≫ (prod.fst : ((Over.map g).obj (Over.mk p) ⨯ Over.mk g) ⨯ Over.mk g ⟶ _).left ≫
          z = coprod.desc (𝟙 _) (𝟙 _) ≫ z := fun z => by rw [← Category.assoc, hE₂f]
  have hE₂s' : ∀ {X : Scheme.{u}} (z : T ⟶ X),
      E₂.hom ≫ (prod.snd : ((Over.map g).obj (Over.mk p) ⨯ Over.mk g) ⨯ Over.mk g ⟶ _).left ≫
          z = coprod.desc (prod.snd : (Over.map g).obj (Over.mk p) ⨯ Over.mk g ⟶ _).left
            ((prod.snd : (Over.map g).obj (Over.mk p) ⨯ Over.mk g ⟶ _).left ≫ s) ≫ z :=
    fun z => by rw [← Category.assoc, hE₂s]
  -- the law `(v · x) · y = v · y` at the universal generalized point of the triple product
  have huniv : gluingAction (Over.mk p) φ
        (gluingAction (Over.mk p) φ
          (prod.fst ≫ prod.fst :
            ((Over.map g).obj (Over.mk p) ⨯ Over.mk g) ⨯ Over.mk g ⟶ _)
          (prod.fst ≫ prod.snd)) prod.snd =
      gluingAction (Over.mk p) φ
        (prod.fst ≫ prod.fst : ((Over.map g).obj (Over.mk p) ⨯ Over.mk g) ⨯ Over.mk g ⟶ _)
        prod.snd := by
    have hvx : (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd) :
        ((Over.map g).obj (Over.mk p) ⨯ Over.mk g) ⨯ Over.mk g ⟶
          (Over.map g).obj (Over.mk p) ⨯ Over.mk g) = prod.fst := by
      refine prod.hom_ext ?_ ?_ <;> simp
    refine Over.OverMorphism.ext ?_
    have hpt : ∀ {Z : Over S} (v : Z ⟶ (Over.map g).obj (Over.mk p)) (x : Z ⟶ Over.mk g),
        ∃ t : Z.left ⟶ pullback (p ≫ g) g, (gluingAction (Over.mk p) φ v x).left = t ≫ α ∧
          t ≫ pullback.fst (p ≫ g) g = v.left ∧ t ≫ pullback.snd (p ≫ g) g = x.left :=
      fun v x => ⟨_, hAct v x, hLfst v x, hLsnd v x⟩
    obtain ⟨t₁, ht₁α, ht₁f, ht₁s⟩ := hpt (gluingAction (Over.mk p) φ
      (prod.fst ≫ prod.fst : ((Over.map g).obj (Over.mk p) ⨯ Over.mk g) ⨯ Over.mk g ⟶ _)
      (prod.fst ≫ prod.snd)) prod.snd
    obtain ⟨t₂, ht₂α, ht₂f, ht₂s⟩ := hpt
      (prod.fst ≫ prod.fst : ((Over.map g).obj (Over.mk p) ⨯ Over.mk g) ⨯ Over.mk g ⟶ _)
      prod.snd
    rw [hAct, hvx, Category.assoc] at ht₁f
    rw [Over.comp_left] at ht₂f
    rw [ht₁α, ht₂α, ← cancel_epi E₂.hom]
    refine coprod.hom_ext ?_ ?_
    · rw [← cancel_epi E₁.hom]
      refine coprod.hom_ext ?_ ?_
      · simp only [← Category.assoc]
        refine congrArg (· ≫ α) (pullback.hom_ext ?_ ?_)
        · simp only [Category.assoc, ht₁f, ht₂f, hE₂f', coprod.inl_desc, coprod.inl_desc_assoc,
            hE₁k', hE₁u, hα, Category.id_comp]
        · simp only [Category.assoc, ht₁s, ht₂s, hE₂s, coprod.inl_desc, hE₁w]
      · simp only [← Category.assoc]
        refine (splitAction_diagonal ε hεf hεs hα _ τ ?_ ?_).trans
          (((splitAction_twisted ε hεf hεs hα _ (𝟙 V) ?_ ?_).trans (Category.id_comp τ)).symm)
        · simp only [Category.assoc, ht₁f, hE₂f', coprod.inr_desc, coprod.inl_desc_assoc, hE₁k', hα,
            Category.id_comp]
        · simp only [Category.assoc, ht₁s, hE₂s, coprod.inl_desc, coprod.inr_desc, hE₁w, hτ]
        · simp only [Category.assoc, ht₂f, hE₂f', coprod.inr_desc, coprod.inl_desc_assoc, hE₁u,
            Category.id_comp]
        · simp only [Category.assoc, ht₂s, hE₂s, coprod.inl_desc, coprod.inr_desc, hE₁w,
            Category.id_comp]
    · rw [← cancel_epi E₁.hom]
      refine coprod.hom_ext ?_ ?_
      · simp only [← Category.assoc]
        refine congrArg (· ≫ α) (pullback.hom_ext ?_ ?_)
        · simp only [Category.assoc, ht₁f, ht₂f, hE₂f', coprod.inl_desc, coprod.inr_desc_assoc,
            hE₁k', hE₁u, hα, Category.id_comp]
        · simp only [Category.assoc, ht₁s, ht₂s, hE₂s, coprod.inr_desc, coprod.inl_desc_assoc,
            hE₁w']
      · simp only [← Category.assoc]
        refine (splitAction_twisted ε hεf hεs hα _ τ ?_ ?_).trans
          ((hττ.trans (Category.id_comp (𝟙 V)).symm).trans
            (splitAction_diagonal ε hεf hεs hα _ (𝟙 V) ?_ ?_).symm)
        · simp only [Category.assoc, ht₁f, hE₂f', coprod.inr_desc, coprod.inr_desc_assoc, hE₁k', hα,
            Category.id_comp]
        · simp only [Category.assoc, ht₁s, hE₂s, coprod.inr_desc, coprod.inr_desc_assoc, hE₁w',
            Category.comp_id, hss, hkey]
        · simp only [Category.assoc, ht₂f, hE₂f', coprod.inr_desc, coprod.inr_desc_assoc, hE₁u,
            Category.id_comp]
        · simp only [Category.assoc, ht₂s, hE₂s, coprod.inr_desc, coprod.inr_desc_assoc, hE₁w',
            Category.id_comp, Category.comp_id, hss]
  -- the law for an arbitrary test object follows by functoriality of the action
  refine (cocycle_iff_gluingAction_act_act (Over.mk p) φ h1 h2).mpr ?_
  intro Z v x y
  have h := congrArg (prod.lift (prod.lift v x) y ≫ ·) huniv
  simpa only [comp_gluingAction, Category.assoc, prod.lift_fst, prod.lift_snd,
    prod.lift_fst_assoc, prod.lift_snd_assoc] using h

/-- **A semilinear involution with no descended scheme is a descent datum which is not
effective.** Let `g : T ⟶ S` be a morphism whose self-product splits as `T ⨿ T` with second
projection `1 ⨿ s` for an involution `s`, let `p : V ⟶ T` be a scheme over `T` and let `τ` be an
involution of `V` lying over `s`.  If there is no scheme `W₀` over `S` together with an
isomorphism `T ×_S W₀ ≅ V` over `T` whose inverse followed by the projection to `W₀` is
`τ`-invariant, then there is a descent datum relative to `g` which is not effective.

The datum is the one assembled from `τ` by
`AlgebraicGeometry.exists_pullbackIso_of_semilinear` and
`AlgebraicGeometry.cocycle_of_semilinear`.  Effectivity would produce exactly the data the
hypothesis forbids: `AlgebraicGeometry.DescentData.exists_descent_proj_of_isEffective` gives the
descended scheme together with the invariance of the projection to it for the action on
generalized points, and evaluating that invariance at the generalized point of `V` given by the
identity and the twisted structure morphism `p ≫ s`, where the action is `τ`, is the
`τ`-invariance. -/
theorem exists_descentDatum_not_isEffective_of_semilinear
    (hsplit : IsPullback (coprod.desc (𝟙 T) (𝟙 T)) (coprod.desc (𝟙 T) s) g g)
    (hss : s ≫ s = 𝟙 T) (hττ : τ ≫ τ = 𝟙 V) (hτ : τ ≫ p = p ≫ s)
    (hno : ∀ (W₀ : Scheme.{u}) (w₀ : W₀ ⟶ S) (α₀ : pullback g w₀ ≅ V),
      α₀.hom ≫ p = pullback.fst g w₀ →
      τ ≫ α₀.inv ≫ pullback.snd g w₀ = α₀.inv ≫ pullback.snd g w₀ → False) :
    ∃ D : DescentDatum g, ¬ DescentData.IsEffective D := by
  have hiso : IsIso τ := ⟨τ, hττ, hττ⟩
  obtain ⟨Θ, hΘ1, hΘ2, -, hΘ4⟩ := exists_pullbackIso_of_semilinear hsplit hss p τ hτ
  obtain ⟨ε, hεf, hεs, hεα⟩ : ∃ ε : V ⨿ V ≅ pullback (p ≫ g) g,
      ε.hom ≫ pullback.fst (p ≫ g) g = coprod.desc (𝟙 V) (𝟙 V) ∧
        ε.hom ≫ pullback.snd (p ≫ g) g = coprod.desc p (p ≫ s) ∧
        ε.hom ≫ Θ.hom ≫ pullback.snd g (p ≫ g) = coprod.desc (𝟙 V) τ :=
    ⟨(isPullback_baseChange_split_of_isPullback hsplit p).isoPullback,
      (isPullback_baseChange_split_of_isPullback hsplit p).isoPullback_hom_fst,
      (isPullback_baseChange_split_of_isPullback hsplit p).isoPullback_hom_snd, hΘ4⟩
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ((Over.map g).obj (Over.mk p) ⨯ Over.mk g).left ≅
        pullback (p ≫ g) g,
      k.hom ≫ pullback.fst (p ≫ g) g =
          (prod.fst : (Over.map g).obj (Over.mk p) ⨯ Over.mk g ⟶ _).left ∧
        k.hom ≫ pullback.snd (p ≫ g) g =
          (prod.snd : (Over.map g).obj (Over.mk p) ⨯ Over.mk g ⟶ _).left :=
    ⟨Over.prodLeftIsoPullback _ _, Over.prodLeftIsoPullback_hom_fst _ _,
      Over.prodLeftIsoPullback_hom_snd _ _⟩
  obtain ⟨k', hk'1, hk'2⟩ : ∃ k' : (Over.mk g ⨯ (Over.map g).obj (Over.mk p)).left ≅
        pullback g (p ≫ g),
      k'.inv ≫ (prod.fst : Over.mk g ⨯ (Over.map g).obj (Over.mk p) ⟶ _).left =
          pullback.fst g (p ≫ g) ∧
        k'.inv ≫ (prod.snd : Over.mk g ⨯ (Over.map g).obj (Over.mk p) ⟶ _).left =
          pullback.snd g (p ≫ g) :=
    ⟨Over.prodLeftIsoPullback _ _, Over.prodLeftIsoPullback_inv_fst _ _,
      Over.prodLeftIsoPullback_inv_snd _ _⟩
  have hsg : s ≫ g = g := by
    have h := congrArg (fun t => (coprod.inr : T ⟶ T ⨿ T) ≫ t) hsplit.w
    simpa only [coprod.inr_desc_assoc, Category.id_comp] using h.symm
  -- the candidate gluing morphism in the `Over S` products, and its action
  have key1 : (k ≪≫ Θ ≪≫ k'.symm).hom ≫
      (prod.fst : Over.mk g ⨯ (Over.map g).obj (Over.mk p) ⟶ _).left =
        (prod.fst : (Over.map g).obj (Over.mk p) ⨯ Over.mk g ⟶ _).left ≫ p := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hk'1]
    rw [hΘ1, ← Category.assoc, hk1]
  have key2 : (k ≪≫ Θ ≪≫ k'.symm).hom ≫
      (prod.snd : Over.mk g ⨯ (Over.map g).obj (Over.mk p) ⟶ _).left ≫ p =
        (prod.snd : (Over.map g).obj (Over.mk p) ⨯ Over.mk g ⟶ _).left := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← Category.assoc _ _ p, hk'2, hΘ2, hk2]
  have hover : (k ≪≫ Θ ≪≫ k'.symm).hom ≫ (Over.mk g ⨯ (Over.map g).obj (Over.mk p)).hom =
      ((Over.map g).obj (Over.mk p) ⨯ Over.mk g).hom := by
    rw [← Over.w (prod.fst : Over.mk g ⨯ (Over.map g).obj (Over.mk p) ⟶ Over.mk g),
      ← Category.assoc, key1, Category.assoc]
    exact Over.w (prod.fst : (Over.map g).obj (Over.mk p) ⨯ Over.mk g ⟶ _)
  have h1 : (Over.isoMk (k ≪≫ Θ ≪≫ k'.symm) hover).hom ≫ prod.fst =
      prod.fst ≫ structureMap g (Over.mk p) := by
    refine Over.OverMorphism.ext ?_
    simpa using key1
  have h2 : (Over.isoMk (k ≪≫ Θ ≪≫ k'.symm) hover).hom ≫
      prod.snd ≫ structureMap g (Over.mk p) = prod.snd := by
    refine Over.OverMorphism.ext ?_
    simpa using key2
  have hAct : ∀ {Z : Over S} (v : Z ⟶ (Over.map g).obj (Over.mk p)) (x : Z ⟶ Over.mk g),
      (gluingAction (Over.mk p) (Over.isoMk (k ≪≫ Θ ≪≫ k'.symm) hover).hom v x).left =
        ((prod.lift v x).left ≫ k.hom) ≫ Θ.hom ≫ pullback.snd g (p ≫ g) := by
    intro Z v x
    simp only [gluingAction, Over.comp_left, Over.isoMk_hom_left, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, hk'2]
  have hw : (Over.isoMk (k ≪≫ Θ ≪≫ k'.symm) hover).hom ≫
      prod.map (𝟙 (Over.mk g)) (structureMap g (Over.mk p)) =
      prod.map (structureMap g (Over.mk p)) (𝟙 (Over.mk g)) := by
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, prod.map_fst, Category.comp_id, prod.map_fst]
      exact h1
    · rw [Category.assoc, prod.map_snd, prod.map_snd, Category.comp_id]
      exact h2
  have hxw : (p ≫ s) ≫ (Over.mk g).hom = ((Over.map g).obj (Over.mk p)).hom := by
    change (p ≫ s) ≫ g = p ≫ g
    rw [Category.assoc, hsg]
  -- at the generalized point given by the identity and the twisted structure morphism, the
  -- action is `τ`
  have hacttwist : (gluingAction (Over.mk p) (Over.isoMk (k ≪≫ Θ ≪≫ k'.symm) hover).hom
      (𝟙 ((Over.map g).obj (Over.mk p))) (Over.homMk (p ≫ s) hxw)).left = τ := by
    rw [hAct]
    refine (splitAction_twisted ε hεf hεs hεα _ (𝟙 V) ?_ ?_).trans (Category.id_comp τ)
    · rw [Category.assoc, hk1, ← Over.comp_left, prod.lift_fst]
      rfl
    · rw [Category.assoc, hk2, ← Over.comp_left, prod.lift_snd, Category.id_comp]
      rfl
  refine ⟨DescentDatum.mk' (Over.mk p) (Over.isoMk (Over.isoMk (k ≪≫ Θ ≪≫ k'.symm) hover) hw)
    (cocycle_of_semilinear ε hεf hεs hsplit hss hττ hτ _ h1 h2 k hk1 hk2 hεα hAct), ?_⟩
  intro hEff
  obtain ⟨W₀, w₀, α₀, hα₀, hinv⟩ := DescentData.exists_descent_proj_of_isEffective _ hEff
  refine hno W₀ w₀ α₀ hα₀ ?_
  have h := hinv (Z := (Over.map g).obj (Over.mk p)) (𝟙 _) (Over.homMk (p ≫ s) hxw)
  rw [← hacttwist]
  exact h.trans (Category.id_comp _)

end AlgebraicGeometry

end
