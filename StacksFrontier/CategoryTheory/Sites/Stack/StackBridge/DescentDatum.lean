module

public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.RestrictionBase

/-!
# The gluing isomorphisms of a descent datum relative to a covering family

A `CategoryTheory.Functor.DescentDatum` supplies gluing isomorphisms `φ i j` between restrictions
of `x i` and `x j` over the overlap `Vᵢ ×_U Vⱼ`, and asserts the cocycle condition through
auxiliary morphisms `αij`, `αjk`, `αik` over the triple overlap which are required to be *canonical
restrictions* of the `φ`s. Nothing in `CategoryTheory.Functor.IsRestrictionOf` forces those
auxiliary morphisms to lie over an identity, and that is what the first result below supplies: the
base morphism of `αij` fixes `s₁₂` because `αij` is a restriction of `φ i j`, it fixes `q₃` because
of the cocycle condition, hence it fixes `s₂₃` because `Vⱼ ×_U Vₖ` is a *genuine* fibre product,
and hence it is the identity because the triple overlap is one too.

With that in hand the gluing isomorphisms are transported to an arbitrary pair of morphisms into
`Vᵢ` and `Vⱼ` agreeing over `U`, which is well defined because such a pair factors uniquely through
the overlap, and the cocycle condition is proved in that generality.

## Main definitions

* `CategoryTheory.Functor.DescentDatum.glueIso`, the gluing isomorphism read between the chosen
  pullbacks;
* `CategoryTheory.Functor.DescentDatum.glue`, that isomorphism transported to an arbitrary
  agreeing pair.

## Main results

* `CategoryTheory.Functor.DescentDatum.isHomLift_id_αij`, that the auxiliary morphisms of the
  cocycle condition lie over an identity;
* `CategoryTheory.Functor.DescentDatum.glue_trans`, the resulting cocycle condition for
  `CategoryTheory.Functor.DescentDatum.glue`.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe w v₁ v₂ u₁ u₂

namespace Functor

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

variable {p : 𝒳 ⥤ 𝒞} [p.IsFibered]
variable {U : 𝒞} {I : Type w} {V : I → 𝒞} {f : ∀ i, V i ⟶ U}
  {Vij : I → I → 𝒞} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
  {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
  {Vijk : I → I → I → 𝒞}
  {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
  {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
  {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
  {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
  {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
  {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
  {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}
  (D : DescentDatum p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)

/-- The auxiliary morphisms of the cocycle condition are morphisms of the fibre over the triple
overlap. This is not part of the datum: it is forced by the cocycle condition together with the
requirement that the double and triple overlaps be genuine fibre products. -/
lemma DescentDatum.isHomLift_id_αij (i j k : I) :
    p.IsHomLift (𝟙 (Vijk i j k)) (D.αij i j k) ∧
      p.IsHomLift (𝟙 (Vijk i j k)) (D.αjk i j k) ∧
      p.IsHomLift (𝟙 (Vijk i j k)) (D.αik i j k) := by
  obtain ⟨e₁, he₁⟩ := exists_isHomLift_base (D.wi i j k).hpt (D.wj i j k).hpt (D.αij i j k)
  obtain ⟨e₂, he₂⟩ := exists_isHomLift_base (D.wj i j k).hpt (D.wk i j k).hpt (D.αjk i j k)
  obtain ⟨e₃, he₃⟩ := exists_isHomLift_base (D.wi i j k).hpt (D.wk i j k).hpt (D.αik i j k)
  -- the three base morphisms fix the three projections they come from
  have h₁ : e₁ ≫ s₁₂ i j k = s₁₂ i j k :=
    comp_eq_of_isRestrictionOf (hq₁ i j k) (hq₂ i j k) (D.xrij i j) (D.xrji i j)
      (D.wi i j k) (D.wj i j k) (D.φ_fibreHom i j) he₁ (D.αij_restr i j k)
  have h₂ : e₂ ≫ s₂₃ i j k = s₂₃ i j k :=
    comp_eq_of_isRestrictionOf ((hq₂ i j k).trans (hVijk i j k).w) (hq₃ i j k)
      (D.xrij j k) (D.xrji j k) (D.wj i j k) (D.wk i j k) (D.φ_fibreHom j k) he₂
      (D.αjk_restr i j k)
  have h₃ : e₃ ≫ D.s₁₃ i j k = D.s₁₃ i j k :=
    comp_eq_of_isRestrictionOf (D.hs₁₃₁ i j k).symm (D.hs₁₃₂ i j k).symm
      (D.xrij i k) (D.xrji i k) (D.wi i j k) (D.wk i j k) (D.φ_fibreHom i k) he₃
      (D.αik_restr i j k)
  -- the cocycle condition identifies `e₃` with `e₁ ≫ e₂`
  have hcomp : e₃ = e₁ ≫ e₂ := by
    have hl : p.IsHomLift (e₁ ≫ e₂) (D.αij i j k ≫ D.αjk i j k) := by
      have := he₁; have := he₂; infer_instance
    rw [← D.cocycle i j k] at hl
    exact eq_of_isHomLift_of_isHomLift he₃ hl
  -- read off what each base morphism does to the three projections
  have e₁q₁ : e₁ ≫ q₁ i j k = q₁ i j k := by rw [hq₁, ← Category.assoc, h₁]
  have e₁q₂ : e₁ ≫ q₂ i j k = q₂ i j k := by rw [hq₂, ← Category.assoc, h₁]
  have e₂q₂ : e₂ ≫ q₂ i j k = q₂ i j k := by
    rw [(hq₂ i j k).trans (hVijk i j k).w, ← Category.assoc, h₂]
  have e₂q₃ : e₂ ≫ q₃ i j k = q₃ i j k := by rw [hq₃, ← Category.assoc, h₂]
  have e₃q₁ : e₃ ≫ q₁ i j k = q₁ i j k := by
    rw [← D.hs₁₃₁ i j k, ← Category.assoc, h₃]
  have e₃q₃ : e₃ ≫ q₃ i j k = q₃ i j k := by
    rw [← D.hs₁₃₂ i j k, ← Category.assoc, h₃]
  -- hence `e₁` fixes `q₃`, so it fixes `s₂₃` because the overlap is a genuine fibre product
  have e₁q₃ : e₁ ≫ q₃ i j k = q₃ i j k := by
    have := e₃q₃
    rw [hcomp, Category.assoc, e₂q₃] at this
    exact this
  have h₁' : e₁ ≫ s₂₃ i j k = s₂₃ i j k := by
    refine (hVij j k).hom_ext ?_ ?_
    · rw [Category.assoc, ← (hq₂ i j k).trans (hVijk i j k).w, e₁q₂,
        (hq₂ i j k).trans (hVijk i j k).w]
    · rw [Category.assoc, ← hq₃ i j k, e₁q₃, hq₃ i j k]
  have he₁id : e₁ = 𝟙 (Vijk i j k) := by
    refine (hVijk i j k).hom_ext ?_ ?_
    · rw [h₁, Category.id_comp]
    · rw [h₁', Category.id_comp]
  -- and then `e₂ = e₃` fixes `q₁` as well, so it too is the identity
  have he₂q₁ : e₂ ≫ q₁ i j k = q₁ i j k := by
    have := e₃q₁
    rwa [hcomp, he₁id, Category.id_comp] at this
  have h₂' : e₂ ≫ s₁₂ i j k = s₁₂ i j k := by
    refine (hVij i j).hom_ext ?_ ?_
    · rw [Category.assoc, ← hq₁ i j k, he₂q₁, hq₁ i j k]
    · rw [Category.assoc, ← hq₂ i j k, e₂q₂, hq₂ i j k]
  have he₂id : e₂ = 𝟙 (Vijk i j k) := by
    refine (hVijk i j k).hom_ext ?_ ?_
    · rw [h₂', Category.id_comp]
    · rw [h₂, Category.id_comp]
  refine ⟨he₁id ▸ he₁, he₂id ▸ he₂, ?_⟩
  have : e₃ = 𝟙 (Vijk i j k) := by rw [hcomp, he₁id, he₂id, Category.id_comp]
  exact this ▸ he₃

/-- The gluing isomorphism of a descent datum over the overlap `Vᵢ ×_U Vⱼ`, read between the chosen
pullbacks of the two objects it compares. -/
noncomputable def DescentDatum.glueIso (i j : I) :
    pullbackFiber p (Fiber.mk (D.hx i)) (pr₁ i j) ≅
      pullbackFiber p (Fiber.mk (D.hx j)) (pr₂ i j) :=
  (D.xrij i j).fiberIsoOf (D.xrji i j) (D.φ_fibreHom i j) (D.φ_iso i j)

/-- The forward direction of `CategoryTheory.Functor.DescentDatum.glueIso` is the reading of the
gluing isomorphism `φᵢⱼ` as a morphism between the chosen pullbacks. -/
@[simp]
lemma DescentDatum.glueIso_hom (i j : I) :
    (D.glueIso i j).hom = (D.xrij i j).fiberMor (D.xrji i j) (D.φ_fibreHom i j) := rfl

/-- The gluing isomorphism of a descent datum, transported to an arbitrary pair of morphisms into
`Vᵢ` and `Vⱼ` that agree over `U`. Because the overlap is a *genuine* fibre product, such a pair
factors through it uniquely, so this is well defined and functorial in the pair. -/
noncomputable def DescentDatum.glue {Z : 𝒞} (i j : I) (u : Z ⟶ V i) (v : Z ⟶ V j)
    (huv : u ≫ f i = v ≫ f j) :
    pullbackFiber p (Fiber.mk (D.hx i)) u ≅ pullbackFiber p (Fiber.mk (D.hx j)) v :=
  baseChangeFiberIso (D.glueIso i j) ((hVij i j).lift u v huv) u
    ((hVij i j).lift_fst u v huv) v ((hVij i j).lift_snd u v huv)

/-- `CategoryTheory.Functor.DescentDatum.glue` computed at any named factorization through the
overlap. -/
lemma DescentDatum.glue_eq {Z : 𝒞} (i j : I) (g : Z ⟶ Vij i j) {u : Z ⟶ V i} {v : Z ⟶ V j}
    (hu : g ≫ pr₁ i j = u) (hv : g ≫ pr₂ i j = v) (huv : u ≫ f i = v ≫ f j) :
    D.glue i j u v huv = baseChangeFiberIso (D.glueIso i j) g u hu v hv := by
  rw [DescentDatum.glue]
  exact baseChangeFiberIso_congr _
    ((hVij i j).hom_ext (by rw [(hVij i j).lift_fst, hu]) (by rw [(hVij i j).lift_snd, hv])) _ _ _ _

/-- The gluing isomorphisms are compatible with base change. -/
lemma DescentDatum.glue_baseChange {Z Z' : 𝒞} (i j : I) (u : Z ⟶ V i) (v : Z ⟶ V j)
    (huv : u ≫ f i = v ≫ f j) (γ : Z' ⟶ Z) (u' : Z' ⟶ V i) (hu' : γ ≫ u = u')
    (v' : Z' ⟶ V j) (hv' : γ ≫ v = v') (hu'v' : u' ≫ f i = v' ≫ f j) :
    baseChangeFiberMor (D.glue i j u v huv).hom γ u' hu' v' hv' =
      (D.glue i j u' v' hu'v').hom := by
  rw [DescentDatum.glue, baseChangeFiberIso_hom, baseChangeFiberMor_baseChangeFiberMor,
    D.glue_eq i j (γ ≫ (hVij i j).lift u v huv)
      (by rw [Category.assoc, (hVij i j).lift_fst, hu'])
      (by rw [Category.assoc, (hVij i j).lift_snd, hv']) hu'v', baseChangeFiberIso_hom]

/-- **The cocycle condition, over the triple overlap.** The three gluing isomorphisms of a descent
datum, transported to the triple overlap along its three projections, compose. -/
lemma DescentDatum.glue_trans_triple (i j k : I)
    (hA : q₁ i j k ≫ f i = q₂ i j k ≫ f j) (hB : q₂ i j k ≫ f j = q₃ i j k ≫ f k)
    (hC : q₁ i j k ≫ f i = q₃ i j k ≫ f k) :
    (D.glue i j (q₁ i j k) (q₂ i j k) hA).hom ≫ (D.glue j k (q₂ i j k) (q₃ i j k) hB).hom =
      (D.glue i k (q₁ i j k) (q₃ i j k) hC).hom := by
  obtain ⟨h1, h2, h3⟩ := D.isHomLift_id_αij i j k
  have hαij := fibreHom_of_isHomLift_id (D.wi i j k).hpt (D.wj i j k).hpt h1
  have hαjk := fibreHom_of_isHomLift_id (D.wj i j k).hpt (D.wk i j k).hpt h2
  have hαik := fibreHom_of_isHomLift_id (D.wi i j k).hpt (D.wk i j k).hpt h3
  -- each transported gluing isomorphism is the reading of the corresponding auxiliary morphism
  have eij : (D.glue i j (q₁ i j k) (q₂ i j k) hA).hom =
      (D.wi i j k).fiberMor (D.wj i j k) hαij := by
    rw [D.glue_eq i j (s₁₂ i j k) (hq₁ i j k).symm (hq₂ i j k).symm hA, baseChangeFiberIso_hom,
      DescentDatum.glueIso_hom]
    exact (fiberMor_eq_baseChangeFiberMor (hq₁ i j k) (hq₂ i j k) (D.xrij i j) (D.xrji i j)
      (D.wi i j k) (D.wj i j k) (D.φ_fibreHom i j) hαij (D.αij_restr i j k)).symm
  have ejk : (D.glue j k (q₂ i j k) (q₃ i j k) hB).hom =
      (D.wj i j k).fiberMor (D.wk i j k) hαjk := by
    rw [D.glue_eq j k (s₂₃ i j k) ((hq₂ i j k).trans (hVijk i j k).w).symm (hq₃ i j k).symm hB,
      baseChangeFiberIso_hom, DescentDatum.glueIso_hom]
    exact (fiberMor_eq_baseChangeFiberMor ((hq₂ i j k).trans (hVijk i j k).w) (hq₃ i j k)
      (D.xrij j k) (D.xrji j k) (D.wj i j k) (D.wk i j k) (D.φ_fibreHom j k) hαjk
      (D.αjk_restr i j k)).symm
  have eik : (D.glue i k (q₁ i j k) (q₃ i j k) hC).hom =
      (D.wi i j k).fiberMor (D.wk i j k) hαik := by
    rw [D.glue_eq i k (D.s₁₃ i j k) (D.hs₁₃₁ i j k) (D.hs₁₃₂ i j k) hC, baseChangeFiberIso_hom,
      DescentDatum.glueIso_hom]
    exact (fiberMor_eq_baseChangeFiberMor (D.hs₁₃₁ i j k).symm (D.hs₁₃₂ i j k).symm
      (D.xrij i k) (D.xrji i k) (D.wi i j k) (D.wk i j k) (D.φ_fibreHom i k) hαik
      (D.αik_restr i j k)).symm
  rw [eij, ejk, eik]
  have hcomp : FibreHom p (D.wi i j k).pt (D.wk i j k).pt (D.wi i j k).hpt (D.wk i j k).hpt
      (D.αij i j k ≫ D.αjk i j k) :=
    fibreHom_of_isHomLift_id _ _ (by
      have := h1; have := h2
      exact isHomLift_of_eq (n := 𝟙 _ ≫ 𝟙 _) inferInstance (by simp))
  rw [Restriction.fiberMor_congr (D.wi i j k) (D.wk i j k) (D.cocycle i j k) hαik hcomp,
    Restriction.fiberMor_comp (D.wi i j k) (D.wj i j k) (D.wk i j k) hαij hαjk hcomp]

/-- **The cocycle condition.** The gluing isomorphisms of a descent datum, transported to any
triple of morphisms into `Vᵢ`, `Vⱼ`, `Vₖ` agreeing over `U`, compose. The triple of morphisms
factors through the triple overlap because the latter is a genuine fibre product, so this follows
from `CategoryTheory.Functor.DescentDatum.glue_trans_triple` by base change. -/
lemma DescentDatum.glue_trans {Z : 𝒞} (i j k : I) (u : Z ⟶ V i) (v : Z ⟶ V j) (w : Z ⟶ V k)
    (h₁ : u ≫ f i = v ≫ f j) (h₂ : v ≫ f j = w ≫ f k) (h₃ : u ≫ f i = w ≫ f k) :
    (D.glue i j u v h₁).hom ≫ (D.glue j k v w h₂).hom = (D.glue i k u w h₃).hom := by
  have hmid : (hVij i j).lift u v h₁ ≫ pr₂ i j = (hVij j k).lift v w h₂ ≫ pr₁ j k := by
    rw [(hVij i j).lift_snd, (hVij j k).lift_fst]
  set ζ := (hVijk i j k).lift ((hVij i j).lift u v h₁) ((hVij j k).lift v w h₂) hmid with hζ
  have hζ1 : ζ ≫ s₁₂ i j k = (hVij i j).lift u v h₁ := (hVijk i j k).lift_fst _ _ hmid
  have hζ2 : ζ ≫ s₂₃ i j k = (hVij j k).lift v w h₂ := (hVijk i j k).lift_snd _ _ hmid
  have hζq₁ : ζ ≫ q₁ i j k = u := by
    rw [hq₁, ← Category.assoc, hζ1, (hVij i j).lift_fst]
  have hζq₂ : ζ ≫ q₂ i j k = v := by
    rw [hq₂, ← Category.assoc, hζ1, (hVij i j).lift_snd]
  have hζq₃ : ζ ≫ q₃ i j k = w := by
    rw [hq₃, ← Category.assoc, hζ2, (hVij j k).lift_snd]
  have hA : q₁ i j k ≫ f i = q₂ i j k ≫ f j := by
    rw [hq₁, hq₂, Category.assoc, Category.assoc, (hVij i j).w]
  have hB : q₂ i j k ≫ f j = q₃ i j k ≫ f k := by
    rw [(hq₂ i j k).trans (hVijk i j k).w, hq₃, Category.assoc, Category.assoc, (hVij j k).w]
  have hC : q₁ i j k ≫ f i = q₃ i j k ≫ f k := by
    rw [← D.hs₁₃₁ i j k, ← D.hs₁₃₂ i j k, Category.assoc, Category.assoc, (hVij i k).w]
  rw [← D.glue_baseChange i j (q₁ i j k) (q₂ i j k) hA ζ u hζq₁ v hζq₂ h₁,
    ← D.glue_baseChange j k (q₂ i j k) (q₃ i j k) hB ζ v hζq₂ w hζq₃ h₂,
    ← D.glue_baseChange i k (q₁ i j k) (q₃ i j k) hC ζ u hζq₁ w hζq₃ h₃,
    ← baseChangeFiberMor_comp, D.glue_trans_triple i j k hA hB hC]

/-- The gluing isomorphism of an index with itself, along one and the same morphism, is the
identity: it is an idempotent isomorphism by the cocycle condition. -/
lemma DescentDatum.glue_self {Z : 𝒞} (i : I) (u : Z ⟶ V i) (h : u ≫ f i = u ≫ f i) :
    (D.glue i i u u h).hom = 𝟙 _ :=
  eq_id_of_comp_self_eq (D.glue i i u u h) (D.glue_trans i i i u u u h h h)

/-- The two gluing isomorphisms of a pair of indices are inverse to each other. -/
lemma DescentDatum.glue_symm {Z : 𝒞} (i j : I) (u : Z ⟶ V i) (v : Z ⟶ V j)
    (h : u ≫ f i = v ≫ f j) : (D.glue j i v u h.symm).hom = (D.glue i j u v h).inv := by
  rw [← cancel_epi (D.glue i j u v h).hom, Iso.hom_inv_id,
    D.glue_trans i j i u v u h h.symm rfl, D.glue_self]

/-- The gluing isomorphism over the overlap itself is the transported one at the two
projections. -/
lemma DescentDatum.glueIso_eq_glue (i j : I) :
    (D.glueIso i j).hom = (D.glue i j (pr₁ i j) (pr₂ i j) (hVij i j).w).hom := by
  rw [D.glue_eq i j (𝟙 (Vij i j)) (Category.id_comp _) (Category.id_comp _) (hVij i j).w,
    baseChangeFiberIso_hom, baseChangeFiberMor_id]

/-- Base change of a gluing isomorphism, read as a morphism between the chosen pullbacks of the
chosen pullbacks. -/
lemma DescentDatum.pullbackFiberHom_glue {Z Z' : 𝒞} (i j : I) (u : Z ⟶ V i) (v : Z ⟶ V j)
    (huv : u ≫ f i = v ≫ f j) (γ : Z' ⟶ Z) (u' : Z' ⟶ V i) (hu' : γ ≫ u = u')
    (v' : Z' ⟶ V j) (hv' : γ ≫ v = v') (hu'v' : u' ≫ f i = v' ≫ f j) :
    pullbackFiberHom (D.glue i j u v huv).hom γ =
      (pullbackFiberCompIso' (Fiber.mk (D.hx i)) u γ u' hu').hom ≫
        (D.glue i j u' v' hu'v').hom ≫
        (pullbackFiberCompIso' (Fiber.mk (D.hx j)) v γ v' hv').inv := by
  rw [pullbackFiberHom_eq_baseChange _ γ u' hu' v' hv', D.glue_baseChange i j u v huv γ u' hu'
    v' hv' hu'v']

end Functor

end CategoryTheory
