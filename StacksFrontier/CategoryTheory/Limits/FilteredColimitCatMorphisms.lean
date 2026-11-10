module

public import Mathlib.AlgebraicTopology.Quasicategory.StrictSegal
public import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncatedQuasicategory
public import Mathlib.CategoryTheory.Category.Cat.Colimit
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Data.Fintype.Sum
import all Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms of a filtered colimit of categories are identified only at a later stage

Let `F : J ⥤ Cat` be a filtered diagram of categories and let `f`, `g` be two parallel morphisms
of one stage `F j` whose images in `colimit F` agree. Then they already agree at some later
stage: there is `u : j ⟶ k` with `(F.map u).map f = (F.map u).map g`.

## Main results

* `CategoryTheory.Cat.exists_common_stage_eq_of_colimit_ι_map_eq`

## Implementation notes

The colimit of a diagram of categories is computed in Mathlib by passing to nerves, so it is a
quotient, and neither its objects nor its morphisms are presented as coming from a stage. For a
*filtered* diagram the `2`-truncated nerve of the colimit is nevertheless the levelwise colimit
of the `2`-truncated nerves: the levelwise colimit is strictly Segal, because a path of
`1`-simplices and an equality of simplices in a filtered colimit of types are both witnessed at a
single stage, and for a strictly Segal `2`-truncated simplicial set the unit of the nerve
adjunction is an isomorphism, which transports the colimit through the adjunction. A morphism of
one stage is a `1`-simplex of its nerve, so the statement becomes the identification of two
elements of a filtered colimit of types, which is
`CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'`.

## References

* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 0CMS](https://stacks.math.columbia.edu/tag/0CMS)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Cat

section ColimitBridge

open CategoryTheory.Limits Opposite SimplexCategory
open scoped Simplicial
open CategoryTheory.Limits.Types.FilteredColimit

universe v w wJ

variable {J : Type v} [Category.{wJ} J] [IsFiltered J]
  [UnivLE.{v, w}] [UnivLE.{wJ, w}]
variable (F : J ⥤ Cat.{w, w})

/-- The diagram `F : J ⥤ Cat.{w, w}` has a colimit, since the universe levels of `J` are at most
`w`. -/
local instance : HasColimit F := by
  let : HasColimitsOfSize.{wJ, v} Cat.{w, w} :=
    hasColimitsOfSizeOfUnivLE.{w, w, wJ, v} Cat
  infer_instance

omit [UnivLE.{v, w}] [UnivLE.{wJ, w}] in
private lemma filteredType_family_stage {G : J ⥤ Type w} [HasColimit G]
    {α : Type*} [Finite α] (x : α → colimit G) :
    ∃ (j : J) (y : α → G.obj j), ∀ a, (colimit.ι G j) (y a) = x a := by
  classical
  let := Fintype.ofFinite α
  refine Fintype.induction_empty_option
    (P := fun α _ => ∀ x : α → colimit G,
      ∃ (j : J) (y : α → G.obj j), ∀ a, (colimit.ι G j) (y a) = x a)
    ?_ ?_ ?_ α x
  · intro α β _ e ih x
    obtain ⟨j, y, hy⟩ := ih (fun a => x (e a))
    exact ⟨j, fun b => y (e.symm b), fun a => by simpa using hy (e.symm a)⟩
  · intro x
    let j : J := Classical.choice (IsFiltered.nonempty (C := J))
    exact ⟨j, fun a => a.elim, fun a => a.elim⟩
  · intro α _ ih x
    obtain ⟨j, y, hy⟩ := ih (x ∘ Option.some)
    obtain ⟨k, z, hz⟩ := Types.jointly_surjective' (x none)
    let l := IsFiltered.max j k
    refine ⟨l, fun a => a.elim (G.map (IsFiltered.rightToMax j k) z)
      (fun a => G.map (IsFiltered.leftToMax j k) (y a)), ?_⟩
    intro a
    cases a with
    | none =>
        calc
          (colimit.ι G l) (G.map (IsFiltered.rightToMax j k) z) =
              (colimit.ι G k) z := by simp [l]
          _ = x none := hz
    | some a =>
        calc
          (colimit.ι G l) (G.map (IsFiltered.leftToMax j k) (y a)) =
              (colimit.ι G j) (y a) := by simp [l]
          _ = (x ∘ Option.some) a := hy a

omit [UnivLE.{v, w}] [UnivLE.{wJ, w}] in
/-- Finitely many equalities in a filtered colimit of types become equal at a
single later stage. -/
@[sga "4 I 2.8.1" "4: forward implication"]
private lemma filteredType_family_eq_eventually {G : J ⥤ Type w} [HasColimit G]
    {α : Type*} [Finite α] (j : J) (x y : α → G.obj j)
    (h : ∀ a, (colimit.ι G j) (x a) = (colimit.ι G j) (y a)) :
    ∃ (j' : J) (f : j ⟶ j'), ∀ a, G.map f (x a) = G.map f (y a) := by
  classical
  let := Fintype.ofFinite α
  refine Fintype.induction_empty_option
    (P := fun α _ => ∀ (j : J) (x y : α → G.obj j),
      (∀ a, (colimit.ι G j) (x a) = (colimit.ι G j) (y a)) →
      ∃ (j' : J) (f : j ⟶ j'), ∀ a, G.map f (x a) = G.map f (y a))
    ?_ ?_ ?_ α j x y h
  · intro α β _ e ih j x y h
    obtain ⟨j', f, hf⟩ := ih j (fun a => x (e a)) (fun a => y (e a)) (fun a => h (e a))
    exact ⟨j', f, fun b => by simpa using hf (e.symm b)⟩
  · intro j x y h
    exact ⟨j, 𝟙 j, fun a => a.elim⟩
  · intro α _ ih j x y h
    obtain ⟨j₁, f₁, h₁⟩ := ih j (fun a => x (Option.some a))
      (fun a => y (Option.some a)) (fun a => h (Option.some a))
    obtain ⟨k, f₂, h₂⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit G)
        (x Option.none) (y Option.none)).mp (h Option.none)
    obtain ⟨l, u, v, -⟩ := IsFilteredOrEmpty.cocone_objs j₁ k
    let g₁ := f₁ ≫ u
    let g₂ := f₂ ≫ v
    let m := IsFiltered.coeq g₁ g₂
    let t := IsFiltered.coeqHom g₁ g₂
    refine ⟨m, g₁ ≫ t, ?_⟩
    intro a
    cases a with
    | none =>
        have hm : g₂ ≫ t = g₁ ≫ t := (IsFiltered.coeq_condition g₁ g₂).symm
        rw [← hm]
        simpa [t, g₂, g₁, m] using
          congrArg (G.map t) (congrArg (G.map v) h₂)
    | some a =>
        simpa [t, g₁, m] using
          congrArg (G.map t) (congrArg (G.map u) (h₁ a))

omit [IsFiltered J] [UnivLE.{wJ, w}] in
private lemma nerveColimit_simplex_stage (k : SimplexCategoryᵒᵖ)
    (s : (colimit (F ⋙ nerveFunctor)).obj k) :
    ∃ (j : J) (z : (nerveFunctor.obj (F.obj j)).obj k),
      (colimit.ι (F ⋙ nerveFunctor) j).app k z = s :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ (Type w)).obj k)
      (colimit.isColimit (F ⋙ nerveFunctor))) s

omit [UnivLE.{wJ, w}] in
private lemma nerveColimit_simplex_family_eq_eventually
    (k : SimplexCategoryᵒᵖ) {α : Type*} [Finite α]
    (j : J) (x y : α → (nerveFunctor.obj (F.obj j)).obj k)
    (h : ∀ a, (colimit.ι (F ⋙ nerveFunctor) j).app k (x a) =
      (colimit.ι (F ⋙ nerveFunctor) j).app k (y a)) :
    ∃ (j' : J) (f : j ⟶ j'), ∀ a,
      ((F ⋙ nerveFunctor).map f).app k (x a) =
        ((F ⋙ nerveFunctor).map f).app k (y a) := by
  let ev := (CategoryTheory.evaluation (SimplexCategoryᵒᵖ) (Type w)).obj k
  let H := (F ⋙ nerveFunctor) ⋙ ev
  let e0 := colimitObjIsoColimitCompEvaluation (F ⋙ nerveFunctor) k
  have hι := colimitObjIsoColimitCompEvaluation_ι_app_hom (F := F ⋙ nerveFunctor) j k
  have hh : ∀ a, (colimit.ι H j) (x a) = (colimit.ι H j) (y a) := fun a =>
    (ConcreteCategory.congr_hom hι (x a)).symm.trans
      ((congrArg e0.hom (h a)).trans (ConcreteCategory.congr_hom hι (y a)))
  obtain ⟨j', f, hf⟩ := filteredType_family_eq_eventually (G := H) j x y hh
  refine ⟨j', f, fun a => ?_⟩
  simpa only [H, ev, Functor.comp_map, evaluation_obj_map] using hf a

omit [UnivLE.{wJ, w}] in
/-- A finite family of simplices in the filtered nerve colimit is represented
in one stage. -/
private lemma nerveColimit_simplex_family_stage
    (k : SimplexCategoryᵒᵖ) {α : Type*} [Finite α]
    (s : α → (colimit (F ⋙ nerveFunctor)).obj k) :
    ∃ (j : J) (z : α → (nerveFunctor.obj (F.obj j)).obj k),
      ∀ a, (colimit.ι (F ⋙ nerveFunctor) j).app k (z a) = s a := by
  let ev := (CategoryTheory.evaluation (SimplexCategoryᵒᵖ) (Type w)).obj k
  let H := (F ⋙ nerveFunctor) ⋙ ev
  let e0 := colimitObjIsoColimitCompEvaluation (F ⋙ nerveFunctor) k
  obtain ⟨j, z, hz⟩ := filteredType_family_stage (fun a => e0.hom (s a))
  refine ⟨j, z, fun a => ?_⟩
  have hz1 : e0.inv.hom ((colimit.ι H j) (z a)) = s a := by
    have hh := congrArg e0.inv.hom (hz a)
    change e0.inv.hom
      ((colimit.ι ((F ⋙ nerveFunctor) ⋙
        (CategoryTheory.evaluation (SimplexCategoryᵒᵖ) (Type w)).obj k) j)
        (z a)) = s a
    simpa only [ConcreteCategory.comp_apply, id_apply] using
      hh.trans (ConcreteCategory.congr_hom e0.hom_inv_id (s a))
  have hz2 : e0.inv.hom ((colimit.ι H j) (z a)) =
      (colimit.ι (F ⋙ nerveFunctor) j).app k (z a) := by
    have hh := CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation_ι_inv
      (F := F ⋙ nerveFunctor) j k
    exact ConcreteCategory.congr_hom hh (z a)
  exact hz2.symm.trans hz1

omit [UnivLE.{wJ, w}] in
/-- Every finite path in the 1-skeleton of the filtered nerve colimit is
represented by a path at a common stage. -/
private lemma nerveColimit_path_stage {n : ℕ} (p :
    (colimit (F ⋙ nerveFunctor)).Path n) :
    ∃ (j : J) (q : (nerveFunctor.obj (F.obj j)).Path n),
      (∀ i, (colimit.ι (F ⋙ nerveFunctor) j).app (op ⦋0⦌)
        (q.vertex i) = p.vertex i) ∧
      (∀ i, (colimit.ι (F ⋙ nerveFunctor) j).app (op ⦋1⦌)
        (q.arrow i) = p.arrow i) := by
  classical
  let k₀ : SimplexCategoryᵒᵖ := op ⦋0⦌
  let k₁ : SimplexCategoryᵒᵖ := op ⦋1⦌
  let G := F ⋙ nerveFunctor
  have hι : ∀ {a b : J} (u : a ⟶ b) (m : SimplexCategoryᵒᵖ) (z : (G.obj a).obj m),
      (colimit.ι G b).app m ((G.map u).app m z) = (colimit.ι G a).app m z :=
    fun u m z => ConcreteCategory.congr_hom (NatTrans.congr_app (colimit.w G u) m) z
  obtain ⟨j₀, v₀, hv₀⟩ := nerveColimit_simplex_family_stage F k₀ p.vertex
  obtain ⟨j₁, e₁, he₁⟩ := nerveColimit_simplex_family_stage F k₁ p.arrow
  let l := IsFiltered.max j₀ j₁
  let u₀ := IsFiltered.leftToMax j₀ j₁
  let u₁ := IsFiltered.rightToMax j₀ j₁
  let v : Fin (n + 1) → (G.obj l).obj k₀ := fun i => ((G.map u₀).app k₀) (v₀ i)
  let e : Fin n → (G.obj l).obj k₁ := fun i => ((G.map u₁).app k₁) (e₁ i)
  have hv : ∀ i, (colimit.ι G l).app k₀ (v i) = p.vertex i :=
    fun i => (hι u₀ k₀ (v₀ i)).trans (hv₀ i)
  have he : ∀ i, (colimit.ι G l).app k₁ (e i) = p.arrow i :=
    fun i => (hι u₁ k₁ (e₁ i)).trans (he₁ i)
  let d₁ : k₁ ⟶ k₀ := (SimplexCategory.δ (n := 0) 1).op
  let d₀ : k₁ ⟶ k₀ := (SimplexCategory.δ (n := 0) 0).op
  let src : Fin n ⊕ Fin n → (G.obj l).obj k₀ := fun a => a.elim
    (fun i => (G.obj l).map d₁ (e i)) (fun i => (G.obj l).map d₀ (e i))
  let dst : Fin n ⊕ Fin n → (G.obj l).obj k₀ := fun a => a.elim
    (fun i => v i.castSucc) (fun i => v i.succ)
  have key : ∀ (d : k₁ ⟶ k₀) (i : Fin n) (w : Fin (n + 1)),
      (colimit G).map d (p.arrow i) = p.vertex w →
      (colimit.ι G l).app k₀ ((G.obj l).map d (e i)) = (colimit.ι G l).app k₀ (v w) :=
    fun d i w h => (NatTrans.naturality_apply (colimit.ι G l) d (e i)).trans
      ((congrArg ((colimit G).map d) (he i)).trans (h.trans (hv w).symm))
  have hsrc : ∀ a, (colimit.ι G l).app k₀ (src a) =
      (colimit.ι G l).app k₀ (dst a) := by
    rintro (i | i)
    exacts [key d₁ i _ (p.arrow_src i), key d₀ i _ (p.arrow_tgt i)]
  obtain ⟨j, f, hf⟩ := nerveColimit_simplex_family_eq_eventually F k₀ l src dst hsrc
  let q : (nerveFunctor.obj (F.obj j)).Path n := {
    vertex := fun i => ((G.map f).app k₀) (v i)
    arrow := fun i => ((G.map f).app k₁) (e i)
    arrow_src := fun i => hf (Sum.inl i)
    arrow_tgt := fun i => hf (Sum.inr i) }
  exact ⟨j, q, fun i => (hι f k₀ (v i)).trans (hv i),
    fun i => (hι f k₁ (e i)).trans (he i)⟩

omit [UnivLE.{wJ, w}] in
private lemma nerveColimit_path_eq_eventually {n : ℕ} (j : J)
    (p q : SSet.Path ((F ⋙ nerveFunctor).obj j) n)
    (h : p.map (colimit.ι (F ⋙ nerveFunctor) j) =
      q.map (colimit.ι (F ⋙ nerveFunctor) j)) :
    ∃ (k : J) (f : j ⟶ k),
      p.map ((F ⋙ nerveFunctor).map f) =
        q.map ((F ⋙ nerveFunctor).map f) := by
  let G := F ⋙ nerveFunctor
  have hv : ∀ i : Fin (n + 1), (colimit.ι G j).app (op ⦋0⦌) (p.vertex i) =
      (colimit.ι G j).app (op ⦋0⦌) (q.vertex i) :=
    fun i => congrArg (fun r : (colimit G).Path n => r.vertex i) h
  have he : ∀ i : Fin n, (colimit.ι G j).app (op ⦋1⦌) (p.arrow i) =
      (colimit.ι G j).app (op ⦋1⦌) (q.arrow i) :=
    fun i => congrArg (fun r : (colimit G).Path n => r.arrow i) h
  obtain ⟨j₀, u₀, hv₀⟩ := nerveColimit_simplex_family_eq_eventually F (op ⦋0⦌) j
    p.vertex q.vertex hv
  obtain ⟨j₁, u₁, he₁⟩ := nerveColimit_simplex_family_eq_eventually F (op ⦋1⦌) j
    p.arrow q.arrow he
  obtain ⟨l, a, b, -⟩ := IsFilteredOrEmpty.cocone_objs j₀ j₁
  let g₀ := u₀ ≫ a
  let g₁ := u₁ ≫ b
  let t := IsFiltered.coeqHom g₀ g₁
  have hcomp : g₁ ≫ t = g₀ ≫ t := (IsFiltered.coeq_condition g₀ g₁).symm
  have hc : ∀ {a b c : J} (u : a ⟶ b) (t : b ⟶ c) {m : SimplexCategoryᵒᵖ}
      {x y : (G.obj a).obj m}, (G.map u).app m x = (G.map u).app m y →
        (G.map (u ≫ t)).app m x = (G.map (u ≫ t)).app m y := by
    intro a b c u t m x y h
    rw [Functor.map_comp]
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
    exact congrArg ((G.map t).app m) h
  refine ⟨IsFiltered.coeq g₀ g₁, g₀ ≫ t, ?_⟩
  apply SSet.Path.ext
  · funext i
    simp only [SSet.Path.map_vertex]
    exact hc g₀ t (hc u₀ a (hv₀ i))
  · funext i
    simp only [SSet.Path.map_arrow]
    rw [← hcomp]
    exact hc g₁ t (hc u₁ b (he₁ i))

omit [UnivLE.{v, w}] [UnivLE.{wJ, w}] in
private lemma nerveColimit_spine_natural {X Y : SSet}
    (g : X ⟶ Y) (n : ℕ) (x : X.obj (op ⦋n⦌)) :
    Y.spine n (g.app (op ⦋n⦌) x) = (X.spine n x).map g := by
  let kₙ : SimplexCategoryᵒᵖ := op ⦋n⦌
  let k₀ : SimplexCategoryᵒᵖ := op ⦋0⦌
  let k₁ : SimplexCategoryᵒᵖ := op ⦋1⦌
  apply SSet.Path.ext
  · funext i
    simp only [SSet.Path.map_vertex]
    let d : kₙ ⟶ k₀ :=
      (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) i).op
    change Y.map d (g.app (op ⦋n⦌) x) =
      g.app k₀ (X.map d x)
    exact (NatTrans.naturality_apply g d x).symm
  · funext i
    simp only [SSet.Path.map_arrow]
    let d : kₙ ⟶ k₁ :=
      (SimplexCategory.mkOfSucc i).op
    change Y.map d (g.app (op ⦋n⦌) x) =
      g.app k₁ (X.map d x)
    exact (NatTrans.naturality_apply g d x).symm

omit [UnivLE.{wJ, w}] in
private lemma nerveColimit_spine_bijective (n : ℕ) :
    Function.Bijective ((colimit (F ⋙ nerveFunctor)).spine n) := by
  let G := F ⋙ nerveFunctor
  have hι : ∀ {a b : J} (u : a ⟶ b) (m : SimplexCategoryᵒᵖ) (z : (G.obj a).obj m),
      (colimit.ι G b).app m ((G.map u).app m z) = (colimit.ι G a).app m z :=
    fun u m z => ConcreteCategory.congr_hom (NatTrans.congr_app (colimit.w G u) m) z
  let kₙ : SimplexCategoryᵒᵖ := op ⦋n⦌
  constructor
  · intro x y h
    obtain ⟨j₀, x₀, hx₀⟩ := nerveColimit_simplex_stage F kₙ x
    obtain ⟨j₁, y₀, hy₀⟩ := nerveColimit_simplex_stage F kₙ y
    let l := IsFiltered.max j₀ j₁
    let u := IsFiltered.leftToMax j₀ j₁
    let v := IsFiltered.rightToMax j₀ j₁
    let x₁ := ((G.map u).app kₙ) x₀
    let y₁ := ((G.map v).app kₙ) y₀
    have hx : (colimit.ι G l).app kₙ x₁ = x := (hι u kₙ x₀).trans hx₀
    have hy : (colimit.ι G l).app kₙ y₁ = y := (hι v kₙ y₀).trans hy₀
    have hsp :
        ((G.obj l).spine n x₁).map (colimit.ι G l) =
          ((G.obj l).spine n y₁).map ((colimit.ι G l)) := by
      calc
        _ = (colimit G).spine n ((colimit.ι G l).app kₙ x₁) :=
          (nerveColimit_spine_natural (colimit.ι G l) n x₁).symm
        _ = (colimit G).spine n ((colimit.ι G l).app kₙ y₁) := by
          rw [hx, hy]
          exact h
        _ = _ := nerveColimit_spine_natural (colimit.ι G l) n y₁
    obtain ⟨k, f, hf⟩ := nerveColimit_path_eq_eventually F l
      ((G.obj l).spine n x₁) ((G.obj l).spine n y₁) hsp
    have hstage : ((G.obj k).spine n (((G.map f).app kₙ) x₁)) =
        ((G.obj k).spine n (((G.map f).app kₙ) y₁)) := by
      rw [nerveColimit_spine_natural (G.map f) n x₁,
        nerveColimit_spine_natural (G.map f) n y₁]
      exact hf
    have hxy : ((G.map f).app kₙ) x₁ = ((G.map f).app kₙ) y₁ :=
      (Nerve.strictSegal (F.obj k)).spineInjective hstage
    exact ((hι f kₙ x₁).trans hx).symm.trans
      ((congrArg ((colimit.ι G k).app kₙ) hxy).trans
        ((hι f kₙ y₁).trans hy))
  · intro p
    obtain ⟨j, q, hv, he⟩ := nerveColimit_path_stage F p
    obtain ⟨z, hz⟩ := ((Nerve.strictSegal (F.obj j)).spineEquiv n).surjective q
    change (nerveFunctor.obj (F.obj j)).obj kₙ at z
    change (nerveFunctor.obj (F.obj j)).spine n z = q at hz
    refine ⟨(colimit.ι G j).app kₙ z, ?_⟩
    rw [nerveColimit_spine_natural (colimit.ι G j) n z]
    apply SSet.Path.ext
    · funext i
      simp only [SSet.Path.map_vertex]
      exact (congrArg ((colimit.ι G j).app (op ⦋0⦌))
        (congrArg (fun r : (G.obj j).Path n => r.vertex i) hz)).trans (hv i)
    · funext i
      simp only [SSet.Path.map_arrow]
      exact (congrArg ((colimit.ι G j).app (op ⦋1⦌))
        (congrArg (fun r : (G.obj j).Path n => r.arrow i) hz)).trans (he i)

omit [UnivLE.{wJ, w}] in
private lemma nerveColimit_isStrictSegal :
    (colimit (F ⋙ nerveFunctor)).IsStrictSegal :=
  ⟨fun n => nerveColimit_spine_bijective F n⟩

open SimplexCategory.Truncated SimplicialObject.Truncated

omit [UnivLE.{v, w}] [UnivLE.{wJ, w}] in
private lemma strictSegal_comp_unique {V : SSet.Truncated 2} [V.IsStrictSegal]
    {x y z : V.obj (op ⦋0⦌₂)} {a : SSet.Truncated.Edge x y}
    {b : SSet.Truncated.Edge y z} {c d : SSet.Truncated.Edge x z}
    (s : a.CompStruct b c) (t : a.CompStruct b d) : c = d := by
  apply SSet.Truncated.Edge.ext
  have h : s.simplex = t.simplex := by
    apply SSet.Truncated.IsStrictSegal.ext
    intro i
    fin_cases i
    · have h₀ : SimplexCategory.mkOfSucc (0 : Fin 2) = SimplexCategory.δ 2 := by decide
      change V.map (Hom.tr (SimplexCategory.mkOfSucc (0 : Fin 2))).op s.simplex =
        V.map (Hom.tr (SimplexCategory.mkOfSucc (0 : Fin 2))).op t.simplex
      rw [h₀]
      exact s.d₂.trans t.d₂.symm
    · have h₁ : SimplexCategory.mkOfSucc (1 : Fin 2) = SimplexCategory.δ 0 := by decide
      change V.map (Hom.tr (SimplexCategory.mkOfSucc (1 : Fin 2))).op s.simplex =
        V.map (Hom.tr (SimplexCategory.mkOfSucc (1 : Fin 2))).op t.simplex
      rw [h₁]
      exact s.d₀.trans t.d₀.symm
  exact s.d₁.symm.trans ((congrArg (V.map (SimplexCategory.Truncated.δ₂ 1).op) h).trans t.d₁)

private noncomputable def homotopyCategoryToEdgeClasses (V : SSet.Truncated 2)
    [V.Quasicategory₂] : V.HomotopyCategory ⥤ V.HomotopyCategory₂ :=
  SSet.Truncated.HomotopyCategory.lift (fun x => ⟨x⟩)
    (fun e => SSet.Truncated.HomotopyCategory₂.homMk e)
    (fun x => SSet.Truncated.HomotopyCategory₂.homMk_id ⟨x⟩)
    (fun s => s.homotopyCategory₂_fac)

omit [UnivLE.{v, w}] [UnivLE.{wJ, w}] in
private lemma strictSegal_homMk_injective (V : SSet.Truncated 2)
    [V.Quasicategory₂] [V.IsStrictSegal] {x y : V.obj (op ⦋0⦌₂)} :
    Function.Injective (SSet.Truncated.HomotopyCategory.homMk (x₀ := x) (x₁ := y)) := by
  intro e f h
  have h' := congrArg (homotopyCategoryToEdgeClasses V).map h
  simp only [homotopyCategoryToEdgeClasses,
    SSet.Truncated.HomotopyCategory.lift_map_homMk] at h'
  have ht : SSet.Truncated.HomotopicL e f := Quotient.exact h'
  exact strictSegal_comp_unique (SSet.Truncated.Edge.CompStruct.compId e) ht.some

omit [UnivLE.{v, w}] [UnivLE.{wJ, w}] in
private lemma quasicategory_homMk_surjective (V : SSet.Truncated 2)
    [V.Quasicategory₂] {x y : V.obj (op ⦋0⦌₂)} :
    Function.Surjective (SSet.Truncated.HomotopyCategory.homMk (x₀ := x) (x₁ := y)) := by
  intro f
  have h : ∀ {a b : V.HomotopyCategory} (g : a ⟶ b),
      ∃ e : SSet.Truncated.Edge a.as.as b.as.as,
        SSet.Truncated.HomotopyCategory.homMk e = g := by
    apply SSet.Truncated.HomotopyCategory.hom_rec
    · exact fun e => ⟨e, rfl⟩
    · intro a b c g h hg hh
      obtain ⟨e, rfl⟩ := hg
      obtain ⟨f, rfl⟩ := hh
      obtain ⟨d, s⟩ := (SSet.Truncated.Quasicategory₂.fill21 e f).some
      exact ⟨d, (SSet.Truncated.HomotopyCategory.homMk_comp_homMk s).symm⟩
  exact h f

omit [UnivLE.{v, w}] [UnivLE.{wJ, w}] in
private lemma pathMap_bijective {n : ℕ} {V W : SSet.Truncated (n + 1)}
    (f : V ⟶ W)
    (h₀ : Function.Bijective (f.app (op ⦋0⦌ₙ₊₁)))
    (h₁ : Function.Bijective (f.app (op ⦋1⦌ₙ₊₁))) (m : ℕ) :
    Function.Bijective (fun p : V.Path m => p.map f) := by
  constructor
  · intro p q h
    apply SSet.Truncated.Path.ext <;> funext i
    exacts [h₀.injective (congrArg (fun r : W.Path m => r.vertex i) h),
      h₁.injective (congrArg (fun r : W.Path m => r.arrow i) h)]
  · intro p
    choose v hv using fun i => h₀.surjective (p.vertex i)
    choose e he using fun i => h₁.surjective (p.arrow i)
    refine ⟨⟨v, e, ?_, ?_⟩, ?_⟩
    · intro i
      apply h₀.injective
      change f.app _ (V.map (Hom.tr (SimplexCategory.δ 1)).op (e i)) =
        f.app _ (v i.castSucc)
      rw [NatTrans.naturality_apply, he, hv]
      exact p.arrow_src i
    · intro i
      apply h₀.injective
      change f.app _ (V.map (Hom.tr (SimplexCategory.δ 0)).op (e i)) =
        f.app _ (v i.succ)
      rw [NatTrans.naturality_apply, he, hv]
      exact p.arrow_tgt i
    · apply SSet.Truncated.Path.ext <;> funext i
      exacts [hv i, he i]

omit [UnivLE.{v, w}] [UnivLE.{wJ, w}] in
private lemma strictSegal_isIso {n : ℕ} {V W : SSet.Truncated (n + 1)}
    [V.IsStrictSegal] [W.IsStrictSegal] (f : V ⟶ W)
    (h₀ : Function.Bijective (f.app (op ⦋0⦌ₙ₊₁)))
    (h₁ : Function.Bijective (f.app (op ⦋1⦌ₙ₊₁))) : IsIso f := by
  have : ∀ k, IsIso (f.app k) := by
    rintro ⟨⟨⟨m⟩, hm⟩⟩
    refine (CategoryTheory.isIso_iff_bijective _).mpr ?_
    have hn : (fun p : V.Path m => p.map f) ∘ (V.spine m hm) =
        (W.spine m hm) ∘ f.app (op ⦋m,hm⦌ₙ₊₁) := by
      funext s
      apply SSet.Truncated.Path.ext <;> funext i <;> exact NatTrans.naturality_apply f _ s
    have hh := (pathMap_bijective f h₀ h₁ m).comp (V.spine_bijective m hm)
    rw [hn] at hh
    refine ⟨fun x y hxy => hh.injective (congrArg (W.spine m hm) hxy), fun y => ?_⟩
    obtain ⟨x, hx⟩ := hh.surjective (W.spine m hm y)
    exact ⟨x, (W.spine_bijective m hm).injective hx⟩
  exact NatIso.isIso_of_isIso_app f

omit [UnivLE.{v, w}] [UnivLE.{wJ, w}] in
private lemma strictSegal_unit_one_bijective (V : SSet.Truncated 2)
    [V.Quasicategory₂] [V.IsStrictSegal] :
    Function.Bijective ((SSet.Truncated.HomotopyCategory.homToNerveMk
      (𝟭 V.HomotopyCategory)).app (op ⦋1⦌₂)) := by
  constructor
  · intro s t h
    obtain ⟨x, y, e, rfl⟩ := SSet.Truncated.Edge.exists_of_simplex s
    obtain ⟨x', y', e', rfl⟩ := SSet.Truncated.Edge.exists_of_simplex t
    simp only [SSet.Truncated.HomotopyCategory.homToNerveMk_app_edge,
      Functor.id_map] at h
    have hx : x = x' := congrArg (fun r : ComposableArrows V.HomotopyCategory 1 =>
      r.left.as.as) h
    have hy : y = y' := congrArg (fun r : ComposableArrows V.HomotopyCategory 1 =>
      r.right.as.as) h
    subst x' y'
    have hh : SSet.Truncated.HomotopyCategory.homMk e =
        SSet.Truncated.HomotopyCategory.homMk e' :=
      (Arrow.mk_inj _ _).mp (congrArg ComposableArrows.arrowEquiv h)
    exact congrArg SSet.Truncated.Edge.edge (strictSegal_homMk_injective V hh)
  · intro s
    obtain ⟨x, y, f, rfl⟩ := ComposableArrows.mk₁_surjective s
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective x
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective y
    obtain ⟨e, rfl⟩ := quasicategory_homMk_surjective V f
    refine ⟨e.edge, ?_⟩
    simp only [SSet.Truncated.HomotopyCategory.homToNerveMk_app_edge, Functor.id_map]
    rfl

omit [UnivLE.{v, w}] [UnivLE.{wJ, w}] in
private lemma strictSegal_unit_isIso (V : SSet.Truncated 2)
    [V.Quasicategory₂] [V.IsStrictSegal] :
    IsIso (SSet.Truncated.nerve₂Adj.unit.app V) := by
  change IsIso (SSet.Truncated.HomotopyCategory.homToNerveMk (𝟭 V.HomotopyCategory))
  apply strictSegal_isIso
  · constructor
    · intro x y h
      exact congrArg (fun x : V.HomotopyCategory => x.as.as) (nerveEquiv.symm.injective h)
    · intro x
      obtain ⟨y, hy⟩ := SSet.Truncated.HomotopyCategory.mk_surjective (nerveEquiv x)
      refine ⟨y, ?_⟩
      change nerveEquiv.symm (SSet.Truncated.HomotopyCategory.mk y) = x
      rw [hy]
      exact nerveEquiv.symm_apply_apply x
  · exact strictSegal_unit_one_bijective V

omit [UnivLE.{v, w}] [UnivLE.{wJ, w}] in
private theorem isColimit_map_of_unit_iso
    {A : Type*} {D : Type*} [Category A] [Category D]
    {L : A ⥤ D} {R : D ⥤ A} (adj : L ⊣ R) [R.Full] [R.Faithful]
    {K : Type*} [Category K] (G : K ⥤ D)
    (c : Cocone (G ⋙ R)) (hc : IsColimit c) [IsIso (adj.unit.app c.pt)] :
    ∃ (d : Cocone G), Nonempty (IsColimit d) ∧ Nonempty (IsColimit (R.mapCocone d)) := by
  let := adj.leftAdjoint_preservesColimits
  let β : (G ⋙ R) ⋙ L ≅ G :=
    Functor.associator G R L ≪≫
      Functor.isoWhiskerLeft G (asIso adj.counit) ≪≫ Functor.rightUnitor G
  let d := (Cocone.precompose β.symm.hom).obj (L.mapCocone c)
  have hd : IsColimit d :=
    (IsColimit.precomposeHomEquiv β.symm _).symm (isColimitOfPreserves L hc)
  refine ⟨d, ⟨hd⟩, ⟨?_⟩⟩
  refine IsColimit.ofIsoColimit hc (Cocone.ext (asIso (adj.unit.app c.pt)) ?_)
  intro j
  change c.ι.app j ≫ adj.unit.app c.pt =
    R.map (β.inv.app j ≫ L.map (c.ι.app j))
  rw [R.map_comp, show c.ι.app j ≫ adj.unit.app c.pt =
    adj.unit.app ((G ⋙ R).obj j) ≫ R.map (L.map (c.ι.app j)) from
      adj.unit.naturality (c.ι.app j)]
  congr 1
  dsimp [β]
  simp only [Category.comp_id, Category.id_comp]
  rw [NatIso.isIso_inv_app]
  apply (cancel_mono (R.map (adj.counit.app (G.obj j)))).mp
  rw [adj.right_triangle_components, ← R.map_comp]
  simp

private noncomputable def filteredNerveIsColimit :
    IsColimit (Nerve.nerveFunctor₂.mapCocone (colimit.cocone F)) := by
  let := (SSet.coskAdj 2).leftAdjoint_preservesColimits
  let V := colimit (F ⋙ nerveFunctor)
  let : V.IsStrictSegal := nerveColimit_isStrictSegal F
  let c : Cocone (F ⋙ Nerve.nerveFunctor₂) :=
    (SSet.truncation 2).mapCocone (colimit.cocone (F ⋙ nerveFunctor))
  let hc : IsColimit c :=
    isColimitOfPreserves (SSet.truncation 2) (colimit.isColimit (F ⋙ nerveFunctor))
  let : IsIso (SSet.Truncated.nerve₂Adj.unit.app c.pt) :=
    strictSegal_unit_isIso ((SSet.truncation 2).obj V)
  let h := isColimit_map_of_unit_iso SSet.Truncated.nerve₂Adj F c hc
  let d := h.choose
  let hd := h.choose_spec.1.some
  let hd' := h.choose_spec.2.some
  refine IsColimit.ofIsoColimit hd' (Cocone.ext
    (Nerve.nerveFunctor₂.mapIso (hd.coconePointUniqueUpToIso (colimit.isColimit F))) ?_)
  intro j
  change Nerve.nerveFunctor₂.map (d.ι.app j) ≫
    Nerve.nerveFunctor₂.map ((hd.coconePointUniqueUpToIso (colimit.isColimit F)).hom) = _
  rw [← Functor.map_comp, hd.comp_coconePointUniqueUpToIso_hom]
  rfl

private noncomputable def filteredCatSimplexIsColimit
    (k : (SimplexCategory.Truncated 2)ᵒᵖ) :
    IsColimit (((evaluation _ (Type w)).obj k).mapCocone
      (Nerve.nerveFunctor₂.mapCocone (colimit.cocone F))) :=
  isColimitOfPreserves ((evaluation _ (Type w)).obj k) (filteredNerveIsColimit F)

/-- Equality of two stage morphisms in a filtered categorical colimit is
witnessed after a transition in the diagram. -/
private lemma filteredCat_hom_eq_eventually (j : J) {x y : F.obj j}
    (f g : x ⟶ y)
    (h : (colimit.ι F j).toFunctor.map f = (colimit.ι F j).toFunctor.map g) :
    ∃ (k : J) (u : j ⟶ k), (F.map u).toFunctor.map f = (F.map u).toFunctor.map g := by
  have hh : (Nerve.nerveFunctor₂.map (colimit.ι F j)).app (op ⦋1⦌₂)
      (ComposableArrows.mk₁ f) =
    (Nerve.nerveFunctor₂.map (colimit.ι F j)).app (op ⦋1⦌₂)
      (ComposableArrows.mk₁ g) := by
    apply ComposableArrows.arrowEquiv.injective
    change Arrow.mk ((colimit.ι F j).toFunctor.map f) =
      Arrow.mk ((colimit.ι F j).toFunctor.map g)
    rw [h]
  obtain ⟨k, u, hu⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (filteredCatSimplexIsColimit F (op ⦋1⦌₂))
      (ComposableArrows.mk₁ f) (ComposableArrows.mk₁ g)).mp hh
  exact ⟨k, u, (Arrow.mk_inj _ _).mp (congrArg ComposableArrows.arrowEquiv hu)⟩

/-- **Morphisms of a filtered colimit in `Cat` are identified only at a later stage.** Two
parallel morphisms of one stage of a filtered diagram of categories whose images in the colimit
agree already agree after some transition of the diagram. -/
alias exists_common_stage_eq_of_colimit_ι_map_eq := filteredCat_hom_eq_eventually

end ColimitBridge

end CategoryTheory.Cat

end
