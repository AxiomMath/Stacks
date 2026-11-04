module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasiIsoOfLocalSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleSubcomplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit

/-!
# The subcomplex locally spanned by sections over a dense family of objects

Let `K` be a cochain complex of sheaves of modules on a site `(C, J)`, and let `c : ι → C` be a
family of objects which is dense: every object is covered by arrows from the `c i`.  A set `G`
of *generators* — sections of the terms of `K` over the objects `c i` — spans, in each degree,
the sub-presheaf of modules of the restrictions of the generators along all arrows, and its
local closure is a submodule of the sheaf.  When `G` is stable under the differential these
submodules form a subcomplex of `K`.

This file builds that subcomplex and proves the two facts about it that bound the size of a
complex up to quasi-isomorphism:

* the inclusion is a quasi-isomorphism as soon as every cycle over a `c i` is locally homologous
  to a cycle of the subcomplex, and every cycle in the span over a `c i` which is a boundary in
  `K` is the boundary of a section of the subcomplex;
* a section of the subcomplex over a `c i` is determined by its restrictions, along the arrows
  from the family, which lie in the span.

## Main definitions

* `Stacks.SheafOfModules.DenseSpan.span`: the span of the restrictions of the generators.
* `Stacks.SheafOfModules.DenseSpan.closure`: its local closure, a submodule of the sheaf.
* `Stacks.SheafOfModules.DenseSpan.IsDClosed`: stability of the generators under the
  differential.
* `Stacks.SheafOfModules.DenseSpan.subcomplex` and `Stacks.SheafOfModules.DenseSpan.ι`: the
  subcomplex and its inclusion into `K`.

## Main results

* `Stacks.SheafOfModules.DenseSpan.exists_mem_sieve_of_dense`: a condition stable under
  restriction which holds locally above every arrow from the family in a covering sieve holds
  on a covering sieve.
* `Stacks.SheafOfModules.DenseSpan.quasiIso_ι`: the quasi-isomorphism criterion.
* `Stacks.SheafOfModules.DenseSpan.injective_restrictSpan`: the sections of the subcomplex over
  an object of the family inject into the families of optional sections of the span indexed by
  the arrows from the family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w t v u u'

namespace Stacks.SheafOfModules.DenseSpan

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {ι : Type w} (c : ι → C) (K : CochainComplex (_root_.SheafOfModules.{t} R) ℤ)

/-- The generators: a set of sections of the terms of `K` over the objects of the family. -/
abbrev Gens := Set (Σ n : ℤ, Σ i : ι, (K.X n).val.obj (op (c i)))

variable {c K} (G : Gens c K)

/-- The restrictions of the generators of degree `n` to `V` along all arrows `V ⟶ c i`. -/
def genSet (n : ℤ) (V : Cᵒᵖ) : Set ((K.X n).val.obj V) :=
  {x | ∃ (i : ι) (s : (K.X n).val.obj (op (c i))) (f : V.unop ⟶ c i),
    ⟨n, i, s⟩ ∈ G ∧ (K.X n).val.map f.op s = x}

/-- **The span of the generators**: the sub-presheaf of modules of the degree-`n` term of `K`
spanned by the restrictions of the generators of degree `n` along all arrows. -/
def span (n : ℤ) : (K.X n).val.Submodule where
  obj V := Submodule.span (R.obj.obj V) (genSet G n V)
  map {V V'} g := by
    rw [Submodule.span_le]
    rintro x ⟨i, s, f, hs, rfl⟩
    refine Submodule.subset_span ⟨i, s, g.unop ≫ f, hs, ?_⟩
    change (K.X n).val.map (g.unop ≫ f).op s = (K.X n).val.map g ((K.X n).val.map f.op s)
    exact PresheafOfModules.map_comp_apply (K.X n).val f.op g s

/-- **The local closure of the span**, a submodule of the degree-`n` term of `K`. -/
def closure (n : ℤ) : (K.X n).Submodule :=
  Stacks.SheafOfModules.localClosure (K.X n) (span G n)

/-- The generators are stable under the differentials. -/
def IsDClosed : Prop :=
  ∀ (m n : ℤ) (i : ι) (s : (K.X m).val.obj (op (c i))), ⟨m, i, s⟩ ∈ G →
    (⟨n, i, (K.d m n).val.app (op (c i)) s⟩ : Σ n : ℤ, Σ i : ι, (K.X n).val.obj (op (c i))) ∈ G

/-- A section of the span stays in the span after restriction. -/
theorem map_mem_span {n : ℤ} {V V' : Cᵒᵖ} (g : V ⟶ V') {x : (K.X n).val.obj V}
    (hx : x ∈ (span G n).obj V) : (K.X n).val.map g x ∈ (span G n).obj V' :=
  (span G n).map g hx

/-- The span is contained in its local closure. -/
theorem mem_closure_of_mem_span {n : ℤ} {V : Cᵒᵖ} {x : (K.X n).val.obj V}
    (hx : x ∈ (span G n).obj V) : x ∈ (closure G n).obj V :=
  J.superset_covering (fun _ f _ => map_mem_span G f.op hx) (J.top_mem V.unop)

/-- A generator is a section of the local closure. -/
theorem mem_closure_of_mem {n : ℤ} {i : ι} {s : (K.X n).val.obj (op (c i))}
    (hs : ⟨n, i, s⟩ ∈ G) : s ∈ (closure G n).obj (op (c i)) := by
  refine mem_closure_of_mem_span G (Submodule.subset_span ⟨i, s, 𝟙 _, hs, ?_⟩)
  show (K.X n).val.map (𝟙 (op (c i))) s = s
  rw [(K.X n).val.map_id]
  rfl

variable {G}

/-- The differential of a restriction is the restriction of the differential. -/
private theorem d_map_eq_of_d_eq {m n : ℤ} {V V' : Cᵒᵖ} (g : V ⟶ V') {x : (K.X m).val.obj V}
    {y : (K.X n).val.obj V} (h : (K.d m n).val.app V x = y) :
    (K.d m n).val.app V' ((K.X m).val.map g x) = (K.X n).val.map g y :=
  (PresheafOfModules.naturality_apply (K.d m n).val g x).trans (congrArg _ h)

/-- The differential carries the span into the span, for generators stable under the
differential. -/
theorem d_mem_span (hG : IsDClosed G) (m n : ℤ) (V : Cᵒᵖ) (x : (K.X m).val.obj V)
    (hx : x ∈ (span G m).obj V) : (K.d m n).val.app V x ∈ (span G n).obj V := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, s, f, hs, rfl⟩ := hx
    refine Submodule.subset_span ⟨i, _, f, hG m n i s hs, ?_⟩
    exact (PresheafOfModules.naturality_apply (K.d m n).val f.op s).symm
  | zero =>
    rw [map_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [(ConcreteCategory.hom ((K.d m n).val.app V)).map_smul]
    exact Submodule.smul_mem _ a hx

/-- The differential carries the local closure into the local closure. -/
theorem d_mem_closure (hG : IsDClosed G) (m n : ℤ) (V : Cᵒᵖ) (x : (K.X m).val.obj V)
    (hx : x ∈ (closure G m).obj V) : (K.d m n).val.app V x ∈ (closure G n).obj V := by
  refine J.superset_covering (fun W f hf => ?_) hx
  show (K.X n).val.map f.op ((K.d m n).val.app V x) ∈ (span G n).obj (op W)
  rw [← PresheafOfModules.naturality_apply]
  exact d_mem_span hG m n _ _ hf

/-- **The subcomplex of `K` locally spanned by the generators.** -/
def subcomplex (hG : IsDClosed G) : CochainComplex (_root_.SheafOfModules.{t} R) ℤ :=
  _root_.SheafOfModules.Submodule.subcomplex (closure G)
    (fun m n V x hx => d_mem_closure hG m n V x hx)

/-- The inclusion of the subcomplex locally spanned by the generators. -/
def incl (hG : IsDClosed G) : subcomplex hG ⟶ K :=
  _root_.SheafOfModules.Submodule.subcomplexι (closure G)
    (fun m n V x hx => d_mem_closure hG m n V x hx)

/-- A section of a term of the subcomplex, as a section of the corresponding term of `K`. -/
abbrev val (hG : IsDClosed G) {n : ℤ} {V : Cᵒᵖ} (x : ((subcomplex hG).X n).val.obj V) :
    (K.X n).val.obj V :=
  Subtype.val (show ↥((closure G n).obj V) from x)

/-- The inclusion of the subcomplex sends a section to its underlying section of `K`. -/
theorem incl_f_val_app_apply (hG : IsDClosed G) (n : ℤ) (V : Cᵒᵖ)
    (x : ((subcomplex hG).X n).val.obj V) :
    ((incl hG).f n).val.app V x = val hG x := rfl

/-- The underlying section of the differential of a section of the subcomplex is the
differential of its underlying section. -/
theorem val_d (hG : IsDClosed G) (m n : ℤ) (V : Cᵒᵖ) (x : ((subcomplex hG).X m).val.obj V) :
    val hG (((subcomplex hG).d m n).val.app V x) = (K.d m n).val.app V (val hG x) := rfl

/-- Taking underlying sections commutes with restriction. -/
theorem val_map (hG : IsDClosed G) (n : ℤ) {V V' : Cᵒᵖ} (g : V ⟶ V')
    (x : ((subcomplex hG).X n).val.obj V) :
    val hG (((subcomplex hG).X n).val.map g x) = (K.X n).val.map g (val hG x) := rfl

/-- A section of the subcomplex is determined by its underlying section of `K`. -/
theorem val_injective (hG : IsDClosed G) (n : ℤ) (V : Cᵒᵖ) :
    Function.Injective (val hG (n := n) (V := V)) :=
  fun _ _ h => Subtype.ext h

/-- The underlying section of a section of the subcomplex lies in the local closure. -/
theorem val_mem (hG : IsDClosed G) {n : ℤ} {V : Cᵒᵖ} (x : ((subcomplex hG).X n).val.obj V) :
    val hG x ∈ (closure G n).obj V :=
  (show ↥((closure G n).obj V) from x).2

/-- A section of the local closure as a section of the subcomplex. -/
abbrev mk (hG : IsDClosed G) {n : ℤ} {V : Cᵒᵖ} (x : (K.X n).val.obj V)
    (hx : x ∈ (closure G n).obj V) : ((subcomplex hG).X n).val.obj V :=
  (⟨x, hx⟩ : ↥((closure G n).obj V))

/-- The underlying section of `mk hG x hx` is `x`. -/
theorem val_mk (hG : IsDClosed G) {n : ℤ} {V : Cᵒᵖ} (x : (K.X n).val.obj V)
    (hx : x ∈ (closure G n).obj V) : val hG (mk hG x hx) = x := rfl

section Dense

variable [hc : (inducedFunctor c).IsCoverDense J]

include hc in
/-- **Density turns local conditions over the family into local conditions.**  If above every
arrow `c i ⟶ V` of a covering sieve `T` a condition on arrows into `V` holds after composing
with the arrows of a covering sieve of `c i`, then it holds on a covering sieve of `V`. -/
theorem exists_mem_sieve_of_dense {V : C} {P : ∀ ⦃W : C⦄, (W ⟶ V) → Prop} (T : Sieve V)
    (hT : T ∈ J V)
    (h : ∀ (i : ι) (a : c i ⟶ V), T a → ∃ S : Sieve (c i), S ∈ J (c i) ∧
      ∀ ⦃W : C⦄ (b : W ⟶ c i), S b → P (b ≫ a)) :
    ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃W : C⦄ (b : W ⟶ V), S b → P b := by
  refine _root_.SheafOfModules.exists_mem_sieve_of_bind T hT (fun W b hb => ?_)
  refine _root_.SheafOfModules.exists_mem_sieve_of_bind (Sieve.coverByImage (inducedFunctor c) W)
    (Functor.IsCoverDense.is_cover W) (fun W' b' hb' => ?_)
  obtain ⟨⟨i, lift, map, fac⟩⟩ := hb'
  obtain ⟨S, hS, hP⟩ := h i (map ≫ b) (T.downward_closed hb map)
  refine ⟨S.pullback lift, J.pullback_stable lift hS, fun W'' b'' hb'' => ?_⟩
  have := hP (b'' ≫ lift) hb''
  rwa [Category.assoc, ← Category.assoc lift, fac, ← Category.assoc] at this

omit hc in
/-- Two sections of a sheaf of modules which agree after restriction along the arrows of a
covering sieve are equal. -/
theorem eq_of_forall_mem_sieve (M : _root_.SheafOfModules.{t} R) {V : C} (x y : M.val.obj (op V))
    (S : Sieve V) (hS : S ∈ J V)
    (h : ∀ ⦃W : C⦄ (b : W ⟶ V), S b → M.val.map b.op x = M.val.map b.op y) : x = y :=
  ((Stacks.SheafOfModules.isSheaf_forgetPresheaf M).isSeparated S hS).ext h

open Classical in
/-- The restrictions of a section along the arrows from the family, recorded where they lie in
the span. -/
def restrictSpan (n : ℤ) (i : ι) (x : (closure G n).obj (op (c i))) :
    ∀ a : (Σ j : ι, c j ⟶ c i), Option ((span G n).obj (op (c a.1))) :=
  fun a => if h : (K.X n).val.map a.2.op x.1 ∈ (span G n).obj (op (c a.1)) then
    some ⟨_, h⟩ else none

include hc in
/-- **A section of the local closure over an object of the family is determined by its
restrictions along the arrows from the family which lie in the span.** -/
theorem injective_restrictSpan (n : ℤ) (i : ι) :
    Function.Injective (restrictSpan (G := G) n i) := by
  intro x y hxy
  apply Subtype.ext
  obtain ⟨S, hS, hP⟩ := exists_mem_sieve_of_dense (c := c)
    (P := fun W b => (K.X n).val.map b.op x.1 = (K.X n).val.map b.op y.1) _ x.2
    (fun j a ha => ⟨⊤, J.top_mem _, fun W b _ => by
      have hj := congrFun hxy ⟨j, a⟩
      have ha' : (K.X n).val.map a.op x.1 ∈ (span G n).obj (op (c j)) := ha
      simp only [restrictSpan, dif_pos ha'] at hj
      split_ifs at hj with hy
      · simp only [Option.some.injEq] at hj
        rw [op_comp, PresheafOfModules.map_comp_apply, PresheafOfModules.map_comp_apply]
        exact congrArg (fun z => (K.X n).val.map b.op z) (congrArg Subtype.val hj)⟩)
  exact eq_of_forall_mem_sieve (K.X n) _ _ S hS hP

variable [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

include hc in
/-- **The inclusion of the locally spanned subcomplex is a quasi-isomorphism** as soon as
(1) every cycle of `K` over an object of the family is locally homologous to a cycle lying in the
local closure, and (2) every section of the span over an object of the family which is a
boundary in `K` is the boundary of a section of the local closure. -/
theorem quasiIso_incl (hG : IsDClosed G)
    (hAP : ∀ (j n k : ℤ), j + 1 = n → n + 1 = k → ∀ (i : ι) (z : (K.X n).val.obj (op (c i))),
      (K.d n k).val.app (op (c i)) z = 0 → ∃ S : Sieve (c i), S ∈ J (c i) ∧
        ∀ ⦃W : C⦄ (b : W ⟶ c i), S b →
          ∃ p : (K.X n).val.obj (op W), p ∈ (closure G n).obj (op W) ∧
            (K.d n k).val.app (op W) p = 0 ∧
            ∃ y : (K.X j).val.obj (op W), (K.X n).val.map b.op z = p + (K.d j n).val.app (op W) y)
    (hW : ∀ (j n : ℤ), j + 1 = n → ∀ (i : ι) (s : (K.X n).val.obj (op (c i))),
      s ∈ (span G n).obj (op (c i)) → (∃ t, (K.d j n).val.app (op (c i)) t = s) →
        ∃ t, t ∈ (closure G j).obj (op (c i)) ∧ (K.d j n).val.app (op (c i)) t = s) :
    QuasiIso (incl hG) := by
  refine _root_.SheafOfModules.quasiIso_of_forall_exists_mem_sieve (incl hG) ?_ ?_
  · intro j n k hj hk V z hz
    refine exists_mem_sieve_of_dense (c := c) ⊤ (J.top_mem V) (fun i a _ => ?_)
    have hz' : (K.d n k).val.app (op (c i)) ((K.X n).val.map a.op z) = 0 :=
      (d_map_eq_of_d_eq a.op hz).trans (map_zero _)
    obtain ⟨S, hS, hloc⟩ := hAP j n k hj hk i _ hz'
    refine ⟨S, hS, fun W b hb => ?_⟩
    obtain ⟨p, hp, hdp, y, hy⟩ := hloc b hb
    refine ⟨mk hG p hp, val_injective hG k _ hdp, y, ?_⟩
    rw [op_comp, PresheafOfModules.map_comp_apply, hy]
    rfl
  · intro j n k hj hk V z' hz' y hy
    refine exists_mem_sieve_of_dense (c := c) _ (val_mem hG z') (fun i a ha => ?_)
    obtain ⟨t, ht, hdt⟩ := hW j n hj i _ ha ⟨(K.X j).val.map a.op y, d_map_eq_of_d_eq a.op hy.symm⟩
    refine ⟨⊤, J.top_mem _, fun W b _ => ⟨mk hG ((K.X j).val.map b.op t)
      (((closure G j).map b.op) ht), ?_⟩⟩
    rw [op_comp, PresheafOfModules.map_comp_apply]
    apply val_injective hG n
    show (K.X n).val.map b.op ((K.X n).val.map a.op (val hG z')) =
      (K.d j n).val.app (op W) ((K.X j).val.map b.op t)
    exact (d_map_eq_of_d_eq b.op hdt).symm

end Dense

end Stacks.SheafOfModules.DenseSpan
