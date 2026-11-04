module

public import StacksFrontier.CategoryTheory.Sites.Sheafification.CechH0
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections commute with colimits along ordinals of large cofinality

Stacks tag 0GS0.  A site is taken in the Stacks sense (tag 00VH): covering families
`{U_i ⟶ X}_{i ∈ I}` carrying explicit index sets, closed under isomorphisms, composition and
base change, with the fibre products `U_i ×_X V` provided by the base-change axiom rather than
by assuming all pullbacks exist.  Let `F : β.ToType ⥤ Sh(C)` be a system of sheaves of sets
indexed by an ordinal `β` whose cofinality exceeds `|I|` for every covering family of the site.
Then the colimit of `F` computed in presheaves already satisfies the Čech sheaf condition, so
the inclusion of sheaves into presheaves preserves the colimit, and for every object `U` the
canonical map `colim_α F_α(U) → (colim_α F_α)(U)` is a bijection.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u

namespace Stacks.Sites.ColimitCofinality

variable {C : Type u} [SmallCategory C]

/-! ### Covering families

A covering family `{U_i ⟶ X}` with an explicit index type is Mathlib's
`CategoryTheory.PreZeroHypercover X`, whose `I₀`, `X` and `f` are the index type, the objects
and the structure morphisms. This file previously declared its own `CoveringFamily` and
re-implemented three pieces of Mathlib's API for it; all four are gone:

* `CoveringFamily.toPresieve` was `Presieve.ofArrows` of the objects and morphisms, i.e.
  `presieve₀` — and it was never used anywhere;
* `CoveringFamily.singleton` is `PreZeroHypercover.singleton`, field for field;
* `CoveringFamily.compose` is `PreZeroHypercover.bind`, field for field and with the same
  association of the composite structure morphism.

Each of those three agreements holds by `rfl`, so nothing downstream changes meaning.

`BaseChange` below is kept rather than replaced by `pullback₂`: it *exhibits* the fibre
products together with an `IsPullback` witness, which is what lets a `Site` be given without
assuming that all pullbacks of `C` exist. `pullback₂` would require a `HasPullback` instance
for every pair and so would strengthen the axiom.
-/

/-- **Base change of a covering family (axiom (3) data).** A base change of `𝒰 = {U_i ⟶ X}`
along a morphism `g : V ⟶ X` consists of chosen fibre-product objects `U_i ×_X V` (indexed by
the same `𝒰.I₀`), the two projections, and a proof that each square is a pullback. This encodes
the existence of the fibre products `U_i ×_X V` *without* assuming all pullbacks of `C` exist. -/
structure BaseChange {X : C} (𝒰 : PreZeroHypercover.{u} X) {V : C} (g : V ⟶ X) where
  /-- The chosen fibre product `U_i ×_X V`. -/
  obj : 𝒰.I₀ → C
  /-- The projection `U_i ×_X V ⟶ U_i`. -/
  fst : (i : 𝒰.I₀) → obj i ⟶ 𝒰.X i
  /-- The projection `U_i ×_X V ⟶ V` (the structure map of the base-changed family over `V`). -/
  snd : (i : 𝒰.I₀) → obj i ⟶ V
  /-- The square `U_i ×_X V ⟶ U_i ⟶ X`, `U_i ×_X V ⟶ V ⟶ X` is a pullback. -/
  isPullback : (i : 𝒰.I₀) → IsPullback (fst i) (snd i) (𝒰.f i) g

/-- The covering family `{U_i ×_X V ⟶ V}` over `V` underlying a base change. -/
@[simps]
abbrev BaseChange.fam {X : C} {𝒰 : PreZeroHypercover.{u} X} {V : C} {g : V ⟶ X}
    (bc : BaseChange 𝒰 g) : PreZeroHypercover.{u} V where
  I₀ := 𝒰.I₀
  X := bc.obj
  f := bc.snd

/-- **Site (Stacks convention, tag 00VH).** A small category `C` with a collection `IsCov` of
covering families `{U_i ⟶ X}_{i ∈ I}` (carrying explicit index sets) satisfying the three Stacks
pretopology axioms, formalized directly:

* `isIso_mem` — every isomorphism `f : Y ⟶ X`, regarded as the singleton family `{f}`, is a
  covering (axiom (1));
* `comp_mem` — if `{U_i ⟶ X}` is a covering and each `{V_{ij} ⟶ U_i}` is a covering, then the
  composed family `{V_{ij} ⟶ X}` indexed by `Σ i, J_i` is a covering (axiom (2), transitivity);
* `baseChange` / `baseChange_mem` — for every covering `{U_i ⟶ X}` and every morphism `g : V ⟶ X`,
  a chosen base change `U_i ×_X V` (with pullback witnesses) is provided, and the base-changed
  family `{U_i ×_X V ⟶ V}` is again a covering (axiom (3), base change).

A site is given by this data; it does NOT require all pullbacks of `C` to exist. -/
@[sga "3 IV 4.2.5", sga "4 II 1.3", sga "4 VI 8.3.7" "comp_mem"]
structure Site (C : Type u) [SmallCategory C] where
  /-- The covering families of the site (with explicit index sets). -/
  IsCov : {X : C} → PreZeroHypercover.{u} X → Prop
  /-- Axiom (1): every isomorphism is a (singleton) covering. -/
  isIso_mem : ∀ {X Y : C} (f : Y ⟶ X) [IsIso f], IsCov (PreZeroHypercover.singleton.{u} f)
  /-- Axiom (2): coverings are closed under composition / transitivity. -/
  comp_mem : ∀ {X : C} (𝒰 : PreZeroHypercover.{u} X)
      (𝒱 : (i : 𝒰.I₀) → PreZeroHypercover.{u} (𝒰.X i)),
    IsCov 𝒰 → (∀ i, IsCov (𝒱 i)) → IsCov (𝒰.bind 𝒱)
  /-- Axiom (3) data: a chosen base change of every covering along every morphism. -/
  baseChange : ∀ {X : C} (𝒰 : PreZeroHypercover.{u} X), IsCov 𝒰 → ∀ {V : C} (g : V ⟶ X),
    BaseChange 𝒰 g
  /-- Axiom (3): the base-changed family is again a covering. -/
  baseChange_mem : ∀ {X : C} (𝒰 : PreZeroHypercover.{u} X) (h : IsCov 𝒰) {V : C} (g : V ⟶ X),
    IsCov (baseChange 𝒰 h g).fam

variable (𝒮 : Site C)

/-- The chosen pairwise fiber product `U_i ×_X U_j` of a covering family `𝒰` of the site, obtained
by base change of `𝒰` along `𝒰.f j : U_j ⟶ X` (axiom (3) with `V = U_j`). -/
def Site.fiberObj {X : C} {𝒰 : PreZeroHypercover.{u} X} (h : 𝒮.IsCov 𝒰) (i j : 𝒰.I₀) : C :=
  (𝒮.baseChange 𝒰 h (𝒰.f j)).obj i

/-- The projection `U_i ×_X U_j ⟶ U_i`. -/
def Site.fiberFst {X : C} {𝒰 : PreZeroHypercover.{u} X} (h : 𝒮.IsCov 𝒰) (i j : 𝒰.I₀) :
    𝒮.fiberObj h i j ⟶ 𝒰.X i :=
  (𝒮.baseChange 𝒰 h (𝒰.f j)).fst i

/-- The projection `U_i ×_X U_j ⟶ U_j`. -/
def Site.fiberSnd {X : C} {𝒰 : PreZeroHypercover.{u} X} (h : 𝒮.IsCov 𝒰) (i j : 𝒰.I₀) :
    𝒮.fiberObj h i j ⟶ 𝒰.X j :=
  (𝒮.baseChange 𝒰 h (𝒰.f j)).snd i

/-- **Čech `H⁰` / the sheaf condition for a covering family (Main Definition 1).**
For a covering family `𝒰 = {U_i ⟶ X}` of the site and a presheaf `G : Cᵒᵖ ⥤ Type u`, this is the
set of families `(s_i)` with `s_i ∈ G(U_i)` that agree on the overlaps `U_i ×_X U_j`:
`pr₁^* s_i = pr₂^* s_j`. It is the equalizer of `∏_i G(U_i) ⇉ ∏_{(i,j)} G(U_i ×_X U_j)`. -/
abbrev Site.cechH0 {X : C} {𝒰 : PreZeroHypercover.{u} X} (h : 𝒮.IsCov 𝒰)
    (G : Cᵒᵖ ⥤ Type u) : Type u :=
  { s : (i : 𝒰.I₀) → G.obj (op (𝒰.X i)) //
      ∀ i j, G.map (𝒮.fiberFst h i j).op (s i) = G.map (𝒮.fiberSnd h i j).op (s j) }

/-- The site's chosen fibre products `U_i ×_X U_j` are pullbacks of `𝒰.f i` along `𝒰.f j`. -/
lemma Site.isPullback_fiber {X : C} {𝒰 : PreZeroHypercover.{u} X} (h : 𝒮.IsCov 𝒰)
    (i j : 𝒰.I₀) :
    IsPullback (𝒮.fiberFst h i j) (𝒮.fiberSnd h i j) (𝒰.f i) (𝒰.f j) :=
  (𝒮.baseChange 𝒰 h (𝒰.f j)).isPullback i

/-- **This site's Čech `H⁰` is the canonical one.** `Site.cechH0` asks for agreement on the
site's *chosen* fibre products; `PreZeroHypercover.H0` asks for agreement on *every* cone over
each pair of sources, and needs no fibre products at all. The two agree, because the chosen
fibre products are pullbacks and so every cone factors through them — this is
`PreZeroHypercover.isMatching_iff_of_isPullback` at the site's base-change data.

So the definition above is not a third notion of Čech `H⁰` alongside the ones used for
Stacks 00W7/00W8: it is the same notion, phrased with the fibre products a site happens to
supply. -/
def Site.cechH0Equiv {X : C} {𝒰 : PreZeroHypercover.{u} X} (h : 𝒮.IsCov 𝒰)
    (G : Cᵒᵖ ⥤ Type u) : 𝒮.cechH0 h G ≃ PreZeroHypercover.H0 G 𝒰 :=
  Equiv.subtypeEquivRight fun s =>
    (PreZeroHypercover.isMatching_iff_of_isPullback G 𝒰 _ _ _ (𝒮.isPullback_fiber h) s).symm

/-- The canonical restriction map `G(X) ⟶ H⁰(𝒰, G)`, `s ↦ (s|_{U_i})_i`. -/
def Site.cechMap {X : C} {𝒰 : PreZeroHypercover.{u} X} (h : 𝒮.IsCov 𝒰)
    (G : Cᵒᵖ ⥤ Type u) (s : G.obj (op X)) : 𝒮.cechH0 h G :=
  ⟨fun i => G.map (𝒰.f i).op s, fun i j => by
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      (𝒮.isPullback_fiber h i j).w]⟩

/-- The `i`-th component of `cechMap h G s` is the restriction `s|_{U_i}`. -/
theorem Site.cechMap_coe {X : C} {𝒰 : PreZeroHypercover.{u} X} (h : 𝒮.IsCov 𝒰)
    (G : Cᵒᵖ ⥤ Type u) (s : G.obj (op X)) (i : 𝒰.I₀) :
    (𝒮.cechMap h G s).1 i = G.map (𝒰.f i).op s :=
  rfl

/-- A presheaf `G` satisfies the **Čech sheaf condition for the covering family `𝒰`** iff the
canonical restriction map `G(X) ⟶ H⁰(𝒰, G)` is a bijection (Main Definition 1). -/
def Site.IsSheafForFamily {X : C} {𝒰 : PreZeroHypercover.{u} X} (h : 𝒮.IsCov 𝒰)
    (G : Cᵒᵖ ⥤ Type u) : Prop :=
  Function.Bijective (𝒮.cechMap h G)

/-- A presheaf `G : Cᵒᵖ ⥤ Type u` is a **sheaf** for the site iff it satisfies the Čech sheaf
condition for every covering family of the site (Main Definition 1). -/
def Site.IsSheaf (G : Cᵒᵖ ⥤ Type u) : Prop :=
  ∀ {X : C} (𝒰 : PreZeroHypercover.{u} X) (h : 𝒮.IsCov 𝒰), 𝒮.IsSheafForFamily h G

/-- The category `Sh(C)` of **sheaves of sets** on the site: the full subcategory of presheaves
`Cᵒᵖ ⥤ Type u` satisfying the Čech sheaf condition `Site.IsSheaf` for the site. -/
@[sga "3 IV 4.3.1" "special case", sga "4 II 2.1" "special case", sga "4 II 6.1" "special case"]
abbrev Site.Sheaf : Type (u + 1) :=
  ObjectProperty.FullSubcategory (fun G : Cᵒᵖ ⥤ Type u => 𝒮.IsSheaf G)

/-- The inclusion `ι : Sh(C) ↪ PSh(C)` of sheaves into presheaves. -/
abbrev Site.sheafInclusion : 𝒮.Sheaf ⥤ (Cᵒᵖ ⥤ Type u) :=
  ObjectProperty.ι (fun G : Cᵒᵖ ⥤ Type u => 𝒮.IsSheaf G)

/-- **The "sections at `U`" functor** `Sh(C) ⥤ Set`: a sheaf is sent to its underlying presheaf
and then evaluated at `U`. Concretely `G ↦ G(U)`. -/
abbrev Site.sectionsAt (U : C) : 𝒮.Sheaf ⥤ Type u :=
  𝒮.sheafInclusion ⋙ (evaluation Cᵒᵖ (Type u)).obj (op U)

/-- **The canonical comparison map (Main Definition 4).**
`c_U : colim_{α<β} F_α(U) ⟶ (colim_{α<β} F_α)(U)`.
It is the canonical comparison `colim (F ⋙ G) ⟶ G (colim F)` for the sections-at-`U` functor
`G = sectionsAt 𝒮 U`, i.e. `CategoryTheory.Limits.colimit.post`. The domain
`colimit (F ⋙ 𝒮.sectionsAt U)` is the colimit in `Type u` of `α ↦ F_α(U)`; the codomain
`(𝒮.sectionsAt U).obj (colimit F)` is the sections at `U` of the colimit sheaf. -/
noncomputable def Site.colimSectionsComparison
    {β : Ordinal.{u}} (F : β.ToType ⥤ 𝒮.Sheaf) [HasColimit F] (U : C) :
    colimit (F ⋙ 𝒮.sectionsAt U) ⟶ (𝒮.sectionsAt U).obj (colimit F) :=
  colimit.post F (𝒮.sectionsAt U)

/-- **"Cofinality large enough" (Main Definition 6, Stacks/pretopology formulation).**
The cofinality of the ordinal `β` is *large enough* for the site `𝒮` when every covering family has
index set of cardinality strictly less than `cf β`: `|I| < cf β` for every covering family
`{U_i ⟶ X}_{i ∈ I}` of the site. This is the *pointwise* (per-covering) bound, exactly the
hypothesis used in Stacks 0GS0. -/
def Site.CofinalityLargeEnough (β : Ordinal.{u}) : Prop :=
  ∀ {X : C} (𝒰 : PreZeroHypercover.{u} X), 𝒮.IsCov 𝒰 → Cardinal.mk 𝒰.I₀ < β.cof

/-- **Cofinality bounding.** If `I` has cardinality `< cf β` and `f : I → β.ToType`, then the
family `f` is bounded above: there is `γ : β.ToType` with `f i ≤ γ` for all `i`. -/
theorem Ordinal.toType_bddAbove_of_lt_cof {β : Ordinal.{u}} {I : Type u}
    (hI : Cardinal.mk I < β.cof) (f : I → β.ToType) :
    ∃ γ : β.ToType, ∀ i, f i ≤ γ := by
  have hcard : Cardinal.mk (Set.range f) < Order.cof β.ToType := by
    rw [Ordinal.cof_toType]
    exact Cardinal.mk_range_le.trans_lt hI
  by_contra hcon
  push Not at hcon
  have hcof : IsCofinal (Set.range f) := fun a =>
    let ⟨i, hi⟩ := hcon a
    ⟨f i, ⟨i, rfl⟩, hi.le⟩
  exact absurd (Order.cof_le hcof) (not_le.mpr hcard)

namespace PointwiseColimit

variable {β : Ordinal.{u}} (G : β.ToType ⥤ (Cᵒᵖ ⥤ Type u)) [HasColimit G]

/-- The pointwise colimit injection through the evaluation iso. -/
theorem ι_app_eq (V : Cᵒᵖ) (α : β.ToType) (t : (G.obj α).obj V) :
    (colimit.ι G α).app V t
      = (colimitObjIsoColimitCompEvaluation G V).inv
          (colimit.ι (G ⋙ (evaluation Cᵒᵖ (Type u)).obj V) α t) := by
  have hm : (colimit.ι G α).app V
      = colimit.ι (G ⋙ (evaluation Cᵒᵖ (Type u)).obj V) α
          ≫ (colimitObjIsoColimitCompEvaluation G V).inv :=
    (Iso.eq_comp_inv _).2 (colimitObjIsoColimitCompEvaluation_ι_app_hom G α V)
  rw [ConcreteCategory.congr_hom hm t]
  rfl

/-- Jointly surjective at a point: every section of the pointwise presheaf colimit is in the image
of some stage. -/
theorem jointly_surjective (V : Cᵒᵖ) (s : (colimit G).obj V) :
    ∃ (α : β.ToType) (t : (G.obj α).obj V), (colimit.ι G α).app V t = s := by
  obtain ⟨α, t, ht⟩ :=
    Types.jointly_surjective' ((colimitObjIsoColimitCompEvaluation G V).hom s)
  refine ⟨α, t, ?_⟩
  rw [ι_app_eq G V α t, ht]
  simp

/-- Filtered colimit equality criterion at a point. -/
theorem ι_app_eq_iff (V : Cᵒᵖ) (α α' : β.ToType) (a : (G.obj α).obj V) (a' : (G.obj α').obj V) :
    (colimit.ι G α).app V a = (colimit.ι G α').app V a' ↔
      ∃ (k : β.ToType) (f : α ⟶ k) (g : α' ⟶ k),
        (G.map f).app V a = (G.map g).app V a' := by
  have hinj : Function.Injective (colimitObjIsoColimitCompEvaluation G V).inv := fun x y hxy => by
    simpa using congrArg (colimitObjIsoColimitCompEvaluation G V).hom hxy
  rw [ι_app_eq G V α a, ι_app_eq G V α' a', hinj.eq_iff,
    Types.FilteredColimit.colimit_eq_iff (G ⋙ (evaluation Cᵒᵖ (Type u)).obj V)]
  rfl

/-- The colimit injections are compatible with the transition maps, elementwise. -/
theorem ι_app_map_app {a b : β.ToType} (f : a ⟶ b) (V : Cᵒᵖ) (x : (G.obj a).obj V) :
    (colimit.ι G b).app V ((G.map f).app V x) = (colimit.ι G a).app V x := by
  have h := congrArg (fun (η : G.obj a ⟶ colimit G) => η.app V x) (colimit.w G f)
  simpa only [NatTrans.comp_app, types_comp_apply] using h

omit [HasColimit G] in
/-- Two composable transition maps compose to any transition map with the same endpoints. -/
theorem map_app_map_app {a b c : β.ToType} (f : a ⟶ b) (g : b ⟶ c) (f' : a ⟶ c) (V : Cᵒᵖ)
    (x : (G.obj a).obj V) : (G.map g).app V ((G.map f).app V x) = (G.map f').app V x := by
  rw [← types_comp_apply ((G.map f).app V) ((G.map g).app V), ← NatTrans.comp_app, ← G.map_comp]
  congr 2

/-- A family of fewer than `cf β` sections of the colimit lifts to a single stage. -/
theorem exists_stage_lift {J : Type u} (hJ : Cardinal.mk J < β.cof) (V : J → Cᵒᵖ)
    (s : ∀ j, (colimit G).obj (V j)) :
    ∃ (γ : β.ToType) (a : ∀ j, (G.obj γ).obj (V j)),
      ∀ j, (colimit.ι G γ).app (V j) (a j) = s j := by
  choose α t ht using fun j => jointly_surjective G (V j) (s j)
  obtain ⟨γ, hγ⟩ := Ordinal.toType_bddAbove_of_lt_cof hJ α
  exact ⟨γ, fun j => (G.map (homOfLE (hγ j))).app (V j) (t j),
    fun j => (ι_app_map_app G _ _ _).trans (ht j)⟩

/-- Fewer than `cf β` pairs of sections at one stage that agree in the colimit already agree at a
single later stage. -/
theorem exists_stage_map_app_eq {J : Type u} (hJ : Cardinal.mk J < β.cof) {V : J → Cᵒᵖ}
    {γ₀ : β.ToType} (x y : ∀ j, (G.obj γ₀).obj (V j))
    (h : ∀ j, (colimit.ι G γ₀).app (V j) (x j) = (colimit.ι G γ₀).app (V j) (y j)) :
    ∃ (γ : β.ToType) (f : γ₀ ⟶ γ),
      ∀ j, (G.map f).app (V j) (x j) = (G.map f).app (V j) (y j) := by
  choose k kf kg hk using fun j => (ι_app_eq_iff G (V j) γ₀ γ₀ (x j) (y j)).1 (h j)
  obtain ⟨γ₁, hγ₁⟩ := Ordinal.toType_bddAbove_of_lt_cof hJ k
  refine ⟨max γ₀ γ₁, homOfLE (le_max_left _ _), fun j => ?_⟩
  have hm := congrArg ((G.map (homOfLE ((hγ₁ j).trans (le_max_right γ₀ γ₁)))).app (V j)) (hk j)
  rwa [map_app_map_app G (kf j) _ (homOfLE (le_max_left γ₀ γ₁)),
    map_app_map_app G (kg j) _ (homOfLE (le_max_left γ₀ γ₁))] at hm

/-- Fewer than `cf β` pairs of restrictions of sections at one stage that agree in the colimit
already agree at a single later stage. -/
private theorem exists_stage_map_eq_of_restrict {J : Type u} (hJ : Cardinal.mk J < β.cof)
    {A₁ A₂ V : J → Cᵒᵖ} (u₁ : ∀ j, A₁ j ⟶ V j) (u₂ : ∀ j, A₂ j ⟶ V j) {γ₀ : β.ToType}
    (a₁ : ∀ j, (G.obj γ₀).obj (A₁ j)) (a₂ : ∀ j, (G.obj γ₀).obj (A₂ j))
    (h : ∀ j, (colimit G).map (u₁ j) ((colimit.ι G γ₀).app (A₁ j) (a₁ j)) =
      (colimit G).map (u₂ j) ((colimit.ι G γ₀).app (A₂ j) (a₂ j))) :
    ∃ (γ : β.ToType) (f : γ₀ ⟶ γ), ∀ j, (G.obj γ).map (u₁ j) ((G.map f).app (A₁ j) (a₁ j)) =
      (G.obj γ).map (u₂ j) ((G.map f).app (A₂ j) (a₂ j)) := by
  obtain ⟨γ, f, hf⟩ := exists_stage_map_app_eq G hJ (V := V)
    (fun j => (G.obj γ₀).map (u₁ j) (a₁ j)) (fun j => (G.obj γ₀).map (u₂ j) (a₂ j)) fun j => by
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
      exact h j
  exact ⟨γ, f, fun j => by simpa only [NatTrans.naturality_apply] using hf j⟩

end PointwiseColimit

-- Key Lemma A (cofinality): the presheaf colimit of a system of sheaves is a sheaf.

/-!
## Decomposition of Lemma A (`Site.isSheaf_colimit_presheaf`)

**Goal.** Under the pointwise cofinality bound `|I| < cf β` (Definition 6), the colimit
`F_colim := colimit (F ⋙ sheafInclusion)` computed *in presheaves* is again a sheaf for the site:
for every covering family `𝒰 = {U_i ⟶ X}_{i∈I}`, the Čech restriction map
`cechMap : F_colim(X) ⟶ H⁰(𝒰, F_colim)` is bijective.

The presheaf colimit is computed pointwise (Mathlib `colimitObjIsoColimitCompEvaluation`), so
`F_colim(W) = colim_α F_α(W)` for every object `W`, and the diagram `β.ToType` is filtered (it is a
linear order, in fact a directed/cofiltered-up poset). Two general facts about a *filtered* colimit
of sets, supplied by the `PointwiseColimit` namespace, drive the whole argument:

* `jointly_surjective`: every element of `F_colim(W)` is `(colimit.ι _ α).app W t` for some stage
  `α` and some `t ∈ F_α(W)`;
* `ι_app_eq_iff`: two such representatives `(α, a)` and `(α', a')` become equal in `F_colim(W)`
  iff they agree after pushing to some common later stage `k`.

We must show `cechMap` is bijective. We split into surjectivity and injectivity, each a *bounded*
filtered-colimit argument that uses the cofinality hypothesis through
`Ordinal.toType_bddAbove_of_lt_cof` (a family indexed by a set of cardinality `< cf β` is bounded
above by a single stage `γ`).

### Surjectivity (`cechMap_surjective`)
Let `s = (s_i)_{i∈I} ∈ H⁰(𝒰, F_colim)`, i.e. `s_i ∈ F_colim(U_i)` with the overlap agreements
`pr₁^* s_i = pr₂^* s_j` in `F_colim(U_i ×_X U_j)`.

1. *Lift each component to a stage.* By `jointly_surjective`, for each `i` pick a stage `αᵢ` and
   `t_i ∈ F_{αᵢ}(U_i)` with `(ι αᵢ).app _ t_i = s_i`. Since `|I| < cf β`, by
   `Ordinal.toType_bddAbove_of_lt_cof` there is a single stage `γ₀` with `αᵢ ≤ γ₀` for all `i`.
   Push every `t_i` along the transition `F_{αᵢ} ⟶ F_{γ₀}` to obtain `a_i ∈ F_{γ₀}(U_i)` with
   `(ι γ₀).app _ a_i = s_i` (functoriality of `ι`).

2. *Make the overlaps agree at one stage.* For each pair `(i,j)`, the two elements
   `pr₁^* a_i` and `pr₂^* a_j` of `F_{γ₀}(U_i ×_X U_j)` map to the *same* element `s` of
   `F_colim(U_i ×_X U_j)` (because `s_i, s_j` already agree there). By `ι_app_eq_iff`, there is a
   later stage `k_{ij}` (with maps `γ₀ ⟶ k_{ij}`) where they become equal. Since
   `|I × I| < cf β` (from `|I| < cf β`: for infinite `I`, `|I×I| = |I|`; for finite `I`, `|I×I|`
   is finite and `cf β` is infinite once any covering is bounded — see `cardinal_prod_lt_cof`),
   apply `Ordinal.toType_bddAbove_of_lt_cof` to the family `(i,j) ↦ k_{ij}` to get a single stage
   `γ ≥ γ₀` at which *all* overlap agreements hold simultaneously. Push the `a_i` to `b_i ∈
   F_γ(U_i)`.

3. *Use the sheaf condition at stage `γ`.* The family `(b_i)` now lies in `H⁰(𝒰, F_γ)` (overlap
   agreements hold at `γ`). Since `F_γ` is a sheaf (`(F.obj γ).2 𝒰 h` gives bijectivity of its
   `cechMap`), there is a unique `b ∈ F_γ(X)` with `cechMap b = (b_i)`. Let
   `x := (ι γ).app (op X) b ∈ F_colim(X)`. Then `cechMap x = s`: its `i`-th component is
   `F_colim.map (𝒰.f i).op x = (ι γ).app (U_i) (F_γ.map (𝒰.f i).op b) = (ι γ).app (U_i) b_i
   = s_i` (naturality of `ι` plus step 1–2 identifications).

### Injectivity (`cechMap_injective`)
Let `x, y ∈ F_colim(X)` with `cechMap x = cechMap y`, i.e. for all `i`,
`F_colim.map (𝒰.f i).op x = F_colim.map (𝒰.f i).op y` in `F_colim(U_i)`.

1. *Lift `x, y` to one stage.* By `jointly_surjective`, write `x = (ι α).app _ p`,
   `y = (ι α').app _ q`; push both to a common stage `γ₀` (linear order is directed) to get
   `p₀, q₀ ∈ F_{γ₀}(X)` with `(ι γ₀).app _ p₀ = x`, `(ι γ₀).app _ q₀ = y`.

2. *Components agree at a later stage.* For each `i`, `(ι γ₀).app (U_i) (F_{γ₀}.map (𝒰.f i).op
p₀) = (ι γ₀).app (U_i) (F_{γ₀}.map (𝒰.f i).op q₀)` (both `= F_colim.map (𝒰.f i).op x` resp `y`,
   which are equal). By `ι_app_eq_iff` there is a stage `k_i ≥ γ₀` where the restricted sections
   agree. Since `|I| < cf β`, `Ordinal.toType_bddAbove_of_lt_cof` gives a single `γ ≥ γ₀` where the
   restrictions of `p₀` and `q₀` to *every* `U_i` agree. Let `p, q ∈ F_γ(X)` be the pushes of
   `p₀, q₀`; then `cechMap p = cechMap q` in `H⁰(𝒰, F_γ)`.

3. *Use injectivity of the sheaf `F_γ`.* `F_γ` is a sheaf, so its `cechMap` is injective, hence
   `p = q`. Therefore `x = (ι γ).app _ p = (ι γ).app _ q = y`.

### Cardinal bound (`cardinal_prod_lt_cof`)
From `|I| < cf β` we need `|I × I| < cf β`. Note `cf β` is the cofinality of an ordinal; whenever a
nonempty covering exists, the bound `|I| < cf β` with `|I| ≥ 1` forces `cf β` infinite (`≥ ℵ₀`).
For *infinite* `I`, `Cardinal.mk (I × I) = Cardinal.mk I < cf β` (`Cardinal.mul_eq_self`). For
*finite* `I`, `|I × I|` is finite, hence `< ℵ₀ ≤ cf β`. We only invoke this for the *specific*
covering family `𝒰` at hand (so `|𝒰.I₀| < cf β` is available); the case split is `|𝒰.I₀|`
infinite vs finite, both giving `|𝒰.I₀ × 𝒰.I₀| < cf β` provided `cf β` is infinite, which holds
because `|𝒰.I₀| < cf β` with the empty case handled separately (if `𝒰.I₀` is empty then `I × I`
is empty too and the bound is trivial as long as `cf β ≠ 0`; and `cf β = 0` iff `β = 0`, in which
case `β.ToType` is empty and there is no colimit data to worry about — but cleanly, `0 < cf β`
always holds for `β` admitting the `HasColimit`, and more simply `|I × I| ≤ max ℵ₀ |I| < cf β`
when `cf β` is infinite).

-/

/-- Helper: from the pointwise cofinality bound on a single covering family we also bound the
cardinality of the pair index `I × I`. (Infinite `I`: `|I×I| = |I|`. Finite `I`: `|I×I|` finite,
and `cf β` is infinite.) The hypothesis `Cardinal.aleph0 ≤ β.cof` is automatic in the application,
since the identity covering `singleton (𝟙 X)` has index `PUnit` of cardinality `1`, forcing
`1 < β.cof`, hence `ℵ₀ ≤ β.cof` (cofinality is never strictly between `1` and `ℵ₀`). -/
theorem cardinal_prod_lt_cof {β : Ordinal.{u}} {I : Type u}
    (hcof : Cardinal.aleph0 ≤ β.cof) (hI : Cardinal.mk I < β.cof) :
    Cardinal.mk (I × I) < β.cof := by
  rcases finite_or_infinite I with hfin | hinf
  · exact lt_of_lt_of_le (Cardinal.lt_aleph0_of_finite _) hcof
  · rwa [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mul_eq_self (Cardinal.aleph0_le_mk I)]

/-- **Lemma A — surjectivity half.** Under the cofinality hypothesis, the Čech restriction map
`cechMap` of the presheaf colimit is surjective for every covering family. -/
theorem Site.cechMap_surjective_colimit
    {β : Ordinal.{u}} (F : β.ToType ⥤ 𝒮.Sheaf) [HasColimit (F ⋙ 𝒮.sheafInclusion)]
    (hβ : 𝒮.CofinalityLargeEnough β) {X : C} (𝒰 : PreZeroHypercover.{u} X) (h : 𝒮.IsCov 𝒰) :
    Function.Surjective (𝒮.cechMap h (colimit (F ⋙ 𝒮.sheafInclusion))) := by
  have hcof : Cardinal.aleph0 ≤ β.cof := Ordinal.aleph0_le_cof_iff.mpr
    (by simpa using hβ (PreZeroHypercover.singleton (𝟙 X)) (𝒮.isIso_mem (𝟙 X)))
  set G : β.ToType ⥤ (Cᵒᵖ ⥤ Type u) := F ⋙ 𝒮.sheafInclusion
  intro s
  obtain ⟨γ₀, a, ha⟩ :=
    PointwiseColimit.exists_stage_lift G (hβ 𝒰 h) (fun i => op (𝒰.X i)) s.1
  obtain ⟨γ, f, hf⟩ := PointwiseColimit.exists_stage_map_eq_of_restrict G
    (cardinal_prod_lt_cof hcof (hβ 𝒰 h)) (V := fun p => op (𝒮.fiberObj h p.1 p.2))
    (fun p => (𝒮.fiberFst h p.1 p.2).op) (fun p => (𝒮.fiberSnd h p.1 p.2).op)
    (fun p => a p.1) (fun p => a p.2) fun p => by
      rw [ha p.1, ha p.2]
      exact s.2 p.1 p.2
  obtain ⟨b₀, hb₀⟩ := ((F.obj γ).2 𝒰 h).2
    ⟨fun i => (G.map f).app (op (𝒰.X i)) (a i), fun i j => hf (i, j)⟩
  have hb₀i : ∀ i, (G.obj γ).map (𝒰.f i).op b₀ = (G.map f).app (op (𝒰.X i)) (a i) :=
    fun i => congrArg (fun z => z.1 i) hb₀
  refine ⟨(colimit.ι G γ).app (op X) b₀, Subtype.ext (funext fun i => ?_)⟩
  rw [Site.cechMap_coe, ← NatTrans.naturality_apply (colimit.ι G γ) (𝒰.f i).op b₀, hb₀i i,
    PointwiseColimit.ι_app_map_app]
  exact ha i

/-- **Lemma A — injectivity half.** Under the cofinality hypothesis, the Čech restriction map
`cechMap` of the presheaf colimit is injective for every covering family. -/
theorem Site.cechMap_injective_colimit
    {β : Ordinal.{u}} (F : β.ToType ⥤ 𝒮.Sheaf) [HasColimit (F ⋙ 𝒮.sheafInclusion)]
    (hβ : 𝒮.CofinalityLargeEnough β) {X : C} (𝒰 : PreZeroHypercover.{u} X) (h : 𝒮.IsCov 𝒰) :
    Function.Injective (𝒮.cechMap h (colimit (F ⋙ 𝒮.sheafInclusion))) := by
  set G : β.ToType ⥤ (Cᵒᵖ ⥤ Type u) := F ⋙ 𝒮.sheafInclusion
  intro x y hxy
  obtain ⟨α, p, rfl⟩ := PointwiseColimit.jointly_surjective G (op X) x
  obtain ⟨α', q, rfl⟩ := PointwiseColimit.jointly_surjective G (op X) y
  obtain ⟨p₀, hp⟩ : ∃ p₀, (colimit.ι G (max α α')).app (op X) p₀ = (colimit.ι G α).app (op X) p :=
    ⟨_, PointwiseColimit.ι_app_map_app G (homOfLE (le_max_left α α')) _ p⟩
  obtain ⟨q₀, hq⟩ : ∃ q₀, (colimit.ι G (max α α')).app (op X) q₀ = (colimit.ι G α').app (op X) q :=
    ⟨_, PointwiseColimit.ι_app_map_app G (homOfLE (le_max_right α α')) _ q⟩
  rw [← hp, ← hq] at hxy ⊢
  obtain ⟨γ, f, hf⟩ := PointwiseColimit.exists_stage_map_eq_of_restrict G (hβ 𝒰 h)
    (V := fun i => op (𝒰.X i)) (fun i => (𝒰.f i).op) (fun i => (𝒰.f i).op)
    (fun _ => p₀) (fun _ => q₀) fun i => congrArg (fun z => z.1 i) hxy
  have hpq : (G.map f).app (op X) p₀ = (G.map f).app (op X) q₀ :=
    ((F.obj γ).2 𝒰 h).1 (Subtype.ext (funext hf))
  rw [← PointwiseColimit.ι_app_map_app G f _ p₀, ← PointwiseColimit.ι_app_map_app G f _ q₀, hpq]

/-- **Lemma A (Stacks 0GS0, heart of the proof).** Under the large-cofinality hypothesis, the
colimit *in presheaves* of a `β`-indexed system of sheaves is again a sheaf.

Proof sketch: a presheaf is a sheaf for the site iff `cechMap` is bijective for every covering
family; this is `Function.Bijective`, i.e. injective ∧ surjective, supplied by
`Site.cechMap_injective_colimit` and `Site.cechMap_surjective_colimit`. -/
theorem Site.isSheaf_colimit_presheaf
    {β : Ordinal.{u}} (F : β.ToType ⥤ 𝒮.Sheaf) [HasColimit (F ⋙ 𝒮.sheafInclusion)]
    (hβ : 𝒮.CofinalityLargeEnough β) :
    𝒮.IsSheaf (colimit (F ⋙ 𝒮.sheafInclusion)) :=
  fun 𝒰 h => ⟨𝒮.cechMap_injective_colimit F hβ 𝒰 h, 𝒮.cechMap_surjective_colimit F hβ 𝒰 h⟩

/-- The inclusion `Sh(C) ↪ PSh(C)` preserves the colimit of a system `F` with large-enough
cofinality (because the presheaf colimit is a sheaf, Lemma A, and the inclusion is fully faithful,
hence reflects colimits). -/
theorem Site.preservesColimit_sheafInclusion
    {β : Ordinal.{u}} (F : β.ToType ⥤ 𝒮.Sheaf) [HasColimit F]
    (hβ : 𝒮.CofinalityLargeEnough β) :
    PreservesColimit F 𝒮.sheafInclusion := by
  have : CreatesColimit F 𝒮.sheafInclusion :=
    createsColimitFullSubcategoryInclusion F (𝒮.isSheaf_colimit_presheaf F hβ)
  infer_instance

/-- **(Stacks 0GS0.) Sections commute with colimits along ordinals of large enough cofinality.**

Let `𝒮` be a site (a small category `C` with covering families carrying explicit index sets and
satisfying axioms (1)–(3); in particular all fiber products `U_i ×_X U_j` exist). Let `β` be an
ordinal and `F : β.ToType ⥤ Sh(C)` a system of sheaves over `β` (a `β`-indexed direct system of
sheaves of sets), whose colimit in `Sh(C)` exists (`Sh(C)` is cocomplete, Definition 3). Suppose
the cofinality of `β` is large enough for `𝒮` (the pointwise bound `|I| < cf β` for every covering
family). Then for every object `U` the canonical comparison map `c_U` is a bijection. -/
@[stacks 0GS0]
theorem sections_commute_colimit_of_cofinality
    {β : Ordinal.{u}} (F : β.ToType ⥤ 𝒮.Sheaf) [HasColimit F]
    (hβ : 𝒮.CofinalityLargeEnough β) (U : C) :
    Function.Bijective (⇑(𝒮.colimSectionsComparison F U)) := by
  -- The inclusion preserves the colimit of `F` (Lemma A), evaluation always preserves colimits,
  -- so the sections-at-`U` functor preserves the colimit of `F`; hence the comparison map
  -- `colimit.post` is an isomorphism, i.e. a bijection in `Type u`.
  have : PreservesColimit F 𝒮.sheafInclusion := 𝒮.preservesColimit_sheafInclusion F hβ
  have : PreservesColimit F (𝒮.sectionsAt U) := by
    unfold Site.sectionsAt
    infer_instance
  have : IsIso (𝒮.colimSectionsComparison F U) := by
    unfold Site.colimSectionsComparison
    infer_instance
  rw [← isIso_iff_bijective]
  infer_instance

/-- Equivalent categorical phrasing of the Main Statement: the canonical comparison map is an
isomorphism (in `Type u`, an isomorphism is exactly a bijection). -/
theorem sections_commute_colimit_of_cofinality'
    {β : Ordinal.{u}} (F : β.ToType ⥤ 𝒮.Sheaf) [HasColimit F]
    (hβ : 𝒮.CofinalityLargeEnough β) (U : C) :
    IsIso (𝒮.colimSectionsComparison F U) :=
  (isIso_iff_bijective _).mpr (sections_commute_colimit_of_cofinality 𝒮 F hβ U)

end Stacks.Sites.ColimitCofinality
