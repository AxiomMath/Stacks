module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.CategoryTheory.Localization.Saturated.Closure
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
public import StacksFrontier.CategoryTheory.Functor.Derived.Shift

/-!
# Objects computing a derived functor everywhere

Let `F : D ⥤ D'` be a functor and `S` a saturated multiplicative system on `D`. If a class of
objects `I` is reachable from every object by a morphism of `S`, and `F` inverts the morphisms
of `S` between objects of `I`, then the right derived functor `RF` is everywhere defined and
every object of `I` computes `RF`; dually for the left derived functor `LF`.

## Main results

* `Stacks.DerivedFunctor.Computing.rightDerived_everywhereDefined_and_computes`: under the
  above hypotheses `F` is right derivable along `S`, and every object of `I` computes `RF`.
* `Stacks.DerivedFunctor.Computing.leftDerived_everywhereDefined_and_computes`: the dual
  statement for `LF`.

## Implementation notes

The statements are made for an arbitrary functor between categories and a `MorphismProperty`
`S` with a calculus of fractions and saturation, rather than for an exact functor of
triangulated categories and a compatible saturated multiplicative system: the triangulated
structure only serves to give `S` a calculus of fractions, so that the comma categories `X/S`
and `S/X` are filtered and cofiltered. The categories `X/S` and `S/X` are presented as
`RightFractionCat S X` and `LeftFractionCat S X`.

## References

* [Stacks, Tag 06XN](https://stacks.math.columbia.edu/tag/06XN)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

namespace Stacks.DerivedFunctor.Computing

variable {D : Type u} [Category.{v} D] {D' : Type u'} [Category.{v'} D']

/-! ## The categories `X/S` and `S/X`

`RightFractionCat S X` is the category `X/S`: its objects are arrows `s : X → X'` of `D`
lying in `S`, and a morphism `(s : X → X') ⟶ (t : X → X'')` is an arrow `a : X' → X''` with
`a ∘ s = t`. Dually, `LeftFractionCat S X` is the category `S/X` of arrows `s : X' → X` in
`S`. The diagrams `rightDiagram F S X` and `leftDiagram F S X` send `s : X → X'`, resp.
`s : X' → X`, to `F(X')`. -/

open StacksDerivedShift (RightFractionCat LeftFractionCat rightDiagram leftDiagram)

/-! ## The identity objects of `X/S` and `S/X` -/

/-- The object `(𝟙 X : X → X)` of `X/S`. -/
def rightIdObj (S : MorphismProperty D) [S.ContainsIdentities] (X : D) : RightFractionCat S X :=
  ⟨StructuredArrow.mk (𝟙 X), MorphismProperty.id_mem _ X⟩

/-- The object `(𝟙 X : X → X)` of `S/X`. -/
def leftIdObj (S : MorphismProperty D) [S.ContainsIdentities] (X : D) : LeftFractionCat S X :=
  ⟨CostructuredArrow.mk (𝟙 X), MorphismProperty.id_mem _ X⟩

/-! ## Filteredness of `X/S` and cofilteredness of `S/X` -/

/-- If `S` admits a left calculus of fractions, the category `X/S` is filtered. -/
theorem isFiltered_rightCat (S : MorphismProperty D) [S.HasLeftCalculusOfFractions] (X : D) :
    IsFiltered (RightFractionCat S X) :=
  IsFiltered.of_equivalence (S.underEquivStructuredArrow X)

/-- If `S` admits a right calculus of fractions, the category `S/X` is cofiltered. -/
theorem isCofiltered_leftCat (S : MorphismProperty D) [S.HasRightCalculusOfFractions] (X : D) :
    IsCofiltered (LeftFractionCat S X) :=
  IsCofiltered.of_equivalence (S.overEquivCostructuredArrow X)

/-! ## Colimits of diagrams inverting all morphisms

For a filtered category `K` and a functor `N : K ⥤ E` sending every morphism to an
isomorphism, `N` has a colimit cocone `constCocone` with apex `N.obj b₀` for any object `b₀`
(`constIsColimit`), and every functor `H` preserves the colimit of `N`
(`preserves_isColimit`). -/
namespace IsoInverting

variable {K E : Type*} [Category K] [Category E] [IsFiltered K] (N : K ⥤ E)
    (hiso : ∀ {a b : K} (f : a ⟶ b), IsIso (N.map f))

include hiso in
/-- On a filtered category, a functor inverting all morphisms identifies parallel morphisms. -/
lemma parallel_eq {a b : K} (f g : a ⟶ b) : N.map f = N.map g := by
  obtain ⟨c, h, hh⟩ : ∃ (c : K) (h : b ⟶ c), f ≫ h = g ≫ h :=
    ⟨IsFiltered.coeq f g, IsFiltered.coeqHom f g, IsFiltered.coeq_condition f g⟩
  have key : N.map (f ≫ h) = N.map (g ≫ h) := by rw [hh]
  simp only [N.map_comp] at key
  have := hiso h
  exact (cancel_mono (N.map h)).mp key

/-- The canonical comparison map `N.obj a ⟶ N.obj b` in a filtered category with all
transition maps invertible under `N`. -/
noncomputable def tau (a b : K) : N.obj a ⟶ N.obj b :=
  haveI := hiso (IsFiltered.rightToMax a b)
  N.map (IsFiltered.leftToMax a b) ≫ inv (N.map (IsFiltered.rightToMax a b))

include hiso in
/-- For any `p : a ⟶ m` and `q : b ⟶ m`, `tau N hiso a b ≫ N.map q = N.map p`. -/
lemma tau_comp_eq {a b m : K} (p : a ⟶ m) (q : b ⟶ m) :
    tau N hiso a b ≫ N.map q = N.map p := by
  have := hiso (IsFiltered.rightToMax a b)
  set u : IsFiltered.max a b ⟶ IsFiltered.max (IsFiltered.max a b) m :=
    IsFiltered.leftToMax (IsFiltered.max a b) m with hu
  set v : m ⟶ IsFiltered.max (IsFiltered.max a b) m :=
    IsFiltered.rightToMax (IsFiltered.max a b) m with hv
  have := hiso v
  have e1 : N.map (IsFiltered.rightToMax a b) ≫ N.map u = N.map q ≫ N.map v := by
    rw [← N.map_comp, ← N.map_comp]; exact parallel_eq N hiso _ _
  have e2 : N.map (IsFiltered.leftToMax a b) ≫ N.map u = N.map p ≫ N.map v := by
    rw [← N.map_comp, ← N.map_comp]; exact parallel_eq N hiso _ _
  rw [tau]
  apply (cancel_mono (N.map v)).mp
  rw [Category.assoc, Category.assoc, ← e1]
  rw [← Category.assoc (inv (N.map (IsFiltered.rightToMax a b))), IsIso.inv_hom_id,
    Category.id_comp]
  exact e2

include hiso in
/-- The image of any morphism `f : a ⟶ b` under `N` is `tau N hiso a b`. -/
lemma map_eq_tau {a b : K} (f : a ⟶ b) : N.map f = tau N hiso a b := by
  have := hiso (IsFiltered.rightToMax a b)
  rw [tau]
  have : N.map f ≫ N.map (IsFiltered.rightToMax a b) = N.map (IsFiltered.leftToMax a b) := by
    rw [← N.map_comp]
    exact parallel_eq N hiso (f ≫ IsFiltered.rightToMax a b) (IsFiltered.leftToMax a b)
  rw [← this, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

include hiso in
/-- The comparison map from an object to itself is the identity. -/
lemma tau_self (a : K) : tau N hiso a a = 𝟙 (N.obj a) := by
  rw [← map_eq_tau N hiso (𝟙 a), N.map_id]

include hiso in
/-- For `f : a ⟶ b`, `N.map f ≫ tau N hiso b c = tau N hiso a c`. -/
lemma tau_naturality {a b : K} (f : a ⟶ b) (c : K) :
    N.map f ≫ tau N hiso b c = tau N hiso a c := by
  have := hiso (IsFiltered.rightToMax b c)
  rw [tau, ← Category.assoc, ← N.map_comp]
  have h := tau_comp_eq N hiso (f ≫ IsFiltered.leftToMax b c) (IsFiltered.rightToMax b c)
  rw [IsIso.comp_inv_eq, ← h]

/-- The (essentially constant) colimit cocone of an iso-inverting diagram, with apex
`N.obj b₀`. -/
noncomputable def constCocone (b₀ : K) : Cocone N where
  pt := N.obj b₀
  ι := { app := fun a => tau N hiso a b₀
         naturality := fun a a' f => by
           simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
           exact tau_naturality N hiso f b₀ }

/-- The apex of `constCocone N hiso b₀` is `N.obj b₀`. -/
@[simp] lemma constCocone_pt (b₀ : K) : (constCocone N hiso b₀).pt = N.obj b₀ := rfl
/-- The leg of `constCocone N hiso b₀` at `a` is `tau N hiso a b₀`. -/
@[simp] lemma constCocone_ι_app (b₀ a : K) :
    (constCocone N hiso b₀).ι.app a = tau N hiso a b₀ := rfl

include hiso in
/-- For every cocone `s` over `N`, `tau N hiso a b₀ ≫ s.ι.app b₀ = s.ι.app a`. -/
lemma tau_fac (b₀ : K) (s : Cocone N) (a : K) :
    tau N hiso a b₀ ≫ s.ι.app b₀ = s.ι.app a := by
  have := hiso (IsFiltered.rightToMax a b₀)
  have hl : N.map (IsFiltered.leftToMax a b₀) ≫ s.ι.app (IsFiltered.max a b₀) = s.ι.app a := by
    simp
  have hr : N.map (IsFiltered.rightToMax a b₀) ≫ s.ι.app (IsFiltered.max a b₀) = s.ι.app b₀ := by
    simp
  rw [tau, ← hl, ← hr, Category.assoc]
  congr 1
  exact IsIso.inv_hom_id_assoc _ _

/-- The `constCocone` is a colimit cocone. -/
noncomputable def constIsColimit (b₀ : K) : IsColimit (constCocone N hiso b₀) where
  desc s := s.ι.app b₀
  fac s a := tau_fac N hiso b₀ s a
  uniq s m hm := by
    have h := hm b₀
    rw [constCocone_ι_app, tau_self] at h
    simpa using h

section Map
variable {E' : Type*} [Category E'] (H : E ⥤ E')

omit [IsFiltered K] in
include hiso in
/-- The composite `N ⋙ H` sends every morphism to an isomorphism. -/
lemma hisoMap : ∀ {a b : K} (f : a ⟶ b), IsIso ((N ⋙ H).map f) := fun {a b} f => by
  have := hiso f
  exact inferInstanceAs (IsIso (H.map (N.map f)))

/-- The image under `H` of `constCocone N hiso b₀` is a colimit cocone. -/
noncomputable def mapConstIsColimit (b₀ : K) :
    IsColimit (H.mapCocone (constCocone N hiso b₀)) := by
  refine IsColimit.ofIsoColimit (constIsColimit (N ⋙ H) (hisoMap N hiso H) b₀) ?_
  refine Cocone.ext (Iso.refl _) ?_
  intro a
  change tau (N ⋙ H) (hisoMap N hiso H) a b₀ ≫ 𝟙 _ = H.map (tau N hiso a b₀)
  rw [Category.comp_id, tau, tau, Functor.map_comp, Functor.map_inv]
  rfl

/-- Any functor preserves the colimit of an iso-inverting diagram on a filtered category. -/
noncomputable def preserves_isColimit (b₀ : K) {s : Cocone N} (hs : IsColimit s) :
    IsColimit (H.mapCocone s) := by
  refine IsColimit.ofIsoColimit (mapConstIsColimit N hiso H b₀) ?_
  exact (Cocone.functoriality N H).mapIso ((constIsColimit N hiso b₀).uniqueUpToIso hs)

end Map
end IsoInverting

/-! ## The subcategory of `X/S` on `S`-arrows into `I`

`JISObj S I X` is the (non-full) subcategory of `X/S` whose objects are arrows `s : X → X'` in
`S` with `X' ∈ I`, and whose morphisms are arrows `a` in `S` with `s ≫ a = t`. -/

/-- An object of the subcategory of `X/S`: an arrow `X → X'` in `S` with `X' ∈ I`. -/
structure JISObj (S : MorphismProperty D) (I : Set D) (X : D) where
  /-- The target `X'`. -/
  right : D
  /-- The arrow `X ⟶ X'`. -/
  hom : X ⟶ right
  /-- The arrow `X ⟶ X'` lies in `S`. -/
  hom_mem : S hom
  /-- The target lies in `I`. -/
  right_mem : right ∈ I

/-- A morphism of `JISObj S I X`: an arrow in `S` commuting with the structure arrows. -/
@[ext] structure JISHom {S : MorphismProperty D} {I : Set D} {X : D} (a b : JISObj S I X) where
  /-- The underlying arrow between targets. -/
  f : a.right ⟶ b.right
  /-- The underlying arrow lies in `S`. -/
  f_mem : S f
  /-- The arrow commutes with the structure arrows. -/
  w : a.hom ≫ f = b.hom

/-- The category structure on `JISObj S I X`, with identities and composition those of `D`. -/
instance JISObj.category (S : MorphismProperty D) (I : Set D) (X : D) [S.IsMultiplicative] :
    Category (JISObj S I X) where
  Hom a b := JISHom a b
  id a := ⟨𝟙 a.right, MorphismProperty.id_mem S a.right, by simp⟩
  comp {a b c} g h := ⟨g.f ≫ h.f, S.comp_mem _ _ g.f_mem h.f_mem, by
    rw [← Category.assoc, g.w, h.w]⟩
  id_comp _ := JISHom.ext (by simp)
  comp_id _ := JISHom.ext (by simp)
  assoc _ _ _ := JISHom.ext (by simp)

/-- The underlying arrow of an identity morphism of `JISObj S I X` is an identity. -/
@[simp] lemma JIS_id_f (S : MorphismProperty D) (I : Set D) (X : D) [S.IsMultiplicative]
    (a : JISObj S I X) : (𝟙 a : JISHom a a).f = 𝟙 a.right := rfl
/-- The underlying arrow of a composite in `JISObj S I X` is the composite of the arrows. -/
@[simp] lemma JIS_comp_f (S : MorphismProperty D) (I : Set D) (X : D) [S.IsMultiplicative]
    {a b c : JISObj S I X} (g : a ⟶ b) (h : b ⟶ c) : (g ≫ h).f = g.f ≫ h.f := rfl

/-- The inclusion of `JISObj S I X` into `X/S = RightFractionCat S X`. -/
def JISincl (S : MorphismProperty D) (I : Set D) (X : D) [S.IsMultiplicative] :
    JISObj S I X ⥤ RightFractionCat S X where
  obj a := ⟨StructuredArrow.mk a.hom, a.hom_mem⟩
  map {a b} g := ⟨StructuredArrow.homMk g.f (by simpa using g.w)⟩
  map_id a := by ext; rfl
  map_comp f g := by ext; rfl

/-- Given an arrow `s ∈ S` equalizing `f₁` and `f₂` on the left, some arrow in `S` into an
object of `I` coequalizes them. -/
private theorem exists_coequalizing_mem (S : MorphismProperty D) [S.HasLeftCalculusOfFractions]
    (I : Set D) (h1 : ∀ X : D, ∃ (X' : D) (s : X ⟶ X'), S s ∧ X' ∈ I)
    {A B C : D} (s : A ⟶ B) (hs : S s) (f₁ f₂ : B ⟶ C) (h : s ≫ f₁ = s ≫ f₂) :
    ∃ (Z : D) (u : C ⟶ Z), S u ∧ Z ∈ I ∧ f₁ ≫ u = f₂ ≫ u := by
  obtain ⟨Y, t, ht, htq⟩ := MorphismProperty.HasLeftCalculusOfFractions.ext f₁ f₂ s hs h
  obtain ⟨Z, r, hr, hZ⟩ := h1 Y
  exact ⟨Z, t ≫ r, S.comp_mem _ _ ht hr, hZ, by rw [← Category.assoc, ← Category.assoc, htq]⟩

/-- If `S` is saturated with a left calculus of fractions and every object admits an arrow
in `S` to an object of `I`, then `JISObj S I X` is filtered. -/
theorem rightCore_JIS_isFiltered (S : MorphismProperty D)
    [S.HasLeftCalculusOfFractions]
    (hSat : S.IsSaturatedMultiplicative) (I : Set D) (X : D)
    (h1 : ∀ X : D, ∃ (X' : D) (s : X ⟶ X'), S s ∧ X' ∈ I) :
    IsFiltered (JISObj S I X) := by
  -- Left cancellation for the saturated multiplicative system `S` admitting a left
  -- calculus of fractions: if `f, f ≫ g ∈ S` then `g ∈ S`. This is the key fact that
  -- keeps both connecting arrows of the cocones inside `S`. It is proved by passing to
  -- the localization `S.Q`: `S.Q.map g` is then an isomorphism, and a left fraction
  -- representing its inverse together with saturation forces `g ∈ S`.
  have cancel : ∀ {A B E : D} (p : A ⟶ B) (q : B ⟶ E), S p → S (p ≫ q) → S q := by
    intro A B E p q hp hpq
    have hQp : IsIso (S.Q.map p) := Localization.inverts S.Q S p hp
    have hQpq : IsIso (S.Q.map (p ≫ q)) := Localization.inverts S.Q S (p ≫ q) hpq
    rw [S.Q.map_comp] at hQpq
    have hQq : IsIso (S.Q.map q) := IsIso.of_isIso_comp_left (S.Q.map p) (S.Q.map q)
    obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction S.Q S (inv (S.Q.map q))
    have key : S.Q.map (q ≫ φ.f) = S.Q.map φ.s := by
      have e : S.Q.map q ≫ inv (S.Q.map q) = 𝟙 _ := IsIso.hom_inv_id _
      rw [hφ, φ.map_eq, ← Category.assoc, Iso.comp_inv_eq] at e
      rw [S.Q.map_comp, ← Localization.isoOfHom_hom S.Q S φ.s φ.hs]
      simpa using e
    rw [MorphismProperty.map_eq_iff_postcomp S.Q S] at key
    obtain ⟨Z, t, ht, htq⟩ := key
    have hqh : S (q ≫ (φ.f ≫ t)) := by
      rw [← Category.assoc, htq]
      exact S.comp_mem _ _ φ.hs ht
    exact hSat.mem_of_comp_mem_comp p q (φ.f ≫ t) hpq hqh
  obtain ⟨X₀, s₀, hs₀, hI₀⟩ := h1 X
  have : Nonempty (JISObj S I X) := ⟨⟨X₀, s₀, hs₀, hI₀⟩⟩
  have : IsFilteredOrEmpty (JISObj S I X) := by
    constructor
    · rintro ⟨A, sa, hsa, hAI⟩ ⟨B, sb, hsb, hBI⟩
      obtain ⟨ψ, hψ⟩ := (MorphismProperty.RightFraction.mk sa hsa sb).exists_leftFraction
      have hψeq : sb ≫ ψ.s = sa ≫ ψ.f := hψ
      have hgS : S ψ.f := cancel sa ψ.f hsa <| by
        rw [← hψeq]
        exact S.comp_mem _ _ hsb ψ.hs
      obtain ⟨Y'', r, hr, hY''I⟩ := h1 ψ.Y'
      refine ⟨⟨Y'', sa ≫ ψ.f ≫ r, ?_, hY''I⟩,
        ⟨ψ.f ≫ r, S.comp_mem _ _ hgS hr, ?_⟩,
        ⟨ψ.s ≫ r, S.comp_mem _ _ ψ.hs hr, ?_⟩, trivial⟩
      · exact S.comp_mem _ _ hsa (S.comp_mem _ _ hgS hr)
      · rfl
      · show sb ≫ ψ.s ≫ r = sa ≫ ψ.f ≫ r
        rw [← Category.assoc, ← Category.assoc, hψeq]
    · rintro ⟨A, sa, hsa, hAI⟩ ⟨B, sb, hsb, hBI⟩ f₁ f₂
      obtain ⟨C, u, hu, hCI, hfu⟩ :=
        exists_coequalizing_mem S I h1 sa hsa f₁.f f₂.f (by rw [f₁.w, f₂.w])
      exact ⟨⟨C, sb ≫ u, S.comp_mem _ _ hsb hu, hCI⟩, ⟨u, hu, rfl⟩, JISHom.ext hfu⟩
  exact IsFiltered.mk

/-- If `S` is saturated with a left calculus of fractions and every object admits an arrow
in `S` to an object of `I`, then the inclusion `JISincl S I X` of `JISObj S I X` into `X/S`
is final. -/
theorem rightCore_JISincl_final (S : MorphismProperty D)
    [S.HasLeftCalculusOfFractions]
    [∀ X : D, IsFiltered (RightFractionCat S X)]
    (hSat : S.IsSaturatedMultiplicative) (I : Set D) (X : D)
    (h1 : ∀ X : D, ∃ (X' : D) (s : X ⟶ X'), S s ∧ X' ∈ I) :
    (JISincl S I X).Final := by
  have : IsFiltered (JISObj S I X) := rightCore_JIS_isFiltered S hSat I X h1
  refine Functor.final_of_exists_of_isFiltered (JISincl S I X) ?_ ?_
  · rintro ⟨sa, hsa⟩
    obtain ⟨X'', r, hr, hX''I⟩ := h1 sa.right
    exact ⟨⟨X'', sa.hom ≫ r, S.comp_mem _ _ hsa hr, hX''I⟩, ⟨⟨StructuredArrow.homMk r rfl⟩⟩⟩
  · rintro ⟨da, hda⟩ c m m'
    obtain ⟨C, u, hu, hCI, hfu⟩ := exists_coequalizing_mem S I h1 da.hom hda m.hom.right
      m'.hom.right ((StructuredArrow.w m.hom).trans (StructuredArrow.w m'.hom).symm)
    exact ⟨⟨C, c.hom ≫ u, S.comp_mem _ _ c.hom_mem hu, hCI⟩, ⟨u, hu, rfl⟩, by ext; exact hfu⟩

/-- If `F` inverts the arrows of `S` between objects of `I`, then the composite
`JISincl S I X ⋙ rightDiagram F S X` sends every morphism to an isomorphism. -/
theorem rightCore_isoInverting (F : D ⥤ D') (S : MorphismProperty D) [S.IsMultiplicative]
    (I : Set D) (X : D)
    (h2 : ∀ ⦃X X' : D⦄ (s : X ⟶ X'), S s → X ∈ I → X' ∈ I → IsIso (F.map s))
    {a b : JISObj S I X} (g : a ⟶ b) :
    IsIso ((JISincl S I X ⋙ rightDiagram F S X).map g) :=
  h2 g.f g.f_mem a.right_mem b.right_mem

/-- Under the hypotheses of `rightDerived_everywhereDefined_and_computes`, for every `X` the
diagram `rightDiagram F S X` has a colimit cocone `c` that every functor
`coyoneda.obj (op W)` sends to a colimit cocone, and whose leg at `rightIdObj S X` is an
isomorphism whenever `X ∈ I`. -/
theorem rightCore (F : D ⥤ D') (S : MorphismProperty D)
    [S.HasLeftCalculusOfFractions]
    [∀ X : D, IsFiltered (RightFractionCat S X)]
    (hSat : S.IsSaturatedMultiplicative)
    (I : Set D)
    (h1 : ∀ X : D, ∃ (X' : D) (s : X ⟶ X'), S s ∧ X' ∈ I)
    (h2 : ∀ ⦃X X' : D⦄ (s : X ⟶ X'), S s → X ∈ I → X' ∈ I → IsIso (F.map s))
    (X : D) :
    ∃ c : Cocone (rightDiagram F S X),
      Nonempty (IsColimit c) ∧
      (∀ W : D', Nonempty (IsColimit ((coyoneda.obj (Opposite.op W)).mapCocone c))) ∧
      (X ∈ I → IsIso (c.ι.app (rightIdObj S X))) := by
  have : IsFiltered (JISObj S I X) := rightCore_JIS_isFiltered S hSat I X h1
  have : (JISincl S I X).Final := rightCore_JISincl_final S hSat I X h1
  set N : JISObj S I X ⥤ D' := JISincl S I X ⋙ rightDiagram F S X
  have hiso : ∀ {a b : JISObj S I X} (g : a ⟶ b), IsIso (N.map g) :=
    fun {a b} g => rightCore_isoInverting F S I X h2 g
  obtain ⟨X₀, s₀, hs₀, hX₀⟩ := h1 X
  set b₀ : JISObj S I X := ⟨X₀, s₀, hs₀, hX₀⟩
  set c : Cocone (rightDiagram F S X) :=
    (Functor.Final.extendCocone (F := JISincl S I X)).obj (IsoInverting.constCocone N hiso b₀)
  have hcol : IsColimit c := (Functor.Final.isColimitExtendCoconeEquiv (JISincl S I X) _).symm
    (IsoInverting.constIsColimit N hiso b₀)
  have hwc : IsColimit (Cocone.whisker (JISincl S I X) c) :=
    (Functor.Final.isColimitWhiskerEquiv (JISincl S I X) c).symm hcol
  refine ⟨c, ⟨hcol⟩, fun W => ?_, fun hX => ?_⟩
  · set H := coyoneda.obj (Opposite.op W)
    have hpre : IsColimit (H.mapCocone (Cocone.whisker (JISincl S I X) c)) :=
      IsoInverting.preserves_isColimit N hiso H b₀ hwc
    have hpre' : IsColimit (Cocone.whisker (JISincl S I X) (H.mapCocone c)) := hpre
    exact ⟨(Functor.Final.isColimitWhiskerEquiv (JISincl S I X) (H.mapCocone c)) hpre'⟩
  · set e₀ : JISObj S I X := ⟨X, 𝟙 X, MorphismProperty.id_mem S X, hX⟩
    have hleg : c.ι.app (rightIdObj S X)
        = (Cocone.whisker (JISincl S I X) c).ι.app e₀ := rfl
    rw [hleg]
    have htauiso : IsIso (IsoInverting.tau N hiso e₀ b₀) := by
      rw [IsoInverting.tau]
      have := hiso (IsFiltered.rightToMax e₀ b₀)
      have := hiso (IsFiltered.leftToMax e₀ b₀)
      infer_instance
    set φ : (Cocone.whisker (JISincl S I X) c) ≅ IsoInverting.constCocone N hiso b₀ :=
      hwc.uniqueUpToIso (IsoInverting.constIsColimit N hiso b₀)
    have hfac : (Cocone.whisker (JISincl S I X) c).ι.app e₀ ≫ φ.hom.hom
        = (IsoInverting.constCocone N hiso b₀).ι.app e₀ := φ.hom.w e₀
    have happ : (IsoInverting.constCocone N hiso b₀).ι.app e₀ = IsoInverting.tau N hiso e₀ b₀ := rfl
    have : IsIso φ.hom.hom := (Cocone.forget _).map_isIso φ.hom
    have : IsIso ((Cocone.whisker (JISincl S I X) c).ι.app e₀ ≫ φ.hom.hom) := by
      rw [hfac, happ]
      exact htauiso
    exact IsIso.of_isIso_comp_right _ φ.hom.hom

/-! ## Limits of diagrams inverting all morphisms

For a cofiltered category `K` and a functor `N : K ⥤ E` sending every morphism to an
isomorphism, `N` has a limit cone `constCone` with apex `N.obj b₀` for any object `b₀`
(`constIsLimit`). -/
namespace IsoInvertingLim

variable {K E : Type*} [Category K] [Category E] [IsCofiltered K] (N : K ⥤ E)
    (hiso : ∀ {a b : K} (f : a ⟶ b), IsIso (N.map f))

include hiso in
/-- On a cofiltered category, a functor inverting all morphisms identifies parallel
morphisms. -/
lemma parallel_eq {a b : K} (f g : a ⟶ b) : N.map f = N.map g := by
  obtain ⟨c, h, hh⟩ : ∃ (c : K) (h : c ⟶ a), h ≫ f = h ≫ g :=
    ⟨IsCofiltered.eq f g, IsCofiltered.eqHom f g, IsCofiltered.eq_condition f g⟩
  have key : N.map (h ≫ f) = N.map (h ≫ g) := by rw [hh]
  simp only [N.map_comp] at key
  have := hiso h
  exact (cancel_epi (N.map h)).mp key

/-- The canonical comparison map `N.obj a ⟶ N.obj b` in a cofiltered category with all
transition maps invertible under `N`. -/
noncomputable def sigma (a b : K) : N.obj a ⟶ N.obj b :=
  haveI := hiso (IsCofiltered.minToLeft a b)
  inv (N.map (IsCofiltered.minToLeft a b)) ≫ N.map (IsCofiltered.minToRight a b)

include hiso in
/-- For any `p : m ⟶ a` and `q : m ⟶ b`, `N.map p ≫ sigma N hiso a b = N.map q`. -/
lemma comp_sigma_eq {a b m : K} (p : m ⟶ a) (q : m ⟶ b) :
    N.map p ≫ sigma N hiso a b = N.map q := by
  have := hiso (IsCofiltered.minToLeft a b)
  set u : IsCofiltered.min m (IsCofiltered.min a b) ⟶ m :=
    IsCofiltered.minToLeft m (IsCofiltered.min a b) with hu
  set v : IsCofiltered.min m (IsCofiltered.min a b) ⟶ IsCofiltered.min a b :=
    IsCofiltered.minToRight m (IsCofiltered.min a b) with hv
  have := hiso u
  have e1 : N.map u ≫ N.map p = N.map v ≫ N.map (IsCofiltered.minToLeft a b) := by
    rw [← N.map_comp, ← N.map_comp]; exact parallel_eq N hiso _ _
  have e2 : N.map u ≫ N.map q = N.map v ≫ N.map (IsCofiltered.minToRight a b) := by
    rw [← N.map_comp, ← N.map_comp]; exact parallel_eq N hiso _ _
  rw [sigma]
  apply (cancel_epi (N.map u)).mp
  rw [← Category.assoc, e1, Category.assoc, IsIso.hom_inv_id_assoc]
  exact e2.symm

include hiso in
/-- The image of any morphism `f : a ⟶ b` under `N` is `sigma N hiso a b`. -/
lemma map_eq_sigma {a b : K} (f : a ⟶ b) : N.map f = sigma N hiso a b := by
  have := hiso (IsCofiltered.minToLeft a b)
  rw [sigma]
  have : N.map (IsCofiltered.minToLeft a b) ≫ N.map f = N.map (IsCofiltered.minToRight a b) := by
    rw [← N.map_comp]
    exact parallel_eq N hiso (IsCofiltered.minToLeft a b ≫ f) (IsCofiltered.minToRight a b)
  rw [← this, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

include hiso in
/-- The comparison map from an object to itself is the identity. -/
lemma sigma_self (a : K) : sigma N hiso a a = 𝟙 (N.obj a) := by
  rw [← map_eq_sigma N hiso (𝟙 a), N.map_id]

include hiso in
/-- For `f : a ⟶ b`, `sigma N hiso c a ≫ N.map f = sigma N hiso c b`. -/
lemma sigma_naturality {a b : K} (f : a ⟶ b) (c : K) :
    sigma N hiso c a ≫ N.map f = sigma N hiso c b := by
  have := hiso (IsCofiltered.minToLeft c a)
  rw [sigma, Category.assoc, ← N.map_comp]
  have h := comp_sigma_eq N hiso (IsCofiltered.minToLeft c a) (IsCofiltered.minToRight c a ≫ f)
  rw [IsIso.inv_comp_eq, ← h, sigma]

/-- The (essentially constant) limit cone of an iso-inverting diagram, with apex
`N.obj b₀`. -/
noncomputable def constCone (b₀ : K) : Cone N where
  pt := N.obj b₀
  π := { app := fun a => sigma N hiso b₀ a
         naturality := fun a a' f => by
           simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
           exact (sigma_naturality N hiso f b₀).symm }

/-- The apex of `constCone N hiso b₀` is `N.obj b₀`. -/
@[simp] lemma constCone_pt (b₀ : K) : (constCone N hiso b₀).pt = N.obj b₀ := rfl
/-- The leg of `constCone N hiso b₀` at `a` is `sigma N hiso b₀ a`. -/
@[simp] lemma constCone_π_app (b₀ a : K) :
    (constCone N hiso b₀).π.app a = sigma N hiso b₀ a := rfl

include hiso in
/-- For every cone `s` over `N`, `s.π.app b₀ ≫ sigma N hiso b₀ a = s.π.app a`. -/
lemma sigma_fac (b₀ : K) (s : Cone N) (a : K) :
    s.π.app b₀ ≫ sigma N hiso b₀ a = s.π.app a := by
  have := hiso (IsCofiltered.minToLeft b₀ a)
  have hl : s.π.app (IsCofiltered.min b₀ a) ≫ N.map (IsCofiltered.minToLeft b₀ a) = s.π.app b₀ := by
    simp
  have hr : s.π.app (IsCofiltered.min b₀ a) ≫ N.map (IsCofiltered.minToRight b₀ a) = s.π.app a := by
    simp
  rw [sigma, ← hl, ← hr, Category.assoc]
  congr 1
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

/-- The `constCone` is a limit cone. -/
noncomputable def constIsLimit (b₀ : K) : IsLimit (constCone N hiso b₀) where
  lift s := s.π.app b₀
  fac s a := sigma_fac N hiso b₀ s a
  uniq s m hm := by
    have h := hm b₀
    rw [constCone_π_app, sigma_self] at h
    simpa using h

end IsoInvertingLim

/-! ## The subcategory of `S/X` on `S`-arrows out of `P`

`JPSObj S P X` is the (non-full) subcategory of `S/X` whose objects are arrows `s : X' → X` in
`S` with `X' ∈ P`, and whose morphisms are arrows `a` in `S` with `a ≫ t = s`. -/

/-- An object of the subcategory of `S/X`: an arrow `X' → X` in `S` with `X' ∈ P`. -/
structure JPSObj (S : MorphismProperty D) (P : Set D) (X : D) where
  /-- The source `X'`. -/
  left : D
  /-- The arrow `X' ⟶ X`. -/
  hom : left ⟶ X
  /-- The arrow `X' ⟶ X` lies in `S`. -/
  hom_mem : S hom
  /-- The source lies in `P`. -/
  left_mem : left ∈ P

/-- A morphism of `JPSObj S P X`: an arrow in `S` commuting with the structure arrows. -/
@[ext] structure JPSHom {S : MorphismProperty D} {P : Set D} {X : D} (a b : JPSObj S P X) where
  /-- The underlying arrow between sources. -/
  f : a.left ⟶ b.left
  /-- The underlying arrow lies in `S`. -/
  f_mem : S f
  /-- The arrow commutes with the structure arrows. -/
  w : f ≫ b.hom = a.hom

/-- The category structure on `JPSObj S P X`, with identities and composition those of `D`. -/
instance JPSObj.category (S : MorphismProperty D) (P : Set D) (X : D) [S.IsMultiplicative] :
    Category (JPSObj S P X) where
  Hom a b := JPSHom a b
  id a := ⟨𝟙 a.left, MorphismProperty.id_mem S a.left, by simp⟩
  comp {a b c} g h := ⟨g.f ≫ h.f, S.comp_mem _ _ g.f_mem h.f_mem, by
    rw [Category.assoc, h.w, g.w]⟩
  id_comp _ := JPSHom.ext (by simp)
  comp_id _ := JPSHom.ext (by simp)
  assoc _ _ _ := JPSHom.ext (by simp)

/-- The underlying arrow of an identity morphism of `JPSObj S P X` is an identity. -/
@[simp] lemma JPS_id_f (S : MorphismProperty D) (P : Set D) (X : D) [S.IsMultiplicative]
    (a : JPSObj S P X) : (𝟙 a : JPSHom a a).f = 𝟙 a.left := rfl
/-- The underlying arrow of a composite in `JPSObj S P X` is the composite of the arrows. -/
@[simp] lemma JPS_comp_f (S : MorphismProperty D) (P : Set D) (X : D) [S.IsMultiplicative]
    {a b c : JPSObj S P X} (g : a ⟶ b) (h : b ⟶ c) : (g ≫ h).f = g.f ≫ h.f := rfl

/-- The inclusion of `JPSObj S P X` into `S/X = LeftFractionCat S X`. -/
def JPSincl (S : MorphismProperty D) (P : Set D) (X : D) [S.IsMultiplicative] :
    JPSObj S P X ⥤ LeftFractionCat S X where
  obj a := ⟨CostructuredArrow.mk a.hom, a.hom_mem⟩
  map {a b} g := ⟨CostructuredArrow.homMk g.f (by simpa using g.w)⟩
  map_id a := by ext; rfl
  map_comp f g := by ext; rfl

/-- Given an arrow `s ∈ S` equalizing `f₁` and `f₂` on the right, some arrow in `S` out of an
object of `P` equalizes them. -/
private theorem exists_equalizing_mem (S : MorphismProperty D) [S.HasRightCalculusOfFractions]
    (P : Set D) (h1 : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), S s ∧ X' ∈ P)
    {A B C : D} (s : B ⟶ C) (hs : S s) (f₁ f₂ : A ⟶ B) (h : f₁ ≫ s = f₂ ≫ s) :
    ∃ (Z : D) (u : Z ⟶ A), S u ∧ Z ∈ P ∧ u ≫ f₁ = u ≫ f₂ := by
  obtain ⟨Y, t, ht, htq⟩ := MorphismProperty.HasRightCalculusOfFractions.ext f₁ f₂ s hs h
  obtain ⟨Z, r, hr, hZ⟩ := h1 Y
  exact ⟨Z, r ≫ t, S.comp_mem _ _ hr ht, hZ, by rw [Category.assoc, Category.assoc, htq]⟩

/-- If `S` is saturated with a right calculus of fractions and every object admits an arrow
in `S` from an object of `P`, then `JPSObj S P X` is cofiltered. -/
theorem leftCore_JPS_isCofiltered (S : MorphismProperty D)
    [S.HasRightCalculusOfFractions]
    (hSat : S.IsSaturatedMultiplicative) (P : Set D) (X : D)
    (h1 : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), S s ∧ X' ∈ P) :
    IsCofiltered (JPSObj S P X) := by
  -- dual cancellation: if `q, p ≫ q ∈ S` then `p ∈ S`; proved via the localization and
  -- a RIGHT fraction representing `inv (S.Q.map p)`, then saturation.
  have cancel : ∀ {A B E : D} (p : A ⟶ B) (q : B ⟶ E), S q → S (p ≫ q) → S p := by
    intro A B E p q hq hpq
    have hQq : IsIso (S.Q.map q) := Localization.inverts S.Q S q hq
    have hQpq : IsIso (S.Q.map (p ≫ q)) := Localization.inverts S.Q S (p ≫ q) hpq
    rw [S.Q.map_comp] at hQpq
    have hQp : IsIso (S.Q.map p) := IsIso.of_isIso_comp_right (S.Q.map p) (S.Q.map q)
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction S.Q S (inv (S.Q.map p))
    have hmap : φ.map S.Q (Localization.inverts S.Q S) = inv (S.Q.map φ.s) ≫ S.Q.map φ.f :=
      eq_of_comp_right_eq fun {Z} => congrFun rfl
    have key : S.Q.map (φ.f ≫ p) = S.Q.map φ.s := by
      have e : inv (S.Q.map p) = inv (S.Q.map φ.s) ≫ S.Q.map φ.f := by rw [hφ, hmap]
      have e2 : S.Q.map φ.s ≫ inv (S.Q.map p) = S.Q.map φ.f := by
        rw [e, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
      have e3 : S.Q.map φ.s = S.Q.map φ.f ≫ S.Q.map p := by
        rw [← e2, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      exact (S.Q.map_comp _ _).trans e3.symm
    rw [MorphismProperty.map_eq_iff_precomp S.Q S] at key
    obtain ⟨Z, t, ht, htq⟩ := key
    have hcomp : S ((t ≫ φ.f) ≫ p) := by
      rw [Category.assoc, htq]
      exact S.comp_mem _ _ ht φ.hs
    exact hSat.mem_of_comp_mem_comp (t ≫ φ.f) p q hcomp hpq
  obtain ⟨X₀, s₀, hs₀, hP₀⟩ := h1 X
  have : Nonempty (JPSObj S P X) := ⟨⟨X₀, s₀, hs₀, hP₀⟩⟩
  have : IsCofilteredOrEmpty (JPSObj S P X) := by
    constructor
    · rintro ⟨A, sa, hsa, hAP⟩ ⟨B, sb, hsb, hBP⟩
      obtain ⟨ψ, hψ⟩ := (MorphismProperty.LeftFraction.mk sa sb hsb).exists_rightFraction
      have hψeq : ψ.s ≫ sa = ψ.f ≫ sb := hψ
      have hfS : S ψ.f := cancel ψ.f sb hsb <| by
        rw [← hψeq]
        exact S.comp_mem _ _ ψ.hs hsa
      obtain ⟨W', r, hr, hW'P⟩ := h1 ψ.X'
      refine ⟨⟨W', r ≫ ψ.s ≫ sa, ?_, hW'P⟩,
        ⟨r ≫ ψ.s, S.comp_mem _ _ hr ψ.hs, ?_⟩,
        ⟨r ≫ ψ.f, S.comp_mem _ _ hr hfS, ?_⟩, trivial⟩
      · exact S.comp_mem _ _ hr (S.comp_mem _ _ ψ.hs hsa)
      · exact Category.assoc _ _ _
      · show (r ≫ ψ.f) ≫ sb = r ≫ ψ.s ≫ sa
        rw [Category.assoc, ← hψeq]
    · rintro ⟨A, sa, hsa, hAP⟩ ⟨B, sb, hsb, hBP⟩ f₁ f₂
      obtain ⟨C, u, hu, hCP, hfu⟩ :=
        exists_equalizing_mem S P h1 sb hsb f₁.f f₂.f (by rw [f₁.w, f₂.w])
      exact ⟨⟨C, u ≫ sa, S.comp_mem _ _ hu hsa, hCP⟩, ⟨u, hu, rfl⟩,
        JPSHom.ext hfu⟩
  exact IsCofiltered.mk

/-- If `S` is saturated with a right calculus of fractions and every object admits an arrow
in `S` from an object of `P`, then the inclusion `JPSincl S P X` of `JPSObj S P X` into `S/X`
is initial. -/
theorem leftCore_JPSincl_initial (S : MorphismProperty D)
    [S.HasRightCalculusOfFractions]
    [∀ X : D, IsCofiltered (LeftFractionCat S X)]
    (hSat : S.IsSaturatedMultiplicative) (P : Set D) (X : D)
    (h1 : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), S s ∧ X' ∈ P) :
    (JPSincl S P X).Initial := by
  have : IsCofiltered (JPSObj S P X) := leftCore_JPS_isCofiltered S hSat P X h1
  refine Functor.initial_of_exists_of_isCofiltered (JPSincl S P X) ?_ ?_
  · rintro ⟨sa, hsa⟩
    obtain ⟨C, r, hr, hCP⟩ := h1 sa.left
    exact ⟨⟨C, r ≫ sa.hom, S.comp_mem _ _ hr hsa, hCP⟩, ⟨⟨CostructuredArrow.homMk r rfl⟩⟩⟩
  · rintro ⟨da, hda⟩ c m m'
    obtain ⟨C, u, hu, hCP, hfu⟩ := exists_equalizing_mem S P h1 da.hom hda m.hom.left
      m'.hom.left ((CostructuredArrow.w m.hom).trans (CostructuredArrow.w m'.hom).symm)
    exact ⟨⟨C, u ≫ c.hom, S.comp_mem _ _ hu c.hom_mem, hCP⟩, ⟨u, hu, rfl⟩,
      by ext; exact hfu⟩

/-- If `F` inverts the arrows of `S` between objects of `P`, then the composite
`JPSincl S P X ⋙ leftDiagram F S X` sends every morphism to an isomorphism. -/
theorem leftCore_isoInverting (F : D ⥤ D') (S : MorphismProperty D) [S.IsMultiplicative]
    (P : Set D) (X : D)
    (h2 : ∀ ⦃X X' : D⦄ (s : X ⟶ X'), S s → X ∈ P → X' ∈ P → IsIso (F.map s))
    {a b : JPSObj S P X} (g : a ⟶ b) :
    IsIso ((JPSincl S P X ⋙ leftDiagram F S X).map g) :=
  h2 g.f g.f_mem a.left_mem b.left_mem

/-- Under the hypotheses of `leftDerived_everywhereDefined_and_computes`, for every `X` the
diagram `leftDiagram F S X` has a limit cone `c` such that every functor `yoneda.obj W` sends
`c.op` to a colimit cocone, and whose leg at `leftIdObj S X` is an isomorphism whenever
`X ∈ P`. -/
theorem leftCore (F : D ⥤ D') (S : MorphismProperty D)
    [S.HasRightCalculusOfFractions]
    [∀ X : D, IsCofiltered (LeftFractionCat S X)]
    (hSat : S.IsSaturatedMultiplicative)
    (P : Set D)
    (h1 : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), S s ∧ X' ∈ P)
    (h2 : ∀ ⦃X X' : D⦄ (s : X ⟶ X'), S s → X ∈ P → X' ∈ P → IsIso (F.map s))
    (X : D) :
    ∃ c : Cone (leftDiagram F S X),
      Nonempty (IsLimit c) ∧
      (∀ W : D', Nonempty (IsColimit ((yoneda.obj W).mapCocone c.op))) ∧
      (X ∈ P → IsIso (c.π.app (leftIdObj S X))) := by
  have : IsCofiltered (JPSObj S P X) := leftCore_JPS_isCofiltered S hSat P X h1
  have : (JPSincl S P X).Initial := leftCore_JPSincl_initial S hSat P X h1
  set N : JPSObj S P X ⥤ D' := JPSincl S P X ⋙ leftDiagram F S X
  have hiso : ∀ {a b : JPSObj S P X} (g : a ⟶ b), IsIso (N.map g) :=
    fun {a b} g => leftCore_isoInverting F S P X h2 g
  have hisoOp : ∀ {a b : (JPSObj S P X)ᵒᵖ} (g : a ⟶ b), IsIso (N.op.map g) := fun g => by
    have := hiso g.unop
    exact inferInstanceAs (IsIso (N.map g.unop).op)
  obtain ⟨X₀, s₀, hs₀, hX₀⟩ := h1 X
  set b₀ : JPSObj S P X := ⟨X₀, s₀, hs₀, hX₀⟩
  set c : Cone (leftDiagram F S X) :=
    (Functor.Initial.extendCone (F := JPSincl S P X)).obj (IsoInvertingLim.constCone N hiso b₀)
  have hlim : IsLimit c := (Functor.Initial.isLimitExtendConeEquiv (JPSincl S P X) _).symm
    (IsoInvertingLim.constIsLimit N hiso b₀)
  have hwc : IsLimit (Cone.whisker (JPSincl S P X) c) :=
    (Functor.Initial.isLimitWhiskerEquiv (JPSincl S P X) c).symm hlim
  refine ⟨c, ⟨hlim⟩, fun W => ?_, fun hX => ?_⟩
  · have hpre : IsColimit ((yoneda.obj W).mapCocone (Cone.whisker (JPSincl S P X) c).op) :=
      IsoInverting.preserves_isColimit N.op hisoOp (yoneda.obj W) (Opposite.op b₀) hwc.op
    have hpre' : IsColimit (Cocone.whisker (JPSincl S P X).op ((yoneda.obj W).mapCocone c.op)) :=
      hpre
    exact ⟨(Functor.Final.isColimitWhiskerEquiv (JPSincl S P X).op ((yoneda.obj W).mapCocone c.op))
      hpre'⟩
  · set e₀ : JPSObj S P X := ⟨X, 𝟙 X, MorphismProperty.id_mem S X, hX⟩
    have hleg : c.π.app (leftIdObj S X)
        = (Cone.whisker (JPSincl S P X) c).π.app e₀ := rfl
    rw [hleg]
    have hsigiso : IsIso (IsoInvertingLim.sigma N hiso b₀ e₀) := by
      rw [IsoInvertingLim.sigma]
      have := hiso (IsCofiltered.minToLeft b₀ e₀)
      have := hiso (IsCofiltered.minToRight b₀ e₀)
      infer_instance
    set φ : IsoInvertingLim.constCone N hiso b₀ ≅ (Cone.whisker (JPSincl S P X) c) :=
      (IsoInvertingLim.constIsLimit N hiso b₀).uniqueUpToIso hwc
    have hfac : φ.hom.hom ≫ (Cone.whisker (JPSincl S P X) c).π.app e₀
        = (IsoInvertingLim.constCone N hiso b₀).π.app e₀ := φ.hom.w e₀
    have happ : (IsoInvertingLim.constCone N hiso b₀).π.app e₀
        = IsoInvertingLim.sigma N hiso b₀ e₀ := rfl
    have : IsIso φ.hom.hom := (Cone.forget _).map_isIso φ.hom
    have hcomp : IsIso (φ.hom.hom ≫ (Cone.whisker (JPSincl S P X) c).π.app e₀) := by
      rw [hfac, happ]
      exact hsigiso
    exact IsIso.of_isIso_comp_left φ.hom.hom _

/-! ## Main results -/

/-- Let `S` be a saturated multiplicative system on `D` admitting a left calculus of fractions,
and `F : D ⥤ D'` a functor. Suppose there is a subset `I ⊆ Ob(D)` such that:
1. for all `X` there is an arrow `s : X → X'` in `S` with `X' ∈ I`; and
2. for every arrow `s : X → X'` in `S` with `X, X' ∈ I`, `F.map s` is an isomorphism.

Then `RF` is everywhere defined, and every `X ∈ I` computes `RF`. -/
@[stacks 06XN "(1)"]
theorem rightDerived_everywhereDefined_and_computes
    (F : D ⥤ D') (S : MorphismProperty D)
    [S.HasLeftCalculusOfFractions]
    (hSat : S.IsSaturatedMultiplicative)
    (I : Set D)
    (h1 : ∀ X : D, ∃ (X' : D) (s : X ⟶ X'), S s ∧ X' ∈ I)
    (h2 : ∀ ⦃X X' : D⦄ (s : X ⟶ X'), S s → X ∈ I → X' ∈ I → IsIso (F.map s)) :
    F.IsRightDerivable S ∧ ∀ X ∈ I, F.ComputesRightDerived S X := by
  have := isFiltered_rightCat S
  have core := rightCore F S hSat I h1 h2
  refine ⟨fun X => ?_, fun X hX => ?_⟩
  · obtain ⟨c, -, hhom, -⟩ := core X
    rw [Functor.exists_isRightDerivedValueAt_iff]
    exact EssentiallyConstantInd.IsEssentiallyConstantInd.of_equivalence
      ⟨c, EssentiallyConstantInd.exists_isEssentiallyConstantWith_of_isColimit_coyoneda c hhom⟩
      (S.underToStructuredArrow X) (𝟭 D') (Iso.refl _)
  · obtain ⟨c, -, hhom, hiso⟩ := core X
    rw [Functor.computesRightDerived_iff]
    exact EssentiallyConstantInd.exists_isIso_of_equivalence (S.underToStructuredArrow X) (𝟭 D')
      (Iso.refl _) (i₀ := rightIdObj S X) (Iso.refl _)
      ⟨c, EssentiallyConstantInd.exists_isEssentiallyConstantWith_of_isColimit_coyoneda c hhom,
        hiso hX⟩

/-- Let `S` be a saturated multiplicative system on `D` admitting a right calculus of fractions,
and `F : D ⥤ D'` a functor. Suppose there is a subset `P ⊆ Ob(D)` such that:
1. for all `X` there is an arrow `s : X' → X` in `S` with `X' ∈ P`; and
2. for every arrow `s : X → X'` in `S` with `X, X' ∈ P`, `F.map s` is an isomorphism.

Then `LF` is everywhere defined, and every `X ∈ P` computes `LF`. -/
@[stacks 06XN "(2)"]
theorem leftDerived_everywhereDefined_and_computes
    (F : D ⥤ D') (S : MorphismProperty D)
    [S.HasRightCalculusOfFractions]
    (hSat : S.IsSaturatedMultiplicative)
    (P : Set D)
    (h1 : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), S s ∧ X' ∈ P)
    (h2 : ∀ ⦃X X' : D⦄ (s : X ⟶ X'), S s → X ∈ P → X' ∈ P → IsIso (F.map s)) :
    F.IsLeftDerivable S ∧ ∀ X ∈ P, F.ComputesLeftDerived S X := by
  have := isCofiltered_leftCat S
  have core := leftCore F S hSat P h1 h2
  refine ⟨fun X => ?_, fun X hX => ?_⟩
  · obtain ⟨c, -, hhom, -⟩ := core X
    rw [Functor.exists_isLeftDerivedValueAt_iff]
    exact EssentiallyConstantPro.IsEssentiallyConstantPro.of_equivalence
      ⟨c, EssentiallyConstantPro.exists_isEssentiallyConstantWith_of_isColimit_yoneda c hhom⟩
      (S.overToCostructuredArrow X) (𝟭 D') (Iso.refl _)
  · obtain ⟨c, -, hhom, hiso⟩ := core X
    rw [Functor.computesLeftDerived_iff]
    exact EssentiallyConstantPro.exists_isIso_of_equivalence (S.overToCostructuredArrow X) (𝟭 D')
      (Iso.refl _) (i₀ := leftIdObj S X) (Iso.refl _)
      ⟨c, EssentiallyConstantPro.exists_isEssentiallyConstantWith_of_isColimit_yoneda c hhom,
        hiso hX⟩

end Stacks.DerivedFunctor.Computing
