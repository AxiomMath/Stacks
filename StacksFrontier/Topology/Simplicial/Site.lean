module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Topology.Category.TopCat.Opens
public import StacksCore.Tactic.StacksAttribute

/-!
# The site of a simplicial topological space

For a simplicial topological space `X`, we form the category whose objects are open subsets of
the spaces in the diagram and whose morphisms are simplex maps that carry one open subset into
another.  The levelwise open covers define a site on this category.

## Main definitions

* `Stacks.Topology.Simplicial.SimplicialOpen`: the category of open subsets in all degrees of a
  simplicial topological space.
* `Stacks.Topology.Simplicial.SimplicialOpen.IsLevelwise`: a morphism whose simplex map is an
  identity.
* `Stacks.Topology.Simplicial.SimplicialOpen.IsCovering`: the prescribed notion of a levelwise
  open covering.
* `Stacks.Topology.Simplicial.SimplicialOpen.precoverage`: these families as a precoverage.
* `Stacks.Topology.Simplicial.SimplicialOpen.grothendieckTopology`: the resulting topology.

## Main results

* `Stacks.Topology.Simplicial.SimplicialOpen.precoverage_hasIsos`,
  `precoverage_hasPullbacks`, `precoverage_isStableUnderBaseChange` and
  `precoverage_isStableUnderComposition`: the prescribed covering families contain singleton
  isomorphisms, admit pullbacks, and are stable under base change and composition.
* `Stacks.Topology.Simplicial.SimplicialOpen.mem_grothendieckTopology`: a sieve is covering
  exactly when it contains a levelwise open covering family.

## Implementation notes

A morphism records its map in the simplex category together with the required containment of
open subsets. Mathlib's `Pretopology` requires all pullbacks in the underlying category, whereas
the definition of a site in the source requires them only along arrows belonging to covering
families. We therefore use a `Precoverage` together with the four classes expressing the site
axioms. Its generated Grothendieck topology is `grothendieckTopology`.

## References

* [Stacks Project, Tag 09VL](https://stacks.math.columbia.edu/tag/09VL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Topology.Simplicial

/-- An object of the site associated to a simplicial topological space: an open subset in one
simplicial degree. -/
structure SimplicialOpen (X : SimplicialObject TopCat.{u}) where
  /-- The simplicial degree containing the open subset. -/
  degree : SimplexCategoryᵒᵖ
  /-- The open subset in the specified degree. -/
  toOpens : Opens (X.obj degree)

namespace SimplicialOpen

variable {X : SimplicialObject TopCat.{u}}

/-- A morphism between simplicial opens is a simplex map whose induced continuous map carries
the source open subset into the target open subset. -/
structure Hom (U V : SimplicialOpen X) where
  /-- The map of simplicial degrees. -/
  base : U.degree ⟶ V.degree
  /-- The source open is contained in the inverse image of the target open. -/
  le : U.toOpens ≤ (Opens.map (X.map base)).obj V.toOpens

/-- Two morphisms of simplicial opens with the same simplex map are equal. -/
@[ext]
theorem Hom.ext {U V : SimplicialOpen X} (f g : Hom U V)
    (h : f.base = g.base) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The identity morphism of a simplicial open. -/
def Hom.id (U : SimplicialOpen X) : Hom U U where
  base := 𝟙 _
  le := by simp

/-- Composition of morphisms of simplicial opens. -/
def Hom.comp {U V W : SimplicialOpen X} (f : Hom U V) (g : Hom V W) : Hom U W where
  base := f.base ≫ g.base
  le := by
    intro x hx
    have hx' := f.le hx
    have hx'' := g.le hx'
    simpa [Functor.map_comp, Opens.map_def, Set.preimage_preimage] using hx''

/-- The category of simplicial opens of `X`, with morphisms `SimplicialOpen.Hom`. -/
instance : Category (SimplicialOpen X) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by ext; simp [Hom.comp, Hom.id]
  comp_id f := by ext; simp [Hom.comp, Hom.id]
  assoc f g h := by ext; simp [Hom.comp]

/-- A morphism of simplicial opens is levelwise if its simplex map is an identity, after the
source and target degrees are identified. -/
def IsLevelwise {U V : SimplicialOpen X} (f : U ⟶ V) : Prop :=
  ∃ e : U.degree = V.degree, f.base = eqToHom e

/-- A family of morphisms to `U` is a covering family when all its maps are levelwise and the
images of their source opens cover `U`. -/
def IsCovering (U : SimplicialOpen X) (R : Presieve U) : Prop :=
  (∀ (V : SimplicialOpen X) (f : V ⟶ U), R f → IsLevelwise f) ∧
    (∀ x ∈ U.toOpens, ∃ (V : SimplicialOpen X) (f : V ⟶ U),
      R f ∧ ∃ y ∈ V.toOpens, X.map f.base y = x)

/-- The levelwise open covering families of a simplicial topological space. -/
def precoverage (X : SimplicialObject TopCat.{u}) : Precoverage (SimplicialOpen X) where
  coverings U := { R | IsCovering U R }

private lemma map_map_eq_of_comp_eq_id {m n : SimplexCategoryᵒᵖ} (a : m ⟶ n) (b : n ⟶ m)
    (h : a ≫ b = 𝟙 m) (x : X.obj m) : X.map b (X.map a x) = x := by
  rw [← Functor.map_comp_apply, h]
  exact ConcreteCategory.congr_hom (X.map_id _) x

private lemma isLevelwise_of_isIso_base {U V : SimplicialOpen X} (f : U ⟶ V) [IsIso f.base] :
    IsLevelwise f := by
  rcases U with ⟨⟨⟨n⟩⟩, Uo⟩
  rcases V with ⟨⟨⟨m⟩⟩, Vo⟩
  obtain rfl : m = n := SimplexCategory.eq_of_isIso f.base.unop
  refine ⟨rfl, ?_⟩
  apply Quiver.Hom.unop_inj
  simpa using SimplexCategory.eq_id_of_isIso f.base.unop

private lemma isLevelwise_of_isIso {U V : SimplicialOpen X} (f : U ⟶ V) [IsIso f] :
    IsLevelwise f :=
  have : IsIso f.base :=
    ⟨⟨(asIso f).inv.base,
      congrArg (fun k : U ⟶ U ↦ k.base) (asIso f).hom_inv_id,
      congrArg (fun k : V ⟶ V ↦ k.base) (asIso f).inv_hom_id⟩⟩
  isLevelwise_of_isIso_base f

/-- **Stacks 09VL.** Singleton isomorphisms are levelwise open covering families. -/
@[stacks 09VL "the identity-covering axiom", instance]
theorem precoverage_hasIsos (X : SimplicialObject TopCat.{u}) :
    (precoverage X).HasIsos := by
  constructor
  intro U V f hf
  constructor
  · rintro W g ⟨⟩
    exact isLevelwise_of_isIso f
  · intro x hx
    refine ⟨U, f, .mk, X.map (asIso f).inv.base x, ?_, ?_⟩
    · exact Hom.le (asIso f).inv hx
    · exact map_map_eq_of_comp_eq_id _ _
        (congrArg (fun k : V ⟶ V ↦ k.base) (asIso f).inv_hom_id) x

private lemma hasPullback_of_isLevelwise {A B C : SimplicialOpen X}
    (f : A ⟶ C) (g : B ⟶ C) (hg : IsLevelwise g) : Limits.HasPullback g f := by
  rcases B with ⟨Bd, Bo⟩
  rcases C with ⟨Cd, Co⟩
  rcases hg with ⟨e, he⟩
  cases e
  rcases g with ⟨gb, gle⟩
  simp only at he
  subst gb
  let P : SimplicialOpen X :=
    ⟨A.degree, A.toOpens ⊓ (Opens.map (X.map f.base)).obj Bo⟩
  let p₁ : P ⟶ (⟨Bd, Bo⟩ : SimplicialOpen X) :=
    ⟨f.base, fun _ hx ↦ hx.2⟩
  let p₂ : P ⟶ A :=
    ⟨𝟙 _, fun _ hx ↦ by simpa using hx.1⟩
  have hc : p₁ ≫ (⟨𝟙 _, gle⟩ : (⟨Bd, Bo⟩ : SimplicialOpen X) ⟶
      (⟨Bd, Co⟩ : SimplicialOpen X)) = p₂ ≫ f := by
    apply Hom.ext
    change f.base ≫ 𝟙 _ = 𝟙 _ ≫ f.base
    simp
  let c : PullbackCone (⟨𝟙 _, gle⟩ : (⟨Bd, Bo⟩ : SimplicialOpen X) ⟶
      (⟨Bd, Co⟩ : SimplicialOpen X)) f := PullbackCone.mk p₁ p₂ hc
  refine ⟨⟨c, ?_⟩⟩
  refine PullbackCone.IsLimit.mk hc (fun s ↦ ?_) (fun s ↦ ?_) (fun s ↦ ?_)
    (fun s m hm₁ hm₂ ↦ ?_)
  · exact ⟨s.snd.base, fun x hx ↦ ⟨Hom.le s.snd hx, by
      have q := congrArg Hom.base s.condition
      change s.fst.base ≫ 𝟙 _ = s.snd.base ≫ f.base at q
      simp only [Category.comp_id] at q
      simpa [q, Functor.map_comp_apply] using Hom.le s.fst hx⟩⟩
  · apply Hom.ext
    have q := congrArg Hom.base s.condition
    change s.fst.base ≫ 𝟙 _ = s.snd.base ≫ f.base at q
    change s.snd.base ≫ f.base = s.fst.base
    simpa using q.symm
  · apply Hom.ext
    change s.snd.base ≫ 𝟙 _ = s.snd.base
    simp
  · apply Hom.ext
    have q := congrArg Hom.base hm₂
    change m.base ≫ 𝟙 _ = s.snd.base at q
    simpa using q

private lemma isLevelwise_comp {A B C : SimplicialOpen X} (f : A ⟶ B) (g : B ⟶ C)
    (hf : IsLevelwise f) (hg : IsLevelwise g) : IsLevelwise (f ≫ g) := by
  rcases hf with ⟨e, he⟩
  rcases hg with ⟨e', he'⟩
  refine ⟨e.trans e', ?_⟩
  change f.base ≫ g.base = _
  rw [he, he']
  simp

/-- **Stacks 09VL.** Pullbacks of arrows in a levelwise open covering family along arbitrary
morphisms exist. -/
@[stacks 09VL "existence of pullbacks of coverings", instance]
theorem precoverage_hasPullbacks (X : SimplicialObject TopCat.{u}) :
    (precoverage X).HasPullbacks := by
  constructor
  intro A C R f hR
  constructor
  intro B g hg
  exact hasPullback_of_isLevelwise f g (hR.1 B g hg)

private lemma isLevelwise_of_isPullback {P Y Z S : SimplicialOpen X}
    (p₁ : P ⟶ Y) (p₂ : P ⟶ Z) (g : Y ⟶ S) (f : Z ⟶ S)
    (hf : IsLevelwise f) (h : IsPullback p₁ p₂ g f) : IsLevelwise p₁ := by
  rcases Z with ⟨Zd, Zo⟩
  rcases S with ⟨Sd, So⟩
  rcases hf with ⟨e, he⟩
  cases e
  rcases f with ⟨fb, fle⟩
  simp only at he
  subst fb
  let Q : SimplicialOpen X := ⟨Y.degree, ⊥⟩
  let a : Q ⟶ Y := ⟨𝟙 _, fun _ hx ↦ hx.elim⟩
  let b : Q ⟶ (⟨Zd, Zo⟩ : SimplicialOpen X) := ⟨g.base, fun _ hx ↦ hx.elim⟩
  have hab : a ≫ g = b ≫ (⟨𝟙 _, fle⟩ : (⟨Zd, Zo⟩ : SimplicialOpen X) ⟶
      (⟨Zd, So⟩ : SimplicialOpen X)) := by
    apply Hom.ext
    change 𝟙 _ ≫ g.base = g.base ≫ 𝟙 _
    simp
  let l : Q ⟶ P := h.lift a b hab
  have hl₁ : l ≫ p₁ = a := h.lift_fst a b hab
  have hl₂ : l ≫ p₂ = b := h.lift_snd a b hab
  let QP : SimplicialOpen X := ⟨P.degree, ⊥⟩
  let r : QP ⟶ Q := ⟨p₁.base, fun _ hx ↦ hx.elim⟩
  let d : QP ⟶ P := ⟨𝟙 _, fun _ hx ↦ hx.elim⟩
  have hrl : r ≫ l = d := h.hom_ext
    (by
      apply Hom.ext
      have q := congrArg Hom.base hl₁
      change l.base ≫ p₁.base = 𝟙 _ at q
      change p₁.base ≫ l.base ≫ p₁.base = 𝟙 _ ≫ p₁.base
      calc
        _ = p₁.base ≫ 𝟙 _ := congrArg (fun k ↦ p₁.base ≫ k) q
        _ = p₁.base := Category.comp_id _
        _ = 𝟙 _ ≫ p₁.base := (Category.id_comp _).symm)
    (by
      apply Hom.ext
      have hs := congrArg Hom.base h.w
      have hl := congrArg Hom.base hl₂
      change l.base ≫ p₂.base = g.base at hl
      change p₁.base ≫ g.base = p₂.base ≫ 𝟙 _ at hs
      change p₁.base ≫ l.base ≫ p₂.base = 𝟙 _ ≫ p₂.base
      rw [hl]
      simp only [hs]
      simp)
  have : IsIso p₁.base := ⟨⟨l.base, congrArg Hom.base hrl, congrArg Hom.base hl₁⟩⟩
  exact isLevelwise_of_isIso_base p₁

/-- **Stacks 09VL.** Levelwise open covering families are stable under base change. -/
@[stacks 09VL "the base-change axiom", instance]
theorem precoverage_isStableUnderBaseChange (X : SimplicialObject TopCat.{u}) :
    (precoverage X).IsStableUnderBaseChange := by
  constructor
  intro ι S Z f hf Y g P p₁ p₂ h
  constructor
  · rintro Q q ⟨i⟩
    exact isLevelwise_of_isPullback _ _ _ _ (hf.1 _ _ (Presieve.ofArrows.mk i)) (h i)
  · intro x hx
    rcases hf.2 (X.map g.base x) (Hom.le g hx) with ⟨Zi, fi, hfi, z, hz, hzmap⟩
    let Y₀ := Y
    let g₀ : Y₀ ⟶ S := g
    rcases hfi with ⟨i⟩
    obtain ⟨e, he⟩ := hf.1 _ _ (Presieve.ofArrows.mk i)
    have : IsIso (f i).base := by
      rw [he]
      infer_instance
    let W : SimplicialOpen X := ⟨Y₀.degree,
      Y₀.toOpens ⊓ (Opens.map (X.map (g₀.base ≫ inv (f i).base))).obj (Z i).toOpens⟩
    let a : W ⟶ Y₀ := ⟨𝟙 _, fun _ hw ↦ by simpa using hw.1⟩
    let b : W ⟶ Z i := ⟨g₀.base ≫ inv (f i).base, fun _ hw ↦ hw.2⟩
    have hab : a ≫ g₀ = b ≫ f i := by
      apply Hom.ext
      change 𝟙 _ ≫ g₀.base = (g₀.base ≫ inv (f i).base) ≫ (f i).base
      simp
    let l : W ⟶ P i := (h i).lift a b hab
    have hxW : x ∈ W.toOpens := ⟨hx, by
      change X.map (g₀.base ≫ inv (f i).base) x ∈ (Z i).toOpens
      rw [Functor.map_comp_apply]
      rw [← hzmap, map_map_eq_of_comp_eq_id _ _ (by simp)]
      exact hz⟩
    refine ⟨P i, p₁ i, Presieve.ofArrows.mk i, X.map l.base x, Hom.le l hxW, ?_⟩
    have hb := congrArg Hom.base ((h i).lift_fst a b hab)
    exact map_map_eq_of_comp_eq_id _ _ hb x

/-- **Stacks 09VL.** Levelwise open covering families are stable under composition. -/
@[stacks 09VL "the composition axiom", instance]
theorem precoverage_isStableUnderComposition (X : SimplicialObject TopCat.{u}) :
    (precoverage X).IsStableUnderComposition := by
  constructor
  intro ι S U f hf σ V g hg
  constructor
  · rintro W k ⟨p⟩
    exact isLevelwise_comp _ _ ((hg p.1).1 _ _ (Presieve.ofArrows.mk p.2))
      (hf.1 _ _ (Presieve.ofArrows.mk p.1))
  · intro x hx
    rcases hf.2 x hx with ⟨Ui, fi, hfi, y, hy, rfl⟩
    rcases hfi with ⟨i⟩
    rcases (hg i).2 y hy with ⟨Vj, gj, hgj, z, hz, rfl⟩
    rcases hgj with ⟨j⟩
    refine ⟨V i j, g i j ≫ f i, Presieve.ofArrows.mk (Sigma.mk i j), z, hz, ?_⟩
    exact Functor.map_comp_apply X (g i j).base (f i).base z

/-- The Grothendieck topology on the category of simplicial opens. -/
abbrev grothendieckTopology (X : SimplicialObject TopCat.{u}) :
    GrothendieckTopology (SimplicialOpen X) :=
  (precoverage X).toGrothendieck

/-- A sieve belongs to the topology of a simplicial space exactly when it contains a levelwise
open covering family. -/
@[simp]
theorem mem_grothendieckTopology (X : SimplicialObject TopCat.{u})
    (U : SimplicialOpen X) (S : Sieve U) :
    S ∈ grothendieckTopology X U ↔
      ∃ R : Presieve U, IsCovering U R ∧ R ≤ S :=
  (precoverage X).mem_toGrothendieck_iff_of_isStableUnderComposition

end SimplicialOpen

end Stacks.Topology.Simplicial

end
