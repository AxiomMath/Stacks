module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Topology.Category.TopCat.Opens
public import StacksCore.Tactic.StacksAttribute

/-!
# The total site of a diagram of topological spaces

`Stacks.Topology.Simplicial.SimplicialOpen` is the site of Stacks 09VL attached to a simplicial
topological space: its objects are the open subsets of the spaces in the diagram, one simplicial
degree at a time, and its coverings are the levelwise open coverings. Nothing in that
construction uses the simplex category beyond one property, namely that an isomorphism of
simplicial degrees is an identity.

This file carries the construction out for a diagram of spaces indexed by an arbitrary category,
and isolates that property as a class. The reason for the generalization is the *slice* of such a
site: the slice of the total site of a simplicial space at an object `(n, W)` is not the site of
opens of `W`, but the total site of a diagram indexed by the category of simplicial degrees over
`n`, whose space at `φ : m ⟶ n` is the open `(X φ)⁻¹W` of `X_m`. That diagram is not a simplicial
space, so the slice comparison cannot even be stated inside `SimplicialOpen`.

## Main definitions

* `Stacks.Topology.Simplicial.IsoRigid`: a category in which every isomorphism has equal
  source and target and is then the identity.
* `Stacks.Topology.Simplicial.DiagramOpen`: the category of open subsets in all degrees of a
  diagram of topological spaces.
* `Stacks.Topology.Simplicial.DiagramOpen.IsLevelwise`: a morphism whose index map is an
  identity.
* `Stacks.Topology.Simplicial.DiagramOpen.IsCovering`: a levelwise open covering family.
* `Stacks.Topology.Simplicial.DiagramOpen.precoverage` and `.grothendieckTopology`: those
  families as a precoverage, and the topology it generates.

## Main results

* `Stacks.Topology.Simplicial.DiagramOpen.precoverage_hasIsos`,
  `.precoverage_hasPullbacks`, `.precoverage_isStableUnderBaseChange` and
  `.precoverage_isStableUnderComposition`: the four site axioms of Stacks 09VL, for a diagram
  indexed by an `IsoRigid` category.
* `Stacks.Topology.Simplicial.DiagramOpen.mem_grothendieckTopology`: a sieve is covering exactly
  when it contains a levelwise open covering family.

## Implementation notes

The index category enters the covering axioms only through `IsoRigid`, which is used twice: an
isomorphism of the site is levelwise, and so is the first projection of a pullback of a levelwise
arrow. `IsoRigid` holds for the simplex category, is stable under passing to the opposite
category, and is stable under passing to a slice — the three facts the slice comparison needs.

The site axioms are packaged as a `CategoryTheory.Precoverage` together with the four classes
expressing them, as in `Stacks.Topology.Simplicial.SimplicialOpen`: Mathlib's `Pretopology`
asks for all pullbacks in the underlying category, whereas the source asks for them only along
arrows of covering families.

## References

* [Stacks Project, Tag 09VL](https://stacks.math.columbia.edu/tag/09VL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v₁ u₁

namespace Stacks.Topology.Simplicial

/-- A category is *iso-rigid* when every isomorphism in it has equal source and target and is
then the identity. The simplex category is iso-rigid, and so is every opposite category and
every slice of an iso-rigid category. -/
class IsoRigid (A : Type u₁) [Category.{v₁} A] : Prop where
  /-- An isomorphism has equal source and target. -/
  eq_of_isIso : ∀ {a b : A} (f : a ⟶ b) [IsIso f], a = b
  /-- An automorphism is the identity. -/
  eq_id_of_isIso : ∀ {a : A} (f : a ⟶ a) [IsIso f], f = 𝟙 a

/-- An isomorphism in an iso-rigid category is `eqToHom` of an equality of its endpoints. -/
theorem IsoRigid.eq_eqToHom {A : Type u₁} [Category.{v₁} A] [IsoRigid A] {a b : A} (f : a ⟶ b)
    [IsIso f] : ∃ h : a = b, f = eqToHom h := by
  obtain rfl := IsoRigid.eq_of_isIso f
  exact ⟨rfl, by simpa using IsoRigid.eq_id_of_isIso f⟩

/-- The simplex category is iso-rigid: an isomorphism of simplices has equal lengths, hence
equal source and target, and is then the identity. -/
instance : IsoRigid SimplexCategory where
  eq_of_isIso {a b} f _ := by
    obtain ⟨p⟩ := a
    obtain ⟨q⟩ := b
    exact congrArg SimplexCategory.mk (SimplexCategory.len_eq_of_isIso f)
  eq_id_of_isIso _ := SimplexCategory.eq_id_of_isIso _

/-- The opposite of an iso-rigid category is iso-rigid. -/
instance isoRigid_op (A : Type u₁) [Category.{v₁} A] [IsoRigid A] : IsoRigid Aᵒᵖ where
  eq_of_isIso {a b} f _ :=
    have : IsIso f.unop := ((asIso f).unop).isIso_hom
    Opposite.unop_injective (IsoRigid.eq_of_isIso f.unop).symm
  eq_id_of_isIso {a} f _ := by
    have : IsIso f.unop := ((asIso f).unop).isIso_hom
    apply Quiver.Hom.unop_inj
    simpa using IsoRigid.eq_id_of_isIso f.unop

/-- A slice of an iso-rigid category is iso-rigid: an isomorphism of the slice is one of the
base, hence an identity, and then the two structure arrows agree. -/
instance isoRigid_over (A : Type u₁) [Category.{v₁} A] [IsoRigid A] (a : A) :
    IsoRigid (Over a) where
  eq_of_isIso {x y} f _ := by
    obtain ⟨xl, xh, rfl⟩ := x.mk_surjective
    obtain ⟨yl, yh, rfl⟩ := y.mk_surjective
    have : IsIso f.left := inferInstanceAs (IsIso ((Over.forget a).map f))
    obtain rfl := IsoRigid.eq_of_isIso f.left
    have hf : f.left = 𝟙 _ := IsoRigid.eq_id_of_isIso f.left
    obtain rfl : xh = yh := by simpa [hf] using (Over.w f).symm
    rfl
  eq_id_of_isIso {x} f _ := by
    have : IsIso f.left := inferInstanceAs (IsIso ((Over.forget a).map f))
    ext
    simpa using IsoRigid.eq_id_of_isIso f.left

/-- An object of the total site of a diagram of topological spaces: an open subset of the space
at one index. -/
structure DiagramOpen {A : Type u₁} [Category.{v₁} A] (X : A ⥤ TopCat.{u}) where
  /-- The index at which the open subset is taken. -/
  index : A
  /-- The open subset of the space at that index. -/
  toOpens : Opens (X.obj index)

namespace DiagramOpen

variable {A : Type u₁} [Category.{v₁} A] {X : A ⥤ TopCat.{u}}

/-- A morphism of the total site: a map of indices whose induced continuous map carries the
source open subset into the target open subset. -/
structure Hom (U V : DiagramOpen X) where
  /-- The map of indices. -/
  base : U.index ⟶ V.index
  /-- The source open is contained in the inverse image of the target open. -/
  le : U.toOpens ≤ (Opens.map (X.map base)).obj V.toOpens

/-- Two morphisms of the total site with the same index map are equal. -/
@[ext]
theorem Hom.ext {U V : DiagramOpen X} (f g : Hom U V) (h : f.base = g.base) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The identity morphism. -/
def Hom.id (U : DiagramOpen X) : Hom U U where
  base := 𝟙 _
  le := by simp

/-- Composition of morphisms of the total site. -/
def Hom.comp {U V W : DiagramOpen X} (f : Hom U V) (g : Hom V W) : Hom U W where
  base := f.base ≫ g.base
  le := by
    intro x hx
    have hx' := f.le hx
    have hx'' := g.le hx'
    simpa [Functor.map_comp, Opens.map_def, Set.preimage_preimage] using hx''

/-- The total site is a category, with the morphisms `Hom`, identities `Hom.id` and composition
`Hom.comp`. -/
instance : Category (DiagramOpen X) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by ext; simp [Hom.comp, Hom.id]
  comp_id f := by ext; simp [Hom.comp, Hom.id]
  assoc f g h := by ext; simp [Hom.comp]

/-- The index map of a composite is the composite of the index maps. -/
@[simp]
theorem Hom.comp_base {U V W : DiagramOpen X} (f : U ⟶ V) (g : V ⟶ W) :
    (f ≫ g).base = f.base ≫ g.base := rfl

/-- The index map of an identity morphism is the identity. -/
@[simp]
theorem Hom.id_base (U : DiagramOpen X) : (𝟙 U : Hom U U).base = 𝟙 U.index := rfl

/-- A morphism of the total site is levelwise if its index map is an identity, after the source
and target indices are identified. -/
def IsLevelwise {U V : DiagramOpen X} (f : U ⟶ V) : Prop :=
  ∃ e : U.index = V.index, f.base = eqToHom e

/-- A family of morphisms to `U` is a covering family when all its maps are levelwise and the
images of their source opens cover `U`. -/
def IsCovering (U : DiagramOpen X) (R : Presieve U) : Prop :=
  (∀ (V : DiagramOpen X) (f : V ⟶ U), R f → IsLevelwise f) ∧
    (∀ x ∈ U.toOpens, ∃ (V : DiagramOpen X) (f : V ⟶ U),
      R f ∧ ∃ y ∈ V.toOpens, X.map f.base y = x)

/-- The levelwise open covering families of a diagram of topological spaces. -/
def precoverage (X : A ⥤ TopCat.{u}) : Precoverage (DiagramOpen X) where
  coverings U := { R | IsCovering U R }

/-- A morphism whose index map has a two-sided inverse is levelwise. -/
private lemma isLevelwise_of_base_inv [IsoRigid A] {U V : DiagramOpen X} (f : U ⟶ V)
    (g : V.index ⟶ U.index) (h₁ : f.base ≫ g = 𝟙 _) (h₂ : g ≫ f.base = 𝟙 _) :
    IsLevelwise f :=
  have : IsIso f.base := ⟨⟨g, h₁, h₂⟩⟩
  IsoRigid.eq_eqToHom f.base

private lemma isLevelwise_of_isIso [IsoRigid A] {U V : DiagramOpen X} (f : U ⟶ V) [IsIso f] :
    IsLevelwise f :=
  isLevelwise_of_base_inv f (asIso f).inv.base
    (congrArg (fun k : U ⟶ U ↦ k.base) (asIso f).hom_inv_id)
    (congrArg (fun k : V ⟶ V ↦ k.base) (asIso f).inv_hom_id)

/-- The identity-covering axiom of Stacks 09VL for a diagram of topological spaces. -/
instance precoverage_hasIsos [IsoRigid A] (X : A ⥤ TopCat.{u}) :
    (precoverage X).HasIsos := by
  constructor
  intro U V f hf
  constructor
  · rintro W g ⟨⟩
    exact isLevelwise_of_isIso f
  · intro x hx
    refine ⟨U, f, .mk, X.map (asIso f).inv.base x, Hom.le (asIso f).inv hx, ?_⟩
    have h : (asIso f).inv.base ≫ f.base = 𝟙 _ := congrArg Hom.base (asIso f).inv_hom_id
    rw [← Functor.map_comp_apply, h]
    exact ConcreteCategory.congr_hom (X.map_id _) x

private lemma hasPullback_of_isLevelwise {P B C : DiagramOpen X}
    (f : P ⟶ C) (g : B ⟶ C) (hg : IsLevelwise g) : Limits.HasPullback g f := by
  rcases B with ⟨Bd, Bo⟩
  rcases C with ⟨Cd, Co⟩
  rcases hg with ⟨e, he⟩
  cases e
  rcases g with ⟨gb, gle⟩
  simp only [eqToHom_refl] at he
  subst gb
  let Q : DiagramOpen X := ⟨P.index, P.toOpens ⊓ (Opens.map (X.map f.base)).obj Bo⟩
  let p₁ : Q ⟶ (⟨Bd, Bo⟩ : DiagramOpen X) := ⟨f.base, fun _ hx ↦ hx.2⟩
  let p₂ : Q ⟶ P := ⟨𝟙 _, fun _ hx ↦ by simpa using hx.1⟩
  have hc : p₁ ≫ (⟨𝟙 _, gle⟩ : (⟨Bd, Bo⟩ : DiagramOpen X) ⟶
      (⟨Bd, Co⟩ : DiagramOpen X)) = p₂ ≫ f := by
    apply Hom.ext
    show f.base ≫ 𝟙 _ = 𝟙 _ ≫ f.base
    simp
  let c : PullbackCone (⟨𝟙 _, gle⟩ : (⟨Bd, Bo⟩ : DiagramOpen X) ⟶
      (⟨Bd, Co⟩ : DiagramOpen X)) f := PullbackCone.mk p₁ p₂ hc
  refine ⟨⟨c, ?_⟩⟩
  refine PullbackCone.IsLimit.mk hc (fun s ↦ ?_) (fun s ↦ ?_) (fun s ↦ ?_)
    (fun s m hm₁ hm₂ ↦ ?_)
  · exact ⟨s.snd.base, fun x hx ↦ ⟨Hom.le s.snd hx, by
      have q : s.fst.base ≫ 𝟙 _ = s.snd.base ≫ f.base := congrArg Hom.base s.condition
      simp only [Category.comp_id] at q
      simpa [q, Functor.map_comp_apply] using Hom.le s.fst hx⟩⟩
  · apply Hom.ext
    have q : s.fst.base ≫ 𝟙 _ = s.snd.base ≫ f.base := congrArg Hom.base s.condition
    show s.snd.base ≫ f.base = s.fst.base
    simpa using q.symm
  · apply Hom.ext
    show s.snd.base ≫ 𝟙 _ = s.snd.base
    simp
  · apply Hom.ext
    have q : m.base ≫ 𝟙 _ = s.snd.base := congrArg Hom.base hm₂
    simpa using q

private lemma isLevelwise_comp {P B C : DiagramOpen X} (f : P ⟶ B) (g : B ⟶ C)
    (hf : IsLevelwise f) (hg : IsLevelwise g) : IsLevelwise (f ≫ g) := by
  rcases hf with ⟨e, he⟩
  rcases hg with ⟨e', he'⟩
  exact ⟨e.trans e', by change f.base ≫ g.base = _; rw [he, he']; simp⟩

/-- The axiom of Stacks 09VL on existence of pullbacks of arrows of covering families. -/
instance precoverage_hasPullbacks (X : A ⥤ TopCat.{u}) : (precoverage X).HasPullbacks := by
  constructor
  intro P C R f hR
  constructor
  intro B g hg
  exact hasPullback_of_isLevelwise f g (hR.1 B g hg)

private lemma isLevelwise_of_isPullback [IsoRigid A] {P Y Z S : DiagramOpen X}
    (p₁ : P ⟶ Y) (p₂ : P ⟶ Z) (g : Y ⟶ S) (f : Z ⟶ S)
    (hf : IsLevelwise f) (h : IsPullback p₁ p₂ g f) : IsLevelwise p₁ := by
  rcases Z with ⟨Zd, Zo⟩
  rcases S with ⟨Sd, So⟩
  rcases hf with ⟨e, he⟩
  cases e
  rcases f with ⟨fb, fle⟩
  simp only [eqToHom_refl] at he
  subst fb
  let Q : DiagramOpen X := ⟨Y.index, ⊥⟩
  let a : Q ⟶ Y := ⟨𝟙 _, fun _ hx ↦ hx.elim⟩
  let b : Q ⟶ (⟨Zd, Zo⟩ : DiagramOpen X) := ⟨g.base, fun _ hx ↦ hx.elim⟩
  have hab : a ≫ g = b ≫ (⟨𝟙 _, fle⟩ : (⟨Zd, Zo⟩ : DiagramOpen X) ⟶
      (⟨Zd, So⟩ : DiagramOpen X)) := by
    apply Hom.ext
    show 𝟙 _ ≫ g.base = g.base ≫ 𝟙 _
    simp
  let l : Q ⟶ P := h.lift a b hab
  have hl₁ : l ≫ p₁ = a := h.lift_fst a b hab
  have hl₂ : l ≫ p₂ = b := h.lift_snd a b hab
  let QP : DiagramOpen X := ⟨P.index, ⊥⟩
  let r : QP ⟶ Q := ⟨p₁.base, fun _ hx ↦ hx.elim⟩
  let d : QP ⟶ P := ⟨𝟙 _, fun _ hx ↦ hx.elim⟩
  have hrl : r ≫ l = d := h.hom_ext
    (by
      apply Hom.ext
      have q : l.base ≫ p₁.base = 𝟙 _ := congrArg Hom.base hl₁
      show (p₁.base ≫ l.base) ≫ p₁.base = 𝟙 _ ≫ p₁.base
      rw [Category.assoc, q, Category.comp_id, Category.id_comp])
    (by
      apply Hom.ext
      have hs : p₁.base ≫ g.base = p₂.base ≫ 𝟙 _ := congrArg Hom.base h.w
      have hl : l.base ≫ p₂.base = g.base := congrArg Hom.base hl₂
      show (p₁.base ≫ l.base) ≫ p₂.base = 𝟙 _ ≫ p₂.base
      rw [Category.assoc, hl, hs, Category.comp_id, Category.id_comp])
  exact isLevelwise_of_base_inv p₁ l.base (congrArg Hom.base hrl) (congrArg Hom.base hl₁)

/-- The base-change axiom of Stacks 09VL for a diagram of topological spaces. -/
instance precoverage_isStableUnderBaseChange [IsoRigid A] (X : A ⥤ TopCat.{u}) :
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
    let W : DiagramOpen X := ⟨Y₀.index,
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
      have hinv : X.map (inv (f i).base) (X.map (f i).base z) = z := by
        rw [← Functor.map_comp_apply]
        simp
      rw [← hzmap, hinv]
      exact hz⟩
    refine ⟨P i, p₁ i, Presieve.ofArrows.mk i, X.map l.base x, Hom.le l hxW, ?_⟩
    have hb : l.base ≫ (p₁ i).base = 𝟙 _ := congrArg Hom.base ((h i).lift_fst a b hab)
    rw [← Functor.map_comp_apply, hb]
    exact ConcreteCategory.congr_hom (X.map_id _) x

/-- The composition axiom of Stacks 09VL for a diagram of topological spaces. -/
instance precoverage_isStableUnderComposition (X : A ⥤ TopCat.{u}) :
    (precoverage X).IsStableUnderComposition := by
  constructor
  intro ι S U f hf σ V g hg
  constructor
  · rintro W k ⟨p⟩
    exact isLevelwise_comp _ _ ((hg p.1).1 _ _ (Presieve.ofArrows.mk p.2))
      (hf.1 _ _ (Presieve.ofArrows.mk p.1))
  · intro x hx
    rcases hf.2 x hx with ⟨Ui, fi, ⟨i⟩, y, hy, rfl⟩
    rcases (hg i).2 y hy with ⟨Vj, gj, ⟨j⟩, z, hz, rfl⟩
    exact ⟨V i j, g i j ≫ f i, Presieve.ofArrows.mk (Sigma.mk i j), z, hz,
      Functor.map_comp_apply X (g i j).base (f i).base z⟩

/-- The levelwise arrow into `U` from an open subset of the space at the index of `U` that is
contained in the open of `U`. -/
def levelHom (U : DiagramOpen X) {V : Opens (X.obj U.index)} (h : V ≤ U.toOpens) :
    (⟨U.index, V⟩ : DiagramOpen X) ⟶ U where
  base := 𝟙 _
  le := by simpa using h

/-- The index map of `levelHom U h` is the identity. -/
@[simp]
theorem levelHom_base (U : DiagramOpen X) {V : Opens (X.obj U.index)} (h : V ≤ U.toOpens) :
    (levelHom U h).base = 𝟙 _ := rfl

/-- Two opens at the same index that are equal give isomorphic objects of the total site. -/
def levelwiseIso {a : A} {V W : Opens (X.obj a)} (h : V = W) :
    (⟨a, V⟩ : DiagramOpen X) ≅ ⟨a, W⟩ where
  hom := ⟨𝟙 _, by subst h; simp⟩
  inv := ⟨𝟙 _, by subst h; simp⟩
  hom_inv_id := Hom.ext _ _ (Category.id_comp (𝟙 a))
  inv_hom_id := Hom.ext _ _ (Category.id_comp (𝟙 a))

/-- The index map of the forward arrow of `levelwiseIso h` is the identity. -/
@[simp]
theorem levelwiseIso_hom_base {a : A} {V W : Opens (X.obj a)} (h : V = W) :
    (levelwiseIso (X := X) h).hom.base = 𝟙 a := rfl

/-- The index map of the inverse arrow of `levelwiseIso h` is the identity. -/
@[simp]
theorem levelwiseIso_inv_base {a : A} {V W : Opens (X.obj a)} (h : V = W) :
    (levelwiseIso (X := X) h).inv.base = 𝟙 a := rfl

/-- The topology of levelwise open coverings on the total site of a diagram of spaces. -/
abbrev grothendieckTopology (X : A ⥤ TopCat.{u}) : GrothendieckTopology (DiagramOpen X) :=
  (precoverage X).toGrothendieck

/-- A sieve on the total site of a diagram of spaces is covering exactly when it contains a
levelwise open covering family. -/
@[simp]
theorem mem_grothendieckTopology [IsoRigid A] (X : A ⥤ TopCat.{u}) (U : DiagramOpen X)
    (S : Sieve U) :
    S ∈ grothendieckTopology X U ↔ ∃ R : Presieve U, IsCovering U R ∧ R ≤ S :=
  (precoverage X).mem_toGrothendieck_iff_of_isStableUnderComposition

/-- **The covering sieves of the total site, pointwise.** A sieve on `U` is covering exactly
when every point of the open of `U` lies in some open at the index of `U`, contained in the
open of `U`, whose levelwise arrow into `U` belongs to the sieve. -/
theorem mem_grothendieckTopology_iff [IsoRigid A] {X : A ⥤ TopCat.{u}} {U : DiagramOpen X}
    (S : Sieve U) :
    S ∈ grothendieckTopology X U ↔
      ∀ x ∈ U.toOpens, ∃ (V : Opens (X.obj U.index)) (h : V ≤ U.toOpens),
        S.arrows (levelHom U h) ∧ x ∈ V := by
  rw [mem_grothendieckTopology]
  constructor
  · rintro ⟨R, hR, hRS⟩ x hx
    obtain ⟨V', f, hRf, y, hy, hyx⟩ := hR.2 x hx
    obtain ⟨e, he⟩ := hR.1 V' f hRf
    rcases V' with ⟨d, V₀⟩
    change d = U.index at e
    cases e
    simp only [eqToHom_refl] at he
    have hle : V₀ ≤ U.toOpens := by simpa [he] using Hom.le f
    have hfe : f = levelHom U hle := Hom.ext _ _ (by simp [he])
    refine ⟨V₀, hle, ?_, ?_⟩
    · rw [← hfe]
      exact hRS _ _ hRf
    · rw [← hyx, he]
      simpa using hy
  · intro H
    refine ⟨fun {_} g ↦ S.arrows g ∧ IsLevelwise g, ⟨fun _ _ hg ↦ hg.2, ?_⟩, fun _ _ hg ↦ hg.1⟩
    intro x hx
    obtain ⟨V, h, hS, hxV⟩ := H x hx
    exact ⟨⟨U.index, V⟩, levelHom U h, ⟨hS, ⟨rfl, rfl⟩⟩, x, hxV,
      ConcreteCategory.congr_hom (X.map_id _) x⟩

end DiagramOpen

end Stacks.Topology.Simplicial

end
