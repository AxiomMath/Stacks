module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SectionMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SpacesOverAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
public import StacksFrontier.CategoryTheory.Bicategory.IsoClassCategory
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.LocallyGroupoid

/-!
# The category `Spaces/𝒳` and its finite products

Stacks 04ZQ introduces the 2-category `Spaces/𝒳` of 1-morphisms to an algebraic stack `𝒳` which
are representable by algebraic spaces, observes that its hom-categories are setoids, and then
replaces its 1-morphisms by their isomorphism classes to obtain a *category*. That category is
`CategoryTheory.Bicategory.IsoClassCategory (Spaces/𝒳)`; it is given finite products here:

* the terminal object is `𝟙 𝒳 : 𝒳 ⟶ 𝒳`, which is representable by algebraic spaces because it
  is a section of itself (Stacks 050J);
* the product of `a : 𝒜 ⟶ 𝒳` and `d : 𝒟 ⟶ 𝒳` is `𝒜 ×_𝒳 𝒟 ⟶ 𝒳`, whose structure 1-morphism is
  representable by algebraic spaces because the first projection is a base change of `d`
  (Stacks 0302) and representability is stable under composition (Stacks 0301); its universal
  property is the 2-categorical universal property of the 2-fibre product (Stacks 04T2), read
  on isomorphism classes.

Together these give a `CategoryTheory.CartesianMonoidalCategory` structure, which is what the
notion of a group object — and hence Stacks 050R — is stated against.

## Main definitions

* `AlgebraicGeometry.Stack.SpacesOverStack.terminalObj`: the terminal object `𝟙 𝒳`.
* `AlgebraicGeometry.Stack.SpacesOverStack.prodObj`, `prodFst`, `prodSnd`, `prodLift`: the
  2-fibre product of two objects of `Spaces/𝒳`, its two projections, and the 1-morphism into it
  determined by a pair of 1-morphisms out of a common object.
* `AlgebraicGeometry.Stack.SpacesOverStack.instCartesianMonoidalCategory`: the finite-product
  monoidal structure on the category of Stacks 04ZQ.

## Main results

* `AlgebraicGeometry.Stack.SpacesOverStack.homGroupoid`: the hom-categories of `Spaces/𝒳` are
  groupoids, so isomorphism classes of 1-morphisms are the same thing as classes modulo the
  existence of a 2-morphism, which is how the source describes them.
* `AlgebraicGeometry.Stack.SpacesOverStack.isTerminal_terminalObj` and
  `AlgebraicGeometry.Stack.SpacesOverStack.prodIsLimit`: the two universal properties.
* `AlgebraicGeometry.Stack.SpacesOverStack.prod_hom_ext`: two morphisms into a 2-fibre product
  which agree on both projections are equal. This is the tool with which a concretely given
  1-morphism is identified with a morphism assembled from the monoidal structure.

## Implementation notes

The hom-categories of `Spaces/𝒳` are groupoids rather than merely setoids: the 2-category of
categories fibred in groupoids is locally groupoidal
(`CategoryTheory.CatFiberedInGroupoids.homGroupoid`), and a 2-morphism of `Spaces/𝒳` is
invertible as soon as its underlying 2-morphism is.

The 2-morphism computations below are written as applications of the five bookkeeping lemmas of
the `Algebra` section, each a plain identity in an abstract category, rather than as `rw`/`simp`
scripts. The reason is that the objects of a hom-category of `Spaces/𝒳` are 1-morphisms of
algebraic stacks, and the hom-category carries two defeq but syntactically distinct `Category`
instances — the one of the induced bicategory and the one `CategoryTheory.Bicategory.homCategory`
supplies — so a tactic that has to match an instance argument makes no progress, while a proof
term is checked up to definitional equality and goes through.

## References

* [Stacks Project, Tag 04ZQ](https://stacks.math.columbia.edu/tag/04ZQ)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 050J](https://stacks.math.columbia.edu/tag/050J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.SpacesOverStack

/-! ### Bookkeeping identities in an abstract category -/

section Algebra

variable {𝒞 : Type*} [Category 𝒞]

/-- A composite in which the middle morphism is an identity and the two outer pairs are mutually
inverse is the morphism it starts with. -/
theorem comp_whisker_cancel {O₁ O₂ O₃ O₄ : 𝒞} (x : O₁ ⟶ O₂) (p : O₂ ⟶ O₃) (q : O₃ ⟶ O₂)
    (s : O₃ ⟶ O₄) (t : O₄ ⟶ O₃) (ι : O₄ ⟶ O₄) (hι : ι = 𝟙 O₄) (hst : s ≫ t = 𝟙 O₃)
    (hpq : p ≫ q = 𝟙 O₂) : ((x ≫ p ≫ s) ≫ ι ≫ t) ≫ q = x := by
  simp [hι, reassoc_of% hst, hpq]

/-- A composite whose middle stretch is rewritten by a commuting square and whose outer pairs
cancel is the morphism in the middle of that square. -/
theorem comp_whisker_cancel' {O₁ O₂ O₃ O₄ O₅ O₆ O₇ : 𝒞} (x : O₁ ⟶ O₂) (y : O₂ ⟶ O₁)
    (z : O₁ ⟶ O₃) (m : O₃ ⟶ O₄) (n : O₄ ⟶ O₃) (p : O₂ ⟶ O₅) (r : O₅ ⟶ O₆) (g : O₆ ⟶ O₇)
    (s : O₄ ⟶ O₇) (t : O₇ ⟶ O₄) (hc : (y ≫ z) ≫ m ≫ s = p ≫ r ≫ g) (hxy : x ≫ y = 𝟙 O₁)
    (hst : s ≫ t = 𝟙 O₄) (hmn : m ≫ n = 𝟙 O₃) : ((x ≫ p ≫ r) ≫ g ≫ t) ≫ n = z := by
  simp [← reassoc_of% hc, reassoc_of% hxy, reassoc_of% hst, hmn]

/-- Cancelling the two invertible stretches at the end of a composite. -/
theorem comp_cancel_inv {O₁ O₂ O₃ O₄ O₅ : 𝒞} (c : O₁ ⟶ O₂) (g : O₂ ⟶ O₃) (i : O₃ ⟶ O₄)
    (j : O₄ ⟶ O₃) (p : O₄ ⟶ O₅) (q : O₅ ⟶ O₄) (x : O₁ ⟶ O₅) (h : (c ≫ g ≫ i) ≫ p = x)
    (hpq : p ≫ q = 𝟙 O₄) (hij : i ≫ j = 𝟙 O₃) : x ≫ q ≫ j = c ≫ g := by
  simp [← h, reassoc_of% hpq, hij]

/-- Two factorisations of one morphism through an invertible morphism agree. -/
theorem comp_cancel_mid {O₁ O₂ O₃ O₄ O₅ O₆ O₇ : 𝒞} (x : O₁ ⟶ O₂) (y : O₂ ⟶ O₁) (z : O₁ ⟶ O₃)
    (a : O₃ ⟶ O₄) (b : O₄ ⟶ O₅) (c : O₁ ⟶ O₆) (g : O₆ ⟶ O₅) (p : O₂ ⟶ O₇) (r : O₇ ⟶ O₆)
    (h₂ : z ≫ a ≫ b = c ≫ g) (h₁ : x ≫ p ≫ r = c) (hyx : y ≫ x = 𝟙 O₂) :
    (y ≫ z) ≫ a ≫ b = p ≫ r ≫ g := by
  simp [h₂, ← h₁, reassoc_of% hyx]

/-- Substituting a naturality square into a factorisation. -/
theorem comp_nat_subst {O₁ O₂ O₃ O₄ O₅ O₆ : 𝒞} (x : O₁ ⟶ O₂) (p : O₂ ⟶ O₃) (w : O₃ ⟶ O₄)
    (r : O₄ ⟶ O₅) (j : O₃ ⟶ O₆) (Θ : O₆ ⟶ O₅) (c : O₁ ⟶ O₆) (pw : O₂ ⟶ O₄)
    (hpw : pw = p ≫ w) (hnat : w ≫ r = j ≫ Θ) (h₁ : x ≫ p ≫ j = c) : c ≫ Θ = x ≫ pw ≫ r := by
  simp [← h₁, hpw, hnat]

end Algebra

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **The hom-categories of `Spaces/𝒳` are groupoids.** A 2-morphism of `Spaces/𝒳` carries one
datum, a 2-morphism of the underlying 1-morphisms of algebraic stacks, and that is invertible
because the 2-category of algebraic stacks is locally groupoidal; the compatibility condition
for the inverse is automatic (`AlgebraicGeometry.Stack.SpacesOverStack.Hom₂.iso`). -/
instance homGroupoid (F G : SpacesOverStack B S hS 𝒳) : IsGroupoid (F ⟶ G) where
  all_isIso η :=
    (Hom₂.iso (asIso η.map) η.compat).isIso_hom

/-- The isomorphism of underlying 1-morphisms of algebraic stacks carried by an isomorphism of
1-morphisms of `Spaces/𝒳`. -/
def mapIso {F G : SpacesOverStack B S hS 𝒳} {f g : F ⟶ G} (e : f ≅ g) : f.map ≅ g.map where
  hom := e.hom.map
  inv := e.inv.map
  hom_inv_id := congrArg Hom₂.map e.hom_inv_id
  inv_hom_id := congrArg Hom₂.map e.inv_hom_id

/-- Two 1-morphisms of `Spaces/𝒳` with equal underlying 1-morphisms of algebraic stacks and
matching comparison 2-morphisms have the same isomorphism class. -/
theorem homMk_eq_of_map_eq {F G : SpacesOverStack B S hS 𝒳} (f g : F ⟶ G) (h : f.map = g.map)
    (hc : f.comm ≫ (eqToIso h).hom ▷ G.map = g.comm) :
    IsoClassCategory.homMk f = IsoClassCategory.homMk g :=
  IsoClassCategory.homMk_eq_of_iso (Hom₂.iso (eqToIso h) hc)

/-! ### The terminal object -/

/-- **The terminal object of `Spaces/𝒳`:** the identity 1-morphism of `𝒳`, which is
representable by algebraic spaces because it is a section of itself (Stacks 050J). -/
def terminalObj (𝒳 : AlgebraicStacks.{u, w} B S hS) : SpacesOverStack B S hS 𝒳 where
  source := 𝒳
  map := 𝟙 𝒳
  representable :=
    isRepresentableByAlgebraicSpaces_section B S hS (𝟙 𝒳) (𝟙 𝒳) ⟨λ_ (𝟙 𝒳)⟩

/-- The canonical 1-morphism of `Spaces/𝒳` to the terminal object: on underlying algebraic
stacks it is the structure 1-morphism itself. -/
def toTerminalObj (F : SpacesOverStack B S hS 𝒳) : F ⟶ terminalObj B S hS 𝒳 where
  map := F.map
  comm := (ρ_ F.map).inv

/-- Every 1-morphism of `Spaces/𝒳` to the terminal object is isomorphic to the canonical one:
its comparison 2-morphism is invertible, and exhibits the isomorphism. -/
noncomputable def toTerminalObjIso {F : SpacesOverStack B S hS 𝒳}
    (k : F ⟶ terminalObj B S hS 𝒳) : k ≅ toTerminalObj B S hS F :=
  Hom₂.iso (asIso k.comm ≪≫ ρ_ k.map).symm (by
    dsimp only [terminalObj, toTerminalObj]
    refine (cancel_mono (ρ_ F.map).hom).1 ?_
    rw [Category.assoc, rightUnitor_naturality, Iso.inv_hom_id, ← Category.assoc]
    exact (asIso k.comm ≪≫ ρ_ k.map).hom_inv_id)

/-- **The identity 1-morphism of `𝒳` is a terminal object of the category of Stacks 04ZQ.** -/
noncomputable def isTerminal_terminalObj (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    IsTerminal (IsoClassCategory.mk (terminalObj B S hS 𝒳)) :=
  IsTerminal.ofUniqueHom
    (fun F => IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) (toTerminalObj B S hS F))
    (fun _ m => by
      induction m using Quotient.inductionOn with
      | _ k => exact IsoClassCategory.homMk_eq_of_iso (toTerminalObjIso B S hS k))

/-! ### Binary products -/

/-- The canonical 2-fibre product square of the structure 1-morphisms of two objects of
`Spaces/𝒳`. -/
abbrev prodSquare (A D : SpacesOverStack B S hS 𝒳) : Bicategory.TwoCommSq A.map D.map :=
  AlgebraicStacks.twoFibreProductSquare B S hS A.map D.map

/-- **The product of two objects of `Spaces/𝒳`:** the 2-fibre product of their structure
1-morphisms, with the first projection followed by the first structure 1-morphism. -/
noncomputable def prodObj (A D : SpacesOverStack B S hS 𝒳) : SpacesOverStack B S hS 𝒳 where
  source := (prodSquare B S hS A D).pt
  map := (prodSquare B S hS A D).fst ≫ A.map
  representable :=
    isRepresentableByAlgebraicSpaces_comp B S hS
      (prodSquare B S hS A D).fst.hom A.map.hom
      (isRepresentableByAlgebraicSpaces_twoFibreProductFst B S hS 𝒳.val A.source.val
        D.source.val A.map.hom.hom D.map.hom.hom D.representable)
      A.representable

/-- The first projection of a binary product in `Spaces/𝒳`. Its comparison 2-morphism is the
identity: the structure 1-morphism of the product *is* the first projection followed by that of
the first factor. -/
noncomputable def prodFst (A D : SpacesOverStack B S hS 𝒳) : prodObj B S hS A D ⟶ A where
  map := (prodSquare B S hS A D).fst
  comm := 𝟙 _

/-- The second projection of a binary product in `Spaces/𝒳`. Its comparison 2-morphism is the
filler of the 2-fibre product square. -/
noncomputable def prodSnd (A D : SpacesOverStack B S hS 𝒳) : prodObj B S hS A D ⟶ D where
  map := (prodSquare B S hS A D).snd
  comm := (prodSquare B S hS A D).iso.hom

/-- The 2-commutative square over the cospan of structure 1-morphisms determined by a pair of
1-morphisms of `Spaces/𝒳` out of a common object: the filler is the composite of their two
comparison 2-morphisms. -/
noncomputable def coneOfPair {Z A D : SpacesOverStack B S hS 𝒳} (u : Z ⟶ A) (v : Z ⟶ D) :
    Bicategory.TwoCommSq A.map D.map where
  pt := Z.source
  fst := u.map
  snd := v.map
  iso := (asIso u.comm).symm ≪≫ asIso v.comm

/-- The pre-morphism of 2-commutative squares supplied by the universal property of the 2-fibre
product (Stacks 04T2) at the square of a pair of 1-morphisms. -/
noncomputable def prodPreHom {Z A D : SpacesOverStack B S hS 𝒳} (u : Z ⟶ A) (v : Z ⟶ D) :
    Bicategory.TwoCommSq.PreHom (coneOfPair B S hS u v) (prodSquare B S hS A D) :=
  Bicategory.twoFibreProductPreHom
    (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS A.map D.map)
    (coneOfPair B S hS u v)

/-- The 1-morphism of `Spaces/𝒳` into a binary product determined by a pair of 1-morphisms out
of a common object. -/
noncomputable def prodLift {Z A D : SpacesOverStack B S hS 𝒳} (u : Z ⟶ A) (v : Z ⟶ D) :
    Z ⟶ prodObj B S hS A D where
  map := (prodPreHom B S hS u v).hom
  comm := u.comm ≫ ((prodPreHom B S hS u v).isoFst.hom ▷ A.map) ≫ (α_ _ _ _).hom

/-- The first projection of `prodLift u v` is `u`. -/
noncomputable def prodLiftFstIso {Z A D : SpacesOverStack B S hS 𝒳} (u : Z ⟶ A) (v : Z ⟶ D) :
    prodLift B S hS u v ≫ prodFst B S hS A D ≅ u :=
  Hom₂.iso (prodPreHom B S hS u v).isoFst.symm
    (comp_whisker_cancel u.comm ((prodPreHom B S hS u v).isoFst.hom ▷ A.map)
      ((prodPreHom B S hS u v).isoFst.inv ▷ A.map)
      (α_ (prodPreHom B S hS u v).hom (prodSquare B S hS A D).fst A.map).hom
      (α_ (prodPreHom B S hS u v).hom (prodSquare B S hS A D).fst A.map).inv
      ((prodPreHom B S hS u v).hom ◁ 𝟙 ((prodSquare B S hS A D).fst ≫ A.map))
      (whiskerLeft_id _ _) (Iso.hom_inv_id _)
      (whiskerRightIso (prodPreHom B S hS u v).isoFst A.map).hom_inv_id)

/-- The second projection of `prodLift u v` is `v`. -/
noncomputable def prodLiftSndIso {Z A D : SpacesOverStack B S hS 𝒳} (u : Z ⟶ A) (v : Z ⟶ D) :
    prodLift B S hS u v ≫ prodSnd B S hS A D ≅ v :=
  Hom₂.iso (prodPreHom B S hS u v).isoSnd.symm
    (comp_whisker_cancel' u.comm (asIso u.comm).inv v.comm
      ((prodPreHom B S hS u v).isoSnd.hom ▷ D.map)
      ((prodPreHom B S hS u v).isoSnd.inv ▷ D.map)
      ((prodPreHom B S hS u v).isoFst.hom ▷ A.map)
      (α_ (prodPreHom B S hS u v).hom (prodSquare B S hS A D).fst A.map).hom
      ((prodPreHom B S hS u v).hom ◁ (prodSquare B S hS A D).iso.hom)
      (α_ (prodPreHom B S hS u v).hom (prodSquare B S hS A D).snd D.map).hom
      (α_ (prodPreHom B S hS u v).hom (prodSquare B S hS A D).snd D.map).inv
      (prodPreHom B S hS u v).compat (IsIso.hom_inv_id _) (Iso.hom_inv_id _)
      (whiskerRightIso (prodPreHom B S hS u v).isoSnd D.map).hom_inv_id)

/-- A 1-morphism into a binary product, read as a pre-morphism of 2-commutative squares over the
square determined by its two projections. -/
noncomputable def prodUniquePreHom {Z A D : SpacesOverStack B S hS 𝒳} {u : Z ⟶ A} {v : Z ⟶ D}
    (m : Z ⟶ prodObj B S hS A D) (e₁ : m ≫ prodFst B S hS A D ≅ u)
    (e₂ : m ≫ prodSnd B S hS A D ≅ v) :
    Bicategory.TwoCommSq.PreHom (coneOfPair B S hS u v) (prodSquare B S hS A D) where
  hom := m.map
  isoFst := (mapIso B S hS e₁).symm
  isoSnd := (mapIso B S hS e₂).symm
  compat :=
    comp_cancel_mid u.comm (asIso u.comm).inv v.comm ((mapIso B S hS e₂).inv ▷ D.map)
      (α_ m.map (prodSquare B S hS A D).snd D.map).hom m.comm
      (m.map ◁ (prodSquare B S hS A D).iso.hom) ((mapIso B S hS e₁).inv ▷ A.map)
      (α_ m.map (prodSquare B S hS A D).fst A.map).hom
      (comp_cancel_inv m.comm (m.map ◁ (prodSquare B S hS A D).iso.hom)
        (α_ m.map (prodSquare B S hS A D).snd D.map).inv
        (α_ m.map (prodSquare B S hS A D).snd D.map).hom
        ((mapIso B S hS e₂).hom ▷ D.map) ((mapIso B S hS e₂).inv ▷ D.map) v.comm
        e₂.hom.compat (whiskerRightIso (mapIso B S hS e₂) D.map).hom_inv_id (Iso.inv_hom_id _))
      ((comp_cancel_inv m.comm (m.map ◁ 𝟙 ((prodSquare B S hS A D).fst ≫ A.map))
        (α_ m.map (prodSquare B S hS A D).fst A.map).inv
        (α_ m.map (prodSquare B S hS A D).fst A.map).hom
        ((mapIso B S hS e₁).hom ▷ A.map) ((mapIso B S hS e₁).inv ▷ A.map) u.comm
        e₁.hom.compat (whiskerRightIso (mapIso B S hS e₁) A.map).hom_inv_id
        (Iso.inv_hom_id _)).trans
          ((congrArg (fun t => m.comm ≫ t) (whiskerLeft_id _ _)).trans (Category.comp_id _)))
      (IsIso.inv_hom_id u.comm)

/-- **A 1-morphism into a binary product is, up to isomorphism, the lift of its two
projections.** This is the uniqueness half of the universal property, read on isomorphism
classes; the mediating 2-isomorphism comes from terminality of the 2-fibre product square in the
category of 2-commutative diagrams over the cospan (Stacks 003O). -/
theorem homMk_eq_prodLift {Z A D : SpacesOverStack B S hS 𝒳} {u : Z ⟶ A} {v : Z ⟶ D}
    (m : Z ⟶ prodObj B S hS A D) (e₁ : m ≫ prodFst B S hS A D ≅ u)
    (e₂ : m ≫ prodSnd B S hS A D ≅ v) :
    IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳) m =
      IsoClassCategory.homMk (prodLift B S hS u v) := by
  obtain ⟨θ, hθ₁, _⟩ := Bicategory.twoFibreProductPreHom_rel
    (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS A.map D.map)
    (prodUniquePreHom B S hS m e₁ e₂) (prodPreHom B S hS u v)
  have h₁ : u.comm ≫ ((mapIso B S hS e₁).inv ▷ A.map) ≫
      (α_ m.map (prodSquare B S hS A D).fst A.map).hom = m.comm :=
    (comp_cancel_inv m.comm (m.map ◁ 𝟙 ((prodSquare B S hS A D).fst ≫ A.map))
      (α_ m.map (prodSquare B S hS A D).fst A.map).inv
      (α_ m.map (prodSquare B S hS A D).fst A.map).hom
      ((mapIso B S hS e₁).hom ▷ A.map) ((mapIso B S hS e₁).inv ▷ A.map) u.comm
      e₁.hom.compat (whiskerRightIso (mapIso B S hS e₁) A.map).hom_inv_id
      (Iso.inv_hom_id _)).trans
        ((congrArg (fun t => m.comm ≫ t) (whiskerLeft_id _ _)).trans (Category.comp_id _))
  exact IsoClassCategory.homMk_eq_of_iso (Hom₂.iso θ (comp_nat_subst u.comm
    ((mapIso B S hS e₁).inv ▷ A.map) ((θ.hom ▷ (prodSquare B S hS A D).fst) ▷ A.map)
    (α_ (prodPreHom B S hS u v).hom (prodSquare B S hS A D).fst A.map).hom
    (α_ m.map (prodSquare B S hS A D).fst A.map).hom
    (θ.hom ▷ ((prodSquare B S hS A D).fst ≫ A.map)) m.comm
    ((prodPreHom B S hS u v).isoFst.hom ▷ A.map)
    ((congrArg (fun t => t ▷ A.map) hθ₁.symm).trans (comp_whiskerRight _ _ _))
    (associator_naturality_left _ _ _) h₁))

/-- **The existence half of the universal property of a binary product**, on isomorphism
classes. -/
theorem exists_prodLift (A D : SpacesOverStack B S hS 𝒳) {Z : SpacesOverStack B S hS 𝒳}
    (f : IsoClassCategory.mk Z ⟶ IsoClassCategory.mk A)
    (g : IsoClassCategory.mk Z ⟶ IsoClassCategory.mk D) :
    ∃ m : IsoClassCategory.mk Z ⟶ IsoClassCategory.mk (prodObj B S hS A D),
      m ≫ IsoClassCategory.homMk (prodFst B S hS A D) = f ∧
        m ≫ IsoClassCategory.homMk (prodSnd B S hS A D) = g := by
  induction f using Quotient.inductionOn with
  | _ u =>
    induction g using Quotient.inductionOn with
    | _ v =>
      exact ⟨IsoClassCategory.homMk (prodLift B S hS u v),
        IsoClassCategory.homMk_eq_of_iso (prodLiftFstIso B S hS u v),
        IsoClassCategory.homMk_eq_of_iso (prodLiftSndIso B S hS u v)⟩

/-- **Two morphisms into a binary product which agree on both projections are equal.** -/
theorem prod_hom_ext {Z A D : SpacesOverStack B S hS 𝒳}
    (m m' : IsoClassCategory.mk Z ⟶ IsoClassCategory.mk (prodObj B S hS A D))
    (h₁ : m ≫ IsoClassCategory.homMk (prodFst B S hS A D) =
      m' ≫ IsoClassCategory.homMk (prodFst B S hS A D))
    (h₂ : m ≫ IsoClassCategory.homMk (prodSnd B S hS A D) =
      m' ≫ IsoClassCategory.homMk (prodSnd B S hS A D)) : m = m' := by
  induction m using Quotient.inductionOn with
  | _ k =>
    induction m' using Quotient.inductionOn with
    | _ k' =>
      exact (homMk_eq_prodLift B S hS k (Iso.refl _) (Iso.refl _)).trans
        (homMk_eq_prodLift B S hS k'
          (Classical.choice ((IsoClassCategory.homMk_eq_iff
            (k ≫ prodFst B S hS A D) (k' ≫ prodFst B S hS A D)).1 h₁)).symm
          (Classical.choice ((IsoClassCategory.homMk_eq_iff
            (k ≫ prodSnd B S hS A D) (k' ≫ prodSnd B S hS A D)).1 h₂)).symm).symm

/-- **The 2-fibre product is a binary product in the category of Stacks 04ZQ.** -/
noncomputable def prodIsLimit (A D : SpacesOverStack B S hS 𝒳) :
    IsLimit (BinaryFan.mk (IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳)
      (prodFst B S hS A D)) (IsoClassCategory.homMk (prodSnd B S hS A D))) :=
  BinaryFan.IsLimit.mk _ (fun f g => Classical.choose (exists_prodLift B S hS A D f g))
    (fun f g => (Classical.choose_spec (exists_prodLift B S hS A D f g)).1)
    (fun f g => (Classical.choose_spec (exists_prodLift B S hS A D f g)).2)
    (fun f g m hf hg => prod_hom_ext B S hS m _
      (hf.trans (Classical.choose_spec (exists_prodLift B S hS A D f g)).1.symm)
      (hg.trans (Classical.choose_spec (exists_prodLift B S hS A D f g)).2.symm))

/-- The terminal object of the category of Stacks 04ZQ, as a chosen limit cone. -/
noncomputable def terminalLimitCone (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    LimitCone (Functor.empty.{0} (IsoClassCategory (SpacesOverStack B S hS 𝒳))) where
  cone := asEmptyCone (IsoClassCategory.mk (terminalObj B S hS 𝒳))
  isLimit := isTerminal_terminalObj B S hS 𝒳

/-- A binary product of the category of Stacks 04ZQ, as a chosen limit cone. -/
noncomputable def prodLimitCone (A D : SpacesOverStack B S hS 𝒳) :
    LimitCone (pair (IsoClassCategory.mk A) (IsoClassCategory.mk D)) where
  cone := BinaryFan.mk (IsoClassCategory.homMk (C := SpacesOverStack B S hS 𝒳)
    (prodFst B S hS A D)) (IsoClassCategory.homMk (prodSnd B S hS A D))
  isLimit := prodIsLimit B S hS A D

/-- **The category of Stacks 04ZQ has finite products**, with `𝟙 𝒳` as terminal object and the
2-fibre product over `𝒳` as binary product. -/
noncomputable instance instCartesianMonoidalCategory (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    CartesianMonoidalCategory (IsoClassCategory (SpacesOverStack B S hS 𝒳)) :=
  CartesianMonoidalCategory.ofChosenFiniteProducts (terminalLimitCone B S hS 𝒳)
    (fun A D => prodLimitCone B S hS A D)

end AlgebraicGeometry.Stack.SpacesOverStack

end
