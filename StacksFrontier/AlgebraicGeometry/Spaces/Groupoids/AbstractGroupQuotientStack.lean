module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.ConstantSheafOfGroups

/-!
# The quotient of a sheaf by an abstract group (Stacks 0371)

Let `S` be a scheme of a big fppf site `B`, let `G` be an abstract group, let `X` be a
presheaf on the big fppf site of `S` — in the intended application an algebraic space over
`S` — and let `ρ : G →* Aut X` be an action of `G` on `X`. This file constructs the category
`[[X/G]]` over `(Sch/S)_fppf`:

* an object is a triple `(U, P, φ)` where `U` is an object of `(Sch/S)_fppf`, `P` is a
  torsor on `(Sch/U)_fppf` under the constant sheaf of groups with value `G`, and
  `φ : P → X` is a `G`-equivariant map of sheaves;
* a morphism `(U, P, φ) ⟶ (U', P', φ')` is a pair `(f, g)` with `f : U ⟶ U'` over `S` and
  `g : P → f^{-1}P'` a `G`-equivariant isomorphism satisfying `φ = φ' ∘ g`.

Forgetting a triple to its object `U` is a functor to `(Sch/S)_fppf`, which is how
`[[X/G]]` is regarded as a category over the big fppf site of `S`.

## Main definitions

* `AlgebraicGeometry.constantGroupSheaf`: the constant sheaf of groups with value `G` on the
  big fppf site of an object `U` of `(Sch/S)_fppf`, which is the localization at `U` of the
  big fppf site of `S`.
* `AlgebraicGeometry.AbstractGroupQuotientStack`: **Stacks 0371**, the objects of `[[X/G]]`.
* `AlgebraicGeometry.AbstractGroupQuotientStack.Hom`: **Stacks 0371**, its morphisms, and
  `AlgebraicGeometry.AbstractGroupQuotientStack.instCategory`, the category they form.
* `AlgebraicGeometry.AbstractGroupQuotientStack.Total`, with its restriction maps
  `totalMap`, its action `totalSmul` and its map `totalToTarget` to `X`: the sheaf on
  `(Sch/S)_fppf` over `U` attached to the torsor of an object.
* `AlgebraicGeometry.AbstractGroupQuotientStack.projection`: the functor
  `[[X/G]] ⥤ (Sch/S)_fppf`.

## Implementation notes

The constant sheaf of groups is `CategoryTheory.constantSheafOfGroups`, the sheafification
of the constant presheaf in `GrpCat`, so the group structure on its sections comes for free;
sheafifiability in `GrpCat.{w}` is a typeclass hypothesis, exactly as it is in Mathlib, which
keeps the universe of the abstract group independent of the universe of the site. On the
localized site `(Sch/U)_fppf` the constant sheaf is taken to be the restriction of the
constant sheaf on `(Sch/S)_fppf`, which identifies the sections of the two by definition, so
that one and the same sheaf of groups acts on the torsors of all fibres of `[[X/G]]`.

The torsor of an object and its torsor condition are literally `PseudoTorsor` and
`PseudoTorsor.IsTorsor` of Stacks 03AH on `(Sch/U)_fppf`.

A morphism `g : P → f^{-1}P'` is recorded on the *total spaces*
`Total A V = Σ a : V ⟶ U, P(V, a)`: this is the sheaf on `(Sch/S)_fppf` corresponding to `P`
under the equivalence between sheaves on `(Sch/U)_fppf` and sheaves on `(Sch/S)_fppf` over
`U`, and it is the presentation the source itself uses for the quotient stack of a group
algebraic space in Stacks 04WL, where a morphism is a map `P → P'` over `f` inducing an
isomorphism `P ≅ U ×_{U'} P'`. Its advantage here is that the type of `g` does not depend on
`f`, so composition of morphisms is strictly associative and no coherence isomorphisms for
the pullback functors `f^{-1}` are needed. Accordingly, that `g` is an isomorphism onto
`f^{-1}P'` is recorded as `Set.BijOn` of `g` from the fibre of `Total A` over `a` to the
fibre of `Total A'` over `a ≫ f`.

Equivariance of `g` is stated for the constant sheaf of groups; equivariance of `φ` is
stated for the abstract group `G` acting through
`CategoryTheory.constantSheafOfGroupsUnit`, since only `G` itself acts on `X`. The two
notions of equivariance for maps of sheaves agree, because the constant sheaf is generated
locally by the constant presheaf.

The category is defined without assuming that `X` is an algebraic space, and for a presheaf
of values in an arbitrary universe: only the presheaf `X` and the action `ρ` enter the
construction. This generalizes the source, whose standing hypothesis — that `X` is an
algebraic space over `S` in the sense of
`AlgebraicGeometry.IsAlgebraicSpace` — is what the propositions built on this definition
add.

## References

* [Stacks Project, Tag 0371](https://stacks.math.columbia.edu/tag/0371)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry

universe t z w u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (G : Type w) [Group G]
  [HasWeakSheafify (BigFppfOver.topology B S hS) GrpCat.{w}]

/-- The constant sheaf of groups with value `G` on the big fppf site `(Sch/U)_fppf` of an
object `U` of `(Sch/S)_fppf`, which is the localization at `U` of the big fppf site of
`S`. -/
abbrev constantGroupSheaf (U : BigFppfOver B S hS) :
    SheafOfGroups.{w} (C := Over U) ((BigFppfOver.topology B S hS).over U) :=
  constantSheafOfGroupsOver (BigFppfOver.topology B S hS) G U

variable (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type z) (ρ : G →* Aut X)

/-- **Stacks 0371.** An object of the quotient `[[X/G]]` of a sheaf `X` by an abstract group
`G`: an object `U` of `(Sch/S)_fppf`, a torsor on `(Sch/U)_fppf` under the constant sheaf of
groups with value `G`, and a `G`-equivariant map of sheaves from it to `X`. -/
@[stacks 0371 "the objects of [[X/G]]"]
structure AbstractGroupQuotientStack where
  /-- The object of `(Sch/S)_fppf` over which the triple lives. -/
  base : BigFppfOver B S hS
  /-- The sheaf on `(Sch/U)_fppf` with its action of the constant sheaf of groups `G`. -/
  torsor : PseudoTorsor.{t} (constantGroupSheaf B S hS G base)
  /-- The action turns the sheaf into a torsor, that is, it is locally nonempty. -/
  isTorsor : torsor.IsTorsor
  /-- The map `φ : P → X`, given on sections over `(Sch/U)_fppf`. -/
  toTarget : ∀ W : (Over base)ᵒᵖ, torsor.presheaf.obj W → X.obj (op W.unop.left)
  /-- `φ` is a map of sheaves, that is, it is compatible with the restriction maps. -/
  toTarget_naturality : ∀ {W W' : (Over base)ᵒᵖ} (h : W ⟶ W') (s : torsor.presheaf.obj W),
    toTarget W' (torsor.presheaf.map h s) =
      X.map ((Over.forget base).map h.unop).op (toTarget W s)
  /-- `φ` is `G`-equivariant: `G` acts on the torsor through the constant sheaf of groups
  and on `X` through `ρ`. -/
  toTarget_equivariant : ∀ (W : (Over base)ᵒᵖ) (g : G) (s : torsor.presheaf.obj W),
    toTarget W (torsor.act W (constantSheafOfGroupsUnit
        (BigFppfOver.topology B S hS) G (op W.unop.left) g) s) =
      (ρ g).hom.app (op W.unop.left) (toTarget W s)

namespace AbstractGroupQuotientStack

variable {B S hS G X ρ}

/-- The total space of the torsor of an object of `[[X/G]]`: the sheaf on `(Sch/S)_fppf`
whose sections over `V` are the pairs of a morphism `a : V ⟶ U` and a section of the torsor
over `(V, a)`. -/
def Total (A : AbstractGroupQuotientStack B S hS G X ρ)
    (V : (BigFppfOver B S hS)ᵒᵖ) :=
  Σ a : V.unop ⟶ A.base, A.torsor.presheaf.obj (op (Over.mk a))

/-- The restriction maps of the total space of the torsor of an object of `[[X/G]]`. -/
def totalMap (A : AbstractGroupQuotientStack B S hS G X ρ)
    {V W : (BigFppfOver B S hS)ᵒᵖ} (h : V ⟶ W) (p : A.Total V) : A.Total W :=
  ⟨h.unop ≫ p.1, A.torsor.presheaf.map
    (Over.homMk h.unop : Over.mk (h.unop ≫ p.1) ⟶ Over.mk p.1).op p.2⟩

/-- The action of the constant sheaf of groups with value `G` on the total space of the
torsor of an object of `[[X/G]]`. -/
def totalSmul (A : AbstractGroupQuotientStack B S hS G X ρ)
    {V : (BigFppfOver B S hS)ᵒᵖ}
    (γ : (constantSheafOfGroups (BigFppfOver.topology B S hS) G).presheaf.obj V)
    (p : A.Total V) : A.Total V :=
  ⟨p.1, A.torsor.act (op (Over.mk p.1)) γ p.2⟩

/-- The equivariant map to `X` of an object of `[[X/G]]`, read on the total space of its
torsor. -/
def totalToTarget (A : AbstractGroupQuotientStack B S hS G X ρ)
    (V : (BigFppfOver B S hS)ᵒᵖ) (p : A.Total V) : X.obj V :=
  A.toTarget (op (Over.mk p.1)) p.2

/-- **Stacks 0371.** A morphism `(U, P, φ) ⟶ (U', P', φ')` of the quotient `[[X/G]]`: a
morphism `f : U ⟶ U'` of `(Sch/S)_fppf` together with a `G`-equivariant isomorphism
`g : P → f^{-1}P'` of torsors under the constant sheaf of groups with value `G`, compatible
with `φ` and `φ'`. The isomorphism is recorded on total spaces: `g` is a map of sheaves on
`(Sch/S)_fppf` over `f` restricting to a bijection from the fibre of `P` over each
`a : V ⟶ U` to the fibre of `P'` over `a ≫ f`. -/
@[stacks 0371 "the morphisms of [[X/G]]"]
structure Hom (A A' : AbstractGroupQuotientStack B S hS G X ρ) where
  /-- The morphism `f : U ⟶ U'` of `(Sch/S)_fppf`. -/
  base : A.base ⟶ A'.base
  /-- The morphism `g`, read on total spaces. -/
  map : ∀ V : (BigFppfOver B S hS)ᵒᵖ, A.Total V → A'.Total V
  /-- `g` is a map of sheaves, that is, it is compatible with the restriction maps. -/
  map_naturality : ∀ {V W : (BigFppfOver B S hS)ᵒᵖ} (h : V ⟶ W) (p : A.Total V),
    map W (totalMap A h p) = totalMap A' h (map V p)
  /-- `g` is equivariant for the constant sheaf of groups with value `G`. -/
  map_equivariant : ∀ (V : (BigFppfOver B S hS)ᵒᵖ)
    (γ : (constantSheafOfGroups (BigFppfOver.topology B S hS) G).presheaf.obj V)
    (p : A.Total V), map V (totalSmul A γ p) = totalSmul A' γ (map V p)
  /-- `g` is an isomorphism onto `f^{-1}P'`: over every `a : V ⟶ U` it is a bijection from
  the sections of `P` over `(V, a)` to the sections of `P'` over `(V, a ≫ f)`. -/
  bijOn_map : ∀ (V : (BigFppfOver B S hS)ᵒᵖ) (a : V.unop ⟶ A.base),
    Set.BijOn (map V) {p : A.Total V | p.1 = a} {q : A'.Total V | q.1 = a ≫ base}
  /-- `φ = φ' ∘ g`. -/
  totalToTarget_comp : ∀ (V : (BigFppfOver B S hS)ᵒᵖ) (p : A.Total V),
    A'.totalToTarget V (map V p) = A.totalToTarget V p

/-- Two morphisms of `[[X/G]]` with the same `f` and the same `g` are equal. -/
@[ext]
theorem Hom.ext {A A' : AbstractGroupQuotientStack B S hS G X ρ} {m m' : Hom A A'}
    (hbase : m.base = m'.base) (hmap : m.map = m'.map) : m = m' := by
  cases m; cases m'; subst hbase; subst hmap; rfl

/-- The morphism `g` of a morphism of `[[X/G]]` lies over `f`: it sends a section of `P`
over `a` to a section of `P'` over `a ≫ f`. -/
theorem Hom.fst_map {A A' : AbstractGroupQuotientStack B S hS G X ρ} (m : Hom A A')
    {V : (BigFppfOver B S hS)ᵒᵖ} (p : A.Total V) : (m.map V p).1 = p.1 ≫ m.base :=
  (m.bijOn_map V p.1).mapsTo rfl

/-- The identity morphism of an object of `[[X/G]]`. -/
def Hom.id (A : AbstractGroupQuotientStack B S hS G X ρ) : Hom A A where
  base := 𝟙 A.base
  map := fun _ p => p
  map_naturality := fun _ _ => rfl
  map_equivariant := fun _ _ _ => rfl
  bijOn_map := fun _ a => by
    simp only [Category.comp_id]
    exact Set.bijOn_id _
  totalToTarget_comp := fun _ _ => rfl

/-- The composition of two morphisms of `[[X/G]]`. -/
def Hom.comp {A A' A'' : AbstractGroupQuotientStack B S hS G X ρ} (m : Hom A A')
    (m' : Hom A' A'') : Hom A A'' where
  base := m.base ≫ m'.base
  map := fun V => m'.map V ∘ m.map V
  map_naturality := fun h p => by
    simp only [Function.comp_apply]
    rw [m.map_naturality, m'.map_naturality]
  map_equivariant := fun V γ p => by
    simp only [Function.comp_apply]
    rw [m.map_equivariant, m'.map_equivariant]
  bijOn_map := fun V a => by
    rw [← Category.assoc]
    exact (m'.bijOn_map V (a ≫ m.base)).comp (m.bijOn_map V a)
  totalToTarget_comp := fun V p => by
    simp only [Function.comp_apply]
    rw [m'.totalToTarget_comp, m.totalToTarget_comp]

/-- **Stacks 0371.** The quotient `[[X/G]]` of a sheaf `X` by an abstract group `G` is a
category: morphisms compose by composing `f` and `g`. -/
@[stacks 0371 "the category [[X/G]]"]
instance instCategory : Category (AbstractGroupQuotientStack B S hS G X ρ) where
  Hom A A' := Hom A A'
  id A := Hom.id A
  comp m m' := Hom.comp m m'
  id_comp _ := Hom.ext (Category.id_comp _) rfl
  comp_id _ := Hom.ext (Category.comp_id _) rfl
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _) rfl

/-- **Stacks 0371.** The functor `[[X/G]] ⥤ (Sch/S)_fppf` sending a triple `(U, P, φ)` to
`U`, which is how `[[X/G]]` is regarded as a category over the big fppf site of `S`. -/
@[stacks 0371 "the functor to the big fppf site"]
def projection :
    AbstractGroupQuotientStack B S hS G X ρ ⥤ BigFppfOver B S hS where
  obj A := A.base
  map m := Hom.base m

end AbstractGroupQuotientStack

end AlgebraicGeometry

end
