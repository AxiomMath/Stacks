module

public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
public import StacksCore.Tactic.StacksAttribute

/-! # Dotted arrows across a 2-cartesian square

Stacks 0H1A (Lemma 4.44.2): in a $(2,1)$-category, split a $2$-commutative rectangle into a
left square with witness `γ'` and a right square with witness `φ`, and assume the right square
is $2$-cartesian (Tag 003O).  Then the category of dotted arrows (Tag 0H18) of the left square
is equivalent to that of the outer rectangle, the equivalence sending a dotted $1$-morphism `a`
to `a ≫ q`, where `q` is the leg of the $2$-cartesian square.

A $(2,1)$-category is modelled as a `Bicategory` `B` together with the hypothesis `hgpd`,
carried on the statements that need it, that every $2$-morphism of `B` is invertible; this is
what makes the $2$-morphisms `θ` between dotted arrows automatically isomorphisms.

The dotted arrows of this file carry their `γ`, `α` and `β` as $2$-**isomorphisms**, and are
named `IsoDottedArrow` to distinguish them from `CategoryTheory.DottedArrow` of
`StacksFrontier/CategoryTheory/DottedArrows/Defs.lean` (Tag 0CLA), whose data is bare
$2$-morphisms; `StacksFrontier/Exercises/NonExercises/DottedArrowsBaseChange.lean` supplies the
equivalence between the two forms and transports the theorem below to Tag 0CLE.

Composition is diagrammatic, so the classical $g \circ f$ is `f ≫ g` and the classical vertical
composite $\tau \circ \sigma$ is `σ ≫ τ`; horizontal whiskerings are `f ◁ η` and `η ▷ h`, and
associators are written out even though they are identities on underlying $1$-morphisms, to
keep the whiskered composites well-typed.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Bicategory

namespace CategoryTheory.DottedArrowBaseChange

variable {B : Type*} [Bicategory B]

/-! ### Definition 1 (Category of dotted arrows; Tag 0H18 / Definition 4.44.1)

The classical $2$-commutative square $x : S \to X$, $j : S \to T$, $f : X \to Y$,
$y : T \to Y$ with witness $\gamma : y \circ j \to f \circ x$ is encoded by Lean morphisms
`x : S ⟶ X`, `j : S ⟶ T`, `f : X ⟶ Y`, `y : T ⟶ Y` and a $2$-isomorphism
`γ : (j ≫ y) ≅ (x ≫ f)`.  Given such a square, a *dotted arrow* is a triple
$(a, \alpha, \beta)$ with $a : T \to X$, $\alpha : a \circ j \to x$ and
$\beta : y \to f \circ a$ ($2$-isomorphisms), subject to the compatibility
$\gamma = (\mathrm{id}_f \star \alpha) \circ (\beta \star \mathrm{id}_j)$.

In Mathlib conventions: $a \circ j$ is `j ≫ a`, $f \circ a$ is `a ≫ f`,
$\beta \star \mathrm{id}_j$ is the left whiskering `j ◁ β.hom` and
$\mathrm{id}_f \star \alpha$ is the right whiskering `α.hom ▷ f` (after re-associating).
The classical composite $(\mathrm{id}_f \star \alpha) \circ (\beta \star \mathrm{id}_j)$
(apply $\beta \star \mathrm{id}_j$ first) becomes `(j ◁ β.hom) ≫ (α_ ...).inv ≫ (α.hom ▷ f)`.
-/

/-- A *dotted arrow* for the $2$-commutative square with witness `γ : (j ≫ y) ≅ (x ≫ f)`. -/
structure IsoDottedArrow {S T X Y : B} (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y) (y : T ⟶ Y)
    (γ : (j ≫ y) ≅ (x ≫ f)) where
  /-- The dotted $1$-morphism $a : T \to X$. -/
  a : T ⟶ X
  /-- The $2$-isomorphism $\alpha : a \circ j \to x$. -/
  α : (j ≫ a) ≅ x
  /-- The $2$-isomorphism $\beta : y \to f \circ a$. -/
  β : y ≅ (a ≫ f)
  /-- Compatibility: $\gamma = (\mathrm{id}_f \star \alpha) \circ (\beta \star \mathrm{id}_j)$. -/
  compat : γ.hom = (j ◁ β.hom) ≫ (α_ j a f).inv ≫ (α.hom ▷ f)

variable {S T X Y : B} {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y} {y : T ⟶ Y}
  {γ : (j ≫ y) ≅ (x ≫ f)}

/-- A morphism of dotted arrows $(a, \alpha, \beta) \to (a', \alpha', \beta')$ is a
$2$-morphism $\theta : a \to a'$ with $\alpha = \alpha' \circ (\theta \star \mathrm{id}_j)$
and $\beta' = (\mathrm{id}_f \star \theta) \circ \beta$.

In the source, since $\mathcal{C}$ is a $(2,1)$-category, every such $\theta$ is
automatically invertible; this is reflected by the standing groupoidal hypothesis carried
on the main theorem (see the file header). -/
structure IsoDottedArrowHom (D₁ D₂ : IsoDottedArrow x j f y γ) where
  /-- The underlying $2$-morphism $\theta : a \to a'$. -/
  θ : D₁.a ⟶ D₂.a
  /-- $\alpha = \alpha' \circ (\theta \star \mathrm{id}_j)$. -/
  compat_α : D₁.α.hom = (j ◁ θ) ≫ D₂.α.hom
  /-- $\beta' = (\mathrm{id}_f \star \theta) \circ \beta$. -/
  compat_β : D₂.β.hom = D₁.β.hom ≫ (θ ▷ f)

namespace IsoDottedArrowHom

/-- Morphisms of dotted arrows are determined by their underlying $2$-morphisms. -/
@[ext] lemma ext {D₁ D₂ : IsoDottedArrow x j f y γ} {h₁ h₂ : IsoDottedArrowHom D₁ D₂}
    (w : h₁.θ = h₂.θ) : h₁ = h₂ := by
  cases h₁; cases h₂; simp_all

/-- The identity morphism of dotted arrows. -/
def id (D : IsoDottedArrow x j f y γ) : IsoDottedArrowHom D D where
  θ := 𝟙 D.a
  compat_α := by simp
  compat_β := by simp

/-- Composition of morphisms of dotted arrows (vertical composition of the underlying
$2$-morphisms). -/
def comp {D₁ D₂ D₃ : IsoDottedArrow x j f y γ}
    (h₁ : IsoDottedArrowHom D₁ D₂) (h₂ : IsoDottedArrowHom D₂ D₃) : IsoDottedArrowHom D₁ D₃ where
  θ := h₁.θ ≫ h₂.θ
  compat_α := by
    rw [h₁.compat_α, h₂.compat_α, Bicategory.whiskerLeft_comp, Category.assoc]
  compat_β := by
    rw [h₂.compat_β, h₁.compat_β, Bicategory.comp_whiskerRight, Category.assoc]

end IsoDottedArrowHom

/-- The category of dotted arrows for a fixed $2$-commutative square and witness `γ`. -/
instance isoDottedArrowCategory : Category (IsoDottedArrow x j f y γ) where
  Hom := IsoDottedArrowHom
  id := IsoDottedArrowHom.id
  comp := IsoDottedArrowHom.comp
  id_comp _ := IsoDottedArrowHom.ext (by simp [IsoDottedArrowHom.comp, IsoDottedArrowHom.id])
  comp_id _ := IsoDottedArrowHom.ext (by simp [IsoDottedArrowHom.comp, IsoDottedArrowHom.id])
  assoc _ _ _ := IsoDottedArrowHom.ext (by simp [IsoDottedArrowHom.comp])

/-- The underlying $2$-morphism of an identity of dotted arrows is an identity. -/
@[simp] lemma IsoDottedArrowHom.id_θ (D : IsoDottedArrow x j f y γ) : (𝟙 D : D ⟶ D).θ = 𝟙 D.a := rfl

/-- The underlying $2$-morphism of a composite of dotted arrows is the vertical composite. -/
@[simp] lemma IsoDottedArrowHom.comp_θ {D₁ D₂ D₃ : IsoDottedArrow x j f y γ} (h₁ : D₁ ⟶ D₂)
    (h₂ : D₂ ⟶ D₃) : (h₁ ≫ h₂).θ = h₁.θ ≫ h₂.θ := rfl

/-- A $2$-isomorphism of the underlying dotted $1$-morphisms that is compatible with the
`α`- and `β`-data is an isomorphism of dotted arrows. -/
def IsoDottedArrow.isoOfIso {D₁ D₂ : IsoDottedArrow x j f y γ} (e : D₁.a ≅ D₂.a)
    (hα : D₁.α.hom = (j ◁ e.hom) ≫ D₂.α.hom)
    (hβ : D₂.β.hom = D₁.β.hom ≫ (e.hom ▷ f)) : D₁ ≅ D₂ where
  hom := { θ := e.hom, compat_α := hα, compat_β := hβ }
  inv :=
    { θ := e.inv
      compat_α := by
        rw [hα, ← Category.assoc, ← Bicategory.whiskerLeft_comp, Iso.inv_hom_id,
          Bicategory.whiskerLeft_id, Category.id_comp]
      compat_β := by
        rw [hβ, Category.assoc, ← Bicategory.comp_whiskerRight, Iso.hom_inv_id,
          Bicategory.id_whiskerRight]
        exact (Category.comp_id _).symm }
  hom_inv_id := IsoDottedArrowHom.ext (by simp)
  inv_hom_id := IsoDottedArrowHom.ext (by simp)

/-! ### Definition 2 ($2$-cartesian square / $2$-fibre product; Tag 003O)

For $1$-morphisms $f : X \to Y$ and $g : Y' \to Y$, a $2$-commutative square
$$
  X' \xrightarrow{q} X,\quad X' \xrightarrow{p} Y',\quad X \xrightarrow{f} Y,\quad
  Y' \xrightarrow{g} Y
$$
with witness $\phi : g \circ p \to f \circ q$ (in Lean `φ : (p ≫ g) ≅ (q ≫ f)`) is
$2$-cartesian if it satisfies the universal property of the $2$-fibre product:

for every test object `W` with $1$-morphisms $a : W \to X$, $b : W \to Y'$ and a
$2$-isomorphism $\psi : g \circ b \to f \circ a$, there is a $1$-morphism $W \to X'$
together with compatible $2$-isomorphisms, unique up to unique $2$-isomorphism.

We package the test data $(a, b, \psi)$ as a `TwoFiberCone`, and a *compatible*
factorization of such a cone through `(q, p, φ)` as a `TwoFiberFactorization`. The
`compat` field of the latter is precisely the requirement that the factorization is a
morphism of $2$-commutative cones (it is compatible with `φ` and `ψ`). The universal
property `IsTwoCartesian` then asserts (i) every cone has a compatible factorization, and
(ii) any two compatible factorizations are joined by a *unique* $2$-isomorphism that is
itself compatible with the factorization data. -/

/-- A test cone over $(f, g)$ with apex `W`: $1$-morphisms `a : W ⟶ X`, `b : W ⟶ Y'`
together with a $2$-isomorphism $\psi : g \circ b \to f \circ a$ (`(b ≫ g) ≅ (a ≫ f)`). -/
structure TwoFiberCone {X Y' Y : B} (f : X ⟶ Y) (g : Y' ⟶ Y) (W : B) where
  /-- The leg $a : W \to X$. -/
  a : W ⟶ X
  /-- The leg $b : W \to Y'$. -/
  b : W ⟶ Y'
  /-- The $2$-isomorphism witnessing $2$-commutativity, $\psi : g \circ b \to f \circ a$. -/
  ψ : (b ≫ g) ≅ (a ≫ f)

/-- A *compatible factorization* of a test cone `c` through the cone `(q, p, φ)`: a
$1$-morphism `h : W ⟶ X'` together with factorization $2$-isomorphisms
`eq : h ≫ q ≅ c.a` and `ep : h ≫ p ≅ c.b`, such that the resulting cone diagram is
compatible with `φ` and `c.ψ`. The `compat` field says, after re-association,
$(\mathrm{ep} \star \mathrm{id}_g) \circ \psi^{-1} = \ldots$, i.e. that `h` (with `eq`, `ep`)
is a morphism of $2$-commutative diagrams from `c` to the universal cone `(q, p, φ)`. -/
structure TwoFiberFactorization {X' X Y' Y : B} (q : X' ⟶ X) (p : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (φ : (p ≫ g) ≅ (q ≫ f))
    {W : B} (c : TwoFiberCone f g W) where
  /-- The induced $1$-morphism `W ⟶ X'`. -/
  h : W ⟶ X'
  /-- Factorization through `q`: $h \circ q \cong a$. -/
  eq : (h ≫ q) ≅ c.a
  /-- Factorization through `p`: $h \circ p \cong b$. -/
  ep : (h ≫ p) ≅ c.b
  /-- Compatibility of the factorization with `φ` and `c.ψ`. -/
  compat :
    (ep.hom ▷ g) ≫ c.ψ.hom
      = (α_ h p g).hom ≫ (h ◁ φ.hom) ≫ (α_ h q f).inv ≫ (eq.hom ▷ f)

/-- The universal property of a $2$-cartesian square (a $2$-fibre product) for the square
with legs `q : X' ⟶ X`, `p : X' ⟶ Y'`, sides `f`, `g`, and witness
$\phi : g \circ p \to f \circ q$.

It consists of:
* `fac`: every test cone `c` admits a compatible factorization `TwoFiberFactorization`;
* `uniq`: any two compatible factorizations `F₁ F₂` of the *same* cone `c` are joined by a
  **unique** $2$-isomorphism `ρ : F₁.h ≅ F₂.h` compatible with the factorization
  $2$-isomorphisms (`ρ ▷ q` intertwines `F₁.eq` and `F₂.eq`, and `ρ ▷ p` intertwines
  `F₁.ep` and `F₂.ep`).

This is the universal property of a final object in the $2$-category of $2$-commutative
diagrams over `f` and `g` (Tag 003O): existence and uniqueness are both stated relative to
*compatible cones*, as required. -/
structure IsTwoCartesian {X' X Y' Y : B} (q : X' ⟶ X) (p : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (φ : (p ≫ g) ≅ (q ≫ f)) where
  /-- Existence: every test cone admits a compatible factorization. -/
  fac : ∀ {W : B} (c : TwoFiberCone f g W), TwoFiberFactorization q p f g φ c
  /-- Uniqueness: any two compatible factorizations of the same cone are connected by a
  unique $2$-isomorphism compatible with the factorization data. -/
  uniq : ∀ {W : B} {c : TwoFiberCone f g W}
    (F₁ F₂ : TwoFiberFactorization q p f g φ c),
    ∃! ρ : F₁.h ≅ F₂.h,
      (ρ.hom ▷ q) ≫ F₂.eq.hom = F₁.eq.hom ∧
      (ρ.hom ▷ p) ≫ F₂.ep.hom = F₁.ep.hom

/-- The test cone induced by a $1$-morphism `v : W ⟶ X'` into the vertex of the square
`(q, p, φ)`: its legs are `v ≫ q` and `v ≫ p`, and its witness is assembled from `φ`. -/
@[implicit_reducible]
noncomputable def inducedTwoFiberCone {X' X Y' Y : B} (q : X' ⟶ X) (p : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (φ : (p ≫ g) ≅ (q ≫ f)) {W : B} (v : W ⟶ X') :
    TwoFiberCone f g W where
  a := v ≫ q
  b := v ≫ p
  ψ := (α_ v p g) ≪≫ whiskerLeftIso v φ ≪≫ (α_ v q f).symm

/-- `v` factors the cone it induces, through identity $2$-isomorphisms. -/
@[implicit_reducible]
noncomputable def selfTwoFiberFactorization {X' X Y' Y : B} (q : X' ⟶ X) (p : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (φ : (p ≫ g) ≅ (q ≫ f)) {W : B} (v : W ⟶ X') :
    TwoFiberFactorization q p f g φ (inducedTwoFiberCone q p f g φ v) where
  h := v
  eq := Iso.refl _
  ep := Iso.refl _
  compat := by
    dsimp only [inducedTwoFiberCone]
    simp only [Iso.refl_hom, Bicategory.id_whiskerRight, Category.id_comp,
      Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom]
    bicategory

/-- An invertible $2$-morphism `μ : u ⟶ v` exhibits `u` as a factorization of the cone induced
by `v`, the factorization data being the whiskerings of `μ` by `q` and by `p`. -/
@[implicit_reducible]
noncomputable def twoFiberFactorizationOfWhiskerIso {X' X Y' Y : B} (q : X' ⟶ X) (p : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (φ : (p ≫ g) ≅ (q ≫ f)) {W : B} {u v : W ⟶ X'} (μ : u ⟶ v)
    [IsIso (μ ▷ q)] [IsIso (μ ▷ p)] :
    TwoFiberFactorization q p f g φ (inducedTwoFiberCone q p f g φ v) where
  h := u
  eq := asIso (μ ▷ q)
  ep := asIso (μ ▷ p)
  compat := by
    dsimp only [inducedTwoFiberCone]
    simp only [asIso_hom, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom]
    rw [← Category.assoc (μ ▷ p ▷ g), Bicategory.associator_naturality_left μ p g]
    simp only [Category.assoc]
    congr 1
    rw [← reassoc_of% (whisker_exchange μ φ.hom),
      Bicategory.associator_inv_naturality_left μ q f]

/-! ### The witness `γ` for the outer rectangle

Given the left-square witness $\gamma' : y' \circ j \to p \circ x'$ (`(j ≫ y') ≅ (x' ≫ p)`)
and the right-square witness $\phi : g \circ p \to f \circ q$, with $x = q \circ x'$
(`x' ≫ q`) and $y = g \circ y'$ (`y' ≫ g`), the outer witness
$\gamma = (\phi \star \mathrm{id}_{x'}) \circ (\mathrm{id}_g \star \gamma')$
is the $2$-isomorphism `(j ≫ (y' ≫ g)) ≅ ((x' ≫ q) ≫ f)` defined below. -/

/-- The outer witness $\gamma$, assembled as a composite of $2$-isomorphisms. -/
noncomputable def outerGamma {S T X X' Y Y' : B}
    {j : S ⟶ T} {x' : S ⟶ X'} {q : X' ⟶ X} {p : X' ⟶ Y'} {f : X ⟶ Y}
    {y' : T ⟶ Y'} {g : Y' ⟶ Y}
    (φ : (p ≫ g) ≅ (q ≫ f)) (γ' : (j ≫ y') ≅ (x' ≫ p)) :
    (j ≫ (y' ≫ g)) ≅ ((x' ≫ q) ≫ f) :=
  (α_ j y' g).symm ≪≫ (whiskerRightIso γ' g) ≪≫ (α_ x' p g) ≪≫
    (whiskerLeftIso x' φ) ≪≫ (α_ x' q f).symm

/-! ### The functor `F : D' → D`

The Stacks-Project proof exhibits the explicit functor
`(a, α, β) ↦ (q ∘ a, id_q ⋆ α, (φ ⋆ id_a) ∘ (id_g ⋆ β))`, `θ ↦ id_q ⋆ θ`, and shows it is an
equivalence using the universal property of the 2-cartesian right square. In Mathlib's
diagrammatic convention the object map sends `a : T ⟶ X'` to `a ≫ q : T ⟶ X`, the
`α`-component `(j ≫ a) ≅ x'` to `(j ≫ (a ≫ q)) ≅ (x' ≫ q)` (right-whisker by `q`), and the
`β`-component `y' ≅ (a ≫ p)` to `(y' ≫ g) ≅ ((a ≫ q) ≫ f)` (right-whisker by `g`, then apply
`φ` left-whiskered by `a`); the morphism map sends `θ : a ⟶ a'` to `θ ▷ q`. -/

variable {S T X X' Y Y' : B}

/-- Object map of the functor `F : D' → D`: `(a, α, β) ↦ (a ≫ q, …)`. The `compat` field relates
`(outerGamma φ γ').hom` to the image's `α`,`β`; it is not pure coherence (it genuinely uses
`D.compat`, which ties `γ'.hom` to `D.α`,`D.β`), but reduces to coherence once `D.compat` is
rewritten in. -/
@[implicit_reducible]
noncomputable def dottedObjMap
    {j : S ⟶ T} {x' : S ⟶ X'} {q : X' ⟶ X} {p : X' ⟶ Y'} {f : X ⟶ Y}
    {y' : T ⟶ Y'} {g : Y' ⟶ Y}
    (φ : (p ≫ g) ≅ (q ≫ f)) (γ' : (j ≫ y') ≅ (x' ≫ p))
    (D : IsoDottedArrow x' j p y' γ') :
    IsoDottedArrow (x' ≫ q) j f (y' ≫ g) (outerGamma φ γ') where
  a := D.a ≫ q
  α := (α_ j D.a q).symm ≪≫ whiskerRightIso D.α q
  β := whiskerRightIso D.β g ≪≫ (α_ D.a p g) ≪≫ whiskerLeftIso D.a φ ≪≫ (α_ D.a q f).symm
  compat := by
    simp only [outerGamma, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, whiskerLeftIso_hom,
      Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight, Category.assoc]
    rw [D.compat]
    simp only [Bicategory.comp_whiskerRight, Category.assoc]
    rw [Bicategory.associator_naturality_left_assoc, ← whisker_exchange_assoc]
    bicategory

/-- The dotted $1$-morphism of `dottedObjMap φ γ' D` is `D.a ≫ q`. -/
@[simp] lemma dottedObjMap_a
    {j : S ⟶ T} {x' : S ⟶ X'} {q : X' ⟶ X} {p : X' ⟶ Y'} {f : X ⟶ Y}
    {y' : T ⟶ Y'} {g : Y' ⟶ Y}
    (φ : (p ≫ g) ≅ (q ≫ f)) (γ' : (j ≫ y') ≅ (x' ≫ p)) (D : IsoDottedArrow x' j p y' γ') :
    (dottedObjMap φ γ' D).a = D.a ≫ q := rfl

/-- The `α`-component of `dottedObjMap φ γ' D` is `D.α` whiskered by `q`. -/
lemma dottedObjMap_α_hom
    {j : S ⟶ T} {x' : S ⟶ X'} {q : X' ⟶ X} {p : X' ⟶ Y'} {f : X ⟶ Y}
    {y' : T ⟶ Y'} {g : Y' ⟶ Y}
    (φ : (p ≫ g) ≅ (q ≫ f)) (γ' : (j ≫ y') ≅ (x' ≫ p)) (D : IsoDottedArrow x' j p y' γ') :
    (dottedObjMap φ γ' D).α.hom = (α_ j D.a q).inv ≫ (D.α.hom ▷ q) := rfl

/-- The `β`-component of `dottedObjMap φ γ' D` is `D.β` whiskered by `g`, followed by `φ`. -/
lemma dottedObjMap_β_hom
    {j : S ⟶ T} {x' : S ⟶ X'} {q : X' ⟶ X} {p : X' ⟶ Y'} {f : X ⟶ Y}
    {y' : T ⟶ Y'} {g : Y' ⟶ Y}
    (φ : (p ≫ g) ≅ (q ≫ f)) (γ' : (j ≫ y') ≅ (x' ≫ p)) (D : IsoDottedArrow x' j p y' γ') :
    (dottedObjMap φ γ' D).β.hom =
      (D.β.hom ▷ g) ≫ (α_ D.a p g).hom ≫ (D.a ◁ φ.hom) ≫ (α_ D.a q f).inv := rfl

/-- Morphism-map `α`-compatibility for `F`. For `θ : D₁ ⟶ D₂` in `D'`, the image `θ ▷ q` must
satisfy `(dottedObjMap … D₁).α = (j ◁ (θ.θ ▷ q)) ≫ (dottedObjMap … D₂).α`. This follows from
`θ.compat_α` (i.e. `D₁.α = (j ◁ θ.θ) ≫ D₂.α`) by right-whiskering the whole equation by `q` and
re-associating: `j ◁ (θ.θ ▷ q) = (α_ …).inv ≫ ((j ◁ θ.θ) ▷ q) ≫ (α_ …).hom` via
`Bicategory.whisker_assoc` / `whisker_exchange`. -/
theorem dottedFunctor_compat_α
    {j : S ⟶ T} {x' : S ⟶ X'} {q : X' ⟶ X} {p : X' ⟶ Y'} {f : X ⟶ Y}
    {y' : T ⟶ Y'} {g : Y' ⟶ Y}
    (φ : (p ≫ g) ≅ (q ≫ f)) (γ' : (j ≫ y') ≅ (x' ≫ p))
    {D₁ D₂ : IsoDottedArrow x' j p y' γ'} (θ : IsoDottedArrowHom D₁ D₂) :
    (dottedObjMap φ γ' D₁).α.hom
      = (j ◁ (θ.θ ▷ q)) ≫ (dottedObjMap φ γ' D₂).α.hom := by
  simp only [dottedObjMap, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom]
  rw [θ.compat_α]
  simp only [Bicategory.comp_whiskerRight]
  bicategory

/-- Morphism-map `β`-compatibility for `F`: `(dottedObjMap … D₂).β =
(dottedObjMap … D₁).β ≫ ((θ.θ ▷ q) ▷ f)`. Follows from `θ.compat_β`
(`D₂.β = D₁.β ≫ (θ.θ ▷ f)`) by right-whiskering by `g`, sliding `φ` past `θ.θ ▷ p`
via `whisker_exchange` (naturality of `φ`), and re-associating. -/
theorem dottedFunctor_compat_β
    {j : S ⟶ T} {x' : S ⟶ X'} {q : X' ⟶ X} {p : X' ⟶ Y'} {f : X ⟶ Y}
    {y' : T ⟶ Y'} {g : Y' ⟶ Y}
    (φ : (p ≫ g) ≅ (q ≫ f)) (γ' : (j ≫ y') ≅ (x' ≫ p))
    {D₁ D₂ : IsoDottedArrow x' j p y' γ'} (θ : IsoDottedArrowHom D₁ D₂) :
    (dottedObjMap φ γ' D₂).β.hom
      = (dottedObjMap φ γ' D₁).β.hom ≫ ((θ.θ ▷ q) ▷ f) := by
  simp only [dottedObjMap, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, whiskerLeftIso_hom,
    Category.assoc]
  rw [θ.compat_β, Bicategory.comp_whiskerRight]
  simp only [Category.assoc]
  congr 1
  rw [Bicategory.associator_naturality_left_assoc θ.θ p g]
  congr 1
  rw [← whisker_exchange_assoc θ.θ φ.hom]
  congr 1
  rw [Bicategory.associator_inv_naturality_left θ.θ q f]

/-- The functor `F : D' ⥤ D`. Object map `dottedObjMap`, morphism map `θ ↦ θ.θ ▷ q`. The
`map_id`/`map_comp` laws are pure whisker identities (`Bicategory.id_whiskerRight`,
`Bicategory.comp_whiskerRight`). -/
@[implicit_reducible]
noncomputable def dottedFunctor
    {j : S ⟶ T} {x' : S ⟶ X'} {q : X' ⟶ X} {p : X' ⟶ Y'} {f : X ⟶ Y}
    {y' : T ⟶ Y'} {g : Y' ⟶ Y}
    (φ : (p ≫ g) ≅ (q ≫ f)) (γ' : (j ≫ y') ≅ (x' ≫ p)) :
    IsoDottedArrow x' j p y' γ' ⥤ IsoDottedArrow (x' ≫ q) j f (y' ≫ g) (outerGamma φ γ') where
  obj D := dottedObjMap φ γ' D
  map {D₁ D₂} θ :=
    { θ := θ.θ ▷ q
      compat_α := dottedFunctor_compat_α φ γ' θ
      compat_β := dottedFunctor_compat_β φ γ' θ }
  map_id D := IsoDottedArrowHom.ext (by simp)
  map_comp {D₁ D₂ D₃} θ₁ θ₂ := IsoDottedArrowHom.ext (by simp)

/-- `dottedFunctor φ γ'` acts on objects by `dottedObjMap φ γ'`. -/
@[simp] lemma dottedFunctor_obj
    {j : S ⟶ T} {x' : S ⟶ X'} {q : X' ⟶ X} {p : X' ⟶ Y'} {f : X ⟶ Y}
    {y' : T ⟶ Y'} {g : Y' ⟶ Y}
    (φ : (p ≫ g) ≅ (q ≫ f)) (γ' : (j ≫ y') ≅ (x' ≫ p)) (D : IsoDottedArrow x' j p y' γ') :
    (dottedFunctor φ γ').obj D = dottedObjMap φ γ' D := rfl

/-- **Joint faithfulness of right-whiskering by `(q, p)`** (the core consequence of the
2-cartesian universal property `hcart.uniq`). For parallel 2-morphisms `μ₁ μ₂ : u ⟶ v`
between 1-morphisms `u v : W ⟶ X'`, if `μ₁ ▷ q = μ₂ ▷ q` and `μ₁ ▷ p = μ₂ ▷ p`, then
`μ₁ = μ₂`.

Proof sketch: Build any cone `c` admitting `u` and `v` as factorization heads with matching
data; the two whiskering equalities make `asIso μ₁` and `asIso μ₂` two solutions of the same
`hcart.uniq` `∃!` problem (comparing the factorization `h := u` with `h := v`), so uniqueness
forces them equal. Concretely take the cone `c := { a := v ≫ q, b := v ≫ p, ψ := canonical }`
with `F_v := { h := v, eq := refl, ep := refl }` and
`F_u := { h := u, eq := asIso (μ₁ ▷ q) , ep := asIso (μ₁ ▷ p) }`; then both `asIso μ₁` and
`asIso μ₂` satisfy the uniqueness predicate (`μᵢ ▷ q ≫ refl = μ₁ ▷ q` etc.), hence are equal.
`hgpd` supplies invertibility of `μ₁, μ₂` and of the whiskerings. -/
theorem whiskerRight_qp_jointly_faithful
    (hgpd : ∀ {A C : B} {u v : A ⟶ C} (θ : u ⟶ v), IsIso θ)
    {X' X Y' Y : B} {q : X' ⟶ X} {p : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {φ : (p ≫ g) ≅ (q ≫ f)} (hcart : IsTwoCartesian q p f g φ)
    {W : B} {u v : W ⟶ X'} (μ₁ μ₂ : u ⟶ v)
    (hq : μ₁ ▷ q = μ₂ ▷ q) (hp : μ₁ ▷ p = μ₂ ▷ p) :
    μ₁ = μ₂ := by
  have := hgpd μ₁
  have := hgpd μ₂
  have := hgpd (μ₁ ▷ q)
  have := hgpd (μ₁ ▷ p)
  obtain ⟨ρ, _, huniq⟩ := hcart.uniq (twoFiberFactorizationOfWhiskerIso q p f g φ μ₁)
    (selfTwoFiberFactorization q p f g φ v)
  have key (μ : u ⟶ v) [IsIso μ] (h₁ : μ ▷ q = μ₁ ▷ q) (h₂ : μ ▷ p = μ₁ ▷ p) :
      asIso μ = ρ :=
    huniq _ ⟨by simp [selfTwoFiberFactorization, twoFiberFactorizationOfWhiskerIso, h₁],
      by simp [selfTwoFiberFactorization, twoFiberFactorizationOfWhiskerIso, h₂]⟩
  simpa only [asIso_hom] using
    congrArg Iso.hom ((key μ₁ rfl rfl).trans (key μ₂ hq.symm hp.symm).symm)

/-- `F` is faithful: `θ ↦ θ.θ ▷ q` is injective on 2-morphisms. The 2-cartesian uniqueness
(`hcart.uniq`) makes right-whiskering by `q` injective on the relevant hom-sets; concretely
two parallel dotted-arrow maps with the same `θ ▷ q` give two compatible factorizations of the
same cone, hence are joined by the unique `ρ`, forcing equality. (Alternatively: the dotted
constraints already pin `θ` from `θ ▷ q` together with `θ ▷ p`, the latter recovered from `q`
via `hcart`.) -/
theorem dottedFunctor_faithful
    (hgpd : ∀ {A C : B} {u v : A ⟶ C} (θ : u ⟶ v), IsIso θ)
    {j : S ⟶ T} {x' : S ⟶ X'} {q : X' ⟶ X} {p : X' ⟶ Y'} {f : X ⟶ Y}
    {y' : T ⟶ Y'} {g : Y' ⟶ Y}
    (φ : (p ≫ g) ≅ (q ≫ f)) (γ' : (j ≫ y') ≅ (x' ≫ p))
    (hcart : IsTwoCartesian q p f g φ) :
    (dottedFunctor φ γ').Faithful := by
  constructor
  intro D₁ D₂ θ₁ θ₂ h
  refine IsoDottedArrowHom.ext (whiskerRight_qp_jointly_faithful hgpd hcart _ _
    (congrArg (fun m => m.θ) h) ?_)
  have h₂ := θ₂.compat_β
  rw [θ₁.compat_β] at h₂
  exact (cancel_epi D₁.β.hom).mp h₂

/-- Cancellation in a whiskered `α`-compatibility: if right-whiskering the $2$-morphism `σ` by
`r` intertwines the whiskered witnesses `A₁` and `A₂`, then `j ◁ σ` agrees with the comparison
$2$-morphism `A₁.hom ≫ A₂.inv` after right-whiskering by `r`. -/
theorem whiskerLeft_whiskerRight_eq_comparison {S T X' Z : B} {j : S ⟶ T} {x' : S ⟶ X'}
    {a₁ a₂ : T ⟶ X'} (r : X' ⟶ Z) {A₁ : (j ≫ a₁) ≅ x'} {A₂ : (j ≫ a₂) ≅ x'} (σ : a₁ ⟶ a₂)
    (h : (α_ j a₁ r).inv ≫ (A₁.hom ▷ r)
        = (j ◁ (σ ▷ r)) ≫ (α_ j a₂ r).inv ≫ (A₂.hom ▷ r)) :
    (j ◁ σ) ▷ r = (A₁.hom ≫ A₂.inv) ▷ r := by
  rw [Bicategory.comp_whiskerRight, whisker_assoc,
    show A₂.inv ▷ r = (whiskerRightIso A₂ r).inv from rfl,
    show A₁.hom ▷ r = (whiskerRightIso A₁ r).hom from rfl, Iso.eq_comp_inv, whiskerRightIso_hom]
  simp only [Category.assoc] at h ⊢
  rw [← h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rfl

/-- `F` is full: every 2-morphism `(D₁.a ≫ q) ⟶ (D₂.a ≫ q)` compatible with the outer dotted
data is `θ ▷ q` for a (unique) `θ` of `D'`. This is the heart of the argument: given an outer
dotted-arrow map `Θ : (a₁ ≫ q) ⟶ (a₂ ≫ q)`, the 2-cartesian property (`hcart.uniq` applied to
two factorizations of a common cone, namely `a₁` factored through `q` directly vs. via `Θ`)
produces a `θ : a₁ ⟶ a₂` with `θ ▷ q = Θ`; the `D'`-compatibilities for `θ` follow by
cancelling the whiskering by `q`/`p` using `hgpd` (invertibility) and `hcart`. -/
theorem dottedFunctor_full
    (hgpd : ∀ {A C : B} {u v : A ⟶ C} (θ : u ⟶ v), IsIso θ)
    {j : S ⟶ T} {x' : S ⟶ X'} {q : X' ⟶ X} {p : X' ⟶ Y'} {f : X ⟶ Y}
    {y' : T ⟶ Y'} {g : Y' ⟶ Y}
    (φ : (p ≫ g) ≅ (q ≫ f)) (γ' : (j ≫ y') ≅ (x' ≫ p))
    (hcart : IsTwoCartesian q p f g φ) :
    (dottedFunctor φ γ').Full := by
  constructor
  intro D₁ D₂ Θ
  have := hgpd Θ.θ
  let F₁ : TwoFiberFactorization q p f g φ (inducedTwoFiberCone q p f g φ D₂.a) :=
    { h := D₁.a
      eq := asIso Θ.θ
      ep := D₁.β.symm ≪≫ D₂.β
      compat := by
        have hΘ := Θ.compat_β
        simp only [dottedFunctor, dottedObjMap, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom,
          whiskerLeftIso_hom, Category.assoc] at hΘ
        dsimp only [inducedTwoFiberCone]
        simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, asIso_hom,
          Bicategory.comp_whiskerRight, Category.assoc]
        rw [hΘ, ← Bicategory.comp_whiskerRight_assoc, Iso.inv_hom_id,
          Bicategory.id_whiskerRight, Category.id_comp] }
  obtain ⟨ρ, ⟨hρq, hρp⟩, _⟩ := hcart.uniq F₁ (selfTwoFiberFactorization q p f g φ D₂.a)
  simp only [F₁, selfTwoFiberFactorization, Iso.refl_hom, Category.comp_id, asIso_hom,
    Iso.trans_hom, Iso.symm_hom] at hρq hρp
  refine ⟨{ θ := ρ.hom, compat_α := ?_, compat_β := ?_ }, ?_⟩
  · have hαq : (j ◁ ρ.hom) ▷ q = (D₁.α.hom ≫ D₂.α.inv) ▷ q := by
      refine whiskerLeft_whiskerRight_eq_comparison (A₁ := D₁.α) (A₂ := D₂.α) q ρ.hom ?_
      have hΘα := Θ.compat_α
      simp only [dottedFunctor, dottedObjMap, Iso.trans_hom, Iso.symm_hom,
        whiskerRightIso_hom] at hΘα
      rwa [hρq]
    have hαp : (j ◁ ρ.hom) ▷ p = (D₁.α.hom ≫ D₂.α.inv) ▷ p := by
      refine whiskerLeft_whiskerRight_eq_comparison (A₁ := D₁.α) (A₂ := D₂.α) p ρ.hom ?_
      have hcompat : (j ◁ D₁.β.hom) ≫ (α_ j D₁.a p).inv ≫ (D₁.α.hom ▷ p)
          = (j ◁ D₂.β.hom) ≫ (α_ j D₂.a p).inv ≫ (D₂.α.hom ▷ p) :=
        D₁.compat.symm.trans D₂.compat
      rw [hρp, Bicategory.whiskerLeft_comp]
      simp only [Category.assoc] at hcompat ⊢
      rw [← hcompat]
      simp
    rw [whiskerRight_qp_jointly_faithful hgpd hcart _ _ hαq hαp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  · rw [hρp, Iso.hom_inv_id_assoc]
  · exact IsoDottedArrowHom.ext hρq

/-- The test cone attached to an outer dotted arrow `Dₒ`: its legs are the dotted
$1$-morphism `Dₒ.a` and `y'`, and its witness is `Dₒ.β`. -/
@[implicit_reducible]
noncomputable def outerTwoFiberCone
    {j : S ⟶ T} {x' : S ⟶ X'} {q : X' ⟶ X} {p : X' ⟶ Y'} {f : X ⟶ Y}
    {y' : T ⟶ Y'} {g : Y' ⟶ Y}
    (φ : (p ≫ g) ≅ (q ≫ f)) (γ' : (j ≫ y') ≅ (x' ≫ p))
    (Dₒ : IsoDottedArrow (x' ≫ q) j f (y' ≫ g) (outerGamma φ γ')) :
    TwoFiberCone f g T where
  a := Dₒ.a
  b := y'
  ψ := Dₒ.β

/-- Precomposing a factorization `F` of `outerTwoFiberCone φ γ' Dₒ` with `j`, and correcting the
factorization data by `Dₒ.α` and by `γ'`, factors the cone induced by `x'`.  Comparing it with
`selfTwoFiberFactorization` is what identifies `j ≫ F.h` with `x'`. -/
@[implicit_reducible]
noncomputable def precompTwoFiberFactorization
    {j : S ⟶ T} {x' : S ⟶ X'} {q : X' ⟶ X} {p : X' ⟶ Y'} {f : X ⟶ Y}
    {y' : T ⟶ Y'} {g : Y' ⟶ Y}
    (φ : (p ≫ g) ≅ (q ≫ f)) (γ' : (j ≫ y') ≅ (x' ≫ p))
    (Dₒ : IsoDottedArrow (x' ≫ q) j f (y' ≫ g) (outerGamma φ γ'))
    (F : TwoFiberFactorization q p f g φ (outerTwoFiberCone φ γ' Dₒ)) :
    TwoFiberFactorization q p f g φ (inducedTwoFiberCone q p f g φ x') where
  h := j ≫ F.h
  eq := (α_ j F.h q) ≪≫ whiskerLeftIso j F.eq ≪≫ Dₒ.α
  ep := (α_ j F.h p) ≪≫ whiskerLeftIso j F.ep ≪≫ γ'
  compat := by
    have hF := F.compat
    dsimp only [outerTwoFiberCone] at hF
    have hαf : Dₒ.α.hom ▷ f
        = (α_ j Dₒ.a f).hom ≫ (j ◁ Dₒ.β.inv) ≫ (outerGamma φ γ').hom := by
      rw [Dₒ.compat, ← Category.assoc (j ◁ Dₒ.β.inv), ← Bicategory.whiskerLeft_comp,
        Iso.inv_hom_id, Bicategory.whiskerLeft_id, Category.id_comp, Iso.hom_inv_id_assoc]
    have hkey : (j ◁ (F.ep.hom ▷ g))
        = (j ◁ ((α_ F.h p g).hom ≫ (F.h ◁ φ.hom) ≫ (α_ F.h q f).inv ≫ (F.eq.hom ▷ f)))
          ≫ (j ◁ Dₒ.β.inv) := by
      rw [← Bicategory.whiskerLeft_comp]
      exact congrArg (j ◁ ·) ((Iso.eq_comp_inv Dₒ.β).mpr hF)
    dsimp only [inducedTwoFiberCone]
    simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
      Bicategory.comp_whiskerRight, Category.assoc]
    rw [hαf]
    simp only [outerGamma, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom]
    rw [whisker_assoc, hkey]
    simp only [Bicategory.whiskerLeft_comp, Category.assoc]
    bicategory

/-- `F` is essentially surjective: every outer dotted arrow is isomorphic to one in the image.
Given `(A, αₒ, βₒ) ∈ D` (so `A : T ⟶ X`), the cone `c` with `c.a := A`, `c.b := y'` (legs into
`X` and `Y'`) and witness `ψ` built from `βₒ`/`αₒ`/`γ'` is factored by `hcart.fac` through `q`:
this yields `a : T ⟶ X'` with `a ≫ q ≅ A` and `a ≫ p ≅ y'`-data. Equip `a` with `α := …`,
`β := …` from the factorization isos to get a `D'` object whose image under `F` is isomorphic to
`(A, αₒ, βₒ)`. -/
theorem dottedFunctor_essSurj
    {j : S ⟶ T} {x' : S ⟶ X'} {q : X' ⟶ X} {p : X' ⟶ Y'} {f : X ⟶ Y}
    {y' : T ⟶ Y'} {g : Y' ⟶ Y}
    (φ : (p ≫ g) ≅ (q ≫ f)) (γ' : (j ≫ y') ≅ (x' ≫ p))
    (hcart : IsTwoCartesian q p f g φ) :
    (dottedFunctor φ γ').EssSurj := by
  constructor
  intro Dₒ
  let Fc : TwoFiberFactorization q p f g φ (outerTwoFiberCone φ γ' Dₒ) :=
    hcart.fac (outerTwoFiberCone φ γ' Dₒ)
  obtain ⟨ρ, ⟨hρq, hρp⟩, _⟩ := hcart.uniq (precompTwoFiberFactorization φ γ' Dₒ Fc)
    (selfTwoFiberFactorization q p f g φ x')
  simp only [precompTwoFiberFactorization, selfTwoFiberFactorization, Iso.refl_hom,
    Category.comp_id, Iso.trans_hom, whiskerLeftIso_hom] at hρq hρp
  let d : IsoDottedArrow x' j p y' γ' :=
    { a := Fc.h
      α := ρ
      β := Fc.ep.symm
      compat := by
        rw [hρp]
        simp }
  refine ⟨d, ⟨IsoDottedArrow.isoOfIso Fc.eq ?_ ?_⟩⟩
  · dsimp only [dottedFunctor_obj]
    rw [dottedObjMap_α_hom, hρq, Iso.inv_hom_id_assoc]
  · have hFc := Fc.compat
    dsimp only [outerTwoFiberCone] at hFc
    dsimp only [dottedFunctor_obj]
    rw [dottedObjMap_β_hom, Iso.symm_hom]
    simp only [Category.assoc] at hFc ⊢
    rw [← hFc]
    simp

/-- **Theorem (Stacks Project, Tag 0H1A / Lemma 4.44.2).**

Let `B` be a $(2,1)$-category (a bicategory in which every $2$-morphism is invertible,
encoded by the hypothesis `hgpd`). Given a $2$-commutative diagram with an
outer rectangle decomposed into a left square (with witness `γ'`) and a right square that
is $2$-cartesian (with witness `φ`), the category of dotted arrows `D'` for the left square
and the category of dotted arrows `D` for the outer rectangle (with the induced witness
`γ = outerGamma φ γ'`) are equivalent categories. -/
@[stacks 0H1A]
theorem dottedArrows_equiv
    (hgpd : ∀ {A C : B} {u v : A ⟶ C} (θ : u ⟶ v), IsIso θ)
    {S T X X' Y Y' : B}
    (j : S ⟶ T) (x' : S ⟶ X') (q : X' ⟶ X) (p : X' ⟶ Y') (f : X ⟶ Y)
    (y' : T ⟶ Y') (g : Y' ⟶ Y)
    (φ : (p ≫ g) ≅ (q ≫ f)) (γ' : (j ≫ y') ≅ (x' ≫ p))
    (hcart : IsTwoCartesian q p f g φ) :
    -- `D'` : dotted arrows for the left square `(x', j, p, y')` with witness `γ'`
    -- `D`  : dotted arrows for the outer rectangle `(x' ≫ q, j, f, y' ≫ g)` with witness `γ`
    Nonempty (IsoDottedArrow x' j p y' γ' ≌
              IsoDottedArrow (x' ≫ q) j f (y' ≫ g) (outerGamma φ γ')) := by
  -- Assemble the equivalence from the explicit functor `dottedFunctor φ γ'`, which is full,
  -- faithful and essentially surjective (the three lemmas above). Full+Faithful+EssSurj ⇒
  -- `IsEquivalence`; then `Functor.asEquivalence` produces a `≌`, wrapped in `Nonempty`.
  have : (dottedFunctor φ γ').Full := dottedFunctor_full hgpd φ γ' hcart
  have : (dottedFunctor φ γ').Faithful := dottedFunctor_faithful hgpd φ γ' hcart
  have : (dottedFunctor φ γ').EssSurj := dottedFunctor_essSurj φ γ' hcart
  have : (dottedFunctor φ γ').IsEquivalence := Functor.IsEquivalence.mk
  exact ⟨(dottedFunctor φ γ').asEquivalence⟩

end CategoryTheory.DottedArrowBaseChange
