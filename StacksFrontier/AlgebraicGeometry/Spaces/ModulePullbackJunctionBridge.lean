module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleCompositionSections

/-!
# The two spelling junctions of the inverse image of a composite, and the head square

Pasting facts about [Stacks Project, Tag 03LU] — the comparison
`AlgebraicGeometry.Space.modulePullbackCompIso` of inverse images of `𝒪`-modules along a
composite of morphisms of algebraic spaces — runs into two places where one object of a module
category has two syntactically different spellings.  Call them the two *junctions*:

* **J1**, the associativity junction: `(modulePullback ((μ ≫ t) ≫ w)).obj N` against
  `(modulePullback (μ ≫ t ≫ w)).obj N`.
* **J2**, the composition junction: `(modulePullback w ⋙ modulePullback t).obj N` against
  `(modulePullback t).obj ((modulePullback w).obj N)`.

Both are definitional, so a composite whose two adjacent factors sit at the two spellings of one
junction elaborates with no transport in sight; the cost is paid by the *kernel*, which has to
identify the two, and `AlgebraicGeometry.Space.modulePullback` unfolds to a sheafification.  Every
assembly in this neighbourhood therefore has to cross each junction as few times as possible, and
each crossing has to happen where it is cheap.

This file is the layer that makes the crossings explicit and names them.

## Main results

* `AlgebraicGeometry.Space.modulePullbackObj_eqToHom_assoc` (with its `_symm`) and
  `AlgebraicGeometry.Space.eqToHom_comp_obj_modulePullback`: **the two bridge identities, one per
  junction.**  Each says that the transport across its junction is an identity, and each is
  `CategoryTheory.eqToHom`-only: neither mentions `AlgebraicGeometry.Space.modulePullbackCompIso`,
  so neither makes the kernel take a `hom` or `inv` projection out of an adjoint-uniqueness
  isomorphism while it is identifying two spellings.
* `AlgebraicGeometry.Space.modulePullbackObj_eqToHom_assoc'` and
  `.modulePullbackObj_eqToHom_assoc_symm'`: the same at an arbitrary proof of the equality of the
  two objects, for a consumer whose transport came out of some other chain of congruences.
* `AlgebraicGeometry.Space.comp_eqToHom_assoc` and
  `AlgebraicGeometry.Space.eqToHom_assoc_comp`: **the absorbing forms** — a transport across the
  associativity junction is swallowed by whatever stands beside it, *the neighbour being a
  variable*.  These are where the associativity junction is crossed in practice; see the
  implementation notes for why the neighbour has to be a variable.
* `AlgebraicGeometry.Space.modulePullback_map_eqToHom` and
  `AlgebraicGeometry.Space.eqToHom_eq_modulePullback_map`: the inverse image of a transport read
  as a transport at the composite spelling, in both orientations.
* `AlgebraicGeometry.Space.modulePullbackCompIso_eqToHom_congr_left`,
  `.modulePullbackCompIso_eqToHom_congr_right`,
  `.modulePullbackCompIso_inv_eqToHom_congr_left` and
  `.modulePullbackCompIso_eqToHom_assoc_app`: **the transports of the comparison, restated so
  that every composite in the statement is junction-free** — each adjacency is syntactically
  exact, so a consumer pasting them identifies nothing.
* `AlgebraicGeometry.Space.modulePullbackCompIso_headSquare`: **the head square.**  The
  comparison along a composite, the transport along a factorization of it, and the inverted
  comparison along the other factorization, are natural in a further morphism in front.
* `AlgebraicGeometry.Space.modulePullbackCompIso_map_eqToHom_square'`,
  `AlgebraicGeometry.Space.modulePullbackCompIso_app_hom_square` and
  `AlgebraicGeometry.Space.headSquareInv_app`: those squares again in the form an
  assembler fed `AlgebraicGeometry.Space.chartCompositeDifferentialsAssociatedIso_hom` verbatim
  needs them — that lemma spells its transports as `CategoryTheory.eqToIso` on `hom` and its
  inverted comparison as `CategoryTheory.Iso.symm` of a component.  The second spelling can be
  restated here directly; the first cannot, and is handled by taking the transports as variables
  with their defining equations.
* `AlgebraicGeometry.Space.modulePullbackCompIso_hom_app_square`,
  `AlgebraicGeometry.Space.modulePullbackCompIso_map_eqToHom_square`,
  `AlgebraicGeometry.Space.headSquareInv` and `AlgebraicGeometry.Space.headSquareTail`: **the
  squares of the head square's three factors one at a time, and the gluing of the last two.**
  The head square pastes all three at once, which is what its own consumer wants; a consumer
  pasting a longer chain whose group boundaries fall between them needs the factors separately,
  so these are not private.

## Implementation notes

*Why the restatements are needed.*  `AlgebraicGeometry.Space.modulePullbackCompIso_congr_left`
and `.modulePullbackCompIso_congr_right` write their transports with
`AlgebraicGeometry.Space.transportNatTrans`, whose component at an object lands at the *nested*
spelling `(modulePullback k).obj ((modulePullback a).obj M)` while the comparison beside it starts
at the *composite* spelling `(modulePullback a ⋙ modulePullback k).obj M`: each statement carries
a J2 crossing, and so does every use of it.  Writing the transport as
`eqToHom (congrArg (fun k ↦ (modulePullback a ⋙ modulePullback k).obj M) e)` instead puts it at
the comparison's own spelling and the crossing disappears.  Likewise
`.modulePullbackCompIso_map_hom_app_comp_eqToHom` carries a J1 crossing, between
`(modulePullback (μ ≫ χ ≫ aa)).obj M` and `(modulePullback ((μ ≫ χ) ≫ aa)).obj M`; keeping the
outer composite as a *variable* `d` with its two factorizations `hd` and `hd'` supplied as
hypotheses removes it, which is the general form of the statement and not a weakening of it.

*Where the cost actually is.*  It is **not** a junction in a statement.  A statement
carrying three or four of them, with the equation supplied as a hypothesis and handed straight
back, is checked in under a second; so is
`.modulePullbackCompIso_map_inv_comp_hom_app` restated verbatim, junction and all.  What is not
affordable is a junction inside a `CategoryTheory.congrArg` **motive**: there the kernel must
identify the two spellings while the motive's own type is being formed, and
`AlgebraicGeometry.Space.modulePullback` unfolds to a sheafification.  Three consequences shape
this file.

*First, every motive here is junction-free.*  Sometimes that forces a step to be stated with its
two sides exchanged: the type of an equation of morphisms is the type of whichever side was
elaborated first, and that is what decides whether a motive built on the equation identifies two
spellings.  `AlgebraicGeometry.Space.eqToHom_eq_modulePullback_map` is
`.modulePullback_map_eqToHom` in the other orientation for exactly this reason, and
`AlgebraicGeometry.Space.invCompHom` is the inverted coherence in the other orientation,
with the associativity transport made explicit where that lemma identifies the two bracketings
across a composition.

*Second, where a junction cannot be avoided, the neighbouring morphism is a variable.*  That is
what `AlgebraicGeometry.Space.comp_eqToHom_assoc` and `.eqToHom_assoc_comp` are for: with the
neighbour a variable the two spellings meet at the level of the equation and nothing else is in
the term, and instantiating at a concrete morphism whose type already carries the right spelling
identifies nothing further.

*Third, two transports are never merged by `rfl` or by `simp [eqToHom_trans]`.*  The route used
throughout is `(eqToHom_trans _ _).trans (congrArg eqToHom (proof_irrel _ _))`, which supplies
the composite proof instead of computing it.

Two claims that had been propagated about this neighbourhood do not survive measurement, and are
recorded here so that they are not inherited again: identifying the two bracketings beside a
`modulePullbackCompIso` projection is cheap, provided every datum is a variable and the
identification is at the level of the equation; and so is identifying the two spellings of J2 at
`modulePullback`.

*Why the tails stay variables.*  The head square is stated with `κ'` and `t'` variables and
`hκ : μ ≫ κ = κ'`, `ht : μ ≫ t = t'`, so that a consumer never has to form the substituted
composite — with the tails substituted, both bracketings of the triple composite are live in the
statement itself.  Inside the proof one of them *is* substituted:
`AlgebraicGeometry.Space.headSquareInv` substitutes `ht`, which is what reduces it to
`AlgebraicGeometry.Space.invCompHom`.

No `@[stacks]` attribute is claimed: Tag 03LU is registered at
`AlgebraicGeometry.Space.modulePullback` and `.modulePullbackCompIso`, and these are the engine
lemmas of its coherence, not a covering set for it.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {P X Z Y T : AlgebraicSpaces B S hS}

/-! ### The two bridge identities -/

/-- **The J1 bridge.**  The transport of an inverse-image object along the associativity of a
triple composite is an identity.

This is where the associativity junction is crossed, and the statement contains no
`AlgebraicGeometry.Space.modulePullbackCompIso` projection: identifying the two bracketings and
taking a `hom` or `inv` out of an adjoint-uniqueness isomorphism are each affordable, and doing
both inside one term is what exhausts the kernel budget.  Note that the two spellings are
identified *at the level of the equation* here, not across a `≫`; the second is the
expensive one. -/
theorem modulePullbackObj_eqToHom_assoc (μ : P ⟶ X) (t : X ⟶ T) (w : T ⟶ Y)
    (N : Modules.{u, u} B S hS Y.1 Y.2) :
    eqToHom (congrArg (fun g : P ⟶ Y => (modulePullback B S hS g).obj N)
        (Category.assoc μ t w)) =
      𝟙 ((modulePullback B S hS ((μ ≫ t) ≫ w)).obj N) :=
  rfl

/-- **The J2 bridge.**  The transport between the two spellings of the inverse image of an
inverse image is an identity.  As with
`AlgebraicGeometry.Space.modulePullbackObj_eqToHom_assoc`, the statement contains no comparison
projection. -/
theorem eqToHom_comp_obj_modulePullback (aa : P ⟶ X) (k : X ⟶ Y)
    (N : Modules.{u, u} B S hS Y.1 Y.2) :
    eqToHom (Functor.comp_obj (modulePullback B S hS k) (modulePullback B S hS aa) N) =
      𝟙 ((modulePullback B S hS k ⋙ modulePullback B S hS aa).obj N) :=
  rfl

/-! ### The consumer forms of the bridges -/

/-- The J1 bridge at an arbitrary proof of the equality of the two objects: a consumer whose
transport came out of some other chain of congruences does not have to produce
`CategoryTheory.Category.assoc` itself. -/
theorem modulePullbackObj_eqToHom_assoc' (μ : P ⟶ X) (t : X ⟶ T) (w : T ⟶ Y)
    (N : Modules.{u, u} B S hS Y.1 Y.2)
    (p : (modulePullback B S hS ((μ ≫ t) ≫ w)).obj N =
      (modulePullback B S hS (μ ≫ t ≫ w)).obj N) :
    eqToHom p = 𝟙 ((modulePullback B S hS ((μ ≫ t) ≫ w)).obj N) :=
  rfl

/-- **A transport across the associativity junction is absorbed by whatever stands in front of
it.**  The morphism in front is a *variable*, which is what keeps this affordable: the junction is
identified at the level of the equation, with no comparison projection in the term, and an
instantiation at a concrete morphism whose target is the left-bracketed composite identifies
nothing further. -/
theorem comp_eqToHom_assoc (μ : P ⟶ X) (t : X ⟶ T) (w : T ⟶ Y)
    (N : Modules.{u, u} B S hS Y.1 Y.2) {A : Modules.{u, u} B S hS P.1 P.2}
    (f : A ⟶ (modulePullback B S hS ((μ ≫ t) ≫ w)).obj N)
    (p : (modulePullback B S hS ((μ ≫ t) ≫ w)).obj N =
      (modulePullback B S hS (μ ≫ t ≫ w)).obj N) :
    f ≫ eqToHom p = f :=
  (congrArg (fun z => f ≫ z) (modulePullbackObj_eqToHom_assoc' B S hS μ t w N p)).trans
    (Category.comp_id f)

/-- **The J1 bridge, the other way round.**  The transport of an inverse-image object from the
right-bracketed to the left-bracketed triple composite is an identity. -/
theorem modulePullbackObj_eqToHom_assoc_symm (μ : P ⟶ X) (t : X ⟶ T) (w : T ⟶ Y)
    (N : Modules.{u, u} B S hS Y.1 Y.2) :
    eqToHom (congrArg (fun g : P ⟶ Y => (modulePullback B S hS g).obj N)
        (Category.assoc μ t w).symm) =
      𝟙 ((modulePullback B S hS (μ ≫ t ≫ w)).obj N) :=
  rfl

/-- `AlgebraicGeometry.Space.modulePullbackObj_eqToHom_assoc_symm` at an arbitrary proof. -/
theorem modulePullbackObj_eqToHom_assoc_symm' (μ : P ⟶ X) (t : X ⟶ T) (w : T ⟶ Y)
    (N : Modules.{u, u} B S hS Y.1 Y.2)
    (p : (modulePullback B S hS (μ ≫ t ≫ w)).obj N =
      (modulePullback B S hS ((μ ≫ t) ≫ w)).obj N) :
    eqToHom p = 𝟙 ((modulePullback B S hS (μ ≫ t ≫ w)).obj N) :=
  rfl

/-- **A transport across the associativity junction is absorbed by whatever stands behind it.**
The companion of `AlgebraicGeometry.Space.comp_eqToHom_assoc` on the other side; again the
morphism is a variable, so the junction is identified with no comparison projection present. -/
theorem eqToHom_assoc_comp (μ : P ⟶ X) (t : X ⟶ T) (w : T ⟶ Y)
    (N : Modules.{u, u} B S hS Y.1 Y.2) {A : Modules.{u, u} B S hS P.1 P.2}
    (f : (modulePullback B S hS ((μ ≫ t) ≫ w)).obj N ⟶ A)
    (p : (modulePullback B S hS (μ ≫ t ≫ w)).obj N =
      (modulePullback B S hS ((μ ≫ t) ≫ w)).obj N) :
    eqToHom p ≫ f = f :=
  (congrArg (fun z => z ≫ f) (modulePullbackObj_eqToHom_assoc_symm' B S hS μ t w N p)).trans
    (Category.id_comp f)

/-- **The inverse image of a transport, read as a transport at the composite spelling.**  This is
the J2 bridge in the form a composite meets it: `CategoryTheory.eqToHom_map` lands at the nested
spelling, and the comparison beside it starts at the composite one. -/
theorem modulePullback_map_eqToHom (aa : P ⟶ X) {k₁ k₂ : X ⟶ Y} (e : k₁ = k₂)
    (N : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS aa).map
        (eqToHom (congrArg (fun k : X ⟶ Y => (modulePullback B S hS k).obj N) e)) =
      eqToHom (congrArg (fun k : X ⟶ Y =>
        (modulePullback B S hS k ⋙ modulePullback B S hS aa).obj N) e) := by
  subst e
  refine ((modulePullback B S hS aa).map_id _).trans ?_
  exact (eqToHom_comp_obj_modulePullback B S hS aa k₁ N).symm.trans
    (congrArg eqToHom (proof_irrel _ _))

/-! ### The transports of the comparison, junction-free -/

/-- **The comparison along a composite is compatible with an equality of its outer morphism**,
with the transport written at the comparison's own spelling so that the statement is
junction-free.  This is `AlgebraicGeometry.Space.modulePullbackCompIso_congr_left` restated: there
the transport is a component of `AlgebraicGeometry.Space.transportNatTrans`, which lands at the
nested spelling of the composite inverse image while the comparison beside it starts at the
composite spelling, so that statement carries a J2 crossing and so does every use of it. -/
theorem modulePullbackCompIso_eqToHom_congr_left {k₁ k₂ : P ⟶ X} (e : k₁ = k₂) (aa : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    eqToHom (congrArg (fun k : P ⟶ X =>
          (modulePullback B S hS aa ⋙ modulePullback B S hS k).obj M) e) ≫
        (modulePullbackCompIso B S hS k₂ aa).hom.app M =
      (modulePullbackCompIso B S hS k₁ aa).hom.app M ≫
        eqToHom (congrArg (fun k : P ⟶ X =>
          (modulePullback B S hS (k ≫ aa)).obj M) e) := by
  subst e
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- **The comparison along a composite is compatible with an equality of its inner morphism**,
junction-free.  This is `AlgebraicGeometry.Space.modulePullbackCompIso_congr_right` restated; see
`AlgebraicGeometry.Space.modulePullbackCompIso_eqToHom_congr_left` for what the restatement
removes.  The transport in front is the inverse image of the one on the inner morphism, read at
the composite spelling by `AlgebraicGeometry.Space.modulePullback_map_eqToHom`. -/
theorem modulePullbackCompIso_eqToHom_congr_right (aa : P ⟶ X) {k₁ k₂ : X ⟶ Y} (e : k₁ = k₂)
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    eqToHom (congrArg (fun k : X ⟶ Y =>
          (modulePullback B S hS k ⋙ modulePullback B S hS aa).obj M) e) ≫
        (modulePullbackCompIso B S hS aa k₂).hom.app M =
      (modulePullbackCompIso B S hS aa k₁).hom.app M ≫
        eqToHom (congrArg (fun k : X ⟶ Y =>
          (modulePullback B S hS (aa ≫ k)).obj M) e) := by
  subst e
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- **The inverted comparison along a composite is compatible with an equality of its outer
morphism**, junction-free.  This is the component form of
`AlgebraicGeometry.Space.modulePullbackCompIso_inv_eqToHom_left`, which is stated between natural
transformations; a consumer at a fixed module needs it here, and at the comparison's own spelling
on both sides. -/
theorem modulePullbackCompIso_inv_eqToHom_congr_left {k₁ k₂ : P ⟶ T} (e : k₁ = k₂) (w : T ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullbackCompIso B S hS k₁ w).inv.app M ≫
        eqToHom (congrArg (fun k : P ⟶ T =>
          (modulePullback B S hS w ⋙ modulePullback B S hS k).obj M) e) =
      eqToHom (congrArg (fun k : P ⟶ T => (modulePullback B S hS (k ≫ w)).obj M) e) ≫
        (modulePullbackCompIso B S hS k₂ w).inv.app M := by
  subst e
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- **The associativity coherence of the comparison across an equality of the outer composite**,
junction-free.  This is
`AlgebraicGeometry.Space.modulePullbackCompIso_map_hom_app_comp_eqToHom` restated with the outer
composite kept as a variable `d` and its two factorizations supplied as `hd` and `hd'`: the
original statement identifies `μ ≫ χ ≫ aa` with `(μ ≫ χ) ≫ aa` inside itself, so every use of it
re-crosses J1, while here each transport's endpoints are exactly its neighbours'. -/
theorem modulePullbackCompIso_eqToHom_assoc_app (μ : P ⟶ X) (χ : X ⟶ Z) (χ' : P ⟶ Z)
    (hμ : μ ≫ χ = χ') (aa : Z ⟶ Y) (d : P ⟶ Y) (hd : μ ≫ χ ≫ aa = d) (hd' : χ' ≫ aa = d)
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS μ).map ((modulePullbackCompIso B S hS χ aa).hom.app M) ≫
        (modulePullbackCompIso B S hS μ (χ ≫ aa)).hom.app M ≫
          eqToHom (congrArg (fun g : P ⟶ Y => (modulePullback B S hS g).obj M) hd) =
      (modulePullbackCompIso B S hS μ χ).hom.app ((modulePullback B S hS aa).obj M) ≫
        eqToHom (congrArg (fun g : P ⟶ Z =>
          (modulePullback B S hS aa ⋙ modulePullback B S hS g).obj M) hμ) ≫
        (modulePullbackCompIso B S hS χ' aa).hom.app M ≫
          eqToHom (congrArg (fun g : P ⟶ Y => (modulePullback B S hS g).obj M) hd') := by
  subst hμ
  subst hd
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  exact ((congrArg (fun z => (modulePullbackCompIso B S hS μ χ).hom.app
          ((modulePullback B S hS aa).obj M) ≫ z)
      (comp_eqToHom_assoc B S hS μ χ aa M
        ((modulePullbackCompIso B S hS (μ ≫ χ) aa).hom.app M)
        (congrArg (fun g : P ⟶ Y => (modulePullback B S hS g).obj M) hd'))).trans
    (modulePullbackCompIso_assoc_app B S hS μ χ aa M)).symm




/-- `AlgebraicGeometry.Space.modulePullback_map_eqToHom` with the two sides exchanged.  This is
not a restatement for its own sake: the *type* of an equation of morphisms is the type of either
side, and which of the two spellings of the composite inverse image it carries decides whether a
`congrArg` motive built on it identifies the two spellings or not.  A motive that does
is what exhausts the kernel budget, so both orientations are wanted. -/
theorem eqToHom_eq_modulePullback_map (aa : P ⟶ X) {k₁ k₂ : X ⟶ Y} (e : k₁ = k₂)
    (N : Modules.{u, u} B S hS Y.1 Y.2) :
    eqToHom (congrArg (fun k : X ⟶ Y =>
        (modulePullback B S hS k ⋙ modulePullback B S hS aa).obj N) e) =
      (modulePullback B S hS aa).map
        (eqToHom (congrArg (fun k : X ⟶ Y => (modulePullback B S hS k).obj N) e)) :=
  (modulePullback_map_eqToHom B S hS aa e N).symm

/-! ### The head square -/

/-- The inverse image of the three-factor head, expanded into the three inverse images. -/
private theorem headMapComp (μ : P ⟶ X) (κ : X ⟶ Z) (a : Z ⟶ Y) (t : X ⟶ T) (w : T ⟶ Y)
    (hc : κ ≫ a = t ≫ w) (N : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS μ).map
        ((modulePullbackCompIso B S hS κ a).hom.app N ≫
          eqToHom (congrArg (fun g : X ⟶ Y => (modulePullback B S hS g).obj N) hc) ≫
          (modulePullbackCompIso B S hS t w).inv.app N) =
      (modulePullback B S hS μ).map ((modulePullbackCompIso B S hS κ a).hom.app N) ≫
        (modulePullback B S hS μ).map
          (eqToHom (congrArg (fun g : X ⟶ Y => (modulePullback B S hS g).obj N) hc)) ≫
        (modulePullback B S hS μ).map ((modulePullbackCompIso B S hS t w).inv.app N) :=
  ((modulePullback B S hS μ).map_comp _ _).trans
    (congrArg (fun z => (modulePullback B S hS μ).map
        ((modulePullbackCompIso B S hS κ a).hom.app N) ≫ z)
      ((modulePullback B S hS μ).map_comp _ _))

/-- **[Stacks Project, Tag 03LU]'s coherence for an inverted comparison, with the associativity
transport made explicit.**  This is
`AlgebraicGeometry.Space.modulePullbackCompIso_map_inv_comp_hom_app` with `eqToHom j` inserted
where that lemma identifies the two bracketings across a composition, and with the two sides
exchanged so that the equation's own type carries the composite spelling. -/
private theorem invCompHom (μ : P ⟶ X) (t : X ⟶ T) (w : T ⟶ Y)
    (N : Modules.{u, u} B S hS Y.1 Y.2)
    (j : (modulePullback B S hS (μ ≫ t ≫ w)).obj N =
      (modulePullback B S hS ((μ ≫ t) ≫ w)).obj N) :
    (modulePullbackCompIso B S hS μ (t ≫ w)).hom.app N ≫ eqToHom j ≫
        (modulePullbackCompIso B S hS (μ ≫ t) w).inv.app N =
      (modulePullback B S hS μ).map ((modulePullbackCompIso B S hS t w).inv.app N) ≫
        (modulePullbackCompIso B S hS μ t).hom.app ((modulePullback B S hS w).obj N) :=
  (congrArg (fun z => (modulePullbackCompIso B S hS μ (t ≫ w)).hom.app N ≫ z)
      (eqToHom_assoc_comp B S hS μ t w N
        ((modulePullbackCompIso B S hS (μ ≫ t) w).inv.app N) j)).trans
    (modulePullbackCompIso_map_inv_comp_hom_app B S hS μ t w N).symm

/-- **The square of [Stacks Project, Tag 03LU] at the outer comparison alone.**  The inverse
image along `μ` of the comparison along `χ ≫ aa`, followed by the comparison along `μ ≫ χ ≫ aa`
and the transport to `χ' ≫ aa`, is the comparison along `μ ≫ χ`, the transport to `χ'`, and the
comparison along `χ' ≫ aa`.

This is `AlgebraicGeometry.Space.modulePullbackCompIso_eqToHom_assoc_app` read at the one choice
of its outer composite `d` that makes its trailing transport an identity, namely `d = χ' ≫ aa`,
and re-bracketed so that the two verticals are single morphisms.  That is the form in which the
comparison at the chart is *one factor* of a longer chain: the head square pastes it together
with the two factors behind it, and a consumer whose next group boundary falls immediately after
it needs it alone. -/
theorem modulePullbackCompIso_hom_app_square (μ : P ⟶ X) (χ : X ⟶ Z) (χ' : P ⟶ Z)
    (hκ : μ ≫ χ = χ') (aa : Z ⟶ Y) (hd : μ ≫ χ ≫ aa = χ' ≫ aa)
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS μ).map ((modulePullbackCompIso B S hS χ aa).hom.app M) ≫
        ((modulePullbackCompIso B S hS μ (χ ≫ aa)).hom.app M ≫
          eqToHom (congrArg (fun g : P ⟶ Y => (modulePullback B S hS g).obj M) hd)) =
      ((modulePullbackCompIso B S hS μ χ).hom.app ((modulePullback B S hS aa).obj M) ≫
          eqToHom (congrArg (fun g : P ⟶ Z =>
            (modulePullback B S hS aa ⋙ modulePullback B S hS g).obj M) hκ)) ≫
        (modulePullbackCompIso B S hS χ' aa).hom.app M := by
  refine (modulePullbackCompIso_eqToHom_assoc_app B S hS μ χ χ' hκ aa (χ' ≫ aa) hd rfl M).trans ?_
  simp only [eqToHom_refl, Category.comp_id, Category.assoc]

/-- **The square of the transport along a factorization**, at a morphism `μ` in front: the
inverse image along `μ` of the transport from `c` to `e`, followed by the comparison along
`μ ≫ e` and the transport to `e'`, is the comparison along `μ ≫ c`, the transport to `c'`, and
the transport from `c'` to `e'`.

Every datum is a variable and the three equations are hypotheses, so the transports meet only at
the level of the equations.  This is the `e`-side companion of
`AlgebraicGeometry.Space.headSquareInv`; together the two cover the two factors of
`AlgebraicGeometry.Space.chartCompositeDifferentialsAssociatedIso` that stand in front of
[Stacks Project, Tag 03LU].  `AlgebraicGeometry.Space.headSquareTail` is the two of them glued,
which is the form the head square needs and not the form an assembler at the individual factors
needs. -/
theorem modulePullbackCompIso_map_eqToHom_square (μ : P ⟶ X) {c e : X ⟶ Y} (hc : c = e)
    (c' e' : P ⟶ Y) (hd : μ ≫ c = c') (he : μ ≫ e = e')
    (N : Modules.{u, u} B S hS Y.1 Y.2)
    (p : (modulePullback B S hS c').obj N = (modulePullback B S hS e').obj N) :
    (modulePullback B S hS μ).map
          (eqToHom (congrArg (fun g : X ⟶ Y => (modulePullback B S hS g).obj N) hc)) ≫
        (modulePullbackCompIso B S hS μ e).hom.app N ≫
          eqToHom (congrArg (fun g : P ⟶ Y => (modulePullback B S hS g).obj N) he) =
      ((modulePullbackCompIso B S hS μ c).hom.app N ≫
          eqToHom (congrArg (fun g : P ⟶ Y => (modulePullback B S hS g).obj N) hd)) ≫
        eqToHom p := by
  subst hc
  subst hd
  subst he
  simp only [eqToHom_refl, Category.comp_id]
  exact (congrArg (fun z => z ≫ (modulePullbackCompIso B S hS μ c).hom.app N)
    ((modulePullback B S hS μ).map_id ((modulePullback B S hS c).obj N))).trans
      (Category.id_comp _)

/-- The inverted comparison moved out of the inverse image along `μ` and carried to the tail.
With the tail substituted this *is* `AlgebraicGeometry.Space.invCompHom`, whose own statement
already has the associativity transport explicit; the tail is kept a variable in the statement so
that a consumer never has to form the substituted composite.

Public because it is one of the two squares that an assembler at the *individual* factors of
`AlgebraicGeometry.Space.chartCompositeDifferentialsAssociatedIso` needs; the other is
`AlgebraicGeometry.Space.modulePullbackCompIso_map_eqToHom_square`. -/
theorem headSquareInv (μ : P ⟶ X) (t : X ⟶ T) (w : T ⟶ Y) (t' : P ⟶ T)
    (ht : μ ≫ t = t') (N : Modules.{u, u} B S hS Y.1 Y.2)
    (q : (modulePullback B S hS (μ ≫ t ≫ w)).obj N =
      (modulePullback B S hS (t' ≫ w)).obj N) :
    (modulePullback B S hS μ).map ((modulePullbackCompIso B S hS t w).inv.app N) ≫
        (modulePullbackCompIso B S hS μ t).hom.app ((modulePullback B S hS w).obj N) ≫
        eqToHom (congrArg (fun g : P ⟶ T =>
          (modulePullback B S hS w ⋙ modulePullback B S hS g).obj N) ht) =
      (modulePullbackCompIso B S hS μ (t ≫ w)).hom.app N ≫
        eqToHom q ≫ (modulePullbackCompIso B S hS t' w).inv.app N := by
  subst ht
  simp only [eqToHom_refl, Category.comp_id]
  exact (invCompHom B S hS μ t w N q).symm

/-- **The t-side of the head square.**  The inverse image of the transport along the
factorization, the inverse image of the inverted comparison, the comparison in front and the
transport to the tail, is the comparison along `μ ≫ (κ ≫ a)`, a single transport, and the
inverted comparison at the tail.

This is `AlgebraicGeometry.Space.modulePullbackCompIso_map_eqToHom_square` and
`AlgebraicGeometry.Space.headSquareInv` glued, with the outer composite presented as `κ ≫ a`;
a consumer assembling at the individual factors wants those two instead. -/
theorem headSquareTail (μ : P ⟶ X) (κ : X ⟶ Z) (a : Z ⟶ Y) (t : X ⟶ T) (w : T ⟶ Y)
    (t' : P ⟶ T) (ht : μ ≫ t = t') (hc : κ ≫ a = t ≫ w)
    (N : Modules.{u, u} B S hS Y.1 Y.2) (hd : μ ≫ κ ≫ a = t' ≫ w)
    (q : (modulePullback B S hS (μ ≫ t ≫ w)).obj N =
      (modulePullback B S hS (t' ≫ w)).obj N) :
    (modulePullback B S hS μ).map
          (eqToHom (congrArg (fun g : X ⟶ Y => (modulePullback B S hS g).obj N) hc)) ≫
        (modulePullback B S hS μ).map ((modulePullbackCompIso B S hS t w).inv.app N) ≫
        (modulePullbackCompIso B S hS μ t).hom.app ((modulePullback B S hS w).obj N) ≫
        eqToHom (congrArg (fun g : P ⟶ T =>
          (modulePullback B S hS w ⋙ modulePullback B S hS g).obj N) ht) =
      (modulePullbackCompIso B S hS μ (κ ≫ a)).hom.app N ≫
        eqToHom (congrArg (fun g : P ⟶ Y => (modulePullback B S hS g).obj N) hd) ≫
        (modulePullbackCompIso B S hS t' w).inv.app N := by
  refine (congrArg (fun z => (modulePullback B S hS μ).map
        (eqToHom (congrArg (fun g : X ⟶ Y => (modulePullback B S hS g).obj N) hc)) ≫ z)
    (headSquareInv B S hS μ t w t' ht N q)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z =>
      (z ≫ (modulePullbackCompIso B S hS μ (t ≫ w)).hom.app N) ≫
        eqToHom q ≫ (modulePullbackCompIso B S hS t' w).inv.app N)
    (eqToHom_eq_modulePullback_map B S hS μ hc N)).symm.trans ?_
  refine (congrArg (fun z => z ≫ eqToHom q ≫
      (modulePullbackCompIso B S hS t' w).inv.app N)
    (modulePullbackCompIso_eqToHom_congr_right B S hS μ hc N)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg (fun z => (modulePullbackCompIso B S hS μ (κ ≫ a)).hom.app N ≫ z) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (fun z => z ≫ (modulePullbackCompIso B S hS t' w).inv.app N)
    ((eqToHom_trans _ _).trans (congrArg eqToHom (proof_irrel _ _)))

/-- The left-hand side of the head square, brought to the comparison along `μ ≫ (κ ≫ a)`, a
single transport, and the inverted comparison at the tail. -/
private theorem headSquareLeft (μ : P ⟶ X) (κ : X ⟶ Z) (a : Z ⟶ Y) (t : X ⟶ T) (w : T ⟶ Y)
    (t' : P ⟶ T) (ht : μ ≫ t = t') (hc : κ ≫ a = t ≫ w)
    (N : Modules.{u, u} B S hS Y.1 Y.2) (hd : μ ≫ κ ≫ a = t' ≫ w)
    (q : (modulePullback B S hS (μ ≫ t ≫ w)).obj N =
      (modulePullback B S hS (t' ≫ w)).obj N) :
    (modulePullback B S hS μ).map
          ((modulePullbackCompIso B S hS κ a).hom.app N ≫
            eqToHom (congrArg (fun g : X ⟶ Y => (modulePullback B S hS g).obj N) hc) ≫
            (modulePullbackCompIso B S hS t w).inv.app N) ≫
        (modulePullbackCompIso B S hS μ t).hom.app ((modulePullback B S hS w).obj N) ≫
        eqToHom (congrArg (fun g : P ⟶ T =>
          (modulePullback B S hS w ⋙ modulePullback B S hS g).obj N) ht) =
      (modulePullback B S hS μ).map ((modulePullbackCompIso B S hS κ a).hom.app N) ≫
        (modulePullbackCompIso B S hS μ (κ ≫ a)).hom.app N ≫
          eqToHom (congrArg (fun g : P ⟶ Y => (modulePullback B S hS g).obj N) hd) ≫
          (modulePullbackCompIso B S hS t' w).inv.app N := by
  refine (congrArg (fun z => z ≫
      (modulePullbackCompIso B S hS μ t).hom.app ((modulePullback B S hS w).obj N) ≫
        eqToHom (congrArg (fun g : P ⟶ T =>
          (modulePullback B S hS w ⋙ modulePullback B S hS g).obj N) ht))
    (headMapComp B S hS μ κ a t w hc N)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => (modulePullback B S hS μ).map
        ((modulePullbackCompIso B S hS κ a).hom.app N) ≫ z)
    (Category.assoc _ _ _)).trans ?_
  exact congrArg (fun z => (modulePullback B S hS μ).map
      ((modulePullbackCompIso B S hS κ a).hom.app N) ≫ z)
    (headSquareTail B S hS μ κ a t w t' ht hc N hd q)

/-- The right-hand side of the head square, reached from the same normal form by the
junction-free associativity coherence
`AlgebraicGeometry.Space.modulePullbackCompIso_eqToHom_assoc_app`. -/
private theorem headSquareRight (μ : P ⟶ X) (κ : X ⟶ Z) (a : Z ⟶ Y) (t' : P ⟶ T) (w : T ⟶ Y)
    (κ' : P ⟶ Z) (hκ : μ ≫ κ = κ') (hc' : κ' ≫ a = t' ≫ w)
    (N : Modules.{u, u} B S hS Y.1 Y.2) (hd : μ ≫ κ ≫ a = t' ≫ w) :
    (modulePullback B S hS μ).map ((modulePullbackCompIso B S hS κ a).hom.app N) ≫
        (modulePullbackCompIso B S hS μ (κ ≫ a)).hom.app N ≫
          eqToHom (congrArg (fun g : P ⟶ Y => (modulePullback B S hS g).obj N) hd) ≫
          (modulePullbackCompIso B S hS t' w).inv.app N =
      (modulePullbackCompIso B S hS μ κ).hom.app ((modulePullback B S hS a).obj N) ≫
        eqToHom (congrArg (fun g : P ⟶ Z =>
          (modulePullback B S hS a ⋙ modulePullback B S hS g).obj N) hκ) ≫
        ((modulePullbackCompIso B S hS κ' a).hom.app N ≫
          eqToHom (congrArg (fun g : P ⟶ Y => (modulePullback B S hS g).obj N) hc') ≫
          (modulePullbackCompIso B S hS t' w).inv.app N) := by
  have h := congrArg (fun z => z ≫ (modulePullbackCompIso B S hS t' w).inv.app N)
    (modulePullbackCompIso_eqToHom_assoc_app B S hS μ κ κ' hκ a (t' ≫ w) hd hc' N)
  simpa only [Category.assoc] using h

/-- **The head square.**  Let `κ ≫ a = t ≫ w` be two factorizations of one morphism of algebraic
spaces, let `μ` be a further morphism in front, and let `κ'` and `t'` be the two composites with
`μ`, kept as variables with their defining equations `hκ` and `ht`.  Then the *head* — the
comparison of [Stacks Project, Tag 03LU] along `κ ≫ a`, the transport along the factorization,
and the comparison along `t ≫ w` inverted — is natural in `μ`: its inverse image along `μ`,
followed by the comparison along `μ ≫ t` and the transport to `t'`, is the comparison along
`μ ≫ κ`, the transport to `κ'`, and the head at `κ'` and `t'`.

This is the head of the source-square chain of
`AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso_hom` — its first three factors,
[Stacks Project, Tag 03LU] at the chart, the transport along the factorization of the chart
composite, and Tag 03LU at the chart square inverted — and it is a statement about
`AlgebraicGeometry.Space.modulePullback` at plain variables, with nothing about charts in it.

The two tails are variables on purpose: substituting them puts both bracketings of the triple
composite into the statement, and identifying those two *across a composition* is what exhausts
the kernel budget.  Here that identification happens only in
`AlgebraicGeometry.Space.comp_eqToHom_assoc` and
`AlgebraicGeometry.Space.eqToHom_assoc_comp`, where the morphism beside it is a variable and the
two spellings meet at the level of the equation. -/
theorem modulePullbackCompIso_headSquare (μ : P ⟶ X) (κ : X ⟶ Z) (a : Z ⟶ Y) (t : X ⟶ T)
    (w : T ⟶ Y) (κ' : P ⟶ Z) (t' : P ⟶ T) (hκ : μ ≫ κ = κ') (ht : μ ≫ t = t')
    (hc : κ ≫ a = t ≫ w) (hc' : κ' ≫ a = t' ≫ w) (N : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS μ).map
          ((modulePullbackCompIso B S hS κ a).hom.app N ≫
            eqToHom (congrArg (fun g : X ⟶ Y => (modulePullback B S hS g).obj N) hc) ≫
            (modulePullbackCompIso B S hS t w).inv.app N) ≫
        (modulePullbackCompIso B S hS μ t).hom.app ((modulePullback B S hS w).obj N) ≫
        eqToHom (congrArg (fun g : P ⟶ T =>
          (modulePullback B S hS w ⋙ modulePullback B S hS g).obj N) ht) =
      (modulePullbackCompIso B S hS μ κ).hom.app ((modulePullback B S hS a).obj N) ≫
        eqToHom (congrArg (fun g : P ⟶ Z =>
          (modulePullback B S hS a ⋙ modulePullback B S hS g).obj N) hκ) ≫
        ((modulePullbackCompIso B S hS κ' a).hom.app N ≫
          eqToHom (congrArg (fun g : P ⟶ Y => (modulePullback B S hS g).obj N) hc') ≫
          (modulePullbackCompIso B S hS t' w).inv.app N) := by
  have hq : μ ≫ t ≫ w = t' ≫ w := by rw [← ht, Category.assoc]
  have hd : μ ≫ κ ≫ a = t' ≫ w := by rw [hc, hq]
  exact (headSquareLeft B S hS μ κ a t w t' ht hc N hd
      (congrArg (fun g : P ⟶ Y => (modulePullback B S hS g).obj N) hq)).trans
    (headSquareRight B S hS μ κ a t' w κ' hκ hc' N hd)

/-! ### The same two squares at the isomorphism-projection spelling

`AlgebraicGeometry.Space.chartCompositeDifferentialsAssociatedIso_hom` writes its two transports
as `CategoryTheory.eqToIso` on `hom` and as `CategoryTheory.Iso.symm` of a *component* of the
comparison, not as `CategoryTheory.eqToHom` and `.inv.app`.  An assembler fed that equation
verbatim therefore needs its squares at those spellings, and **the identification cannot be made
at the point of use**: there the two spellings meet inside a composite whose adjacent factor is a
chart-level comparison, and the kernel has to re-identify the composition junction underneath
them, which does not finish.  At plain variables it costs nothing, so the two restatements live
here. -/

/-- `AlgebraicGeometry.Space.modulePullbackCompIso_map_eqToHom_square` **with its two outer
transports taken as variables** carrying their defining equations.

The two transports are the ones a consumer's own goal spells, and it may spell them as
`CategoryTheory.eqToIso` on `hom` rather than as `CategoryTheory.eqToHom`.  Restating this square
*at* that spelling is a kernel timeout even here, at plain variables; taking each transport as a
variable and letting the consumer supply `CategoryTheory.eqToIso.hom` as its defining equation
costs nothing, because then no definitional equality is ever demanded — the two spellings meet at
the level of an equation of bare morphisms with nothing else in the term. -/
theorem modulePullbackCompIso_map_eqToHom_square' (μ : P ⟶ X) {c e : X ⟶ Y} (hc : c = e)
    (c' e' : P ⟶ Y) (hd : μ ≫ c = c') (he : μ ≫ e = e')
    (N : Modules.{u, u} B S hS Y.1 Y.2)
    (p : (modulePullback B S hS c').obj N = (modulePullback B S hS e').obj N)
    (τ : (modulePullback B S hS c).obj N ⟶ (modulePullback B S hS e).obj N)
    (hτ : τ = eqToHom (congrArg (fun g : X ⟶ Y => (modulePullback B S hS g).obj N) hc))
    (τ' : (modulePullback B S hS c').obj N ⟶ (modulePullback B S hS e').obj N)
    (hτ' : τ' = eqToHom p) :
    (modulePullback B S hS μ).map τ ≫
        ((modulePullbackCompIso B S hS μ e).hom.app N ≫
          eqToHom (congrArg (fun g : P ⟶ Y => (modulePullback B S hS g).obj N) he)) =
      ((modulePullbackCompIso B S hS μ c).hom.app N ≫
          eqToHom (congrArg (fun g : P ⟶ Y => (modulePullback B S hS g).obj N) hd)) ≫ τ' := by
  subst hτ
  subst hτ'
  exact modulePullbackCompIso_map_eqToHom_square B S hS μ hc c' e' hd he N p

/-- `AlgebraicGeometry.Space.modulePullbackCompIso_hom_app_square` with the two comparisons that
are *factors* of the chain written as `CategoryTheory.Iso.app` of the comparison followed by
`hom` — which is how `AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso_hom`
spells its first factor.  The two verticals are left at `.hom.app`, because that is the spelling
the square of the next factor along uses. -/
theorem modulePullbackCompIso_app_hom_square (μ : P ⟶ X) (χ : X ⟶ Z) (χ' : P ⟶ Z)
    (hκ : μ ≫ χ = χ') (aa : Z ⟶ Y) (hd : μ ≫ χ ≫ aa = χ' ≫ aa)
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS μ).map ((modulePullbackCompIso B S hS χ aa).app M).hom ≫
        ((modulePullbackCompIso B S hS μ (χ ≫ aa)).hom.app M ≫
          eqToHom (congrArg (fun g : P ⟶ Y => (modulePullback B S hS g).obj M) hd)) =
      ((modulePullbackCompIso B S hS μ χ).hom.app ((modulePullback B S hS aa).obj M) ≫
          eqToHom (congrArg (fun g : P ⟶ Z =>
            (modulePullback B S hS aa ⋙ modulePullback B S hS g).obj M) hκ)) ≫
        ((modulePullbackCompIso B S hS χ' aa).app M).hom := by
  simp only [Iso.app_hom]
  exact modulePullbackCompIso_hom_app_square B S hS μ χ χ' hκ aa hd M

/-- `AlgebraicGeometry.Space.headSquareInv` with the inverted comparison written as
`CategoryTheory.Iso.symm` of a component, and re-bracketed so that each vertical is a single
morphism. -/
theorem headSquareInv_app (μ : P ⟶ X) (t : X ⟶ T) (w : T ⟶ Y) (t' : P ⟶ T)
    (ht : μ ≫ t = t') (N : Modules.{u, u} B S hS Y.1 Y.2)
    (q : (modulePullback B S hS (μ ≫ t ≫ w)).obj N =
      (modulePullback B S hS (t' ≫ w)).obj N) :
    (modulePullback B S hS μ).map ((modulePullbackCompIso B S hS t w).app N).symm.hom ≫
        ((modulePullbackCompIso B S hS μ t).hom.app ((modulePullback B S hS w).obj N) ≫
          eqToHom (congrArg (fun g : P ⟶ T =>
            (modulePullback B S hS w ⋙ modulePullback B S hS g).obj N) ht)) =
      ((modulePullbackCompIso B S hS μ (t ≫ w)).hom.app N ≫ eqToHom q) ≫
        ((modulePullbackCompIso B S hS t' w).app N).symm.hom := by
  simp only [Iso.symm_hom, Iso.app_inv]
  exact (headSquareInv B S hS μ t w t' ht N q).trans (Category.assoc _ _ _).symm

end AlgebraicGeometry.Space

end
