module

public import StacksFrontier.Algebra.Homology.DualComplexOfSignedMateDuals
public import StacksFrontier.Algebra.Homology.SignedDualComplex

/-!
# Functoriality of the signed dual complex

Given a complex `K` in a monoidal preadditive category, a family of objects `D` and pairings `q`
exhibiting `D j` as a dual of `K^{-j}`, `CochainComplex.dualComplex K D q` is the complex whose
differential is the signed transpose of that of `K`. A morphism `φ : K ⟶ K'` induces a morphism
of the dual complexes **in the opposite direction**, the assignment is functorial, and a diagram
of complexes with duals therefore has a diagram of dual complexes over the opposite index
category.

The degreewise map is the *unsigned* mate: no sign appears, because the signs of the two
differentials are the same `(-1)^n` and cancel. All the content is
`CategoryTheory.ExactPairing.comp_mate` — Mathlib's `CategoryTheory.comp_rightAdjointMate`,
the statement that taking mates is an anti-homomorphism — read twice against the commuting square
`d_K ≫ φ^{n+1} = φ^n ≫ d_{K'}`.

## Main definitions

* `CochainComplex.dualMate`: the mate of `φ^n`, read as a map of the degree-`j` terms of the two
  dual families with `n + j = 0`. Indexing the pairings by that equation is what keeps the index
  flip `j ↦ -j` transport-free, as in `CochainComplex.signedTransposeIn`.
* `CochainComplex.dualComplexMap`: **the induced morphism `D'^• ⟶ D^•` of dual complexes.**
* `CochainComplex.dualComplexMapIso`: the induced isomorphism, for `φ` an isomorphism.
* `CochainComplex.dualDiagram`: **the diagram of dual complexes** of a diagram
  `F : J ⥤ CochainComplex C ℤ` of complexes with duals, a functor `Jᵒᵖ ⥤ CochainComplex C ℤ`.
  For `J = ℕ` this turns a direct system of complexes into an inverse system (an `ℕᵒᵖ`-diagram)
  of dual complexes.
* `CochainComplex.dualDiagramMap` and `CochainComplex.dualDiagramIso`: a morphism, resp. an
  isomorphism, of such diagrams is carried to one of the diagrams of duals.

## Main results

* `CochainComplex.dualMate_comp_signedTransposeAt`: **the mate of `φ` commutes with the signed
  transposes.** This is the whole mathematical content, and it is two applications of
  `CategoryTheory.ExactPairing.comp_mate`.
* `CochainComplex.dualComplexMap_id` and `CochainComplex.dualComplexMap_comp`: the assignment is
  functorial, contravariantly.

## Implementation notes

**Why no sign.** `CochainComplex.signedTransposeAt` is `(-1)^n` times the mate of
`d_K^{n,n+1}`. In the square to be checked both differentials carry the same `(-1)^n`, so the
factor is pulled out of both sides by `CategoryTheory.Linear.units_smul_comp` and
`CategoryTheory.Linear.comp_units_smul` and cancelled; what is left is the unsigned statement
`(φ^{n+1})^∨ ≫ (d_K)^∨ = (d_{K'})^∨ ≫ (φ^n)^∨`, which is `comp_mate` applied to the two
factorisations of `(d_K ≫ φ^{n+1})^∨ = (φ^n ≫ d_{K'})^∨`. A signed degreewise map would *not*
give a chain map.

**The index flip.** `CochainComplex.dualMate` takes the degree `n` of the complexes and the
degree `j` of the dual families as separate arguments together with `n + j = 0`, exactly as
`CochainComplex.signedTransposeIn` does, so that the pairings `q n j` and `q' n j` apply on the
nose and no `eqToHom` is needed anywhere. `CochainComplex.dualComplexMapX` specialises to
`n = -j`, and `CochainComplex.dualComplexMapX_eq` moves between the two spellings, mirroring
`CochainComplex.dualD_eq`.

**Direction of the diagram.** `CochainComplex.dualDiagram` takes `F : J ⥤ CochainComplex C ℤ`
to a functor out of `Jᵒᵖ`. A tower `ℕᵒᵖ ⥤ CochainComplex C ℤ` of dual complexes therefore comes
from a *direct* system `ℕ ⥤ CochainComplex C ℤ`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory GradedObject

noncomputable section

universe v u

namespace CategoryTheory.ExactPairing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **The mate of an identity is an identity.** -/
@[simp]
theorem mate_id {X X' : C} (p : ExactPairing X X') : mate p p (𝟙 X) = 𝟙 X' :=
  @rightAdjointMate_id C _ _ X (hasRightDual p)

end CategoryTheory.ExactPairing

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C]

section Degreewise

variable (K : CochainComplex C ℤ) (D : ℤ → C)
  (q : ∀ i j : ℤ, i + j = 0 → ExactPairing (K.X i) (D j))
  (K' : CochainComplex C ℤ) (D' : ℤ → C)
  (q' : ∀ i j : ℤ, i + j = 0 → ExactPairing (K'.X i) (D' j))
  (φ : K ⟶ K')

omit [MonoidalPreadditive C] in
/-- `CochainComplex.signedTransposeAt` with the two pairings named rather than packaged as
`CategoryTheory.HasRightDual` instances. -/
theorem signedTransposeAt_eq_mate (n : ℤ) :
    signedTransposeAt K D q n =
      (n.negOnePow : ℤˣ) • ExactPairing.mate (dualPairing K D q n) (dualPairing K D q (n + 1))
        (K.d n (n + 1)) :=
  rfl

/-- **The mate of `φ^n`**, read as a morphism from the degree-`j` term of the dual family of `K'`
to the degree-`j` term of the dual family of `K`, the degree `n` of the two complexes being
pinned to `-j` by the equation. No sign appears: the mate of a degree-preserving map needs
none. -/
def dualMate (n j : ℤ) (h : n + j = 0) : D' j ⟶ D j :=
  ExactPairing.mate (q n j h) (q' n j h) (φ.f n)

/-- The degree-`j` component of the induced morphism of dual complexes. -/
def dualComplexMapX (j : ℤ) : D' j ⟶ D j :=
  dualMate K D q K' D' q' φ (-j) j (by omega)

omit [MonoidalPreadditive C] in
/-- The degree-`j` component of the induced morphism, with the degree of the complexes whose map
it transposes supplied as a parameter. -/
theorem dualComplexMapX_eq (n j : ℤ) (h : n + j = 0) :
    dualComplexMapX K D q K' D' q' φ j = dualMate K D q K' D' q' φ n j h := by
  obtain rfl : n = -j := by omega
  rfl

omit [MonoidalPreadditive C] in
/-- `CochainComplex.dualMate` at the degrees it is designed for, with the two pairings spelled as
`CochainComplex.dualPairing`. -/
theorem dualMate_eq_mate_dualPairing (n : ℤ) (h : n + -n = 0) :
    dualMate K D q K' D' q' φ n (-n) h =
      ExactPairing.mate (dualPairing K D q n) (dualPairing K' D' q' n) (φ.f n) :=
  rfl

omit [MonoidalPreadditive C] in
/-- **The mate of `φ` commutes with the signed transposes.** Both signed transposes carry the
same sign `(-1)^n`, which cancels; what remains is the two readings of the mate of the commuting
square of `φ` with the differentials, by `CategoryTheory.ExactPairing.comp_mate`. -/
theorem dualMate_comp_signedTransposeAt (n : ℤ) :
    ExactPairing.mate (dualPairing K D q (n + 1)) (dualPairing K' D' q' (n + 1)) (φ.f (n + 1)) ≫
        signedTransposeAt K D q n =
      signedTransposeAt K' D' q' n ≫
        ExactPairing.mate (dualPairing K D q n) (dualPairing K' D' q' n) (φ.f n) := by
  have h1 := ExactPairing.comp_mate (dualPairing K D q n) (dualPairing K D q (n + 1))
    (dualPairing K' D' q' (n + 1)) (K.d n (n + 1)) (φ.f (n + 1))
  have h2 := ExactPairing.comp_mate (dualPairing K D q n) (dualPairing K' D' q' n)
    (dualPairing K' D' q' (n + 1)) (φ.f n) (K'.d n (n + 1))
  unfold signedTransposeAt
  rw [Linear.comp_units_smul, Linear.units_smul_comp]
  exact congrArg _ (h1.symm.trans ((congrArg _ (φ.comm n (n + 1)).symm).trans h2))

omit [MonoidalPreadditive C] in
/-- **The induced degreewise maps commute with the differentials of the dual complexes.** -/
theorem dualComplexMapX_comp_dualD (n i j : ℤ) (hi : n + 1 + i = 0) (hj : n + j = 0) :
    dualComplexMapX K D q K' D' q' φ i ≫ dualD K D q i j =
      dualD K' D' q' i j ≫ dualComplexMapX K D q K' D' q' φ j := by
  obtain rfl : i = -(n + 1) := by omega
  obtain rfl : j = -n := by omega
  rw [dualD_eq K D q n _ _ (by omega) (by omega), dualD_eq K' D' q' n _ _ (by omega) (by omega),
    signedTransposeIn_eq, signedTransposeIn_eq,
    dualComplexMapX_eq K D q K' D' q' φ (n + 1) (-(n + 1)) (by omega),
    dualComplexMapX_eq K D q K' D' q' φ n (-n) (by omega),
    dualMate_eq_mate_dualPairing, dualMate_eq_mate_dualPairing]
  exact dualMate_comp_signedTransposeAt K D q K' D' q' φ n

/-- **The morphism of dual complexes induced by a morphism of complexes**, in the opposite
direction. Its degree-`j` component is the mate of `φ^{-j}`. -/
def dualComplexMap : dualComplex K' D' q' ⟶ dualComplex K D q where
  f j := dualComplexMapX K D q K' D' q' φ j
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    exact dualComplexMapX_comp_dualD K D q K' D' q' φ (-j) i j (by omega) (by omega)

/-- The components of the induced morphism of dual complexes. -/
@[simp]
theorem dualComplexMap_f (j : ℤ) :
    (dualComplexMap K D q K' D' q' φ).f j = dualComplexMapX K D q K' D' q' φ j :=
  rfl

end Degreewise

section Functorial

variable (K : CochainComplex C ℤ) (D : ℤ → C)
  (q : ∀ i j : ℤ, i + j = 0 → ExactPairing (K.X i) (D j))

omit [MonoidalPreadditive C] in
/-- The degreewise map induced by the identity is the identity. -/
@[simp]
theorem dualComplexMapX_id (j : ℤ) : dualComplexMapX K D q K D q (𝟙 K) j = 𝟙 (D j) :=
  ExactPairing.mate_id (q (-j) j (by omega))

/-- **The morphism of dual complexes induced by the identity is the identity.** -/
@[simp]
theorem dualComplexMap_id : dualComplexMap K D q K D q (𝟙 K) = 𝟙 (dualComplex K D q) := by
  ext j
  exact dualComplexMapX_id K D q j

variable (K' : CochainComplex C ℤ) (D' : ℤ → C)
  (q' : ∀ i j : ℤ, i + j = 0 → ExactPairing (K'.X i) (D' j))
  (φ : K ⟶ K')
  (K'' : CochainComplex C ℤ) (D'' : ℤ → C)
  (q'' : ∀ i j : ℤ, i + j = 0 → ExactPairing (K''.X i) (D'' j))
  (ψ : K' ⟶ K'')

omit [MonoidalPreadditive C] in
/-- The degreewise map induced by a composite is the composite of the induced maps, in the other
order. -/
theorem dualComplexMapX_comp (j : ℤ) :
    dualComplexMapX K D q K'' D'' q'' (φ ≫ ψ) j =
      dualComplexMapX K' D' q' K'' D'' q'' ψ j ≫ dualComplexMapX K D q K' D' q' φ j :=
  ExactPairing.comp_mate (q (-j) j (by omega)) (q' (-j) j (by omega)) (q'' (-j) j (by omega))
    (φ.f (-j)) (ψ.f (-j))

/-- **The morphism of dual complexes induced by a composite is the composite of the induced
morphisms, in the other order.** -/
theorem dualComplexMap_comp :
    dualComplexMap K D q K'' D'' q'' (φ ≫ ψ) =
      dualComplexMap K' D' q' K'' D'' q'' ψ ≫ dualComplexMap K D q K' D' q' φ := by
  ext j
  exact dualComplexMapX_comp K D q K' D' q' φ K'' D'' q'' ψ j

end Functorial

section Square

variable (A : CochainComplex C ℤ) (DA : ℤ → C)
  (qA : ∀ i j : ℤ, i + j = 0 → ExactPairing (A.X i) (DA j))
  (B : CochainComplex C ℤ) (DB : ℤ → C)
  (qB : ∀ i j : ℤ, i + j = 0 → ExactPairing (B.X i) (DB j))
  (A' : CochainComplex C ℤ) (DA' : ℤ → C)
  (qA' : ∀ i j : ℤ, i + j = 0 → ExactPairing (A'.X i) (DA' j))
  (B' : CochainComplex C ℤ) (DB' : ℤ → C)
  (qB' : ∀ i j : ℤ, i + j = 0 → ExactPairing (B'.X i) (DB' j))

/-- **A commuting square of complexes with duals dualises to a commuting square.** -/
theorem dualComplexMap_square (u : B ⟶ A) (u' : B' ⟶ A') (a : A ⟶ A') (b : B ⟶ B')
    (h : u ≫ a = b ≫ u') :
    dualComplexMap B' DB' qB' A' DA' qA' u' ≫ dualComplexMap B DB qB B' DB' qB' b =
      dualComplexMap A DA qA A' DA' qA' a ≫ dualComplexMap B DB qB A DA qA u := by
  rw [← dualComplexMap_comp B DB qB B' DB' qB' b A' DA' qA' u',
    ← dualComplexMap_comp B DB qB A DA qA u A' DA' qA' a, h]

end Square

section Iso

variable (K : CochainComplex C ℤ) (D : ℤ → C)
  (q : ∀ i j : ℤ, i + j = 0 → ExactPairing (K.X i) (D j))
  (K' : CochainComplex C ℤ) (D' : ℤ → C)
  (q' : ∀ i j : ℤ, i + j = 0 → ExactPairing (K'.X i) (D' j))
  (e : K ≅ K')

/-- **An isomorphism of complexes induces an isomorphism of the dual complexes**, in the opposite
direction. -/
def dualComplexMapIso : dualComplex K' D' q' ≅ dualComplex K D q where
  hom := dualComplexMap K D q K' D' q' e.hom
  inv := dualComplexMap K' D' q' K D q e.inv
  hom_inv_id := by
    rw [← dualComplexMap_comp K' D' q' K D q e.inv K' D' q' e.hom, e.inv_hom_id,
      dualComplexMap_id]
  inv_hom_id := by
    rw [← dualComplexMap_comp K D q K' D' q' e.hom K D q e.inv, e.hom_inv_id,
      dualComplexMap_id]

/-- The forward map of `dualComplexMapIso` is the dual map of `e.hom`. -/
@[simp]
theorem dualComplexMapIso_hom :
    (dualComplexMapIso K D q K' D' q' e).hom = dualComplexMap K D q K' D' q' e.hom :=
  rfl

/-- The inverse map of `dualComplexMapIso` is the dual map of `e.inv`. -/
@[simp]
theorem dualComplexMapIso_inv :
    (dualComplexMapIso K D q K' D' q' e).inv = dualComplexMap K' D' q' K D q e.inv :=
  rfl

end Iso

section Diagram

variable {J : Type*} [Category J] (F : J ⥤ CochainComplex C ℤ) (D : J → ℤ → C)
  (q : ∀ (a : J) (i j : ℤ), i + j = 0 → ExactPairing ((F.obj a).X i) (D a j))

/-- **The diagram of dual complexes of a diagram of complexes with duals.** The dual of the
complex at `a` sits at `a`, and the transition maps run in the opposite direction, so this is a
functor out of `Jᵒᵖ`. Taking `J = ℕ` turns a direct system of complexes into an inverse system
(an `ℕᵒᵖ`-diagram, a tower) of dual complexes. -/
def dualDiagram : Jᵒᵖ ⥤ CochainComplex C ℤ where
  obj a := dualComplex (F.obj a.unop) (D a.unop) (q a.unop)
  map {a b} f := dualComplexMap (F.obj b.unop) (D b.unop) (q b.unop)
    (F.obj a.unop) (D a.unop) (q a.unop) (F.map f.unop)
  map_id a := by
    rw [show (𝟙 a : a ⟶ a).unop = 𝟙 a.unop from rfl, F.map_id]
    exact dualComplexMap_id (F.obj a.unop) (D a.unop) (q a.unop)
  map_comp {a b c} f g := by
    rw [show (f ≫ g).unop = g.unop ≫ f.unop from rfl, F.map_comp]
    exact dualComplexMap_comp (F.obj c.unop) (D c.unop) (q c.unop)
      (F.obj b.unop) (D b.unop) (q b.unop) (F.map g.unop)
      (F.obj a.unop) (D a.unop) (q a.unop) (F.map f.unop)

/-- The value of `dualDiagram` at `a` is the dual complex of `F.obj a.unop`. -/
@[simp]
theorem dualDiagram_obj (a : Jᵒᵖ) :
    (dualDiagram F D q).obj a = dualComplex (F.obj a.unop) (D a.unop) (q a.unop) :=
  rfl

/-- The transition map of `dualDiagram` along `f` is the dual map of `F.map f.unop`. -/
@[simp]
theorem dualDiagram_map {a b : Jᵒᵖ} (f : a ⟶ b) :
    (dualDiagram F D q).map f = dualComplexMap (F.obj b.unop) (D b.unop) (q b.unop)
      (F.obj a.unop) (D a.unop) (q a.unop) (F.map f.unop) :=
  rfl

variable (F' : J ⥤ CochainComplex C ℤ) (D' : J → ℤ → C)
  (q' : ∀ (a : J) (i j : ℤ), i + j = 0 → ExactPairing ((F'.obj a).X i) (D' a j))

/-- **A morphism of diagrams of complexes induces a morphism of the diagrams of dual
complexes**, in the opposite direction. -/
def dualDiagramMap (e : F ⟶ F') : dualDiagram F' D' q' ⟶ dualDiagram F D q where
  app a := dualComplexMap (F.obj a.unop) (D a.unop) (q a.unop)
    (F'.obj a.unop) (D' a.unop) (q' a.unop) (e.app a.unop)
  naturality a b f :=
    dualComplexMap_square (F.obj a.unop) (D a.unop) (q a.unop) (F.obj b.unop) (D b.unop)
      (q b.unop) (F'.obj a.unop) (D' a.unop) (q' a.unop) (F'.obj b.unop) (D' b.unop)
      (q' b.unop) (F.map f.unop) (F'.map f.unop) (e.app a.unop) (e.app b.unop)
      (e.naturality f.unop)

/-- The component of `dualDiagramMap` at `a` is the dual map of `e.app a.unop`. -/
@[simp]
theorem dualDiagramMap_app (e : F ⟶ F') (a : Jᵒᵖ) :
    (dualDiagramMap F D q F' D' q' e).app a = dualComplexMap (F.obj a.unop) (D a.unop)
      (q a.unop) (F'.obj a.unop) (D' a.unop) (q' a.unop) (e.app a.unop) :=
  rfl

/-- **An objectwise isomorphism of diagrams of complexes upgrades to an isomorphism of the
diagrams of dual complexes.** -/
def dualDiagramIso (e : F ≅ F') : dualDiagram F' D' q' ≅ dualDiagram F D q :=
  NatIso.ofComponents
    (fun a => dualComplexMapIso (F.obj a.unop) (D a.unop) (q a.unop)
      (F'.obj a.unop) (D' a.unop) (q' a.unop) (e.app a.unop))
    (fun {_ _} f => (dualDiagramMap F D q F' D' q' e.hom).naturality f)

/-- The forward map of `dualDiagramIso` is `dualDiagramMap` of `e.hom`. -/
@[simp]
theorem dualDiagramIso_hom (e : F ≅ F') :
    (dualDiagramIso F D q F' D' q' e).hom = dualDiagramMap F D q F' D' q' e.hom :=
  rfl

/-- The inverse map of `dualDiagramIso` is `dualDiagramMap` of `e.inv`. -/
@[simp]
theorem dualDiagramIso_inv (e : F ≅ F') :
    (dualDiagramIso F D q F' D' q' e).inv = dualDiagramMap F' D' q' F D q e.inv :=
  rfl

end Diagram

end CochainComplex

end

end
