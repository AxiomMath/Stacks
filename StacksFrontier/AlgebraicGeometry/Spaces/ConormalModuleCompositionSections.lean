module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIsoComparison

/-!
# Pasting the square comparisons of two stacked squares of closed subspaces

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
|        |
f'       g'
↓        ↓
Z'' i''→ X''
```
be two vertically composable commutative squares of algebraic spaces over a scheme `S` contained
in a big fppf site `B`, with `Z ⊆ X`, `Z' ⊆ X'` and `Z'' ⊆ X''` closed subspaces.  Each square
carries the identification `f^*(i')^* ≅ i^*g^*` of inverse-image functors of
`AlgebraicGeometry.Space.conormalPullbackCompIso`, which is the comparison factor of the
canonical map of conormal modules of [Stacks Project, Tag 04CP].  This file proves that those
identifications **paste**: the one attached to the outer rectangle, read through the composition
comparison `AlgebraicGeometry.Space.modulePullbackCompIso` of [Stacks Project, Tag 03LU] on each
of the two vertical edges, is the one of the lower square followed by the one of the upper
square.

This is the comparison-isomorphism half of the composition formula of
[Stacks Project, Tag 04G2], part (3): that formula is the pasting below combined with the
corresponding composition law for the map of defining ideal sheaves.

## Main results

* `AlgebraicGeometry.Space.modulePullbackCompIso_assoc_app`,
  `AlgebraicGeometry.Space.modulePullbackCompIso_assoc_inv`,
  `AlgebraicGeometry.Space.modulePullbackCompIso_inv_comp_whiskerRight_hom`: the associativity
  coherence of [Stacks Project, Tag 03LU] for the comparison of inverse images, in the three
  forms the pasting consumes.
* `AlgebraicGeometry.Space.conormalPullbackCompIso_hom`: the square comparison written out as the
  comparison along the upper edge, the transport along the commutativity of the square, and the
  inverse of the comparison along the lower edge.
* `AlgebraicGeometry.Space.conormalPullbackCompIso_paste`: **the pasting of the two square
  comparisons.**
* `AlgebraicGeometry.Space.conormalPullbackCompIso_paste_app`: the same at a module, with the
  pasted composite left unexpanded.

## Implementation notes

Everything is proved at the level of natural transformations of inverse-image functors, and the
two transports along the commutativity of a square are moved past the composition comparisons by
`AlgebraicGeometry.Space.modulePullbackCompIso_inv_eqToHom_right` and
`AlgebraicGeometry.Space.modulePullbackCompIso_inv_eqToHom_left`, after which the three
transports compose to the one of the outer rectangle by `CategoryTheory.eqToHom_trans`.

The pasted composite of `AlgebraicGeometry.Space.conormalPullbackCompIso_paste_app` is left as a
single natural transformation evaluated at the module rather than expanded into its three
factors: the expanded statement, written out, is not accepted at the default budget, while each
of its factors in isolation is.

The cost does not come from the expansion mixing the two spellings `(F ⋙ G).obj M` and
`F.obj (G.obj M)` of one object inside a single composite: at these inverse images the two spellings
of an object are
`rfl` and instant, so is a composition one of whose ends carries each, and so is transporting an
equation of morphisms across them.  What is not free is *declaring* the expanded type.  A
consumer that needs the three factors separately gets them by composing this lemma with
`CategoryTheory.NatTrans.comp_app`, `CategoryTheory.Functor.whiskerLeft_app` and
`CategoryTheory.Functor.whiskerRight_app` as **terms**, leaving the type of the composite
inferred — that costs seconds — and never by stating the expansion or by rewriting with those
lemmas, neither of which the pattern matcher fires here.

The same unfolding is why the rewrites of the right-hand side of
`AlgebraicGeometry.Space.conormalPullbackCompIso_paste` are entered with `conv` so that each
pattern sits at the root of the goal.  `rw` attempts its keyed match at the outermost
composition first, and matching a factor of the pattern against an unrelated factor of the
composite drives the whole of `AlgebraicGeometry.Space.modulePullbackCompIso` open, through
`CategoryTheory.Adjunction.leftAdjointUniq` and on down to sheafification: rewriting
at the whole composite is rejected with `(deterministic) timeout at isDefEq`, while the same
rewrites with their patterns entered are accepted in seconds.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

/-- A commutative square two of whose edges are invertible, read with the two invertible edges
moved to the other side. -/
private theorem inv_comp_eq_comp_inv {D : Type*} [Category D] {P Q R T : D}
    (A : P ≅ Q) (u : P ⟶ R) (v : Q ⟶ T) (E : R ≅ T) (h : A.hom ≫ v = u ≫ E.hom) :
    A.inv ≫ u = v ≫ E.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Whiskering cancels a composite of the two directions of an isomorphism. -/
private theorem whiskerLeft_inv_hom_assoc {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) {G H : D ⥤ E} (e : G ≅ H) {T : C ⥤ E} (h : F ⋙ H ⟶ T) :
    Functor.whiskerLeft F e.inv ≫ Functor.whiskerLeft F e.hom ≫ h = h := by
  rw [← Category.assoc, ← Functor.whiskerLeft_comp, Iso.inv_hom_id, Functor.whiskerLeft_id',
    Category.id_comp]

/-- Whiskering cancels a composite of the two directions of an isomorphism.  This is the
statement of `whiskerLeft_inv_hom_assoc` as a declaration downstream modules may use. -/
public alias whiskerLeft_inv_hom_cancel := whiskerLeft_inv_hom_assoc

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Coherence of the composition comparison of inverse images -/

section Coherence

variable {W Y Y' Y'' : AlgebraicSpaces B S hS}

/-- The associativity coherence of the composition comparison, at a module. -/
theorem modulePullbackCompIso_assoc_app (a : W ⟶ Y) (b : Y ⟶ Y') (c : Y' ⟶ Y'')
    (M : Modules.{u, u} B S hS Y''.1 Y''.2) :
    (modulePullbackCompIso B S hS a b).hom.app ((modulePullback B S hS c).obj M) ≫
        (modulePullbackCompIso B S hS (a ≫ b) c).hom.app M =
      (modulePullback B S hS a).map ((modulePullbackCompIso B S hS b c).hom.app M) ≫
        (modulePullbackCompIso B S hS a (b ≫ c)).hom.app M := by
  have h := NatTrans.congr_app
    (congrArg Iso.hom (modulePullbackCompIso_assoc B S hS a b c)) M
  simpa using h

/-- The associativity coherence of the composition comparison, inverted, at a module. -/
theorem modulePullbackCompIso_assoc_inv_app (a : W ⟶ Y) (b : Y ⟶ Y') (c : Y' ⟶ Y'')
    (M : Modules.{u, u} B S hS Y''.1 Y''.2) :
    (modulePullbackCompIso B S hS (a ≫ b) c).inv.app M ≫
        (modulePullbackCompIso B S hS a b).inv.app ((modulePullback B S hS c).obj M) =
      (modulePullbackCompIso B S hS a (b ≫ c)).inv.app M ≫
        (modulePullback B S hS a).map ((modulePullbackCompIso B S hS b c).inv.app M) := by
  have h := NatTrans.congr_app
    (congrArg Iso.inv (modulePullbackCompIso_assoc B S hS a b c)) M
  simpa using h

/-- The associativity coherence of the composition comparison, with the two comparisons along
the outer morphism inverted, at a module. -/
theorem modulePullbackCompIso_inv_comp_map_hom_app (a : W ⟶ Y) (b : Y ⟶ Y') (c : Y' ⟶ Y'')
    (M : Modules.{u, u} B S hS Y''.1 Y''.2) :
    (modulePullbackCompIso B S hS a b).inv.app ((modulePullback B S hS c).obj M) ≫
        (modulePullback B S hS a).map ((modulePullbackCompIso B S hS b c).hom.app M) =
      (modulePullbackCompIso B S hS (a ≫ b) c).hom.app M ≫
        (modulePullbackCompIso B S hS a (b ≫ c)).inv.app M :=
  inv_comp_eq_comp_inv
    ((modulePullbackCompIso B S hS a b).app ((modulePullback B S hS c).obj M))
    ((modulePullback B S hS a).map ((modulePullbackCompIso B S hS b c).hom.app M))
    ((modulePullbackCompIso B S hS (a ≫ b) c).hom.app M)
    ((modulePullbackCompIso B S hS a (b ≫ c)).app M)
    (modulePullbackCompIso_assoc_app B S hS a b c M)

/-- The associativity coherence of the composition comparison, with the two comparisons along
the *inner* morphism inverted, at a module.  This is
`AlgebraicGeometry.Space.modulePullbackCompIso_inv_comp_map_hom_app` read on the inverses, and
it is the form in which the inverse comparison standing at the head of a composite — the shape
`AlgebraicGeometry.Space.chartCompositeDifferentialsAssociatedIso` has — is moved to the
outside. -/
theorem modulePullbackCompIso_map_inv_comp_hom_app (a : W ⟶ Y) (b : Y ⟶ Y') (c : Y' ⟶ Y'')
    (M : Modules.{u, u} B S hS Y''.1 Y''.2) :
    (modulePullback B S hS a).map ((modulePullbackCompIso B S hS b c).inv.app M) ≫
        (modulePullbackCompIso B S hS a b).hom.app ((modulePullback B S hS c).obj M) =
      (modulePullbackCompIso B S hS a (b ≫ c)).hom.app M ≫
        (modulePullbackCompIso B S hS (a ≫ b) c).inv.app M := by
  exact inv_comp_eq_comp_inv
    ((modulePullback B S hS a).mapIso ((modulePullbackCompIso B S hS b c).app M))
    ((modulePullbackCompIso B S hS a b).hom.app ((modulePullback B S hS c).obj M))
    ((modulePullbackCompIso B S hS a (b ≫ c)).hom.app M)
    ((modulePullbackCompIso B S hS (a ≫ b) c).app M)
    (modulePullbackCompIso_assoc_app B S hS a b c M).symm

/-- **The associativity coherence of the composition comparison across an equality of the outer
composite.**  For `μ ≫ χ = χ'`, comparing the inverse image along `χ` of the comparison for
`χ ≫ aa` with the comparison for `μ` and then transporting along the equality is comparing for
`μ` and `χ`, transporting, and comparing for `χ'` and `aa`.

This is `AlgebraicGeometry.Space.modulePullbackCompIso_assoc_app` followed by the transport of
the comparison along an equality of its outer morphism; it is stated with the two transports
written as `CategoryTheory.eqToHom` of the equalities of inverse-image functors they come from,
which is the shape a consumer comparing two charts of one algebraic space meets. -/
theorem modulePullbackCompIso_map_hom_app_comp_eqToHom (μ : W ⟶ Y) (χ : Y ⟶ Y') (χ' : W ⟶ Y')
    (hμ : μ ≫ χ = χ') (aa : Y' ⟶ Y'') (M : Modules.{u, u} B S hS Y''.1 Y''.2) :
    (modulePullback B S hS μ).map ((modulePullbackCompIso B S hS χ aa).hom.app M) ≫
        (modulePullbackCompIso B S hS μ (χ ≫ aa)).hom.app M ≫
          eqToHom (congrArg (fun g : W ⟶ Y'' => (modulePullback B S hS g).obj M)
            (congrArg (fun g : W ⟶ Y' => g ≫ aa) hμ)) =
      (modulePullbackCompIso B S hS μ χ).hom.app ((modulePullback B S hS aa).obj M) ≫
        eqToHom (congrArg (fun g : W ⟶ Y' =>
          (modulePullback B S hS g).obj ((modulePullback B S hS aa).obj M)) hμ) ≫
        (modulePullbackCompIso B S hS χ' aa).hom.app M := by
  subst hμ
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  exact (modulePullbackCompIso_assoc_app B S hS μ χ aa M).symm

/-- The associativity coherence of the composition comparison, inverted. -/
@[reassoc]
theorem modulePullbackCompIso_assoc_inv (a : W ⟶ Y) (b : Y ⟶ Y') (c : Y' ⟶ Y'') :
    (modulePullbackCompIso B S hS (a ≫ b) c).inv ≫
        Functor.whiskerLeft (modulePullback B S hS c)
          (modulePullbackCompIso B S hS a b).inv =
      (modulePullbackCompIso B S hS a (b ≫ c)).inv ≫
        Functor.whiskerRight (modulePullbackCompIso B S hS b c).inv
          (modulePullback B S hS a) := by
  refine NatTrans.ext (funext fun M ↦ ?_)
  simpa using modulePullbackCompIso_assoc_inv_app B S hS a b c M

/-- The associativity coherence of the composition comparison, with the two comparisons along
the outer morphism inverted. -/
@[reassoc]
theorem modulePullbackCompIso_inv_comp_whiskerRight_hom (a : W ⟶ Y) (b : Y ⟶ Y')
    (c : Y' ⟶ Y'') :
    Functor.whiskerLeft (modulePullback B S hS c) (modulePullbackCompIso B S hS a b).inv ≫
        Functor.whiskerRight (modulePullbackCompIso B S hS b c).hom
          (modulePullback B S hS a) =
      (modulePullbackCompIso B S hS (a ≫ b) c).hom ≫
        (modulePullbackCompIso B S hS a (b ≫ c)).inv := by
  refine NatTrans.ext (funext fun M ↦ ?_)
  simpa using modulePullbackCompIso_inv_comp_map_hom_app B S hS a b c M

/-- The composition comparison transported along an equality of the inner morphism. -/
@[reassoc]
theorem modulePullbackCompIso_inv_eqToHom_right (a : W ⟶ Y) {b b' : Y ⟶ Y''} (p : b = b') :
    (modulePullbackCompIso B S hS a b).inv ≫
        Functor.whiskerRight
          (eqToHom (congrArg (fun h : Y ⟶ Y'' ↦ modulePullback B S hS h) p))
          (modulePullback B S hS a) =
      eqToHom (congrArg (fun h : W ⟶ Y'' ↦ modulePullback B S hS h)
          (congrArg (fun h : Y ⟶ Y'' ↦ a ≫ h) p)) ≫
        (modulePullbackCompIso B S hS a b').inv := by
  subst p
  simp

/-- The composition comparison transported along an equality of the outer morphism. -/
@[reassoc]
theorem modulePullbackCompIso_inv_eqToHom_left {a a' : W ⟶ Y} (p : a = a') (b : Y ⟶ Y'') :
    (modulePullbackCompIso B S hS a b).inv ≫
        Functor.whiskerLeft (modulePullback B S hS b)
          (eqToHom (congrArg (fun h : W ⟶ Y ↦ modulePullback B S hS h) p)) =
      eqToHom (congrArg (fun h : W ⟶ Y'' ↦ modulePullback B S hS h)
          (congrArg (fun h : W ⟶ Y ↦ h ≫ b) p)) ≫
        (modulePullbackCompIso B S hS a' b).inv := by
  subst p
  simp

end Coherence

/-! ### Pasting the square comparisons of two stacked squares -/

variable {X X' X'' : AlgebraicSpaces B S hS}

/-- The square comparison of `AlgebraicGeometry.Space.conormalPullbackCompIso`, written out. -/
theorem conormalPullbackCompIso_hom (Z : ClosedSubspaces B S hS X.1)
    (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z') :
    (conormalPullbackCompIso B S hS Z Z' g f hsq).hom =
      (modulePullbackCompIso B S hS f (subspaceInclusion B S hS X' Z')).hom ≫
        eqToHom (congrArg
          (fun h : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X' ↦
            modulePullback B S hS h) hsq.symm) ≫
        (modulePullbackCompIso B S hS (subspaceInclusion B S hS X Z) g).inv := by
  rw [conormalPullbackCompIso]
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom]

variable (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1)
    (Z'' : ClosedSubspaces B S hS X''.1) (g : X ⟶ X') (g' : X' ⟶ X'')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (f' : (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (hsq' : subspaceInclusion B S hS X' Z' ≫ g' = f' ≫ subspaceInclusion B S hS X'' Z'')
    (hsq'' : subspaceInclusion B S hS X Z ≫ g ≫ g' =
      (f ≫ f') ≫ subspaceInclusion B S hS X'' Z'')

/-- **The square comparisons of two vertically stacked squares paste.** -/
theorem conormalPullbackCompIso_paste :
    (conormalPullbackCompIso B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'').hom ≫
        Functor.whiskerRight (modulePullbackCompIso B S hS g g').inv
          (modulePullback B S hS (subspaceInclusion B S hS X Z)) =
      Functor.whiskerLeft (modulePullback B S hS (subspaceInclusion B S hS X'' Z''))
          (modulePullbackCompIso B S hS f f').inv ≫
        Functor.whiskerRight (conormalPullbackCompIso B S hS Z' Z'' g' f' hsq').hom
          (modulePullback B S hS f) ≫
        Functor.whiskerLeft (modulePullback B S hS g')
          (conormalPullbackCompIso B S hS Z Z' g f hsq).hom := by
  rw [conormalPullbackCompIso_hom, conormalPullbackCompIso_hom, conormalPullbackCompIso_hom,
    Functor.whiskerRight_comp, Functor.whiskerRight_comp, Functor.whiskerLeft_comp,
    Functor.whiskerLeft_comp]
  simp only [Category.assoc]
  conv_lhs => rw [← modulePullbackCompIso_assoc_inv B S hS (subspaceInclusion B S hS X Z) g g']
  conv_rhs =>
    rw [modulePullbackCompIso_inv_comp_whiskerRight_hom_assoc B S hS f f'
        (subspaceInclusion B S hS X'' Z''),
      modulePullbackCompIso_inv_eqToHom_right_assoc B S hS f hsq'.symm]
    enter [2, 2]
    rw [← modulePullbackCompIso_assoc_inv_assoc B S hS f (subspaceInclusion B S hS X' Z') g']
    enter [2]
    rw [whiskerLeft_inv_hom_assoc]
  conv_rhs =>
    enter [2, 2]
    rw [modulePullbackCompIso_inv_eqToHom_left_assoc B S hS hsq.symm g']
  conv_rhs =>
    enter [2]
    rw [eqToHom_trans_assoc]

/-- **The pasting of the two square comparisons, at a module.**  The comparison of the outer
rectangle, followed by the inverse image along the inclusion of `Z` of the composition comparison
of the two lower edges, is the pasted composite of the comparisons of the two squares.

The pasted composite is left as a single natural transformation evaluated at `M`; see the
implementation notes of this file for why it is not expanded into its three factors here. -/
theorem conormalPullbackCompIso_paste_app (M : Modules.{u, u} B S hS X''.1 X''.2) :
    (conormalPullbackCompIso B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'').hom.app M ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          ((modulePullbackCompIso B S hS g g').inv.app M) =
      (Functor.whiskerLeft (modulePullback B S hS (subspaceInclusion B S hS X'' Z''))
            (modulePullbackCompIso B S hS f f').inv ≫
          Functor.whiskerRight (conormalPullbackCompIso B S hS Z' Z'' g' f' hsq').hom
            (modulePullback B S hS f) ≫
          Functor.whiskerLeft (modulePullback B S hS g')
            (conormalPullbackCompIso B S hS Z Z' g f hsq).hom).app M :=
  (congrArg
      (fun t ↦ (conormalPullbackCompIso B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'').hom.app M ≫ t)
      (Functor.whiskerRight_app (modulePullbackCompIso B S hS g g').inv
        (modulePullback B S hS (subspaceInclusion B S hS X Z)) M).symm).trans
    ((NatTrans.comp_app (conormalPullbackCompIso B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'').hom
          (Functor.whiskerRight (modulePullbackCompIso B S hS g g').inv
            (modulePullback B S hS (subspaceInclusion B S hS X Z))) M).symm.trans
      (NatTrans.congr_app
        (conormalPullbackCompIso_paste B S hS Z Z' Z'' g g' f f' hsq hsq' hsq'') M))

end AlgebraicGeometry.Space

end
