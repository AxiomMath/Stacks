module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.RepresentedPolarizedFunctor
public import StacksFrontier.CategoryTheory.Bicategory.CoGrothendieckInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcChartFullness

/-!
# The inverse image along a square, in the language of Stacks 04W5

The fibre of the inverse image of a morphism of triples
(`CategoryTheory.Pseudofunctor.CoGrothendieck.squareFiber` at the pseudofunctor of modules on
algebraic spaces) is the inverse image of the given morphism of modules followed by the canonical
comparison of the two iterated inverse images of Stacks 04W5
(`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison`).

## Main results

* `AlgebraicGeometry.Space.modulesPseudofunctor_mapComp'_inv_app` and
  `AlgebraicGeometry.Space.modulesPseudofunctor_mapComp'_hom_app`: the components of the
  comparisons of the pseudofunctor along a factorization are the comparisons of an inverse image
  with an iterated inverse image of Stacks 03LU.
* `AlgebraicGeometry.Space.squareFiber_modulesPseudofunctor`: the inverse image along a square.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.inverseImage_map_fiber_eq_squareFiber`: the fibre
  of the inverse image of a morphism of triples is an inverse image along a square, to which
  `AlgebraicGeometry.Space.squareFiber_modulesPseudofunctor` applies.

## Implementation notes

The fibre categories of the pseudofunctor are the categories of modules, but only after unfolding
the pseudofunctor, so a composite in a fibre category and the same composite of modules carry
category structures that are equal only by unfolding. Comparing such composites makes the kernel
unfold the category structure of sheaves of modules, which is unaffordable as soon as one factor
is itself a composite or a transport `eqToHom` precedes a component. Every identification below
therefore passes from one language to the other one morphism at a time: each factor is identified
with a single morphism of modules (a component of a comparison of Stacks 03LU, or one of its
inverses), and the composites are only ever formed in one language. The common composite of a
factorization is kept as a variable and substituted, so that no transport between the two
spellings `f.op.toLoc ≫ q.op.toLoc` and `(q ≫ f).op.toLoc` of a composite ever has to be compared
across the languages.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-- The hom of the `2`-isomorphism of `Cat` attached to the inverse of a natural isomorphism. -/
theorem CategoryTheory.Cat.Hom.isoMk_symm_hom_toNatTrans.{v₀, u₀} {C D : Type u₀}
    [Category.{v₀} C] [Category.{v₀} D] {F G : C ⥤ D} (e : F ≅ G) :
    (Cat.Hom.isoMk (F := G) (G := F) e.symm).hom.toNatTrans = e.inv :=
  rfl

/-- The inverse image along a square, with the two comparisons replaced by given morphisms. -/
theorem CategoryTheory.Pseudofunctor.CoGrothendieck.squareFiber_eq_of {B : Type*}
    [Bicategory B] [Bicategory.Strict B] (F : Pseudofunctor B Cat)
    {x x' y y' : B} (q : x ⟶ y) (q' : x' ⟶ y') (f : x' ⟶ x) (g : y' ⟶ y)
    (k : x' ⟶ y) (h₁ : f ≫ q = k) (h₂ : q' ≫ g = k) {Y : F.obj x} {Y' : F.obj x'}
    (φ : Y ⟶ (F.map f).toFunctor.obj Y')
    (A : (F.map f ≫ F.map q).toFunctor.obj Y' ⟶ (F.map k).toFunctor.obj Y')
    (C : (F.map k).toFunctor.obj Y' ⟶ (F.map q' ≫ F.map g).toFunctor.obj Y')
    (hA : (F.mapComp' f q k h₁).inv.toNatTrans.app Y' = A)
    (hC : (F.mapComp' q' g k h₂).hom.toNatTrans.app Y' = C) :
    squareFiber F q q' f g k h₁ h₂ φ = (F.map q).toFunctor.map φ ≫ (A ≫ C) := by
  subst hA hC
  rfl

/-- The fibre of the inverse image of a morphism of triples is the inverse image along the square
of the morphism. -/
theorem CategoryTheory.Pseudofunctor.CoGrothendieck.inverseImage_map_fiber_eq_squareFiber
    {𝒮 : Type*} [Category 𝒮] {𝒟 : Type*} [Category 𝒟]
    (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat) (G : 𝒟 ⥤ 𝒮) {c c' : Comma G (forget F)}
    (m : c ⟶ c') :
    ((inverseImage F G).map m).fiber =
      squareFiber F c.hom.op.toLoc c'.hom.op.toLoc m.right.base.op.toLoc (G.map m.left).op.toLoc
        (c.hom ≫ m.right.base).op.toLoc rfl (inverseImage_square F G m) m.right.fiber :=
  rfl

namespace AlgebraicGeometry.Space

-- Elaboration compares the inverse images of the pseudofunctor with the functors themselves
-- without unfolding the latter.
attribute [local irreducible] modulePullback modulePullbackCompIso

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- If a component of the inverse of an isomorphism in `Cat` is the hom of an isomorphism, then the
same component of its hom is the inverse of that isomorphism. -/
private theorem hom_toNatTrans_app_eq_inv {C D : Cat.{u, u}} {F G : C ⟶ D} (e : F ≅ G) (M : C)
    (i : G.toFunctor.obj M ≅ F.toFunctor.obj M) (h : e.inv.toNatTrans.app M = i.hom) :
    e.hom.toNatTrans.app M = i.inv := by
  rw [← cancel_mono i.hom, i.inv_hom_id, ← h]
  simp

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The inverse of the composition comparison of the pseudofunctor of modules at a module is the
comparison of Stacks 03LU. -/
theorem modulesPseudofunctor_mapComp_inv_app {X Y Z : AlgebraicSpaces B S hS} (q : Z ⟶ Y)
    (f : Y ⟶ X) (M : (modulesPseudofunctor B S hS).obj ⟨Opposite.op X⟩) :
    ((modulesPseudofunctor B S hS).mapComp f.op.toLoc q.op.toLoc).inv.toNatTrans.app M =
      (modulePullbackCompIso B S hS q f).hom.app M :=
  (congrArg (fun e => NatTrans.app (Cat.Hom₂.toNatTrans (Iso.inv e)) M)
      (show (modulesPseudofunctor B S hS).mapComp f.op.toLoc q.op.toLoc =
        Cat.Hom.isoMk (modulePullbackCompIso B S hS q f).symm from rfl)).trans
    (congrArg (fun x => NatTrans.app x M)
      (Cat.Hom.isoMk_symm_inv_toNatTrans (modulePullbackCompIso B S hS q f)))

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The composition comparison of the pseudofunctor of modules at a module is the inverse of the
comparison of Stacks 03LU. -/
theorem modulesPseudofunctor_mapComp_hom_app {X Y Z : AlgebraicSpaces B S hS} (q : Z ⟶ Y)
    (f : Y ⟶ X) (M : (modulesPseudofunctor B S hS).obj ⟨Opposite.op X⟩) :
    ((modulesPseudofunctor B S hS).mapComp f.op.toLoc q.op.toLoc).hom.toNatTrans.app M =
      (modulePullbackCompIso B S hS q f).inv.app M :=
  hom_toNatTrans_app_eq_inv ((modulesPseudofunctor B S hS).mapComp f.op.toLoc q.op.toLoc) M
    ((modulePullbackCompIso B S hS q f).app M) (modulesPseudofunctor_mapComp_inv_app q f M)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **The inverse of the comparison of the pseudofunctor of modules along a factorization
`q ≫ f = k`** is the inverse of the comparison of the inverse image along `k` with the iterated
inverse image (Stacks 03LU). -/
theorem modulesPseudofunctor_mapComp'_inv_app {X Y Z : AlgebraicSpaces B S hS} (q : Z ⟶ Y)
    (f : Y ⟶ X) (k : Z ⟶ X) (hk : q ≫ f = k) (hF : f.op.toLoc ≫ q.op.toLoc = k.op.toLoc)
    (M : (modulesPseudofunctor B S hS).obj ⟨Opposite.op X⟩) :
    ((modulesPseudofunctor B S hS).mapComp' f.op.toLoc q.op.toLoc k.op.toLoc hF).inv.toNatTrans.app
        M = (QuasiCoherentDescent.pullbackComparison B S hS q f k hk M).inv := by
  subst hk
  refine (Pseudofunctor.CoGrothendieck.mapComp'_inv_app_eq (modulesPseudofunctor B S hS)
    f.op.toLoc q.op.toLoc _ hF M).trans ?_
  refine (congrArg (fun x => x ≫ eqToHom _) (modulesPseudofunctor_mapComp_inv_app q f M)).trans ?_
  refine ((congrArg (fun x => _ ≫ x) (eqToHom_refl _ _)).trans (Category.comp_id _)).trans ?_
  refine Eq.symm ((congrArg Iso.inv (QuasiCoherentDescent.pullbackComparison_rfl q f M)).trans ?_)
  exact (Iso.symm_inv _).trans (Iso.app_hom _ _)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **The comparison of the pseudofunctor of modules along a factorization `q ≫ f = k`** is the
comparison of the inverse image along `k` with the iterated inverse image (Stacks 03LU). -/
theorem modulesPseudofunctor_mapComp'_hom_app {X Y Z : AlgebraicSpaces B S hS} (q : Z ⟶ Y)
    (f : Y ⟶ X) (k : Z ⟶ X) (hk : q ≫ f = k) (hF : f.op.toLoc ≫ q.op.toLoc = k.op.toLoc)
    (M : (modulesPseudofunctor B S hS).obj ⟨Opposite.op X⟩) :
    ((modulesPseudofunctor B S hS).mapComp' f.op.toLoc q.op.toLoc k.op.toLoc hF).hom.toNatTrans.app
        M = (QuasiCoherentDescent.pullbackComparison B S hS q f k hk M).hom :=
  hom_toNatTrans_app_eq_inv
    ((modulesPseudofunctor B S hS).mapComp' f.op.toLoc q.op.toLoc k.op.toLoc hF) M
    (QuasiCoherentDescent.pullbackComparison B S hS q f k hk M).symm
    (modulesPseudofunctor_mapComp'_inv_app q f k hk hF M)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **The inverse image along a square is the inverse image followed by the canonical
comparison of Stacks 04W5.** For a commutative square `q ≫ f = k = g ≫ q'` of algebraic spaces
and `φ : M ⟶ f^*M'`, the fibre of the inverse image of `(g, (f, φ))` is
`q^*φ ≫ (q^*f^*M' ≅ g^*q'^*M')`. -/
theorem squareFiber_modulesPseudofunctor {X X' Z Z' : AlgebraicSpaces B S hS}
    (q : Z ⟶ X) (q' : Z' ⟶ X') (f : X ⟶ X') (g : Z ⟶ Z') (k : Z ⟶ X') (hk₁ : q ≫ f = k)
    (hk₂ : g ≫ q' = k) (h₁ : f.op.toLoc ≫ q.op.toLoc = k.op.toLoc)
    (h₂ : q'.op.toLoc ≫ g.op.toLoc = k.op.toLoc)
    {M : (modulesPseudofunctor B S hS).obj ⟨Opposite.op X⟩}
    {M' : (modulesPseudofunctor B S hS).obj ⟨Opposite.op X'⟩}
    (φ : M ⟶ ((modulesPseudofunctor B S hS).map f.op.toLoc).toFunctor.obj M') :
    Pseudofunctor.CoGrothendieck.squareFiber (modulesPseudofunctor B S hS) q.op.toLoc
        q'.op.toLoc f.op.toLoc g.op.toLoc k.op.toLoc h₁ h₂ φ =
      ((modulesPseudofunctor B S hS).map q.op.toLoc).toFunctor.map φ ≫
        (QuasiCoherentDescent.canonicalComparison q g f q' (hk₁.trans hk₂.symm) M').hom := by
  refine (Pseudofunctor.CoGrothendieck.squareFiber_eq_of (modulesPseudofunctor B S hS) _ _ _ _ _
    h₁ h₂ φ _ _ (modulesPseudofunctor_mapComp'_inv_app q f k hk₁ h₁ M')
    (modulesPseudofunctor_mapComp'_hom_app g q' k hk₂ h₂ M')).trans
    (congrArg (fun x => _ ≫ x) ?_)
  refine Eq.trans ?_ (congrArg Iso.hom
    (QuasiCoherentDescent.canonicalComparison_eq_pullbackComparison B S hS q g f q'
      (hk₁.trans hk₂.symm) k hk₁ hk₂ M')).symm
  refine Eq.trans ?_ (Iso.trans_hom _ _).symm
  exact congrArg (fun x => x ≫ _) (Iso.symm_hom _).symm

end AlgebraicGeometry.Space

end
