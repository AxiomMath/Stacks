module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.AlgebraicGeometry.AffineSpace
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence

/-!
# Rational maps of algebraic spaces and the ring of rational functions

A rational map between algebraic spaces over a scheme is an equivalence class of morphisms
defined on dense open subspaces. Two representatives are equivalent if their restrictions
agree on a common dense open subspace. Relative to maps to a third algebraic space, a
rational map is over that space if it has a representative over it. A rational *function* is
a rational map to the relative affine line, and the pointwise operations on representatives
make the rational functions a commutative ring.

## Main definitions

* `AlgebraicGeometry.Space.IsDenseOpenSubspace` is an open subspace whose point set is dense.
* `AlgebraicGeometry.Space.PartialMap` is a morphism defined on a dense open subspace.
* `AlgebraicGeometry.Space.PartialMap.Equivalent` is agreement on a common dense open
  subspace.
* `AlgebraicGeometry.Space.RationalMap` is the quotient of partial maps by this equivalence.
* `AlgebraicGeometry.Space.RationalMap.IsOver` is the relative rational-map predicate.
* `AlgebraicGeometry.Space.affineLineOver` is the relative affine line as a scheme over the
  base, `AlgebraicGeometry.Space.affineLineFunctor` its functor of points on the big fppf
  site, and `AlgebraicGeometry.Space.affineLineCoordinate` the coordinate of an
  affine-line-valued point.
* `AlgebraicGeometry.Space.rationalFunctions` is the type of rational functions.

## Main results

* `AlgebraicGeometry.Space.exists_isDenseOpenSubspace_le`: two dense open subspaces of an
  algebraic space contain a common dense open subspace.
* `AlgebraicGeometry.Space.isDenseOpenSubspace_top`: the whole space is a dense open
  subspace of itself.
* `AlgebraicGeometry.Space.PartialMap.equivalence_equivalent` is part (1) of Tag 0EMM:
  agreement on a common dense open subspace is an equivalence relation.
* `AlgebraicGeometry.Space.PartialMap.toRationalMap_eq_iff` characterizes equality of
  classes.
* `AlgebraicGeometry.Space.RationalMap.exists_rep` gives a dense-open representative of
  every class.
* `AlgebraicGeometry.Space.rationalFunctionsRing` is Tag 0EMP: the commutative ring
  structure on the rational functions, characterized by the pointwise operations on the
  coordinates of representatives defined on one dense open subspace. The instance below it
  is that ring structure.

## Implementation notes

A subspace is a subfunctor. Its underlying point set is the range of the map on field-valued
point classes induced by its inclusion, and density refers to
`AlgebraicGeometry.Space.pointTopology`, the topology of Tag 03BX on the point set of Tag
03BU, installed here as a local instance. Thus the chosen big fppf site is explicit, as in
the preceding algebraic-space material. The quotient and its class map are exposed to
clients through the usual quotient API; the relative predicate asks for one representative
commuting with the two maps to the base.

The algebraicity hypothesis `hX` is a parameter of `IsDenseOpenSubspace` even though
`AlgebraicGeometry.Space.pointTopology` needs no such hypothesis, so that the predicate, the
structure of partial maps and the type of rational maps are indexed exactly as in the source
definition; it is named `_hX` where it is unused. It is *used* in the proof that two dense
open subspaces contain a common one: that is where the open subspace cut out by an open set
of points, Tag 03BZ, enters.

Transitivity is the only non-formal clause of part (1) of Tag 0EMM. The common dense open
subspace of two dense open subspaces is the one cut out by the intersection of their point
sets, which is open because the point set of an open subspace is open, and dense because the
intersection of a dense open set with a dense set is dense. Note that no irreducibility or
integrality hypothesis is needed for this, even though the source introduces rational
functions only for integral algebraic spaces: the intersection of two dense *open* sets is
dense in an arbitrary topological space. The same two facts — a common refinement, and `⊤`
as a dense open subspace — are what make the dense open subspaces a nonempty directed system
under reverse inclusion, which is how the ring structure is built.

The ring of rational functions is obtained as a direct limit, not by defining the operations
on the quotient by hand. Three private constructions carry that out, and none of them is
part of the interface of this file:

* `sectionsRing Z` is the ring of *natural families of global sections* on a presheaf `Z`:
  families assigning to a section of `Z` over an object of the site a global section of the
  underlying scheme, compatibly with restriction. It is a subring of a product of rings, so
  its commutative-ring structure is free, and `sectionsEquiv` identifies it with the
  morphisms `Z ⟶ affineLineFunctor` through `affineLineCoordinate`. The alternative — a
  commutative-ring instance on the type `Z ⟶ affineLineFunctor` itself — was rejected
  because such an instance is keyed on `Quiver.Hom` and would be attempted on every
  morphism of presheaves.
* `DenseOpen` is the dense open subspaces ordered by reverse inclusion. It is a bespoke
  structure with its own `Preorder` instance rather than `OrderDual` of a subtype of
  `Subfunctor X`, because the proof terms of the source definition — a containment of
  subfunctors — are then *syntactically* the `≤` of the index, and the projection to the
  underlying subfunctor reduces by iota on a constructor. With `OrderDual` both go through
  `Equiv` coercions which block `rw` and elaboration.
* `toDenseOpenLimit` is the resulting bijection with `Ring.DirectLimit`, along which the
  ring structure is transported by `Equiv.commRing`. Mathlib's other direct limit,
  `_root_.DirectLimit`, is literally a quotient of a sigma type by the relation of Tag 0EMM
  and would give the bijection for free, but its algebraic instances are stated through
  `FunLike`/hom-class instance arguments whose resolution needs a raised
  `maxSynthPendingDepth`, so `Ring.DirectLimit` is used instead and the bijection is proved
  by hand from `Ring.DirectLimit.exists_of` and `Ring.DirectLimit.of.zero_exact`.

Mathlib has the same notions for schemes, as `AlgebraicGeometry.Scheme.PartialMap` and
`AlgebraicGeometry.Scheme.RationalMap`; the declarations here are the algebraic-space
versions and live in the `AlgebraicGeometry.Space` namespace, so no name is shadowed.

## References

* [Stacks Project, Tag 0EMM](https://stacks.math.columbia.edu/tag/0EMM)
* [Stacks Project, Tag 0EMP](https://stacks.math.columbia.edu/tag/0EMP)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
-/

@[expose] public section

open CategoryTheory

universe w v' v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- The inclusions of subfunctors induced by two nested containments compose to the
inclusion induced by their composite. -/
private theorem homOfLe_comp_homOfLe {C : Type v} [Category.{v'} C] {F : C ⥤ Type w}
    {G₁ G₂ G₃ : Subfunctor F} (h₁ : G₁ ≤ G₂) (h₂ : G₂ ≤ G₃) :
    Subfunctor.homOfLe h₁ ≫ Subfunctor.homOfLe h₂ = Subfunctor.homOfLe (h₁.trans h₂) := rfl

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An open subspace whose underlying point set is dense in the source. -/
abbrev IsDenseOpenSubspace (_hX : IsAlgebraicSpace B S hS X) (U : Subfunctor X) : Prop :=
  IsOpenSubspace B S hS U ∧ Dense (Set.range (pointsMap B S hS U.toFunctor U.ι))

/-- Two dense open subspaces of an algebraic space over `S` contain a common dense open
subspace, namely the open subspace cut out by the intersection of their point sets. -/
theorem exists_isDenseOpenSubspace_le (hX : IsAlgebraicSpace B S hS X) {U V : Subfunctor X}
    (hU : IsDenseOpenSubspace B S hS hX U) (hV : IsDenseOpenSubspace B S hS hX V) :
    ∃ W : Subfunctor X, IsDenseOpenSubspace B S hS hX W ∧ W ≤ U ∧ W ≤ V := by
  have hUopen : IsOpen (Set.range (pointsMap B S hS U.toFunctor U.ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS U.ι hU.1.2
  have hVopen : IsOpen (Set.range (pointsMap B S hS V.toFunctor V.ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS V.ι hV.1.2
  refine ⟨openSubspaceOfPoints B S hS X (Set.range (pointsMap B S hS U.toFunctor U.ι) ∩
      Set.range (pointsMap B S hS V.toFunctor V.ι)),
    ⟨isOpenSubspace_openSubspaceOfPoints B S hS hX _ (hUopen.inter hVopen), ?_⟩,
    le_of_range_pointsMap_ι_subset B S hS hU.1 ?_,
    le_of_range_pointsMap_ι_subset B S hS hV.1 ?_⟩
  · rw [range_pointsMap_ι_openSubspaceOfPoints]
    exact hU.2.inter_of_isOpen_left hV.2 hUopen
  · rw [range_pointsMap_ι_openSubspaceOfPoints]
    exact Set.inter_subset_left
  · rw [range_pointsMap_ι_openSubspaceOfPoints]
    exact Set.inter_subset_right

/-- A morphism to `Y` defined on a dense open subspace of `X`. -/
structure PartialMap (hX : IsAlgebraicSpace B S hS X)
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  /-- The domain of the partial map. -/
  domain : Subfunctor X
  /-- The domain is a dense open subspace. -/
  dense_open_domain : IsDenseOpenSubspace B S hS hX domain
  /-- The morphism on the domain. -/
  hom : domain.toFunctor ⟶ Y

namespace PartialMap

variable {hX : IsAlgebraicSpace B S hS X}

/-- Two partial maps agree after restriction to a common dense open subspace. -/
@[stacks 0EMM "part (1): equivalence of representatives", ega "I 7.1.1" "equivalence definition"]
def Equivalent (f g : PartialMap B S hS hX Y) : Prop :=
  ∃ W : Subfunctor X,
    IsDenseOpenSubspace B S hS hX W ∧
      ∃ (hWf : W ≤ f.domain) (hWg : W ≤ g.domain),
        Subfunctor.homOfLe hWf ≫ f.hom =
          Subfunctor.homOfLe hWg ≫ g.hom

/-- **Stacks 0EMM, part (1).** Agreement on a common dense open subspace is an equivalence
relation.

Transitivity restricts to the dense open subspace common to the two witnesses, which exists
by `AlgebraicGeometry.Space.exists_isDenseOpenSubspace_le`. -/
@[stacks 0EMM "part (1): equivalence relation", ega "I 7.1.1" "is an equivalence rel."]
theorem equivalence_equivalent :
    Equivalence (Equivalent B S hS (X := X) (Y := Y) (hX := hX)) := by
  refine ⟨fun f ↦ ⟨f.domain, f.dense_open_domain, le_rfl, le_rfl, rfl⟩,
    fun ⟨W, hW, hWf, hWg, h⟩ ↦ ⟨W, hW, hWg, hWf, h.symm⟩, ?_⟩
  rintro f g k ⟨W₁, hW₁, hW₁f, hW₁g, h₁⟩ ⟨W₂, hW₂, hW₂g, hW₂k, h₂⟩
  obtain ⟨W, hW, hWW₁, hWW₂⟩ := exists_isDenseOpenSubspace_le B S hS hX hW₁ hW₂
  refine ⟨W, hW, hWW₁.trans hW₁f, hWW₂.trans hW₂k, ?_⟩
  have e₁ : Subfunctor.homOfLe (hWW₁.trans hW₁f) ≫ f.hom =
      Subfunctor.homOfLe (hWW₁.trans hW₁g) ≫ g.hom := by
    rw [← homOfLe_comp_homOfLe hWW₁ hW₁f, ← homOfLe_comp_homOfLe hWW₁ hW₁g,
      Category.assoc, Category.assoc, h₁]
  have e₂ : Subfunctor.homOfLe (hWW₂.trans hW₂g) ≫ g.hom =
      Subfunctor.homOfLe (hWW₂.trans hW₂k) ≫ k.hom := by
    rw [← homOfLe_comp_homOfLe hWW₂ hW₂g, ← homOfLe_comp_homOfLe hWW₂ hW₂k,
      Category.assoc, Category.assoc, h₂]
  rw [e₁, ← e₂]

/-- Partial maps defined on dense open subspaces, up to agreement on a common dense open
subspace. -/
instance : Setoid (PartialMap B S hS hX Y) where
  r := Equivalent B S hS
  iseqv := equivalence_equivalent B S hS

end PartialMap

/-- **Stacks 0EMM, part (2).** A rational map of algebraic spaces is a class of dense-open
representatives. -/
@[stacks 0EMM "part (2): rational maps", ega "I 7.1.2" "rational map"]
def RationalMap (hX : IsAlgebraicSpace B S hS X)
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Type _ :=
  @Quotient (PartialMap B S hS hX Y) inferInstance

namespace PartialMap

variable {hX : IsAlgebraicSpace B S hS X}

/-- The class of a dense-open representative. -/
def toRationalMap (f : PartialMap B S hS hX Y) : RationalMap B S hS hX Y := Quotient.mk _ f

/-- Two dense-open representatives have the same class as rational maps if and only if they
agree on a common dense open subspace. -/
@[simp]
theorem toRationalMap_eq_iff {f g : PartialMap B S hS hX Y} :
    toRationalMap B S hS f = toRationalMap B S hS g ↔ Equivalent B S hS f g := Quotient.eq

/-- Every rational map has a dense-open representative. -/
theorem toRationalMap_surjective :
    Function.Surjective (@toRationalMap B S hS X Y hX) :=
  Quotient.exists_rep

end PartialMap

namespace RationalMap

variable {hX : IsAlgebraicSpace B S hS X}

/-- A rational map has a representative on a dense open subspace. -/
theorem exists_rep (φ : RationalMap B S hS hX Y) :
    ∃ f : PartialMap B S hS hX Y, f.toRationalMap B S hS = φ :=
  PartialMap.toRationalMap_surjective B S hS φ

/-- **Stacks 0EMM, part (3).** A rational map is over another algebraic space if one
representative is. -/
@[stacks 0EMM "part (3): relative rational maps"]
abbrev IsOver {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (xToT : X ⟶ T) (yToT : Y ⟶ T)
    (φ : RationalMap B S hS hX Y) : Prop :=
  ∃ f : PartialMap B S hS hX Y,
    f.hom ≫ yToT = f.domain.ι ≫ xToT ∧ f.toRationalMap B S hS = φ

end RationalMap

/-! ### The ring of rational functions -/

/-- The affine line over the base scheme. -/
noncomputable abbrev affineLineOver : Over S :=
  Over.mk (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)

/-- The relative Hom functor into the affine line. -/
noncomputable abbrev affineLineFunctor :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (Over.post B.inclusion).op ⋙ yoneda.obj (affineLineOver S)

/-- The global section given by the unique coordinate of an affine-line-valued point. -/
noncomputable abbrev affineLineCoordinate
    (T : (BigFppfOver B S hS)ᵒᵖ)
    (f : (affineLineFunctor B S hS).obj T) :
    Γ((BigFppfOver.toScheme B S hS).obj T.unop, ⊤) :=
  f.left.appTop (AffineSpace.coord S (ULift.up (0 : Fin 1)))

/-- The point of the relative affine line with a prescribed coordinate. -/
public noncomputable def ofSection (T : (BigFppfOver B S hS)ᵒᵖ)
    (s : Γ((BigFppfOver.toScheme B S hS).obj T.unop, ⊤)) :
    (affineLineFunctor B S hS).obj T :=
  Over.homMk (AffineSpace.homOfVector ((Over.post B.inclusion).obj T.unop).hom (fun _ ↦ s))
    (AffineSpace.homOfVector_over _ _)

/-- The unique coordinate of the point of the relative affine line with prescribed coordinate
`s` is `s`. -/
@[simp]
public theorem affineLineCoordinate_ofSection (T : (BigFppfOver B S hS)ᵒᵖ)
    (s : Γ((BigFppfOver.toScheme B S hS).obj T.unop, ⊤)) :
    affineLineCoordinate B S hS T (ofSection B S hS T s) = s :=
  AffineSpace.homOfVector_appTop_coord _ _ _

/-- The point of the relative affine line with a prescribed coordinate recovers the point it came
from: the two components of a morphism to the relative affine line are its structure morphism over
the base and its unique coordinate. -/
public theorem ofSection_affineLineCoordinate (T : (BigFppfOver B S hS)ᵒᵖ)
    (f : (affineLineFunctor B S hS).obj T) :
    ofSection B S hS T (affineLineCoordinate B S hS T f) = f := by
  refine Over.OverMorphism.ext (AffineSpace.hom_ext ?_ ?_)
  · rw [ofSection]
    exact (AffineSpace.homOfVector_over _ _).trans (Over.w f).symm
  · intro i
    have hi : i = ULift.up (0 : Fin 1) := Subsingleton.elim _ _
    subst hi
    simp only [ofSection, Over.homMk_left]
    exact AffineSpace.homOfVector_appTop_coord _ _ _

/-- An affine-line-valued point is determined by its coordinate. -/
public theorem affineLineCoordinate_injective (T : (BigFppfOver B S hS)ᵒᵖ)
    {f g : (affineLineFunctor B S hS).obj T}
    (h : affineLineCoordinate B S hS T f = affineLineCoordinate B S hS T g) : f = g := by
  rw [← ofSection_affineLineCoordinate B S hS T f, ← ofSection_affineLineCoordinate B S hS T g, h]

/-- The coordinate of an affine-line-valued point moves by pullback of global sections. -/
public theorem affineLineCoordinate_map {T T' : (BigFppfOver B S hS)ᵒᵖ} (i : T ⟶ T')
    (f : (affineLineFunctor B S hS).obj T) :
    affineLineCoordinate B S hS T' ((affineLineFunctor B S hS).map i f) =
      ((BigFppfOver.toScheme B S hS).map i.unop).appTop (affineLineCoordinate B S hS T f) := by
  change (((Over.post B.inclusion).map i.unop).left ≫ f.left).appTop _ = _
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- The commutative ring of natural families of global sections on a presheaf over the big
fppf site of `S`: the coordinates of a morphism to the relative affine line. -/
private def sectionsRing (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    Subring (∀ T : (BigFppfOver B S hS)ᵒᵖ, Z.obj T →
      Γ((BigFppfOver.toScheme B S hS).obj T.unop, ⊤)) where
  carrier := {s | ∀ ⦃T T' : (BigFppfOver B S hS)ᵒᵖ⦄ (i : T ⟶ T') (z : Z.obj T),
    s T' (Z.map i z) = ((BigFppfOver.toScheme B S hS).map i.unop).appTop (s T z)}
  mul_mem' := by intro a b hs ht T T' i z; simp [hs i z, ht i z]
  one_mem' := by intro T T' i z; simp
  add_mem' := by intro a b hs ht T T' i z; simp [hs i z, ht i z]
  zero_mem' := by intro T T' i z; simp
  neg_mem' := by intro a hs T T' i z; simp [hs i z]

/-- The coordinate of a morphism to the relative affine line, as a bijection onto the
natural families of global sections. -/
private noncomputable def sectionsEquiv (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    (Z ⟶ affineLineFunctor B S hS) ≃ sectionsRing B S hS Z where
  toFun ν := ⟨fun T z ↦ affineLineCoordinate B S hS T (ν.app T z), by
    intro T T' i z
    rw [← affineLineCoordinate_map]
    exact congrArg _ (NatTrans.naturality_apply ν i z)⟩
  invFun s :=
    { app := fun T ↦ ↾fun z ↦ ofSection B S hS T (s.1 T z)
      naturality := by
        intro T T' i
        refine ConcreteCategory.hom_ext _ _ fun z ↦ ?_
        simp only [ConcreteCategory.comp_apply, TypeCat.ofHom_apply]
        refine affineLineCoordinate_injective B S hS T' ?_
        rw [affineLineCoordinate_ofSection, affineLineCoordinate_map,
          affineLineCoordinate_ofSection]
        exact s.2 i z }
  left_inv ν := by
    refine NatTrans.ext (funext fun T ↦ ConcreteCategory.hom_ext _ _ fun z ↦ ?_)
    exact ofSection_affineLineCoordinate B S hS T (ν.app T z)
  right_inv s := by
    refine Subtype.ext (funext fun T ↦ funext fun z ↦ ?_)
    exact affineLineCoordinate_ofSection B S hS T (s.1 T z)

/-- Restriction of natural families of global sections along a containment of subfunctors. -/
private def restrictSections {W U : Subfunctor X} (h : W ≤ U) :
    sectionsRing B S hS U.toFunctor →+* sectionsRing B S hS W.toFunctor where
  toFun s := ⟨fun T z ↦ s.1 T ((Subfunctor.homOfLe h).app T z), by
    intro T T' i z
    exact s.2 i ((Subfunctor.homOfLe h).app T z)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem restrictSections_sectionsEquiv {W U : Subfunctor X} (h : W ≤ U)
    (ν : U.toFunctor ⟶ affineLineFunctor B S hS) :
    restrictSections B S hS h (sectionsEquiv B S hS U.toFunctor ν) =
      sectionsEquiv B S hS W.toFunctor (Subfunctor.homOfLe h ≫ ν) := rfl

/-- The whole algebraic space is a dense open subspace of itself: its inclusion is an
isomorphism, hence an open immersion, and surjective on points. -/
theorem isDenseOpenSubspace_top (hX : IsAlgebraicSpace B S hS X) :
    IsDenseOpenSubspace B S hS hX ⊤ := by
  refine ⟨⟨hX.of_iso (asIso (Subfunctor.ι (⊤ : Subfunctor X))).symm,
    MorphismProperty.presheaf_of_isIso _ _⟩, ?_⟩
  have hsurj : Function.Surjective (pointsMap B S hS (⊤ : Subfunctor X).toFunctor
      (Subfunctor.ι (⊤ : Subfunctor X))) := by
    intro x
    refine ⟨pointsMap B S hS X (inv (Subfunctor.ι (⊤ : Subfunctor X))) x, ?_⟩
    rw [show pointsMap B S hS (⊤ : Subfunctor X).toFunctor (Subfunctor.ι (⊤ : Subfunctor X))
        (pointsMap B S hS X (inv (Subfunctor.ι (⊤ : Subfunctor X))) x) =
        (pointsMap B S hS (⊤ : Subfunctor X).toFunctor (Subfunctor.ι (⊤ : Subfunctor X)) ∘
          pointsMap B S hS X (inv (Subfunctor.ι (⊤ : Subfunctor X)))) x from rfl,
      ← pointsMap_comp, IsIso.inv_hom_id, pointsMap_id, id_eq]
  rw [hsurj.range_eq]
  exact dense_univ

section Limit

/-- A dense open subspace of an algebraic space, ordered by reverse inclusion. -/
private structure DenseOpen (hX : IsAlgebraicSpace B S hS X) where
  /-- The underlying subfunctor. -/
  carrier : Subfunctor X
  /-- It is a dense open subspace. -/
  isDenseOpen : IsDenseOpenSubspace B S hS hX carrier

variable {hX : IsAlgebraicSpace B S hS X}

private instance : Preorder (DenseOpen B S hS hX) where
  le U V := V.carrier ≤ U.carrier
  le_refl _ := le_rfl
  le_trans _ _ _ h₁ h₂ := h₂.trans h₁

private instance : Nonempty (DenseOpen B S hS hX) :=
  ⟨⟨⊤, isDenseOpenSubspace_top B S hS hX⟩⟩

private instance : IsDirectedOrder (DenseOpen B S hS hX) where
  directed i j := by
    obtain ⟨W, hW, hWi, hWj⟩ :=
      exists_isDenseOpenSubspace_le B S hS hX i.isDenseOpen j.isDenseOpen
    exact ⟨⟨W, hW⟩, hWi, hWj⟩

/-- The sections over a dense open subspace. -/
private abbrev denseOpenSections (i : DenseOpen B S hS hX) : Type (u + 1) :=
  sectionsRing B S hS i.carrier.toFunctor

/-- Restriction of sections to a smaller dense open subspace. -/
private abbrev denseOpenRestrict (i j : DenseOpen B S hS hX) (h : i ≤ j) :
    denseOpenSections B S hS (hX := hX) i →+* denseOpenSections B S hS (hX := hX) j :=
  restrictSections B S hS h

private instance : DirectedSystem (denseOpenSections B S hS (hX := hX))
    (fun i j h ↦ denseOpenRestrict B S hS i j h) where
  map_self := by intro i x; rfl
  map_map := by intro k j i hij hjk x; rfl

/-- The direct limit of the rings of sections over the dense open subspaces. -/
private noncomputable abbrev denseOpenLimit (hX : IsAlgebraicSpace B S hS X) : Type (u + 1) :=
  Ring.DirectLimit (denseOpenSections B S hS (hX := hX))
    (denseOpenRestrict B S hS (hX := hX) · · ·)

/-- The map from the sections over one dense open subspace to the direct limit. -/
private noncomputable abbrev denseOpenOf (i : DenseOpen B S hS hX) :
    denseOpenSections B S hS (hX := hX) i →+* denseOpenLimit B S hS hX :=
  Ring.DirectLimit.of (denseOpenSections B S hS (hX := hX))
    (denseOpenRestrict B S hS (hX := hX) · · ·) i

/-- A rational function, read as an element of the direct limit of the rings of sections
over the dense open subspaces. -/
private noncomputable def toDenseOpenLimit :
    RationalMap B S hS hX (affineLineFunctor B S hS) → denseOpenLimit B S hS hX :=
  Quotient.lift
    (fun f ↦ denseOpenOf B S hS ⟨f.domain, f.dense_open_domain⟩
      (sectionsEquiv B S hS f.domain.toFunctor f.hom))
    (by
      rintro f g ⟨W, hW, hWf, hWg, h⟩
      rw [← Ring.DirectLimit.of_f (i := (⟨f.domain, f.dense_open_domain⟩ : DenseOpen B S hS hX))
          (j := (⟨W, hW⟩ : DenseOpen B S hS hX)) hWf,
        ← Ring.DirectLimit.of_f (i := (⟨g.domain, g.dense_open_domain⟩ : DenseOpen B S hS hX))
          (j := (⟨W, hW⟩ : DenseOpen B S hS hX)) hWg]
      exact congrArg _ ((restrictSections_sectionsEquiv B S hS hWf f.hom).trans
        ((congrArg _ h).trans (restrictSections_sectionsEquiv B S hS hWg g.hom).symm)))

private theorem toDenseOpenLimit_toRationalMap (U : Subfunctor X)
    (hU : IsDenseOpenSubspace B S hS hX U) (ν : U.toFunctor ⟶ affineLineFunctor B S hS) :
    toDenseOpenLimit B S hS (PartialMap.toRationalMap B S hS
        (⟨U, hU, ν⟩ : PartialMap B S hS hX (affineLineFunctor B S hS))) =
      denseOpenOf B S hS ⟨U, hU⟩ (sectionsEquiv B S hS U.toFunctor ν) :=
  rfl

private theorem toDenseOpenLimit_bijective :
    Function.Bijective (toDenseOpenLimit B S hS (hX := hX)) := by
  constructor
  · refine fun x y ↦ Quotient.inductionOn₂ x y fun f g h ↦ ?_
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge (⟨f.domain, f.dense_open_domain⟩ : DenseOpen B S hS hX)
      (⟨g.domain, g.dense_open_domain⟩ : DenseOpen B S hS hX)
    have hzero : denseOpenOf B S hS k
        (denseOpenRestrict B S hS _ _ hik (sectionsEquiv B S hS f.domain.toFunctor f.hom) -
          denseOpenRestrict B S hS _ _ hjk
            (sectionsEquiv B S hS g.domain.toFunctor g.hom)) = 0 := by
      rwa [map_sub, Ring.DirectLimit.of_f, Ring.DirectLimit.of_f, sub_eq_zero]
    obtain ⟨l, hkl, hl⟩ := Ring.DirectLimit.of.zero_exact
      (f' := denseOpenRestrict B S hS (hX := hX)) hzero
    rw [map_sub, sub_eq_zero] at hl
    refine Quotient.sound ⟨l.carrier, l.isDenseOpen, hik.trans hkl, hjk.trans hkl,
      (sectionsEquiv B S hS l.carrier.toFunctor).injective ?_⟩
    rwa [← restrictSections_sectionsEquiv, ← restrictSections_sectionsEquiv]
  · intro z
    obtain ⟨i, x, hx⟩ := Ring.DirectLimit.exists_of z
    refine ⟨PartialMap.toRationalMap B S hS
      ⟨i.carrier, i.isDenseOpen, (sectionsEquiv B S hS i.carrier.toFunctor).symm x⟩, ?_⟩
    rwa [toDenseOpenLimit_toRationalMap, Equiv.apply_symm_apply]

/-- A rational function is a rational map to the relative affine line. -/
@[stacks 0EMN "rational functions as rational maps to the relative affine line"]
noncomputable abbrev rationalFunctions (hX : IsAlgebraicSpace B S hS X) : Type (u + 1) :=
  RationalMap B S hS hX (affineLineFunctor B S hS)

/-- **Stacks 0EMP.** Pointwise ring operations on common dense-open representatives
determine the commutative ring structure on rational functions.

The ring is the direct limit of the rings of sections over the dense open subspaces, which
is a directed system because two dense open subspaces contain a common one. -/
@[stacks 0EMP]
theorem rationalFunctionsRing (hX : IsAlgebraicSpace B S hS X) :
    ∃ R : CommRing (rationalFunctions B S hS hX),
      letI := R
      (∀ (U : Subfunctor X) (hU : IsDenseOpenSubspace B S hS hX U)
          (f g : U.toFunctor ⟶ affineLineFunctor B S hS),
        ∃ a m : U.toFunctor ⟶ affineLineFunctor B S hS,
          (∀ T x, affineLineCoordinate B S hS T (a.app T x) =
            affineLineCoordinate B S hS T (f.app T x) +
              affineLineCoordinate B S hS T (g.app T x)) ∧
          (∀ T x, affineLineCoordinate B S hS T (m.app T x) =
            affineLineCoordinate B S hS T (f.app T x) *
              affineLineCoordinate B S hS T (g.app T x)) ∧
          (PartialMap.toRationalMap B S hS
            (⟨U, hU, a⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)) =
            PartialMap.toRationalMap B S hS
              (⟨U, hU, f⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)) +
            PartialMap.toRationalMap B S hS
              (⟨U, hU, g⟩ : PartialMap B S hS hX (affineLineFunctor B S hS))) ∧
          (PartialMap.toRationalMap B S hS
            (⟨U, hU, m⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)) =
            PartialMap.toRationalMap B S hS
              (⟨U, hU, f⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)) *
            PartialMap.toRationalMap B S hS
              (⟨U, hU, g⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)))) ∧
      (∀ (U : Subfunctor X) (hU : IsDenseOpenSubspace B S hS hX U),
        ∃ z o : U.toFunctor ⟶ affineLineFunctor B S hS,
          (∀ T x, affineLineCoordinate B S hS T (z.app T x) = 0) ∧
          (∀ T x, affineLineCoordinate B S hS T (o.app T x) = 1) ∧
          (PartialMap.toRationalMap B S hS
            (⟨U, hU, z⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)) = 0) ∧
          (PartialMap.toRationalMap B S hS
            (⟨U, hU, o⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)) = 1)) ∧
      (∀ (U : Subfunctor X) (hU : IsDenseOpenSubspace B S hS hX U)
          (f : U.toFunctor ⟶ affineLineFunctor B S hS),
        ∃ n : U.toFunctor ⟶ affineLineFunctor B S hS,
          (∀ T x, affineLineCoordinate B S hS T (n.app T x) =
            -affineLineCoordinate B S hS T (f.app T x)) ∧
          (PartialMap.toRationalMap B S hS
            (⟨U, hU, n⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)) =
            -PartialMap.toRationalMap B S hS
              (⟨U, hU, f⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)))) := by
  let e : rationalFunctions B S hS hX ≃ denseOpenLimit B S hS hX :=
    Equiv.ofBijective _ (toDenseOpenLimit_bijective B S hS (hX := hX))
  let R : CommRing (rationalFunctions B S hS hX) := e.commRing
  have hadd : ∀ x y : rationalFunctions B S hS hX, e (x + y) = e x + e y :=
    fun _ _ ↦ e.apply_symm_apply _
  have hmul : ∀ x y : rationalFunctions B S hS hX, e (x * y) = e x * e y :=
    fun _ _ ↦ e.apply_symm_apply _
  have hneg : ∀ x : rationalFunctions B S hS hX, e (-x) = -e x :=
    fun _ ↦ e.apply_symm_apply _
  have hzero : e (0 : rationalFunctions B S hS hX) = 0 := e.apply_symm_apply 0
  have hone : e (1 : rationalFunctions B S hS hX) = 1 := e.apply_symm_apply 1
  have hmk : ∀ (U : Subfunctor X) (hU : IsDenseOpenSubspace B S hS hX U)
      (ν : U.toFunctor ⟶ affineLineFunctor B S hS),
      e (PartialMap.toRationalMap B S hS
          (⟨U, hU, ν⟩ : PartialMap B S hS hX (affineLineFunctor B S hS))) =
        denseOpenOf B S hS ⟨U, hU⟩ (sectionsEquiv B S hS U.toFunctor ν) :=
    toDenseOpenLimit_toRationalMap B S hS
  have hsymm : ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (s : sectionsRing B S hS Z)
      (T : (BigFppfOver B S hS)ᵒᵖ) (x : Z.obj T),
      affineLineCoordinate B S hS T (((sectionsEquiv B S hS Z).symm s).app T x) = s.1 T x :=
    fun Z s T x ↦ affineLineCoordinate_ofSection B S hS T (s.1 T x)
  refine ⟨R, fun U hU f g ↦ ?_, fun U hU ↦ ?_, fun U hU f ↦ ?_⟩
  · refine ⟨(sectionsEquiv B S hS U.toFunctor).symm
        (sectionsEquiv B S hS U.toFunctor f + sectionsEquiv B S hS U.toFunctor g),
      (sectionsEquiv B S hS U.toFunctor).symm
        (sectionsEquiv B S hS U.toFunctor f * sectionsEquiv B S hS U.toFunctor g),
      fun T x ↦ hsymm _ _ T x, fun T x ↦ hsymm _ _ T x, ?_, ?_⟩
    · refine e.injective ?_
      rw [hadd, hmk, hmk, hmk, Equiv.apply_symm_apply]
      exact map_add (denseOpenOf B S hS _) _ _
    · refine e.injective ?_
      rw [hmul, hmk, hmk, hmk, Equiv.apply_symm_apply]
      exact map_mul (denseOpenOf B S hS _) _ _
  · refine ⟨(sectionsEquiv B S hS U.toFunctor).symm 0,
      (sectionsEquiv B S hS U.toFunctor).symm 1,
      fun T x ↦ hsymm _ _ T x, fun T x ↦ hsymm _ _ T x, ?_, ?_⟩
    · refine e.injective ?_
      rw [hzero, hmk, Equiv.apply_symm_apply]
      exact (denseOpenOf B S hS ⟨U, hU⟩).map_zero
    · refine e.injective ?_
      rw [hone, hmk, Equiv.apply_symm_apply]
      exact (denseOpenOf B S hS ⟨U, hU⟩).map_one
  · refine ⟨(sectionsEquiv B S hS U.toFunctor).symm (-(sectionsEquiv B S hS U.toFunctor f)),
      fun T x ↦ hsymm _ _ T x, ?_⟩
    refine e.injective ?_
    rw [hneg, hmk, hmk, Equiv.apply_symm_apply]
    exact map_neg (denseOpenOf B S hS ⟨U, hU⟩) _

/-- The canonical commutative ring of rational functions. -/
noncomputable instance (hX : IsAlgebraicSpace B S hS X) :
    CommRing (rationalFunctions B S hS hX) :=
  (rationalFunctionsRing B S hS hX).choose

end Limit

end AlgebraicGeometry.Space

end
