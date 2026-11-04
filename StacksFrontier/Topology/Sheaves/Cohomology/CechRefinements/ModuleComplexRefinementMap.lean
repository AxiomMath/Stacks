module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.ComparisonToDerivedSections
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.DerivedGlobalSections
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Homology.DerivedIndexing.Extend
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Čech refinement map of an `f`-map of sheaves of modules

Let `f : X ⟶ Y` be a morphism of ringed spaces, let `U` be an open covering of `X`, let `V` be
an open covering of `Y`, and let `c` be a refinement function, so that `U i ⊆ f⁻¹(V (c i))` for
every `i`.  An `f`-map `φ : f^* G ⟶ F` of sheaves of modules then induces a morphism

`Č•(V, G) ⟶ Č•(U, F)`

of Čech complexes, `Γ(Y, 𝒪_Y)`-linearly: a `V`-cochain is carried to the `U`-cochain whose
value on an intersection `U i₀ ∩ ⋯ ∩ U iₙ` is the image under `φ` of the value on
`V (c i₀) ∩ ⋯ ∩ V (c iₙ)`, restricted along the inclusion the refinement provides.  This is the
map `γ` of the first paragraph of the proof of [Stacks, Tag 01FD].

## Main definitions

* `Stacks.CategoryTheory.CechComplex.refinementMap`: the general construction, for a functor
  `T : D ⥤ C` between categories with finite products, families `U : I → C` and `V : J → D`,
  presheaves `P` on `C` and `Q` on `D`, a natural map `Q ⟶ T.op ⋙ P` and a refinement
  function with a compatible family of intersection maps.
* `Stacks.CategoryTheory.CechComplex.coefficientsIso`: applying an additive functor that
  preserves the relevant products to the coefficients commutes with forming the Čech complex.
* `Stacks.Cohomology.CechRefinement.cechComplexRefinementMap`: the map `γ` on the
  module-valued Čech complexes of [Stacks, Tag 01EQ], in natural degrees.
* `Stacks.Cohomology.CechRefinement.cechComplexRefinementMapInt`: the same in integer degrees,
  after extension by zero.

## Main results

* `Stacks.Cohomology.CechRefinement.cechComplexRefinementMap_comp_map_π`: the degreewise
  formula.
* `Stacks.Cohomology.CechRefinement.cechComplexRefinementMap_naturality`: naturality in the
  pair `(F, G)` of coefficient sheaves.

## Implementation notes

The general `refinementMap` is defined degreewise through
`Stacks.CategoryTheory.CechComplex.lift`, and commutes with the Čech differentials because
`Stacks.CategoryTheory.CechComplex.d_comp_π` presents the differential as the alternating sum
of restrictions along `Stacks.CategoryTheory.CechComplex.interMap`.  The compatibility of the
intersection maps with those reindexings is automatic when `C` is thin, which is the case for a
slice category of a lattice of opens, so no coherence datum has to be supplied.

The `f`-map is kept in its adjoint form `f^* G ⟶ F`, matching
`AlgebraicGeometry.RingedSpaceModuleAdjunction.homEquiv`; the adjoint `G ⟶ f_* F` is read off
that bijection and composed with `pushforwardSectionsIso`, which identifies the sections of a
pushforward over the slice over `Y` with the sections over the inverse-image slice, scalars
restricted to `Γ(Y, 𝒪_Y)`.  Both sides of that isomorphism restrict scalars along a composite
of two ring maps, and the two composites agree by naturality of `f^♯`, so
`ModuleCat.restrictScalarsComp'App` builds the comparison with no transport of module
structures.

## References

* [Stacks Project, Tag 01FD](https://stacks.math.columbia.edu/tag/01FD)
* [Stacks Project, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf (SectionRing coverObject sectionsPresheaf
  sectionsPresheafFunctor inter_coverObject_left)
open Stacks.Cohomology.CechDerived (cechComplexNatFunctor cechComplexIntFunctor)

attribute [local implicit_reducible] TopCat.Sheaf
attribute [local implicit_reducible] structureSheafRing
attribute [local implicit_reducible] Stacks.Cohomology.CechSheaf.sectionsPresheaf
attribute [local implicit_reducible] Stacks.Cohomology.CechSheaf.cechComplexFunctorOfCover
attribute [local implicit_reducible] Stacks.Cohomology.CechDerived.cechComplexNatFunctor
attribute [local implicit_reducible] Stacks.Cohomology.CechDerived.cechComplexIntFunctor
attribute [local implicit_reducible] ComplexShape.Embedding.extendFunctor
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf
open RingedSpaceModuleAdjunction (structureSheafHom modulePushforward modulePullback homEquiv)

universe vA vB vC vD uA uB uC uD uI uJ u

namespace Stacks.CategoryTheory.CechComplex

noncomputable section

section Functoriality

variable {C : Type uC} [Category.{vC} C] [HasFiniteProducts C]
  {A : Type uA} [Category.{vA} A] [Preadditive A] {I : Type uI} [HasProducts.{uI} A]
  (U : I → C)

/-- A morphism of presheaves acts componentwise on the Čech complex. -/
@[reassoc (attr := simp)]
theorem map_f_comp_π {P Q : Cᵒᵖ ⥤ A} (θ : P ⟶ Q) (n : ℕ) (x : Fin (n + 1) → I) :
    ((cechComplexFunctor U).map θ).f n ≫ π U Q n x =
      π U P n x ≫ θ.app (op (inter U x)) :=
  limMap_π _ _

end Functoriality

/-! ### The Čech complex of a refinement -/

section Refinement

variable {C : Type uC} [Category.{vC} C] [HasFiniteProducts C] [Quiver.IsThin C]
  {D : Type uD} [Category.{vD} D] [HasFiniteProducts D]
  {A : Type uA} [Category.{vA} A] [Preadditive A]
  [HasProducts.{uI} A] [HasProducts.{uJ} A]
  {I : Type uI} {J : Type uJ} (U : I → C) (V : J → D) (T : D ⥤ C)
  (P : Cᵒᵖ ⥤ A) (Q : Dᵒᵖ ⥤ A) (η : Q ⟶ T.op ⋙ P) (c : I → J)
  (r : ∀ (n : ℕ) (x : Fin (n + 1) → I), inter U x ⟶ T.obj (inter V (c ∘ x)))

/-- The degree-`n` component of the Čech complex map of a refinement: on the factor indexed by
`x` it is the value of `η` at `inter V (c ∘ x)`, restricted along `r n x`. -/
def refinementMapF (n : ℕ) :
    ((cechComplexFunctor V).obj Q).X n ⟶ ((cechComplexFunctor U).obj P).X n :=
  lift U P fun x ↦ π V Q n (c ∘ x) ≫ η.app (op (inter V (c ∘ x))) ≫ P.map (r n x).op

omit [Quiver.IsThin C] in
/-- The factor of `refinementMapF` indexed by `x` is the projection to the factor indexed by
`c ∘ x`, followed by `η` and restriction along `r n x`. -/
@[reassoc (attr := simp)]
theorem refinementMapF_comp_π (n : ℕ) (x : Fin (n + 1) → I) :
    refinementMapF U V T P Q η c r n ≫ π U P n x =
      π V Q n (c ∘ x) ≫ η.app (op (inter V (c ∘ x))) ≫ P.map (r n x).op :=
  lift_comp_π U P _ x

omit [HasProducts.{uJ} A] in
/-- The restriction maps supplied by a refinement are compatible with the reindexings that
occur in the Čech differential: in a thin category there is nothing to check. -/
theorem r_comp_interMap (n : ℕ) (y : Fin (n + 2) → I) (i : Fin (n + 2)) :
    r (n + 1) y ≫ T.map (interMap V (c ∘ y) i.succAbove) =
      interMap U y i.succAbove ≫ r n (y ∘ i.succAbove) :=
  Subsingleton.elim _ _

/-- The degreewise maps of a refinement commute with the Čech differentials. -/
theorem refinementMapF_comm (n : ℕ) :
    refinementMapF U V T P Q η c r n ≫ ((cechComplexFunctor U).obj P).d n (n + 1) =
      ((cechComplexFunctor V).obj Q).d n (n + 1) ≫
        refinementMapF U V T P Q η c r (n + 1) := by
  refine hom_ext U P fun y ↦ ?_
  have hL : (refinementMapF U V T P Q η c r n ≫ ((cechComplexFunctor U).obj P).d n (n + 1)) ≫
      π U P (n + 1) y =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (π V Q n (c ∘ (y ∘ i.succAbove)) ≫
        η.app (op (inter V (c ∘ (y ∘ i.succAbove)))) ≫
          P.map (r n (y ∘ i.succAbove)).op ≫ P.map (interMap U y i.succAbove).op) := by
    rw [Category.assoc, d_comp_π, Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Preadditive.comp_zsmul, refinementMapF_comp_π_assoc]
  have hR : (((cechComplexFunctor V).obj Q).d n (n + 1) ≫
      refinementMapF U V T P Q η c r (n + 1)) ≫ π U P (n + 1) y =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (π V Q n (c ∘ (y ∘ i.succAbove)) ≫
        η.app (op (inter V (c ∘ (y ∘ i.succAbove)))) ≫
          P.map (r n (y ∘ i.succAbove)).op ≫ P.map (interMap U y i.succAbove).op) := by
    rw [Category.assoc, refinementMapF_comp_π, ← Category.assoc, d_comp_π,
      Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Preadditive.zsmul_comp, Category.assoc]
    refine congrArg (fun z ↦ (-1 : ℤ) ^ (i : ℕ) • z) ?_
    have hη := η.naturality (interMap V (c ∘ y) i.succAbove).op
    have key : Q.map (interMap V (c ∘ y) i.succAbove).op ≫
        η.app (op (inter V (c ∘ y))) ≫ P.map (r (n + 1) y).op =
        η.app (op (inter V ((c ∘ y) ∘ i.succAbove))) ≫
          P.map (r n (y ∘ i.succAbove)).op ≫ P.map (interMap U y i.succAbove).op := by
      rw [← Category.assoc, hη, Category.assoc]
      simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op]
      rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp,
        r_comp_interMap U V T c r n y i]
    rw [key]
    rfl
  rw [hL, hR]

/-- **The Čech complex of a refinement.** Given a functor `T : D ⥤ C`, a map `c : I → J` of
index sets, maps `r n x : inter U x ⟶ T (inter V (c ∘ x))` and a natural map
`η : Q ⟶ T.op ⋙ P` of coefficients, this is the induced morphism of Čech complexes
`Č•(V, Q) ⟶ Č•(U, P)`: on the factor indexed by `x` it is the value of `η` at
`inter V (c ∘ x)` followed by the restriction along `r n x`.

This is the general shape of the map `γ` in the proof of [Stacks, Tag 01FD]: refinement of a
covering, inverse images and reindexing are all instances of it. The maps `r` need no
coherence hypothesis because `C` is thin. -/
@[ega "III 6.6.7" "partial"]
def refinementMap : (cechComplexFunctor V).obj Q ⟶ (cechComplexFunctor U).obj P where
  f n := refinementMapF U V T P Q η c r n
  comm' n m hnm := by
    obtain rfl : n + 1 = m := hnm
    exact refinementMapF_comm U V T P Q η c r n

/-- The factor of the degree-`n` component of `refinementMap` indexed by `x` is the projection
to the factor indexed by `c ∘ x`, followed by `η` and restriction along `r n x`. -/
@[reassoc (attr := simp)]
theorem refinementMap_comp_π (n : ℕ) (x : Fin (n + 1) → I) :
    (refinementMap U V T P Q η c r).f n ≫ π U P n x =
      π V Q n (c ∘ x) ≫ η.app (op (inter V (c ∘ x))) ≫ P.map (r n x).op :=
  refinementMapF_comp_π U V T P Q η c r n x

/-- **The Čech complex of a refinement is natural in the coefficients.** -/
theorem refinementMap_naturality {P' : Cᵒᵖ ⥤ A} {Q' : Dᵒᵖ ⥤ A} (η' : Q' ⟶ T.op ⋙ P')
    (θ : P ⟶ P') (ξ : Q ⟶ Q') (h : ∀ W, ξ.app W ≫ η'.app W = η.app W ≫ θ.app (T.op.obj W)) :
    (cechComplexFunctor V).map ξ ≫ refinementMap U V T P' Q' η' c r =
      refinementMap U V T P Q η c r ≫ (cechComplexFunctor U).map θ := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ hom_ext U P' fun x ↦ ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc, Category.assoc,
    refinementMap_comp_π, map_f_comp_π, refinementMap_comp_π_assoc,
    map_f_comp_π_assoc, ← Category.assoc (ξ.app _), h]
  simp only [Category.assoc]
  exact congrArg (fun z ↦ π V Q n (c ∘ x) ≫ η.app (op (inter V (c ∘ x))) ≫ z)
    (θ.naturality (r n x).op).symm

end Refinement

/-! ### Changing the coefficient category -/

section Coefficients

variable {C : Type uC} [Category.{vC} C] [HasFiniteProducts C]
  {A : Type uA} [Category.{vA} A] [Preadditive A]
  {B : Type uB} [Category.{vB} B] [Preadditive B]
  {I : Type uI} [HasProducts.{uI} A] [HasProducts.{uI} B]
  (U : I → C) (P : Cᵒᵖ ⥤ A) (H : A ⥤ B) [H.Additive]
  [∀ n : ℕ, PreservesLimit
    (Discrete.functor fun x : Fin (n + 1) → I ↦ P.obj (op (inter U x))) H]

/-- Applying `H` to the degree-`n` term of a Čech complex gives the degree-`n` term of the Čech
complex with coefficients in `P ⋙ H`, because `H` preserves the defining product. -/
def coefficientsIsoX (n : ℕ) :
    H.obj (((cechComplexFunctor U).obj P).X n) ≅
      ((cechComplexFunctor U).obj (P ⋙ H)).X n :=
  PreservesProduct.iso H fun x : Fin (n + 1) → I ↦ P.obj (op (inter U x))

omit [H.Additive] in
/-- Composing `coefficientsIsoX` with the projection to the factor indexed by `x` is `H`
applied to the projection to that factor. -/
@[reassoc (attr := simp)]
theorem coefficientsIsoX_hom_comp_π (n : ℕ) (x : Fin (n + 1) → I) :
    (coefficientsIsoX U P H n).hom ≫ π U (P ⋙ H) n x = H.map (π U P n x) := by
  rw [coefficientsIsoX, PreservesProduct.iso_hom]
  exact piComparison_comp_π _ _ x

/-- **An additive functor preserving products commutes with the Čech complex.** -/
def coefficientsIso :
    (H.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj P) ≅
      (cechComplexFunctor U).obj (P ⋙ H) :=
  HomologicalComplex.Hom.isoOfComponents (coefficientsIsoX U P H) (by
    intro n m hnm
    obtain rfl : n + 1 = m := hnm
    refine hom_ext U (P ⋙ H) fun y ↦ ?_
    have hL : ((coefficientsIsoX U P H n).hom ≫
        ((cechComplexFunctor U).obj (P ⋙ H)).d n (n + 1)) ≫ π U (P ⋙ H) (n + 1) y =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (H.map (π U P n (y ∘ i.succAbove)) ≫
          H.map (P.map (interMap U y i.succAbove).op)) := by
      rw [Category.assoc, d_comp_π, Preadditive.comp_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Preadditive.comp_zsmul, coefficientsIsoX_hom_comp_π_assoc]
      rfl
    have hR : (((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U).obj P)).d n (n + 1) ≫
        (coefficientsIsoX U P H (n + 1)).hom) ≫ π U (P ⋙ H) (n + 1) y =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (H.map (π U P n (y ∘ i.succAbove)) ≫
          H.map (P.map (interMap U y i.succAbove).op)) := by
      rw [Category.assoc, coefficientsIsoX_hom_comp_π,
        Functor.mapHomologicalComplex_obj_d, ← H.map_comp, d_comp_π, H.map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Functor.map_zsmul, H.map_comp]
    rw [hL, hR])

/-- The degree-`n` component of `coefficientsIso`, followed by the projection to the factor
indexed by `x`, is `H` applied to the projection to that factor. -/
@[reassoc (attr := simp)]
theorem coefficientsIso_hom_f_comp_π (n : ℕ) (x : Fin (n + 1) → I) :
    (coefficientsIso U P H).hom.f n ≫ π U (P ⋙ H) n x = H.map (π U P n x) :=
  coefficientsIsoX_hom_comp_π U P H n x

/-- The degree-`n` component of the inverse of `coefficientsIso`, followed by `H` applied to the
projection to the factor indexed by `x`, is the projection to that factor. -/
@[reassoc (attr := simp)]
theorem coefficientsIso_inv_f_comp_map_π (n : ℕ) (x : Fin (n + 1) → I) :
    (coefficientsIso U P H).inv.f n ≫ H.map (π U P n x) = π U (P ⋙ H) n x := by
  rw [← coefficientsIso_hom_f_comp_π U P H n x, ← Category.assoc]
  change ((coefficientsIso U P H).inv ≫ (coefficientsIso U P H).hom).f n ≫ _ = _
  rw [(coefficientsIso U P H).inv_hom_id]
  exact Category.id_comp _

/-- **The coefficient comparison is natural in the presheaf.** -/
theorem coefficientsIso_naturality {P' : Cᵒᵖ ⥤ A}
    [∀ n : ℕ, PreservesLimit
      (Discrete.functor fun x : Fin (n + 1) → I ↦ P'.obj (op (inter U x))) H]
    (θ : P ⟶ P') :
    (H.mapHomologicalComplex (ComplexShape.up ℕ)).map ((cechComplexFunctor U).map θ) ≫
        (coefficientsIso U P' H).hom =
      (coefficientsIso U P H).hom ≫
        (cechComplexFunctor U).map (Functor.whiskerRight θ H) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ hom_ext U (P' ⋙ H) fun x ↦ ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc, Category.assoc,
    coefficientsIso_hom_f_comp_π, map_f_comp_π, coefficientsIso_hom_f_comp_π_assoc,
    Functor.mapHomologicalComplex_map_f, ← H.map_comp, map_f_comp_π]
  exact H.map_comp _ _

end Coefficients

end

end Stacks.CategoryTheory.CechComplex

namespace Stacks.Cohomology.CechRefinement

open Stacks.CategoryTheory.CechComplex

noncomputable section

attribute [local instance] ModuleCat.hasLimitsOfSize

/-- A slice category over an open subset is thin: a morphism over `W` is determined by its
source and target, because `Opens` is a partial order. -/
instance overIsThin {Z : Type u} [TopologicalSpace Z] (W : Opens Z) :
    Quiver.IsThin (Over W) :=
  fun _ _ ↦ ⟨fun g h ↦ Over.OverMorphism.ext (Subsingleton.elim g.left h.left)⟩

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **Inverse image on the slices over the whole space.** A morphism `f : X ⟶ Y` of ringed
spaces carries an open subset of `Y` to its inverse image in `X`; both are regarded as objects
of the slice over the whole space, which is where the Čech complex of [Stacks, Tag 01EQ]
lives. -/
def sliceMap : Over (⊤ : Opens Y.carrier) ⥤ Over (⊤ : Opens X.carrier) where
  obj W := Over.mk (homOfLE (show (Opens.map f.hom.base).obj W.left ≤ ⊤ from le_top))
  map h := Over.homMk ((Opens.map f.hom.base).map h.left)

/-- Restriction of the structure sheaf from the whole space to an object of the slice over it.
This is the ring map along which the Čech complex of [Stacks, Tag 01EQ] restricts scalars. -/
def sliceRes {Z : Type u} [TopologicalSpace Z]
    (R : Sheaf (Opens.grothendieckTopology Z) RingCat.{u}) (W : Over (⊤ : Opens Z)) :
    SectionRing R ⊤ ⟶ R.obj.obj (op W.left) :=
  R.obj.map (homOfLE (show W.left ≤ ⊤ from le_top)).op

/-- The ring map from global sections on `Y` to sections on the inverse image of an object of
the slice over `Y`: restrict to the open, then apply `f^♯`. -/
def refinementRingHom (W : Over (⊤ : Opens Y.carrier)) :
    SectionRing (ringCatSheaf Y) ⊤ ⟶
      (ringCatSheaf X).obj.obj (op ((Opens.map f.hom.base).obj W.left)) :=
  sliceRes (ringCatSheaf Y) W ≫ (structureSheafHom f).hom.app (op W.left)

/-- **The two routes from global sections on `Y` to sections on an inverse image agree**:
restricting and then applying `f^♯` is applying `f^♯` on global sections and then restricting.
This is naturality of `f^♯`. -/
theorem refinementRingHom_eq (W : Over (⊤ : Opens Y.carrier)) :
    (refinementRingHom f W).hom =
      (sliceRes (ringCatSheaf X) ((sliceMap f).obj W)).hom.comp
        (globalSectionsRingHom f).hom := by
  have h : (ringCatSheaf Y).obj.map (homOfLE (show W.left ≤ ⊤ from le_top)).op ≫
      (structureSheafHom f).hom.app (op W.left) =
      (structureSheafHom f).hom.app (op ⊤) ≫
        (ringCatSheaf X).obj.map
          ((Opens.map f.hom.base).map (homOfLE (show W.left ≤ ⊤ from le_top))).op :=
    (structureSheafHom f).hom.naturality (homOfLE (show W.left ≤ ⊤ from le_top)).op
  exact congrArg RingCat.Hom.hom h

variable (F : Modules X)

/-- **Sections of a pushforward over the slice over `Y`, at one object.** The sections of
`f_* F` over `W` are the sections of `F` over `f⁻¹ W`; as modules over `Γ(Y, 𝒪_Y)` the two
spellings restrict scalars along the two composites of `refinementRingHom_eq`, so the
comparison is the identity on sections. -/
def pushforwardSectionsIsoApp (W : Over (⊤ : Opens Y.carrier)) :
    (sectionsPresheaf (⊤ : Opens Y.carrier) ((modulePushforward f).obj F)).obj (op W) ≅
      (restrictGlobalScalars f).obj
        ((sectionsPresheaf (⊤ : Opens X.carrier) F).obj (op ((sliceMap f).obj W))) :=
  (ModuleCat.restrictScalarsComp'App (sliceRes (ringCatSheaf Y) W).hom
      ((structureSheafHom f).hom.app (op W.left)).hom (refinementRingHom f W).hom rfl
      ((SheafOfModules.evaluation (ringCatSheaf X)
        (op ((Opens.map f.hom.base).obj W.left))).obj F)).symm ≪≫
    ModuleCat.restrictScalarsComp'App (globalSectionsRingHom f).hom
      (sliceRes (ringCatSheaf X) ((sliceMap f).obj W)).hom (refinementRingHom f W).hom
      (refinementRingHom_eq f W)
      ((SheafOfModules.evaluation (ringCatSheaf X)
        (op ((Opens.map f.hom.base).obj W.left))).obj F)

/-- **Sections of a pushforward over the slice over `Y`.** The natural isomorphism assembled
from `pushforwardSectionsIsoApp`; it is the identity on sections. -/
def pushforwardSectionsIso :
    sectionsPresheaf (⊤ : Opens Y.carrier) ((modulePushforward f).obj F) ≅
      (sliceMap f).op ⋙ sectionsPresheaf (⊤ : Opens X.carrier) F ⋙
        restrictGlobalScalars f :=
  NatIso.ofComponents (fun W ↦ pushforwardSectionsIsoApp f F W.unop) (by intros; rfl)

/-- **Sections of a pushforward are natural in the sheaf of modules**, compatibly with
`pushforwardSectionsIso`: both sides are the map on sections of `f_* b`. -/
theorem pushforwardSectionsIso_hom_naturality {F' : Modules X} (b : F ⟶ F') :
    (sectionsPresheafFunctor (⊤ : Opens Y.carrier)).map ((modulePushforward f).map b) ≫
        (pushforwardSectionsIso f F').hom =
      (pushforwardSectionsIso f F).hom ≫
        Functor.whiskerLeft (sliceMap f).op (Functor.whiskerRight
          ((sectionsPresheafFunctor (⊤ : Opens X.carrier)).map b)
          (restrictGlobalScalars f)) :=
  NatTrans.ext (funext fun _ ↦ rfl)

variable (G : Modules Y) (φ : (modulePullback f).obj G ⟶ F)

/-- **The map on sections attached to an `f`-map.** On an object `W` of the slice over `Y` it
sends a section of `G` over `W` to its image under the adjoint `G ⟶ f_* F` of `φ`, read as a
section of `F` over `f⁻¹ W`; it is linear over `Γ(Y, 𝒪_Y)`. -/
def sectionsRefinement :
    sectionsPresheaf (⊤ : Opens Y.carrier) G ⟶
      (sliceMap f).op ⋙ (sectionsPresheaf (⊤ : Opens X.carrier) F ⋙
        restrictGlobalScalars f) :=
  (sectionsPresheafFunctor (⊤ : Opens Y.carrier)).map (homEquiv f F G φ) ≫
    (pushforwardSectionsIso f F).hom

variable {I J : Type u} (U : I → Opens X.carrier) (V : J → Opens Y.carrier)
  (hU : ⊤ = ⨆ i, U i) (hV : ⊤ = ⨆ j, V j)
  (c : I → J) (hc : ∀ i, U i ≤ (Opens.map f.hom.base).obj (V (c i)))

include hc in
/-- **A refined intersection sits inside the inverse image of the corresponding
intersection.** -/
theorem inter_le_map_inter (n : ℕ) (x : Fin (n + 1) → I) :
    (inter (coverObject U hU) x).left ≤
      (Opens.map f.hom.base).obj ((inter (coverObject V hV) (c ∘ x)).left) := by
  rw [inter_coverObject_left, inter_coverObject_left, inter_eq_iInf, inter_eq_iInf]
  intro z hz
  have hi : ∀ a, z ∈ U (x a) := fun a ↦ (iInf_le (fun b ↦ U (x b)) a) hz
  change f.hom.base z ∈ (⨅ a, V ((c ∘ x) a) : Opens Y.carrier)
  rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  exact fun a ↦ hc (x a) (hi a)

/-- **The inclusion of a refined intersection** into the inverse image of the corresponding
intersection, as a morphism of the slice over the whole space. -/
def refinementInclusion (n : ℕ) (x : Fin (n + 1) → I) :
    inter (coverObject U hU) x ⟶ (sliceMap f).obj (inter (coverObject V hV) (c ∘ x)) :=
  Over.homMk (homOfLE (inter_le_map_inter f U V hU hV c hc n x))

/-- **The Čech refinement map `γ` of [Stacks, Tag 01FD].** For an `f`-map `φ : f^* G ⟶ F` and
a refinement `c` of the inverse image of the covering `V` by the covering `U`, this is the
induced morphism from the Čech complex of `(V, G)` on `Y` to the Čech complex of `(U, F)` on
`X`, the latter regarded as a complex of `Γ(Y, 𝒪_Y)`-modules by restriction of scalars. On the
factor indexed by `x` it applies the `f`-map on the intersection selected by `c ∘ x` and then
restricts along the inclusion of the refined intersection. -/
def cechComplexRefinementMap :
    (cechComplexNatFunctor (ringCatSheaf Y) ⊤ V hV).obj G ⟶
      ((restrictGlobalScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((cechComplexNatFunctor (ringCatSheaf X) ⊤ U hU).obj F) :=
  refinementMap (coverObject U hU) (coverObject V hV) (sliceMap f)
      (sectionsPresheaf (⊤ : Opens X.carrier) F ⋙ restrictGlobalScalars f)
      (sectionsPresheaf (⊤ : Opens Y.carrier) G)
      (sectionsRefinement f F G φ) c (refinementInclusion f U V hU hV c hc) ≫
    (coefficientsIso (coverObject U hU) (sectionsPresheaf (⊤ : Opens X.carrier) F)
      (restrictGlobalScalars f)).inv

section Degreewise

variable {F G} {I J : Type u} {U : I → Opens X.carrier} {V : J → Opens Y.carrier}
  {hU : ⊤ = ⨆ i, U i} {hV : ⊤ = ⨆ j, V j}
  {c : I → J} {hc : ∀ i, U i ≤ (Opens.map f.hom.base).obj (V (c i))}

/-- **The degreewise formula for the Čech refinement map.** On the factor indexed by `x` it is
the `f`-map on sections over the intersection selected by `c ∘ x`, followed by restriction
along the inclusion of the refined intersection. -/
@[reassoc]
theorem cechComplexRefinementMap_comp_map_π (φ : (modulePullback f).obj G ⟶ F)
    (n : ℕ) (x : Fin (n + 1) → I) :
    (cechComplexRefinementMap f F G φ U V hU hV c hc).f n ≫
        (restrictGlobalScalars f).map
          (π (coverObject U hU) (sectionsPresheaf (⊤ : Opens X.carrier) F) n x) =
      π (coverObject V hV) (sectionsPresheaf (⊤ : Opens Y.carrier) G) n (c ∘ x) ≫
        (sectionsRefinement f F G φ).app
            (op (inter (coverObject V hV) (c ∘ x))) ≫
          (sectionsPresheaf (⊤ : Opens X.carrier) F ⋙ restrictGlobalScalars f).map
            (refinementInclusion f U V hU hV c hc n x).op := by
  rw [cechComplexRefinementMap, HomologicalComplex.comp_f, Category.assoc,
    coefficientsIso_inv_f_comp_map_π, refinementMap_comp_π]

/-- **The Čech refinement map is natural in the pair of coefficient sheaves.** -/
theorem cechComplexRefinementMap_naturality {F' : Modules X} {G' : Modules Y}
    (φ : (modulePullback f).obj G ⟶ F) (φ' : (modulePullback f).obj G' ⟶ F')
    (a : G ⟶ G') (b : F ⟶ F')
    (h : a ≫ homEquiv f F' G' φ' = homEquiv f F G φ ≫ (modulePushforward f).map b) :
    (cechComplexNatFunctor (ringCatSheaf Y) ⊤ V hV).map a ≫
        cechComplexRefinementMap f F' G' φ' U V hU hV c hc =
      cechComplexRefinementMap f F G φ U V hU hV c hc ≫
        ((restrictGlobalScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((cechComplexNatFunctor (ringCatSheaf X) ⊤ U hU).map b) := by
  set H := restrictGlobalScalars f with hH
  set θ₀ := (sectionsPresheafFunctor (⊤ : Opens X.carrier)).map b with hθ₀
  have hsec : (sectionsPresheafFunctor (⊤ : Opens Y.carrier)).map a ≫
      sectionsRefinement f F' G' φ' =
      sectionsRefinement f F G φ ≫
        Functor.whiskerLeft (sliceMap f).op (Functor.whiskerRight θ₀ H) := by
    rw [sectionsRefinement, sectionsRefinement, ← Category.assoc,
      ← Functor.map_comp, h, Functor.map_comp, Category.assoc]
    exact congrArg
      (fun k ↦ (sectionsPresheafFunctor (⊤ : Opens Y.carrier)).map
        (homEquiv f F G φ) ≫ k)
      (pushforwardSectionsIso_hom_naturality f F b)
  have hη : ∀ W, ((sectionsPresheafFunctor (⊤ : Opens Y.carrier)).map a).app W ≫
      (sectionsRefinement f F' G' φ').app W =
      (sectionsRefinement f F G φ).app W ≫
        (Functor.whiskerRight θ₀ H).app ((sliceMap f).op.obj W) :=
    fun W ↦ congrArg (fun k ↦ NatTrans.app k W) hsec
  have hrefine := refinementMap_naturality (coverObject U hU) (coverObject V hV) (sliceMap f)
    (sectionsPresheaf (⊤ : Opens X.carrier) F ⋙ H)
    (sectionsPresheaf (⊤ : Opens Y.carrier) G) (sectionsRefinement f F G φ) c
    (refinementInclusion f U V hU hV c hc) (sectionsRefinement f F' G' φ')
    (Functor.whiskerRight θ₀ H) ((sectionsPresheafFunctor (⊤ : Opens Y.carrier)).map a) hη
  have hcoef := coefficientsIso_naturality (coverObject U hU)
    (sectionsPresheaf (⊤ : Opens X.carrier) F) H
    (P' := sectionsPresheaf (⊤ : Opens X.carrier) F') θ₀
  have hcoef' : (cechComplexFunctor (coverObject U hU)).map (Functor.whiskerRight θ₀ H) ≫
      (coefficientsIso (coverObject U hU)
        (sectionsPresheaf (⊤ : Opens X.carrier) F') H).inv =
      (coefficientsIso (coverObject U hU) (sectionsPresheaf (⊤ : Opens X.carrier) F) H).inv ≫
        (H.mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((cechComplexFunctor (coverObject U hU)).map θ₀) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact hcoef.symm
  dsimp only [cechComplexRefinementMap]
  change (cechComplexFunctor (coverObject V hV)).map
      ((sectionsPresheafFunctor (⊤ : Opens Y.carrier)).map a) ≫ _ = _
  rw [← Category.assoc, hrefine, Category.assoc, hcoef', Category.assoc]
  rfl

end Degreewise

/-! ### The refinement map in integer degrees -/

/-- **The Čech refinement map of [Stacks, Tag 01FD], in integer degrees.** The map of natural
degrees, extended by zero from `ℕ` to `ℤ` and read through the comparison of extension by zero
with restriction of scalars applied termwise. -/
def cechComplexRefinementMapInt :
    (cechComplexIntFunctor (ringCatSheaf Y) ⊤ V hV).obj G ⟶
      ((restrictGlobalScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((cechComplexIntFunctor (ringCatSheaf X) ⊤ U hU).obj F) :=
  HomologicalComplex.extendMap (cechComplexRefinementMap f F G φ U V hU hV c hc)
      ComplexShape.embeddingUpNat ≫
    (Stacks.DerivedIndexing.mapExtendIso (restrictGlobalScalars f)
      ComplexShape.embeddingUpNat
      ((cechComplexNatFunctor (ringCatSheaf X) ⊤ U hU).obj F)).hom

/-- **The Čech refinement map in integer degrees is natural in the pair of coefficient
sheaves.** -/
theorem cechComplexRefinementMapInt_naturality {F' : Modules X} {G' : Modules Y}
    (φ' : (modulePullback f).obj G' ⟶ F') (a : G ⟶ G') (b : F ⟶ F')
    (h : a ≫ homEquiv f F' G' φ' = homEquiv f F G φ ≫ (modulePushforward f).map b) :
    (cechComplexIntFunctor (ringCatSheaf Y) ⊤ V hV).map a ≫
        cechComplexRefinementMapInt f F' G' φ' U V hU hV c hc =
      cechComplexRefinementMapInt f F G φ U V hU hV c hc ≫
        ((restrictGlobalScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((cechComplexIntFunctor (ringCatSheaf X) ⊤ U hU).map b) := by
  have hnat := congrArg
    (fun g ↦ HomologicalComplex.extendMap g ComplexShape.embeddingUpNat)
    (cechComplexRefinementMap_naturality (U := U) (V := V) (hU := hU) (hV := hV)
      (c := c) (hc := hc) f φ φ' a b h)
  simp only [HomologicalComplex.extendMap_comp] at hnat
  have hext : HomologicalComplex.extendMap
        (((restrictGlobalScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((cechComplexNatFunctor (ringCatSheaf X) ⊤ U hU).map b))
        ComplexShape.embeddingUpNat ≫
      (Stacks.DerivedIndexing.mapExtendIso (restrictGlobalScalars f)
        ComplexShape.embeddingUpNat
        ((cechComplexNatFunctor (ringCatSheaf X) ⊤ U hU).obj F')).hom =
      (Stacks.DerivedIndexing.mapExtendIso (restrictGlobalScalars f)
        ComplexShape.embeddingUpNat
        ((cechComplexNatFunctor (ringCatSheaf X) ⊤ U hU).obj F)).hom ≫
        ((restrictGlobalScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap
            ((cechComplexNatFunctor (ringCatSheaf X) ⊤ U hU).map b)
            ComplexShape.embeddingUpNat) :=
    (Stacks.DerivedIndexing.mapExtendNatIso (restrictGlobalScalars f)
      ComplexShape.embeddingUpNat).hom.naturality
        ((cechComplexNatFunctor (ringCatSheaf X) ⊤ U hU).map b)
  dsimp only [cechComplexRefinementMapInt]
  change HomologicalComplex.extendMap
      ((cechComplexNatFunctor (ringCatSheaf Y) ⊤ V hV).map a) ComplexShape.embeddingUpNat ≫
        HomologicalComplex.extendMap
          (cechComplexRefinementMap f F' G' φ' U V hU hV c hc)
          ComplexShape.embeddingUpNat ≫ _ = _
  rw [← Category.assoc _ (HomologicalComplex.extendMap
      (cechComplexRefinementMap f F' G' φ' U V hU hV c hc)
      ComplexShape.embeddingUpNat) _, hnat, Category.assoc, hext, Category.assoc]
  rfl

end

end Stacks.Cohomology.CechRefinement
