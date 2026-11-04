module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.RestrictionOfEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TensorOfStrictlyPerfectComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximationsGeneral
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IteratedSlice
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import StacksFrontier.CategoryTheory.Limits.SigmaSupport
public import StacksFrontier.Algebra.Homology.DerivedCategory.ShiftedSumIsProduct

/-!
# Local models of a derived tensor product with a perfect factor

Let `(C, O)` be a ringed site whose objects form a type in a universe `c` of their own while its
morphisms, the sections of `O` and the sections of its modules lie in one universe `u`, with `C`
essentially `u`-small; this is the shape of the small étale site of an algebraic space.  Let `E`
be a perfect object of `D(O)` and `G` an arbitrary complex of `O`-modules.  Then there is a family
of objects `V` covering the final object of `C`, and on each member a strictly perfect complex `P`
of `O|_V`-modules, such that the restriction of `E ⊗^L_O G` to the slice over `V` is the class of
the ordinary total tensor complex `Tot(P ⊗_{O|_V} G|_V)`.

This is the sentence of the source, in the proofs of Stacks 0DJQ and Stacks 0DKJ: "locally `E` is
isomorphic to a finite complex of finite free modules, hence locally `E ⊗^L 𝒢` is isomorphic to a
finite complex whose terms are finite direct sums of the `𝒢^i`".

## Main results

In the namespace `Stacks.SheafOfModules`:

* `isFlat_of_isDirectSummandOfFiniteFree'`: a direct summand of a finite free `O`-module is flat,
  at a site whose sections live below its objects.
* `isKFlat_of_isStrictlyPerfect`: a strictly perfect complex is K-flat, at the same universes.
* `DerivedTensorProduct.OfEssentiallySmall.restrictDerivedTensorKFlatIso`: for `A` K-flat, the
  restriction of `Q(A) ⊗^L_O Q(G)` to a slice is `Q(Tot(A|_V ⊗ G|_V))`.
* `DerivedTensorProduct.OfEssentiallySmall.exists_coversTop_restrict_tensor_models`: the local
  models.

## Implementation notes

A K-flat resolution `A ⟶ E'` of a perfect complex `E'` representing `E` is chosen once on `C`.  Its
restriction to every slice is K-flat (Stacks 0E8K at this universe shape), and so is a strictly
perfect complex (Stacks 06YQ), so on the slice the left comparison of any derived tensor product
`T_V` formed there identifies both `Q(Tot(A|_V ⊗ G|_V))` and `Q(Tot(P ⊗ G|_V))` with
`T_V(Q(A|_V), Q(G|_V)) ≅ T_V(Q(P), Q(G|_V))`, the two first factors being isomorphic through the
two quasi-isomorphisms `A|_V ⟶ E'|_V ⟵ P`.  No naturality of any comparison is used.

## References

* [Stacks Project, Tag 0DKJ](https://stacks.math.columbia.edu/tag/0DKJ)
* [Stacks Project, Tag 0DJQ](https://stacks.math.columbia.edu/tag/0DJQ)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 0E8K](https://stacks.math.columbia.edu/tag/0E8K)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u c d

namespace CategoryTheory.ObjectProperty

open Limits

/-- **A property of objects of an abelian category closed under isomorphisms and extensions and
containing zero is closed under finite coproducts**: a binary coproduct is a binary biproduct,
which is an extension of its two summands. -/
theorem isClosedUnderFiniteCoproducts_of_isClosedUnderExtensions {A : Type*} [Category A]
    [Abelian A] (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    [P.IsClosedUnderExtensions] : P.IsClosedUnderFiniteCoproducts := by
  have : P.IsClosedUnderColimitsOfShape (Discrete WalkingPair) := by
    refine ⟨fun X ⟨h⟩ => ?_⟩
    let e₁ : X ≅ colimit h.diag :=
      h.isColimit.coconePointUniqueUpToIso (colimit.isColimit h.diag)
    let e₂ : colimit h.diag ≅ h.diag.obj ⟨WalkingPair.left⟩ ⨿ h.diag.obj ⟨WalkingPair.right⟩ :=
      HasColimit.isoOfNatIso (diagramIsoPair h.diag)
    let e₃ : h.diag.obj ⟨WalkingPair.left⟩ ⨿ h.diag.obj ⟨WalkingPair.right⟩ ≅
        h.diag.obj ⟨WalkingPair.left⟩ ⊞ h.diag.obj ⟨WalkingPair.right⟩ :=
      (biprod.isoCoprod _ _).symm
    exact P.prop_of_iso (e₁ ≪≫ e₂ ≪≫ e₃).symm
      (P.prop_biprod (h.prop_diag_obj _) (h.prop_diag_obj _))
  exact IsClosedUnderFiniteCoproducts.mk'

end CategoryTheory.ObjectProperty

namespace Stacks.TotalComplexTerms

open Limits

/-- The term in degree `n` of the total complex of a bifunctor double complex is the coproduct
over the pairs `(p, q)` with `p + q = n` of the values `F(K^p, L^q)`. -/
private theorem mapBifunctor_X_eq_coproduct {C₁ C₂ A : Type*} [Category C₁] [Category C₂]
    [Category A] [Preadditive C₁] [Preadditive C₂] [Abelian A]
    (F : C₁ ⥤ C₂ ⥤ A) (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ)
    [F.Additive] [∀ M, (F.obj M).Additive]
    [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)] (n : ℤ) :
    (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K).obj L).X n =
      ∐ (((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K).obj L).toGradedObject.mapObjFun
          (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n := rfl

/-- **A term of the total complex of a bifunctor double complex has a property closed under
finite coproducts** as soon as the property holds of the values of the bifunctor on the pairs
of terms in complementary degrees, and the first factor is bounded.  The term in degree `n` is
the coproduct over the pairs `(p, q)` with `p + q = n` of the values `F(K^p, L^q)`, of which only
finitely many are nonzero; the vanishing summands are discarded by
`CategoryTheory.Limits.sigmaSubtypeIsoOfIsZero`. -/
theorem prop_mapBifunctor_X {C₁ C₂ A : Type*} [Category C₁] [Category C₂]
    [Category A] [Preadditive C₁] [Preadditive C₂] [Abelian A]
    (F : C₁ ⥤ C₂ ⥤ A) (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ)
    [F.Additive] [∀ M, (F.obj M).Additive]
    [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
    (Q : ObjectProperty A) [Q.IsClosedUnderIsomorphisms] [Q.IsClosedUnderFiniteCoproducts]
    (a b : ℤ) (hK : ∀ p : ℤ, p < a ∨ b < p → IsZero (K.X p)) (n : ℤ)
    (hQ : ∀ p q : ℤ, p + q = n → Q ((F.obj (K.X p)).obj (L.X q))) :
    Q ((((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj K).obj L).X n) := by
  classical
  rw [mapBifunctor_X_eq_coproduct F K L n]
  let M := (((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)).obj K).obj L).toGradedObject.mapObjFun
      (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n
  -- only the pairs whose first coordinate lies in `[a, b]` contribute, and there are finitely many
  have hinj : Function.Injective
      (fun j : ↑(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⁻¹' {n}) => ((j : ℤ × ℤ)).1) := by
    rintro ⟨⟨p₁, q₁⟩, h₁⟩ ⟨⟨p₂, q₂⟩, h₂⟩ hp
    have e₁ : p₁ + q₁ = n := h₁
    have e₂ : p₂ + q₂ = n := h₂
    obtain rfl : p₁ = p₂ := hp
    obtain rfl : q₁ = q₂ := by omega
    rfl
  have hfib : {j : ↑(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n}) | ((j : ℤ × ℤ)).1 ∈ Set.Icc a b}.Finite :=
    Set.Finite.of_finite_image ((Set.finite_Icc a b).subset
      (by rintro x ⟨j, hj, rfl⟩; exact hj)) hinj.injOn
  have hfin : {j | ¬ IsZero (M j)}.Finite := by
    refine hfib.subset fun j hj => ?_
    obtain ⟨⟨p, q⟩, hpq⟩ := j
    by_cases hc : a ≤ p ∧ p ≤ b
    · exact hc
    · exact absurd ((Functor.map_isZero F (hK p (by omega))).obj _) hj
  have : Finite {j // ¬ IsZero (M j)} := hfin.to_subtype
  refine Q.prop_of_iso
    (sigmaSubtypeIsoOfIsZero M (fun j => ¬ IsZero (M j)) fun _ hj => not_not.1 hj)
    (Q.prop_coproduct fun j => ?_)
  obtain ⟨⟨⟨p, q⟩, hpq⟩, -⟩ := j
  exact hQ p q hpq

/-- **The total complex of a bifunctor double complex vanishes termwise outside the sum of the
two factors' ranges**: in every pair of complementary degrees one of the two factors vanishes,
the bifunctor is additive in each variable, and a coproduct of zero objects is zero. -/
theorem isZero_mapBifunctor_X_of_bounds {C₁ C₂ D : Type*} [Category C₁] [Category C₂]
    [Category D] [Preadditive C₁] [Preadditive C₂] [Abelian D]
    (F : C₁ ⥤ C₂ ⥤ D) (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ)
    [F.Additive] [∀ M, (F.obj M).Additive]
    [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
    (aK bK aL bL : ℤ)
    (hK : ∀ p : ℤ, p < aK ∨ bK < p → IsZero (K.X p))
    (hL : ∀ q : ℤ, q < aL ∨ bL < q → IsZero (L.X q))
    (n : ℤ) (hn : n < aK + aL ∨ bK + bL < n) :
    IsZero ((((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj K).obj L).X n) := by
  rw [mapBifunctor_X_eq_coproduct F K L n]
  refine Stacks.ShiftedSum.isZero_coproduct _ fun j => ?_
  obtain ⟨⟨p, q⟩, hpq⟩ := j
  have hpq' : p + q = n := hpq
  have h : IsZero (K.X p) ∨ IsZero (L.X q) := by
    rcases hn with h | h
    · by_cases hp : p < aK
      · exact Or.inl (hK p (Or.inl hp))
      · exact Or.inr (hL q (Or.inl (by omega)))
    · by_cases hp : bK < p
      · exact Or.inl (hK p (Or.inr hp))
      · exact Or.inr (hL q (Or.inr (by omega)))
  rcases h with hK | hL
  · exact (Functor.map_isZero F hK).obj _
  · exact Functor.map_isZero _ hL

end Stacks.TotalComplexTerms

namespace Stacks.SheafOfModules

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

section TensorWithSummand

open Limits

variable {C : Type c} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} R).Additive]

/-- Tensoring on the right with a fixed module is an additive functor. -/
instance flip_obj_sheafTensor_additive (N : _root_.SheafOfModules.{u} (Tensor.ringSheaf R)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} R).flip.obj N).Additive where
  map_add {_ _ f g} := by
    change ((Stacks.SheafOfModules.Tensor.sheafTensor R).map (f + g)).app N = _
    rw [Functor.map_add]
    rfl

/-- **A tensor product `M ⊗ N` with `M` a direct summand of a finite free module has every
property of `N` that is closed under isomorphisms, finite coproducts and retracts**: `M ⊗ N` is a
retract of `O^n ⊗ N ≅ N^{⊕ n}`. -/
theorem prop_sheafTensor_of_isDirectSummandOfFiniteFree
    (Q : ObjectProperty (_root_.SheafOfModules.{u} (Tensor.ringSheaf R)))
    [Q.IsClosedUnderIsomorphisms] [Q.IsClosedUnderFiniteCoproducts]
    (hret : ∀ {M N : _root_.SheafOfModules.{u} (Tensor.ringSheaf R)} (i : M ⟶ N) (r : N ⟶ M),
      i ≫ r = 𝟙 M → Q N → Q M)
    (M N : _root_.SheafOfModules.{u} (Tensor.ringSheaf R))
    (hM : IsDirectSummandOfFiniteFree (Tensor.ringSheaf R) M) (hN : Q N) :
    Q (((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} R).obj M).obj N) := by
  obtain ⟨n, i, r, hir⟩ :=
    (isDirectSummandOfFiniteFree_iff_free (Tensor.ringSheaf R) M).1 hM
  let F := (Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} R).flip.obj N
  have : HasFiniteBiproducts (_root_.SheafOfModules.{u} (Tensor.ringSheaf R)) :=
    Abelian.hasFiniteBiproducts
  have : F.Additive := flip_obj_sheafTensor_additive R N
  have hfree : Q (F.obj (_root_.SheafOfModules.free (ULift.{u} (Fin n)))) := by
    let f : Fin n → _root_.SheafOfModules.{u} (Tensor.ringSheaf R) :=
      fun _ => _root_.SheafOfModules.unit (Tensor.ringSheaf R)
    have e₀ : ∐ f ≅ _root_.SheafOfModules.free (ULift.{u} (Fin n)) :=
      Sigma.reindex Equiv.ulift.symm
        (fun _ : ULift.{u} (Fin n) => _root_.SheafOfModules.unit (Tensor.ringSheaf R))
    have e : F.obj (∐ f) ≅ ∐ (fun j => F.obj (f j)) :=
      F.mapIso (biproduct.isoCoproduct f).symm ≪≫ F.mapBiproduct f ≪≫
        biproduct.isoCoproduct _
    exact Q.prop_of_iso (e.symm ≪≫ F.mapIso e₀) (Q.prop_coproduct fun _ =>
      Q.prop_of_iso (Stacks.SheafOfModules.Tensor.sheafTensorUnitIsoLeft R N).symm hN)
  exact hret (F.map i) (F.map r) (by rw [← F.map_comp, hir, F.map_id]; rfl) hfree

end TensorWithSummand

section Flatness

variable {Y : RingedSite.{c, u, u}}
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A direct summand of a finite free `O`-module is flat**, on a ringed site whose objects
live in a universe of their own.  A finite free module is a finite coproduct of copies of the
structure sheaf, which is flat, and a retract of a flat module is flat. -/
theorem isFlat_of_isDirectSummandOfFiniteFree'
    (F : RingedSite.Modules.{c, u, u} Y)
    (hF : IsDirectSummandOfFiniteFree (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, c, u, u} (O := Y.O) F := by
  obtain ⟨n, i, r, hir⟩ :=
    (isDirectSummandOfFiniteFree_iff_free (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F).1 hF
  exact FlatRetract.isFlat_of_retract Y.O i r hir
    (FlatColimits.isFlat_coproduct_finite Y.O
      (fun _ : ULift.{u} (Fin n) =>
        _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      fun _ => DerivedTensorProduct.isFlat_unit)

/-- **A strictly perfect complex is K-flat**, on a ringed site whose objects live in a universe of
their own: its terms are flat and it is bounded above (Stacks 06YQ). -/
theorem isKFlat_of_isStrictlyPerfect
    (P : CochainComplex (RingedSite.Modules.{c, u, u} Y) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) P) :
    IsKFlat Y.O P := by
  obtain ⟨r, hr⟩ := hP.bounded.bddAbove
  have hLE : P.IsStrictlyLE r := by
    refine (CochainComplex.isStrictlyLE_iff P r).2 fun i hi => ?_
    by_contra h
    exact absurd (hr (by simpa only [Set.mem_ofPred_eq] using h)) (by omega)
  exact kFlat_of_boundedAbove_of_flat Y.O P ⟨r, hLE⟩
    fun i => isFlat_of_isDirectSummandOfFiniteFree' (P.X i) (hP.termDirectSummand i)

end Flatness

namespace DerivedTensorProduct.OfEssentiallySmall

open Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall (restriction restrictionComplex)
open Stacks.SheafOfModules.Tensor (tensorComplex)
open AlgebraicGeometry.RingedSite (tensorComplexOverIso)

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] sliceHasSheafify sliceWEqualsLocallyBijective
  preservesFiniteLimits_restriction preservesFiniteColimits_restriction

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ U : X.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor

variable [HasDerivedCategory.{d} (RingedSite.Modules.{c, u, u} X)]
  [hSliceDerived : ∀ U : X.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{max c u, u, u} (X.over U))]

attribute [local instance] sliceHasDerivedCategory

/-- The derived category of the modules on a slice, at the spelling `(ringSheaf X.O).over U`. -/
local instance sliceHasDerivedCategory'' (U : X.C) :
    HasDerivedCategory.{d}
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O).over U)) :=
  hSliceDerived U

/-- The total tensor complex `Tot(P ⊗_{O|_U} G|_U)` of a complex of `O|_U`-modules with the
restriction of a complex of `O`-modules. -/
abbrev restrictTensorComplex (U : X.C) (P : CochainComplex (SliceModules X U) ℤ)
    (G : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ) :
    CochainComplex (SliceModules X U) ℤ :=
  ((tensorComplex.{max c u, u, u} (X.O.over U)).obj P).obj ((restrictionComplex X U).obj G)

/-- **The restriction of `Q(A) ⊗^L_O Q(G)` to a slice is `Q(Tot(A|_U ⊗ G|_U))`**, for `A` a
K-flat complex: the left comparison of `T`, the factorisation of the derived restriction through
the restriction of complexes (restriction being exact), and the commutation of restriction with
the total tensor complex. -/
def restrictDerivedTensorKFlatIso (U : X.C) (T : DerivedTensorProduct.{c, u, u, d} X)
    (A G : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ) (hA : IsKFlat X.O A) :
    (RingedSite.derivedRestriction.{c, u, u, d} X U).obj
        ((T.tensor.obj (DerivedCategory.Q.obj A)).obj (DerivedCategory.Q.obj G)) ≅
      DerivedCategory.Q.obj (restrictTensorComplex X U ((restrictionComplex X U).obj A) G) :=
  (RingedSite.derivedRestriction.{c, u, u, d} X U).mapIso (T.comparisonLeft A G hA) ≪≫
    (restriction X U).mapDerivedCategoryFactors.app
      (((tensorComplex.{c, u, u} X.O).obj A).obj G) ≪≫
    DerivedCategory.Q.mapIso (tensorComplexOverIso X U A G)

/-- **Two K-flat complexes on a slice with isomorphic classes have quasi-isomorphic total tensor
complexes with any third complex**, read through a derived tensor product `TU` on the slice. -/
def tensorComplexIsoOfKFlat (U : X.C) (TU : DerivedTensorProduct.{max c u, u, u, d} (X.over U))
    (P P' L : CochainComplex (SliceModules X U) ℤ)
    (hP : IsKFlat (X.O.over U) P) (hP' : IsKFlat (X.O.over U) P')
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P') :
    DerivedCategory.Q.obj (((tensorComplex.{max c u, u, u} (X.O.over U)).obj P).obj L) ≅
      DerivedCategory.Q.obj (((tensorComplex.{max c u, u, u} (X.O.over U)).obj P').obj L) :=
  (TU.comparisonLeft P L hP).symm ≪≫ (TU.tensor.mapIso e).app _ ≪≫ TU.comparisonLeft P' L hP'

/-- **The restriction of `E ⊗^L_O Q(G)` to an object carrying a strictly perfect model of `E`.**
If `E'` is a complex with class `E` and `q : P ⟶ E'|_V` is a quasi-isomorphism from a strictly
perfect complex of `O|_V`-modules, then `(E ⊗^L_O Q(G))|_V ≅ Q(Tot(P ⊗_{O|_V} G|_V))`. -/
def restrictDerivedTensorIsoOfModel (T : DerivedTensorProduct.{c, u, u, d} X)
    (E : RingedSite.DerivedModules.{c, u, u, d} X)
    (E' : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ)
    (eE : DerivedCategory.Q.obj E' ≅ E) (V : X.C)
    (P : CochainComplex (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ)
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P)
    (q : P ⟶ X.restrictComplex E' V) (hq : QuasiIso q)
    (G : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ) :
    (RingedSite.derivedRestriction.{c, u, u, d} X V).obj
        ((T.tensor.obj E).obj (DerivedCategory.Q.obj G)) ≅
      DerivedCategory.Q.obj (restrictTensorComplex X V P G) :=
  let A := (Stacks.SheafOfModules.KFlatResolution.exists_kFlat_quasiIso_ofSize X.O E').choose
  let a := (Stacks.SheafOfModules.KFlatResolution.exists_kFlat_quasiIso_ofSize X.O
    E').choose_spec.choose
  have hA : IsKFlat X.O A := (Stacks.SheafOfModules.KFlatResolution.exists_kFlat_quasiIso_ofSize
    X.O E').choose_spec.choose_spec.1
  have : QuasiIso a := (Stacks.SheafOfModules.KFlatResolution.exists_kFlat_quasiIso_ofSize
    X.O E').choose_spec.choose_spec.2
  let TU := Stacks.SheafOfModules.canonicalDerivedTensorProduct.{max c u, u, d} (X.over V)
  have : QuasiIso ((restrictionComplex X V).map a) := inferInstance
  let eAP : DerivedCategory.Q.obj ((restrictionComplex X V).obj A) ≅
      DerivedCategory.Q.obj P :=
    asIso (DerivedCategory.Q.map ((restrictionComplex X V).map a)) ≪≫
      (asIso (DerivedCategory.Q.map q)).symm
  (RingedSite.derivedRestriction.{c, u, u, d} X V).mapIso
      ((T.tensor.mapIso (asIso (DerivedCategory.Q.map a) ≪≫ eE).symm).app _) ≪≫
    restrictDerivedTensorKFlatIso X V T A G hA ≪≫
    tensorComplexIsoOfKFlat X V TU _ P _
      (Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall.kFlat_restrictionComplex X V A hA)
      (isKFlat_of_isStrictlyPerfect (Y := X.over V) P hP) eAP

omit [EssentiallySmall.{u} X.C] [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ U : X.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.over U).O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d} (RingedSite.Modules.{c, u, u} X)] hSliceDerived in
/-- **A strictly perfect model restricts along an arrow of the site.** -/
theorem exists_model_of_map (E' : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ)
    {V W : X.C} (g : W ⟶ V)
    (P : CochainComplex (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ)
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P)
    (q : P ⟶ X.restrictComplex E' V) (hq : QuasiIso q) :
    ∃ (P' : CochainComplex (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ)
      (_ : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) P')
      (_ : ∀ n, IsZero (P.X n) → IsZero (P'.X n))
      (q' : P' ⟶ X.restrictComplex E' W), QuasiIso q' := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O
  have : PreservesFiniteLimits (SheafOfModules.overMap.{u} R g) :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits g
  have : PreservesFiniteColimits (SheafOfModules.overMap.{u} R g) :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits g
  refine ⟨Stacks.SheafOfModules.restrictComplexAlongGeneral R g P,
    Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general R g hP,
    fun n hn => (SheafOfModules.overMap.{u} R g).map_isZero hn,
    ((SheafOfModules.overMap.{u} R g).mapHomologicalComplex (ComplexShape.up ℤ)).map q ≫
      (Stacks.SheafOfModules.overFunctorMapComplexIso R g).hom.app E', ?_⟩
  have : (SheafOfModules.overMap.{u} R g).Additive := ⟨by intros; ext; rfl⟩
  have h1 : QuasiIso (((SheafOfModules.overMap.{u} R g).mapHomologicalComplex
      (ComplexShape.up ℤ)).map q) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology q (SheafOfModules.overMap.{u} R g)
  have h2 : QuasiIso ((Stacks.SheafOfModules.overFunctorMapComplexIso R g).hom.app E') :=
    inferInstance
  exact quasiIso_comp _ _

/-- **Local models of a derived tensor product with a perfect factor.** For `E` perfect and `G`
any complex of `O`-modules there is a family of objects covering the final object and, on each
member `V`, a strictly perfect complex `P` of `O|_V`-modules with
`(E ⊗^L_O G)|_V ≅ Q(Tot(P ⊗_{O|_V} G|_V))`. -/
theorem exists_coversTop_restrict_tensor_models (T : DerivedTensorProduct.{c, u, u, d} X)
    (E : RingedSite.DerivedModules.{c, u, u, d} X)
    (hE : X.IsPerfect E) (G : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ) :
    ∃ (K : Type (max c u)) (V : K → X.C), X.J.CoversTop V ∧
      ∀ k, ∃ P : CochainComplex (SliceModules X (V k)) ℤ,
        IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over (V k))) P ∧
        Nonempty ((RingedSite.derivedRestriction.{c, u, u, d} X (V k)).obj
            ((T.tensor.obj E).obj (DerivedCategory.Q.obj G)) ≅
          DerivedCategory.Q.obj (restrictTensorComplex X (V k) P G)) := by
  obtain ⟨E', hE', ⟨eE⟩⟩ := hE
  obtain ⟨K, V, hV, hmod⟩ := X.exists_coversTop_isStrictlyPerfect_of_isPerfectComplex E' hE'
  refine ⟨K, V, hV, fun k => ?_⟩
  obtain ⟨P, hP, q, hq⟩ := hmod k
  exact ⟨P, hP, ⟨restrictDerivedTensorIsoOfModel X T E E' eE (V k) P hP q hq G⟩⟩

omit [EssentiallySmall.{u} X.C]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O) (ComplexShape.up ℤ)] in
/-- **The cohomology of an object with a local tensor model vanishes, on the member, outside the
range of the model.**  If `K|_V ≅ Q(Tot(P ⊗ G|_V))` with `P` zero outside `[aP, bP]` and `G` zero
outside `[aG, bG]`, then the restriction to `V` of `Hⁿ(K)` vanishes for `n` outside
`[aP + aG, bP + bG]`. -/
theorem isZero_restrict_homology_of_model (V : X.C) (K : RingedSite.DerivedModules.{c, u, u, d} X)
    (P : CochainComplex (SliceModules X V) ℤ)
    (G : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ)
    (e : (RingedSite.derivedRestriction.{c, u, u, d} X V).obj K ≅
      DerivedCategory.Q.obj (restrictTensorComplex X V P G))
    (aP bP aG bG : ℤ) (hP : ∀ p : ℤ, p < aP ∨ bP < p → IsZero (P.X p))
    (hG : ∀ q : ℤ, q < aG ∨ bG < q → IsZero (G.X q)) (n : ℤ) (hn : n < aP + aG ∨ bP + bG < n) :
    IsZero ((restriction X V).obj ((DerivedCategory.homologyFunctor _ n).obj K)) := by
  have hX : IsZero ((restrictTensorComplex X V P G).X n) :=
    Stacks.TotalComplexTerms.isZero_mapBifunctor_X_of_bounds
      (Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.O.over V))
      P ((restrictionComplex X V).obj G) aP bP aG bG hP
      (fun q hq => (restriction X V).map_isZero (hG q hq)) n hn
  have hH : IsZero ((restrictTensorComplex X V P G).homology n) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _ hX
  exact hH.of_iso (((DerivedCategory.homologyFunctorFactors _ n).app _).symm.trans
    ((DerivedCategory.homologyFunctor _ n).mapIso e.symm ≪≫
      (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (restriction X V) n).app _)).symm

end DerivedTensorProduct.OfEssentiallySmall

end Stacks.SheafOfModules

end
