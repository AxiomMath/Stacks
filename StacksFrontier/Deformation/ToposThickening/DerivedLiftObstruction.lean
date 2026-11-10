module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Triangulated.Functor
public import StacksFrontier.Deformation.ToposThickening.DerivedLiftAutomorphisms

/-!
# The obstruction to lifting a morphism of reductions, and the difference of two lifts

Let `f : O ⟶ O₀` be a surjection of sheaves of commutative rings on a site whose kernel is an
ideal sheaf `I` of square zero, let `K₀` be a bounded above object of the derived category of
`O₀`-modules, and let `K₁`, `K₂` be objects of the derived category of `O`-modules. A morphism
`α₀ : K₁ ⊗^L O₀ ⟶ K₂ ⊗^L O₀` between the reductions need not come from a morphism
`K₁ ⟶ K₂`, and the obstruction to its doing so is the composite

`K₁ ⟶ K₂ ⊗^L O₀ ⟶ (K₂ ⊗^L I)⟦1⟧`

of the unit of the adjunction with `α₀` and the connecting morphism of the reduction triangle
of `K₂`. It vanishes exactly when `α₀` is the reduction of a morphism `K₁ ⟶ K₂`, by exactness
of `Hom(K₁, -)` along the reduction triangle.

Applied to two lifts `(K₁, α₁)`, `(K₂, α₂)` of the same `K₀` and to the morphism
`α₁ ≫ α₂⁻¹` of their reductions, this produces the *difference class* of the two lifts in
`Ext¹(K₀, K₀ ⊗^L I)`, and the obstruction statement says that it vanishes exactly when the two
lifts are isomorphic. The implication that needs more than the reduction triangle is that a
morphism of lifts whose reduction is an isomorphism is itself an isomorphism: its cone has zero
reduction, hence both outer vertices of its own reduction triangle vanish, hence the cone
vanishes.

## Main definitions

* `Deformation.ComplexLift.DerivedReduction.liftObstruction`: **Stacks 0DIY**, the obstruction
  class of a morphism of reductions.
* `Deformation.ComplexLift.DerivedReduction.extObstructionAddEquiv`: the identification by
  adjunction of `Ext¹(K₀, L₀ ⊗^L I)` with the group the obstruction class is written in.
* `Deformation.ComplexLift.DerivedReduction.extLiftObstruction`: **Stacks 0DIY**, the same
  obstruction class as an element of `Ext¹(K₀, L₀ ⊗^L I)`.
* `Deformation.ComplexLift.DerivedLift.Isomorphic`: two lifts of `K₀` are isomorphic when an
  isomorphism of the underlying objects matches up their identifications with `K₀`.
* `Deformation.ComplexLift.DerivedLift.setoid`: isomorphy of lifts as an equivalence relation,
  whose quotient is the set of isomorphism classes of lifts.
* `Deformation.ComplexLift.liftDifference`: the difference class in `Ext¹(K₀, K₀ ⊗^L I)` of two
  lifts of `K₀`.

## Main results

* `Deformation.ComplexLift.DerivedReduction.liftObstruction_eq_zero_iff`: **Stacks 0DIY**, the
  obstruction vanishes exactly when the morphism of reductions lifts.
* `Deformation.ComplexLift.DerivedReduction.extLiftObstruction_eq_zero_iff`: **Stacks 0DIY**,
  the same criterion for the class read in `Ext¹(K₀, L₀ ⊗^L I)`.
* `Deformation.ComplexLift.DerivedReduction.isIso_of_isIso_baseChange_map`: a morphism whose
  derived base change is an isomorphism is an isomorphism.
* `Deformation.ComplexLift.DerivedReduction.liftObstruction_baseChange_map_comp`: precomposing a
  morphism of reductions with the reduction of `a : K₁ ⟶ K₂` multiplies its obstruction by `a`.
* `Deformation.ComplexLift.liftDifference_eq_zero_iff`: the difference class of two lifts
  vanishes exactly when they are isomorphic as lifts.
* `Deformation.ComplexLift.liftDifference_self`: the difference class of a lift from itself
  vanishes.
* `Deformation.ComplexLift.liftDifference_congr_left`: the difference class depends on the first
  lift only through its isomorphism class.

## Implementation notes

As in `Deformation.ComplexLift.DerivedLiftAutomorphisms`, the reduction triangle is the data
`Deformation.ComplexLift.DerivedReduction`; nothing below adds a field to it. That datum is
constructed for a square-zero extension by
`Deformation.ComplexLift.nonempty_derivedReduction`, so the parameter `R` below ranges over a
nonempty collection: the statements carrying it are statements about the reduction triangle of
such an extension, and taking the triangle as a parameter rather than fixing the constructed one
keeps them independent of how it is built. Two further
inputs about derived base change are used, and only where they are needed, as instance
arguments: that `T.baseChange` is a triangulated functor, and that the derived tensor product
`- ⊗^L_{O₀} I` is additive. Both are properties of the functors a reduction triangle is built
from rather than statements about lifts, which is why they are hypotheses of the two
declarations that need them instead of fields.

`Ext¹(K₀, K₀ ⊗^L I)` is written as the group of morphisms `K₀ ⟶ (K₀ ⊗^L I)⟦1⟧` in the derived
category of `O₀`-modules, and `Deformation.ComplexLift.obstructionAddEquiv` identifies it with
the group the obstruction of a pair of lifts lives in, by the adjunction, the commutation of
restriction of scalars with the shift, and the two identifications with `K₀`. The first two of
those three steps alone are
`Deformation.ComplexLift.DerivedReduction.extObstructionAddEquiv`, which identifies
`Ext¹(K₀, L₀ ⊗^L I)` with the group `liftObstruction` is written in for an arbitrary pair of
objects `K`, `L`; `Deformation.ComplexLift.DerivedReduction.extLiftObstruction` is the
obstruction class read through it, which is the group Stacks 0DIY names.

## References

* [Stacks Project, Tag 0DIY](https://stacks.math.columbia.edu/tag/0DIY)
* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated

universe d d₀ v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} {f : O ⟶ O₀}
variable
  [HasDerivedCategory.{d} (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))]
variable
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))]

namespace DerivedReduction

variable {T : DerivedExtensionOfScalars f}
  {idealTensor :
    DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀)))) ⥤
      DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))}
  (R : DerivedReduction T idealTensor)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The second morphism of the reduction triangle is the unit of the adjunction. -/
theorem triangle_mor₂
  (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))) :
    (R.triangle K).mor₂ = R.adjunction.unit.app K := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The third morphism of the reduction triangle is the connecting morphism. -/
theorem triangle_mor₃
  (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))) :
    (R.triangle K).mor₃ = R.connecting K := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The last two morphisms of the reduction triangle compose to zero. -/
theorem unit_comp_connecting
  (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))) :
    R.adjunction.unit.app K ≫ R.connecting K = 0 :=
  comp_distTriang_mor_zero₂₃ _ (R.distinguished K)

/-- **Stacks 0DIY.** The obstruction to lifting a morphism `α₀ : K₁ ⊗^L O₀ ⟶ K₂ ⊗^L O₀` of
reductions to a morphism `K₁ ⟶ K₂`: the composite of the unit of the adjunction with `α₀` and
the connecting morphism of the reduction triangle of `K₂`, a morphism
`K₁ ⟶ (K₂ ⊗^L I)⟦1⟧`. -/
@[stacks 0DIY "the obstruction class of a morphism of reductions"]
noncomputable def liftObstruction
    (K₁ K₂ : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))))
    (α₀ : T.baseChange.obj K₁ ⟶ T.baseChange.obj K₂) :
    K₁ ⟶ (R.restriction.obj (idealTensor.obj (T.baseChange.obj K₂)))⟦(1 : ℤ)⟧ :=
  R.adjunction.unit.app K₁ ≫ R.restriction.map α₀ ≫ R.connecting K₂

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Stacks 0DIY.** The obstruction class of `α₀` vanishes exactly when `α₀` is the derived
base change of a morphism `K₁ ⟶ K₂`. The forward implication is exactness of `Hom(K₁, -)` at
the third vertex of the reduction triangle of `K₂`, followed by the universal property of the
unit; the converse is the vanishing of the composite of the last two morphisms of that
triangle. -/
@[stacks 0DIY "the vanishing criterion"]
theorem liftObstruction_eq_zero_iff
    (K₁ K₂ : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))))
    (α₀ : T.baseChange.obj K₁ ⟶ T.baseChange.obj K₂) :
    R.liftObstruction K₁ K₂ α₀ = 0 ↔ ∃ a : K₁ ⟶ K₂, T.baseChange.map a = α₀ := by
  have hn (a : K₁ ⟶ K₂) : a ≫ R.adjunction.unit.app K₂ =
      R.adjunction.unit.app K₁ ≫ R.restriction.map (T.baseChange.map a) :=
    R.adjunction.unit.naturality a
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₃ (R.triangle K₂) (R.distinguished K₂)
      (R.adjunction.unit.app K₁ ≫ R.restriction.map α₀)
      (by rw [R.triangle_mor₃ K₂]; exact (Category.assoc _ _ _).trans h)
    refine ⟨a, (R.adjunction.homEquiv K₁ (T.baseChange.obj K₂)).injective ?_⟩
    refine (R.adjunction.homEquiv_unit K₁ _ _).trans ?_
    refine Eq.trans ?_ (R.adjunction.homEquiv_unit K₁ _ _).symm
    exact (hn a).symm.trans ha.symm
  · rintro ⟨a, rfl⟩
    rw [liftObstruction, ← Category.assoc, ← hn a, Category.assoc, R.unit_comp_connecting,
      Limits.comp_zero]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The underlying function of the adjunction isomorphism of groups of morphisms. -/
theorem homAddEquiv_apply
  (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))))
    (N : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀)))))
      (x : T.baseChange.obj K ⟶ N) :
    R.homAddEquiv K N x = R.adjunction.homEquiv K N x := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The obstruction class, written with the adjunction isomorphism in place of the unit. -/
theorem liftObstruction_eq_homEquiv
    (K₁ K₂ : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))))
    (α₀ : T.baseChange.obj K₁ ⟶ T.baseChange.obj K₂) :
    R.liftObstruction K₁ K₂ α₀ =
      R.adjunction.homEquiv K₁ (T.baseChange.obj K₂) α₀ ≫ R.connecting K₂ :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ R.connecting K₂)
      (R.adjunction.homEquiv_unit K₁ (T.baseChange.obj K₂) α₀).symm)

/-- The identification of `Ext¹_{O₀}(K₀, L₀ ⊗^L_{O₀} I)` with the group of morphisms
`K ⟶ ((L₀ ⊗^L_{O₀} I)|_O)⟦1⟧` in which
`Deformation.ComplexLift.DerivedReduction.liftObstruction` is written: the adjunction between
derived base change and restriction of scalars, followed by the commutation of restriction of
scalars with the shift. This is the identification by adjunction of the proof of Stacks 0DIY,
at an arbitrary pair of objects rather than at a pair of lifts. -/
noncomputable def extObstructionAddEquiv
    (K₁ K₂ : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))) :
    (T.baseChange.obj K₁ ⟶ (idealTensor.obj (T.baseChange.obj K₂))⟦(1 : ℤ)⟧) ≃+
      (K₁ ⟶ (R.restriction.obj (idealTensor.obj (T.baseChange.obj K₂)))⟦(1 : ℤ)⟧) :=
  (R.homAddEquiv K₁ ((idealTensor.obj (T.baseChange.obj K₂))⟦(1 : ℤ)⟧)).trans
    (Stacks.Injectives.homCongrAddEquiv (Iso.refl K₁)
      ((R.restriction.commShiftIso (1 : ℤ)).app (idealTensor.obj (T.baseChange.obj K₂))))

/-- **Stacks 0DIY.** The obstruction class `o(α₀)` of a morphism `α₀ : K₀ ⟶ L₀` of reductions
as an element of `Ext¹_{O₀}(K₀, L₀ ⊗^L_{O₀} I)`, the group the tag states it in:
`Deformation.ComplexLift.DerivedReduction.liftObstruction` read through the adjunction. -/
@[stacks 0DIY "the obstruction class in Ext¹"]
noncomputable def extLiftObstruction
    (K₁ K₂ : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (α₀ : T.baseChange.obj K₁ ⟶ T.baseChange.obj K₂) :
    T.baseChange.obj K₁ ⟶ (idealTensor.obj (T.baseChange.obj K₂))⟦(1 : ℤ)⟧ :=
  (R.extObstructionAddEquiv K₁ K₂).symm (R.liftObstruction K₁ K₂ α₀)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The obstruction class in `Ext¹_{O₀}(K₀, L₀ ⊗^L_{O₀} I)` corresponds to the composite
`Deformation.ComplexLift.DerivedReduction.liftObstruction` under the adjunction. -/
theorem extObstructionAddEquiv_extLiftObstruction
    (K₁ K₂ : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (α₀ : T.baseChange.obj K₁ ⟶ T.baseChange.obj K₂) :
    R.extObstructionAddEquiv K₁ K₂ (R.extLiftObstruction K₁ K₂ α₀) =
      R.liftObstruction K₁ K₂ α₀ :=
  (R.extObstructionAddEquiv K₁ K₂).apply_symm_apply _

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Stacks 0DIY.** The obstruction class in `Ext¹_{O₀}(K₀, L₀ ⊗^L_{O₀} I)` vanishes exactly
when `α₀` is the derived base change of a morphism `K₁ ⟶ K₂`: the identification of that group
with the group of morphisms `K₁ ⟶ ((L₀ ⊗^L_{O₀} I)|_O)⟦1⟧` is an isomorphism, so it reflects
vanishing from `Deformation.ComplexLift.DerivedReduction.liftObstruction_eq_zero_iff`. -/
@[stacks 0DIY "the vanishing criterion in Ext¹"]
theorem extLiftObstruction_eq_zero_iff
    (K₁ K₂ : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (α₀ : T.baseChange.obj K₁ ⟶ T.baseChange.obj K₂) :
    R.extLiftObstruction K₁ K₂ α₀ = 0 ↔ ∃ a : K₁ ⟶ K₂, T.baseChange.map a = α₀ :=
  ((R.extObstructionAddEquiv K₁ K₂).symm.map_eq_zero_iff).trans
    (R.liftObstruction_eq_zero_iff K₁ K₂ α₀)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Precomposing a morphism of reductions with one that comes from a morphism `a : K₁ ⟶ K₂`
multiplies its obstruction class by `a`. This is the equivariance that makes the obstruction
class of a pair of lifts depend only on the isomorphism class of the first lift. -/
theorem liftObstruction_baseChange_map_comp
    (K₁ K₂ K₃ : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))))
      (a : K₁ ⟶ K₂)
    (β₀ : T.baseChange.obj K₂ ⟶ T.baseChange.obj K₃) :
    R.liftObstruction K₁ K₃ (T.baseChange.map a ≫ β₀) =
      a ≫ R.liftObstruction K₂ K₃ β₀ := by
  refine (R.liftObstruction_eq_homEquiv K₁ K₃ _).trans ?_
  refine (congrArg (fun k => k ≫ R.connecting K₃)
    (R.adjunction.homEquiv_naturality_left a β₀)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun k => a ≫ k) (R.liftObstruction_eq_homEquiv K₂ K₃ β₀).symm

include R in
omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- A morphism of the derived category of `O`-modules whose derived base change is an
isomorphism is an isomorphism. Its cone `Z` fits in a distinguished triangle whose image under
`T.baseChange` has an isomorphism for first morphism, so `Z ⊗^L O₀` vanishes; both outer
vertices of the reduction triangle of `Z` are built from `Z ⊗^L O₀` by additive functors, so
they vanish too, and hence so does `Z`. -/
theorem isIso_of_isIso_baseChange_map [T.baseChange.CommShift ℤ]
    [T.baseChange.IsTriangulated] [idealTensor.Additive]
    {K₁ K₂ : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))}
      (a : K₁ ⟶ K₂)
    (ha : IsIso (T.baseChange.map a)) : IsIso a := by
  obtain ⟨Z, i, p, hZ⟩ := Pretriangulated.distinguished_cocone_triangle a
  have hbZ : Limits.IsZero (T.baseChange.obj Z) :=
    (Triangle.isZero₃_iff_isIso₁ _ (T.baseChange.map_distinguished _ hZ)).2 ha
  have hZ0 : Limits.IsZero Z :=
    Triangle.isZero₂_of_isZero₁₃ _ (R.distinguished Z)
      (R.restriction.map_isZero (idealTensor.map_isZero hbZ))
      (R.restriction.map_isZero hbZ)
  exact (Triangle.isZero₃_iff_isIso₁ _ hZ).1 hZ0

end DerivedReduction

namespace DerivedLift

variable {T : DerivedExtensionOfScalars f}
  {K₀ : DerivedCategory.Minus (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))}

/-- Two lifts of `K₀` are *isomorphic* when there is an isomorphism of the underlying objects
of the derived category of `O`-modules whose derived base change carries the identification of
the second lift to that of the first. -/
def Isomorphic (L₁ L₂ : DerivedLift T K₀) : Prop :=
  ∃ e : L₁.K.obj ≅ L₂.K.obj,
    T.baseChange.map e.hom ≫ L₂.identification.hom = L₁.identification.hom

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- A lift is isomorphic to itself. -/
theorem Isomorphic.refl (L : DerivedLift T K₀) : Isomorphic L L :=
  ⟨Iso.refl _, by rw [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp]⟩

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Isomorphy of lifts is symmetric: the inverse isomorphism matches the identifications the
other way round. -/
theorem Isomorphic.symm {L₁ L₂ : DerivedLift T K₀} (h : Isomorphic L₁ L₂) :
    Isomorphic L₂ L₁ := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  rw [Iso.symm_hom, ← he, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Isomorphy of lifts is transitive, by composing the two isomorphisms. -/
theorem Isomorphic.trans {L₁ L₂ L₃ : DerivedLift T K₀} (h : Isomorphic L₁ L₂)
    (h' : Isomorphic L₂ L₃) : Isomorphic L₁ L₃ := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e ≪≫ e', by
    rw [Iso.trans_hom, CategoryTheory.Functor.map_comp, Category.assoc, he', he]⟩

/-- Isomorphy of lifts of `K₀` is an equivalence relation; the isomorphism classes of lifts are
the quotient by it. -/
def setoid : Setoid (DerivedLift T K₀) where
  r := Isomorphic
  iseqv := ⟨Isomorphic.refl, Isomorphic.symm, Isomorphic.trans⟩

end DerivedLift

section Lift

variable {T : DerivedExtensionOfScalars f}
  {idealTensor :
    DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀)))) ⥤
      DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))}
  (R : DerivedReduction T idealTensor)
  {K₀ : DerivedCategory.Minus (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))}
  (L₁ L₂ : DerivedLift T K₀)

/-- The identification of `Ext¹(K₀, K₀ ⊗^L I)` with the group of morphisms
`K₁ ⟶ (K₂ ⊗^L I)⟦1⟧` in which the obstruction of a pair of lifts lives: the adjunction and the
commutation of restriction of scalars with the shift, after transport along the two
identifications with `K₀`. -/
noncomputable def obstructionAddEquiv :
    (K₀.obj ⟶ (idealTensor.obj K₀.obj)⟦(1 : ℤ)⟧) ≃+
      (L₁.K.obj ⟶
        (R.restriction.obj (idealTensor.obj (T.baseChange.obj L₂.K.obj)))⟦(1 : ℤ)⟧) :=
  ((Stacks.Injectives.homCongrAddEquiv L₁.identification.symm
        (((CategoryTheory.shiftFunctor
              (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀)))))
                (1 : ℤ)).mapIso
            (idealTensor.mapIso L₂.identification)).symm)).trans
      (R.homAddEquiv L₁.K.obj ((idealTensor.obj (T.baseChange.obj L₂.K.obj))⟦(1 : ℤ)⟧))).trans
    (Stacks.Injectives.homCongrAddEquiv (Iso.refl L₁.K.obj)
      ((R.restriction.commShiftIso (1 : ℤ)).app (idealTensor.obj (T.baseChange.obj L₂.K.obj))))

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The underlying function of `Deformation.ComplexLift.obstructionAddEquiv`, with the three
conjugations written out. -/
theorem obstructionAddEquiv_apply (ξ : K₀.obj ⟶ (idealTensor.obj K₀.obj)⟦(1 : ℤ)⟧) :
    obstructionAddEquiv R L₁ L₂ ξ =
      R.adjunction.homEquiv L₁.K.obj
          ((idealTensor.obj (T.baseChange.obj L₂.K.obj))⟦(1 : ℤ)⟧)
          (L₁.identification.hom ≫ ξ ≫
            (CategoryTheory.shiftFunctor
                (DerivedCategory
                  (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀)))))
                (1 : ℤ)).map (idealTensor.map L₂.identification.inv)) ≫
        ((R.restriction.commShiftIso (1 : ℤ)).app
          (idealTensor.obj (T.baseChange.obj L₂.K.obj))).hom := by
  simp only [obstructionAddEquiv, AddEquiv.trans_apply,
    Stacks.Injectives.homCongrAddEquiv_apply, DerivedReduction.homAddEquiv_apply, Iso.symm_hom,
    Iso.symm_inv, Iso.refl_inv, Category.id_comp, CategoryTheory.Functor.mapIso_inv]

/-- The difference class in `Ext¹(K₀, K₀ ⊗^L I)` of two lifts of `K₀`: the obstruction to
lifting the comparison `α₁ ≫ α₂⁻¹` of their reductions, read in `Ext¹(K₀, K₀ ⊗^L I)` through
`Deformation.ComplexLift.obstructionAddEquiv`. -/
noncomputable def liftDifference : K₀.obj ⟶ (idealTensor.obj K₀.obj)⟦(1 : ℤ)⟧ :=
  (obstructionAddEquiv R L₁ L₂).symm
    (R.liftObstruction L₁.K.obj L₂.K.obj
      (L₁.identification.hom ≫ L₂.identification.inv))

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The difference class of two lifts vanishes exactly when their obstruction class does, the
identification between the two groups being an isomorphism. -/
theorem liftDifference_eq_zero_iff_obstruction_eq_zero :
    liftDifference R L₁ L₂ = 0 ↔
      R.liftObstruction L₁.K.obj L₂.K.obj
        (L₁.identification.hom ≫ L₂.identification.inv) = 0 :=
  (obstructionAddEquiv R L₁ L₂).symm.map_eq_zero_iff

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The difference class of two lifts of `K₀` vanishes exactly when they are isomorphic as
lifts. This is the injectivity half of the statement that the isomorphism classes of lifts are
a principal homogeneous space under `Ext¹(K₀, K₀ ⊗^L I)`. -/
theorem liftDifference_eq_zero_iff [T.baseChange.CommShift ℤ]
    [T.baseChange.IsTriangulated] [idealTensor.Additive] :
    liftDifference R L₁ L₂ = 0 ↔ DerivedLift.Isomorphic L₁ L₂ := by
  rw [liftDifference_eq_zero_iff_obstruction_eq_zero, R.liftObstruction_eq_zero_iff]
  constructor
  · rintro ⟨a, ha⟩
    have : IsIso (T.baseChange.map a) := by
      rw [ha]
      infer_instance
    have : IsIso a := R.isIso_of_isIso_baseChange_map a this
    refine ⟨asIso a, ?_⟩
    rw [asIso_hom, ha, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rintro ⟨e, he⟩
    exact ⟨e.hom, by rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩

end Lift

section Transport

variable {T : DerivedExtensionOfScalars f}
  {idealTensor :
    DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀)))) ⥤
      DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))}
  (R : DerivedReduction T idealTensor)
  {K₀ : DerivedCategory.Minus (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))}

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The difference class of a lift from itself vanishes: the comparison of its identification
with itself is the identity, which lifts. -/
theorem liftDifference_self (L : DerivedLift T K₀) : liftDifference R L L = 0 := by
  rw [liftDifference_eq_zero_iff_obstruction_eq_zero, R.liftObstruction_eq_zero_iff]
  exact ⟨𝟙 L.K.obj, by rw [CategoryTheory.Functor.map_id, Iso.hom_inv_id]⟩

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Replacing a lift by an isomorphic one precomposes the adjoint of a morphism out of `K₀`
with the comparison isomorphism. -/
theorem homEquiv_identification_comp {L₁ L₁' : DerivedLift T K₀} (e : L₁.K.obj ≅ L₁'.K.obj)
    (he : T.baseChange.map e.hom ≫ L₁'.identification.hom = L₁.identification.hom)
    {W : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))}
      (z : K₀.obj ⟶ W) :
    R.adjunction.homEquiv L₁.K.obj W (L₁.identification.hom ≫ z) =
      e.hom ≫ R.adjunction.homEquiv L₁'.K.obj W (L₁'.identification.hom ≫ z) := by
  rw [← he, Category.assoc, R.adjunction.homEquiv_naturality_left]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Replacing the first of two lifts by an isomorphic one precomposes the identification of
`Ext¹(K₀, K₀ ⊗^L I)` with the comparison isomorphism. -/
theorem obstructionAddEquiv_congr_left {L₁ L₁' L₂ : DerivedLift T K₀}
    (e : L₁.K.obj ≅ L₁'.K.obj)
    (he : T.baseChange.map e.hom ≫ L₁'.identification.hom = L₁.identification.hom)
    (ξ : K₀.obj ⟶ (idealTensor.obj K₀.obj)⟦(1 : ℤ)⟧) :
    obstructionAddEquiv R L₁ L₂ ξ = e.hom ≫ obstructionAddEquiv R L₁' L₂ ξ := by
  rw [obstructionAddEquiv_apply, obstructionAddEquiv_apply,
    homEquiv_identification_comp R e he, Category.assoc]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The difference class of two lifts depends on the first lift only through its isomorphism
class. Together with `Deformation.ComplexLift.liftDifference_eq_zero_iff` this is the
well-definedness and freeness of the putative action of `Ext¹(K₀, K₀ ⊗^L I)` on the
isomorphism classes of lifts, in the first variable. -/
theorem liftDifference_congr_left {L₁ L₁' L₂ : DerivedLift T K₀}
    (h : DerivedLift.Isomorphic L₁ L₁') :
    liftDifference R L₁ L₂ = liftDifference R L₁' L₂ := by
  obtain ⟨e, he⟩ := h
  have ho : R.liftObstruction L₁.K.obj L₂.K.obj
        (L₁.identification.hom ≫ L₂.identification.inv) =
      e.hom ≫ R.liftObstruction L₁'.K.obj L₂.K.obj
        (L₁'.identification.hom ≫ L₂.identification.inv) := by
    rw [← R.liftObstruction_baseChange_map_comp, ← Category.assoc, he]
  simp only [liftDifference, ho]
  refine (AddEquiv.symm_apply_eq _).2 ?_
  rw [obstructionAddEquiv_congr_left R e he, AddEquiv.apply_symm_apply]

end Transport

end Deformation.ComplexLift

end
