module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.IdealActionVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TowerOfShortExactSequences
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnitOfSize
import StacksCore.Tactic.StacksAttribute

/-!
# The reduction triangle of a sheaf of ideals

Let `(C, O)` be a ringed site, let `I ⊆ O` be a sheaf of ideals and let `O₀ = O/I` be the
quotient. For every object `K` of the derived category of `O`-modules the short exact sequence

`0 ⟶ I ⟶ O ⟶ O₀ ⟶ 0`

of sheaves of `O`-modules gives a distinguished triangle

`K ⊗^L_O I ⟶ K ⟶ K ⊗^L_O O₀ ⟶ (K ⊗^L_O I)⟦1⟧`

in the derived category of `O`-modules, whose second morphism is the derived tensor product of
`K` with the quotient map. This is the *reduction triangle* of `K`, step (2) of the proof of
[Stacks, Tag 0DIY].

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorProduct.rightUnitor`: `K ⊗^L_O O ≅ K`, for an arbitrary
  object of the derived category.
* `Stacks.SheafOfModules.DerivedTensorProduct.tensorSingleTriangle`: the image under
  `K ⊗^L_O -` of the triangle of a short exact sequence of `O`-modules.
* `Stacks.SheafOfModules.DerivedTensorProduct.reductionTriangle`: the triangle above, for a
  short exact sequence of `O`-modules whose middle term is identified with the structure sheaf.
* `Stacks.Sites.idealReductionTriangle`: the same for a sheaf of ideals and its quotient.
* `Stacks.SheafOfModules.DerivedTensorProduct.reductionObstruction`: the obstruction class of a
  morphism into the reduction of an object, a morphism `L ⟶ (K ⊗^L_O I)⟦1⟧`.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.reductionTriangle_distinguished` and
  `Stacks.Sites.idealReductionTriangle_distinguished`: the reduction triangle is distinguished.
* `Stacks.SheafOfModules.DerivedTensorProduct.reductionObstruction_eq_zero_iff` and
  `Stacks.Sites.idealReductionObstruction_eq_zero_iff`: the obstruction class of a morphism into
  the reduction of `K` vanishes exactly when that morphism comes from a morphism into `K`. This
  is step (3) of the proof of [Stacks, Tag 0DIY], with both sides read in `D(O)`.

## Implementation notes

Tensoring with a fixed object is an exact functor of triangulated categories — the `exact_right`
field of `Stacks.SheafOfModules.DerivedTensorProduct` — so no K-flat resolution is taken here:
the triangle is the image under `K ⊗^L_O -` of the distinguished triangle
`CategoryTheory.ShortComplex.ShortExact.singleTriangle` of the short exact sequence, which is
`Stacks.SheafOfModules.DerivedTensorProduct.mapTriangle_singleTriangle_distinguished`. The only
work is replacing the middle vertex `K ⊗^L_O O` by `K`, which is the right unit constraint, and
an isomorphism of triangles with two identity components transports distinguishedness.

The right unit constraint is built here rather than taken from
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso`: that one is stated for the
parallel `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` structure, with all three
universes of the site collapsed and the standard derived category in force, whereas the triangle
above is available at an independent derived-category universe and at a site all three of whose
universes are free. Only the isomorphism is needed, not its naturality, since the triangle is
built one object at a time; so an arbitrary preimage of `K` under the localization suffices in
place of a chosen K-flat model, the right factor `O[0]` being K-flat already
(`Stacks.SheafOfModules.isKFlat_single_unit_ofSize`).

The sections universe is free of the site. The unit law for the total tensor complex is taken
in the form `Stacks.SheafOfModules.tensorComplexUnitIsoOfSize` of
`StacksFrontier/CategoryTheory/Sites/Modules/TensorUnitOfSize.lean`, which reads the module-level
unitor off the presheaf right unitor carried through sheafification, rather than
`Stacks.SheafOfModules.tensorComplexUnitIso`, which reads it off the monoidal structure of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/MonoidalSheafTensor.lean` and is available only
at `max u v`. The left unit law
`Stacks.SheafOfModules.DerivedTensorProduct.unitTensorSingleIso` still carries that pin, and is
not used here.

## References

* [Stacks Project, Tag 0DIY](https://stacks.math.columbia.edu/tag/0DIY)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe u v w d

namespace Stacks.SheafOfModules.DerivedTensorProduct

open AlgebraicGeometry.RingedSite

variable {X : RingedSite.{u, v, w}}

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable (T : DerivedTensorProduct.{u, v, w, d} X)

/-- The structure sheaf of a ringed site, as an object of `D(O)` placed in degree zero: the
unit of the derived tensor product. -/
abbrev unitObj : DerivedModules.{u, v, w, d} X :=
  (DerivedCategory.singleFunctor (Modules.{u, v, w} X) 0).obj
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The structure sheaf in degree zero is a right unit for the derived tensor product:**
`K ⊗^L_O O ≅ K` for every object `K` of `D(O)`.

The right factor `O[0]` is K-flat, so the K-flat comparison computes the derived tensor product
of any representative of `K` as the ordinary total tensor complex, where the unit law
`Stacks.SheafOfModules.tensorComplexUnitIso` applies; the statement for `K` itself follows by
conjugating with an arbitrary identification of `K` with the image of a representative. -/
def rightUnitor (K : DerivedModules.{u, v, w, d} X) :
    (T.tensor.obj K).obj (unitObj (X := X)) ≅ K :=
  have := Localization.essSurj (DerivedCategory.Q (C := Modules.{u, v, w} X))
    (HomologicalComplex.quasiIso (Modules.{u, v, w} X) (ComplexShape.up ℤ))
  let P := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  ((T.tensor.mapIso e).app (unitObj (X := X))).symm ≪≫
    T.comparisonRight P
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      (Stacks.SheafOfModules.isKFlat_single_unit_ofSize X.O) ≪≫
    DerivedCategory.Q.mapIso (Stacks.SheafOfModules.tensorComplexUnitIsoOfSize X.O P) ≪≫ e

section Reduction

variable {S : ShortComplex (Modules.{u, v, w} X)} (hS : S.ShortExact)
  (e : S.X₂ ≅ _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (K : DerivedModules.{u, v, w, d} X)

/-- The image under `K ⊗^L_O -` of the distinguished triangle of a short exact sequence of
sheaves of `O`-modules. -/
def tensorSingleTriangle : Triangle (DerivedModules.{u, v, w, d} X) :=
  (T.tensor.obj K).mapTriangle.obj hS.singleTriangle

/-- The image under `K ⊗^L_O -` of the triangle of a short exact sequence is distinguished. -/
theorem tensorSingleTriangle_distinguished :
    T.tensorSingleTriangle hS K ∈ distTriang (DerivedModules.{u, v, w, d} X) :=
  mapTriangle_singleTriangle_distinguished T K hS

/-- The identification of the middle vertex `K ⊗^L_O S.X₂` of
`Stacks.SheafOfModules.DerivedTensorProduct.tensorSingleTriangle` with `K`, for a short exact
sequence whose middle term is identified with the structure sheaf.

The type is stated at the vertex of the triangle rather than at
`(T.tensor.obj K).obj ((DerivedCategory.singleFunctor _ 0).obj S.X₂)`: the two are definitionally
equal but not at the transparency at which the triangle API type-checks its commutativity
squares, so the spelling has to be fixed in the stated type of a definition. -/
def middleUnitor : (T.tensorSingleTriangle hS K).obj₂ ≅ K :=
  (T.tensor.obj K).mapIso
      ((DerivedCategory.singleFunctor (Modules.{u, v, w} X) 0).mapIso e) ≪≫
    T.rightUnitor K

/-- **The reduction triangle.** For a short exact sequence `0 ⟶ S.X₁ ⟶ O ⟶ S.X₃ ⟶ 0` of sheaves
of `O`-modules whose middle term is the structure sheaf, and an object `K` of `D(O)`, the
triangle

`K ⊗^L_O S.X₁ ⟶ K ⟶ K ⊗^L_O S.X₃ ⟶ (K ⊗^L_O S.X₁)⟦1⟧`

whose second morphism is the derived tensor product of `K` with the surjection `O ⟶ S.X₃`, read
through the unit law. This is the triangle of step (2) of the proof of [Stacks, Tag 0DIY], at
the square-zero ideal sequence `0 ⟶ I ⟶ O ⟶ O₀ ⟶ 0`. -/
def reductionTriangle : Triangle (DerivedModules.{u, v, w, d} X) :=
  Triangle.mk ((T.tensorSingleTriangle hS K).mor₁ ≫ (T.middleUnitor hS e K).hom)
    ((T.middleUnitor hS e K).inv ≫ (T.tensorSingleTriangle hS K).mor₂)
    ((T.tensorSingleTriangle hS K).mor₃)

/-- The reduction triangle is isomorphic to the image under `K ⊗^L_O -` of the triangle of the
short exact sequence: only the middle vertex is moved. -/
def reductionTriangleIso :
    T.reductionTriangle hS e K ≅ T.tensorSingleTriangle hS K :=
  Triangle.isoMk _ _ (Iso.refl _) (T.middleUnitor hS e K).symm (Iso.refl _)
    (by
      dsimp [reductionTriangle]
      rw [Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id])
    (by dsimp [reductionTriangle]; rw [Category.comp_id])
    (by
      dsimp [reductionTriangle]
      rw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id])

/-- **The reduction triangle is distinguished.** Tensoring with `K` is an exact functor of
triangulated categories, so it carries the distinguished triangle of the short exact sequence to
a distinguished triangle; replacing the middle vertex `K ⊗^L_O O` by `K` along the unit law is an
isomorphism of triangles. -/
theorem reductionTriangle_distinguished :
    T.reductionTriangle hS e K ∈ distTriang (DerivedModules.{u, v, w, d} X) :=
  isomorphic_distinguished _ (T.tensorSingleTriangle_distinguished hS K) _
    (T.reductionTriangleIso hS e K)

/-- **The obstruction class of a morphism into the reduction of `K`.** For a morphism
`β : L ⟶ K ⊗^L_O S.X₃` of `D(O)`, the composite of `β` with the connecting morphism of the
reduction triangle of `K`, a morphism `L ⟶ (K ⊗^L_O S.X₁)⟦1⟧`.

This is the obstruction of [Stacks, Tag 0DIY] in the derived category of `O`-modules: at the
square-zero ideal sequence and `β` the composite of the reduction map `L ⟶ L₀` with a morphism
`α₀ : L₀ ⟶ K₀`, it is the class `o(α₀)`, which the source reads in
`Ext¹_{O₀}(L₀, K₀ ⊗^L_{O₀} I)` by adjunction. -/
def reductionObstruction (L : DerivedModules.{u, v, w, d} X)
    (β : L ⟶ (T.reductionTriangle hS e K).obj₃) :
    L ⟶ ((T.reductionTriangle hS e K).obj₁)⟦(1 : ℤ)⟧ :=
  β ≫ (T.reductionTriangle hS e K).mor₃

/-- **The obstruction class vanishes exactly when the morphism lifts.** A morphism
`β : L ⟶ K ⊗^L_O S.X₃` is the composite of a morphism `L ⟶ K` with the reduction map
`K ⟶ K ⊗^L_O S.X₃` if and only if its composite with the connecting morphism of the reduction
triangle vanishes.

This is step (3) of the proof of [Stacks, Tag 0DIY], read at the reduction triangle itself: the
forward implication is exactness of `Hom(L, -)` at the third vertex of a distinguished triangle,
the converse the vanishing of the composite of the last two morphisms of that triangle. Nothing
is assumed here beyond a derived tensor product on the site: no derived base change along a
morphism of sheaves of rings and no adjunction enter, because both sides of the equivalence are
read in `D(O)`. -/
theorem reductionObstruction_eq_zero_iff (L : DerivedModules.{u, v, w, d} X)
    (β : L ⟶ (T.reductionTriangle hS e K).obj₃) :
    T.reductionObstruction hS e K L β = 0 ↔
      ∃ a : L ⟶ K, a ≫ (T.reductionTriangle hS e K).mor₂ = β := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₃ _ (T.reductionTriangle_distinguished hS e K) β h
    exact ⟨a, ha.symm⟩
  · rintro ⟨a, rfl⟩
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => a ≫ k)
      (comp_distTriang_mor_zero₂₃ _ (T.reductionTriangle_distinguished hS e K))).trans ?_
    exact Limits.comp_zero

end Reduction

end Stacks.SheafOfModules.DerivedTensorProduct

namespace Stacks.Sites

open AlgebraicGeometry.RingedSite Stacks.SheafOfModules

variable {X : RingedSite.{u, v, w}}

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable (T : DerivedTensorProduct.{u, v, w, d} X)
  (I : IdealSubsheaf.{v, u, w} X.O)

omit [HasDerivedCategory.{d} (Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- The short exact sequence `0 ⟶ I ⟶ O ⟶ O/I ⟶ 0` of sheaves of `O`-modules attached to a
sheaf of ideals, with the quotient taken as the cokernel of the inclusion. -/
theorem idealShortExact :
    (ShortComplex.cokernelSequence (I.ι)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact I.ι)
    (inferInstanceAs (Mono I.ι)) (inferInstanceAs (Epi (cokernel.π I.ι)))

/-- **The reduction triangle of a sheaf of ideals:**
`K ⊗^L_O I ⟶ K ⟶ K ⊗^L_O (O/I) ⟶ (K ⊗^L_O I)⟦1⟧`.

This is the triangle attached to `0 ⟶ I ⟶ O ⟶ O₀ ⟶ 0` in step (2) of the proof of
[Stacks, Tag 0DIY]. -/
def idealReductionTriangle (K : DerivedModules.{u, v, w, d} X) :
    Triangle (DerivedModules.{u, v, w, d} X) :=
  T.reductionTriangle (idealShortExact I) (Iso.refl _) K

/-- **The reduction triangle of a sheaf of ideals is distinguished.** -/
theorem idealReductionTriangle_distinguished (K : DerivedModules.{u, v, w, d} X) :
    idealReductionTriangle T I K ∈ distTriang (DerivedModules.{u, v, w, d} X) :=
  T.reductionTriangle_distinguished (idealShortExact I) (Iso.refl _) K

/-- **The obstruction class of a morphism into the reduction of `K` modulo a sheaf of
ideals**, a morphism `L ⟶ (K ⊗^L_O I)⟦1⟧`. -/
def idealReductionObstruction (K L : DerivedModules.{u, v, w, d} X)
    (β : L ⟶ (idealReductionTriangle T I K).obj₃) :
    L ⟶ ((idealReductionTriangle T I K).obj₁)⟦(1 : ℤ)⟧ :=
  T.reductionObstruction (idealShortExact I) (Iso.refl _) K L β

/-- **The obstruction class modulo a sheaf of ideals vanishes exactly when the morphism
lifts.** Step (3) of the proof of [Stacks, Tag 0DIY] at the sequence `0 ⟶ I ⟶ O ⟶ O/I ⟶ 0`. -/
theorem idealReductionObstruction_eq_zero_iff (K L : DerivedModules.{u, v, w, d} X)
    (β : L ⟶ (idealReductionTriangle T I K).obj₃) :
    idealReductionObstruction T I K L β = 0 ↔
      ∃ a : L ⟶ K, a ≫ (idealReductionTriangle T I K).mor₂ = β :=
  T.reductionObstruction_eq_zero_iff (idealShortExact I) (Iso.refl _) K L β

end Stacks.Sites

end
