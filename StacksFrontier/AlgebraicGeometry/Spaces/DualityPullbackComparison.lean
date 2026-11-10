module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Shift.CommShiftTwo
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
import StacksCore.Tactic.StacksAttribute

/-!
# Comparing the right adjoint of pushforward with derived pullback on algebraic spaces

Let `f : X ⟶ Y` be a morphism of quasi-compact quasi-separated algebraic spaces over a scheme
`S` and let `a` be a right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. For `K, L` in
`D_QCoh(𝒪_Y)` there is a canonical map

  `Lf^*K ⊗ᴸ_{𝒪_X} a(L) ⟶ a(K ⊗ᴸ_{𝒪_Y} L)`,

the map adjoint to the inverse projection formula followed by the identity of `K` tensored with
the trace `Rf_*(a(L)) ⟶ L`. At `L = 𝒪_Y`, composed with `a` applied to the right unitor, it is
the map displayed in [Stacks, Tag 0E5P],

  `Lf^*K ⊗ᴸ_{𝒪_X} a(𝒪_Y) ⟶ a(K)`,

functorial in `K`.

## Main definitions

* `AlgebraicGeometry.Space.derivedStructureSheaf` — `𝒪_F` in degree zero, as an object of
  `D_QCoh(𝒪_F)`.
* `AlgebraicGeometry.Space.PullbackComparisonData` — the derived tensor products of the two
  quasi-coherent derived categories, derived pullback and derived pushforward along `f` with
  their adjunction, and the compatibility of derived pullback with the two tensor products.
* `AlgebraicGeometry.Space.PullbackComparisonData.projectionFormulaMap` — the
  projection-formula map `K ⊗ᴸ_{𝒪_Y} Rf_*E ⟶ Rf_*(Lf^*K ⊗ᴸ_{𝒪_X} E)`.
* `AlgebraicGeometry.Space.PullbackComparisonData.compareWithPullbackTensor` — the two-variable
  comparison map, and
  `AlgebraicGeometry.Space.PullbackComparisonData.compareWithPullback` — the map displayed in
  [Stacks, Tag 0E5P].
* `AlgebraicGeometry.Space.PullbackComparisonData.compareWithPullbackNatTrans` — the displayed
  map as a natural transformation of functors of `K`.

## Main results

All in the namespace `AlgebraicGeometry.Space.PullbackComparisonData`.

* `projectionFormulaMap_comp_map_compareWithPullbackTensor_comp_counit` and
  `compareWithPullbackTensor_eq_of_counit`: the projection formula followed by `Rf_*` of the
  two-variable comparison map and the trace map is the identity of `K` tensored with the trace
  map, and that equation determines the comparison map. For the displayed map the pair is
  `projectionFormulaMap_comp_map_compareWithPullback_comp_counit` and
  `compareWithPullback_eq_of_counit`.
* `compareWithPullback_naturality` — the displayed map is functorial in `K`;
  `compareWithPullbackTensor_naturality_left`, `compareWithPullbackTensor_naturality_right` and
  `compareWithPullbackTensor_naturality` are the naturality of the two-variable map.

## Implementation notes

*Which inputs are data, and why.* The quasi-coherent derived categories of `X` and of `Y` are
the ones of [Stacks, Tag 071X]. On them this repository has neither derived pullback nor derived
pushforward, nor the derived tensor product: derived-level quasi-coherence of the tensor product
is available for schemes only (`Stacks.Duality.isQuasicoherent_homology_derivedTensor`), and no
restriction of derived pullback or of derived pushforward along a morphism of algebraic spaces to
the complexes with quasi-coherent cohomology exists. The two tensor products, the two derived
functors along `f`, their adjunction and the compatibility of derived pullback with the tensor
products are therefore carried as data, exactly as in
`AlgebraicGeometry.Space.TorIndependentBaseChangeSquare.DualityData`.

*Which inputs are hypotheses, and why.* The source cites a result at each remaining point.

* The right adjoint `a` and the adjunction `Rf_* ⊣ a` come from [Stacks, Tag 0E55], an existence
  statement; they are explicit arguments, which is the shape the source's own "let `a` be the
  right adjoint" asks for and the shape in which a consumer has them.
* Invertibility of `projectionFormulaMap` is [Stacks, Tag 08IN], the projection formula for a
  quasi-compact quasi-separated morphism of algebraic spaces. It is hypothesised as an `IsIso`
  instance, a `Prop`, so no further datum enters.
* The right unitor `ρ`, sending `K` to `K ⊗ᴸ_{𝒪_Y} 𝒪_Y ≅ K`, is an explicit argument, as in
  `Stacks.Duality.compareWithPullback`: the carried tensor product is a bifunctor with no unit,
  so there is no unitor to invoke. Taking `ρ` as an isomorphism of functors rather than a family
  of isomorphisms is what makes `compareWithPullback_naturality` follow from naturality of the
  two-variable map. The unit *object* is not hypothesised: it is
  `AlgebraicGeometry.Space.derivedStructureSheaf`.

Each comparison map is a function of those inputs, and `compareWithPullbackTensor_eq_of_counit`
and `compareWithPullback_eq_of_counit` show the inputs determine it uniquely.

*The module universe is `u`.* `AlgebraicGeometry.Space.QuasicoherentDerivedCategory` is stated at
a free universe for the module sections, but `SheafOfModules.isQuasicoherentOnSite_unit` places
the structure sheaf among the quasi-coherent modules only when that universe is the universe of
the structure rings, so `𝒪_F` is an object of `D_QCoh(𝒪_F)` only there.

*Compatibility with distinguished triangles.* For a natural transformation between functors
commuting with translation this is `CategoryTheory.NatTrans.CommShift`; it is
`compareWithPullbackNatTrans_commShift`, with `compareWithPullback_shift` as its componentwise
form. It takes further inputs, of a different kind than the three the source cites: the two
carried tensor products commute with translation in each variable
(`CategoryTheory.Functor.CommShift₂Int`), derived pullback and derived pushforward commute with
translation, `a` does so compatibly with `adja`, and the carried projection formula and the right
unitor commute with translation. The shift on `D_QCoh(𝒪_F)` is not among them: quasi-coherence of
every cohomology sheaf is stable under translation, which is
`derivedCategoryB_isQuasicoherentOnSite_isStableUnderShift`, and the shift of `D(𝒪_F)` descends
along it.

## References

* [Stacks Project, Tag 0E5P](https://stacks.math.columbia.edu/tag/0E5P)
* [Stacks Project, Tag 0E55](https://stacks.math.columbia.edu/tag/0E55)
* [Stacks Project, Tag 08IN](https://stacks.math.columbia.edu/tag/08IN)
* [Stacks Project, Tag 071X](https://stacks.math.columbia.edu/tag/071X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open scoped CategoryTheory.Prod

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

/-! ### The structure sheaf in degree zero -/

section StructureSheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
  [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A quasi-coherent `𝒪_F`-module in degree zero lies in `D_QCoh(𝒪_F)`: its zeroth cohomology
sheaf is the module itself and the others vanish, and a zero module is quasi-coherent. -/
theorem derivedCategoryB_singleFunctor_obj (M : Modules.{u, u} B S hS F hF)
    (hM : M.IsQuasicoherentOnSite) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS F hF) 0).obj M) := by
  intro i
  rcases lt_trichotomy i 0 with h | rfl | h
  · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
      (DerivedCategory.isZero_of_isGE (C := Modules.{u, u} B S hS F hF)
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS F hF) 0).obj M) 0 i h)
  · exact (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (Modules.{u, u} B S hS F hF) 0).app M).symm hM
  · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
      (DerivedCategory.isZero_of_isLE (C := Modules.{u, u} B S hS F hF)
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS F hF) 0).obj M) 0 i h)

/-- The structure sheaf `𝒪_F` in degree zero, as an object of `D_QCoh(𝒪_F)`. -/
def derivedStructureSheaf : QuasicoherentDerivedCategory.{u, u} B S hS F hF :=
  ⟨(DerivedCategory.singleFunctor (Modules.{u, u} B S hS F hF) 0).obj
      (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))),
    derivedCategoryB_singleFunctor_obj B S hS F hF _ inferInstance⟩

end StructureSheaf

/-! ### The data entering the comparison -/

/-- The data entering the comparison of a right adjoint of pushforward with derived pullback
along a morphism `f : X ⟶ Y` of algebraic spaces: `f` is quasi-compact and quasi-separated, the
quasi-coherent derived categories of `X` and of `Y` carry derived tensor products, derived
pullback and derived pushforward along `f` act on them and are adjoint, and derived pullback is
compatible with the two tensor products. -/
structure PullbackComparisonData (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    [HasSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u}]
    [(smallEtaleRingedSite B S hS X.1 X.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify (smallEtaleRingedSite B S hS Y.1 Y.2).J AddCommGrpCat.{u}]
    [(smallEtaleRingedSite B S hS Y.1 Y.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}] where
  /-- The morphism is quasi-compact. -/
  isQuasiCompact : IsQuasiCompact B S hS f.hom
  /-- The morphism is quasi-separated. -/
  isQuasiSeparated : IsQuasiSeparated B S hS f.hom
  /-- The derived tensor product of `D_QCoh(𝒪_X)`, curried. -/
  tensorX : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 ⥤
    QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 ⥤
    QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2
  /-- The derived tensor product of `D_QCoh(𝒪_Y)`, curried. -/
  tensorY : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2 ⥤
    QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2 ⥤
    QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2
  /-- Derived pullback `Lf^*`. -/
  pullback : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2 ⥤
    QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2
  /-- Derived pushforward `Rf_*`. -/
  pushforward : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 ⥤
    QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2
  /-- The adjunction `Lf^* ⊣ Rf_*`. -/
  adj : pullback ⊣ pushforward
  /-- The compatibility of derived pullback with the two tensor products: at `(K₁, K₂)` it is
  the map `Lf^*(K₂ ⊗ᴸ_{𝒪_Y} K₁) ⟶ Lf^*K₂ ⊗ᴸ_{𝒪_X} Lf^*K₁`, natural in both arguments. -/
  tensorPullbackComparison :
    (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj tensorY) ⋙ pullback ⟶
      pullback.prod pullback ⋙
        (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj tensorX)

/-- Morphisms into `G.obj _` are intertwined by `α` and `β` if their transposes are. -/
private theorem adjunction_naturality_of_homEquiv_symm {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {P P' : C} {Q Q' : D} (α : P ⟶ P') (β : Q ⟶ Q')
    (c : P ⟶ G.obj Q) (c' : P' ⟶ G.obj Q')
    (h : F.map α ≫ (adj.homEquiv _ _).symm c' = (adj.homEquiv _ _).symm c ≫ β) :
    α ≫ c' = c ≫ G.map β := by
  apply (adj.homEquiv _ _).symm.injective
  rw [adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_right_symm]
  exact h

namespace PullbackComparisonData

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  [HasSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS X.1 X.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedSite B S hS Y.1 Y.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS Y.1 Y.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (D : PullbackComparisonData B S hS f)

/-! ### The projection-formula map -/

/-- The projection-formula map `K ⊗ᴸ_{𝒪_Y} Rf_*E ⟶ Rf_*(Lf^*K ⊗ᴸ_{𝒪_X} E)`: the adjoint
transpose, for the adjunction `Lf^* ⊣ Rf_*`, of the compatibility of derived pullback with the
two tensor products followed by the counit of that adjunction in the pushforward factor. Its
invertibility is [Stacks, Tag 08IN]. -/
def projectionFormulaMap (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    (D.tensorY.obj K).obj (D.pushforward.obj E) ⟶
      D.pushforward.obj ((D.tensorX.obj (D.pullback.obj K)).obj E) :=
  CategoryTheory.adjunctionTensorMap D.adj
    (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj D.tensorY)
    (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj D.tensorX)
    D.tensorPullbackComparison E K

/-- The projection-formula map is natural in both arguments. -/
theorem projectionFormulaMap_naturality
    {E E' : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2}
    {K K' : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2} (φ : E ⟶ E') (h : K ⟶ K') :
    ((D.tensorY.map h).app (D.pushforward.obj E) ≫
        (D.tensorY.obj K').map (D.pushforward.map φ)) ≫ D.projectionFormulaMap E' K' =
      D.projectionFormulaMap E K ≫
        D.pushforward.map ((D.tensorX.map (D.pullback.map h)).app E ≫
          (D.tensorX.obj (D.pullback.obj K')).map φ) :=
  CategoryTheory.adjunctionTensorMap_natural D.adj
    (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj D.tensorY)
    (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj D.tensorX)
    D.tensorPullbackComparison φ h

/-- Naturality of the projection-formula map in the pulled-back argument. -/
theorem projectionFormulaMap_naturality_left
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    {K K' : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2} (h : K ⟶ K') :
    (D.tensorY.map h).app (D.pushforward.obj E) ≫ D.projectionFormulaMap E K' =
      D.projectionFormulaMap E K ≫
        D.pushforward.map ((D.tensorX.map (D.pullback.map h)).app E) := by
  simpa using D.projectionFormulaMap_naturality (𝟙 E) h

/-- Naturality of the projection-formula map in the pushed-forward argument. -/
theorem projectionFormulaMap_naturality_right
    {E E' : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2} (φ : E ⟶ E')
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    (D.tensorY.obj K).map (D.pushforward.map φ) ≫ D.projectionFormulaMap E' K =
      D.projectionFormulaMap E K ≫
        D.pushforward.map ((D.tensorX.obj (D.pullback.obj K)).map φ) := by
  simpa using D.projectionFormulaMap_naturality φ (𝟙 K)

/-! ### The two-variable comparison map -/

section Comparison

variable [∀ (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2),
    IsIso (D.projectionFormulaMap E K)]
  {a : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2 ⥤
    QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2}
  (adja : D.pushforward ⊣ a)

/-- **The two-variable comparison map of [Stacks, Tag 0E5P]**:
`Lf^*K ⊗ᴸ_{𝒪_X} a(L) ⟶ a(K ⊗ᴸ_{𝒪_Y} L)`, for a right adjoint `a` of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. It is the map adjoint to the inverse of the projection
formula `Rf_*(Lf^*K ⊗ᴸ_{𝒪_X} a(L)) ≅ K ⊗ᴸ_{𝒪_Y} Rf_*(a(L))` followed by the identity of `K`
tensored with the trace map `adja.counit.app L : Rf_*(a(L)) ⟶ L`. -/
@[stacks 0E5P "two-variable construction"]
def compareWithPullbackTensor (K L : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    (D.tensorX.obj (D.pullback.obj K)).obj (a.obj L) ⟶ a.obj ((D.tensorY.obj K).obj L) :=
  adja.homEquiv _ _ (inv (D.projectionFormulaMap (a.obj L) K) ≫
    (D.tensorY.obj K).map (adja.counit.app L))

/-- The adjoint transpose of the two-variable comparison map is the inverse projection formula
followed by the identity of `K` tensored with the trace map. -/
@[stacks 0E5P "two-variable adjunction characterization"]
theorem homEquiv_symm_compareWithPullbackTensor
    (K L : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    (adja.homEquiv _ _).symm (D.compareWithPullbackTensor adja K L) =
      inv (D.projectionFormulaMap (a.obj L) K) ≫
        (D.tensorY.obj K).map (adja.counit.app L) :=
  (adja.homEquiv _ _).symm_apply_apply _

/-- `Rf_*` of the two-variable comparison map followed by the trace map is the inverse
projection formula followed by the identity of `K` tensored with the trace map. -/
theorem map_compareWithPullbackTensor_comp_counit
    (K L : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    D.pushforward.map (D.compareWithPullbackTensor adja K L) ≫
        adja.counit.app ((D.tensorY.obj K).obj L) =
      inv (D.projectionFormulaMap (a.obj L) K) ≫
        (D.tensorY.obj K).map (adja.counit.app L) :=
  D.homEquiv_symm_compareWithPullbackTensor adja K L

/-- **The two-variable comparison map as the source constructs it**: the projection formula,
followed by `Rf_*` of the comparison map and the trace map, is the identity of `K` tensored with
the trace map. This is the characterization with no inverse in it. -/
@[stacks 0E5P "two-variable characterization without the inverse"]
theorem projectionFormulaMap_comp_map_compareWithPullbackTensor_comp_counit
    (K L : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    D.projectionFormulaMap (a.obj L) K ≫
        D.pushforward.map (D.compareWithPullbackTensor adja K L) ≫
          adja.counit.app ((D.tensorY.obj K).obj L) =
      (D.tensorY.obj K).map (adja.counit.app L) := by
  rw [D.map_compareWithPullbackTensor_comp_counit adja, IsIso.hom_inv_id_assoc]

/-- That characterization determines the two-variable comparison map: a morphism satisfying it
is the comparison map. -/
theorem compareWithPullbackTensor_eq_of_counit
    (K L : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    (c : (D.tensorX.obj (D.pullback.obj K)).obj (a.obj L) ⟶ a.obj ((D.tensorY.obj K).obj L))
    (hc : D.projectionFormulaMap (a.obj L) K ≫
        D.pushforward.map c ≫ adja.counit.app ((D.tensorY.obj K).obj L) =
      (D.tensorY.obj K).map (adja.counit.app L)) :
    c = D.compareWithPullbackTensor adja K L := by
  apply (adja.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [D.map_compareWithPullbackTensor_comp_counit adja, IsIso.eq_inv_comp]
  exact hc

/-- The two-variable comparison map is natural in `K`. -/
theorem compareWithPullbackTensor_naturality_left
    {K K' : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2} (h : K ⟶ K')
    (L : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    (D.tensorX.map (D.pullback.map h)).app (a.obj L) ≫
        D.compareWithPullbackTensor adja K' L =
      D.compareWithPullbackTensor adja K L ≫ a.map ((D.tensorY.map h).app L) := by
  have key' : D.pushforward.map ((D.tensorX.map (D.pullback.map h)).app (a.obj L)) ≫
      inv (D.projectionFormulaMap (a.obj L) K') =
    inv (D.projectionFormulaMap (a.obj L) K) ≫
      (D.tensorY.map h).app (D.pushforward.obj (a.obj L)) := by
    rw [IsIso.comp_inv_eq, Category.assoc, D.projectionFormulaMap_naturality_left (a.obj L) h,
      IsIso.inv_hom_id_assoc]
  refine adjunction_naturality_of_homEquiv_symm adja _ _ _ _ ?_
  rw [D.homEquiv_symm_compareWithPullbackTensor adja,
    D.homEquiv_symm_compareWithPullbackTensor adja,
    reassoc_of% key', Category.assoc]
  exact congrArg _ ((D.tensorY.map h).naturality (adja.counit.app L)).symm

/-- The two-variable comparison map is natural in `L`. -/
theorem compareWithPullbackTensor_naturality_right
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    {L L' : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2} (g : L ⟶ L') :
    (D.tensorX.obj (D.pullback.obj K)).map (a.map g) ≫
        D.compareWithPullbackTensor adja K L' =
      D.compareWithPullbackTensor adja K L ≫ a.map ((D.tensorY.obj K).map g) := by
  have key' : D.pushforward.map ((D.tensorX.obj (D.pullback.obj K)).map (a.map g)) ≫
      inv (D.projectionFormulaMap (a.obj L') K) =
    inv (D.projectionFormulaMap (a.obj L) K) ≫
      (D.tensorY.obj K).map (D.pushforward.map (a.map g)) := by
    rw [IsIso.comp_inv_eq, Category.assoc, D.projectionFormulaMap_naturality_right (a.map g) K,
      IsIso.inv_hom_id_assoc]
  refine adjunction_naturality_of_homEquiv_symm adja _ _ _ _ ?_
  rw [D.homEquiv_symm_compareWithPullbackTensor adja,
    D.homEquiv_symm_compareWithPullbackTensor adja,
    reassoc_of% key', Category.assoc]
  refine congrArg _ ?_
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _ (adja.counit_naturality g)

/-- The two-variable comparison map is natural in `K` and `L` jointly. -/
@[stacks 0E5P "two-variable naturality"]
theorem compareWithPullbackTensor_naturality
    {K K' L L' : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2} (h : K ⟶ K') (g : L ⟶ L') :
    (D.tensorX.map (D.pullback.map h)).app (a.obj L) ≫
        (D.tensorX.obj (D.pullback.obj K')).map (a.map g) ≫
          D.compareWithPullbackTensor adja K' L' =
      D.compareWithPullbackTensor adja K L ≫
        a.map ((D.tensorY.map h).app L ≫ (D.tensorY.obj K').map g) := by
  rw [D.compareWithPullbackTensor_naturality_right adja, ← Category.assoc,
    D.compareWithPullbackTensor_naturality_left adja, Category.assoc, ← Functor.map_comp]

/-! ### The displayed comparison map -/

variable (ρ : D.tensorY.flip.obj (derivedStructureSheaf B S hS Y.1 Y.2) ≅ 𝟭 _)

/-- **Equation 86.7.0.1 of [Stacks, Tag 0E5P]**: the comparison map
`Lf^*K ⊗ᴸ_{𝒪_X} a(𝒪_Y) ⟶ a(K)`, the two-variable comparison map at `L = 𝒪_Y` followed by `a`
applied to the right unitor `K ⊗ᴸ_{𝒪_Y} 𝒪_Y ≅ K`. -/
@[stacks 0E5P]
def compareWithPullback (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    (D.tensorX.obj (D.pullback.obj K)).obj
        (a.obj (derivedStructureSheaf B S hS Y.1 Y.2)) ⟶ a.obj K :=
  D.compareWithPullbackTensor adja K (derivedStructureSheaf B S hS Y.1 Y.2) ≫
    a.map (ρ.hom.app K)

/-- `Rf_*` of Equation 86.7.0.1 followed by the trace map is the inverse projection formula
followed by the identity of `K` tensored with the trace map at `𝒪_Y` and the right unitor. -/
theorem map_compareWithPullback_comp_counit
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    D.pushforward.map (D.compareWithPullback adja ρ K) ≫ adja.counit.app K =
      inv (D.projectionFormulaMap (a.obj (derivedStructureSheaf B S hS Y.1 Y.2)) K) ≫
        (D.tensorY.obj K).map (adja.counit.app (derivedStructureSheaf B S hS Y.1 Y.2)) ≫
          ρ.hom.app K := by
  have e : D.compareWithPullback adja ρ K =
      adja.homEquiv _ _
        (inv (D.projectionFormulaMap (a.obj (derivedStructureSheaf B S hS Y.1 Y.2)) K) ≫
          (D.tensorY.obj K).map (adja.counit.app (derivedStructureSheaf B S hS Y.1 Y.2)) ≫
            ρ.hom.app K) := by
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
    rfl
  rw [e]
  exact (adja.homEquiv _ _).symm_apply_apply _

/-- **Equation 86.7.0.1 as the source constructs it**: the projection formula, followed by `Rf_*`
of the displayed comparison map and the trace map, is the identity of `K` tensored with the trace
map at `𝒪_Y`, followed by the right unitor. -/
@[stacks 0E5P "characterization without the inverse"]
theorem projectionFormulaMap_comp_map_compareWithPullback_comp_counit
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    D.projectionFormulaMap (a.obj (derivedStructureSheaf B S hS Y.1 Y.2)) K ≫
        D.pushforward.map (D.compareWithPullback adja ρ K) ≫ adja.counit.app K =
      (D.tensorY.obj K).map (adja.counit.app (derivedStructureSheaf B S hS Y.1 Y.2)) ≫
        ρ.hom.app K := by
  rw [D.map_compareWithPullback_comp_counit adja ρ, IsIso.hom_inv_id_assoc]

/-- That characterization determines Equation 86.7.0.1: a morphism satisfying it is the
displayed comparison map. -/
theorem compareWithPullback_eq_of_counit
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    (c : (D.tensorX.obj (D.pullback.obj K)).obj
      (a.obj (derivedStructureSheaf B S hS Y.1 Y.2)) ⟶ a.obj K)
    (hc : D.projectionFormulaMap (a.obj (derivedStructureSheaf B S hS Y.1 Y.2)) K ≫
        D.pushforward.map c ≫ adja.counit.app K =
      (D.tensorY.obj K).map (adja.counit.app (derivedStructureSheaf B S hS Y.1 Y.2)) ≫
        ρ.hom.app K) :
    c = D.compareWithPullback adja ρ K := by
  apply (adja.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [D.map_compareWithPullback_comp_counit adja ρ, IsIso.eq_inv_comp]
  exact hc

/-- Equation 86.7.0.1 is functorial in `K`. -/
@[stacks 0E5P "functoriality in K"]
theorem compareWithPullback_naturality
    {K K' : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2} (h : K ⟶ K') :
    (D.tensorX.map (D.pullback.map h)).app
          (a.obj (derivedStructureSheaf B S hS Y.1 Y.2)) ≫
        D.compareWithPullback adja ρ K' =
      D.compareWithPullback adja ρ K ≫ a.map h := by
  have hρ : (D.tensorY.map h).app (derivedStructureSheaf B S hS Y.1 Y.2) ≫ ρ.hom.app K' =
      ρ.hom.app K ≫ h := ρ.hom.naturality h
  have hnat := D.compareWithPullbackTensor_naturality_left adja h
    (derivedStructureSheaf B S hS Y.1 Y.2)
  change (D.tensorX.map (D.pullback.map h)).app
        (a.obj (derivedStructureSheaf B S hS Y.1 Y.2)) ≫
      (D.compareWithPullbackTensor adja K' (derivedStructureSheaf B S hS Y.1 Y.2) ≫
        a.map (ρ.hom.app K')) =
    (D.compareWithPullbackTensor adja K (derivedStructureSheaf B S hS Y.1 Y.2) ≫
      a.map (ρ.hom.app K)) ≫ a.map h
  rw [← Category.assoc, hnat, Category.assoc, ← Functor.map_comp, hρ, Functor.map_comp,
    Category.assoc]

end Comparison

/-- The source of Equation 86.7.0.1 as a functor of `K`: derived pullback followed by tensoring
with a fixed object, which for the displayed map is `a(𝒪_Y)`. -/
def compareWithPullbackSource (T : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2 ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
  D.pullback ⋙ D.tensorX.flip.obj T

section NatTrans

variable [∀ (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2),
    IsIso (D.projectionFormulaMap E K)]
  {a : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2 ⥤
    QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2}
  (adja : D.pushforward ⊣ a)
  (ρ : D.tensorY.flip.obj (derivedStructureSheaf B S hS Y.1 Y.2) ≅ 𝟭 _)

/-- Equation 86.7.0.1 as a natural transformation of functors of `K`, which is its
functoriality in `K`. -/
@[stacks 0E5P "functoriality in K, as a natural transformation"]
def compareWithPullbackNatTrans :
    D.compareWithPullbackSource (a.obj (derivedStructureSheaf B S hS Y.1 Y.2)) ⟶ a where
  app K := D.compareWithPullback adja ρ K
  naturality _ _ h := D.compareWithPullback_naturality adja ρ h

end NatTrans

end PullbackComparisonData

/-! ### The shift on the quasi-coherent derived category -/

section Shift

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
  [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Quasi-coherence of every cohomology sheaf is stable under translation: the cohomology
sheaves of `K⟦a⟧` are those of `K`, renumbered. So `D_QCoh(𝒪_F)` carries the shift of the
derived category of `𝒪_F`-modules. -/
instance derivedCategoryB_isQuasicoherentOnSite_isStableUnderShift :
    (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)))).IsStableUnderShift ℤ := by
  refine ⟨fun a => ⟨fun K hK => ?_⟩⟩
  rw [ObjectProperty.prop_shift_iff]
  intro n
  exact (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).prop_of_iso
    (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) 0).shiftIso
      a n (a + n) rfl).app K).symm (hK (a + n))

end Shift

namespace PullbackComparisonData

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  [HasSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS X.1 X.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedSite B S hS Y.1 Y.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS Y.1 Y.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (D : PullbackComparisonData B S hS f)

/-! ### Compatibility with distinguished triangles -/

/-- The projection-formula map as a natural transformation of functors of `K`, the pushed-forward
argument being fixed: at `K` it is `K ⊗ᴸ_{𝒪_Y} Rf_*E ⟶ Rf_*(Lf^*K ⊗ᴸ_{𝒪_X} E)`. -/
def projectionFormulaNatTrans (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    D.tensorY.flip.obj (D.pushforward.obj E) ⟶
      D.compareWithPullbackSource E ⋙ D.pushforward where
  app K := D.projectionFormulaMap E K
  naturality K K' h := by
    simpa [compareWithPullbackSource] using D.projectionFormulaMap_naturality_left E h

/-- The source of Equation 86.7.0.1 commutes with translation when derived pullback and the
derived tensor product of `D_QCoh(𝒪_X)` do. -/
instance compareWithPullbackSource_commShift
    (T : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    [D.pullback.CommShift ℤ] [D.tensorX.CommShift₂Int] :
    (D.compareWithPullbackSource T).CommShift ℤ := by
  unfold compareWithPullbackSource
  infer_instance

section Triangles

variable [∀ (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2),
    IsIso (D.projectionFormulaMap E K)]
  {a : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2 ⥤
    QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2}
  (adja : D.pushforward ⊣ a)
  (ρ : D.tensorY.flip.obj (derivedStructureSheaf B S hS Y.1 Y.2) ≅ 𝟭 _)

/-- The projection formula is an isomorphism of functors of `K`, each of its components being
invertible. -/
instance isIso_projectionFormulaNatTrans
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    IsIso (D.projectionFormulaNatTrans E) := by
  have : ∀ (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2),
      IsIso ((D.projectionFormulaNatTrans E).app K) := fun K =>
    inferInstanceAs (IsIso (D.projectionFormulaMap E K))
  exact NatIso.isIso_of_isIso_app _

/-- The adjoint transpose of Equation 86.7.0.1 as a natural transformation of functors of `K`:
the inverse projection formula, the trace map at `𝒪_Y`, and the right unitor. -/
def compareWithPullbackTranspose :
    D.compareWithPullbackSource (a.obj (derivedStructureSheaf B S hS Y.1 Y.2)) ⋙
        D.pushforward ⟶ 𝟭 _ :=
  inv (D.projectionFormulaNatTrans (a.obj (derivedStructureSheaf B S hS Y.1 Y.2))) ≫
    D.tensorY.flip.map (adja.counit.app (derivedStructureSheaf B S hS Y.1 Y.2)) ≫ ρ.hom

/-- Equation 86.7.0.1 is the adjunct of its transpose: the unit of `Rf_* ⊣ a`, followed by `a`
applied to the transpose. -/
theorem compareWithPullbackNatTrans_eq :
    D.compareWithPullbackNatTrans adja ρ =
      (D.compareWithPullbackSource
            (a.obj (derivedStructureSheaf B S hS Y.1 Y.2))).rightUnitor.inv ≫
        Functor.whiskerLeft _ adja.unit ≫
          (Functor.associator _ D.pushforward a).inv ≫
            Functor.whiskerRight (D.compareWithPullbackTranspose adja ρ) a ≫
              a.leftUnitor.hom := by
  ext K
  simp [compareWithPullbackNatTrans, compareWithPullback, compareWithPullbackTensor,
    compareWithPullbackTranspose, Adjunction.homEquiv_unit, projectionFormulaNatTrans,
    NatIso.isIso_inv_app, compareWithPullbackSource, Functor.map_inv]

variable [D.pullback.CommShift ℤ] [D.pushforward.CommShift ℤ] [D.tensorX.CommShift₂Int]
  [D.tensorY.CommShift₂Int] [a.CommShift ℤ] [adja.CommShift ℤ]
  [NatTrans.CommShift (D.projectionFormulaNatTrans
    (a.obj (derivedStructureSheaf B S hS Y.1 Y.2))) ℤ]
  [NatTrans.CommShift ρ.hom ℤ]

/-- The adjoint transpose of Equation 86.7.0.1 commutes with translation. -/
instance compareWithPullbackTranspose_commShift :
    NatTrans.CommShift (D.compareWithPullbackTranspose adja ρ) ℤ := by
  have := NatTrans.CommShift.of_isIso
    (τ := D.projectionFormulaNatTrans (a.obj (derivedStructureSheaf B S hS Y.1 Y.2))) (A := ℤ)
  unfold compareWithPullbackTranspose
  infer_instance

/-- **Compatibility of Equation 86.7.0.1 with distinguished triangles**: the displayed comparison
map commutes with translation, so it carries the third morphism of a distinguished triangle of
`D_QCoh(𝒪_Y)` to the third morphism of its image. -/
@[stacks 0E5P "compatibility with distinguished triangles"]
theorem compareWithPullbackNatTrans_commShift :
    NatTrans.CommShift (D.compareWithPullbackNatTrans adja ρ) ℤ := by
  rw [D.compareWithPullbackNatTrans_eq adja ρ]
  infer_instance

/-- Equation 86.7.0.1 at a translate of `K`, which is that compatibility componentwise. -/
@[stacks 0E5P "compatibility with distinguished triangles, componentwise"]
theorem compareWithPullback_shift (n : ℤ)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    D.compareWithPullback adja ρ ((shiftFunctor _ n).obj K) =
      ((D.compareWithPullbackSource
          (a.obj (derivedStructureSheaf B S hS Y.1 Y.2))).commShiftIso n).hom.app K ≫
        (shiftFunctor _ n).map (D.compareWithPullback adja ρ K) ≫
          (a.commShiftIso n).inv.app K := by
  have := D.compareWithPullbackNatTrans_commShift adja ρ
  exact NatTrans.app_shift (D.compareWithPullbackNatTrans adja ρ) n K

end Triangles

end PullbackComparisonData

end AlgebraicGeometry.Space

end
