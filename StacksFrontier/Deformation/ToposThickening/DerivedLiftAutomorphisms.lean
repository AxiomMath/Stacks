module

public import StacksFrontier.CategoryTheory.Triangulated.TriangleAutomorphisms
public import StacksFrontier.Deformation.ToposThickening.DerivedComplexLift
public import StacksFrontier.Homology.Injectives.FilteredComplex.HomComplex

/-!
# Automorphisms of a lift of a bounded above derived complex

Let `f : O ⟶ O₀` be a surjection of sheaves of commutative rings on a site whose kernel is an
ideal sheaf `I` of square zero, let `K₀` be a bounded above object of the derived category of
`O₀`-modules, and let `(K, α)` be a lift of `K₀` across `f` in the sense of
`Deformation.ComplexLift.DerivedLift`. An automorphism of the pair is an automorphism `φ` of
`K` whose derived base change is the identity, and this file identifies the group of these
automorphisms with the cokernel of a map
`Ext⁻¹(K₀, K₀) ⟶ Hom(K₀, K₀ ⊗^L I)`.

The mechanism is the short exact sequence `0 ⟶ I ⟶ O ⟶ O₀ ⟶ 0`, which turns the reduction of
`K` into a distinguished triangle

`K ⊗^L I ⟶ K ⟶ K ⊗^L O₀ ⟶ (K ⊗^L I)⟦1⟧`

in the derived category of `O`-modules whose second morphism is the unit of the adjunction
between derived base change and restriction of scalars. Because `I` has square zero the first
term is restricted from `O₀`-modules, so every morphism out of `K` into it factors through the
unit; the automorphisms of `K` fixing the unit are then exactly the morphisms `𝟙 + t ≫ ι`, and
two of them agree exactly when the parameters differ by one coming from the shifted third term.
That is the general statement
`CategoryTheory.Pretriangulated.Triangle.autFixingMor₂MulEquiv`, and the content of this file
is its translation into the two `Ext` groups of the source along the adjunction and the
identification `α`.

## Main definitions

* `Deformation.ComplexLift.DerivedReduction`: the reduction triangle of a square-zero
  extension, as data: a derived restriction functor right adjoint to derived base change,
  commuting with the shift, together with the distinguished triangle above.
* `Deformation.ComplexLift.automorphismsOfLift`: **Stacks 0DIZ**, the automorphisms of a lift.
* `Deformation.ComplexLift.boundary`: **Stacks 0DIZ (1)**, the map
  `Ext⁻¹(K₀, K₀) ⟶ Hom(K₀, K₀ ⊗^L I)` whose cokernel the automorphisms are.

## Main results

* `Deformation.ComplexLift.DerivedReduction.hasSquareZeroMor₁`: every morphism from `K` into
  the ideal part of its reduction triangle is killed by the inclusion of that ideal part.
* `Deformation.ComplexLift.automorphismsOfLift_eq_autFixingMor₂`: an automorphism of `K` has
  trivial derived base change exactly when it fixes the unit of the adjunction.
* `Deformation.ComplexLift.automorphismsOfLiftMulEquiv`: **Stacks 0DIZ (1)**, the
  automorphisms of a lift are the cokernel of `boundary`.

## Implementation notes

Following `Deformation.ComplexLift.DerivedExtensionOfScalars`, derived base change is a
parameter rather than a construction, and for the same reason the reduction triangle is taken
as data: Stacks 0DIZ is a statement about lifts, not about the construction of
`- ⊗^L_O O₀`, of its right adjoint, or of the triangle attached to
`0 ⟶ I ⟶ O ⟶ O₀ ⟶ 0`. Only the universal properties of those objects are used, and no field
of `DerivedReduction` mentions automorphisms, cokernels or exactness: every such statement
below is proved. The derived tensor product `- ⊗^L_{O₀} I` enters only through the functor
`idealTensor`, which is a parameter for the same reason. Each of those parameters is inhabited:
derived base change by `Deformation.ComplexLift.nonempty_derivedExtensionOfScalars` and the
reduction triangle, for a square-zero extension, by
`Deformation.ComplexLift.nonempty_derivedReduction`.

`Ext⁻¹(K₀, K₀)` and `Hom(K₀, K₀ ⊗^L I)` are written as the groups of morphisms
`K₀ ⟶ K₀⟦-1⟧` and `K₀ ⟶ idealTensor.obj K₀` in the derived category of `O₀`-modules; the two
derived categories keep the independent hom universes `d` and `d₀` of
`Deformation.ComplexLift.DerivedExtensionOfScalars`.

## References

* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
* [Stacks Project, Tag 0DIY](https://stacks.math.columbia.edu/tag/0DIY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated

universe d d₀ v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} {f : O ⟶ O₀}
variable [HasDerivedCategory.{d}
  (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))]
variable [HasDerivedCategory.{d₀}
  (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))]

/-- The reduction triangle of a square-zero extension `f : O ⟶ O₀` with ideal sheaf `I`,
relative to a derived base change `T` and the derived tensor product `idealTensor` with `I`:
a right adjoint `restriction` of `T.baseChange` commuting with the shift, and for every
object `K` of the derived category of `O`-modules a distinguished triangle

`K ⊗^L I ⟶ K ⟶ K ⊗^L O₀ ⟶ (K ⊗^L I)⟦1⟧`

whose second morphism is the unit of the adjunction. This is the triangle attached to the
short exact sequence `0 ⟶ I ⟶ O ⟶ O₀ ⟶ 0`; squareness of the ideal is what makes its first
term restricted from `O₀`-modules, which is how it is recorded here. -/
structure DerivedReduction (T : DerivedExtensionOfScalars f)
    (idealTensor :
      DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀)))) ⥤
      DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))) where
  /-- Restriction of scalars along `f`, on derived categories. -/
  restriction :
    DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀)))) ⥤
    DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))
  /-- Restriction of scalars is additive. -/
  additive : restriction.Additive
  /-- Restriction of scalars commutes with the shift. -/
  commShift : restriction.CommShift ℤ
  /-- Derived base change is left adjoint to restriction of scalars. -/
  adjunction : T.baseChange ⊣ restriction
  /-- The inclusion of the ideal part of a complex. -/
  idealInclusion
      (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))) :
    restriction.obj (idealTensor.obj (T.baseChange.obj K)) ⟶ K
  /-- The connecting morphism of the reduction triangle. -/
  connecting
      (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))) :
    restriction.obj (T.baseChange.obj K) ⟶
      (restriction.obj (idealTensor.obj (T.baseChange.obj K)))⟦(1 : ℤ)⟧
  /-- The reduction triangle is distinguished. -/
  distinguished
      (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))) :
    Triangle.mk (idealInclusion K) (adjunction.unit.app K) (connecting K) ∈ distTriang _

attribute [instance] DerivedReduction.additive DerivedReduction.commShift

/-- **Stacks 0DIZ.** The automorphisms of a lift `(K, α)` of `K₀`: the automorphisms of `K`
whose derived base change is the identity. Since `α` is an isomorphism these are exactly the
automorphisms of the pair, and the subgroup does not depend on `α`. -/
@[stacks 0DIZ "the automorphism group of a lift"]
noncomputable def automorphismsOfLift (T : DerivedExtensionOfScalars f)
    {K₀ :
      DerivedCategory.Minus (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))}
    (L : DerivedLift T K₀) : Subgroup (Aut L.K.obj) :=
  MonoidHom.ker (T.baseChange.mapAut L.K.obj)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- An automorphism of `K` lies in the automorphism group of the lift exactly when its derived
base change is the identity. -/
theorem mem_automorphismsOfLift_iff {T : DerivedExtensionOfScalars f}
    {K₀ :
      DerivedCategory.Minus (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))}
    {L : DerivedLift T K₀} (φ : Aut L.K.obj) :
    φ ∈ automorphismsOfLift T L ↔ T.baseChange.map φ.hom = 𝟙 _ := by
  rw [automorphismsOfLift, MonoidHom.mem_ker]
  exact ⟨fun h => (congrArg Iso.hom h :), fun h => Aut.ext h⟩

namespace DerivedReduction

variable {T : DerivedExtensionOfScalars f}
  {idealTensor :
    DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀)))) ⥤
    DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))}
  (R : DerivedReduction T idealTensor)

/-- The reduction triangle `K ⊗^L I ⟶ K ⟶ K ⊗^L O₀ ⟶ (K ⊗^L I)⟦1⟧` of an object `K`. -/
noncomputable def triangle
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))) :
    Triangle
      (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))) :=
  Triangle.mk (R.idealInclusion K) (R.adjunction.unit.app K) (R.connecting K)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The reduction triangle of `K` is distinguished. -/
theorem triangle_mem_distTriang
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))) :
    R.triangle K ∈ distTriang _ := R.distinguished K

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The inclusion of the ideal part followed by the unit of the adjunction is zero. -/
theorem idealInclusion_comp_unit
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))) :
    R.idealInclusion K ≫ R.adjunction.unit.app K = 0 :=
  comp_distTriang_mor_zero₁₂ _ (R.distinguished K)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Every morphism from `K` into an object restricted from `O₀`-modules factors through the
unit of the adjunction, hence is annihilated by the inclusion of the ideal part. This is where
squareness of the ideal is used: it is what puts the ideal part of the reduction triangle in
the image of restriction of scalars. -/
theorem idealInclusion_comp_eq_zero
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))))
    (N : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀)))))
    (s : K ⟶ R.restriction.obj N) : R.idealInclusion K ≫ s = 0 := by
  obtain ⟨g, hg⟩ : ∃ g, s = R.adjunction.unit.app K ≫ R.restriction.map g :=
    ⟨(R.adjunction.homEquiv K N).symm s,
      ((R.adjunction.homEquiv K N).apply_symm_apply s).symm.trans
        (R.adjunction.homEquiv_unit K N _)⟩
  rw [hg, ← Category.assoc, R.idealInclusion_comp_unit K, Limits.zero_comp]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The reduction triangle has square-zero first morphism. -/
theorem hasSquareZeroMor₁
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))) :
    (R.triangle K).HasSquareZeroMor₁ :=
  fun s => R.idealInclusion_comp_eq_zero K _ s

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- An automorphism of `K` lies in the automorphism group of the reduction triangle fixing its
second morphism exactly when it fixes the unit of the adjunction. -/
theorem mem_triangle_autFixingMor₂_iff
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))))
    (φ : Aut K) :
    φ ∈ (R.triangle K).autFixingMor₂ ↔
      φ.hom ≫ R.adjunction.unit.app K = R.adjunction.unit.app K :=
  Triangle.mem_autFixingMor₂ (R.triangle K)

/-- The connecting map of the reduction triangle of `K`, with its source and target written
out: postcomposition with the morphism `(K ⊗^L O₀)⟦-1⟧ ⟶ K ⊗^L I` of the inverse rotation. -/
noncomputable def reductionConnecting
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))) :
    (K ⟶ (R.restriction.obj (T.baseChange.obj K))⟦(-1 : ℤ)⟧) →+
      (K ⟶ R.restriction.obj (idealTensor.obj (T.baseChange.obj K))) :=
  (R.triangle K).connecting

/-- The unipotent automorphisms along the inclusion of the ideal part, with the source group
written out. -/
noncomputable def reductionUnipotentHom
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))) :
    Multiplicative (K ⟶ R.restriction.obj (idealTensor.obj (T.baseChange.obj K))) →*
      Aut K :=
  Triangle.unipotentHom (R.hasSquareZeroMor₁ K)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The unipotent automorphisms along the ideal part are exactly the automorphisms of `K`
fixing the unit of the adjunction. -/
theorem reductionUnipotentHom_range
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))) :
    (R.reductionUnipotentHom K).range = (R.triangle K).autFixingMor₂ :=
  Triangle.unipotentHom_range (R.triangle_mem_distTriang K) (R.hasSquareZeroMor₁ K)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The kernel of the unipotent automorphism map is the image of the connecting map of the
reduction triangle. -/
theorem reductionUnipotentHom_ker
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))) :
    (R.reductionUnipotentHom K).ker =
      AddSubgroup.toSubgroup (R.reductionConnecting K).range :=
  Triangle.unipotentHom_ker (R.triangle_mem_distTriang K) (R.hasSquareZeroMor₁ K)

/-- The adjunction between derived base change and restriction of scalars, as an isomorphism
of the additive groups of morphisms. -/
noncomputable def homAddEquiv
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O)))))
    (N : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))) :
    (T.baseChange.obj K ⟶ N) ≃+ (K ⟶ R.restriction.obj N) where
  toFun := R.adjunction.homEquiv K N
  invFun := (R.adjunction.homEquiv K N).symm
  left_inv := (R.adjunction.homEquiv K N).left_inv
  right_inv := (R.adjunction.homEquiv K N).right_inv
  map_add' g g' := by
    simp only [Adjunction.homEquiv_unit, Functor.map_add, Preadditive.comp_add]

end DerivedReduction

section Lift

variable {T : DerivedExtensionOfScalars f}
  {idealTensor :
    DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀)))) ⥤
    DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))}
  (R : DerivedReduction T idealTensor)
  {K₀ : DerivedCategory.Minus (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))}
  (L : DerivedLift T K₀)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- An automorphism of `K` has trivial derived base change exactly when it fixes the unit of
the adjunction, by the universal property of the unit. -/
theorem automorphismsOfLift_eq_autFixingMor₂ :
    automorphismsOfLift T L = (R.triangle L.K.obj).autFixingMor₂ := by
  have hiff : ∀ φ : Aut L.K.obj, T.baseChange.map φ.hom = 𝟙 _ ↔
      φ.hom ≫ R.adjunction.unit.app L.K.obj = R.adjunction.unit.app L.K.obj := by
    intro φ
    have hn : φ.hom ≫ R.adjunction.unit.app L.K.obj =
        R.adjunction.unit.app L.K.obj ≫ R.restriction.map (T.baseChange.map φ.hom) :=
      R.adjunction.unit.naturality φ.hom
    refine ⟨fun h => by rw [hn, h, CategoryTheory.Functor.map_id]; exact Category.comp_id _,
      fun hφ => (R.adjunction.homEquiv L.K.obj (T.baseChange.obj L.K.obj)).injective ?_⟩
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id,
      ← hn, hφ]
    exact (Category.comp_id _).symm
  exact Subgroup.ext fun φ => (mem_automorphismsOfLift_iff φ).trans
    ((hiff φ).trans (R.mem_triangle_autFixingMor₂_iff L.K.obj φ).symm)

/-- The identification of `Hom(K₀, K₀ ⊗^L I)` with the morphisms from `K` into the ideal part
of its reduction triangle: adjunction, after transport along the identification `α`. -/
noncomputable def fiberAddEquiv :
    (K₀.obj ⟶ idealTensor.obj K₀.obj) ≃+
      (L.K.obj ⟶ R.restriction.obj (idealTensor.obj (T.baseChange.obj L.K.obj))) :=
  (Stacks.Injectives.homCongrAddEquiv L.identification.symm
      (idealTensor.mapIso L.identification).symm).trans
    (R.homAddEquiv L.K.obj (idealTensor.obj (T.baseChange.obj L.K.obj)))

/-- The identification of `Ext⁻¹(K₀, K₀)` with the morphisms from `K` into the shift by `-1`
of the reduction of `K`: adjunction and the commutation of restriction of scalars with the
shift, after transport along the identification `α`. -/
noncomputable def shiftedReductionAddEquiv :
    (K₀.obj ⟶ K₀.obj⟦(-1 : ℤ)⟧) ≃+
      (L.K.obj ⟶ (R.restriction.obj (T.baseChange.obj L.K.obj))⟦(-1 : ℤ)⟧) :=
  ((Stacks.Injectives.homCongrAddEquiv L.identification.symm
        (((CategoryTheory.shiftFunctor
            (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀)))))
            (-1 : ℤ)).mapIso
          L.identification).symm)).trans
      (R.homAddEquiv L.K.obj ((T.baseChange.obj L.K.obj)⟦(-1 : ℤ)⟧))).trans
    (Stacks.Injectives.homCongrAddEquiv (Iso.refl L.K.obj)
      ((R.restriction.commShiftIso (-1 : ℤ)).app (T.baseChange.obj L.K.obj)))

/-- **Stacks 0DIZ.** The canonical map `Ext⁻¹(K₀, K₀) ⟶ Hom(K₀, K₀ ⊗^L I)`: the connecting map
of the reduction triangle of `K`, read in the two groups of the source through the adjunction
and the identification `α`. -/
@[stacks 0DIZ "part (1): the map whose cokernel the automorphism group is"]
noncomputable def boundary :
    (K₀.obj ⟶ K₀.obj⟦(-1 : ℤ)⟧) →+ (K₀.obj ⟶ idealTensor.obj K₀.obj) :=
  ((fiberAddEquiv R L).symm.toAddMonoidHom.comp
      (R.reductionConnecting L.K.obj)).comp (shiftedReductionAddEquiv R L).toAddMonoidHom

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The boundary map unfolded: the connecting map read through the two identifications. -/
theorem boundary_apply (s : K₀.obj ⟶ K₀.obj⟦(-1 : ℤ)⟧) :
    boundary R L s = (fiberAddEquiv R L).symm
      (R.reductionConnecting L.K.obj (shiftedReductionAddEquiv R L s)) := rfl

/-- The comparison homomorphism: `t` goes to the automorphism `𝟙 + t ≫ ι` of `K`, where `ι` is
the inclusion of the ideal part of the reduction triangle and `t` is read in
`Hom(K, K ⊗^L I)` through the adjunction. -/
noncomputable def comparisonHom :
    Multiplicative (K₀.obj ⟶ idealTensor.obj K₀.obj) →* Aut L.K.obj :=
  (R.reductionUnipotentHom L.K.obj).comp
    (AddMonoidHom.toMultiplicative (fiberAddEquiv R L).toAddMonoidHom)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The comparison homomorphism unfolded: the unipotent automorphism of the transported
morphism. -/
theorem comparisonHom_apply (t : Multiplicative (K₀.obj ⟶ idealTensor.obj K₀.obj)) :
    comparisonHom R L t = R.reductionUnipotentHom L.K.obj
      (Multiplicative.ofAdd (fiberAddEquiv R L (Multiplicative.toAdd t))) := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The comparison homomorphism is onto the automorphisms of the lift. -/
theorem comparisonHom_range :
    (comparisonHom R L).range = automorphismsOfLift T L := by
  rw [automorphismsOfLift_eq_autFixingMor₂ R L, ← R.reductionUnipotentHom_range L.K.obj]
  refine SetLike.coe_injective ?_
  rw [MonoidHom.coe_range, MonoidHom.coe_range]
  have hs : Function.Surjective
      (AddMonoidHom.toMultiplicative (fiberAddEquiv R L).toAddMonoidHom) :=
    (fiberAddEquiv R L).surjective
  exact hs.range_comp ⇑(R.reductionUnipotentHom L.K.obj)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- A morphism lies in the image of the boundary map exactly when its transport lies in the
image of the connecting map of the reduction triangle. -/
theorem mem_boundary_range_iff (t : K₀.obj ⟶ idealTensor.obj K₀.obj) :
    t ∈ (boundary R L).range ↔
      fiberAddEquiv R L t ∈ (R.reductionConnecting L.K.obj).range := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨shiftedReductionAddEquiv R L s, by rw [boundary_apply, AddEquiv.apply_symm_apply]⟩
  · rintro ⟨g, hg⟩
    exact ⟨(shiftedReductionAddEquiv R L).symm g, by
      rw [boundary_apply, AddEquiv.apply_symm_apply, hg, AddEquiv.symm_apply_apply]⟩

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The kernel of the comparison homomorphism is the image of the boundary map. -/
theorem comparisonHom_ker :
    (comparisonHom R L).ker = AddSubgroup.toSubgroup (boundary R L).range := by
  ext t
  rw [MonoidHom.mem_ker, comparisonHom_apply, Multiplicative.mem_toSubgroup,
    mem_boundary_range_iff, ← MonoidHom.mem_ker, R.reductionUnipotentHom_ker L.K.obj,
    Multiplicative.mem_toSubgroup, toAdd_ofAdd]

/-- **Stacks 0DIZ (1).** The automorphisms of a lift `(K, α)` of `K₀` form the cokernel of the
canonical map `Ext⁻¹(K₀, K₀) ⟶ Hom(K₀, K₀ ⊗^L I)`. -/
@[stacks 0DIZ "part (1): the automorphisms of a lift are a cokernel"]
noncomputable def automorphismsOfLiftMulEquiv :
    Multiplicative (K₀.obj ⟶ idealTensor.obj K₀.obj) ⧸
        AddSubgroup.toSubgroup (boundary R L).range ≃* automorphismsOfLift T L :=
  (QuotientGroup.quotientMulEquivOfEq (comparisonHom_ker R L).symm).trans
    ((QuotientGroup.quotientKerEquivRange (comparisonHom R L)).trans
      (MulEquiv.subgroupCongr (comparisonHom_range R L)))

end Lift

end Deformation.ComplexLift

end
