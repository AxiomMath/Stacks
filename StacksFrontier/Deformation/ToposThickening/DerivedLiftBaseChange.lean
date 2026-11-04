module

public import StacksFrontier.Deformation.ToposThickening.DerivedLiftConnectingClass

/-!
# Base change of lifts of a bounded above complex, and naturality of the difference class

Let `f : O ⟶ O₀` and `f' : O' ⟶ O₀` be surjections of sheaves of commutative rings on the same
site with square-zero kernels `I` and `I'`, and let `K₀ ∈ D⁻(O₀)`. A morphism `O ⟶ O'` over
`O₀` induces a derived base change `β : D(O) ⥤ D(O')` with `(β K) ⊗^L_{O'} O₀ ≅ K ⊗^L_O O₀`,
so it carries a lift `(K, α)` of `K₀` across `f` to a lift `(β K, α)` across `f'`, and it maps
`K₀ ⊗^L I` to `K₀ ⊗^L I'`. The difference class of Stacks 0DIZ is natural for this: the
difference class of the base-changed lifts is the image of the difference class of the lifts.

This is the input that makes the classes of the lifts of a complex over `k[V]`, in the proof of
Stacks 0DLL, natural in the finite-dimensional vector space `V`: a linear map `V ⟶ W` induces
the map `k[V] ⟶ k[W]`, hence a morphism of the two square-zero thickenings of the special fibre.

The base change is recorded by `Deformation.ComplexLift.DerivedReductionBaseChange`: the functor
`β`, the fact that it preserves bounded above objects, the identification of the two derived
base changes to `O₀`, the map of ideal parts, and the one property that relates the two
reduction triangles, namely that `β` carries the obstruction class of Stacks 0DIY of a
morphism of reductions to the obstruction class of its base change. Everything below is formal
from that property.

## Main definitions

* `Deformation.ComplexLift.DerivedReductionBaseChange`: a base change between two reduction
  triangles, compatible with the obstruction classes of Stacks 0DIY.
* `Deformation.ComplexLift.DerivedLift.baseChange`: the base change of a lift.
* `Deformation.ComplexLift.DerivedReductionBaseChange.liftClassMap`: the induced map on
  isomorphism classes of lifts.

## Main results

* `Deformation.ComplexLift.liftDifference_eq_extLiftObstruction`: the difference class of two
  lifts is the obstruction class of Stacks 0DIY of the comparison of their identifications,
  conjugated by the identifications.
* `Deformation.ComplexLift.extLiftObstruction_baseChange_of_connecting`: the compatibility of
  the obstruction classes with a base change, from the compatibility of the connecting
  morphisms of the reduction triangles at the target, by adjunction alone.
* `Deformation.ComplexLift.DerivedLift.Isomorphic.baseChange`: base change preserves
  isomorphy of lifts.
* `Deformation.ComplexLift.liftDifference_baseChange`: **naturality of the difference class**,
  the difference class of two base-changed lifts is the image of their difference class under
  the map of ideal parts (for a second lift in `D^{≤ 0}`).
* `Deformation.ComplexLift.liftClassMap_baseChange`: the same for the bijection
  `[L'] ↦ liftDifference R L' L` of Stacks 0DIZ (2).

## References

* [Stacks Project, Tag 0DIY](https://stacks.math.columbia.edu/tag/0DIY)
* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

open CategoryTheory

universe d d' d₀ v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

section Difference

variable {O O₀ : Sheaf J CommRingCat.{u}} {f : O ⟶ O₀}
variable
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
variable {T : DerivedExtensionOfScalars f}
  {idealTensor : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))}
  (R : DerivedReduction T idealTensor)
  {K₀ : DerivedCategory.Minus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))}

/-- The identification of `Ext¹(K₀, K₀ ⊗^L I)` with the group of the obstructions of a pair of
lifts is the identification of Stacks 0DIY at the underlying objects, conjugated by the two
identifications with `K₀`. -/
theorem obstructionAddEquiv_eq_extObstructionAddEquiv (L₁ L₂ : DerivedLift T K₀)
    (ξ : K₀.obj ⟶ (idealTensor.obj K₀.obj)⟦(1 : ℤ)⟧) :
    obstructionAddEquiv R L₁ L₂ ξ =
      R.extObstructionAddEquiv L₁.K.obj L₂.K.obj (L₁.identification.hom ≫ ξ ≫
        (idealTensor.map L₂.identification.inv)⟦(1 : ℤ)⟧') := by
  rw [obstructionAddEquiv_apply]
  simp only [DerivedReduction.extObstructionAddEquiv, AddEquiv.trans_apply,
    Stacks.Injectives.homCongrAddEquiv_apply, DerivedReduction.homAddEquiv_apply, Iso.refl_inv,
    Category.id_comp, Iso.app_hom]

/-- **The difference class is an obstruction class.** The difference class of two lifts
`(K₁, α₁)` and `(K₂, α₂)` of `K₀` is the obstruction class of Stacks 0DIY of the comparison
`α₁ ≫ α₂⁻¹` of their reductions, read in `Ext¹(K₀, K₀ ⊗^L I)` along `α₁` and `α₂`. -/
theorem liftDifference_eq_extLiftObstruction (L₁ L₂ : DerivedLift T K₀) :
    liftDifference R L₁ L₂ =
      L₁.identification.inv ≫
        R.extLiftObstruction L₁.K.obj L₂.K.obj
          (L₁.identification.hom ≫ L₂.identification.inv) ≫
        (idealTensor.map L₂.identification.hom)⟦(1 : ℤ)⟧' := by
  refine (AddEquiv.symm_apply_eq _).2 ?_
  rw [obstructionAddEquiv_eq_extObstructionAddEquiv, DerivedReduction.extLiftObstruction]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← CategoryTheory.Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id, AddEquiv.apply_symm_apply]

end Difference

section BaseChange

variable {O O' O₀ : Sheaf J CommRingCat.{u}} {f : O ⟶ O₀} {f' : O' ⟶ O₀}
variable
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
variable {T : DerivedExtensionOfScalars f} {T' : DerivedExtensionOfScalars f'}
  {idealTensor idealTensor' :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))}
  (R : DerivedReduction T idealTensor) (R' : DerivedReduction T' idealTensor')

/-- **Base change of obstruction classes from the connecting morphisms.** Let `β ⊣ G` be an
adjunction `D(O) ⇄ D(O')`, `φ : (β -) ⊗^L_{O'} O₀ ≅ - ⊗^L_O O₀` and
`ρ : G ∘ (restriction along f') ≅ restriction along f`, compatible with the shift, such that the
transpose along `f` of `φ⁻¹ ≫ x` is the transpose along `f'` and then along `β ⊣ G` of `x`. If
the connecting morphisms of the reduction triangles of `K₂` and of `β K₂` correspond, through
`φ`, `ρ` and a map `u` of ideal parts, then `β` carries the obstruction class of Stacks 0DIY of
any `α : K₁ ⊗^L O₀ ⟶ K₂ ⊗^L O₀` to that of its base change, followed by `u`.

This is the formal half of the base change of obstruction classes: the only input that sees the
reduction triangles is the comparison `hconn` of the connecting morphisms at `K₂`. -/
theorem extLiftObstruction_baseChange_of_connecting
    {β : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))}
    {G : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O')) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    [G.CommShift ℤ] (adj : β ⊣ G) (φ : β ⋙ T'.baseChange ≅ T.baseChange)
    (ρ : R'.restriction ⋙ G ≅ R.restriction) [NatTrans.CommShift ρ.hom ℤ]
    (hφ : ∀ (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
      (Y : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)))
      (x : T'.baseChange.obj (β.obj K) ⟶ Y),
      R.adjunction.homEquiv K Y (φ.inv.app K ≫ x) =
        adj.homEquiv K _ (R'.adjunction.homEquiv _ Y x) ≫ ρ.hom.app Y)
    (u : idealTensor ⟶ idealTensor')
    (K₁ K₂ : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (hconn : R.restriction.map (φ.inv.app K₂) ≫ ρ.inv.app _ ≫
        G.map (R'.connecting (β.obj K₂)) ≫ (G.commShiftIso (1 : ℤ)).hom.app _ ≫
        (ρ.hom.app _)⟦(1 : ℤ)⟧' =
      R.connecting K₂ ≫
        (R.restriction.map (u.app (T.baseChange.obj K₂) ≫
          idealTensor'.map (φ.inv.app K₂)))⟦(1 : ℤ)⟧')
    (α : T.baseChange.obj K₁ ⟶ T.baseChange.obj K₂) :
    R'.extLiftObstruction (β.obj K₁) (β.obj K₂) (φ.hom.app K₁ ≫ α ≫ φ.inv.app K₂) =
      φ.hom.app K₁ ≫ R.extLiftObstruction K₁ K₂ α ≫
        (u.app (T.baseChange.obj K₂))⟦(1 : ℤ)⟧' ≫
        (idealTensor'.map (φ.inv.app K₂))⟦(1 : ℤ)⟧' := by
  refine (AddEquiv.symm_apply_eq _).2 ?_
  rw [R'.liftObstruction_eq_homEquiv]
  simp only [DerivedReduction.extObstructionAddEquiv, AddEquiv.trans_apply,
    Stacks.Injectives.homCongrAddEquiv_apply, DerivedReduction.homAddEquiv_apply, Iso.refl_inv,
    Category.id_comp, Iso.app_hom]
  apply (adj.homEquiv K₁ _).injective
  have key : ∀ (Y : DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)))
      (x : T'.baseChange.obj (β.obj K₁) ⟶ Y),
      adj.homEquiv K₁ _ (R'.adjunction.homEquiv _ Y x) =
        R.adjunction.homEquiv K₁ Y (φ.inv.app K₁ ≫ x) ≫ ρ.inv.app Y := by
    intro Y x
    rw [hφ]
    simp
  rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_right, key, key,
    Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app_assoc, R.adjunction.homEquiv_naturality_right,
    R.adjunction.homEquiv_naturality_right]
  have he : R.adjunction.homEquiv _ _ (R.extLiftObstruction K₁ K₂ α) =
      R.adjunction.homEquiv _ _ α ≫ R.connecting K₂ ≫
        (R.restriction.commShiftIso (1 : ℤ)).inv.app _ := by
    have h := R.extObstructionAddEquiv_extLiftObstruction K₁ K₂ α
    simp only [DerivedReduction.extObstructionAddEquiv, AddEquiv.trans_apply,
      Stacks.Injectives.homCongrAddEquiv_apply, DerivedReduction.homAddEquiv_apply, Iso.refl_inv,
      Category.id_comp, Iso.app_hom] at h
    rw [R.liftObstruction_eq_homEquiv] at h
    rw [← Category.assoc, ← h]
    simp
  have hρ := NatTrans.shift_app_comm ρ.inv (1 : ℤ)
    (idealTensor'.obj (T'.baseChange.obj (β.obj K₂)))
  rw [Functor.commShiftIso_comp_hom_app] at hρ
  rw [he, ← cancel_mono ((G.commShiftIso (1 : ℤ)).hom.app _)]
  simp only [Category.assoc]
  have hn := (R.restriction.commShiftIso (1 : ℤ)).hom.naturality
    (u.app (T.baseChange.obj K₂) ≫ idealTensor'.map (φ.inv.app K₂))
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn hconn ⊢
  rw [← hρ, ← Functor.map_comp (shiftFunctor _ (1 : ℤ)), reassoc_of% hn, Iso.inv_hom_id_app_assoc,
    ← reassoc_of% hconn]
  simp

/-- **A base change between two reduction triangles.** For reduction triangles `R` and `R'`
of derived base changes along `f : O ⟶ O₀` and `f' : O' ⟶ O₀`, with ideal parts `- ⊗^L I` and
`- ⊗^L I'`: a functor `β : D(O) ⥤ D(O')` preserving bounded above objects, an identification of
`(β -) ⊗^L_{O'} O₀` with `- ⊗^L_O O₀`, a map `- ⊗^L I ⟶ - ⊗^L I'` of ideal parts, such that `β`
carries the obstruction class of Stacks 0DIY of a morphism `α` of reductions to the image of
that obstruction class under the map of ideal parts.

This is what the derived base change along a morphism `O ⟶ O'` of square-zero extensions of
`O₀` provides, with the map of ideal parts induced by `I ⟶ I'`. -/
structure DerivedReductionBaseChange where
  /-- The base change functor `D(O) ⥤ D(O')`. -/
  functor : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
  /-- It preserves bounded above objects. -/
  minus (K : DerivedCategory.Minus
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))) :
    DerivedCategory.TStructure.t.minus (functor.obj K.obj)
  /-- Base change to `O'` and then to `O₀` is base change to `O₀`. -/
  baseChangeIso : functor ⋙ T'.baseChange ≅ T.baseChange
  /-- The map of ideal parts. -/
  idealMap : idealTensor ⟶ idealTensor'
  /-- The base change of the obstruction class of a morphism of reductions is the obstruction
  class of the base-changed morphism, for a target in `D^{≤ 0}` (where the reduction triangles
  of `K₂` and `β K₂` are computed by one flat resolution strictly in degrees `≤ 0`). -/
  extLiftObstruction_eq
    (K₁ K₂ : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    [K₂.IsLE 0] (α : T.baseChange.obj K₁ ⟶ T.baseChange.obj K₂) :
    R'.extLiftObstruction (functor.obj K₁) (functor.obj K₂)
        (baseChangeIso.hom.app K₁ ≫ α ≫ baseChangeIso.inv.app K₂) =
      baseChangeIso.hom.app K₁ ≫ R.extLiftObstruction K₁ K₂ α ≫
        (idealMap.app (T.baseChange.obj K₂))⟦(1 : ℤ)⟧' ≫
        (idealTensor'.map (baseChangeIso.inv.app K₂))⟦(1 : ℤ)⟧'

variable {R R'} (B : DerivedReductionBaseChange R R')
  {K₀ : DerivedCategory.Minus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))}

/-- **The base change of a lift.** A lift `(K, α)` of `K₀` across `f` gives the lift
`(β K, α)` of `K₀` across `f'`, through `(β K) ⊗^L_{O'} O₀ ≅ K ⊗^L_O O₀`. -/
def DerivedLift.baseChange (L : DerivedLift T K₀) : DerivedLift T' K₀ where
  K := ⟨B.functor.obj L.K.obj, B.minus L.K⟩
  identification := B.baseChangeIso.app L.K.obj ≪≫ L.identification

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Base change preserves isomorphy of lifts. -/
theorem DerivedLift.Isomorphic.baseChange {L₁ L₂ : DerivedLift T K₀}
    (h : DerivedLift.Isomorphic L₁ L₂) :
    DerivedLift.Isomorphic (L₁.baseChange B) (L₂.baseChange B) := by
  obtain ⟨e, he⟩ := h
  refine ⟨B.functor.mapIso e, ?_⟩
  have hn : T'.baseChange.map (B.functor.map e.hom) ≫ B.baseChangeIso.hom.app L₂.K.obj =
      B.baseChangeIso.hom.app L₁.K.obj ≫ T.baseChange.map e.hom :=
    B.baseChangeIso.hom.naturality e.hom
  show T'.baseChange.map (B.functor.map e.hom) ≫ B.baseChangeIso.hom.app L₂.K.obj ≫
      L₂.identification.hom = B.baseChangeIso.hom.app L₁.K.obj ≫ L₁.identification.hom
  rw [← he, reassoc_of% hn]

/-- **Naturality of the difference class.** The difference class of Stacks 0DIZ of two
base-changed lifts is the image of the difference class of the two lifts under the map of
ideal parts `K₀ ⊗^L I ⟶ K₀ ⊗^L I'`, when the second lift lies in `D^{≤ 0}`. -/
theorem liftDifference_baseChange (L₁ L₂ : DerivedLift T K₀) [L₂.K.obj.IsLE 0] :
    liftDifference R' (L₁.baseChange B) (L₂.baseChange B) =
      liftDifference R L₁ L₂ ≫ (B.idealMap.app K₀.obj)⟦(1 : ℤ)⟧' := by
  rw [liftDifference_eq_extLiftObstruction, liftDifference_eq_extLiftObstruction]
  dsimp only [DerivedLift.baseChange, Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv]
  have h := B.extLiftObstruction_eq L₁.K.obj L₂.K.obj
    (L₁.identification.hom ≫ L₂.identification.inv)
  simp only [Category.assoc] at h ⊢
  rw [h]
  have hι : idealTensor.map L₂.identification.hom ≫ B.idealMap.app K₀.obj =
      B.idealMap.app _ ≫ idealTensor'.map L₂.identification.hom :=
    B.idealMap.naturality L₂.identification.hom
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← CategoryTheory.Functor.map_comp, hι]

/-- **The base change of isomorphism classes of lifts.** -/
def DerivedReductionBaseChange.liftClassMap :
    Quotient (DerivedLift.setoid (T := T) (K₀ := K₀)) →
      Quotient (DerivedLift.setoid (T := T') (K₀ := K₀)) :=
  Quotient.map (DerivedLift.baseChange B) fun _ _ h => DerivedLift.Isomorphic.baseChange B h

/-- The base change map sends the isomorphism class of a lift `L` to the isomorphism class of
`L.baseChange B`. -/
theorem DerivedReductionBaseChange.liftClassMap_mk (L : DerivedLift T K₀) :
    B.liftClassMap ⟦L⟧ = ⟦L.baseChange B⟧ := rfl

/-- **Naturality of the bijection of Stacks 0DIZ (2).** For a fixed lift `L`, the class
`[L'] ↦ liftDifference R L' L` of a lift relative to `L` is carried by base change to the class
of the base-changed lift relative to the base change of `L`, followed by the map of ideal
parts. -/
theorem liftClassMap_baseChange (L : DerivedLift T K₀) [L.K.obj.IsLE 0]
    (q : Quotient (DerivedLift.setoid (T := T) (K₀ := K₀))) :
    liftClassMap R' (L.baseChange B) (B.liftClassMap q) =
      liftClassMap R L q ≫ (B.idealMap.app K₀.obj)⟦(1 : ℤ)⟧' := by
  induction q using Quotient.inductionOn with
  | h L' => exact liftDifference_baseChange B L' L

end BaseChange

end Deformation.ComplexLift

end
