module

public import StacksFrontier.Deformation.ToposThickening.DerivedLiftObstruction

/-!
# Lifts of a bounded above complex are classified by their connecting morphisms

Let `R` be a reduction triangle (`Deformation.ComplexLift.DerivedReduction`) for a derived base
change `T` along `f : O ⟶ O₀` and a derived tensor product `- ⊗^L I`, and let `K₀ ∈ D⁻(O₀)`.
A lift `(K, α)` of `K₀` has a reduction triangle `R(TK ⊗^L I) ⟶ K ⟶ R(TK) ⟶ R(TK ⊗^L I)⟦1⟧`,
which `α` carries to a triangle `R(K₀ ⊗^L I) ⟶ K ⟶ R(K₀) ⟶ R(K₀ ⊗^L I)⟦1⟧` with outer vertices
depending on `K₀` only. Its third morphism, the *connecting class* of the lift, determines the
lift up to isomorphism: two lifts with the same connecting class are joined by a morphism of
triangles over the identity of the outer vertices, which is an isomorphism and matches up the
identifications with `K₀`.

The difference class `Deformation.ComplexLift.liftDifference` of two lifts is computed by their
connecting classes: if the connecting classes of `L` and `L'` differ by the restriction of a
class `ξ ∈ Ext¹(K₀, K₀ ⊗^L I)`, then the difference class of `L'` relative to `L` is `ξ`.

So as soon as the connecting classes of any two lifts differ by such a restriction, and every
`ξ` is realized as such a difference, the difference class makes the isomorphism classes of
lifts a principal homogeneous space under `Ext¹(K₀, K₀ ⊗^L I)`, and for a fixed lift `L` the map
`[L'] ↦ liftDifference R L' L` is a bijection. Those two inputs are the content of Stacks 0DIZ
(2) at a particular reduction triangle; this file derives the principal homogeneous structure
from them.

## Main definitions

* `Deformation.ComplexLift.connectingClass`: the connecting morphism of a lift, transported to
  the outer vertices `R(K₀)` and `R(K₀ ⊗^L I)`.
* `Deformation.ComplexLift.shiftedRestriction`: a class `ξ : K₀ ⟶ (K₀ ⊗^L I)⟦1⟧` read as a
  morphism `R(K₀) ⟶ R(K₀ ⊗^L I)⟦1⟧`.
* `Deformation.ComplexLift.liftClassEquiv`: for a fixed lift `L`, the bijection
  `[L'] ↦ liftDifference R L' L` between isomorphism classes of lifts and `Ext¹(K₀, K₀ ⊗^L I)`.

## Main results

* `Deformation.ComplexLift.isomorphic_of_connectingClass_eq`: lifts with equal connecting class
  are isomorphic.
* `Deformation.ComplexLift.liftDifference_eq_of_connectingClass_sub`: the difference class is
  read off the difference of connecting classes.
* `Deformation.ComplexLift.exists_addTorsor_liftClasses`: the isomorphism classes of lifts are a
  principal homogeneous space under `Ext¹(K₀, K₀ ⊗^L I)`, the action being characterized by the
  difference class.

## References

* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
* [Stacks Project, Tag 0DIY](https://stacks.math.columbia.edu/tag/0DIY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated

universe d d₀ v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} {f : O ⟶ O₀}
variable
  [HasDerivedCategory.{d} (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))]
variable
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))]

variable {T : DerivedExtensionOfScalars f}
  {idealTensor :
    DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀)))) ⥤
      DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))}
  (R : DerivedReduction T idealTensor)
  {K₀ : DerivedCategory.Minus (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O₀))))}

/-- The connecting morphism of the reduction triangle of a lift `(K, α)` of `K₀`, transported
along `α` to a morphism `R(K₀) ⟶ R(K₀ ⊗^L I)⟦1⟧`. -/
def connectingClass (L : DerivedLift T K₀) :
    R.restriction.obj K₀.obj ⟶ (R.restriction.obj (idealTensor.obj K₀.obj))⟦(1 : ℤ)⟧ :=
  R.restriction.map L.identification.inv ≫ R.connecting L.K.obj ≫
    (R.restriction.map (idealTensor.map L.identification.hom))⟦(1 : ℤ)⟧'

/-- A class `ξ ∈ Ext¹(K₀, K₀ ⊗^L I)` read as a morphism `R(K₀) ⟶ R(K₀ ⊗^L I)⟦1⟧`: its
restriction of scalars followed by the commutation of restriction with the shift. -/
def shiftedRestriction : (K₀.obj ⟶ (idealTensor.obj K₀.obj)⟦(1 : ℤ)⟧) →+
    (R.restriction.obj K₀.obj ⟶ (R.restriction.obj (idealTensor.obj K₀.obj))⟦(1 : ℤ)⟧) where
  toFun ξ := R.restriction.map ξ ≫ (R.restriction.commShiftIso (1 : ℤ)).hom.app _
  map_zero' := by rw [Functor.map_zero, Limits.zero_comp]
  map_add' ξ ξ' := by rw [Functor.map_add, Preadditive.add_comp]

/-- The restricted class of `ξ` is the restriction of `ξ` followed by the commutation of
restriction with the shift. -/
theorem shiftedRestriction_apply (ξ : K₀.obj ⟶ (idealTensor.obj K₀.obj)⟦(1 : ℤ)⟧) :
    shiftedRestriction R ξ =
      R.restriction.map ξ ≫ (R.restriction.commShiftIso (1 : ℤ)).hom.app _ := rfl

/-- The reduction map of a lift, read through its identification, kills its connecting class. -/
theorem unit_comp_connectingClass (L : DerivedLift T K₀) :
    R.adjunction.unit.app L.K.obj ≫ R.restriction.map L.identification.hom ≫
      connectingClass R L = 0 := by
  rw [connectingClass, ← Category.assoc (R.restriction.map L.identification.hom),
    ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp, ← Category.assoc, R.unit_comp_connecting, Limits.zero_comp]

/-- The connecting morphism of the reduction triangle of the underlying object of a lift,
recovered from its connecting class. -/
theorem connecting_eq_connectingClass (L : DerivedLift T K₀) :
    R.connecting L.K.obj = R.restriction.map L.identification.hom ≫ connectingClass R L ≫
      (R.restriction.map (idealTensor.map L.identification.inv))⟦(1 : ℤ)⟧' := by
  simp only [connectingClass, Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    ← CategoryTheory.Functor.map_comp, Category.comp_id]

/-- The reduction triangle of a lift, transported along its identification to the outer
vertices `R(K₀ ⊗^L I)` and `R(K₀)`. -/
def liftTriangle (L : DerivedLift T K₀) : Triangle (DerivedCategory
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))) :=
  Triangle.mk (R.restriction.map (idealTensor.map L.identification.inv) ≫ R.idealInclusion L.K.obj)
    (R.adjunction.unit.app L.K.obj ≫ R.restriction.map L.identification.hom)
    (connectingClass R L)

/-- The transported reduction triangle of a lift is distinguished. -/
theorem liftTriangle_distinguished (L : DerivedLift T K₀) : liftTriangle R L ∈ distTriang _ :=
  isomorphic_distinguished _ (R.distinguished L.K.obj) _
    (Triangle.isoMk _ _ (R.restriction.mapIso (idealTensor.mapIso L.identification.symm))
      (Iso.refl _) (R.restriction.mapIso L.identification.symm)
      (by simp [liftTriangle])
      (by simp [liftTriangle])
      (by
        simp only [liftTriangle, Triangle.mk_mor₃, Triangle.mk_obj₃, Triangle.mk_obj₁,
          Functor.mapIso_hom, Iso.symm_hom]
        rw [connecting_eq_connectingClass R L]
        simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
          CategoryTheory.Functor.map_id, Category.id_comp]))

/-- A morphism of lifts compatible with the reduction maps through the identifications is
compatible with the identifications. -/
private theorem baseChange_map_comp_identification {L₁ L₂ : DerivedLift T K₀}
    (b : L₁.K.obj ⟶ L₂.K.obj)
    (hb : (liftTriangle R L₁).mor₂ = b ≫ (liftTriangle R L₂).mor₂) :
    T.baseChange.map b ≫ L₂.identification.hom = L₁.identification.hom := by
  apply (R.adjunction.homEquiv L₁.K.obj K₀.obj).injective
  have hn : R.adjunction.unit.app L₁.K.obj ≫ R.restriction.map (T.baseChange.map b) =
      b ≫ R.adjunction.unit.app L₂.K.obj := (R.adjunction.unit.naturality b).symm
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, hn, Category.assoc]
  exact hb.symm

/-- **Two lifts with the same connecting class are isomorphic**: their transported reduction
triangles are distinguished triangles with the same outer vertices and the same third morphism,
so a morphism of triangles over the identities joins them, which is an isomorphism matching up
the reduction maps, hence the identifications with `K₀`. -/
theorem isomorphic_of_connectingClass_eq {L₁ L₂ : DerivedLift T K₀}
    (h : connectingClass R L₁ = connectingClass R L₂) : DerivedLift.Isomorphic L₁ L₂ := by
  obtain ⟨b, hb₁, hb₂⟩ := complete_distinguished_triangle_morphism₂ _ _
    (liftTriangle_distinguished R L₁) (liftTriangle_distinguished R L₂) (𝟙 _) (𝟙 _)
    (by simp only [liftTriangle, Triangle.mk_mor₃, CategoryTheory.Functor.map_id, Category.comp_id,
      Category.id_comp, h])
  have hiso : IsIso b := isIso₂_of_isIso₁₃
    (Triangle.homMk (liftTriangle R L₁) (liftTriangle R L₂)
      (𝟙 (R.restriction.obj (idealTensor.obj K₀.obj))) b (𝟙 (R.restriction.obj K₀.obj)) hb₁ hb₂
      (by
        simp only [liftTriangle, Triangle.mk_mor₃, h]
        have e : (shiftFunctor (DerivedCategory (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf O))) (1 : ℤ)).map
              (𝟙 (R.restriction.obj (idealTensor.obj K₀.obj))) = 𝟙 _ :=
          (shiftFunctor _ (1 : ℤ)).map_id _
        rw [e]
        exact (Category.comp_id (connectingClass R L₂)).trans
          (Category.id_comp (connectingClass R L₂)).symm))
    (liftTriangle_distinguished R L₁) (liftTriangle_distinguished R L₂)
    (IsIso.id (R.restriction.obj (idealTensor.obj K₀.obj))) (IsIso.id (R.restriction.obj K₀.obj))
  let b' : L₁.K.obj ⟶ L₂.K.obj := b
  have hiso' : IsIso b' := hiso
  exact ⟨asIso b', baseChange_map_comp_identification R b' ((Category.comp_id _).symm.trans hb₂)⟩

/-- **The difference class is read off the connecting classes.** If the connecting classes of
`L` and `L'` differ by the restriction of `ξ`, then the difference class of `L'` relative to `L`
is `ξ`. -/
theorem liftDifference_eq_of_connectingClass_sub (L' L : DerivedLift T K₀)
    (ξ : K₀.obj ⟶ (idealTensor.obj K₀.obj)⟦(1 : ℤ)⟧)
    (h : connectingClass R L - connectingClass R L' = shiftedRestriction R ξ) :
    liftDifference R L' L = ξ := by
  refine (AddEquiv.symm_apply_eq _).2 ?_
  rw [obstructionAddEquiv_apply, Adjunction.homEquiv_unit, DerivedReduction.liftObstruction,
    connecting_eq_connectingClass R L]
  have hL' := unit_comp_connectingClass R L'
  have hc : connectingClass R L = connectingClass R L' + shiftedRestriction R ξ := by
    rw [← h, add_sub_cancel]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc R.restriction L.identification.inv, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, hc, Preadditive.add_comp, Preadditive.comp_add,
    Preadditive.comp_add, reassoc_of% hL', Limits.zero_comp, zero_add, shiftedRestriction_apply]
  simp only [Category.assoc, Iso.app_hom]
  rw [Functor.commShiftIso_hom_naturality]

/-- For a fixed lift `L`, the map sending a lift `L'` to its difference class relative to `L`,
on isomorphism classes of lifts. -/
def liftClassMap (L : DerivedLift T K₀) :
    Quotient (DerivedLift.setoid (T := T) (K₀ := K₀)) →
      (K₀.obj ⟶ (idealTensor.obj K₀.obj)⟦(1 : ℤ)⟧) :=
  Quotient.lift (fun L' => liftDifference R L' L) fun _ _ h => liftDifference_congr_left R h

/-- The class of a lift `L'` is sent to the difference class of `L'` relative to `L`. -/
theorem liftClassMap_mk (L L' : DerivedLift T K₀) :
    liftClassMap R L ⟦L'⟧ = liftDifference R L' L := rfl

section Classification

variable (hdiff : ∀ L L' : DerivedLift T K₀, ∃ ξ,
  connectingClass R L - connectingClass R L' = shiftedRestriction R ξ)
include hdiff

/-- Under the hypothesis that connecting classes always differ by a restricted class, they differ
by the restriction of the difference class. -/
theorem connectingClass_sub_eq (L L' : DerivedLift T K₀) :
    connectingClass R L - connectingClass R L' = shiftedRestriction R (liftDifference R L' L) := by
  obtain ⟨ξ, hξ⟩ := hdiff L L'
  rw [hξ, liftDifference_eq_of_connectingClass_sub R L' L ξ hξ]

/-- **The difference class is a cocycle.** -/
theorem liftDifference_add (L₁ L₂ L₃ : DerivedLift T K₀) :
    liftDifference R L₁ L₂ + liftDifference R L₂ L₃ = liftDifference R L₁ L₃ := by
  refine (liftDifference_eq_of_connectingClass_sub R L₁ L₃ _ ?_).symm
  rw [map_add, ← connectingClass_sub_eq R hdiff, ← connectingClass_sub_eq R hdiff]
  abel

omit hdiff in
/-- The difference class of a lift relative to an isomorphic one vanishes. -/
theorem liftDifference_eq_zero_of_isomorphic {L₁ L₂ : DerivedLift T K₀}
    (h : DerivedLift.Isomorphic L₁ L₂) : liftDifference R L₁ L₂ = 0 := by
  obtain ⟨e, he⟩ := h
  rw [liftDifference_eq_zero_iff_obstruction_eq_zero, R.liftObstruction_eq_zero_iff]
  exact ⟨e.hom, by rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩

/-- Two lifts are isomorphic exactly when their difference class vanishes. -/
theorem liftDifference_eq_zero_iff_isomorphic (L₁ L₂ : DerivedLift T K₀) :
    liftDifference R L₁ L₂ = 0 ↔ DerivedLift.Isomorphic L₁ L₂ := by
  refine ⟨fun h => ?_, liftDifference_eq_zero_of_isomorphic R⟩
  have h' := connectingClass_sub_eq R hdiff L₂ L₁
  rw [h, map_zero, sub_eq_zero] at h'
  exact isomorphic_of_connectingClass_eq R h'.symm

/-- The difference class depends on its second argument only through its isomorphism class. -/
theorem liftDifference_congr_right {L₁ L₂ L₂' : DerivedLift T K₀}
    (h : DerivedLift.Isomorphic L₂ L₂') : liftDifference R L₁ L₂ = liftDifference R L₁ L₂' := by
  rw [← liftDifference_add R hdiff L₁ L₂ L₂', liftDifference_eq_zero_of_isomorphic R h,
    add_zero]

/-- Isomorphism classes of lifts with the same difference class relative to `L` are equal. -/
theorem liftClassMap_injective (L : DerivedLift T K₀) :
    Function.Injective (liftClassMap R L) := by
  intro x y hxy
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  rename_i L₁ L₂
  rw [liftClassMap_mk, liftClassMap_mk] at hxy
  refine Quotient.sound ((liftDifference_eq_zero_iff_isomorphic R hdiff L₁ L₂).1 ?_)
  have h := liftDifference_add R hdiff L₁ L₂ L
  rw [← hxy] at h
  simpa using h

variable (hreal : ∀ (L : DerivedLift T K₀) (ξ : K₀.obj ⟶ (idealTensor.obj K₀.obj)⟦(1 : ℤ)⟧),
  ∃ L' : DerivedLift T K₀, connectingClass R L - connectingClass R L' = shiftedRestriction R ξ)
include hreal

omit hdiff in
/-- Every class of `Ext¹(K₀, K₀ ⊗^L I)` is the difference class of some lift relative to `L`. -/
theorem liftClassMap_surjective (L : DerivedLift T K₀) :
    Function.Surjective (liftClassMap R L) := by
  intro ξ
  obtain ⟨L', hL'⟩ := hreal L ξ
  exact ⟨⟦L'⟧, liftDifference_eq_of_connectingClass_sub R L' L ξ hL'⟩

/-- **The canonical bijection** between the isomorphism classes of lifts of `K₀` and
`Ext¹(K₀, K₀ ⊗^L I)` attached to a lift `L`: a lift `L'` goes to its difference class relative to
`L`, the obstruction to lifting the comparison of the two identifications with `K₀`. -/
def liftClassEquiv (L : DerivedLift T K₀) :
    Quotient (DerivedLift.setoid (T := T) (K₀ := K₀)) ≃
      (K₀.obj ⟶ (idealTensor.obj K₀.obj)⟦(1 : ℤ)⟧) :=
  Equiv.ofBijective (liftClassMap R L)
    ⟨liftClassMap_injective R hdiff L, liftClassMap_surjective R hreal L⟩

/-- The bijection sends the class of a lift `L'` to its difference class relative to `L`. -/
theorem liftClassEquiv_mk (L L' : DerivedLift T K₀) :
    liftClassEquiv R hdiff hreal L ⟦L'⟧ = liftDifference R L' L := rfl

/-- **The isomorphism classes of lifts are a principal homogeneous space under
`Ext¹(K₀, K₀ ⊗^L I)`**, as soon as there is a lift: there is an action of `Ext¹(K₀, K₀ ⊗^L I)`
on them, simply transitive, under which `ξ` carries the class of `L'` to the class of `L''`
exactly when `ξ` is the difference class of `L''` relative to `L'`. -/
theorem exists_addTorsor_liftClasses [Nonempty (DerivedLift T K₀)] :
    ∃ τ : AddTorsor (K₀.obj ⟶ (idealTensor.obj K₀.obj)⟦(1 : ℤ)⟧)
        (Quotient (DerivedLift.setoid (T := T) (K₀ := K₀))),
      ∀ (ξ : K₀.obj ⟶ (idealTensor.obj K₀.obj)⟦(1 : ℤ)⟧) (L' L'' : DerivedLift T K₀),
        τ.vadd ξ ⟦L'⟧ = ⟦L''⟧ ↔ liftDifference R L'' L' = ξ := by
  obtain ⟨L⟩ := ‹Nonempty (DerivedLift T K₀)›
  let e := liftClassEquiv R hdiff hreal L
  let τ : AddTorsor (K₀.obj ⟶ (idealTensor.obj K₀.obj)⟦(1 : ℤ)⟧)
      (Quotient (DerivedLift.setoid (T := T) (K₀ := K₀))) :=
    { vadd := fun ξ x => e.symm (ξ + e x)
      zero_vadd := fun x => show e.symm (0 + e x) = x by simp
      add_vadd := fun ξ ξ' x => show e.symm ((ξ + ξ') + e x) = e.symm (ξ + e (e.symm (ξ' + e x)))
        by simp [add_assoc]
      vsub := fun x y => e x - e y
      nonempty := ⟨⟦L⟧⟩
      vsub_vadd' := fun x y => show e.symm ((e x - e y) + e y) = x by simp
      vadd_vsub' := fun ξ x => show e (e.symm (ξ + e x)) - e x = ξ by simp }
  refine ⟨τ, fun ξ L' L'' => ?_⟩
  change e.symm (ξ + e ⟦L'⟧) = ⟦L''⟧ ↔ _
  rw [Equiv.symm_apply_eq, liftClassEquiv_mk, liftClassEquiv_mk,
    ← liftDifference_add R hdiff L'' L' L]
  constructor
  · intro h
    exact (add_right_cancel h).symm
  · intro h
    rw [h]

end Classification

/-! ### Natural reduction triangles -/

section Naturality

variable
  (hnat₁ : ∀ {K K' : DerivedCategory (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))} (φ : K ⟶ K'),
    R.idealInclusion K ≫ φ =
      R.restriction.map (idealTensor.map (T.baseChange.map φ)) ≫ R.idealInclusion K')
  (hnat₃ : ∀ {K K' : DerivedCategory (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))} (φ : K ⟶ K'),
    R.connecting K ≫ (R.restriction.map (idealTensor.map (T.baseChange.map φ)))⟦(1 : ℤ)⟧' =
      R.restriction.map (T.baseChange.map φ) ≫ R.connecting K')

include hnat₁ hnat₃

/-- For a natural reduction triangle, a morphism whose derived base change is an isomorphism is
an isomorphism: the morphism of reduction triangles it induces is an isomorphism on the two
outer vertices. -/
theorem isIso_of_isIso_baseChange_map_of_naturality
    {K K' : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (O))))}
    (φ : K ⟶ K') (hφ : IsIso (T.baseChange.map φ)) : IsIso φ :=
  have := hφ
  isIso₂_of_isIso₁₃
    (Triangle.homMk (R.triangle K) (R.triangle K')
      (R.restriction.map (idealTensor.map (T.baseChange.map φ))) φ
      (R.restriction.map (T.baseChange.map φ)) (hnat₁ φ)
      (R.adjunction.unit.naturality φ).symm (hnat₃ φ))
    (R.distinguished K) (R.distinguished K')
    (inferInstanceAs (IsIso (R.restriction.map (idealTensor.map (T.baseChange.map φ)))))
    (inferInstanceAs (IsIso (R.restriction.map (T.baseChange.map φ))))

omit hnat₁ in
/-- For a natural reduction triangle, isomorphic lifts have the same connecting class. -/
theorem connectingClass_eq_of_isomorphic {L L' : DerivedLift T K₀}
    (h : DerivedLift.Isomorphic L L') : connectingClass R L = connectingClass R L' := by
  obtain ⟨e, he⟩ := h
  have hα : L.identification.inv = L'.identification.inv ≫ T.baseChange.map e.inv := by
    rw [← cancel_epi L.identification.hom, Iso.hom_inv_id, ← he, Category.assoc,
      Iso.hom_inv_id_assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id]
  have hn := hnat₃ e.hom
  have hn' : R.restriction.map (T.baseChange.map e.inv) ≫ R.connecting L.K.obj ≫
      (R.restriction.map (idealTensor.map (T.baseChange.map e.hom)))⟦(1 : ℤ)⟧' =
      R.connecting L'.K.obj := by
    rw [hn, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [connectingClass]
  rw [hα, ← he, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc, ← hn']
  simp only [Category.assoc]

omit hnat₁ hnat₃ in
/-- The obstruction class of the comparison of two lifts, read through the identification of the
target lift: the reduction map of the first lift followed by the connecting class of the
second. -/
theorem liftObstruction_identification_eq (L' L : DerivedLift T K₀) :
    R.liftObstruction L'.K.obj L.K.obj (L'.identification.hom ≫ L.identification.inv) =
      (R.adjunction.unit.app L'.K.obj ≫ R.restriction.map L'.identification.hom) ≫
        connectingClass R L ≫
          (R.restriction.map (idealTensor.map L.identification.inv))⟦(1 : ℤ)⟧' := by
  rw [DerivedReduction.liftObstruction, connecting_eq_connectingClass R L]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc,
    ← CategoryTheory.Functor.map_comp_assoc R.restriction L.identification.inv, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

omit hnat₁ hnat₃ in
/-- The identification of `Ext¹(K₀, K₀ ⊗^L I)` with the group of the obstruction class, read
through the identification of the target lift. -/
theorem obstructionAddEquiv_apply_eq (L' L : DerivedLift T K₀)
    (ξ : K₀.obj ⟶ (idealTensor.obj K₀.obj)⟦(1 : ℤ)⟧) :
    obstructionAddEquiv R L' L ξ =
      (R.adjunction.unit.app L'.K.obj ≫ R.restriction.map L'.identification.hom) ≫
        shiftedRestriction R ξ ≫
          (R.restriction.map (idealTensor.map L.identification.inv))⟦(1 : ℤ)⟧' := by
  rw [obstructionAddEquiv_apply, Adjunction.homEquiv_unit, shiftedRestriction_apply]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc, Iso.app_hom]
  rw [Functor.commShiftIso_hom_naturality]

omit hnat₁ hnat₃ in
/-- **The difference class, characterized.** `ξ` is the difference class of `L'` relative to `L`
exactly when the reduction map of `L'` sends the restriction of `ξ` to its image under the
connecting class of `L`. -/
theorem liftDifference_eq_iff (L' L : DerivedLift T K₀)
    (ξ : K₀.obj ⟶ (idealTensor.obj K₀.obj)⟦(1 : ℤ)⟧) :
    liftDifference R L' L = ξ ↔
      (R.adjunction.unit.app L'.K.obj ≫ R.restriction.map L'.identification.hom) ≫
          shiftedRestriction R ξ =
        (R.adjunction.unit.app L'.K.obj ≫ R.restriction.map L'.identification.hom) ≫
          connectingClass R L := by
  rw [liftDifference, AddEquiv.symm_apply_eq, obstructionAddEquiv_apply_eq,
    liftObstruction_identification_eq]
  constructor
  · intro h
    have h' := congrArg (· ≫ (R.restriction.map (idealTensor.map L.identification.hom))⟦(1 : ℤ)⟧')
      h
    simp only [Category.assoc] at h'
    have e : (R.restriction.map (idealTensor.map L.identification.inv))⟦(1 : ℤ)⟧' ≫
        (R.restriction.map (idealTensor.map L.identification.hom))⟦(1 : ℤ)⟧' = 𝟙 _ := by
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
        ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
        CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rw [e, Category.comp_id, Category.comp_id] at h'
    simpa only [Category.assoc] using h'.symm
  · intro h
    have := congrArg (· ≫ (R.restriction.map (idealTensor.map L.identification.inv))⟦(1 : ℤ)⟧') h
    simpa only [Category.assoc] using this.symm

variable (hreal : ∀ (L : DerivedLift T K₀) (ξ : K₀.obj ⟶ (idealTensor.obj K₀.obj)⟦(1 : ℤ)⟧),
  ∃ L' : DerivedLift T K₀, connectingClass R L - connectingClass R L' = shiftedRestriction R ξ)
include hreal

/-- For a natural reduction triangle in which every class is realized as a difference of
connecting classes, any two connecting classes differ by a restricted class. -/
theorem connectingClass_sub_exists (L L' : DerivedLift T K₀) :
    ∃ ξ, connectingClass R L - connectingClass R L' = shiftedRestriction R ξ := by
  obtain ⟨L'', hL''⟩ := hreal L (liftDifference R L' L)
  refine ⟨liftDifference R L' L, ?_⟩
  have h₁ := (liftDifference_eq_iff R L' L (liftDifference R L' L)).1 rfl
  have hk : (R.adjunction.unit.app L'.K.obj ≫ R.restriction.map L'.identification.hom) ≫
      connectingClass R L'' = 0 := by
    have : connectingClass R L'' = connectingClass R L -
        shiftedRestriction R (liftDifference R L' L) := by rw [← hL'', sub_sub_cancel]
    rw [this, Preadditive.comp_sub, h₁, sub_self]
  obtain ⟨b₀, hb⟩ := Triangle.coyoneda_exact₃ (liftTriangle R L'')
    (liftTriangle_distinguished R L'') _ hk
  let b : L'.K.obj ⟶ L''.K.obj := b₀
  have hTb := baseChange_map_comp_identification R b hb
  have hiso : IsIso (T.baseChange.map b) := by
    have : T.baseChange.map b = L'.identification.hom ≫ L''.identification.inv := by
      rw [← hTb, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [this]; infer_instance
  have := isIso_of_isIso_baseChange_map_of_naturality R hnat₁ hnat₃ b hiso
  have hiso' : DerivedLift.Isomorphic L' L'' := ⟨asIso b, hTb⟩
  rw [connectingClass_eq_of_isomorphic R hnat₃ hiso', hL'']

/-- **Stacks 0DIZ (2), abstractly.** For a natural reduction triangle in which every class of
`Ext¹(K₀, K₀ ⊗^L I)` is realized as a difference of connecting classes, the isomorphism classes
of lifts of `K₀` are, as soon as there is one, a principal homogeneous space under
`Ext¹(K₀, K₀ ⊗^L I)`, the class `ξ` carrying `[L']` to `[L'']` exactly when `ξ` is the difference
class of `L''` relative to `L'`. -/
theorem exists_addTorsor_liftClasses_of_naturality [Nonempty (DerivedLift T K₀)] :
    ∃ τ : AddTorsor (K₀.obj ⟶ (idealTensor.obj K₀.obj)⟦(1 : ℤ)⟧)
        (Quotient (DerivedLift.setoid (T := T) (K₀ := K₀))),
      ∀ (ξ : K₀.obj ⟶ (idealTensor.obj K₀.obj)⟦(1 : ℤ)⟧) (L' L'' : DerivedLift T K₀),
        τ.vadd ξ ⟦L'⟧ = ⟦L''⟧ ↔ liftDifference R L'' L' = ξ :=
  exists_addTorsor_liftClasses R (connectingClass_sub_exists R hnat₁ hnat₃ hreal) hreal

end Naturality

end Deformation.ComplexLift

end
