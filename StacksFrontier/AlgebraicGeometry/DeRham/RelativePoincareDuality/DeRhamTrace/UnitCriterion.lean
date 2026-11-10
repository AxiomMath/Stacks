module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.UnitAction
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.TraceUniqueness
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Rescaling the trace of relative Poincaré duality for de Rham cohomology

In the situation of [Stacks, Tag 0G8G] let `s : Rf_*(Ω^•_{X/S}[2n]) ⟶ 𝒪_S` be a trace with the
property of [Stacks, Tag 0G8K]: the pairing `(ξ, ξ') ↦ s(ξ ∪ ξ')` on
`Rf_*Ω^•_{X/S} ⊗^L Rf_*(Ω^•_{X/S}[2n])` is perfect. A global function `g ∈ Γ(X, 𝒪_X)` is closed, so
it acts on `Ω^•_{X/S}`, and precomposing `s` with this action precomposes the pairing with the
action on the first factor: the wedge product is `Γ(X, 𝒪_X)`-linear in its first factor and the
relative cup product is natural. Hence for a unit `g` the rescaled trace has the property again.

Conversely, if `s` and `g · s` both have the property, then multiplication by `g` on
`Rf_*Ω^•_{X/S}` is an isomorphism. Maps `𝒪_S ⟶ Rf_*Ω^•_{X/S}` are maps `f⁻¹𝒪_S[0] ⟶ Ω^•_{X/S}`,
the unit `1` of `Ω^0` is closed and so lifts the identity, and projecting to `Ω^0[0]` shows that
`1` is a multiple of `g`: so `g` is a unit. Finally, multiplication by `g` commutes with the
inclusion `Rf_*Ω^n[n] ⟶ Rf_*(Ω^•[2n])` of the top piece, which compares the action here with the
action on the trace of [Stacks, Tag 0G8I].

## Main results

* `AlgebraicGeometry.RelativeDualitySituation.topInclusion_comp_smul`: the inclusion of the top
  piece is `Γ(X, 𝒪_X)`-linear.
* `AlgebraicGeometry.RelativeDualitySituation.deRhamPoincarePairing_smul_comp`: the pairing of
  `g · s` is the pairing of `s` precomposed with `g` on the first factor.
* `AlgebraicGeometry.RelativeDualitySituation.isDeRhamPoincareTrace_smul_comp`: rescaling by a unit
  preserves the property of [Stacks, Tag 0G8K].
* `AlgebraicGeometry.RelativeDualitySituation.isUnit_of_isDeRhamPoincareTrace_smul_comp`: if `s`
  and `g · s` have the property, `g` is a unit.

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
* [Stacks Project, Tag 0G8I](https://stacks.math.columbia.edu/tag/0G8I)
* [Stacks Project, Tag 0G8H](https://stacks.math.columbia.edu/tag/0G8H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Stacks.StandardDerivedModel
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.DerivedTensor.RingedSite (DerivedModules derivedTensorProductFunctor
  canonicalDerivedTensorProduct)
open Stacks.DeRhamDirectImage (inverseImageBase inverseImageBaseProjection)
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi (TensorHomAdjunction)

universe u

namespace CategoryTheory.Iso

/-- Two commuting squares along isomorphisms paste to a commuting square along their composite. -/
theorem comp_trans_hom_of_comp_hom {C : Type*} [Category* C] {X Y Z : C} (e₁ : X ≅ Y) (e₂ : Y ≅ Z)
    {F : X ⟶ X} {G : Y ⟶ Y} {H : Z ⟶ Z} (h₁ : F ≫ e₁.hom = e₁.hom ≫ G)
    (h₂ : G ≫ e₂.hom = e₂.hom ≫ H) : F ≫ (e₁ ≪≫ e₂).hom = (e₁ ≪≫ e₂).hom ≫ H := by
  rw [Iso.trans_hom, reassoc_of% h₁, h₂, Category.assoc]

end CategoryTheory.Iso

namespace HomologicalComplex

/-- A square out of a single complex commutes as soon as it commutes in the degree of the single
complex. -/
theorem single_map_comp_mkHomFromSingle {V : Type*} [Category* V] [HasZeroMorphisms V]
    [HasZeroObject V] {ι : Type*} [DecidableEq ι] {c : ComplexShape ι}
    {K L : HomologicalComplex V c} {j : ι} {A B : V} (ψ : A ⟶ B) (φA : A ⟶ K.X j)
    (hA : ∀ k, c.Rel j k → φA ≫ K.d j k = 0) (φB : B ⟶ L.X j)
    (hB : ∀ k, c.Rel j k → φB ≫ L.d j k = 0) (χ : K ⟶ L) (h : ψ ≫ φB = φA ≫ χ.f j) :
    (single V c j).map ψ ≫ mkHomFromSingle φB hB = mkHomFromSingle φA hA ≫ χ := by
  refine from_single_hom_ext ?_
  simp [mkHomFromSingle_f, single_map_f_self, h]

/-- A square into a single complex commutes as soon as it commutes in the degree of the single
complex. -/
theorem mkHomToSingle_comp_single_map {V : Type*} [Category* V] [HasZeroMorphisms V]
    [HasZeroObject V] {ι : Type*} [DecidableEq ι] {c : ComplexShape ι}
    {K L : HomologicalComplex V c} {j : ι} {A B : V} (χ : K ⟶ L) (φK : K.X j ⟶ A)
    (hK : ∀ i, c.Rel i j → K.d i j ≫ φK = 0) (φL : L.X j ⟶ B)
    (hL : ∀ i, c.Rel i j → L.d i j ≫ φL = 0) (ψ : A ⟶ B) (h : χ.f j ≫ φL = φK ≫ ψ) :
    χ ≫ mkHomToSingle φL hL = mkHomToSingle φK hK ≫ (single V c j).map ψ := by
  refine to_single_hom_ext ?_
  simp [mkHomToSingle_f, single_map_f_self, reassoc_of% h]

end HomologicalComplex

namespace CategoryTheory.Adjunction

/-- If `R.map f` is an isomorphism for a right adjoint `R`, every map `L Z ⟶ K'` out of the image
of the left adjoint lifts along `f`. -/
theorem exists_comp_eq_of_isIso_map {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) {K K' : D} (f : K ⟶ K') (hf : IsIso (R.map f)) {Z : C}
    (x : L.obj Z ⟶ K') : ∃ z : L.obj Z ⟶ K, z ≫ f = x :=
  ⟨(adj.homEquiv _ _).symm (adj.homEquiv _ _ x ≫ inv (R.map f)), by
    rw [← Adjunction.homEquiv_naturality_right_symm, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id, Equiv.symm_apply_apply]⟩

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

/-- A functor with a left inverse up to isomorphism reflects factorizations: if `w ≫ G.map χ`
is the image of `u` for some `w : G A ⟶ G B`, then `u` factors through `χ`. -/
theorem exists_comp_eq_of_comp_map_eq {C D : Type*} [Category* C] [Category* D] {G : C ⥤ D}
    {H : D ⥤ C} (e : G ⋙ H ≅ 𝟭 C) {A B B' : C} (w : G.obj A ⟶ G.obj B) (χ : B ⟶ B')
    (u : A ⟶ B') (h : w ≫ G.map χ = G.map u) : ∃ ψ : A ⟶ B, ψ ≫ χ = u :=
  ⟨(e.app A).inv ≫ H.map w ≫ (e.app B).hom, by
    have h₁ := e.hom.naturality χ
    have h₂ := e.hom.naturality u
    simp only [Functor.comp_map, Functor.id_map] at h₁ h₂
    rw [Category.assoc, Category.assoc, Iso.app_hom, ← h₁, ← Functor.map_comp_assoc, h, h₂,
      Iso.app_inv, ← NatTrans.comp_app_assoc, Iso.inv_hom_id, NatTrans.id_app, Category.id_comp]⟩

end CategoryTheory.Functor

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

/-- Transporting along an equality of morphisms of ringed spaces commutes with the derived
direct image of a morphism. -/
@[reassoc]
theorem derivedPushforward_map_comp_eqToHom {X Y : AlgebraicGeometry.RingedSpace.{u, u}}
    {F G : X ⟶ Y} (h : F = G)
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (φ : K ⟶ L) :
    (derivedPushforward F).map φ ≫ eqToHom (congrArg (fun F => (derivedPushforward F).obj L) h) =
      eqToHom (congrArg (fun F => (derivedPushforward F).obj K) h) ≫
        (derivedPushforward G).map φ := by
  subst h
  simp

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **`Scheme.Hom.formsDirectImageIso` is natural** in maps of differential forms. -/
theorem formsDirectImageIso_hom_naturality {p q : ℤ}
    (φ : relativeDifferentialForms f p ⟶ relativeDifferentialForms f q) :
    (derivedPushforward f.toLRSHom.toShHom).map (DerivedCategory.Q.map
        ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map φ)) ≫
        (f.formsDirectImageIso q).hom =
      (f.formsDirectImageIso p).hom ≫
        (derivedPushforward (inverseImageBaseProjection f)).map
          ((DerivedCategory.singleFunctor _ 0).map
            ((RingedSpaceModuleAdjunction.modulePushforward
              (Stacks.DeRhamDirectImage.toInverseImageBase f)).map φ)) := by
  simp only [formsDirectImageIso, Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom, Category.assoc]
  have key := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward_map_comp_eqToHom
    (Stacks.DeRhamDirectImage.toInverseImageBase_comp f).symm
    (DerivedCategory.Q.map ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map φ))
  refine ((reassoc_of% key) _).trans ?_
  refine (cancel_epi _).2 ?_
  have i1 := (DerivedCategory.singleFunctorIsoCompQ X.Modules 0).inv.naturality φ
  have i2 := (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardSingleIso
    (Stacks.DeRhamDirectImage.toInverseImageBase f)).inv.naturality φ
  have inner : (derivedPushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)).map
        (DerivedCategory.Q.map
          ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map φ)) ≫
        (derivedPushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)).map
          ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).inv.app _) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardSingleIso
          (Stacks.DeRhamDirectImage.toInverseImageBase f)).inv.app _ =
      ((derivedPushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)).map
          ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).inv.app _) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardSingleIso
          (Stacks.DeRhamDirectImage.toInverseImageBase f)).inv.app _) ≫
        (DerivedCategory.singleFunctor _ 0).map
          ((RingedSpaceModuleAdjunction.modulePushforward
            (Stacks.DeRhamDirectImage.toInverseImageBase f)).map φ) :=
    (Functor.map_comp_assoc _ _ _ _).symm.trans ((congrArg (fun k =>
      (derivedPushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)).map k ≫ _) i1).trans
      ((congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) i2).trans (Category.assoc _ _ _).symm))))
  refine ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
    (Stacks.DeRhamDirectImage.toInverseImageBase f)
      (inverseImageBaseProjection f)).inv.naturality_assoc
      _ _).trans (congrArg (_ ≫ ·) ?_)
  exact (Functor.map_comp _ _ _).symm.trans ((congrArg _ inner).trans (Functor.map_comp _ _ _))

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.RelativeDualitySituation

variable (D : RelativeDualitySituation.{u})

/-- Multiplication by a global function commutes with `topPieceIso`: each of the isomorphisms it
is assembled from is natural. -/
theorem formsShiftSMul_comp_topPieceIso_hom (g : Γ(D.X, ⊤)) :
    D.f.formsShiftSMul D.n g ≫ D.topPieceIso.hom =
      D.topPieceIso.hom ≫
        (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f)).map
        ((shiftFunctor (DerivedModules.{u + 1, u} (inverseImageBase D.f).sheaf) (2 * D.n : ℤ)).map
          (DerivedCategory.Q.map ((HomologicalComplex.single _ (ComplexShape.up ℤ) (D.n : ℤ)).map
            (D.formsSMul g D.n : D.topForms ⟶ D.topForms)))) := by
  let := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
    D.f.toLRSHom.toShHom
  let := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
    (inverseImageBaseProjection D.f)
  have hA := (derivedPushforward D.f.toLRSHom.toShHom).commShiftIso_hom_naturality
    (D.f.formsInDegreeZeroSMul g D.n) (D.n : ℤ)
  have hB := (Functor.map_comp _ _ _).symm.trans ((congrArg (shiftFunctor _ (D.n : ℤ)).map
    (D.f.formsDirectImageIso_hom_naturality (Stacks.Cohomology.InvertibleDerived.smulHom
      (X := D.X.toRingedSpace) g (Scheme.Hom.relativeDifferentialForms D.f (D.n : ℤ))))).trans
    (Functor.map_comp _ _ _))
  have hC := (derivedPushforward (inverseImageBaseProjection D.f)).commShiftIso_inv_naturality
    ((DerivedCategory.singleFunctor
      (SheafOfModules (structureSheafRing (inverseImageBase D.f))) 0).map
      (D.formsSMul g D.n)) (D.n : ℤ)
  have hE1 := ((DerivedCategory.singleFunctors
    (SheafOfModules (structureSheafRing (inverseImageBase D.f)))).shiftIso (D.n : ℤ) (-(D.n : ℤ)) 0
    (by omega)).hom.naturality (D.formsSMul g D.n)
  have hE2 := ((DerivedCategory.singleFunctors
    (SheafOfModules (structureSheafRing (inverseImageBase D.f)))).shiftIso (2 * D.n : ℤ)
    (-(D.n : ℤ)) (D.n : ℤ)
    (by omega)).inv.naturality (D.formsSMul g D.n)
  refine CategoryTheory.Iso.comp_trans_hom_of_comp_hom _ _ hA ?_
  refine CategoryTheory.Iso.comp_trans_hom_of_comp_hom _ _ hB ?_
  refine CategoryTheory.Iso.comp_trans_hom_of_comp_hom _ _ hC ?_
  refine (Functor.map_commSq _ (CommSq.mk ?_)).w
  refine CategoryTheory.Iso.comp_trans_hom_of_comp_hom _ _ hE1 ?_
  refine CategoryTheory.Iso.comp_trans_hom_of_comp_hom _ _ hE2 ?_
  refine (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id (shiftFunctor (DerivedCategory
    (SheafOfModules (structureSheafRing (inverseImageBase D.f)))) (2 * D.n : ℤ)) _)).trans
    ((Category.comp_id _).trans ?_)
  refine Eq.trans ?_ ((congrArg (· ≫ _) (CategoryTheory.Functor.map_id (shiftFunctor
    (DerivedCategory
    (SheafOfModules (structureSheafRing (inverseImageBase D.f)))) (2 * D.n : ℤ)) _)).trans
    (Category.id_comp _)).symm
  rfl

/-- Multiplication by a global function commutes with the inclusion `Ω^n[-n] ⟶ Ω^•` of
complexes. -/
theorem single_map_formsSMul_comp_topFormsToDeRham (g : Γ(D.X, ⊤)) :
    (HomologicalComplex.single _ (ComplexShape.up ℤ) (D.n : ℤ)).map
      (D.formsSMul g D.n : D.topForms ⟶ D.topForms) ≫ D.topFormsToDeRham =
      D.topFormsToDeRham ≫
        HomologicalComplex.extendMap (D.deRhamComplexSMul g) ComplexShape.embeddingUpNat := by
  refine HomologicalComplex.single_map_comp_mkHomFromSingle _ _ _ _ _ _ ?_
  exact (Iso.inv_hom_id_assoc _ _).symm.trans (congrArg (_ ≫ ·)
    (HomologicalComplex.extendMap_f (D.deRhamComplexSMul g) ComplexShape.embeddingUpNat
      (i := D.n) (i' := (D.n : ℤ)) rfl).symm)

/-- Multiplication by `g` commutes with the inclusion of the top piece. -/
theorem topInclusion_comp_smul (g : Γ(D.X, ⊤)) :
    D.topInclusion ≫ D.deRhamDirectImageTopSMul g = D.f.formsShiftSMul D.n g ≫ D.topInclusion := by
  let ψ : D.topForms ⟶ D.topForms := D.formsSMul g D.n
  let Q := DerivedCategory.Q
    (C := (Stacks.DerivedTensor.RingedSite.Modules (inverseImageBase D.f).sheaf))
  let S := shiftFunctor (DerivedModules.{u + 1, u} (inverseImageBase D.f).sheaf) (2 * D.n : ℤ)
  let R := derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f)
  let a := (HomologicalComplex.single (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf
    ((TopCat.Sheaf.pullback CommRingCat D.f.base).obj D.S.sheaf))) (ComplexShape.up ℤ)
      (D.n : ℤ)).map ψ
  let a' := (HomologicalComplex.single
    (Stacks.DerivedTensor.RingedSite.Modules (inverseImageBase D.f).sheaf) (ComplexShape.up ℤ)
      (D.n : ℤ)).map ψ
  let ι := D.topFormsToDeRham
  let e := HomologicalComplex.extendMap (D.deRhamComplexSMul g) ComplexShape.embeddingUpNat
  have hc : a ≫ ι = ι ≫ e := D.single_map_formsSMul_comp_topFormsToDeRham g
  have hR : R.map (S.map (Q.map a')) ≫ R.map (S.map (Q.map ι)) =
      R.map (S.map (Q.map ι)) ≫ R.map (S.map (Q.map e)) :=
    (Functor.map_commSq (Q ⋙ S ⋙ R) (CommSq.mk hc)).w
  have h1 : D.f.formsShiftSMul D.n g ≫ D.topPieceIso.hom =
      D.topPieceIso.hom ≫ R.map (S.map (Q.map a')) := D.formsShiftSMul_comp_topPieceIso_hom g
  have s1 : D.topInclusion ≫ D.deRhamDirectImageTopSMul g =
      D.topPieceIso.hom ≫ (R.map (S.map (Q.map ι)) ≫ R.map (S.map (Q.map e))) :=
    Category.assoc _ _ _
  have s2 : D.topPieceIso.hom ≫ (R.map (S.map (Q.map ι)) ≫ R.map (S.map (Q.map e))) =
      D.topPieceIso.hom ≫ (R.map (S.map (Q.map a')) ≫ R.map (S.map (Q.map ι))) :=
    congrArg (D.topPieceIso.hom ≫ ·) hR.symm
  have s3 : D.topPieceIso.hom ≫ (R.map (S.map (Q.map a')) ≫ R.map (S.map (Q.map ι))) =
      D.f.formsShiftSMul D.n g ≫ (D.topPieceIso.hom ≫ R.map (S.map (Q.map ι))) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ R.map (S.map (Q.map ι))) h1.symm).trans
      (Category.assoc _ _ _))
  exact s1.trans (s2.trans s3)

end AlgebraicGeometry.RelativeDualitySituation

namespace AlgebraicGeometry.SheafOfModules

open TopologicalSpace

open scoped Stacks.Topology.SheafTensorAdditiveOnOpens

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- **The wedge product of the de Rham complex is linear over the global functions in its first
factor**: if a map of complexes `Φ : Ω^• ⟶ Ω^•` is multiplication by `g` in every degree, then
`(Φ ω) ∧ η = Φ (ω ∧ η)`. -/
theorem wedgeProduct_comp_of_formsSMul (g : X.presheaf.obj (Opposite.op ⊤))
    (Φ : deRhamComplex B D ⟶ deRhamComplex B D) (hΦ : ∀ p, Φ.f p = formsSMul B g p) :
    wedgeProduct B D ≫ Φ =
      HomologicalComplex.mapBifunctorMap Φ (𝟙 (deRhamComplex B D))
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ) ≫
        wedgeProduct B D := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine (HomologicalComplex.comp_f _ _ n).trans
    (Eq.trans ?_ (HomologicalComplex.comp_f _ _ n).symm)
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q hpq => ?_
  obtain rfl : p + q = n := hpq
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc, wedgeProduct_f,
    ι_wedgeProductDesc_assoc, ι_wedgeProductDesc]
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, hΦ,
    HomologicalComplex.id_f, CategoryTheory.Functor.map_id]
  exact (exteriorProductComponent_formsSMul_left B g p q).symm

/-- `wedgeProduct_comp_of_formsSMul`, in the form of the hypothesis of
`AlgebraicGeometry.SheafOfModules.toTensor_multiplicationInt_naturality`. -/
theorem wedgeProduct_comp_eq_tensorBifunctorNat_of_formsSMul (g : X.presheaf.obj (Opposite.op ⊤))
    (Φ : deRhamComplex B D ⟶ deRhamComplex B D) (hΦ : ∀ p, Φ.f p = formsSMul B g p) :
    wedgeProduct B D ≫ Φ = ((tensorBifunctorNat (A := A)).obj (deRhamComplex B D)).map
      (𝟙 (deRhamComplex B D)) ≫ ((tensorBifunctorNat (A := A)).map Φ).app (deRhamComplex B D) ≫
        wedgeProduct B D :=
  (wedgeProduct_comp_of_formsSMul B D g Φ hΦ).trans
    ((Category.id_comp _).symm.trans (congrArg (· ≫ _)
      (CategoryTheory.Functor.map_id ((tensorBifunctorNat (A := A)).obj (deRhamComplex B D))
        (deRhamComplex B D)).symm))

/-- **The derived multiplication of the de Rham complex is linear over the global functions in its
first factor**, for a map of complexes that is multiplication by `g` in every degree. -/
theorem deRhamDerivedMul_comp_of_formsSMul (g : X.presheaf.obj (Opposite.op ⊤))
    (Φ : deRhamComplex B D ⟶ deRhamComplex B D) (hΦ : ∀ p, Φ.f p = formsSMul B g p) :
    deRhamDerivedMul B D ≫ DerivedCategory.Q.map
        (HomologicalComplex.extendMap Φ ComplexShape.embeddingUpNat) =
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (baseRingedSpace A).sheaf).map
          (DerivedCategory.Q.map (HomologicalComplex.extendMap Φ ComplexShape.embeddingUpNat))).app
          (moduleDerived (deRhamComplex B D)) ≫ deRhamDerivedMul B D := by
  have key := toTensor_multiplicationInt_naturality Φ (𝟙 (deRhamComplex B D)) (wedgeProduct B D)
    (wedgeProduct B D) Φ (wedgeProduct_comp_eq_tensorBifunctorNat_of_formsSMul B D g Φ hΦ)
  have e1 : DerivedCategory.Q.map (HomologicalComplex.extendMap (𝟙 (deRhamComplex B D))
      ComplexShape.embeddingUpNat) = 𝟙 (moduleDerived (deRhamComplex B D)) :=
    (congrArg DerivedCategory.Q.map (HomologicalComplex.extendMap_id _ _)).trans
      (CategoryTheory.Functor.map_id _ _)
  exact key.symm.trans (congrArg (· ≫ deRhamDerivedMul B D)
    ((congrArg (fun x => (Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      (baseRingedSpace A).sheaf)).map (Prod.mkHom (DerivedCategory.Q.map
        (HomologicalComplex.extendMap Φ ComplexShape.embeddingUpNat)) x)) e1).trans
      (Stacks.Cohomology.LerayCupPairing.uncurry_map_prod_id _ _ _)))

/-- **The unit `1 ∈ Ω^0` is closed**: the de Rham differential kills the unit `A ⟶ Ω^0` of the
wedge product. -/
theorem unitToForms_comp_d : unitToForms B D ≫ (deRhamComplex B D).d 0 1 = 0 := by
  refine (_root_.SheafOfModules.unitHomEquiv _).injective (Subtype.ext (funext fun U => ?_))
  change ((deRhamComplex B D).d 0 1).val.app U ((unitToForms B D).val.app U
    (1 : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj.obj U)) = 0
  rw [unitToForms_app, one_smul]
  have h := deRhamComplex_degreeZero B D U 1
  rw [one_smul] at h
  refine (eq_of_heq h).trans ?_
  have h1 :=
    (PresheafOfModulesOfCommRing.Derivation'.app (universalDerivation.{u, u, u} φ) U).d_map 1
  rw [map_one] at h1
  exact (congrArg (B.exteriorGenerator.val.app U) h1).trans (map_zero _)

/-- **The unit `A[0] ⟶ Ω^•`** of the de Rham complex extended by zero to `ℤ`-indexed complexes:
the unit `A ⟶ Ω^0` of the wedge product, a cocycle because the unit of `Ω^0` is closed. -/
def unitToDeRhamExtend :
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ⟶
      (deRhamComplex B D).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.mkHomFromSingle
    (unitToForms B D ≫ ((deRhamComplex B D).extendXIso ComplexShape.embeddingUpNat
      (i := 0) rfl).inv) (fun k hk => by
        obtain rfl : (0 : ℤ) + 1 = k := hk
        exact (congrArg (_ ≫ ·) (HomologicalComplex.extend_d_eq (deRhamComplex B D)
          ComplexShape.embeddingUpNat (i := 0) (j := 1) (i' := 0) (j' := 0 + 1) rfl rfl)).trans
          ((Category.assoc _ _ _).trans ((congrArg (unitToForms B D ≫ ·)
            (Iso.inv_hom_id_assoc _ _)).trans ((Category.assoc _ _ _).symm.trans
              ((congrArg (· ≫ _) (unitToForms_comp_d B D)).trans zero_comp)))))

/-- **The projection `Ω^• ⟶ Ω^0[0]`** of the de Rham complex extended by zero onto its degree-zero
term: a map of complexes because nothing lies in negative degrees. -/
def deRhamExtendToFormsZero :
    (deRhamComplex B D).extend ComplexShape.embeddingUpNat ⟶
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj ((deRhamComplex B D).X 0) :=
  HomologicalComplex.mkHomToSingle
    ((deRhamComplex B D).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom
    (fun i hi => ((deRhamComplex B D).isZero_extend_X ComplexShape.embeddingUpNat i
      (fun k hk => by
        have h1 : (k : ℤ) = i := hk
        have h2 : i + 1 = 0 := hi
        omega)).eq_of_src _ _)

/-- The unit followed by the projection onto degree zero is the unit `A ⟶ Ω^0` in degree zero. -/
theorem unitToDeRhamExtend_comp_deRhamExtendToFormsZero :
    unitToDeRhamExtend B D ≫ deRhamExtendToFormsZero B D =
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (unitToForms B D) := by
  refine HomologicalComplex.from_single_hom_ext ((congrArg₂ (· ≫ ·)
    (HomologicalComplex.mkHomFromSingle_f _ _) (HomologicalComplex.mkHomToSingle_f _ _)).trans
      (Eq.trans ?_ (HomologicalComplex.single_map_f_self _ _ _).symm))
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (unitToForms B D ≫ ·) (Iso.inv_hom_id_assoc _ _))))

/-- The projection onto degree zero commutes with every map of de Rham complexes. -/
theorem extendMap_comp_deRhamExtendToFormsZero (Φ : deRhamComplex B D ⟶ deRhamComplex B D) :
    HomologicalComplex.extendMap Φ ComplexShape.embeddingUpNat ≫ deRhamExtendToFormsZero B D =
      deRhamExtendToFormsZero B D ≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (Φ.f 0) :=
  HomologicalComplex.mkHomToSingle_comp_single_map _ _ _ _ _ _
    ((congrArg (· ≫ _) (HomologicalComplex.extendMap_f Φ ComplexShape.embeddingUpNat
      (i := 0) (i' := 0) rfl)).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
        ((Category.assoc _ _ _).trans ((congrArg (Φ.f 0 ≫ ·) (Iso.inv_hom_id _)).trans
          (Category.comp_id _))))))

/-- **A global function that divides the unit of `Ω^0` is a unit**: if the unit `A ⟶ Ω^0` factors
through multiplication by `g`, then `g` is invertible. -/
theorem isUnit_of_comp_formsSMul_eq_unitToForms (g : X.presheaf.obj (Opposite.op ⊤))
    (ψ : _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A) ⟶
      (deRhamComplex B D).X 0)
    (h : ψ ≫ formsSMul B g 0 = unitToForms B D) : IsUnit g := by
  have h' := congrArg (fun χ : _root_.SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A) ⟶ (deRhamComplex B D).X 0 =>
    χ.val.app (Opposite.op ⊤) (1 : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj.obj
      (Opposite.op ⊤))) h
  have h3 := (formsSMul_app B g 0 _ _).symm.trans (h'.trans (unitToForms_app B D _ _))
  have h2 := congrArg (B.exteriorPieceZeroIsoUnit.hom.val.app (Opposite.op ⊤)) h3
  have h4 := (map_smul (B.exteriorPieceZeroIsoUnit.hom.val.app (Opposite.op ⊤)).hom _ _).symm.trans
    (h2.trans ((congrArg _ (one_smul _ _)).trans (B.exteriorPieceZeroIsoUnit_one _)))
  have h5 : Stacks.Cohomology.InvertibleDerived.globalRes g ⊤ * _ = 1 := h4
  rw [Stacks.Cohomology.InvertibleDerived.globalRes_top] at h5
  exact IsUnit.of_mul_eq_one _ h5

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The shifted multiplication `Ω^• ⊗^L Ω^•[m] ⟶ Ω^•[m]` is linear in its first factor** for
every endomorphism of `Ω^•` along which the unshifted multiplication is linear in its first
factor. -/
theorem deRhamDerivedMulShift_comp_shift_map (m : ℤ)
    (Φ : Scheme.deRhamDerived f ⟶ Scheme.deRhamDerived f)
    (h : SheafOfModules.deRhamDerivedMul _ _ ≫ Φ =
      ((derivedTensorProductFunctor (Stacks.DeRhamDirectImage.inverseImageBase f).sheaf).map Φ).app
        (Scheme.deRhamDerived f) ≫ SheafOfModules.deRhamDerivedMul _ _) :
    f.deRhamDerivedMulShift m ≫ Φ⟦m⟧' =
      ((derivedTensorProductFunctor (Stacks.DeRhamDirectImage.inverseImageBase f).sheaf).map Φ).app
        ((Scheme.deRhamDerived f)⟦m⟧) ≫ f.deRhamDerivedMulShift m := by
  let := (canonicalDerivedTensorProduct (Stacks.DeRhamDirectImage.inverseImageBase f).sheaf
    ).commShift_right (Scheme.deRhamDerived f)
  have := (canonicalDerivedTensorProduct (Stacks.DeRhamDirectImage.inverseImageBase f).sheaf
    ).commShift₂.commShift_map Φ
  have hc := NatTrans.shift_app_comm
    ((derivedTensorProductFunctor (Stacks.DeRhamDirectImage.inverseImageBase f).sheaf).map Φ) m
    (Scheme.deRhamDerived f)
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Functor.map_comp _ _ _).symm.trans
    ((congrArg _ h).trans (Functor.map_comp _ _ _)))).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (SheafOfModules.deRhamDerivedMul (deRhamAlgebras f)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras f)))⟦m⟧') hc).trans
          (Category.assoc _ _ _))))

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.RelativeDualitySituation

variable (D : RelativeDualitySituation.{u})

/-- The derived multiplication of `Ω^•_{X/S}` is linear over `Γ(X, 𝒪_X)` in its first factor. -/
theorem deRhamDerivedMul_comp_deRhamDerivedSMul (g : Γ(D.X, ⊤)) :
    SheafOfModules.deRhamDerivedMul _ _ ≫ D.deRhamDerivedSMul g =
      ((derivedTensorProductFunctor (inverseImageBase D.f).sheaf).map (D.deRhamDerivedSMul g)).app
        (Scheme.deRhamDerived D.f) ≫ SheafOfModules.deRhamDerivedMul _ _ :=
  SheafOfModules.deRhamDerivedMul_comp_of_formsSMul (Scheme.Hom.deRhamAlgebras D.f)
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)) g (D.deRhamComplexSMul g)
    (fun _ => rfl)

/-- **Rescaling the trace rescales the pairing of [Stacks, Tag 0G8K]**: the pairing of `g · s` is
the pairing of `s` precomposed with multiplication by `g` on its first factor. -/
theorem deRhamPoincarePairing_smul_comp (g : Γ(D.X, ⊤))
    (s : D.deRhamDirectImageTop ⟶ (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj) :
    D.f.deRhamPoincarePairing (2 * D.n) (D.deRhamDirectImageTopSMul g ≫ s) =
      ((derivedTensorProductFunctor (Stacks.SheafOfModules.ringedSite D.S.sheaf).O).map
          ((derivedPushforward (inverseImageBaseProjection D.f)).map (D.deRhamDerivedSMul g))).app
          _ ≫ D.f.deRhamPoincarePairing (2 * D.n) s := by
  have hL := D.f.deRhamDerivedMulShift_comp_shift_map (2 * D.n) (D.deRhamDerivedSMul g)
    (D.deRhamDerivedMul_comp_deRhamDerivedSMul g)
  have hR := (Functor.map_commSq (derivedPushforward (inverseImageBaseProjection D.f))
    (CommSq.mk hL)).w
  have hc := Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_natural_left
    (inverseImageBaseProjection D.f) (D.deRhamDerivedSMul g)
    ((Scheme.deRhamDerived D.f)⟦(2 * D.n : ℤ)⟧)
  exact (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ s) hR).trans
    (Category.assoc _ _ _)))).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) hc.symm).trans (Category.assoc _ _ _)))

/-- Multiplication by `g` and then by `h` on `Ω^•_{X/S}` is multiplication by `h g`. -/
theorem deRhamComplexSMul_comp (g h : Γ(D.X, ⊤)) :
    D.deRhamComplexSMul g ≫ D.deRhamComplexSMul h = D.deRhamComplexSMul (h * g) :=
  HomologicalComplex.hom_ext _ _ fun _ => (Functor.map_comp _ _ _).symm.trans
    (congrArg (RingedSpaceModuleAdjunction.modulePushforward
      (Stacks.DeRhamDirectImage.toInverseImageBase D.f)).map
      (Stacks.Cohomology.InvertibleDerived.smulHom_comp (X := D.X.toRingedSpace) g h _))

/-- Multiplication by `1` on `Ω^•_{X/S}` is the identity. -/
theorem deRhamComplexSMul_one : D.deRhamComplexSMul 1 = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun _ => (congrArg (RingedSpaceModuleAdjunction.modulePushforward
      (Stacks.DeRhamDirectImage.toInverseImageBase D.f)).map
      (AlgebraicGeometry.SheafOfModules.smulHom_one _)).trans (CategoryTheory.Functor.map_id _ _)

/-- Multiplication by `g` and then by `h` on `Ω^•_{X/S}` in the derived category is multiplication
by `h g`. -/
theorem deRhamDerivedSMul_comp (g h : Γ(D.X, ⊤)) :
    D.deRhamDerivedSMul g ≫ D.deRhamDerivedSMul h = D.deRhamDerivedSMul (h * g) :=
  (DerivedCategory.Q.map_comp _ _).symm.trans (congrArg DerivedCategory.Q.map
    ((HomologicalComplex.extendMap_comp _ _ _).symm.trans
      (congrArg (HomologicalComplex.extendMap · ComplexShape.embeddingUpNat)
        (D.deRhamComplexSMul_comp g h))))

/-- Multiplication by `1` on `Ω^•_{X/S}` in the derived category is the identity. -/
theorem deRhamDerivedSMul_one : D.deRhamDerivedSMul 1 = 𝟙 _ :=
  (congrArg DerivedCategory.Q.map ((congrArg (HomologicalComplex.extendMap ·
    ComplexShape.embeddingUpNat) D.deRhamComplexSMul_one).trans
      (HomologicalComplex.extendMap_id _ _))).trans (CategoryTheory.Functor.map_id _ _)

/-- Multiplication by a unit on `Ω^•_{X/S}` in the derived category is an isomorphism. -/
theorem isIso_deRhamDerivedSMul (u : (Γ(D.X, ⊤))ˣ) : IsIso (D.deRhamDerivedSMul (u : Γ(D.X, ⊤))) :=
  ⟨D.deRhamDerivedSMul ((u⁻¹ : (Γ(D.X, ⊤))ˣ) : Γ(D.X, ⊤)),
    (D.deRhamDerivedSMul_comp _ _).trans ((congrArg D.deRhamDerivedSMul (Units.inv_mul u)).trans
      D.deRhamDerivedSMul_one),
    (D.deRhamDerivedSMul_comp _ _).trans ((congrArg D.deRhamDerivedSMul (Units.mul_inv u)).trans
      D.deRhamDerivedSMul_one)⟩

/-- The adjoint of the pairing of `g · s` is the adjoint of the pairing of `s` precomposed with
multiplication by `g` on `Rf_*Ω^•_{X/S}`. -/
private theorem homEquiv_symm_deRhamPoincarePairing_smul_comp (DY : DerivedTensorHomAdjunction D.S)
    (g : Γ(D.X, ⊤))
    (s : D.deRhamDirectImageTop ⟶ (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj) :
    (DY.homEquiv _ _ _).symm
      (D.f.deRhamPoincarePairing (2 * D.n) (D.deRhamDirectImageTopSMul g ≫ s)) =
      (derivedPushforward (inverseImageBaseProjection D.f)).map (D.deRhamDerivedSMul g) ≫
        (DY.homEquiv _ _ _).symm (D.f.deRhamPoincarePairing (2 * D.n) s) := by
  rw [D.deRhamPoincarePairing_smul_comp]
  exact TensorHomAdjunction.homEquiv_symm_map_app_comp DY _ _

/-- **Rescaling by a unit preserves perfectness of the pairing of [Stacks, Tag 0G8K]**, for any
tensor–internal-Hom adjunction `DY`. -/
theorem isPerfectDerivedPairing_deRhamPoincarePairing_smul_comp
    (DY : DerivedTensorHomAdjunction D.S)
    (u : (Γ(D.X, ⊤))ˣ)
    (s : D.deRhamDirectImageTop ⟶ (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj)
    (hs : IsPerfectDerivedPairing DY (D.f.deRhamPoincarePairing (2 * D.n) s)) :
    IsPerfectDerivedPairing DY
      (D.f.deRhamPoincarePairing (2 * D.n) (D.deRhamDirectImageTopSMul (u : Γ(D.X, ⊤)) ≫ s)) := by
  obtain ⟨h₁, h₂, h₃⟩ := hs
  refine ⟨h₁, h₂, ?_⟩
  rw [D.homEquiv_symm_deRhamPoincarePairing_smul_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    (@Functor.map_isIso _ _ _ _ _ _ (derivedPushforward (inverseImageBaseProjection D.f))
      (D.deRhamDerivedSMul (u : Γ(D.X, ⊤))) (D.isIso_deRhamDerivedSMul u)) h₃

/-- Rescaling a trace with the property of [Stacks, Tag 0G8K] by a unit gives such a trace. -/
theorem isDeRhamPoincareTrace_smul_comp (u : (Γ(D.X, ⊤))ˣ)
    (s : D.deRhamDirectImageTop ⟶ (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj)
    (hs : D.IsDeRhamPoincareTrace s) :
    D.IsDeRhamPoincareTrace (D.deRhamDirectImageTopSMul (u : Γ(D.X, ⊤)) ≫ s) :=
  D.isPerfectDerivedPairing_deRhamPoincarePairing_smul_comp _ u s hs

/-- **Two perfect pairings differing by `g` make multiplication by `g` invertible**: if the
pairings of `s` and of `g · s` are both perfect, then multiplication by `g` on `Rf_*Ω^•_{X/S}` is
an isomorphism, since it is the quotient of the two maps to `R𝓗om(Rf_*(Ω^•[2n]), 𝒪_S)`. -/
theorem isIso_map_deRhamDerivedSMul_of_isPerfectDerivedPairing (DY : DerivedTensorHomAdjunction D.S)
    (g : Γ(D.X, ⊤))
    (s : D.deRhamDirectImageTop ⟶ (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj)
    (hs : IsPerfectDerivedPairing DY (D.f.deRhamPoincarePairing (2 * D.n) s))
    (hgs : IsPerfectDerivedPairing DY
      (D.f.deRhamPoincarePairing (2 * D.n) (D.deRhamDirectImageTopSMul g ≫ s))) :
    IsIso ((derivedPushforward (inverseImageBaseProjection D.f)).map (D.deRhamDerivedSMul g)) := by
  have h := hgs.2.2
  rw [D.homEquiv_symm_deRhamPoincarePairing_smul_comp] at h
  exact @IsIso.of_isIso_comp_right _ _ _ _ _
    ((derivedPushforward (inverseImageBaseProjection D.f)).map (D.deRhamDerivedSMul g))
    ((DY.homEquiv _ _ _).symm (D.f.deRhamPoincarePairing (2 * D.n) s)) hs.2.2 h

/-- If both `t` and `g · t` have the property of [Stacks, Tag 0G8K], then `g` is a unit. -/
theorem isUnit_of_isDeRhamPoincareTrace_smul_comp (g : Γ(D.X, ⊤))
    (s : D.deRhamDirectImageTop ⟶ (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj)
    (hs : D.IsDeRhamPoincareTrace s)
    (hgs : D.IsDeRhamPoincareTrace (D.deRhamDirectImageTopSMul g ≫ s)) :
    IsUnit g := by
  obtain ⟨z, hz⟩ := (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
    (inverseImageBaseProjection D.f)).exists_comp_eq_of_isIso_map (D.deRhamDerivedSMul g)
    (D.isIso_map_deRhamDerivedSMul_of_isPerfectDerivedPairing _ g s hs hgs)
    ((Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso
      (inverseImageBaseProjection D.f)).hom ≫ DerivedCategory.Q.map
        (SheafOfModules.unitToDeRhamExtend (Scheme.Hom.deRhamAlgebras D.f)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))))
  let eU := Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso
    (inverseImageBaseProjection D.f)
  let π := SheafOfModules.deRhamExtendToFormsZero (Scheme.Hom.deRhamAlgebras D.f)
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))
  have hw : (eU.inv ≫ z ≫ DerivedCategory.Q.map π) ≫ (DerivedCategory.singleFunctor
      (Stacks.DerivedTensor.RingedSite.Modules (inverseImageBase D.f).sheaf) 0).map
        (D.formsSMul g 0) = (DerivedCategory.singleFunctor
      (Stacks.DerivedTensor.RingedSite.Modules (inverseImageBase D.f).sheaf) 0).map
        (SheafOfModules.unitToForms (Scheme.Hom.deRhamAlgebras D.f)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))) := by
    have hQ1 := (DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map
      (SheafOfModules.extendMap_comp_deRhamExtendToFormsZero (Scheme.Hom.deRhamAlgebras D.f)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))
          (D.deRhamComplexSMul g))).trans (DerivedCategory.Q.map_comp _ _))
    have hQ2 := (DerivedCategory.Q.map_comp _ _).symm.trans (congrArg DerivedCategory.Q.map
      (SheafOfModules.unitToDeRhamExtend_comp_deRhamExtendToFormsZero
        (Scheme.Hom.deRhamAlgebras D.f)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))))
    refine (Category.assoc _ _ _).trans ((congrArg (eU.inv ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (z ≫ ·) hQ1.symm))).trans ?_)
    refine (congrArg (eU.inv ≫ ·) ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ DerivedCategory.Q.map π) hz))).trans ?_
    exact (congrArg (eU.inv ≫ ·) (Category.assoc _ _ _)).trans
      ((Iso.inv_hom_id_assoc _ _).trans hQ2)
  obtain ⟨ψ, hψ⟩ := Functor.exists_comp_eq_of_comp_map_eq
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0) _ _ _ hw
  exact SheafOfModules.isUnit_of_comp_formsSMul_eq_unitToForms _ _ g ψ hψ

end AlgebraicGeometry.RelativeDualitySituation

