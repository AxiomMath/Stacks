module

public import StacksFrontier.AlgebraicGeometry.Quot.PullSheafHomComparisonNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedDualSystems
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSheafHomContravariantCommShift
public import StacksFrontier.Algebra.Homology.DerivedCategory.HomBijectiveOfHomologyIso

/-!
# Morphisms on an algebraic space as sections of the derived internal Hom, naturally

Let `X` be an algebraic space.  By Stacks 08JA, `Hom(K, G) ≃ Hom(𝒪_X, R𝓗om(K, G))`
(`AlgebraicGeometry.Space.homEquivStructureHomSheafHom`).  This file proves that this
identification is natural in `K`, which rests on the dinaturality of Stacks 08J8
(`AlgebraicGeometry.Space.smallEtaleDerivedTensorSheafHomAdjunction_dinaturality`) and the
naturality of the left unit constraint `𝒪_X ⊗^L K ≅ K`, and builds the commutation
`R𝓗om(K[1], G) ≅ R𝓗om(K, G)[-1]` of the derived internal Hom with the shift in its
contravariant variable, natural in `K`, from that of the equi-universe model
(`AlgebraicGeometry.RingedSite.derivedSheafHomSourceShiftIso`).

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedLeftUnitIso_naturality`: the left unit constraint
  is natural.
* `AlgebraicGeometry.Space.homEquivStructureHomSheafHom_comp`: Stacks 08JA is natural in the
  source.
* `AlgebraicGeometry.Space.smallEtaleDerivedSheafHomSourceShiftIso` and its naturality
  `AlgebraicGeometry.Space.smallEtaleDerivedSheafHomSourceShiftIso_naturality`.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

namespace Functor

/-- **The transported left unit constraint is natural.**  If `T(-, P) ≅ E ⋙ TM(-, E P) ⋙ E⁻¹`
is natural in `P` and `λ : TM(OM, -) ≅ 𝟭` is natural, then the left unit constraint
`T(O, P) ≅ P` built from them and `σ : E O ≅ OM` is natural in `P`. -/
theorem leftUnitIsoConj_naturality {C M : Type*} [Category* C] [Category* M] (e : C ≌ M)
    (T : C ⥤ C ⥤ C) (TM : M ⥤ M ⥤ M)
    (ρ : ∀ P : C, T.flip.obj P ≅ e.functor ⋙ TM.flip.obj (e.functor.obj P) ⋙ e.inverse)
    (hρ : ∀ {P' P : C} (v : P' ⟶ P) (X : C), (T.obj X).map v ≫ (ρ P).hom.app X =
      (ρ P').hom.app X ≫ e.inverse.map ((TM.obj (e.functor.obj X)).map (e.functor.map v)))
    (O : C) (OM : M) (σ : e.functor.obj O ≅ OM) (lam : ∀ m : M, (TM.obj OM).obj m ≅ m)
    (hlam : ∀ {m m' : M} (g : m ⟶ m'), (TM.obj OM).map g ≫ (lam m').hom = (lam m).hom ≫ g)
    (lC : ∀ P : C, (T.obj O).obj P ≅ P)
    (hlC : ∀ P : C, lC P = (ρ P).app O ≪≫
      e.inverse.mapIso ((TM.flip.obj (e.functor.obj P)).mapIso σ ≪≫ lam (e.functor.obj P)) ≪≫
        (e.unitIso.app P).symm)
    {P' P : C} (u : P' ⟶ P) : (T.obj O).map u ≫ (lC P).hom = (lC P').hom ≫ u := by
  rw [hlC, hlC]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
    Functor.flip_obj_map, Category.assoc]
  rw [reassoc_of% (hρ u O)]
  congr 1
  have h1 : (TM.obj (e.functor.obj O)).map (e.functor.map u) ≫
      (TM.map σ.hom).app (e.functor.obj P) ≫ (lam (e.functor.obj P)).hom =
      ((TM.map σ.hom).app (e.functor.obj P') ≫ (lam (e.functor.obj P')).hom) ≫
        e.functor.map u := by
    rw [NatTrans.naturality_assoc, hlam, Category.assoc]
  rw [← e.inverse.map_comp_assoc, h1, e.inverse.map_comp, Category.assoc]
  congr 1
  exact e.unitIso.inv.naturality u

/-- The commutation `RM(E(A[1]), E Z) ≅ RM(E A, E Z)[-1]` read through an equivalence `E`
commuting with the shifts, from a commutation `sM` of `RM` with the shift in its contravariant
variable. -/
def sourceShiftIsoConj {C M : Type*} [Category* C] [Category* M] [HasShift C ℤ] [HasShift M ℤ]
    (e : C ≌ M) [e.functor.CommShift ℤ] [e.inverse.CommShift ℤ] (RM : Mᵒᵖ ⥤ M ⥤ M)
    (sM : ∀ a z : M, (RM.obj (op (a⟦(1 : ℤ)⟧))).obj z ≅ ((RM.obj (op a)).obj z)⟦(-1 : ℤ)⟧)
    (A Z : C) :
    e.inverse.obj ((RM.obj (op (e.functor.obj (A⟦(1 : ℤ)⟧)))).obj (e.functor.obj Z)) ≅
      (e.inverse.obj ((RM.obj (op (e.functor.obj A))).obj (e.functor.obj Z)))⟦(-1 : ℤ)⟧ :=
  e.inverse.mapIso ((RM.mapIso ((e.functor.commShiftIso (1 : ℤ)).app A).symm.op).app
      (e.functor.obj Z) ≪≫ sM (e.functor.obj A) (e.functor.obj Z)) ≪≫
    (e.inverse.commShiftIso (-1 : ℤ)).app _

/-- `CategoryTheory.Functor.sourceShiftIsoConj` is natural in the contravariant variable. -/
theorem sourceShiftIsoConj_naturality {C M : Type*} [Category* C] [Category* M] [HasShift C ℤ]
    [HasShift M ℤ] (e : C ≌ M) [e.functor.CommShift ℤ] [e.inverse.CommShift ℤ]
    (RM : Mᵒᵖ ⥤ M ⥤ M)
    (sM : ∀ a z : M, (RM.obj (op (a⟦(1 : ℤ)⟧))).obj z ≅ ((RM.obj (op a)).obj z)⟦(-1 : ℤ)⟧)
    (hsM : ∀ {a a' : M} (φ : a ⟶ a') (z : M), (RM.map (φ⟦(1 : ℤ)⟧').op).app z ≫ (sM a z).hom =
      (sM a' z).hom ≫ ((RM.map φ.op).app z)⟦(-1 : ℤ)⟧')
    {A A' : C} (u : A ⟶ A') (Z : C) :
    e.inverse.map ((RM.map (e.functor.map (u⟦(1 : ℤ)⟧')).op).app (e.functor.obj Z)) ≫
        (sourceShiftIsoConj e RM sM A Z).hom =
      (sourceShiftIsoConj e RM sM A' Z).hom ≫
        (e.inverse.map ((RM.map (e.functor.map u).op).app (e.functor.obj Z)))⟦(-1 : ℤ)⟧' := by
  have hc : (e.functor.commShiftIso (1 : ℤ)).inv.app A ≫ e.functor.map (u⟦(1 : ℤ)⟧') =
      (e.functor.map u)⟦(1 : ℤ)⟧' ≫ (e.functor.commShiftIso (1 : ℤ)).inv.app A' :=
    ((e.functor.commShiftIso (1 : ℤ)).inv.naturality u).symm
  have h2 : (RM.map (e.functor.map (u⟦(1 : ℤ)⟧')).op).app (e.functor.obj Z) ≫
      (RM.map ((e.functor.commShiftIso (1 : ℤ)).inv.app A).op).app (e.functor.obj Z) =
      (RM.map ((e.functor.commShiftIso (1 : ℤ)).inv.app A').op).app (e.functor.obj Z) ≫
        (RM.map ((e.functor.map u)⟦(1 : ℤ)⟧').op).app (e.functor.obj Z) := by
    rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp, hc, op_comp, Functor.map_comp,
      NatTrans.comp_app]
  have hin : (RM.map (e.functor.map (u⟦(1 : ℤ)⟧')).op).app (e.functor.obj Z) ≫
      (RM.map ((e.functor.commShiftIso (1 : ℤ)).inv.app A).op).app (e.functor.obj Z) ≫
        (sM (e.functor.obj A) (e.functor.obj Z)).hom =
      (RM.map ((e.functor.commShiftIso (1 : ℤ)).inv.app A').op).app (e.functor.obj Z) ≫
        (sM (e.functor.obj A') (e.functor.obj Z)).hom ≫
          ((RM.map (e.functor.map u).op).app (e.functor.obj Z))⟦(-1 : ℤ)⟧' := by
    rw [reassoc_of% h2, hsM]
  have hcs := (e.inverse.commShiftIso (-1 : ℤ)).hom.naturality
    ((RM.map (e.functor.map u).op).app (e.functor.obj Z))
  simp only [Functor.comp_map] at hcs
  simp only [sourceShiftIsoConj, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.op_hom,
    Iso.symm_hom, Iso.app_inv, Category.assoc]
  rw [← e.inverse.map_comp_assoc, hin, e.inverse.map_comp, e.inverse.map_comp, Category.assoc,
    Category.assoc, hcs]
  simp only [Functor.map_comp, Category.assoc]

end Functor

namespace Adjunction

/-- **Morphisms as sections of the internal Hom, naturally in the source.**  For dinatural
tensor–Hom adjunctions and a natural left unit constraint `λ : T(O, -) ≅ 𝟭`, the bijection
`Hom(K, Z) ≃ Hom(O, R(K, Z))`, `x ↦ (λ ≫ x)♭`, carries precomposition with `u : K' ⟶ K` to
postcomposition with `R(u, Z)`. -/
theorem homEquiv_comp_naturality_of_dinat {C : Type*} [Category* C] (T : C ⥤ C ⥤ C)
    (R : Cᵒᵖ ⥤ C ⥤ C) (adj : ∀ P : C, T.flip.obj P ⊣ R.obj (Opposite.op P))
    (hd : ∀ {P' P : C} (v : P' ⟶ P) (A Z : C) (h : A ⟶ (R.obj (Opposite.op P)).obj Z),
      ((adj P').homEquiv A Z).symm (h ≫ (R.map v.op).app Z) =
        (T.obj A).map v ≫ ((adj P).homEquiv A Z).symm h)
    (O : C) (lC : ∀ P : C, (T.obj O).obj P ≅ P)
    (hlC : ∀ {P' P : C} (u : P' ⟶ P), (T.obj O).map u ≫ (lC P).hom = (lC P').hom ≫ u)
    {K' K Z : C} (u : K' ⟶ K) (x : K ⟶ Z) :
    (((lC K').homCongr (Iso.refl Z)).symm.trans ((adj K').homEquiv O Z)) (u ≫ x) =
      (((lC K).homCongr (Iso.refl Z)).symm.trans ((adj K).homEquiv O Z)) x ≫
        (R.map u.op).app Z := by
  simp only [Equiv.trans_apply, Iso.homCongr_symm, Iso.homCongr_apply, Iso.symm_inv,
    Iso.refl_symm, Iso.refl_hom, Category.comp_id]
  apply ((adj K').homEquiv O Z).symm.injective
  rw [Equiv.symm_apply_apply, hd, Equiv.symm_apply_apply, reassoc_of% (hlC u)]

end Adjunction

namespace Pretriangulated

/-- **Composition with a map which a cohomological reading turns into an isomorphism in low
degrees.**  Let `S_A : Hom(A, E) ≃ Hom(O, R(H A))` be natural in `A` (`H` contravariant, `R`
commuting with the shift, `O ∈ D^{≤ 0}`), and let `H(A[1]) ≅ (H A)[-1]` naturally.  If
`R(H u)` is an isomorphism on cohomology in degrees `≤ m`, `m ≥ 1`, for `u : A ⟶ A'`, then
composing with `u` is bijective on `Hom(A', E)`, and composing with `u[1]` is bijective on
`Hom(A'[1], E)`. -/
theorem bijective_comp_of_isIso_homology_sections {C : Type*} [Category* C] [HasShift C ℤ]
    {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]
    (R : C ⥤ DerivedCategory 𝒜) [hR : R.CommShift ℤ] (H : Cᵒᵖ ⥤ C) (E : C)
    (O : DerivedCategory 𝒜) [O.IsLE 0] (S : ∀ A : C, (A ⟶ E) ≃ (O ⟶ R.obj (H.obj (op A))))
    (hS : ∀ {A A' : C} (u : A ⟶ A') (x : A' ⟶ E), S A (u ≫ x) = S A' x ≫ R.map (H.map u.op))
    (ι : ∀ A : C, H.obj (op (A⟦(1 : ℤ)⟧)) ≅ (H.obj (op A))⟦(-1 : ℤ)⟧)
    (hι : ∀ {A A' : C} (u : A ⟶ A'),
      H.map (u⟦(1 : ℤ)⟧').op ≫ (ι A).hom = (ι A').hom ≫ (H.map u.op)⟦(-1 : ℤ)⟧')
    {A A' : C} (u : A ⟶ A') (m : ℤ) (hm : 1 ≤ m)
    (hu : ∀ i : ℤ, i ≤ m →
      IsIso ((_root_.DerivedCategory.homologyFunctor 𝒜 i).map (R.map (H.map u.op)))) :
    Function.Bijective (fun x : A' ⟶ E => u ≫ x) ∧
      Function.Bijective (fun x : A'⟦(1 : ℤ)⟧ ⟶ E => u⟦(1 : ℤ)⟧' ≫ x) := by
  let S' : ∀ A : C, (A⟦(1 : ℤ)⟧ ⟶ E) ≃ (O ⟶ (R.obj (H.obj (op A)))⟦(-1 : ℤ)⟧) := fun A =>
    Equiv.trans (S (A⟦(1 : ℤ)⟧))
      ((Iso.refl O).homCongr (R.mapIso (ι A) ≪≫ (R.commShiftIso (-1 : ℤ)).app _))
  have hdef : ∀ (A : C) (y : A⟦(1 : ℤ)⟧ ⟶ E), S' A y = (Iso.refl O).inv ≫ S (A⟦(1 : ℤ)⟧) y ≫
      (R.map (ι A).hom ≫ (R.commShiftIso (-1 : ℤ)).hom.app (H.obj (op A))) := fun _ _ => rfl
  have hn := (R.commShiftIso (-1 : ℤ)).hom.naturality (H.map u.op)
  simp only [Functor.comp_map] at hn
  have hS' : ∀ x : A'⟦(1 : ℤ)⟧ ⟶ E,
      S' A (u⟦(1 : ℤ)⟧' ≫ x) = S' A' x ≫ (R.map (H.map u.op))⟦(-1 : ℤ)⟧' := by
    intro x
    rw [hdef, hdef, hS]
    simp only [Iso.refl_inv, Category.id_comp, Category.assoc]
    rw [← R.map_comp_assoc, hι, R.map_comp_assoc, hn]
  refine ⟨((S A).comp_bijective _).mp ?_, ((S' A).comp_bijective _).mp ?_⟩
  · convert (_root_.DerivedCategory.bijective_comp_of_isIso_homologyMap_le _ m hu O 0
      (by omega)).comp (S A').bijective using 1
    exact funext (hS u)
  · convert (_root_.DerivedCategory.bijective_comp_shift_of_isIso_homologyMap_le _ m hu O 0
      (by omega)).comp (S' A').bijective using 1
    exact funext hS'

end Pretriangulated

end CategoryTheory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Model

/- Forced, as in `StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedExtLeray`, where the
left unit constraint is defined: the model's derived tensor product, its monoidal structure and
its internal Hom are those of the standard derived category. -/
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel

/-- **The left unit constraint `𝒪_X ⊗^L P ≅ P` of an algebraic space is natural in `P`.** -/
theorem smallEtaleDerivedLeftUnitIso_naturality (X : AlgebraicSpaces B S hS)
    {P' P : derivedModules B S hS X} (u : P' ⟶ P) :
    ((smallEtaleDerivedTensor B S hS X).obj (structureObject B S hS X)).map u ≫
        (smallEtaleDerivedLeftUnitIso B S hS P).hom =
      (smallEtaleDerivedLeftUnitIso B S hS P').hom ≫ u :=
  let := RingedSite.derivedTensorMonoidal (smallEtaleModelRingedSite B S hS X.1 X.2)
  Functor.leftUnitIsoConj_naturality (smallEtaleModelDerivedEquivalence B S hS X)
    (smallEtaleDerivedTensor B S hS X)
    (Stacks.SheafOfModules.derivedTensorProductFunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
    (smallEtaleDerivedTensorRightIso B S hS X)
    (fun v X' => Functor.flipObjIsoOfUncurryIsoConj_naturality
      (smallEtaleModelDerivedEquivalence B S hS X) (smallEtaleModelDerivedTensorIso B S hS X) v X')
    (structureObject B S hS X)
    (RingedSite.derivedStructureSheaf (smallEtaleModelRingedSite B S hS X.1 X.2))
    (smallEtaleModelDerivedStructureSheafIso B S hS X)
    (fun m => MonoidalCategory.leftUnitor m)
    (fun g => MonoidalCategory.leftUnitor_naturality g)
    (fun P => smallEtaleDerivedLeftUnitIso B S hS P) (fun _ => rfl) u

/-- **The derived internal Hom of an algebraic space commutes with the shift in its
contravariant variable**: `R𝓗om(A[1], Z) ≅ R𝓗om(A, Z)[-1]`, that of the equi-universe model
(`AlgebraicGeometry.RingedSite.derivedSheafHomSourceShiftIso`) read through the derived
equivalence with the model. -/
def smallEtaleDerivedSheafHomSourceShiftIso (X : AlgebraicSpaces B S hS)
    (A Z : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    ((smallEtaleDerivedSheafHom B S hS X).obj (op (A⟦(1 : ℤ)⟧))).obj Z ≅
      (((smallEtaleDerivedSheafHom B S hS X).obj (op A)).obj Z)⟦(-1 : ℤ)⟧ :=
  Functor.sourceShiftIsoConj (smallEtaleModelDerivedEquivalence B S hS X)
    (RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
    (fun a z => RingedSite.derivedSheafHomSourceShiftIso
      (smallEtaleModelRingedSite B S hS X.1 X.2) a z 1) A Z

/-- `AlgebraicGeometry.Space.smallEtaleDerivedSheafHomSourceShiftIso` is natural in the
contravariant variable. -/
theorem smallEtaleDerivedSheafHomSourceShiftIso_naturality (X : AlgebraicSpaces B S hS)
    {A A' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (u : A ⟶ A')
    (Z : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    ((smallEtaleDerivedSheafHom B S hS X).map (u⟦(1 : ℤ)⟧').op).app Z ≫
        (smallEtaleDerivedSheafHomSourceShiftIso X A Z).hom =
      (smallEtaleDerivedSheafHomSourceShiftIso X A' Z).hom ≫
        (((smallEtaleDerivedSheafHom B S hS X).map u.op).app Z)⟦(-1 : ℤ)⟧' :=
  Functor.sourceShiftIsoConj_naturality (smallEtaleModelDerivedEquivalence B S hS X)
    (RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
    (fun a z => RingedSite.derivedSheafHomSourceShiftIso
      (smallEtaleModelRingedSite B S hS X.1 X.2) a z 1)
    (fun φ z => RingedSite.derivedSheafHomSourceShiftIso_hom_naturality_left
      (smallEtaleModelRingedSite B S hS X.1 X.2) z φ 1) u Z

/-- The commutation of `Rf_*` with the shift, named so that it can be supplied where instance
search runs with another model of `D(𝒪_X)`. -/
abbrev spaceDerivedPushforwardCommShift {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (spaceDerivedPushforward B S hS f).CommShift ℤ :=
  inferInstance

end Model

end AlgebraicGeometry.Space

end
