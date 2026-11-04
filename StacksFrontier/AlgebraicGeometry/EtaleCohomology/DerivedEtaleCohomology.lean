module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMate

/-!
# Étale cohomology of an object of the derived category, and restriction

For a scheme `Y` and `M` in the unbounded derived category `D(Y_étale)` of abelian sheaves on the
small étale site, the `p`-th étale cohomology group is `H^p(Y, M) = Hom(ℤ_Y[-p], M)`, the
morphisms in `D(Y_étale)` out of the constant sheaf `ℤ_Y` placed in degree `p`; equivalently
`Hom(ℤ_Y[0], M[p])` (`Stacks.EtaleCohomology.etaleDerivedCohomologyEquivShiftedHom`), which for a
sheaf `F` placed in degree `0` is `Ext^p(ℤ_Y, F)`, Mathlib's `Sheaf.H F p`. A morphism
`f : Y ⟶ X` induces the restriction map `H^p(X, K) ⟶ H^p(Y, f⁻¹ K)`, by applying the exact
functor `f⁻¹` and identifying `f⁻¹ ℤ_X[-p]` with `ℤ_Y[-p]`.

## Main definitions

* `Stacks.EtaleCohomology.etaleConstantIntegers`: the constant sheaf `ℤ_Y` placed in degree `p`.
* `Stacks.EtaleCohomology.etaleDerivedCohomology`: `H^p(Y, M)`.
* `Stacks.EtaleCohomology.etaleDerivedCohomologyRestriction`: the restriction map along `f`.
* `Stacks.EtaleCohomology.etaleDerivedCohomologyDirectImageEquiv`: `H^p(X, Rf_* N) ≅ H^p(Y, N)`,
  for the description of `H^p` as morphisms out of `ℤ[-p]`.
* `Stacks.EtaleCohomology.etaleDerivedCohomologyEquivShiftedHom`: `H^p(Y, M) ≅ Hom(ℤ_Y[0], M[p])`.

## Main results

* `Stacks.EtaleCohomology.etaleConstantIntegersIso_comp`: the identifications
  `f⁻¹ ℤ_X[-p] ≅ ℤ_Y[-p]` are compatible with composition.
* `Stacks.EtaleCohomology.etaleDerivedCohomologyDirectImageEquiv_comp_unit`: under
  `H^p(X, Rf_* f⁻¹ K) ≅ H^p(Y, f⁻¹ K)`, the map induced by the unit `K ⟶ Rf_* f⁻¹ K` is the
  restriction map.

## Implementation notes

`ℤ_Y[-p]` is realized as the inverse image of `ℤ[-p]` along the structure morphism
`Y ⟶ Spec ℤ` to the final scheme; the identification of `f⁻¹ ℤ_X[-p]` with `ℤ_Y[-p]` is then the
comparison `(Y ⟶ Spec ℤ)⁻¹ ≅ f⁻¹ ∘ (X ⟶ Spec ℤ)⁻¹` of derived inverse images, and its
compatibility with composition is the associativity of these comparisons
(`Stacks.EtaleCohomology.etaleAbelianDerivedInverseImageCompIso'_assoc`). The inverse image of
the constant sheaf along `Y ⟶ Spec ℤ` is the constant sheaf
(`Stacks.EtaleCohomology.etaleAbelianInverseImageConstantIso`), which is how
`Stacks.EtaleCohomology.etaleDerivedCohomologyEquivShiftedHom` is built.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

section Definitions

/-- The structure morphism from a scheme to the final scheme `Spec ℤ`. -/
public def toSpecULiftZ (Y : Scheme.{u}) : Y ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
  specULiftZIsTerminal.from Y

/-- Structure morphisms to `Spec ℤ` are compatible with every morphism of schemes. -/
public theorem toSpecULiftZ_eq_comp {X Y : Scheme.{u}} (f : Y ⟶ X) :
    toSpecULiftZ Y = f ≫ toSpecULiftZ X :=
  specULiftZIsTerminal.hom_ext _ _

/-- **The constant sheaf `ℤ_Y` placed in degree `p`**, `ℤ_Y[-p]`, as an object of `D(Y_étale)`:
the inverse image along `Y ⟶ Spec ℤ` of the constant sheaf `ℤ` on `Spec ℤ` placed in degree
`p`. -/
public def etaleConstantIntegers (Y : Scheme.{u}) (p : ℤ) :
    DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  (etaleAbelianDerivedInverseImage.{u, v} (toSpecULiftZ Y)).obj
    ((DerivedCategory.singleFunctor _ p).obj
      ((constantSheaf (Spec (CommRingCat.of (ULift.{u} ℤ))).smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v}).obj (AddCommGrpCat.of (ULift ℤ))))

/-- **The `p`-th étale cohomology group of an object of the derived category**,
`H^p(Y, M) = Hom(ℤ_Y[-p], M)` for `M` in `D(Y_étale)`. -/
public abbrev etaleDerivedCohomology (Y : Scheme.{u}) (p : ℤ)
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :=
  etaleConstantIntegers.{u, v} Y p ⟶ M

variable {X Y : Scheme.{u}}

/-- The identification `ℤ_Y[-p] ≅ f⁻¹ ℤ_X[-p]` for `f : Y ⟶ X`: the comparison of the derived
inverse image along `Y ⟶ Spec ℤ` with the composite of those along `f` and `X ⟶ Spec ℤ`. -/
public def etaleConstantIntegersIso (f : Y ⟶ X) (p : ℤ) :
    etaleConstantIntegers.{u, v} Y p ≅
      (etaleAbelianDerivedInverseImage.{u, v} f).obj (etaleConstantIntegers.{u, v} X p) :=
  (etaleAbelianDerivedInverseImageCompIso'.{u, v} f (toSpecULiftZ X) (toSpecULiftZ Y)
    (toSpecULiftZ_eq_comp f)).app _

/-- **The restriction map** `H^p(X, K) ⟶ H^p(Y, f⁻¹ K)` along `f : Y ⟶ X`: apply `f⁻¹` and
identify `f⁻¹ ℤ_X[-p]` with `ℤ_Y[-p]`. -/
public def etaleDerivedCohomologyRestriction (f : Y ⟶ X) (p : ℤ)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    etaleDerivedCohomology.{u, v} X p K →+
      etaleDerivedCohomology.{u, v} Y p ((etaleAbelianDerivedInverseImage.{u, v} f).obj K) :=
  (Preadditive.leftComp _ (etaleConstantIntegersIso.{u, v} f p).hom).comp
    (etaleAbelianDerivedInverseImage.{u, v} f).mapAddHom

/-- The restriction map, written out. -/
public theorem etaleDerivedCohomologyRestriction_apply (f : Y ⟶ X) (p : ℤ)
    {K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (x : etaleDerivedCohomology.{u, v} X p K) :
    etaleDerivedCohomologyRestriction.{u, v} f p K x =
      (etaleConstantIntegersIso.{u, v} f p).hom ≫
        (etaleAbelianDerivedInverseImage.{u, v} f).map x :=
  rfl

end Definitions

section Composition

variable {E Z X : Scheme.{u}} (π : E ⟶ Z) (i : Z ⟶ X) (c : E ⟶ X) (hc : c = π ≫ i)

/-- **The identifications `f⁻¹ ℤ_X[-p] ≅ ℤ_Y[-p]` are compatible with composition.** For
`c = π ≫ i`, identifying `ℤ_E[-p]` with `c⁻¹ ℤ_X[-p] ≅ π⁻¹ i⁻¹ ℤ_X[-p]` agrees with identifying it
with `π⁻¹ ℤ_Z[-p]` and then with `π⁻¹ i⁻¹ ℤ_X[-p]`: this is the associativity of the comparisons
of derived inverse images for `E ⟶ Z ⟶ X ⟶ Spec ℤ`. -/
public theorem etaleConstantIntegersIso_comp (p : ℤ) :
    (etaleConstantIntegersIso.{u, v} c p).hom ≫
        (etaleAbelianDerivedInverseImageCompIso'.{u, v} π i c hc).hom.app
          (etaleConstantIntegers.{u, v} X p) =
      (etaleConstantIntegersIso.{u, v} π p).hom ≫
        (etaleAbelianDerivedInverseImage.{u, v} π).map
          (etaleConstantIntegersIso.{u, v} i p).hom := by
  have h := congrArg (fun e ↦ e.hom.app ((DerivedCategory.singleFunctor _ p).obj
      ((constantSheaf (Spec (CommRingCat.of (ULift.{u} ℤ))).smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v}).obj (AddCommGrpCat.of (ULift ℤ)))))
    (etaleAbelianDerivedInverseImageCompIso'_assoc.{u, v} (toSpecULiftZ X) i π (toSpecULiftZ Z)
      (toSpecULiftZ_eq_comp i) c hc (toSpecULiftZ E) (toSpecULiftZ_eq_comp c)
      (toSpecULiftZ_eq_comp π))
  dsimp at h
  simp only [Category.id_comp] at h
  have e : ((etaleConstantIntegersIso.{u, v} c p) ≪≫
      (etaleAbelianDerivedInverseImageCompIso'.{u, v} π i c hc).app
        (etaleConstantIntegers.{u, v} X p)).symm =
      ((etaleConstantIntegersIso.{u, v} π p) ≪≫
        (etaleAbelianDerivedInverseImage.{u, v} π).mapIso
          (etaleConstantIntegersIso.{u, v} i p)).symm :=
    Iso.ext (by simpa [etaleConstantIntegersIso, etaleConstantIntegers] using h)
  exact congrArg Iso.hom (Iso.symm_eq_iff.mp e)

end Composition

section Equivalences

variable {X Y : Scheme.{u}}

/-- **`H^p(X, Rf_* N) ≅ H^p(Y, N)`** for `f : Y ⟶ X`, with `H^p` read as morphisms out of
`ℤ[-p]`: the adjunction `f⁻¹ ⊣ Rf_*` and the identification `ℤ_Y[-p] ≅ f⁻¹ ℤ_X[-p]`. -/
public def etaleDerivedCohomologyDirectImageEquiv (f : Y ⟶ X) (p : ℤ)
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    etaleDerivedCohomology.{u, v} X p ((etaleAbelianDerivedDirectImage.{u, v} f).obj N) ≃+
      etaleDerivedCohomology.{u, v} Y p N :=
  ((etaleAbelianDerivedAdjunction.{u, v} f).homAddEquiv _ _).symm.trans
    (AddEquiv.ofBijective (Preadditive.leftComp N (etaleConstantIntegersIso.{u, v} f p).hom)
      ⟨fun _ _ h ↦ (cancel_epi _).mp h, fun x ↦ ⟨(etaleConstantIntegersIso.{u, v} f p).inv ≫ x,
        by simp [Preadditive.leftComp]⟩⟩)

/-- The identification `H^p(X, Rf_* N) ≅ H^p(Y, N)`, written out. -/
public theorem etaleDerivedCohomologyDirectImageEquiv_apply (f : Y ⟶ X) (p : ℤ)
    {N : DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (w : etaleDerivedCohomology.{u, v} X p ((etaleAbelianDerivedDirectImage.{u, v} f).obj N)) :
    etaleDerivedCohomologyDirectImageEquiv.{u, v} f p N w =
      (etaleConstantIntegersIso.{u, v} f p).hom ≫
        ((etaleAbelianDerivedAdjunction.{u, v} f).homEquiv _ _).symm w :=
  rfl

/-- The identification `H^p(X, Rf_* N) ≅ H^p(Y, N)` is natural in `N`. -/
public theorem etaleDerivedCohomologyDirectImageEquiv_comp (f : Y ⟶ X) (p : ℤ)
    {N N' : DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (w : etaleDerivedCohomology.{u, v} X p ((etaleAbelianDerivedDirectImage.{u, v} f).obj N))
    (h : N ⟶ N') :
    etaleDerivedCohomologyDirectImageEquiv.{u, v} f p N'
        (w ≫ (etaleAbelianDerivedDirectImage.{u, v} f).map h) =
      etaleDerivedCohomologyDirectImageEquiv.{u, v} f p N w ≫ h := by
  rw [etaleDerivedCohomologyDirectImageEquiv_apply, etaleDerivedCohomologyDirectImageEquiv_apply,
    Adjunction.homEquiv_naturality_right_symm, Category.assoc]

/-- **Under `H^p(X, Rf_* f⁻¹ K) ≅ H^p(Y, f⁻¹ K)`, the unit `K ⟶ Rf_* f⁻¹ K` induces the
restriction map.** -/
public theorem etaleDerivedCohomologyDirectImageEquiv_comp_unit (f : Y ⟶ X) (p : ℤ)
    {K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (x : etaleDerivedCohomology.{u, v} X p K) :
    etaleDerivedCohomologyDirectImageEquiv.{u, v} f p _
        (x ≫ (etaleAbelianDerivedAdjunction.{u, v} f).unit.app K) =
      etaleDerivedCohomologyRestriction.{u, v} f p K x := by
  rw [etaleDerivedCohomologyDirectImageEquiv_apply, etaleDerivedCohomologyRestriction_apply,
    Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_counit]
  simp

/-- The identification `ℤ_X[-(p+1)] ≅ ℤ_X[-p][-1]`: the shift of a single complex, through the
commutation of the derived inverse image along `X ⟶ Spec ℤ` with the shift. -/
public def etaleConstantIntegersShiftIso (X : Scheme.{u}) (p : ℤ) :
    etaleConstantIntegers.{u, v} X (p + 1) ≅ (etaleConstantIntegers.{u, v} X p)⟦(-1 : ℤ)⟧ :=
  (etaleAbelianDerivedInverseImage.{u, v} (toSpecULiftZ X)).mapIso
      (((DerivedCategory.singleFunctors _).shiftIso (-1) (p + 1) p (by omega)).app _).symm ≪≫
    ((etaleAbelianDerivedInverseImage.{u, v} (toSpecULiftZ X)).commShiftIso (-1 : ℤ)).app _

/-- The map `Hom(ℤ_X[-p], M[1]) ⟶ H^{p+1}(X, M)`: shift by `-1`, then identify
`ℤ_X[-(p+1)] ≅ ℤ_X[-p][-1]` and `M[1][-1] ≅ M`. -/
public def etaleDerivedCohomologyShiftHom (X : Scheme.{u}) (p : ℤ)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    (etaleConstantIntegers.{u, v} X p ⟶ M⟦(1 : ℤ)⟧) →+ etaleDerivedCohomology.{u, v} X (p + 1) M :=
  (Preadditive.leftComp _ (etaleConstantIntegersShiftIso.{u, v} X p).hom).comp
    ((Preadditive.rightComp _ ((shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).hom.app M)).comp
      (shiftFunctor _ (-1 : ℤ)).mapAddHom)

/-- The map `Hom(ℤ_X[-p], M[1]) ⟶ H^{p+1}(X, M)`, written out. -/
public theorem etaleDerivedCohomologyShiftHom_apply (X : Scheme.{u}) (p : ℤ)
    {M : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (y : etaleConstantIntegers.{u, v} X p ⟶ M⟦(1 : ℤ)⟧) :
    etaleDerivedCohomologyShiftHom.{u, v} X p M y =
      (etaleConstantIntegersShiftIso.{u, v} X p).hom ≫ y⟦(-1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).hom.app M :=
  rfl

/-- **`Hom(ℤ_X[-p], M[1]) ≅ H^{p+1}(X, M)`**: the shift is an equivalence. -/
public def etaleDerivedCohomologyShiftEquiv (X : Scheme.{u}) (p : ℤ)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    (etaleConstantIntegers.{u, v} X p ⟶ M⟦(1 : ℤ)⟧) ≃+ etaleDerivedCohomology.{u, v} X (p + 1) M :=
  AddEquiv.ofBijective (etaleDerivedCohomologyShiftHom.{u, v} X p M) (by
    refine ⟨fun y y' h ↦ ?_, fun x ↦ ?_⟩
    · simp only [etaleDerivedCohomologyShiftHom_apply, cancel_epi, cancel_mono] at h
      exact (shiftFunctor _ (-1 : ℤ)).map_injective h
    · obtain ⟨y, hy⟩ := (shiftFunctor _ (-1 : ℤ)).map_surjective
        ((etaleConstantIntegersShiftIso.{u, v} X p).inv ≫ x ≫
          (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).inv.app M)
      exact ⟨y, by simp [etaleDerivedCohomologyShiftHom_apply, hy]⟩)

/-- The identification `Hom(ℤ_X[-p], M[1]) ≅ H^{p+1}(X, M)` is natural in `M`. -/
public theorem etaleDerivedCohomologyShiftEquiv_comp (X : Scheme.{u}) (p : ℤ)
    {M M' : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (y : etaleConstantIntegers.{u, v} X p ⟶ M⟦(1 : ℤ)⟧) (h : M ⟶ M') :
    etaleDerivedCohomologyShiftEquiv.{u, v} X p M' (y ≫ h⟦(1 : ℤ)⟧') =
      etaleDerivedCohomologyShiftEquiv.{u, v} X p M y ≫ h := by
  have hn := (shiftFunctorCompIsoId (DerivedCategory (Sheaf X.smallEtaleTopology
    AddCommGrpCat.{max (u + 1) v})) (1 : ℤ) (-1) (by omega)).hom.naturality h
  simp only [Functor.comp_map, Functor.id_map] at hn
  simp only [etaleDerivedCohomologyShiftEquiv, AddEquiv.ofBijective_apply,
    etaleDerivedCohomologyShiftHom_apply, Functor.map_comp, Category.assoc, hn]

/-- The identification `ℤ_Y[-p] ≅ ℤ_Y[0][-p]` of the constant sheaf placed in degree `p` with the
shift of the constant sheaf placed in degree `0`, `ℤ_Y` being Mathlib's constant sheaf on `ℤ`. -/
public def etaleConstantIntegersIsoShift (Y : Scheme.{u}) (p : ℤ) :
    etaleConstantIntegers.{u, v} Y p ≅
      ((DerivedCategory.singleFunctor _ 0).obj ((constantSheaf Y.smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v}).obj (AddCommGrpCat.of (ULift ℤ))))⟦-p⟧ :=
  (etaleAbelianDerivedInverseImage.{u, v} (toSpecULiftZ Y)).mapIso
      (((DerivedCategory.singleFunctors _).shiftIso (-p) p 0 (by omega)).app _).symm ≪≫
    ((etaleAbelianDerivedInverseImage.{u, v} (toSpecULiftZ Y)).commShiftIso (-p)).app _ ≪≫
    (shiftFunctor _ (-p)).mapIso
      (((etaleAbelianInverseImage.{u, v} (toSpecULiftZ Y)).mapDerivedCategorySingleFunctor
          0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          ((etaleAbelianInverseImageConstantIso.{u, v} (toSpecULiftZ Y)).app _))

/-- **`H^p(Y, M)` is `Hom(ℤ_Y[0], M[p])`**, the group of shifted morphisms of degree `p` from the
constant sheaf `ℤ_Y` placed in degree `0`; for `M` a sheaf `F` placed in degree `0` this is the
description of Mathlib's `Sheaf.H F p = Ext^p(ℤ_Y, F)` in the derived category. -/
public def etaleDerivedCohomologyEquivShiftedHom (Y : Scheme.{u}) (p : ℤ)
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    etaleDerivedCohomology.{u, v} Y p M ≃+
      ShiftedHom ((DerivedCategory.singleFunctor _ 0).obj ((constantSheaf Y.smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v}).obj (AddCommGrpCat.of (ULift ℤ)))) M p :=
  (AddEquiv.ofBijective (Preadditive.leftComp M (etaleConstantIntegersIsoShift.{u, v} Y p).inv)
      ⟨fun _ _ h ↦ (cancel_epi _).mp h, fun x ↦ ⟨(etaleConstantIntegersIsoShift.{u, v} Y p).hom ≫ x,
        by simp [Preadditive.leftComp]⟩⟩).trans
    (haveI : (shiftEquiv' (DerivedCategory (Sheaf Y.smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v})) (-p) p (by omega)).functor.Additive :=
      inferInstanceAs (shiftFunctor _ (-p)).Additive
    (shiftEquiv' _ (-p) p (by omega)).toAdjunction.homAddEquiv _ _)

end Equivalences

end Stacks.EtaleCohomology

end
