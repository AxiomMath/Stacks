module

public import StacksFrontier.Cotangent.SheavesOfRings.BaseChangedNaiveMapConormal
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentSquare
public import StacksFrontier.Deformation.ToposThickening.CotangentObstructionNaiveSquare

/-!
# The comparison `L ⟶ NL` commutes with change of base

Let `g : A ⟶ B` and `h : B ⟶ D` be homomorphisms of sheaves of commutative rings on a site. The
canonical map `L_{D/A} ⟶ NL_{D/A}` of Tag 08US from the cotangent complex to the naive cotangent
complex of Tag 08TW, `CategoryTheory.Sheaf.canonicalNaiveComparison`, is compatible with the
change of base ring along `g`: the square

`L_{D/A} ⟶ L_{D/B}`, `NL_{D/A} ⟶ NL_{D/B}`

formed with `CategoryTheory.Sheaf.towerCotangentChangeOfBase` and
`Stacks.SheafOfModules.naiveCotangentComplexMapOfBase` commutes, as a square of maps of
complexes.

## Main results

* `CategoryTheory.Sheaf.towerFunctorialitySquare_resolution_zero_comp_resolutionZeroIsoFreeAlgebra`
  : the map `P₀(A → D) ⟶ P₀(B → D)` of degree-zero terms of the standard resolutions is, through
  `P₀ ≅ A[D]` and `P₀ ≅ B[D]`, the map `A[D] ⟶ B[D]` of free algebras.
* `CategoryTheory.Sheaf.towerCotangentChangeOfBase_comp_canonicalNaiveComparison`: **the square
  commutes.**

## Implementation notes

Both composites are maps into a complex concentrated in degrees `-1` and `0`, and are compared
there on the pure differentials `d x` that generate the terms of `L_{D/A}`. In degree `-1` the
value is the conormal class of `d₀ x - d₁ x`, in degree `0` it is `1 ⊗ d x`, read in the
canonical presentation `A[D] ⟶ D`; the comparison of the two presentations is the ring map
identity above, checked on coefficients and on variables. Universe parameters are written out
where `w` would otherwise be inferred only from `max u v w`, which sends the elaborator into
expensive unfoldings.

## References

* [Stacks Project, Tag 08US](https://stacks.math.columbia.edu/tag/08US)
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX)
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B D : Sheaf J CommRingCat.{max u v w}} (g : A ⟶ B) (h : B ⟶ D)

/-- An `eqToHom` followed by the image of `eqToHom ≫ φ` is a single `eqToHom` followed by the
image of `φ`. -/
theorem eqToHom_comp_map_eqToHom_comp {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (K : 𝒞 ⥤ 𝒟)
    {X Y Z : 𝒞} {W : 𝒟} (p : X = Y) (φ : Y ⟶ Z) (q : W = K.obj X) :
    eqToHom q ≫ K.map (eqToHom p ≫ φ) = eqToHom (q.trans (congrArg K.obj p)) ≫ K.map φ := by
  subst p
  simp

/-- If `f` is `N` conjugated by `eqToHom`s, then `f` precomposed with the inverse of the source
`eqToHom` is `N` followed by the target `eqToHom`. -/
private theorem eqToHom_symm_comp_of_eq_eqToHom_comp {𝒞 : Type*} [Category 𝒞] {X X' Y Y' : 𝒞}
    {p : X = X'} {q : Y' = Y} {f : X ⟶ Y} {N : X' ⟶ Y'}
    (hf : f = eqToHom p ≫ N ≫ eqToHom q) : eqToHom p.symm ≫ f = N ≫ eqToHom q := by
  subst p q
  simpa using hf

/-- **The degree-zero map of standard resolutions of the change of base is the map of free
algebras**: through `P₀ ≅ A[D]` and `P₀ ≅ B[D]`, the map `P₀(A → D) ⟶ P₀(B → D)` of the square
`(g, 𝟙 D)` is the map `A[D] ⟶ B[D]` along `g` sending `[d]` to `[d]`. -/
theorem towerFunctorialitySquare_resolution_zero_comp_resolutionZeroIsoFreeAlgebra :
    (towerFunctorialitySquare.{u, v, w} J g h).resolution (op ⦋0⦌) ≫
        (resolutionZeroIsoFreeAlgebra.{u, v, w} J h).hom =
      (resolutionZeroIsoFreeAlgebra.{u, v, w} J (g ≫ h)).hom ≫
        Stacks.SheafOfModules.canonicalFreeAlgebraMapOfSquare J A B D D g (𝟙 D) := by
  rw [← cancel_epi (resolutionZeroIsoFreeAlgebra.{u, v, w} J (g ≫ h)).inv, Iso.inv_hom_id_assoc]
  refine Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_hom_ext J A _ _ ?_ ?_
  · rw [← Category.assoc, coefficientMap_comp_resolutionZeroIsoFreeAlgebra_inv, ← Category.assoc,
      (towerFunctorialitySquare.{u, v, w} J g h).resolution_base, Category.assoc,
      resolutionBase_comp_resolutionZeroIsoFreeAlgebra_hom,
      Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare]
  · have hX : (resolutionZeroIsoFreeAlgebra.{u, v, w} J (g ≫ h)).inv ≫
        (towerFunctorialitySquare.{u, v, w} J g h).resolution (op ⦋0⦌) ≫
          (resolutionZeroIsoFreeAlgebra.{u, v, w} J h).hom =
        (ofFreeAlgebraUnder.{u, v, w} J (g ≫ h) ≫
          (standardResolutionComonad J A : Under A ⥤ Under A).map
            (squareAlgebraMap.{u, v, w} J g (𝟙 D) (by simp)) ≫
          (standardResolutionComonadSquareHom.{u, v, w} J g).app (Under.mk h) ≫
          (squareAlgebras J g).map (toFreeAlgebraUnder.{u, v, w} J h)).right := by
      have h1 : ∀ {X : Under A} {Z : Under B} (u : X ⟶ (squareAlgebras J g).obj Z),
          Functor.iterateCompHomObj (standardResolutionComonadSquareHom.{u, v, w} J g) 1 u =
            (standardResolutionComonad J A : Under A ⥤ Under A).map u ≫
              (standardResolutionComonadSquareHom.{u, v, w} J g).app Z := by
        intro X Z u
        simp [Functor.iterateCompHomObj, Functor.iterateCompHom, Functor.iterate]
      have hU : (resolutionZeroIsoFreeAlgebraUnder.{u, v, w} J (g ≫ h)).inv ≫
          squareResolutionTermMap.{u, v, w} J g (𝟙 D) (by simp) 0 ≫
            (squareAlgebras J g).map (resolutionZeroIsoFreeAlgebraUnder.{u, v, w} J h).hom =
          ofFreeAlgebraUnder.{u, v, w} J (g ≫ h) ≫
            (standardResolutionComonad J A : Under A ⥤ Under A).map
              (squareAlgebraMap.{u, v, w} J g (𝟙 D) (by simp)) ≫
            (standardResolutionComonadSquareHom.{u, v, w} J g).app (Under.mk h) ≫
            (squareAlgebras J g).map (toFreeAlgebraUnder.{u, v, w} J h) := by
        simp only [resolutionZeroIsoFreeAlgebraUnder, squareResolutionTermMap,
          Functor.transportObjHom, h1, Iso.trans_inv, Iso.trans_hom, eqToIso.inv, eqToIso.hom,
          eqToHom_map, Category.assoc]
        refine (Category.assoc _ _ _).trans
          (congrArg (ofFreeAlgebraUnder.{u, v, w} J (g ≫ h) ≫ ·) ?_)
        refine (eqToHom_trans_assoc _ _ _).trans ?_
        refine (congrArg (· ≫ _) (eqToHom_refl _ _)).trans ((Category.id_comp _).trans ?_)
        refine congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_)
        exact (eqToHom_comp_map_eqToHom_comp _ _ _ _).trans
          ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _))
      exact congrArg Under.Hom.right hU
    rw [hX]
    have hsq : (g ≫ h) ≫ 𝟙 D = g ≫ h := Category.comp_id _
    have hφ := (freeAlgebraSheafAdjunction J A).unit.naturality
      ((forgetAlgebraSheaf J A).map (squareAlgebraMap.{u, v, w} J g (𝟙 D) hsq))
    have he := Adjunction.unit_comp_map_comonadSquareHom (freeAlgebraSheafAdjunction J A)
      (freeAlgebraSheafAdjunction J B) (Iso.refl (squareAlgebras J g ⋙ forgetAlgebraSheaf J A))
      (Under.mk h)
    have ht := ((freeAlgebraSheafAdjunction J B).homEquiv_unit _ _
      (toFreeAlgebraUnder.{u, v, w} J h)).symm
    have key : (freeAlgebraSheafAdjunction J A).unit.app
          ((forgetAlgebraSheaf J A).obj (Under.mk (g ≫ h))) ≫
        (forgetAlgebraSheaf J A).map
          ((standardResolutionComonad J A : Under A ⥤ Under A).map
            (squareAlgebraMap.{u, v, w} J g (𝟙 D) hsq) ≫
          (standardResolutionComonadSquareHom.{u, v, w} J g).app (Under.mk h) ≫
          (squareAlgebras J g).map (toFreeAlgebraUnder.{u, v, w} J h)) =
        (forgetAlgebraSheaf J A).map (squareAlgebraMap.{u, v, w} J g (𝟙 D) hsq) ≫
          (freeAlgebraSheafAdjunction J B).homEquiv _ _ (toFreeAlgebraUnder.{u, v, w} J h) := by
      simp only [Functor.id_map, Functor.comp_map] at hφ
      simp only [Iso.refl_hom, Iso.refl_inv, NatTrans.id_app] at he
      refine (congrArg (_ ≫ ·) (((forgetAlgebraSheaf J A).map_comp _ _).trans
        (congrArg (_ ≫ ·) ((forgetAlgebraSheaf J A).map_comp _ _)))).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ _) hφ.symm).trans ?_
      refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
      refine (Category.assoc _ _ _).symm.trans ?_
      exact (congrArg (· ≫ _) he).trans ht
    have hv := Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc J A _
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf J D) (freeOnTarget.{u, v, w} J (g ≫ h)).hom
      ((freeAlgebraSheafAdjunction J A).unit.app
        ((forgetAlgebraSheaf J A).obj (Under.mk (g ≫ h)))).hom
    have hk := congrArg (fun t => t.hom) key
    rw [Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_freeAlgebraMapOfSquare]
    change Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable J A _ ≫ Functor.whiskerRight
      ((sheafToPresheaf J CommRingCat).map ((ofFreeAlgebraUnder.{u, v, w} J (g ≫ h)).right ≫
        ((standardResolutionComonad J A : Under A ⥤ Under A).map
            (squareAlgebraMap.{u, v, w} J g (𝟙 D) hsq) ≫
          (standardResolutionComonadSquareHom.{u, v, w} J g).app (Under.mk h) ≫
          (squareAlgebras J g).map (toFreeAlgebraUnder.{u, v, w} J h)).right))
        (forget CommRingCat) = _
    refine (congrArg (_ ≫ ·) ((congrArg (fun t => Functor.whiskerRight t (forget CommRingCat))
      ((sheafToPresheaf J CommRingCat).map_comp _ _)).trans
        (Functor.whiskerRight_comp _ _ _))).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) hv).trans ?_
    refine Eq.trans ?_ (hk.trans ?_)
    · rfl
    · exact (congrArg (fun t => ((forgetAlgebraSheaf J A).map
        (squareAlgebraMap.{u, v, w} J g (𝟙 D) hsq) ≫ t).hom)
          (Equiv.apply_symm_apply _ _)).trans rfl

/-- The change-of-base map `L_{D/A} ⟶ L_{D/B}` on a pure differential `d x` in degree `-n` is the
pure differential of the image of `x` under the map of standard resolutions. -/
theorem towerCotangentChangeOfBase_f_degreeIso_inv (n : ℕ) (U : Cᵒᵖ)
    (x : (resolutionTerm.{u, v, w} J (g ≫ h) (op ⦋n⦌)).obj.obj U) :
    ((towerCotangentChangeOfBase.{u, v, w} J g h).f (-(n : ℤ))).val.app U
        ((cotangentComplex_degreeIso.{u, v, w} J (g ≫ h) n).inv.val.app U
          (((cotangentSimplicialModule.{u, v, w} J (g ≫ h)).universalDerivation (op ⦋n⦌)).d x)) =
      (cotangentComplex_degreeIso.{u, v, w} J h n).inv.val.app U
        (((cotangentSimplicialModule.{u, v, w} J h).universalDerivation (op ⦋n⦌)).d
          (((towerFunctorialitySquare.{u, v, w} J g h).resolution (op ⦋n⦌)).hom.app U x)) := by
  have e := towerCotangentChangeOfBase_derivation.{u, v, w} J g h n U x
  rw [derivationEquiv_val_app] at e
  have hm : (cotangentComplex_degreeIso.{u, v, w} J (g ≫ h) n).inv ≫
      (towerCotangentChangeOfBase.{u, v, w} J g h).f (-(n : ℤ)) =
      ((cotangentComplex_degreeIso.{u, v, w} J (g ≫ h) n).inv ≫
        (towerCotangentChangeOfBase.{u, v, w} J g h).f (-(n : ℤ)) ≫
          (cotangentComplex_degreeIso.{u, v, w} J h n).hom) ≫
        (cotangentComplex_degreeIso.{u, v, w} J h n).inv := by
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (congrArg (fun k => (k.val.app U).hom
      (((cotangentSimplicialModule.{u, v, w} J (g ≫ h)).universalDerivation (op ⦋n⦌)).d x))
        hm).trans
    (congrArg ((cotangentComplex_degreeIso.{u, v, w} J h n).inv.val.app U).hom e)

section Generic

universe v₁ u₁ w₁ z₁

variable {C₁ : Type u₁} [Category.{v₁} C₁] (K : GrothendieckTopology C₁)
  [HasWeakSheafify K CommRingCat.{w₁}]
  [K.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  (A₀ B₀ : Sheaf K CommRingCat.{w₁}) (a : A₀ ⟶ B₀) (A₀' : Sheaf K CommRingCat.{w₁})
  (a' : A₀' ⟶ B₀) (f : A₀ ⟶ A₀') (hf : a = f ≫ a')
  [Presheaf.IsLocallySurjective K (Stacks.Sites.FreeAlgebra.canonicalPresentation K A₀ B₀ a).hom]
  [Presheaf.IsLocallySurjective K
    (Stacks.Sites.FreeAlgebra.canonicalPresentation K A₀' B₀ a').hom]

include hf in
/-- The change of base ring of the naive cotangent complex, in degree `-1`, on a conormal class:
the class of `z` goes to the class of its image in `A'[B]`. -/
theorem naiveCotangentConormalMapOfBase_conormalClass (X : C₁ᵒᵖ)
    (x : Stacks.Sites.Conormal.kernelIdeal
      (Stacks.Sites.FreeAlgebra.canonicalPresentation K A₀ B₀ a).hom X) :
    ((Stacks.SheafOfModules.naiveCotangentConormalMapOfBase.{v₁, u₁, w₁, z₁} K A₀ B₀ a A₀' a' f
        hf).val.app X)
      (Stacks.Sites.Conormal.conormalClass.{v₁, u₁, w₁, z₁} K A₀ _ B₀
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap K A₀
          (Stacks.Sites.FreeAlgebra.underlyingPresheaf K B₀))
        (Stacks.Sites.FreeAlgebra.canonicalPresentation K A₀ B₀ a) X x) =
      Stacks.Sites.Conormal.conormalClass.{v₁, u₁, w₁, z₁} K A₀' _ B₀
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap K A₀'
          (Stacks.Sites.FreeAlgebra.underlyingPresheaf K B₀))
        (Stacks.Sites.FreeAlgebra.canonicalPresentation K A₀' B₀ a') X
        ⟨(Stacks.SheafOfModules.canonicalFreeAlgebraMapOfSquare K A₀ A₀' B₀ B₀ f (𝟙 B₀)).hom.app
          X x, Stacks.Sites.Conormal.kernelIdeal_le_comap_square _ _ _ _
            (Stacks.Sites.Conormal.hom_of_square
              (Stacks.SheafOfModules.freeAlgebraMapOfSquare_comp_canonicalPresentation K A₀ A₀'
                B₀ B₀ a a' f (𝟙 B₀) (Stacks.SheafOfModules.comp_id_eq_comp_of_fac K A₀ B₀ a A₀'
                  a' f hf))) X x.2⟩ :=
  Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass.{v₁, u₁, w₁, z₁} K A₀ A₀' _ _ B₀
    B₀ _ _ _ _ _ _ _ X x

include hf in
/-- The change of base ring of the naive cotangent complex, in degree `0`, on `1 ⊗ d x`: it is
`1 ⊗ d` of the image of `x` in `A'[B]`. -/
theorem naiveCotangentTensorMapOfBase_tensorDifferential (X : C₁ᵒᵖ)
    (x : (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf K A₀
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf K B₀)).obj.obj X) :
    ((Stacks.SheafOfModules.naiveCotangentTensorMapOfBase.{v₁, u₁, w₁, z₁} K A₀ B₀ a A₀' a' f
        hf).val.app X)
      (Stacks.Sites.Conormal.tensorDifferential.{v₁, u₁, w₁, z₁} K A₀ _ B₀
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap K A₀
          (Stacks.Sites.FreeAlgebra.underlyingPresheaf K B₀))
        (Stacks.Sites.FreeAlgebra.canonicalPresentation K A₀ B₀ a) X x) =
      Stacks.Sites.Conormal.tensorDifferential.{v₁, u₁, w₁, z₁} K A₀' _ B₀
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap K A₀'
          (Stacks.Sites.FreeAlgebra.underlyingPresheaf K B₀))
        (Stacks.Sites.FreeAlgebra.canonicalPresentation K A₀' B₀ a') X
        ((Stacks.SheafOfModules.canonicalFreeAlgebraMapOfSquare K A₀ A₀' B₀ B₀ f (𝟙 B₀)).hom.app
          X x) :=
  Stacks.Sites.Conormal.tensorSheafMapOfSquare_tensorDifferential.{v₁, u₁, w₁, z₁} K A₀ A₀' _ _
    B₀ B₀ _ _ _ _ _ _ _ _ _ X x

end Generic

/-- The two composites of the square, in degree `-1`, on a pure differential. -/
theorem towerCotangentChangeOfBase_comp_canonicalNaiveComparison_negOne_apply (U : Cᵒᵖ)
    (x : (resolutionTerm.{u, v, w} J (g ≫ h) (op ⦋1⦌)).obj.obj U) :
    ((canonicalNaiveComparison.{u, v, w} J h).f (-1)).val.app U
        (((towerCotangentChangeOfBase.{u, v, w} J g h).f (-1)).val.app U
          ((cotangentComplex_degreeIso.{u, v, w} J (g ≫ h) 1).inv.val.app U
            (((cotangentSimplicialModule.{u, v, w} J (g ≫ h)).universalDerivation
              (op ⦋1⦌)).d x))) =
      ((Stacks.SheafOfModules.naiveCotangentComplexMapOfBase.{v, u, max u v w, u}
          J A D (g ≫ h) B h g rfl).f (-1)).val.app U
        (((canonicalNaiveComparison.{u, v, w} J (g ≫ h)).f (-1)).val.app U
          ((cotangentComplex_degreeIso.{u, v, w} J (g ≫ h) 1).inv.val.app U
            (((cotangentSimplicialModule.{u, v, w} J (g ≫ h)).universalDerivation
              (op ⦋1⦌)).d x))) := by
  have e₁ := towerCotangentChangeOfBase_f_degreeIso_inv.{u, v, w} J g h 1 U x
  have e₂ := canonicalNaiveComparison_negOne_apply.{u, v, w} J h U
    (((towerFunctorialitySquare.{u, v, w} J g h).resolution (op ⦋1⦌)).hom.app U x)
  have e₃ := canonicalNaiveComparison_negOne_apply.{u, v, w} J (g ≫ h) U x
  rw [canonicalNaiveClass_eq.{u, v, w}] at e₂ e₃
  refine (congrArg (((canonicalNaiveComparison.{u, v, w} J h).f (-1)).val.app U).hom e₁).trans
    (e₂.trans ?_)
  rw [e₃]
  have hM := Stacks.SheafOfModules.naiveCotangentComplexMapOfBase_f_negOne.{v, u, max u v w, u}
    J A D (g ≫ h) B h g rfl
  have hk := eqToHom_symm_comp_of_eq_eqToHom_comp hM
  refine Eq.trans ?_ (congrArg (fun k => (k.val.app U).hom
    (Stacks.Sites.Conormal.conormalClass.{v, u, max u v w, u} J A _ D
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J D))
      (Stacks.Sites.FreeAlgebra.canonicalPresentation J A D (g ≫ h)) U
      (canonicalRelation.{u, v, w} J (g ≫ h) U (faceDifference.{u, v, w} J (g ≫ h) U x)))) hk).symm
  have hc := naiveCotangentConormalMapOfBase_conormalClass.{v, u, max u v w, u} J A D (g ≫ h) B h
    g rfl U (canonicalRelation.{u, v, w} J (g ≫ h) U (faceDifference.{u, v, w} J (g ≫ h) U x))
  refine Eq.trans ?_ (congrArg ((eqToHom
    (Stacks.SheafOfModules.naiveCotangentComplex_X_negOne.{v, u, max u v w, u}
      J B D h).symm).val.app U).hom hc).symm
  refine congrArg (naiveConormalClass.{u, v, w} J h U) (Subtype.ext ?_)
  have hfd := faceDifference_resolution (towerFunctorialitySquare.{u, v, w} J g h) U x
  have hR := congrArg (fun k => k.hom.app U
      ((faceDifference.{u, v, w} J (g ≫ h) U x : Stacks.Sites.Conormal.kernelIdeal
        (resolutionAugmentation J (g ≫ h) (op ⦋0⦌)).hom U) :
          (resolutionTerm.{u, v, w} J (g ≫ h) (op ⦋0⦌)).obj.obj U))
    (towerFunctorialitySquare_resolution_zero_comp_resolutionZeroIsoFreeAlgebra.{u, v, w} J g h)
  change ((resolutionZeroIsoFreeAlgebra.{u, v, w} J h).hom.hom.app U)
      ((faceDifference.{u, v, w} J h U
        (((towerFunctorialitySquare.{u, v, w} J g h).resolution (op ⦋1⦌)).hom.app U x) :
          Stacks.Sites.Conormal.kernelIdeal (resolutionAugmentation J h (op ⦋0⦌)).hom U) :
        (resolutionTerm.{u, v, w} J h (op ⦋0⦌)).obj.obj U) = _
  rw [← hfd]
  exact hR

section Zero

variable {A' B' : Sheaf J CommRingCat.{max u v w}} (f : A' ⟶ B')

/-- In degree `0` the identification of the naive cotangent complexes of the presentations by `P₀`
and by `A[B]` is the identification of their tensor-differential sheaves. -/
theorem naiveCotangentComplexXZeroIso_inv_comp_isoCanonical :
    (naiveCotangentComplexXZeroIso.{u, v, w} J f).inv ≫
        (naiveCotangentComplexIsoCanonical.{u, v, w} J f).hom.f 0 =
      (naiveTensorIso.{u, v, w} J f).hom ≫
        eqToHom (Stacks.SheafOfModules.naiveCotangentComplex_X_zero.{v, u, max u v w, u}
          J A' B' f).symm := by
  rw [naiveCotangentComplexIsoCanonical, HomologicalComplex.doubleIsoOfIso_hom,
    HomologicalComplex.doubleMap_f₁, naiveCotangentComplexXZeroIso]
  exact (Iso.inv_hom_id_assoc (HomologicalComplex.doubleXIso₁ (naiveSequence.{u, v, w} J f).f
    ComplexShape.upIntRelNegOneZero (by decide)) _).trans rfl

/-- The local section `1 ⊗ d q` of `B ⊗_{A[B]} Ω_{A[B]/A}`, read in the middle term of the conormal
sequence of the canonical presentation `A[B] ⟶ B`. -/
noncomputable abbrev canonicalTensorDifferentialSections (U : Cᵒᵖ)
    (q : (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A'
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B')).obj.obj U) :
    (Stacks.SheafOfModules.canonicalConormalSequence.{v, u, max u v w, u} J A' B' f).X₂.val.obj
      U :=
  Stacks.Sites.Conormal.tensorDifferential.{v, u, max u v w, u} J A' _ B'
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A'
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B'))
    (Stacks.Sites.FreeAlgebra.canonicalPresentation J A' B' f) U q

/-- The identification `B ⊗_{P₀} Ω_{P₀/A} ≅ B ⊗_{A[B]} Ω_{A[B]/A}` sends `1 ⊗ d p` to
`1 ⊗ d` of the image of `p` in `A[B]`. -/
theorem naiveTensorIso_hom_tensorDifferentialSections (U : Cᵒᵖ)
    (p : (resolutionTerm.{u, v, w} J f (op ⦋0⦌)).obj.obj U) :
    ((naiveTensorIso.{u, v, w} J f).hom.val.app U).hom
        (tensorDifferentialSections.{u, v, w} J f U p) =
      canonicalTensorDifferentialSections.{u, v, w} J f U
        ((resolutionZeroIsoFreeAlgebra.{u, v, w} J f).hom.hom.app U p) :=
  Stacks.Sites.Conormal.tensorSheafMapOfFac_tensorDifferential _ _ _ _ _ _ _ _ _ _
    (resolutionZeroIsoFreeAlgebra_hom_comp_canonicalPresentation.{u, v, w} J f)
    (resolutionBase_comp_resolutionZeroIsoFreeAlgebra_hom.{u, v, w} J f) _ _

/-- **The comparison of Tag 08US on a pure differential, in degree `0`**: it sends `d p` to
`1 ⊗ d p`, read in the canonical presentation. -/
theorem canonicalNaiveComparison_zero_apply (U : Cᵒᵖ)
    (p : (resolutionTerm.{u, v, w} J f (op ⦋0⦌)).obj.obj U) :
    ((canonicalNaiveComparison.{u, v, w} J f).f 0).val.app U
        ((cotangentComplex_degreeIso.{u, v, w} J f 0).inv.val.app U
          (((cotangentSimplicialModule.{u, v, w} J f).universalDerivation (op ⦋0⦌)).d p)) =
      (eqToHom (Stacks.SheafOfModules.naiveCotangentComplex_X_zero.{v, u, max u v w, u}
          J A' B' f).symm).val.app U
        (canonicalTensorDifferentialSections.{u, v, w} J f U
          ((resolutionZeroIsoFreeAlgebra.{u, v, w} J f).hom.hom.app U p)) := by
  have hm : (cotangentComplex_degreeIso.{u, v, w} J f 0).inv ≫
      (canonicalNaiveComparison.{u, v, w} J f).f 0 =
      naiveComparisonZero.{u, v, w} J f ≫ (naiveTensorIso.{u, v, w} J f).hom ≫
        eqToHom (Stacks.SheafOfModules.naiveCotangentComplex_X_zero.{v, u, max u v w, u}
          J A' B' f).symm := by
    rw [canonicalNaiveComparison, HomologicalComplex.comp_f, naiveComparison_f_zero,
      ← naiveCotangentComplexXZeroIso_inv_comp_isoCanonical]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hz := derivationEquiv_naiveComparisonZero.{u, v, w} J f U p
  rw [derivationEquiv_val_app] at hz
  refine (congrArg (fun k => (k.val.app U).hom
    (((cotangentSimplicialModule.{u, v, w} J f).universalDerivation (op ⦋0⦌)).d p)) hm).trans ?_
  have h1 := congrArg ((naiveTensorIso.{u, v, w} J f).hom.val.app U).hom hz
  have h2 := h1.trans (naiveTensorIso_hom_tensorDifferentialSections.{u, v, w} J f U p)
  have h3 := congrArg ((eqToHom (Stacks.SheafOfModules.naiveCotangentComplex_X_zero.{v, u,
    max u v w, u} J A' B' f).symm).val.app U).hom h2
  exact h3

end Zero

/-- The two composites of the square, in degree `0`, on a pure differential. -/
theorem towerCotangentChangeOfBase_comp_canonicalNaiveComparison_zero_apply (U : Cᵒᵖ)
    (p : (resolutionTerm.{u, v, w} J (g ≫ h) (op ⦋0⦌)).obj.obj U) :
    ((canonicalNaiveComparison.{u, v, w} J h).f 0).val.app U
        (((towerCotangentChangeOfBase.{u, v, w} J g h).f 0).val.app U
          ((cotangentComplex_degreeIso.{u, v, w} J (g ≫ h) 0).inv.val.app U
            (((cotangentSimplicialModule.{u, v, w} J (g ≫ h)).universalDerivation
              (op ⦋0⦌)).d p))) =
      ((Stacks.SheafOfModules.naiveCotangentComplexMapOfBase.{v, u, max u v w, u}
          J A D (g ≫ h) B h g rfl).f 0).val.app U
        (((canonicalNaiveComparison.{u, v, w} J (g ≫ h)).f 0).val.app U
          ((cotangentComplex_degreeIso.{u, v, w} J (g ≫ h) 0).inv.val.app U
            (((cotangentSimplicialModule.{u, v, w} J (g ≫ h)).universalDerivation
              (op ⦋0⦌)).d p))) := by
  have e₁ := towerCotangentChangeOfBase_f_degreeIso_inv.{u, v, w} J g h 0 U p
  have e₂ := canonicalNaiveComparison_zero_apply.{u, v, w} J h U
    (((towerFunctorialitySquare.{u, v, w} J g h).resolution (op ⦋0⦌)).hom.app U p)
  have e₃ := canonicalNaiveComparison_zero_apply.{u, v, w} J (g ≫ h) U p
  have hM := Stacks.SheafOfModules.naiveCotangentComplexMapOfBase_f_zero.{v, u, max u v w, u}
    J A D (g ≫ h) B h g rfl
  have hk := eqToHom_symm_comp_of_eq_eqToHom_comp hM
  have htm := naiveCotangentTensorMapOfBase_tensorDifferential.{v, u, max u v w, u} J A D (g ≫ h)
    B h g rfl U ((resolutionZeroIsoFreeAlgebra.{u, v, w} J (g ≫ h)).hom.hom.app U p)
  have hR := congrArg (fun k => k.hom.app U p)
    (towerFunctorialitySquare_resolution_zero_comp_resolutionZeroIsoFreeAlgebra.{u, v, w} J g h)
  have l₁ := (congrArg (((canonicalNaiveComparison.{u, v, w} J h).f 0).val.app U).hom e₁).trans e₂
  have r₁ := congrArg ((((Stacks.SheafOfModules.naiveCotangentComplexMapOfBase.{v, u,
    max u v w, u} J A D (g ≫ h) B h g rfl).f 0).val.app U).hom) e₃
  have r₂ := congrArg (fun k => (k.val.app U).hom
    (canonicalTensorDifferentialSections.{u, v, w} J (g ≫ h) U
      ((resolutionZeroIsoFreeAlgebra.{u, v, w} J (g ≫ h)).hom.hom.app U p))) hk
  have r₃ := congrArg ((eqToHom (Stacks.SheafOfModules.naiveCotangentComplex_X_zero.{v, u,
    max u v w, u} J B D h).symm).val.app U).hom htm
  refine l₁.trans (Eq.trans ?_ (r₁.trans (r₂.trans r₃)).symm)
  have hR' : ((resolutionZeroIsoFreeAlgebra.{u, v, w} J h).hom.hom.app U)
      (((towerFunctorialitySquare.{u, v, w} J g h).resolution (op ⦋0⦌)).hom.app U p) =
      ((Stacks.SheafOfModules.canonicalFreeAlgebraMapOfSquare J A B D D g (𝟙 D)).hom.app U)
        (((resolutionZeroIsoFreeAlgebra.{u, v, w} J (g ≫ h)).hom.hom.app U) p) := hR
  rw [hR']

/-- **The comparison `L ⟶ NL` of Tag 08US commutes with change of base.** For a tower
`A ⟶ B ⟶ D`, the change-of-base map `L_{D/A} ⟶ L_{D/B}` followed by the canonical map
`L_{D/B} ⟶ NL_{D/B}` is the canonical map `L_{D/A} ⟶ NL_{D/A}` followed by the change of base
ring `NL_{D/A} ⟶ NL_{D/B}` of the naive cotangent complexes. -/
theorem towerCotangentChangeOfBase_comp_canonicalNaiveComparison :
    towerCotangentChangeOfBase.{u, v, w} J g h ≫ canonicalNaiveComparison.{u, v, w} J h =
      canonicalNaiveComparison.{u, v, w} J (g ≫ h) ≫
        Stacks.SheafOfModules.naiveCotangentComplexMapOfBase.{v, u, max u v w, u}
          J A D (g ≫ h) B h g rfl := by
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  by_cases hj₁ : j = -1
  · subst hj₁
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      ← cancel_epi (cotangentComplex_degreeIso.{u, v, w} J (g ≫ h) 1).inv]
    refine hom_ext_of_derivationEquiv.{u, v, w} J (g ≫ h) (op ⦋1⦌) fun U x => ?_
    rw [derivationEquiv_val_app.{u, v, w}, derivationEquiv_val_app.{u, v, w}]
    exact towerCotangentChangeOfBase_comp_canonicalNaiveComparison_negOne_apply.{u, v, w}
      J g h U x
  by_cases hj₀ : j = 0
  · subst hj₀
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      ← cancel_epi (cotangentComplex_degreeIso.{u, v, w} J (g ≫ h) 0).inv]
    refine hom_ext_of_derivationEquiv.{u, v, w} J (g ≫ h) (op ⦋0⦌) fun U p => ?_
    rw [derivationEquiv_val_app.{u, v, w}, derivationEquiv_val_app.{u, v, w}]
    exact towerCotangentChangeOfBase_comp_canonicalNaiveComparison_zero_apply.{u, v, w}
      J g h U p
  · exact (Stacks.SheafOfModules.naiveCotangentComplex_isZero_X.{v, u, max u v w, u}
      J B D h j hj₁ hj₀).eq_of_tgt _ _

end CategoryTheory.Sheaf
