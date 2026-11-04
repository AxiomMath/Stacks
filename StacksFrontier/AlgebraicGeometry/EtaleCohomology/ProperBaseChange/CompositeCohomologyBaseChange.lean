module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CompositeMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.InjectiveVanishingBaseChange

/-!
# Cohomology commuting with base change is closed under composition

[Stacks, Tag 0A4D](https://stacks.math.columbia.edu/tag/0A4D): if `f : X ⟶ Y` and `g : Y ⟶ Z`
are proper and cohomology commutes with base change for `f` and for `g`, then it does so for
`g ∘ f`.

The proof uses neither [Stacks, Tag 0A3U] nor the injectivity of `f_* I` for an injective sheaf
`I` of `ℤ/ℓℤ`-modules, unlike the source's argument through condition (2) of [Stacks, Tag 0A4B].

## Main results

* `Stacks.EtaleCohomology.torsionSheafProperty_of_nsmul_id_eq_zero` — a sheaf killed by a
  positive integer is torsion.
* `Stacks.EtaleCohomology.etaleAbelianDerivedDirectImageSingleIsoOfInjective` — for the underlying
  abelian sheaf `G` of an injective sheaf of `ℤ/ℓℤ`-modules, `Rf_*(G[0]) ≅ (f_* G)[0]`.
* `Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_comp` — cohomology commuting with base
  change is stable under composition of proper morphisms ([Stacks, Tag 0A4D]).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.ZModSheaf

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

/-- A sheaf killed by a positive integer is torsion. -/
public theorem torsionSheafProperty_of_nsmul_id_eq_zero {X : Scheme.{u}}
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) (hn : 0 < n)
    (hA : n • 𝟙 A = 0) : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology A := by
  intro U x
  refine ⟨⊤, X.smallEtaleTopology.top_mem U, fun V g _ ↦ ⟨n, hn, ?_⟩⟩
  have h := (zsmul_id_eq_zero_iff A (n : ℤ)).1 (by rw [natCast_zsmul]; exact hA)
    (Opposite.op V) (A.obj.map g.op x)
  rwa [natCast_zsmul] at h

/-- **`(f_* G)[0] ≅ Rf_*(G[0])`** for the underlying abelian sheaf `G` of an injective sheaf of
`ℤ/ℓℤ`-modules. -/
public def etaleAbelianDerivedDirectImageSingleIsoOfInjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ℓ : ℕ) (I : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ))
    [Injective I] :
    (DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
        ((etaleAbelianDirectImage.{u, 0} f).obj ((SheafOfModules.toSheaf _).obj I)) ≅
      (etaleAbelianDerivedDirectImage.{u, 0} f).obj
        ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
          ((SheafOfModules.toSheaf _).obj I)) := by
  set G := (SheafOfModules.toSheaf _).obj I
  have hG₁ : (etaleAbelianDirectImage.{u, 0} f).rightAcyclic G :=
    (rightAcyclic_etaleAbelianDirectImage_iff.{u, 0} f G).2
      (isZero_homology_etaleAbelianDerivedDirectImage_single_toSheaf_of_injective.{u, 0} f ℓ I)
  have hK : CochainComplex.plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      ((CochainComplex.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
        G) :=
    ⟨0, inferInstance⟩
  have hac : ∀ n : ℤ, (etaleAbelianDirectImage.{u, 0} f).rightAcyclic
      (((CochainComplex.singleFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj G).X n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · exact (etaleAbelianDirectImage.{u, 0} f).rightAcyclic.prop_of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).symm hG₁
    · exact Stacks.RightAcyclicProduct.rightAcyclic_of_isZero _
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 G n hn)
  have hu := isIso_etaleAbelianDerivedDirectImageUnit_app_of_plus_of_rightAcyclic.{u, 0} f _ hK hac
  exact (DerivedCategory.singleFunctorIsoCompQ _ 0).app _ ≪≫
    ((DerivedCategory.quotientCompQhIso _).app _).symm ≪≫
    DerivedCategory.Qh.mapIso ((HomotopyCategory.quotient
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (etaleAbelianDirectImage.{u, 0} f)
          (ComplexShape.up ℤ) 0).app G).symm) ≪≫
    @asIso _ _ _ _ ((etaleAbelianDerivedDirectImageUnit.{u, 0} f).app
      ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
        (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj G))) hu ≪≫
    (etaleAbelianDerivedDirectImage.{u, 0} f).mapIso
      ((DerivedCategory.quotientCompQhIso _).app _ ≪≫
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app G).symm)

/-- The base change map of `g ∘ f` at the underlying sheaf of an injective `ℤ/ℓℤ`-module is
invertible when cohomology commutes with base change for `f` and `g`. -/
theorem isIso_etaleAbelianSheafDerivedBaseChange_comp_of_injective {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : CohomologyCommutesWithBaseChange.{u, 0} f)
    (hg : CohomologyCommutesWithBaseChange.{u, 0} g) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (I : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ)) [Injective I]
    {X' Z' : Scheme.{u}} (c : Z' ⟶ Z) (e : X' ⟶ X) (q : X' ⟶ Z')
    (sq : IsPullback e q (f ≫ g) c) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, 0} (f ≫ g) c e q sq.w
      ((SheafOfModules.toSheaf _).obj I)) := by
  set G := (SheafOfModules.toSheaf _).obj I
  set d := pullback.fst g c
  set g' := pullback.snd g c
  have hw : (e ≫ f) ≫ g = q ≫ c := by rw [Category.assoc]; exact sq.w
  set f' : X' ⟶ pullback g c := pullback.lift (e ≫ f) q hw
  have hq : q = f' ≫ g' := (pullback.lift_snd _ _ _).symm
  have hsq₂ : e ≫ f = f' ≫ d := (pullback.lift_fst _ _ _).symm
  have lower : IsPullback d g' g c := IsPullback.of_hasPullback g c
  have upper : IsPullback e f' f d := IsPullback.of_bot (hq ▸ sq) hsq₂ lower
  set K :=
    (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj G
  have D := etaleAbelianDerivedBaseChange_compDirectImage_app.{u, 0} f g (f ≫ g) rfl c d g' e f' q
    hq pullback.condition hsq₂ sq.w K
  have hG : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G :=
    torsionSheafProperty_toSheaf_zmod.{u, 0} hℓ I
  have h₂ : IsIso ((etaleAbelianDerivedBaseChange.{u, 0} f d e f' hsq₂).app K) :=
    hf d e f' upper G hG
  have hfG : Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology
      ((etaleAbelianDirectImage.{u, 0} f).obj G) := by
    refine torsionSheafProperty_of_nsmul_id_eq_zero _ ℓ hℓ ?_
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, nsmul_id_toSheaf_eq_zero.{u, 0} ℓ I,
      Functor.map_zero]
  have h₁' : IsIso ((etaleAbelianDerivedBaseChange.{u, 0} g c d g' pullback.condition).app
      ((DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
        ((etaleAbelianDirectImage.{u, 0} f).obj G))) :=
    hg c d g' lower _ hfG
  have h₁ : IsIso ((etaleAbelianDerivedBaseChange.{u, 0} g c d g' pullback.condition).app
      ((etaleAbelianDerivedDirectImage.{u, 0} f).obj K)) :=
    (NatTrans.isIso_app_iff_of_iso _
      (etaleAbelianDerivedDirectImageSingleIsoOfInjective f ℓ I)).1 h₁'
  rw [etaleAbelianSheafDerivedBaseChange, D]
  infer_instance

/-- **[Stacks, Tag 0A4D].** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be proper morphisms of schemes. If
cohomology commutes with base change for `f` and for `g`, then it does so for `g ∘ f`. -/
public theorem cohomologyCommutesWithBaseChange_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) [IsProper f] [IsProper g] (hf : CohomologyCommutesWithBaseChange.{u, 0} f)
    (hg : CohomologyCommutesWithBaseChange.{u, 0} g) :
    CohomologyCommutesWithBaseChange.{u, 0} (f ≫ g) :=
  cohomologyCommutesWithBaseChange_of_isIso_injective fun ℓ hℓ I hI _ _ c e q sq ↦ by
    have : Injective I := hI
    exact isIso_etaleAbelianSheafDerivedBaseChange_comp_of_injective f g hf hg ℓ hℓ.pos I c e q sq

end Stacks.EtaleCohomology

end
