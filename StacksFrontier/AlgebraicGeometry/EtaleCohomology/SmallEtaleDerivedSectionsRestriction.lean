module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSections
public import StacksFrontier.CategoryTheory.Sites.PullbackSectionsComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupHigherVanishing
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.TerminalSectionsRestriction

/-!
# Restriction of derived sections is derived sections of the adjunction unit

Let `c : T ⟶ Z` be a morphism of schemes. The canonical map

`RΓ(Z, M) ⟶ RΓ(T, c⁻¹M)`

on unbounded derived categories of abelian sheaves on the small étale sites,
`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsRestriction`, is built by descending the
restriction of sections along the unit of the derivation of global sections. This file shows that
it is the composite

`RΓ(Z, M) ⟶ RΓ(Z, Rc_* c⁻¹M) ≅ RΓ(T, c⁻¹M)`

of derived sections of the unit of the derived adjunction `c⁻¹ ⊣ Rc_*` with Leray for `c`
(`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsRestriction_app`).

It also identifies the inverse image of abelian sheaves of the small étale sites used here,
Mathlib's sheaf pullback `Stacks.EtaleCohomology.smallEtalePullbackAb`, with the inverse image
`Stacks.EtaleCohomology.etaleAbelianInverseImage`, built as a left Kan extension followed by
sheafification: both are left adjoint to one and the same direct image.

## Main definitions

* `Stacks.EtaleCohomology.smallEtalePullbackAbIsoInverseImage` — the two inverse images of
  abelian étale sheaves are canonically isomorphic.
* `Stacks.EtaleCohomology.smallEtaleDerivedAdjunctionAb` — the adjunction `c⁻¹ ⊣ Rc_*` on
  unbounded derived categories.
* `Stacks.EtaleCohomology.smallEtaleDerivedPushforwardGlobalSectionsIso` — Leray for `c`,
  `RΓ(Z, Rc_* N) ≅ RΓ(T, N)`.

## Main results

* `Stacks.EtaleCohomology.smallEtaleGlobalSectionsRestrictionAb_app` — on abelian sheaves,
  restriction of global sections along `c` is global sections of the adjunction unit followed by
  the identification `Γ(Z, c_*G) = Γ(T, G)`.
* `Stacks.EtaleCohomology.smallEtaleDerivedPushforwardGlobalSectionsIso_hom_fac` — Leray for `c`
  on the image of a complex.
* `Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsRestriction_app` — **the derived
  restriction map is derived sections of the unit of `c⁻¹ ⊣ Rc_*`, followed by Leray for `c`.**

## References

* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {Z T : Scheme.{u}} (c : T ⟶ Z)

/-! ### The two inverse images of abelian étale sheaves -/

/-- **The two inverse images of abelian sheaves of the small étale sites agree.** Mathlib's sheaf
pullback `Stacks.EtaleCohomology.smallEtalePullbackAb` and the left Kan extension followed by
sheafification `Stacks.EtaleCohomology.etaleAbelianInverseImage` are both left adjoint to direct
image along `c`, so they are canonically isomorphic. -/
def smallEtalePullbackAbIsoInverseImage :
    smallEtalePullbackAb c ≅ etaleAbelianInverseImage.{u, 0} c :=
  Adjunction.leftAdjointUniq (smallEtaleAdjunctionAb c)
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} c)

/-- Global sections on `Z` of a direct image along `c : T ⟶ Z` are global sections on `T`: this
is `Stacks.EtaleCohomology.etaleAbelianDirectImageCompGlobalSectionsIso` with coefficients in
`Ab.{u + 1}`, read on the direct image `Stacks.EtaleCohomology.smallEtalePushforwardAb`. -/
def smallEtalePushforwardAbGlobalSectionsIso :
    smallEtalePushforwardAb c ⋙ Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1} ≅
      Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1} :=
  etaleAbelianDirectImageCompGlobalSectionsIso c

/-! ### The derived adjunction and Leray -/

/-- **The adjunction `c⁻¹ ⊣ Rc_*` on unbounded derived categories** of abelian sheaves of the
small étale sites. -/
def smallEtaleDerivedAdjunctionAb :
    smallEtaleDerivedPullbackAb c ⊣ smallEtaleDerivedPushforwardAb c :=
  Stacks.DerivedFunctor.derivedAdjunction (smallEtaleAdjunctionAb c)
    (smallEtaleDerivedPushforwardAb c) (smallEtaleDerivedPushforwardAbUnit c)
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective

/-- The unit of `c⁻¹ ⊣ Rc_*` at the image of a complex `J` is the image of the degreewise unit,
followed by the unit of the derivation of direct image and the identification of the two actions
of inverse image. -/
theorem smallEtaleDerivedAdjunctionAb_unit_app_Qh
    (J : HomotopyCategory (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ)) :
    (smallEtaleDerivedAdjunctionAb c).unit.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map
          ((Adjunction.mapHomotopyCategoryAdjunction (smallEtaleAdjunctionAb c)
            (.up ℤ)).unit.app J) ≫
        (smallEtaleDerivedPushforwardAbUnit c).app
          (((smallEtalePullbackAb c).mapHomotopyCategory (.up ℤ)).obj J) ≫
        (smallEtaleDerivedPushforwardAb c).map
          ((smallEtalePullbackAb c).mapDerivedCategoryFactorsh.inv.app J) := by
  have h := Stacks.DerivedFunctor.derivedAdjunction_unit_app (smallEtaleAdjunctionAb c)
    (smallEtaleDerivedPushforwardAb c) (smallEtaleDerivedPushforwardAbUnit c)
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective J
  rw [← Category.assoc]
  exact (Iso.eq_comp_inv ((smallEtaleDerivedPushforwardAb c).mapIso
    ((smallEtalePullbackAb c).mapDerivedCategoryFactorsh.app J))).2 h

/-- **Leray for a morphism of schemes.** Unbounded derived global sections on `Z` of a derived
direct image along `c : T ⟶ Z` are unbounded derived global sections on `T`:

`RΓ(Z, Rc_* N) ≅ RΓ(T, N)`,

naturally in `N`. -/
def smallEtaleDerivedPushforwardGlobalSectionsIso :
    smallEtaleDerivedPushforwardAb c ⋙ smallEtaleDerivedGlobalSections Z ≅
      smallEtaleDerivedGlobalSections T :=
  Stacks.Cohomology.LerayUnbounded.derivedCompIso (smallEtalePushforwardAb c)
    (Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}) (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1})
    (smallEtalePushforwardAbGlobalSectionsIso c)
    (fun I _ => CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _
      (smallEtaleAdjunctionAb c) I)

/-- Leray for `c` on the image of a complex `J`: the unit of the derivation of global sections on
`Z` at the degreewise direct image, followed by derived sections of the unit of the derivation of
direct image and by Leray, is the degreewise identification `Γ(Z, c_*G) = Γ(T, G)` followed by
the unit of the derivation of global sections on `T`. -/
theorem smallEtaleDerivedPushforwardGlobalSectionsIso_hom_fac
    (J : HomotopyCategory (Sheaf (smallEtaleTopology T) Ab.{u + 1}) (.up ℤ)) :
    (smallEtaleDerivedGlobalSectionsUnit Z).app
        (((smallEtalePushforwardAb c).mapHomotopyCategory (.up ℤ)).obj J) ≫
      (smallEtaleDerivedGlobalSections Z).map ((smallEtaleDerivedPushforwardAbUnit c).app J) ≫
        (smallEtaleDerivedPushforwardGlobalSectionsIso c).hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (smallEtalePushforwardAbGlobalSectionsIso c) (.up ℤ)).hom.app J) ≫
        (smallEtaleDerivedGlobalSectionsUnit T).app J := by
  have := Stacks.Cohomology.LerayUnbounded.isRightDerivedFunctor_derivedCompUnit
    (smallEtalePushforwardAb c) (Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1})
    (fun I _ => CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _
      (smallEtaleAdjunctionAb c) I)
  rw [← Category.assoc]
  exact Functor.rightDerivedNatTrans_app
    (DerivedFunctor.totalRightDerived (smallEtalePushforwardAb c) ⋙
      DerivedFunctor.totalRightDerived (Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}))
    (DerivedFunctor.totalRightDerived (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}))
    (Stacks.Cohomology.LerayUnbounded.derivedCompUnit (smallEtalePushforwardAb c)
      (Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}))
    (Stacks.Cohomology.LerayUnbounded.totalDerivedUnit
      (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}))
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology T) Ab.{u + 1}) (.up ℤ))
    (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso
      (smallEtalePushforwardAbGlobalSectionsIso c) (.up ℤ)) DerivedCategory.Qh).hom J

/-! ### Restriction of sections and the adjunction unit -/

/-- **Restriction of global sections along `c` is global sections of the adjunction unit.** On an
abelian sheaf `F` on `Z_étale`, the restriction `Γ(Z, F) ⟶ Γ(T, c⁻¹F)` is `Γ(Z, -)` of the unit
`F ⟶ c_*c⁻¹F` followed by the identification `Γ(Z, c_*G) = Γ(T, G)`. -/
theorem smallEtaleGlobalSectionsRestrictionAb_app (F : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) :
    (smallEtaleGlobalSectionsRestrictionAb c).app F =
      (Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}).map ((smallEtaleAdjunctionAb c).unit.app F) ≫
        (smallEtalePushforwardAbGlobalSectionsIso c).hom.app
          ((smallEtalePullbackAb c).obj F) := by
  let hZ : IsTerminal (Scheme.Etale.mk (𝟙 Z)) := isTerminalEtaleMkId Z
  let hT : IsTerminal (Scheme.Etale.mk (𝟙 T)) := isTerminalEtaleMkId T
  let hZ' : IsTerminal (⊤_ Z.Etale) := terminalIsTerminal
  let hT' : IsTerminal ((smallEtaleBaseChange c).obj (⊤_ Z.Etale)) :=
    isTerminalSmallEtaleBaseChangeObj c terminalIsTerminal
  let m : Scheme.Etale.mk (𝟙 Z) ⟶ ⊤_ Z.Etale := hZ'.from _
  let ℓ : Scheme.Etale.mk (𝟙 T) ⟶ (smallEtaleBaseChange c).obj (Scheme.Etale.mk (𝟙 Z)) :=
    smallEtaleBaseChangeLift c (Scheme.Etale.mk (𝟙 Z)) c (Category.comp_id c)
  set G := (smallEtalePullbackAb c).obj F
  set η := (smallEtaleAdjunctionAb c).unit.app F
  have hmZ := Sheaf.ΓNatIsoSheafSections_hom_app_map_general (smallEtaleTopology Z) hZ' hZ m F
  have hmT := Sheaf.ΓNatIsoSheafSections_hom_app_map_general (smallEtaleTopology T) hT' hT
    (ℓ ≫ (smallEtaleBaseChange c).map m) G
  have hnat : (Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}).map η ≫
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Z) Ab.{u + 1} hZ').hom.app
        ((smallEtalePushforwardAb c).obj G) =
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Z) Ab.{u + 1} hZ').hom.app F ≫
        η.hom.app (op (⊤_ Z.Etale)) :=
    (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Z) Ab.{u + 1} hZ').hom.naturality η
  have hunit : F.obj.map m.op ≫ η.hom.app (op (Scheme.Etale.mk (𝟙 Z))) =
      η.hom.app (op (⊤_ Z.Etale)) ≫ G.obj.map ((smallEtaleBaseChange c).map m).op :=
    η.hom.naturality m.op
  have hT'' : G.obj.map ((smallEtaleBaseChange c).map m).op ≫ G.obj.map ℓ.op ≫
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1} hT).inv.app G =
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1} hT').inv.app G := by
    rw [← cancel_epi ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1} hT').hom.app G),
      Iso.hom_inv_id_app, ← Functor.map_comp_assoc, ← op_comp, reassoc_of% hmT,
      Iso.hom_inv_id_app]
  calc (smallEtaleGlobalSectionsRestrictionAb c).app F
      = (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Z) Ab.{u + 1} hZ).hom.app F ≫
          η.hom.app (op (Scheme.Etale.mk (𝟙 Z))) ≫ G.obj.map ℓ.op ≫
            (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1} hT).inv.app G := rfl
    _ = (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Z) Ab.{u + 1} hZ').hom.app F ≫
          (F.obj.map m.op ≫ η.hom.app (op (Scheme.Etale.mk (𝟙 Z)))) ≫ G.obj.map ℓ.op ≫
            (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1} hT).inv.app G := by
        rw [← hmZ, Category.assoc, Category.assoc]
    _ = (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Z) Ab.{u + 1} hZ').hom.app F ≫
          η.hom.app (op (⊤_ Z.Etale)) ≫ G.obj.map ((smallEtaleBaseChange c).map m).op ≫
            G.obj.map ℓ.op ≫
              (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1} hT).inv.app G := by
        rw [hunit]
        exact congrArg (_ ≫ ·) (Category.assoc _ _ _)
    _ = (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Z) Ab.{u + 1} hZ').hom.app F ≫
          η.hom.app (op (⊤_ Z.Etale)) ≫
            (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1} hT').inv.app G :=
        congrArg (fun x => (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Z) Ab.{u + 1}
          hZ').hom.app F ≫ η.hom.app (op (⊤_ Z.Etale)) ≫ x) hT''
    _ = ((Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}).map η ≫
          (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Z) Ab.{u + 1} hZ').hom.app
            ((smallEtalePushforwardAb c).obj G)) ≫
            (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1} hT').inv.app G :=
        ((congrArg (· ≫ (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1}
          hT').inv.app G) hnat).trans (Category.assoc _ _ _)).symm
    _ = _ := Category.assoc _ _ _

/-- The restriction of sections along `c`, applied degreewise to complexes, is the degreewise
global sections of the unit of the adjunction on homotopy categories, followed by the degreewise
identification `Γ(Z, c_*G) = Γ(T, G)`. -/
theorem mapHomotopyCategoryOfComp_smallEtaleGlobalSectionsRestrictionAb_app
    (J : HomotopyCategory (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ)) :
    (Stacks.DerivedFunctor.mapHomotopyCategoryOfComp (Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1})
        (smallEtalePullbackAb c) (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1})
        (smallEtaleGlobalSectionsRestrictionAb c)).app J =
      ((Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}).mapHomotopyCategory (.up ℤ)).map
          ((Adjunction.mapHomotopyCategoryAdjunction (smallEtaleAdjunctionAb c)
            (.up ℤ)).unit.app J) ≫
        (Functor.mapHomotopyCategoryCompIso
          (smallEtalePushforwardAbGlobalSectionsIso c) (.up ℤ)).hom.app
            (((smallEtalePullbackAb c).mapHomotopyCategory (.up ℤ)).obj J) := by
  rw [Stacks.DerivedFunctor.mapHomotopyCategoryOfComp_app]
  change _ = ((Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}).mapHomotopyCategory (.up ℤ)).map
      ((HomotopyCategory.quotient _ _).map
        (((smallEtaleAdjunctionAb c).mapHomologicalComplexAdjunction
          (ComplexShape.up ℤ)).unit.app J.as)) ≫
    (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex
      (smallEtalePushforwardAbGlobalSectionsIso c).hom (ComplexShape.up ℤ)).app
        (((smallEtalePullbackAb c).mapHomologicalComplex (ComplexShape.up ℤ)).obj J.as))
  rw [Functor.mapHomotopyCategory_map]
  refine (congrArg (HomotopyCategory.quotient _ _).map ?_).trans
    ((HomotopyCategory.quotient _ _).map_comp _ _)
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  simp only [NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f]
  exact smallEtaleGlobalSectionsRestrictionAb_app c (J.as.X n)

/-! ### The derived restriction map -/

/-- **The derived restriction map is derived sections of the adjunction unit, followed by
Leray.** For a morphism of schemes `c : T ⟶ Z` and an object `M` of `D(Z_étale)`, the canonical
map `RΓ(Z, M) ⟶ RΓ(T, c⁻¹M)` is the composite

`RΓ(Z, M) ⟶ RΓ(Z, Rc_* c⁻¹M) ≅ RΓ(T, c⁻¹M)`

of `RΓ(Z, -)` applied to the unit of `c⁻¹ ⊣ Rc_*` with Leray for `c`. -/
theorem smallEtaleDerivedGlobalSectionsRestriction_app (M : smallEtaleDerivedCategory Z) :
    (smallEtaleDerivedGlobalSectionsRestriction c).app M =
      (smallEtaleDerivedGlobalSections Z).map ((smallEtaleDerivedAdjunctionAb c).unit.app M) ≫
        (smallEtaleDerivedPushforwardGlobalSectionsIso c).hom.app
          ((smallEtaleDerivedPullbackAb c).obj M) := by
  let γ : smallEtaleDerivedGlobalSections Z ⟶
      smallEtaleDerivedPullbackAb c ⋙ smallEtaleDerivedGlobalSections T :=
    (Functor.leftUnitor _).inv ≫
      Functor.whiskerRight (smallEtaleDerivedAdjunctionAb c).unit
        (smallEtaleDerivedGlobalSections Z) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (smallEtaleDerivedPullbackAb c)
        (smallEtaleDerivedPushforwardGlobalSectionsIso c).hom
  have hγ : smallEtaleDerivedGlobalSectionsRestriction c = γ := by
    refine Functor.rightDerived_ext (smallEtaleDerivedGlobalSections Z)
      (smallEtaleDerivedGlobalSectionsUnit Z)
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ)) _ _ _ ?_
    ext J
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    rw [smallEtaleDerivedGlobalSectionsRestriction_fac_app,
      mapHomotopyCategoryOfComp_smallEtaleGlobalSectionsRestrictionAb_app]
    simp only [γ, NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp]
    rw [smallEtaleDerivedAdjunctionAb_unit_app_Qh]
    have hnatQ := ((smallEtaleDerivedGlobalSectionsUnit Z).naturality
      ((Adjunction.mapHomotopyCategoryAdjunction (smallEtaleAdjunctionAb c) (.up ℤ)).unit.app J))
    have hL := (smallEtaleDerivedPushforwardGlobalSectionsIso c).hom.naturality
      ((smallEtalePullbackAb c).mapDerivedCategoryFactorsh.inv.app J)
    have hfac := smallEtaleDerivedPushforwardGlobalSectionsIso_hom_fac c
      (((smallEtalePullbackAb c).mapHomotopyCategory (.up ℤ)).obj J)
    simp only [Functor.comp_obj, Functor.comp_map] at hnatQ hL hfac
    simp only [Functor.map_comp, Category.assoc]
    rw [hL, ← reassoc_of% hnatQ, reassoc_of% hfac]
  rw [hγ]
  simp [γ]

end Stacks.EtaleCohomology

end
