module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedFibreSectionsIdentities
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLerayGlobalSectionsAb
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.CospecializationMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedSectionsRestrictionComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SpecializationMapAndFibres
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cospecialization map and the specialization map

Let `f : X ⟶ S` be a morphism of schemes, `s` a geometric point of `S`, `t` a geometric point of
`Spec 𝒪^{sh}_{S,s}`, `Y = X ×_S Spec 𝒪^{sh}_{S,s}`, and

`X_t ⟶ Y ⟵ X_s`

the morphisms `h` and `i` of Section 0GJT, with `β_{K,s,t} : K|_Y ⟶ Rh_*(K|_{X_t})` the adjunction
unit (`AlgebraicGeometry.cospecializationUnit`). When `i⁻¹β_{K,s,t}` is invertible the source
defines the cospecialization map `cosp : RΓ(X_t, K) ⟶ RΓ(X_s, K)` as `RΓ(X_t, K) = RΓ(Y, Rh_* -)`,
followed by pullback along `i` and the inverse of `i⁻¹β_{K,s,t}`. This file constructs it and
proves the commutativity of the square of Stacks 0GJV,

```
(Rf_*K)_s ----------> RΓ(X_s, K)
   | sp                    ^ cosp
   v                       |
(Rf_*K)_t ----------> RΓ(X_t, K)
```

whose horizontal arrows are the base change maps of Stacks 0GIX, for every proof that
`i⁻¹β_{K,s,t}` is invertible.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleDerivedPullbackPushforwardAbUnit` — the unit
  `M ⟶ Rh_*h⁻¹M` of the derived adjunction along `h`, on the unbounded derived category.
* `AlgebraicGeometry.cospecializationMapOfIsIso` — the cospecialization map of the source, with
  source the cohomology of the fibre `Y ×_{Spec 𝒪^{sh}_{S,s}} t`.
* `AlgebraicGeometry.cospecializationMapGeometricFibre` — the same map with source the cohomology
  of the geometric fibre `X ×_S t`, read through the canonical isomorphism of the two models of
  `X_t` (`AlgebraicGeometry.cospecializationFibreIso`).

## Main results

* `Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsRestriction_eq_pullbackPushforwardUnit`
  — derived restriction of global sections along `h` is `RΓ` of the derived adjunction unit,
  followed by `RΓ(Y, Rh_* -) ≅ RΓ(T, -)`.
* `AlgebraicGeometry.cospecializationRestriction_comp_cospecializationMapOfIsIso` — the core of
  the proof of Stacks 0GJV: pulling back cohomology along `h` and applying `cosp` is the map of
  Stacks 0GIX to the closed fibre.
* `AlgebraicGeometry.specializationStalk_comp_baseChange_comp_cospecializationMapGeometricFibre`
  — the square of Stacks 0GJV, for every invertibility of `i⁻¹β_{K,s,t}`.

## Implementation notes

The source proves Stacks 0GJV for `f` quasi-compact and quasi-separated, using Theorem 03Q9 to
identify `(Rf_*K)_s` with `RΓ(X ×_S Spec 𝒪^{sh}_{S,s}, K)`. The argument here routes the
specialization map through Stacks 0GJ9 instead
(`derivedPushforwardStalkToStrictHenselizationSections_comp_sectionsSpecialization`), which holds
with no hypothesis on `f`, so the square commutes for an arbitrary morphism of schemes; the
hypotheses of the source enter only through the existence of `cosp`, that is through the
invertibility of `i⁻¹β_{K,s,t}` (Stacks 0GJU).

## References

* [Stacks Project, Tag 0GJT](https://stacks.math.columbia.edu/tag/0GJT)
* [Stacks Project, Tag 0GJU](https://stacks.math.columbia.edu/tag/0GJU)
* [Stacks Project, Tag 0GJV](https://stacks.math.columbia.edu/tag/0GJV)
* [Stacks Project, Tag 0GJ9](https://stacks.math.columbia.edu/tag/0GJ9)
* [Stacks Project, Tag 0GIX](https://stacks.math.columbia.edu/tag/0GIX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Underived

/-- Cancelling an isomorphism followed by its inverse inside a composite. -/
private theorem comp_inv_hom_comp {C : Type*} [Category C] {P Q R R' W : C} (a : P ⟶ Q)
    (b : Q ⟶ R) (e : R' ≅ R) (c : R ⟶ W) : a ≫ b ≫ e.inv ≫ e.hom ≫ c = a ≫ b ≫ c := by
  simp

variable {T Y : Scheme.{u}} (h : T ⟶ Y)

/-- Restriction of global sections along `h : T ⟶ Y` is global sections of the adjunction unit
`F ⟶ h_*h⁻¹F`, read through `Γ(Y, h_* -) ≅ Γ(T, -)`. -/
theorem smallEtaleGlobalSectionsRestrictionAb_eq_unit :
    smallEtaleGlobalSectionsRestrictionAb h =
      Functor.whiskerRight (smallEtaleAdjunctionAb h).unit
          (Sheaf.Γ (smallEtaleTopology Y) Ab.{u + 1}) ≫
        Functor.whiskerLeft (smallEtalePullbackAb h) (smallEtalePushforwardGammaIsoAb h).hom := by
  ext F : 2
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  have h2 := (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Y) Ab.{u + 1}
    (isTerminalEtaleMkId Y)).hom.naturality ((smallEtaleAdjunctionAb h).unit.app F)
  have hu : (Sheaf.Γ (smallEtaleTopology Y) Ab.{u + 1}).map
      ((smallEtaleAdjunctionAb h).unit.app F) =
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Y) Ab.{u + 1}
          (isTerminalEtaleMkId Y)).hom.app F ≫
        ((sheafSections (smallEtaleTopology Y) Ab.{u + 1}).obj
          (op (Scheme.Etale.mk (𝟙 Y)))).map ((smallEtaleAdjunctionAb h).unit.app F) ≫
        (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Y) Ab.{u + 1}
          (isTerminalEtaleMkId Y)).inv.app
            ((smallEtalePushforwardAb h).obj ((smallEtalePullbackAb h).obj F)) := by
    rw [← Category.assoc]
    exact (Iso.eq_comp_inv ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Y) Ab.{u + 1}
      (isTerminalEtaleMkId Y)).app _)).2 h2
  have hp := (Iso.inv_comp_eq ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Y) Ab.{u + 1}
      (isTerminalEtaleMkId Y)).app _)).1
    (smallEtalePushforwardGammaIsoAb_hom_app h ((smallEtalePullbackAb h).obj F))
  rw [hu, hp]
  simp only [Category.assoc, Iso.app_hom]
  refine Eq.trans ?_ (comp_inv_hom_comp _ _ ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Y)
    Ab.{u + 1} (isTerminalEtaleMkId Y)).app
      ((smallEtalePushforwardAb h).obj ((smallEtalePullbackAb h).obj F))) _).symm
  rfl

end Underived

/-- A functor carries a composite of two morphisms to the composite of their images, at
variables. -/
private theorem map_comp_two {C D : Type*} [Category C] [Category D] (Fn : C ⥤ D) {A B₁ B₂ : C}
    (a : A ⟶ B₁) (b : B₁ ⟶ B₂) {d : A ⟶ B₂} (h : a ≫ b = d) : Fn.map a ≫ Fn.map b = Fn.map d := by
  rw [← Fn.map_comp, h]

/-- The rearrangement behind
`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsRestriction_eq_pullbackPushforwardUnit`,
for bare morphisms. -/
private theorem l1_rearrange {C : Type*} [Category C] {A A₁ B B₁ B₂ B₃ E E₀ E₁ : C}
    (uY : A ⟶ B) (rε : B ⟶ B₁) (rη : B₁ ⟶ B₂) (rfi : B₂ ⟶ B₃) (L : B₃ ⟶ E)
    (qε : A ⟶ A₁) (uY' : A₁ ⟶ B₁) (L' : B₂ ⟶ E₁) (rTfi : E₁ ⟶ E) (qc : A₁ ⟶ E₀)
    (uT : E₀ ⟶ E₁) (qm : A ⟶ E₀)
    (h1 : uY ≫ rε = qε ≫ uY') (h2 : rfi ≫ L = L' ≫ rTfi) (h3 : uY' ≫ rη ≫ L' = qc ≫ uT)
    (h4 : qε ≫ qc = qm) :
    qm ≫ uT ≫ rTfi = uY ≫ (rε ≫ rη ≫ rfi) ≫ L := by
  have e1 : uY ≫ (rε ≫ rη ≫ rfi) ≫ L = (uY ≫ rε) ≫ rη ≫ (rfi ≫ L) := by
    simp only [Category.assoc]
  rw [e1, h1, h2]
  have e2 : (qε ≫ uY') ≫ rη ≫ L' ≫ rTfi = qε ≫ (uY' ≫ rη ≫ L') ≫ rTfi := by
    simp only [Category.assoc]
  rw [e2, h3, ← h4]
  simp only [Category.assoc]

/-- The rearrangement behind
`Stacks.EtaleCohomology.smallEtaleDerivedPushforwardAbPullbackUnit_eq_pullbackPushforwardUnit`,
for bare morphisms. -/
private theorem l2_rearrange {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {A A' A₁ A₂ : D} {P P₀ P₁ P₂ Q : C}
    (fic : A ⟶ A') (ηYc : A' ⟶ R.obj P) (lift : P ⟶ Q) (ηY' : A ⟶ R.obj P₀) (hfic : P₀ ⟶ P)
    (qε : A ⟶ A₁) (ηp : A₁ ⟶ R.obj P₁) (fih : P₁ ⟶ P₀) (hfhc : P ⟶ P₀) (fhh : P₀ ⟶ P₁)
    (qχ : P₁ ⟶ P₂) (fihc : P₂ ⟶ Q) (qhχ : A₁ ⟶ A₂) (ηp' : A₂ ⟶ R.obj P₂) (qm : A ⟶ A₂)
    (ha : fic ≫ ηYc = ηY' ≫ R.map hfic) (hb : ηY' = qε ≫ ηp ≫ R.map fih)
    (hc : lift = hfhc ≫ fhh ≫ qχ ≫ fihc) (hd : ηp ≫ R.map qχ = qhχ ≫ ηp')
    (he : qε ≫ qhχ = qm) (h₁ : hfic ≫ hfhc = 𝟙 P₀) (h₂ : fih ≫ fhh = 𝟙 P₁) :
    fic ≫ ηYc ≫ R.map lift = qm ≫ ηp' ≫ R.map fihc := by
  have e : fih ≫ hfic ≫ hfhc ≫ fhh ≫ qχ ≫ fihc = qχ ≫ fihc := by
    rw [reassoc_of% h₁, reassoc_of% h₂]
  rw [← Category.assoc, ha, hb, hc, ← he]
  simp only [Category.assoc, ← R.map_comp]
  rw [e, R.map_comp, reassoc_of% hd]

/-- Absorbing identities on both sides of a morphism, at variables, so that it applies by `exact`
across definitionally equal spellings of the two objects. -/
private theorem id_comp_comp_id {C : Type*} [Category C] {A B : C} (f : A ⟶ B) :
    𝟙 A ≫ f ≫ 𝟙 B = f := by
  simp

section HomotopyId

variable (V : Type*) [Category* V] [Preadditive V] {ι : Type*} (c : ComplexShape ι)

/-- The functor induced on homotopy categories by the identity functor is the identity. -/
def mapHomotopyCategoryIdIso : (𝟭 V).mapHomotopyCategory c ≅ 𝟭 (HomotopyCategory V c) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    rintro ⟨K⟩ ⟨L⟩ ⟨f : K ⟶ L⟩
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Each component of the hom of `mapHomotopyCategoryIdIso` is the identity. -/
@[simp]
theorem mapHomotopyCategoryIdIso_hom_app (K : HomotopyCategory V c) :
    (mapHomotopyCategoryIdIso V c).hom.app K = 𝟙 _ :=
  rfl

/-- Each component of the inverse of `mapHomotopyCategoryIdIso` is the identity. -/
@[simp]
theorem mapHomotopyCategoryIdIso_inv_app (K : HomotopyCategory V c) :
    (mapHomotopyCategoryIdIso V c).inv.app K = 𝟙 _ :=
  rfl

end HomotopyId

section DerivedUnit

variable {T Y : Scheme.{u}} (h : T ⟶ Y)

/-- The unit `J ⟶ h_*h⁻¹J` of the inverse-image/direct-image adjunction along `h`, applied
degreewise to complexes of abelian sheaves, on the homotopy category. -/
def homotopyCategoryPullbackPushforwardAbUnit :
    𝟭 (HomotopyCategory (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (.up ℤ)) ⟶
      (smallEtalePullbackAb h).mapHomotopyCategory (.up ℤ) ⋙
        (smallEtalePushforwardAb h).mapHomotopyCategory (.up ℤ) :=
  (mapHomotopyCategoryIdIso _ _).inv ≫
    NatTrans.mapHomotopyCategory (smallEtaleAdjunctionAb h).unit (.up ℤ) ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).inv

/-- On a complex, the degreewise adjunction unit is the quotient of the adjunction unit applied
in each degree. -/
theorem homotopyCategoryPullbackPushforwardAbUnit_app
    (J : HomotopyCategory (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (.up ℤ)) :
    (homotopyCategoryPullbackPushforwardAbUnit h).app J =
      (HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex (smallEtaleAdjunctionAb h).unit (.up ℤ)).app J.as) := by
  have hinv : (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (smallEtalePullbackAb h ⋙ smallEtalePushforwardAb h)) (.up ℤ)).inv.app
        J = 𝟙 _ :=
    Iso.inv_ext (f := (Functor.mapHomotopyCategoryCompIso _ _).app J) (by
      rw [Iso.app_hom, Stacks.DerivedFunctor.mapHomotopyCategoryCompIso_refl_hom_app]
      exact Category.comp_id _)
  rw [homotopyCategoryPullbackPushforwardAbUnit, NatTrans.comp_app, NatTrans.comp_app,
    mapHomotopyCategoryIdIso_inv_app, hinv]
  exact (id_comp_comp_id _).trans (NatTrans.mapHomotopyCategory_app _ _ _)

/-- Global sections of the degreewise adjunction unit, read through `Γ(Y, h_* -) ≅ Γ(T, -)`, are
the degreewise restriction of global sections along `h`. -/
theorem homotopyCategoryPullbackPushforwardAbUnit_globalSections
    (J : HomotopyCategory (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (.up ℤ)) :
    ((Sheaf.Γ (smallEtaleTopology Y) Ab.{u + 1}).mapHomotopyCategory (.up ℤ)).map
          ((homotopyCategoryPullbackPushforwardAbUnit h).app J) ≫
        (Functor.mapHomotopyCategoryCompIso (smallEtalePushforwardGammaIsoAb h) (.up ℤ)).hom.app
          (((smallEtalePullbackAb h).mapHomotopyCategory (.up ℤ)).obj J) =
      (Stacks.DerivedFunctor.mapHomotopyCategoryOfComp (Sheaf.Γ (smallEtaleTopology Y) Ab.{u + 1})
        (smallEtalePullbackAb h) (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1})
        (smallEtaleGlobalSectionsRestrictionAb h)).app J := by
  rw [homotopyCategoryPullbackPushforwardAbUnit_app,
    Stacks.DerivedFunctor.mapHomotopyCategoryOfComp_app,
    Stacks.DerivedFunctor.mapHomotopyCategoryCompIso_hom_app,
    smallEtaleGlobalSectionsRestrictionAb_eq_unit]
  exact map_comp_two (HomotopyCategory.quotient _ _) _ _
    (HomologicalComplex.hom_ext _ _ fun _ => rfl)

/-- The comparison on the homotopy category of `Y` from which the derived unit descends. -/
def derivedPullbackPushforwardAbUnitAux :
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙
      (smallEtaleDerivedPullbackAb h ⋙ smallEtaleDerivedPushforwardAb h) :=
  Functor.whiskerRight (homotopyCategoryPullbackPushforwardAbUnit h) DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((smallEtalePullbackAb h).mapHomotopyCategory (.up ℤ))
      (smallEtaleDerivedPushforwardAbUnit h) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (smallEtalePullbackAb h).mapDerivedCategoryFactorsh.inv
      (smallEtaleDerivedPushforwardAb h) ≫
    (Functor.associator _ _ _).hom

/-- On a complex, the comparison from which the derived unit descends is the degreewise unit,
followed by the unit of the derivation of direct image and the identification of the two
actions of inverse image. -/
theorem derivedPullbackPushforwardAbUnitAux_app
    (J : HomotopyCategory (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (.up ℤ)) :
    (derivedPullbackPushforwardAbUnitAux h).app J =
      DerivedCategory.Qh.map ((homotopyCategoryPullbackPushforwardAbUnit h).app J) ≫
        (smallEtaleDerivedPushforwardAbUnit h).app
          (((smallEtalePullbackAb h).mapHomotopyCategory (.up ℤ)).obj J) ≫
        (smallEtaleDerivedPushforwardAb h).map
          ((smallEtalePullbackAb h).mapDerivedCategoryFactorsh.inv.app J) := by
  simp [derivedPullbackPushforwardAbUnitAux]

/-- The identity functor of the derived category of abelian sheaves on the small étale site of `Y`
is a right derived functor of the localization functor `DerivedCategory.Qh` with respect to
quasi-isomorphisms. -/
instance isRightDerivedFunctor_id_smallEtale (Y : Scheme.{u}) :
    (𝟭 (smallEtaleDerivedCategory Y)).IsRightDerivedFunctor
      (Functor.rightUnitor (DerivedCategory.Qh (C := Sheaf (smallEtaleTopology Y) Ab.{u + 1}))).inv
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _ _

/-- The unit `M ⟶ Rh_*h⁻¹M` of the adjunction between derived inverse image and derived direct
image along `h : T ⟶ Y`, on the unbounded derived category of abelian sheaves on the small
étale site of `Y`. -/
def smallEtaleDerivedPullbackPushforwardAbUnit :
    𝟭 (smallEtaleDerivedCategory Y) ⟶
      smallEtaleDerivedPullbackAb h ⋙ smallEtaleDerivedPushforwardAb h :=
  (𝟭 (smallEtaleDerivedCategory Y)).rightDerivedDesc (Functor.rightUnitor _).inv
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (.up ℤ)) _
    (derivedPullbackPushforwardAbUnitAux h)

/-- On the image of a complex `J`, the derived adjunction unit along `h` is
`Stacks.EtaleCohomology.derivedPullbackPushforwardAbUnitAux` at `J`. -/
theorem smallEtaleDerivedPullbackPushforwardAbUnit_app_Qh
    (J : HomotopyCategory (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (.up ℤ)) :
    (smallEtaleDerivedPullbackPushforwardAbUnit h).app (DerivedCategory.Qh.obj J) =
      (derivedPullbackPushforwardAbUnitAux h).app J := by
  simpa [smallEtaleDerivedPullbackPushforwardAbUnit] using
    Functor.rightDerived_fac_app (𝟭 (smallEtaleDerivedCategory Y))
    (Functor.rightUnitor _).inv
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (.up ℤ)) _
    (derivedPullbackPushforwardAbUnitAux h) J

/-- **Restriction of derived global sections along `h` is derived global sections of the derived
adjunction unit.** For a morphism of schemes `h : T ⟶ Y` the derived restriction
`RΓ(Y, M) ⟶ RΓ(T, h⁻¹M)` is `RΓ(Y, -)` of the unit `M ⟶ Rh_*h⁻¹M`, followed by
`RΓ(Y, Rh_* -) ≅ RΓ(T, -)`, naturally in `M` on the whole unbounded derived category. -/
theorem smallEtaleDerivedGlobalSectionsRestriction_eq_pullbackPushforwardUnit :
    smallEtaleDerivedGlobalSectionsRestriction h =
      (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (smallEtaleDerivedPullbackPushforwardAbUnit h)
          (smallEtaleDerivedGlobalSections Y) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (smallEtaleDerivedPullbackAb h)
          (smallEtaleDerivedGlobalSectionsPushforwardIsoAb h).hom := by
  refine Functor.rightDerived_ext (smallEtaleDerivedGlobalSections Y)
    (smallEtaleDerivedGlobalSectionsUnit Y)
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (.up ℤ)) _ _ _ ?_
  refine NatTrans.ext (funext fun J => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.leftUnitor_inv_app, Category.id_comp]
  rw [smallEtaleDerivedGlobalSectionsRestriction_fac_app,
    smallEtaleDerivedPullbackPushforwardAbUnit_app_Qh, derivedPullbackPushforwardAbUnitAux_app,
    Functor.map_comp, Functor.map_comp]
  exact l1_rearrange _ _ _ _ _ _ _ _ _ _ _ _
    ((smallEtaleDerivedGlobalSectionsUnit Y).naturality
      ((homotopyCategoryPullbackPushforwardAbUnit h).app J)).symm
    ((smallEtaleDerivedGlobalSectionsPushforwardIsoAb h).hom.naturality
      ((smallEtalePullbackAb h).mapDerivedCategoryFactorsh.inv.app J))
    (smallEtaleDerivedGlobalSectionsPushforwardIsoAb_fac_app h
      (((smallEtalePullbackAb h).mapHomotopyCategory (.up ℤ)).obj J))
    (map_comp_two DerivedCategory.Qh _ _
      (homotopyCategoryPullbackPushforwardAbUnit_globalSections h J))

end DerivedUnit

section RestrictionComp

variable {Y : Scheme.{u}}

variable {T X' Y' : Scheme.{u}} (a : Y' ⟶ Y) (b : X' ⟶ Y') (e : T ⟶ X') (h : T ⟶ Y)

/-- The identification `h⁻¹N ≅ e⁻¹b⁻¹a⁻¹N` attached to a factorization `e ≫ b ≫ a = h`: the
transport along the factorization followed by the inverses of the two composition
isomorphisms. -/
def smallEtaleDerivedPullbackThreeCompIso (hh : e ≫ b ≫ a = h) :
    smallEtaleDerivedPullbackAb h ≅
      (smallEtaleDerivedPullbackAb a ⋙ smallEtaleDerivedPullbackAb b) ⋙
        smallEtaleDerivedPullbackAb e :=
  eqToIso (congrArg smallEtaleDerivedPullbackAb hh.symm) ≪≫
    (smallEtaleDerivedPullbackAbCompIsoQhLift (smallEtalePullbackAbCompIso e (b ≫ a))).symm ≪≫
    Functor.isoWhiskerRight
      (smallEtaleDerivedPullbackAbCompIsoQhLift (smallEtalePullbackAbCompIso b a)).symm
      (smallEtaleDerivedPullbackAb e)

/-- **Derived restriction along three morphisms in turn is derived restriction along their
composite**, read through `Stacks.EtaleCohomology.smallEtaleDerivedPullbackThreeCompIso`. -/
theorem smallEtaleDerivedGlobalSectionsRestriction_three (hh : e ≫ b ≫ a = h)
    (N : smallEtaleDerivedCategory Y) :
    (smallEtaleDerivedGlobalSectionsRestriction a).app N ≫
        (smallEtaleDerivedGlobalSectionsRestriction b).app
          ((smallEtaleDerivedPullbackAb a).obj N) ≫
        (smallEtaleDerivedGlobalSectionsRestriction e).app
          ((smallEtaleDerivedPullbackAb b).obj ((smallEtaleDerivedPullbackAb a).obj N)) =
      (smallEtaleDerivedGlobalSectionsRestriction h).app N ≫
        (smallEtaleDerivedGlobalSections T).map
          ((smallEtaleDerivedPullbackThreeCompIso a b e h hh).hom.app N) := by
  subst hh
  have h1 := NatTrans.congr_app (smallEtaleDerivedGlobalSectionsRestriction_comp e (b ≫ a)) N
  have h2 := NatTrans.congr_app (smallEtaleDerivedGlobalSectionsRestriction_comp b a) N
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] at h1 h2
  rw [h1, h2]
  simp only [smallEtaleDerivedPullbackThreeCompIso, Iso.trans_hom, NatTrans.comp_app,
    eqToIso_refl, Iso.refl_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.id_comp, Category.assoc, Functor.map_comp]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, (smallEtaleDerivedGlobalSectionsRestriction e).naturality_assoc,
    Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  exact congrArg (_ ≫ _ ≫ ·) (Category.comp_id _).symm

end RestrictionComp

section UnitAlongPullback

variable {Z Y T : Scheme.{u}} (c : Y ⟶ Z) (h : T ⟶ Y)

/-- The degreewise identity behind
`Stacks.EtaleCohomology.smallEtaleDerivedPushforwardAbPullbackUnit_eq_pullbackPushforwardUnit`:
the degreewise adjunction unit at `c⁻¹J`, followed by `h_*` of the composition isomorphism, is the
degreewise action of the comparison `c⁻¹ ⟶ h_*(h ≫ c)⁻¹`. -/
theorem homotopyCategoryPullbackPushforwardAbUnit_comp_compIso
    (J : HomotopyCategory (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ)) :
    (homotopyCategoryPullbackPushforwardAbUnit h).app
          (((smallEtalePullbackAb c).mapHomotopyCategory (.up ℤ)).obj J) ≫
        ((smallEtalePushforwardAb h).mapHomotopyCategory (.up ℤ)).map
          ((Functor.mapHomotopyCategoryCompIso (smallEtalePullbackAbCompIso h c) (.up ℤ)).hom.app
            J) =
      (Stacks.DerivedFunctor.mapHomotopyCategoryOfComp (smallEtalePullbackAb c)
        (smallEtalePullbackAb (h ≫ c)) (smallEtalePushforwardAb h)
        (smallEtalePushforwardAbPullbackUnit c h)).app J := by
  rw [homotopyCategoryPullbackPushforwardAbUnit_app,
    Stacks.DerivedFunctor.mapHomotopyCategoryOfComp_app,
    Stacks.DerivedFunctor.mapHomotopyCategoryCompIso_hom_app]
  exact map_comp_two (HomotopyCategory.quotient _ _) _ _
    (HomologicalComplex.hom_ext _ _ fun _ => (smallEtalePushforwardAbPullbackUnit_app c h _).symm)

/-- **The comparison `β : c⁻¹K ⟶ Rh_*((h ≫ c)⁻¹K)` is the derived adjunction unit at `c⁻¹K`.**
For morphisms of schemes `c : Y ⟶ Z` and `h : T ⟶ Y`, the comparison
`Stacks.EtaleCohomology.smallEtaleDerivedPushforwardAbPullbackUnit` is the unit
`c⁻¹K ⟶ Rh_*h⁻¹c⁻¹K` of the derived adjunction along `h`, followed by `Rh_*` of the
identification `h⁻¹c⁻¹ ≅ (h ≫ c)⁻¹`. -/
theorem smallEtaleDerivedPushforwardAbPullbackUnit_eq_pullbackPushforwardUnit :
    smallEtaleDerivedPushforwardAbPullbackUnit c h =
      (Functor.rightUnitor _).inv ≫
        Functor.whiskerLeft (smallEtaleDerivedPullbackAb c)
          (smallEtaleDerivedPullbackPushforwardAbUnit h) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (smallEtaleDerivedPullbackAbCompIsoQhLift (smallEtalePullbackAbCompIso h c)).hom
          (smallEtaleDerivedPushforwardAb h) := by
  refine Functor.rightDerived_ext (smallEtaleDerivedPullbackAb c)
    (smallEtalePullbackAb c).mapDerivedCategoryFactorsh.inv
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ)) _ _ _ ?_
  refine NatTrans.ext (funext fun J => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Category.id_comp]
  rw [smallEtaleDerivedPushforwardAbPullbackUnit_fac_app]
  refine (l2_rearrange (smallEtaleDerivedPushforwardAb h) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((smallEtaleDerivedPullbackPushforwardAbUnit h).naturality
      ((smallEtalePullbackAb c).mapDerivedCategoryFactorsh.inv.app J))
    ((smallEtaleDerivedPullbackPushforwardAbUnit_app_Qh h _).trans
      (derivedPullbackPushforwardAbUnitAux_app h _))
    (smallEtaleDerivedPullbackAbCompIsoQhLift_hom_app _ J)
    ((smallEtaleDerivedPushforwardAbUnit h).naturality
      ((Functor.mapHomotopyCategoryCompIso (smallEtalePullbackAbCompIso h c) (.up ℤ)).hom.app
        J)).symm
    (map_comp_two DerivedCategory.Qh _ _
      (homotopyCategoryPullbackPushforwardAbUnit_comp_compIso c h J))
    (by rw [← Functor.map_comp, Iso.inv_hom_id_app]; exact CategoryTheory.Functor.map_id _ _)
    (Iso.inv_hom_id_app _ _)).symm

/-- **Derived global sections of `β`, read through `RΓ(Y, Rh_* -) ≅ RΓ(T, -)`, are restriction
along `h`.** For morphisms of schemes `c : Y ⟶ Z` and `h : T ⟶ Y` and `K` in `D(Z_étale)`,
`RΓ(Y, β_K)` followed by `RΓ(Y, Rh_*(h ≫ c)⁻¹K) ≅ RΓ(T, (h ≫ c)⁻¹K)` is the derived restriction
`RΓ(Y, c⁻¹K) ⟶ RΓ(T, h⁻¹c⁻¹K)` followed by the identification `h⁻¹c⁻¹ ≅ (h ≫ c)⁻¹`. -/
theorem globalSections_smallEtaleDerivedPushforwardAbPullbackUnit_app
    (K : smallEtaleDerivedCategory Z) :
    (smallEtaleDerivedGlobalSections Y).map
          ((smallEtaleDerivedPushforwardAbPullbackUnit c h).app K) ≫
        (smallEtaleDerivedGlobalSectionsPushforwardIsoAb h).hom.app
          ((smallEtaleDerivedPullbackAb (h ≫ c)).obj K) =
      (smallEtaleDerivedGlobalSectionsRestriction h).app ((smallEtaleDerivedPullbackAb c).obj K) ≫
        (smallEtaleDerivedGlobalSections T).map
          ((smallEtaleDerivedPullbackAbCompIsoQhLift
            (smallEtalePullbackAbCompIso h c)).hom.app K) := by
  have h2 := NatTrans.congr_app
    (smallEtaleDerivedPushforwardAbPullbackUnit_eq_pullbackPushforwardUnit c h) K
  have h1 := NatTrans.congr_app
    (smallEtaleDerivedGlobalSectionsRestriction_eq_pullbackPushforwardUnit h)
    ((smallEtaleDerivedPullbackAb c).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.rightUnitor_inv_app,
    Functor.leftUnitor_inv_app, Category.id_comp] at h1 h2
  rw [h2, h1, Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg (_ ≫ ·) ((smallEtaleDerivedGlobalSectionsPushforwardIsoAb h).hom.naturality
    ((smallEtaleDerivedPullbackAbCompIsoQhLift (smallEtalePullbackAbCompIso h c)).hom.app K))

end UnitAlongPullback

/-- The rearrangement behind
`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsRestriction_transport`, for bare
morphisms. -/
private theorem transport_rearrange {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {M₀ M₁ M₂ : D} {U V W₁ W₂ W₃ W₄ Z : C} (ra : M₀ ⟶ M₁) (rb : M₁ ⟶ M₂)
    (re : M₂ ⟶ R.obj V) (rh : M₀ ⟶ R.obj U) (T' : U ⟶ V) (A₁ : V ⟶ W₁) (A₂ : W₁ ⟶ W₂)
    (A₃ : W₂ ⟶ W₃) (A₄ : W₃ ⟶ W₄) (A₅ : W₄ ⟶ U) (F : U ⟶ Z)
    (hG : ra ≫ rb ≫ re = rh ≫ R.map T') (hk : T' ≫ A₁ ≫ A₂ ≫ A₃ ≫ A₄ ≫ A₅ = 𝟙 U) :
    ra ≫ rb ≫ re ≫ R.map A₁ ≫ R.map A₂ ≫ R.map A₃ ≫ R.map A₄ ≫ R.map A₅ ≫ R.map F =
      rh ≫ R.map F := by
  have hR : R.map T' ≫ R.map A₁ ≫ R.map A₂ ≫ R.map A₃ ≫ R.map A₄ ≫ R.map A₅ = 𝟙 _ := by
    simp only [← R.map_comp]
    rw [hk, R.map_id]
  rw [reassoc_of% hG, reassoc_of% hR]

section FibreTransport

variable {X Y Y' X' T : Scheme.{u}} (p : Y ⟶ X) (a : Y' ⟶ Y) (p' : Y' ⟶ X) (b : X' ⟶ Y')
  (g' : X' ⟶ X) (e : T ⟶ X') (h : T ⟶ Y) (hh : e ≫ b ≫ a = h)
  (χ₁ : smallEtaleDerivedPullbackAb p ⋙ smallEtaleDerivedPullbackAb a ≅
    smallEtaleDerivedPullbackAb p')
  (χ₂ : smallEtaleDerivedPullbackAb p' ⋙ smallEtaleDerivedPullbackAb b ≅
    smallEtaleDerivedPullbackAb g')
  {Q : smallEtaleDerivedCategory X ⥤ smallEtaleDerivedCategory T}
  (χ₄ : smallEtaleDerivedPullbackAb p ⋙ smallEtaleDerivedPullbackAb h ≅ Q)

/-- The identification `e⁻¹g'⁻¹ ≅ Q` assembled from identifications `a⁻¹p⁻¹ ≅ p'⁻¹`,
`b⁻¹p'⁻¹ ≅ g'⁻¹` and `h⁻¹p⁻¹ ≅ Q` along a factorization `e ≫ b ≫ a = h`. -/
def smallEtaleDerivedPullbackTransportIso :
    smallEtaleDerivedPullbackAb g' ⋙ smallEtaleDerivedPullbackAb e ≅ Q :=
  Functor.isoWhiskerRight χ₂.symm (smallEtaleDerivedPullbackAb e) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight χ₁.symm (smallEtaleDerivedPullbackAb b))
      (smallEtaleDerivedPullbackAb e) ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _) (smallEtaleDerivedPullbackAb e) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (smallEtaleDerivedPullbackAb p)
      (smallEtaleDerivedPullbackThreeCompIso a b e h hh).symm ≪≫
    χ₄

/-- **Restriction along `a`, then `b`, then `e`, read through identifications of the inverse
images, is restriction along `h = e ≫ b ≫ a`**, as transformations
`p⁻¹ ⋙ RΓ(Y, -) ⟶ Q ⋙ RΓ(T, -)`. -/
theorem smallEtaleDerivedGlobalSectionsRestriction_transport :
    (Functor.whiskerLeft (smallEtaleDerivedPullbackAb p)
          (smallEtaleDerivedGlobalSectionsRestriction a) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight χ₁.hom (smallEtaleDerivedGlobalSections Y')) ≫
      (Functor.whiskerLeft (smallEtaleDerivedPullbackAb p')
          (smallEtaleDerivedGlobalSectionsRestriction b) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight χ₂.hom (smallEtaleDerivedGlobalSections X')) ≫
      (Functor.whiskerLeft (smallEtaleDerivedPullbackAb g')
          (smallEtaleDerivedGlobalSectionsRestriction e) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (smallEtaleDerivedPullbackTransportIso p a p' b g' e h hh χ₁ χ₂ χ₄).hom
          (smallEtaleDerivedGlobalSections T)) =
      Functor.whiskerLeft (smallEtaleDerivedPullbackAb p)
          (smallEtaleDerivedGlobalSectionsRestriction h) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight χ₄.hom (smallEtaleDerivedGlobalSections T) := by
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp, Category.assoc,
    smallEtaleDerivedPullbackTransportIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.map_comp]
  rw [(smallEtaleDerivedGlobalSectionsRestriction b).naturality_assoc, Functor.comp_map,
    ← Functor.map_comp_assoc, (smallEtaleDerivedGlobalSectionsRestriction e).naturality_assoc,
    Functor.comp_map]
  refine transport_rearrange (smallEtaleDerivedGlobalSections T) _ _ _ _ _ _ _ _ _ _ _
    (smallEtaleDerivedGlobalSectionsRestriction_three a b e h hh _) ?_
  simp only [← Functor.map_comp_assoc, CategoryTheory.Functor.map_id,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  simp [← Functor.map_comp]

end FibreTransport

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Cospecialization

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s))
  (K : smallEtaleDerivedCategory X)

/-- The inverse image `i⁻¹β_{K,s,t}` on the closed geometric fibre `X_s` of the comparison
`β_{K,s,t} : K|_Y ⟶ Rh_*(K|_{X_t})`, along `i : X_s ⟶ Y = X ×_S Spec 𝒪^{sh}_{S,s}`. -/
abbrev cospecializationUnitOnClosedFibre :=
  (smallEtaleDerivedPullbackAb (geometricFibreToStrictHenselizationBaseChange B hS f s)).map
    (cospecializationUnit B hS f s t K)

/-- **The cospecialization map of the source**, `RΓ(X_t, K) ⟶ RΓ(X_s, K)`, defined whenever
`i⁻¹β_{K,s,t}` is invertible: identify `RΓ(X_t, K)` with `RΓ(Y, Rh_*(K|_{X_t}))`, pull back
along `i : X_s ⟶ Y`, apply the inverse of `i⁻¹β_{K,s,t}` and identify `i⁻¹(K|_Y)` with
`K|_{X_s}`. Here `X_t` is the fibre `Y ×_{Spec 𝒪^{sh}_{S,s}} t` of the source. -/
def cospecializationMapOfIsIso [IsIso (cospecializationUnitOnClosedFibre B hS f s t K)] :
    (smallEtaleDerivedGlobalSections (cospecializationFibre B hS f s t)).obj
        ((smallEtaleDerivedPullbackAb (cospecializationFibreToSource B hS f s t)).obj K) ⟶
      (smallEtaleDerivedGlobalSections (geometricFibre f s)).obj
        ((smallEtaleDerivedPullbackAb (geometricFibreToSource f s)).obj K) :=
  (smallEtaleDerivedGlobalSectionsPushforwardIsoAb
      (cospecializationFibreToBaseChange B hS f s t)).inv.app
      ((smallEtaleDerivedPullbackAb (cospecializationFibreToSource B hS f s t)).obj K) ≫
    (smallEtaleDerivedGlobalSectionsRestriction
      (geometricFibreToStrictHenselizationBaseChange B hS f s)).app _ ≫
    (smallEtaleDerivedGlobalSections (geometricFibre f s)).map
      (inv (cospecializationUnitOnClosedFibre B hS f s t K)) ≫
    (smallEtaleDerivedGlobalSections (geometricFibre f s)).map
      ((Functor.mapDerivedCategoryCompIsoOfCompIso
        (geometricFibrePullbackAbCompIso B hS f s)).hom.app K)

/-- Pullback of cohomology along `h : X_t ⟶ Y`, written as derived global sections on `Y` of
`β_{K,s,t}` followed by `RΓ(Y, Rh_* -) ≅ RΓ(X_t, -)`. -/
abbrev cospecializationRestriction :
    (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s)).obj
        ((smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj K) ⟶
      (smallEtaleDerivedGlobalSections (cospecializationFibre B hS f s t)).obj
        ((smallEtaleDerivedPullbackAb (cospecializationFibreToSource B hS f s t)).obj K) :=
  (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s)).map
      (cospecializationUnit B hS f s t K) ≫
    (smallEtaleDerivedGlobalSectionsPushforwardIsoAb
      (cospecializationFibreToBaseChange B hS f s t)).hom.app _

/-- **The core of Stacks 0GJV.** Pulling back cohomology along `h : X_t ⟶ Y` and then applying
the cospecialization map is the map of Stacks 0GIX to the closed fibre,
`RΓ(X ×_S Spec 𝒪^{sh}_{S,s}, K) ⟶ RΓ(X_s, K)`. -/
theorem cospecializationRestriction_comp_cospecializationMapOfIsIso
    [IsIso (cospecializationUnitOnClosedFibre B hS f s t K)] :
    cospecializationRestriction B hS f s t K ≫ cospecializationMapOfIsIso B hS f s t K =
      (strictHenselizationSectionsToFibreSections B hS f s).app K := by
  simp only [cospecializationRestriction, cospecializationMapOfIsIso, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, (smallEtaleDerivedGlobalSectionsRestriction
    (geometricFibreToStrictHenselizationBaseChange B hS f s)).naturality, Functor.comp_map,
    Category.assoc, ← Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [fibreSections_app]

/-- The rearrangement behind
`AlgebraicGeometry.specializationStalk_comp_baseChange_comp_cospecializationMapGeometricFibre`,
for bare morphisms. -/
private theorem square_rearrange {C : Type*} [Category C] {A₀ A₁ A₂ B₁ B₂ B₃ B₄ : C}
    {sp : A₀ ⟶ A₁} {F₁ : A₁ ⟶ B₁} {F₂ : B₁ ⟶ B₂} {Tr : B₂ ⟶ B₃} {C₀ : B₃ ⟶ B₄}
    {Fs : A₀ ⟶ A₂} {SpS : A₂ ⟶ B₁} {R : A₂ ⟶ B₃} {Ss : A₂ ⟶ B₄}
    (h₉ : Fs ≫ SpS = sp ≫ F₁) (hS : SpS ≫ F₂ ≫ Tr = R) (hC : R ≫ C₀ = Ss) :
    sp ≫ F₁ ≫ F₂ ≫ Tr ≫ C₀ = Fs ≫ Ss := by
  rw [← reassoc_of% h₉, reassoc_of% hS, hC]

/-- The first projection of the factorization of `h`, for bare morphisms. -/
private theorem factor_fst {C : Type*} [Category C] {A₀ A₁ A₂ A₃ Z : C} {e : A₀ ⟶ A₁}
    {i : A₁ ⟶ A₂} {a : A₂ ⟶ A₃} {F : A₃ ⟶ Z} {p' : A₂ ⟶ Z} {g : A₁ ⟶ Z} {r : A₀ ⟶ Z}
    (ha : a ≫ F = p') (hi : i ≫ p' = g) (he : e ≫ g = r) : (e ≫ i ≫ a) ≫ F = r := by
  rw [Category.assoc, Category.assoc, ha, hi, he]

/-- The second projection of the factorization of `h`, for bare morphisms. -/
private theorem factor_snd {C : Type*} [Category C] {A₀ A₁ A₂ A₃ Z Z' P : C} {e : A₀ ⟶ A₁}
    {i : A₁ ⟶ A₂} {a : A₂ ⟶ A₃} {G : A₃ ⟶ Z} {G' : A₂ ⟶ Z'} {c : Z' ⟶ Z} {m : A₁ ⟶ P}
    {γ : P ⟶ Z'} {n : A₀ ⟶ P} {τ : P ⟶ Z} {r' : A₀ ⟶ Z}
    (ha : a ≫ G = G' ≫ c) (hi : i ≫ G' = m ≫ γ) (he : e ≫ m = n) (hc : γ ≫ c = τ)
    (hr : r' = n ≫ τ) : (e ≫ i ≫ a) ≫ G = r' := by
  rw [Category.assoc, Category.assoc, ha, reassoc_of% hi, reassoc_of% he, hc, hr]

/-- The two models of the fibre over `t`: the fibre `Y ×_{Spec 𝒪^{sh}_{S,s}} t` of the base change
`Y = X ×_S Spec 𝒪^{sh}_{S,s}`, and the geometric fibre `X ×_S t` of `f` at the image of `t` in
`S`, are canonically isomorphic by pasting of pullback squares. -/
def cospecializationFibreIso :
    cospecializationFibre B hS f s t ≅
      geometricFibre f (t.map (strictHenselizationToBase B S hS s)) :=
  pullbackLeftPullbackSndIso f (strictHenselizationToBase B S hS s) t.hom

/-- The isomorphism of the two models of the fibre over `t` lies over `X`. -/
theorem cospecializationFibreIso_hom_comp_toSource :
    (cospecializationFibreIso B hS f s t).hom ≫
        geometricFibreToSource f (t.map (strictHenselizationToBase B S hS s)) =
      cospecializationFibreToSource B hS f s t :=
  pullbackLeftPullbackSndIso_hom_fst _ _ _

/-- **The morphism `h : X_t ⟶ Y` factors through the base change to the strict henselization at
the specialized point**: it is the isomorphism of the two models of `X_t`, followed by the
canonical morphism from the geometric fibre at the specialized point to the base change there,
and by `id_X × c`. -/
theorem cospecializationFibreIso_hom_comp_comp :
    (cospecializationFibreIso B hS f s t).hom ≫
        geometricFibreToStrictHenselizationBaseChange B hS f
          (t.map (strictHenselizationToBase B S hS s)) ≫
        strictHenselizationBaseChangeSpecializationMap B hS f s t =
      cospecializationFibreToBaseChange B hS f s t := by
  apply pullback.hom_ext
  · exact factor_fst (strictHenselizationBaseChangeSpecializationMap_comp_toSource B hS f s t)
      (geometricFibreToStrictHenselizationBaseChange_comp_toSource B hS f
        (t.map (strictHenselizationToBase B S hS s)))
      (pullbackLeftPullbackSndIso_hom_fst _ _ _)
  · have hi : geometricFibreToStrictHenselizationBaseChange B hS f
          (t.map (strictHenselizationToBase B S hS s)) ≫
        strictHenselizationBaseChangeToStrictHenselization B hS f
          (t.map (strictHenselizationToBase B S hS s)) =
        geometricFibreToPoint f (t.map (strictHenselizationToBase B S hS s)) ≫
          geometricPointToStrictHenselization B S hS (t.map (strictHenselizationToBase B S hS s)) :=
      pullback.lift_snd _ _ _
    have he : (cospecializationFibreIso B hS f s t).hom ≫
        geometricFibreToPoint f (t.map (strictHenselizationToBase B S hS s)) =
        cospecializationFibreToPoint B hS f s t :=
      pullbackLeftPullbackSndIso_hom_snd _ _ _
    have hr : cospecializationFibreToBaseChange B hS f s t ≫
        strictHenselizationBaseChangeToStrictHenselization B hS f s =
        cospecializationFibreToPoint B hS f s t ≫ t.hom :=
      pullback.condition
    exact factor_snd
      (strictHenselizationBaseChangeSpecializationMap_comp_toStrictHenselization B hS f s t)
      hi he (geometricPointToStrictHenselization_comp_specializationMorphism B S hS s t) hr

/-- The identification of the inverse images of `K` to the model `Y ×_{Spec 𝒪^{sh}_{S,s}} t` of
the fibre over `t`: the restriction to `X ×_S t` followed by the isomorphism of the two models,
against the restriction along `h ≫ p`, assembled from the composition isomorphisms of inverse
images along the factorization `e ≫ i_t ≫ (id_X × c) = h`. -/
abbrev cospecializationFibrePullbackIso :=
  smallEtaleDerivedPullbackTransportIso (strictHenselizationBaseChangeToSource B hS f s)
    (strictHenselizationBaseChangeSpecializationMap B hS f s t)
    (strictHenselizationBaseChangeToSource B hS f (t.map (strictHenselizationToBase B S hS s)))
    (geometricFibreToStrictHenselizationBaseChange B hS f
      (t.map (strictHenselizationToBase B S hS s)))
    (geometricFibreToSource f (t.map (strictHenselizationToBase B S hS s)))
    (cospecializationFibreIso B hS f s t).hom
    (cospecializationFibreToBaseChange B hS f s t)
    (cospecializationFibreIso_hom_comp_comp B hS f s t)
    (smallEtaleDerivedPullbackAbCompIsoQhLift
      (strictHenselizationBaseChangeSpecializationPullbackAbCompIso B hS f s t))
    (Functor.mapDerivedCategoryCompIsoOfCompIso
      (geometricFibrePullbackAbCompIso B hS f (t.map (strictHenselizationToBase B S hS s))))
    (smallEtaleDerivedPullbackAbCompIsoQhLift
      (smallEtalePullbackAbCompIso (cospecializationFibreToBaseChange B hS f s t)
        (strictHenselizationBaseChangeToSource B hS f s)))

/-- Restriction of cohomology from the geometric fibre `X ×_S t` at the image of `t` to the model
`Y ×_{Spec 𝒪^{sh}_{S,s}} t` of the fibre, along the isomorphism of the two models. It is an
isomorphism. -/
def cospecializationFibreSections :
    smallEtaleDerivedPullbackAb
          (geometricFibreToSource f (t.map (strictHenselizationToBase B S hS s))) ⋙
        smallEtaleDerivedGlobalSections
          (geometricFibre f (t.map (strictHenselizationToBase B S hS s))) ⟶
      smallEtaleDerivedPullbackAb (cospecializationFibreToSource B hS f s t) ⋙
        smallEtaleDerivedGlobalSections (cospecializationFibre B hS f s t) :=
  Functor.whiskerLeft
      (smallEtaleDerivedPullbackAb
        (geometricFibreToSource f (t.map (strictHenselizationToBase B S hS s))))
      (smallEtaleDerivedGlobalSectionsRestriction (cospecializationFibreIso B hS f s t).hom) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (cospecializationFibrePullbackIso B hS f s t).hom
      (smallEtaleDerivedGlobalSections (cospecializationFibre B hS f s t))

/-- `AlgebraicGeometry.fibreSections_app` as an identity of transformations. -/
private theorem strictHenselizationSectionsToFibreSections_eq (s : GeometricPoint S) :
    strictHenselizationSectionsToFibreSections B hS f s =
      Functor.whiskerLeft
          (smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s))
          (smallEtaleDerivedGlobalSectionsRestriction
            (geometricFibreToStrictHenselizationBaseChange B hS f s)) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (Functor.mapDerivedCategoryCompIsoOfCompIso
            (geometricFibrePullbackAbCompIso B hS f s)).hom
          (smallEtaleDerivedGlobalSections (geometricFibre f s)) := by
  ext K
  rw [fibreSections_app]
  simp

/-- Pulling back cohomology along `id_X × c`, then to the geometric fibre at the specialized
point, then to the model `Y ×_{Spec 𝒪^{sh}_{S,s}} t` of that fibre, is pulling back cohomology
along `h : X_t ⟶ Y`. -/
theorem sectionsSpecialization_comp_fibreSections_comp_cospecializationFibreSections :
    strictHenselizationSectionsSpecializationAt B hS f s t ≫
        strictHenselizationSectionsToFibreSections B hS f
          (t.map (strictHenselizationToBase B S hS s)) ≫
        cospecializationFibreSections B hS f s t =
      Functor.whiskerLeft
          (smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s))
          (smallEtaleDerivedGlobalSectionsRestriction
            (cospecializationFibreToBaseChange B hS f s t)) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (smallEtaleDerivedPullbackAbCompIsoQhLift
            (smallEtalePullbackAbCompIso (cospecializationFibreToBaseChange B hS f s t)
              (strictHenselizationBaseChangeToSource B hS f s))).hom
          (smallEtaleDerivedGlobalSections (cospecializationFibre B hS f s t)) := by
  rw [strictHenselizationSectionsToFibreSections_eq]
  exact smallEtaleDerivedGlobalSectionsRestriction_transport _ _ _ _ _ _ _ _ _ _ _

/-- Pulling back cohomology along `h : X_t ⟶ Y` is `RΓ(Y, β_{K,s,t})` followed by
`RΓ(Y, Rh_* -) ≅ RΓ(X_t, -)`. -/
theorem cospecializationRestriction_eq :
    (Functor.whiskerLeft
          (smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s))
          (smallEtaleDerivedGlobalSectionsRestriction
            (cospecializationFibreToBaseChange B hS f s t)) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (smallEtaleDerivedPullbackAbCompIsoQhLift
            (smallEtalePullbackAbCompIso (cospecializationFibreToBaseChange B hS f s t)
              (strictHenselizationBaseChangeToSource B hS f s))).hom
          (smallEtaleDerivedGlobalSections (cospecializationFibre B hS f s t))).app K =
      cospecializationRestriction B hS f s t K := by
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp]
  exact (globalSections_smallEtaleDerivedPushforwardAbPullbackUnit_app _ _ K).symm

/-- **The cospecialization map** `cosp : RΓ(X_t, K) ⟶ RΓ(X_s, K)` of the source, for
`X_t = X ×_S t` the geometric fibre of `f` at the image of `t` in `S`: identify `RΓ(X_t, K)` with
the cohomology of the model `Y ×_{Spec 𝒪^{sh}_{S,s}} t` of `X_t` and apply
`AlgebraicGeometry.cospecializationMapOfIsIso`. It is defined whenever `i⁻¹β_{K,s,t}` is
invertible, which is Stacks 0GJU. -/
@[sga "4½ Arcata 5.1.6" "more general"]
def cospecializationMapGeometricFibre [IsIso (cospecializationUnitOnClosedFibre B hS f s t K)] :
    (smallEtaleDerivedGlobalSections
          (geometricFibre f (t.map (strictHenselizationToBase B S hS s)))).obj
        ((smallEtaleDerivedPullbackAb
          (geometricFibreToSource f (t.map (strictHenselizationToBase B S hS s)))).obj K) ⟶
      (smallEtaleDerivedGlobalSections (geometricFibre f s)).obj
        ((smallEtaleDerivedPullbackAb (geometricFibreToSource f s)).obj K) :=
  (cospecializationFibreSections B hS f s t).app K ≫ cospecializationMapOfIsIso B hS f s t K

/-- **Stacks 0GJV, for any invertibility of `i⁻¹β_{K,s,t}`.** The square

```
(Rf_*K)_s ----------> RΓ(X_s, K)
   | sp                    ^ cosp
   v                       |
(Rf_*K)_t ----------> RΓ(X_t, K)
```

commutes, the horizontal arrows being the base change maps of Stacks 0GIX (the composites of its
two canonical maps). -/
theorem specializationStalk_comp_baseChange_comp_cospecializationMapGeometricFibre
    [IsIso (cospecializationUnitOnClosedFibre B hS f s t K)] :
    (smallEtaleDerivedSpecializationStalkAbAt B S hS s t).app
          ((smallEtaleDerivedPushforwardAb f).obj K) ≫
        (derivedPushforwardStalkToStrictHenselizationSections B hS f
          (t.map (strictHenselizationToBase B S hS s))).app K ≫
        (strictHenselizationSectionsToFibreSections B hS f
          (t.map (strictHenselizationToBase B S hS s))).app K ≫
        cospecializationMapGeometricFibre B hS f s t K =
      (derivedPushforwardStalkToStrictHenselizationSections B hS f s).app K ≫
        (strictHenselizationSectionsToFibreSections B hS f s).app K := by
  have h9 := NatTrans.congr_app
    (derivedPushforwardStalkToStrictHenselizationSections_comp_sectionsSpecialization B hS f s t) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h9
  have hS' : (strictHenselizationSectionsSpecializationAt B hS f s t).app K ≫
      (strictHenselizationSectionsToFibreSections B hS f
          (t.map (strictHenselizationToBase B S hS s))).app K ≫
        (cospecializationFibreSections B hS f s t).app K =
      cospecializationRestriction B hS f s t K :=
    (NatTrans.congr_app
      (sectionsSpecialization_comp_fibreSections_comp_cospecializationFibreSections
        B hS f s t) K).trans (cospecializationRestriction_eq B hS f s t K)
  exact square_rearrange h9 hS'
    (cospecializationRestriction_comp_cospecializationMapOfIsIso B hS f s t K)

end Cospecialization

end AlgebraicGeometry
