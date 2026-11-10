module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorConnectingMorphism
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusSingleCompatible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.DerivedFunctorBoundary
public import StacksFrontier.Homology.DerivedIndexing.Composite
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit

/-!
# The base change map on higher direct images in degree zero

Let `h ≫ f' = e ≫ g` be a commutative square of schemes. The base change map
`Stacks.EtaleCohomology.higherBaseChangeMapAb` of [Stacks, Tag 0F02], `(f')⁻¹R^q g_* ⟶
R^q h_* e⁻¹`, is the degree-`q` cohomology of the derived base change comparison
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`, which is itself the descent along the
derived-functor unit of `Rg_*` of the underived base change map
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb`, the mate of the square. This file proves that
in degree zero the construction returns what it was descended from: through the
identifications `g_* ≅ R⁰g_*` and `h_* ≅ R⁰h_*` of the two left exact direct images with their
degree-zero right derived functors, the base change map in degree `0` is the mate.

The argument is abstract. For additive functors `F, F'` and exact functors `G, G'` with a
transformation `τ : F ⋙ G ⟶ G' ⋙ F'`, the descended comparison
`Stacks.Cohomology.BaseChange.derived` is characterised by its composite with the derived-functor
unit of `RF` (`Stacks.Cohomology.BaseChange.derived_fac_app`), and at the complex `X[0]` that
unit, the unit of `RG` and the comparisons of the exact functors with the single functors and
with homology are all computed by the corresponding maps of complexes concentrated in degree
zero. What remains is that an exact functor commutes with the homology of such a complex
compatibly with the identifications of that homology with the object, which is checked on
cycles.

## Main definitions

* `Stacks.DerivedFunctor.homologyQhSingleIso` — the identification `H⁰(Qh(Y[0])) ≅ Y` in the
  bounded below derived category.

## Main results

* `Stacks.Cohomology.BaseChange.map_rightDerivedZeroUnit_comp_derived` — **the descended
  comparison in degree zero is `τ`**, read through the identifications
  `Stacks.RightDerivedPlus.rightDerivedZeroUnit` of `F` and `F'` with `R⁰F` and `R⁰F'`.
* `Stacks.EtaleCohomology.map_rightDerivedZeroUnit_comp_higherBaseChangeMapAb_zero` — **the base
  change map on higher direct images in degree zero is the underived base change map**.
* `Stacks.DerivedFunctor.rightDerivedZeroUnit_eq` — the closed form of
  `Stacks.RightDerivedPlus.rightDerivedZeroUnit` through the comparison of a functor with the
  formation of complexes concentrated in degree zero.
* `Stacks.DerivedFunctor.map_homologyQhSingleIso_hom_comp` — an exact functor commutes with the
  homology of the image of a complex concentrated in degree zero, compatibly with
  `Stacks.DerivedFunctor.homologyQhSingleIso`.

## Implementation notes

The identities between components of comparison isomorphisms are proved by rearrangement lemmas
stated on morphisms of an abstract category and applied by `exact`: at the instances they are
used at, the sources and targets of the components agree only definitionally, and a rewrite
builds a motive that is not type correct.

## References

* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedFunctor

/-! ### An exact functor and complexes concentrated in degree zero -/

section Homology

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The identification of the homology of an object placed in degree zero with the object,
through the homology of the complex concentrated in degree zero. -/
theorem singleFunctorCompHomologyFunctorIso_hom_app' (Y : C) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app Y =
      (DerivedCategory.homologyFunctorFactors C 0).hom.app
          ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj Y) ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 Y).hom := by
  simp only [Functor.comp_obj, Functor.id_obj, DerivedCategory.singleFunctorCompHomologyFunctorIso,
    SingleFunctors.evaluation_obj, SingleFunctors.postcomp_functor,
    DerivedCategory.singleFunctorsPostcompQIso, Functor.mapIso_refl, Functor.isoWhiskerRight_refl,
    HomologicalComplex.homologyFunctorSingleIso, Iso.refl_trans, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, DerivedCategory.Q_obj_single_obj]
  exact Category.id_comp _

end Homology

section HomologyPlus

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

private theorem nat_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₄ o₅ : 𝒳}
    {a : o₀ ⟶ o₁} {b : o₁ ⟶ o₂} {c : o₂ ⟶ o₃} {d : o₀ ⟶ o₄} {m : o₄ ⟶ o₂} {e : o₄ ⟶ o₅}
    {g : o₅ ⟶ o₃} (h₁ : a ≫ b = d ≫ m) (h₂ : m ≫ c = e ≫ g) : a ≫ b ≫ c = (d ≫ e) ≫ g := by
  rw [reassoc_of% h₁, h₂, Category.assoc]

/-- A composite with the image of a composite, regrouped. -/
theorem comp_map_comp {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Φ : 𝒞 ⥤ 𝒟) {X : 𝒟}
    {Y Y' Y'' : 𝒞} (a : X ⟶ Φ.obj Y) (b : Y ⟶ Y') (c : Y' ⟶ Y'') :
    a ≫ Φ.map (b ≫ c) = (a ≫ Φ.map b) ≫ Φ.map c := by
  rw [Φ.map_comp, Category.assoc]

/-- **The homology in degree zero of the image of a complex concentrated in degree zero**, in the
bounded below derived category: `H⁰(Qh(Y[0])) ≅ Y`, through the identification of the single
functor into `D⁺(C)` with the single functor into `K⁺(C)` followed by `Qh`. -/
def homologyQhSingleIso (Y : C) :
    Y ≅ (DerivedCategory.Plus.homologyFunctor C 0).obj
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor C 0).obj Y)) :=
  ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app Y).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor C 0).mapIso
      ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).app Y)

/-- The components of `Stacks.DerivedFunctor.homologyQhSingleIso`. -/
theorem homologyQhSingleIso_hom (Y : C) :
    (homologyQhSingleIso Y).hom =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app Y ≫
        (DerivedCategory.Plus.homologyFunctor C 0).map
          ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).hom.app Y) :=
  rfl

/-- `Stacks.DerivedFunctor.homologyQhSingleIso` is natural. -/
@[reassoc]
theorem homologyQhSingleIso_hom_naturality {Y Y' : C} (f : Y ⟶ Y') :
    f ≫ (homologyQhSingleIso Y').hom =
      (homologyQhSingleIso Y).hom ≫ (DerivedCategory.Plus.homologyFunctor C 0).map
        (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.singleFunctor C 0).map f)) := by
  have h₁ := (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.naturality f
  have h₂ := congrArg (DerivedCategory.Plus.homologyFunctor C 0).map
    ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).hom.naturality f)
  simp only [Functor.comp_map, Functor.id_map, Functor.map_comp] at h₁ h₂
  exact nat_chain h₁ h₂

end HomologyPlus

section Single

variable {B D : Type*} [Category* B] [Category* D] [Abelian B] [Abelian D]
  (G : B ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

private theorem s2c_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₄ o₅ : 𝒳}
    {cm : o₀ ⟶ o₁} {π : o₁ ⟶ o₂} {mh : o₂ ⟶ o₃} {gs : o₃ ⟶ o₄} {mc : o₁ ⟶ o₅}
    {gπ : o₅ ⟶ o₃} {gc : o₅ ⟶ o₄} {c₁ : o₀ ⟶ o₄}
    (h₂ : π ≫ mh = mc ≫ gπ) (h₃ : gπ ≫ gs = gc) (h₅ : cm ≫ mc ≫ gc = c₁) :
    cm ≫ π ≫ mh ≫ gs = c₁ := by
  rw [reassoc_of% h₂, h₃, h₅]

private theorem cycles_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₄ o₅ : 𝒳}
    {cm : o₀ ⟶ o₁} {mc : o₁ ⟶ o₂} {gm : o₂ ⟶ o₃} {giC : o₂ ⟶ o₄} {gx : o₄ ⟶ o₃}
    {iCm : o₁ ⟶ o₄} {iC' : o₀ ⟶ o₅} {φ₀ : o₅ ⟶ o₄} {x' : o₅ ⟶ o₃} {gxi : o₃ ⟶ o₄}
    (hm : gm = giC ≫ gx) (ha : mc ≫ giC = iCm) (hb : cm ≫ iCm = iC' ≫ φ₀)
    (hc : φ₀ = x' ≫ gxi) (hd : gxi ≫ gx = 𝟙 _) : cm ≫ mc ≫ gm = iC' ≫ x' := by
  rw [hm, reassoc_of% ha, reassoc_of% hb, hc, Category.assoc, hd, Category.comp_id]

/-- **An exact functor commutes with the cycles of a complex concentrated in degree zero**,
compatibly with the identifications of both cycles with the object. -/
theorem cyclesMap_singleMapHomologicalComplex_inv_comp (Y : B) :
    HomologicalComplex.cyclesMap
        ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).inv.app Y) 0 ≫
      ((((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj Y).sc 0).mapCyclesIso G).hom ≫
      G.map (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 Y).hom =
    (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 (G.obj Y)).hom := by
  rw [HomologicalComplex.singleObjCyclesSelfIso_hom, HomologicalComplex.singleObjCyclesSelfIso_hom]
  exact cycles_chain (G.map_comp _ _)
    ((((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj Y).sc 0).mapCyclesIso_hom_iCycles G)
    (HomologicalComplex.cyclesMap_i _ 0)
    (HomologicalComplex.singleMapHomologicalComplex_inv_app_self G (ComplexShape.up ℤ) 0 Y)
    (G.mapIso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y)).inv_hom_id

/-- **An exact functor commutes with the homology of a complex concentrated in degree zero**,
compatibly with the identifications of both homologies with the object: the comparison
`Stacks.DerivedFunctor.complexHomologyIso` at `Y[0]`, read through
`HomologicalComplex.singleMapHomologicalComplex`, is the identity of `G(Y)`. -/
theorem homologyMap_singleMapHomologicalComplex_inv_comp (Y : B) :
    HomologicalComplex.homologyMap
        ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).inv.app Y) 0 ≫
      (complexHomologyIso G (ComplexShape.up ℤ) 0).hom.app
        ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj Y) ≫
      G.map (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 Y).hom =
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (G.obj Y)).hom := by
  rw [complexHomologyIso_hom_app, ← cancel_epi (HomologicalComplex.homologyπ _ 0)]
  dsimp only [Functor.comp_obj]
  rw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.homologyπ_naturality_assoc]
  have h2 := Stacks.Homology.mapHomologyIso_homologyπ
    (((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj Y).sc 0) G
  have h3 := congrArg G.map (HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom
    (ComplexShape.up ℤ) 0 Y)
  rw [G.map_comp] at h3
  exact s2c_chain h2 h3 (cyclesMap_singleMapHomologicalComplex_inv_comp G Y)

section

variable [HasDerivedCategory B] [HasDerivedCategory D]

private theorem s2u_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₄ o₅ o₆ o₇ : 𝒳}
    {hs : o₀ ⟶ o₁} {hf : o₁ ⟶ o₂} {ff : o₂ ⟶ o₃} {ch : o₃ ⟶ o₄} {gfi : o₄ ⟶ o₅}
    {gs : o₅ ⟶ o₆} {hq : o₀ ⟶ o₂} {ff' : o₀ ⟶ o₇} {hm : o₇ ⟶ o₃} {gso : o₄ ⟶ o₆}
    {so : o₇ ⟶ o₆} {r : o₀ ⟶ o₆}
    (h₁ : hs ≫ hf = hq) (h₂ : hq ≫ ff = ff' ≫ hm) (h₃ : gfi ≫ gs = gso)
    (h₄ : hm ≫ ch ≫ gso = so) (h₅ : r = ff' ≫ so) :
    hs ≫ (hf ≫ ff ≫ ch ≫ gfi) ≫ gs = r := by
  rw [h₅, ← h₄, ← h₃]
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂]

/-- **The homology comparison of an exact functor on the derived category, at an object placed
in degree zero**: read through `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` and the
two identifications `DerivedCategory.singleFunctorCompHomologyFunctorIso`, it is the identity. -/
theorem homologyFunctor_map_mapDerivedCategorySingleFunctor_inv_comp (Y : B) :
    (DerivedCategory.homologyFunctor D 0).map ((G.mapDerivedCategorySingleFunctor 0).inv.app Y) ≫
      (derivedHomologyIso G 0).hom.app ((DerivedCategory.singleFunctor B 0).obj Y) ≫
      G.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).hom.app Y) =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).hom.app (G.obj Y) := by
  have hd := derivedHomologyIso_hom_app_Q G 0
    ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj Y)
  have h₁ := congrArg (DerivedCategory.homologyFunctor D 0).map
    (G.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app Y)
  rw [Functor.map_comp] at h₁
  have h₂ := (DerivedCategory.homologyFunctorFactors D 0).hom.naturality
    ((G.mapCochainComplexSingleFunctor 0).inv.app Y)
  have h₃ : G.map ((DerivedCategory.homologyFunctorFactors B 0).inv.app
      ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj Y)) ≫
      G.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).hom.app Y) =
      G.map (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 Y).hom := by
    rw [← G.map_comp, singleFunctorCompHomologyFunctorIso_hom_app']
    exact congrArg G.map (Iso.inv_hom_id_app_assoc _ _ _)
  exact (congrArg (fun z => _ ≫ z ≫ _) hd).trans (s2u_chain h₁ h₂ h₃
    (homologyMap_singleMapHomologicalComplex_inv_comp G Y)
    (singleFunctorCompHomologyFunctorIso_hom_app' (G.obj Y)))

private theorem s1u_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₄ o₅ : 𝒳}
    {gi : o₀ ⟶ o₁} {fh : o₁ ⟶ o₂} {gh : o₁ ⟶ o₀} {f : o₀ ⟶ o₃} {q : o₃ ⟶ o₂}
    {m : o₂ ⟶ o₂} {s : o₀ ⟶ o₄} {si : o₄ ⟶ o₀} {Qs : o₄ ⟶ o₃} {q' : o₄ ⟶ o₅}
    {qm : o₅ ⟶ o₂}
    (hfh : fh = gh ≫ f ≫ q ≫ m) (hgi : gi ≫ gh = 𝟙 _) (hm : m = 𝟙 _) (hf : si ≫ f = Qs)
    (hs : s ≫ si = 𝟙 _) (hnat : Qs ≫ q = q' ≫ qm) :
    gi ≫ fh = s ≫ q' ≫ qm := by
  rw [hfh, reassoc_of% hgi, hm, Category.comp_id, ← hnat, ← hf, Category.assoc,
    reassoc_of% hs]

/-- **The degreewise action of an exact functor on the derived category, at an object placed in
degree zero.** The comparison `CategoryTheory.Functor.mapDerivedCategoryFactorsh` of the action
with the action on the homotopy category, read at `Y[0]` through the identifications of the
single functors, is `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` followed by
`CategoryTheory.Functor.mapHomotopyCategorySingleFunctor`. -/
theorem mapDerivedCategory_map_singleFunctorIsoCompQh_comp (Y : B) :
    G.mapDerivedCategory.map ((DerivedCategory.singleFunctorIsoCompQh B 0).hom.app Y) ≫
        G.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.singleFunctor B 0).obj Y) =
      (G.mapDerivedCategorySingleFunctor 0).hom.app Y ≫
        (DerivedCategory.singleFunctorIsoCompQh D 0).hom.app (G.obj Y) ≫
        DerivedCategory.Qh.map ((G.mapHomotopyCategorySingleFunctor 0).inv.app Y) := by
  rw [Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app,
    Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app,
    Stacks.DerivedIndexing.mapHomotopyCategorySingleFunctor_inv_app]
  have hfh := G.mapDerivedCategoryFactorsh_hom_app
    ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj Y)
  have hgi := (G.mapDerivedCategory.mapIso ((DerivedCategory.quotientCompQhIso B).app
    ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj Y))).inv_hom_id
  have hnat := (DerivedCategory.quotientCompQhIso D).inv.naturality
    ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).inv.app Y)
  have hf := G.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app Y
  exact s1u_chain hfh hgi (DerivedCategory.Qh.map_id _) hf
    ((G.mapDerivedCategorySingleFunctor 0).hom_inv_id_app Y) hnat

private theorem inv_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ : 𝒳}
    {a : o₀ ⟶ o₁} {b : o₁ ⟶ o₂} {c : o₂ ⟶ o₃} {d : o₀ ⟶ o₃}
    {a' : o₁ ⟶ o₀} {b' : o₂ ⟶ o₁} {c' : o₃ ⟶ o₂} {d' : o₃ ⟶ o₀}
    (h : a ≫ b ≫ c = d) (hd : d ≫ d' = 𝟙 _) (ha : a' ≫ a = 𝟙 _) (hb : b' ≫ b = 𝟙 _)
    (hc : c' ≫ c = 𝟙 _) : c' ≫ b' ≫ a' = d' := by
  calc c' ≫ b' ≫ a' = (c' ≫ b' ≫ a') ≫ d ≫ d' := by rw [hd, Category.comp_id]
    _ = d' := by
      rw [← h]
      simp only [Category.assoc]
      rw [reassoc_of% ha, reassoc_of% hb, reassoc_of% hc]

/-- `homologyFunctor_map_mapDerivedCategorySingleFunctor_inv_comp`, inverted. -/
theorem map_singleFunctorCompHomologyFunctorIso_inv_comp (Y : B) :
    G.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).inv.app Y) ≫
      (derivedHomologyIso G 0).inv.app ((DerivedCategory.singleFunctor B 0).obj Y) ≫
      (DerivedCategory.homologyFunctor D 0).map ((G.mapDerivedCategorySingleFunctor 0).hom.app Y) =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).inv.app (G.obj Y) :=
  inv_chain (homologyFunctor_map_mapDerivedCategorySingleFunctor_inv_comp G Y)
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).hom_inv_id_app (G.obj Y))
    ((DerivedCategory.homologyFunctor D 0).mapIso
      ((G.mapDerivedCategorySingleFunctor 0).app Y)).hom_inv_id
    ((derivedHomologyIso G 0).inv_hom_id_app _)
    (G.mapIso ((DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).app Y)).inv_hom_id

private theorem e2u_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₄ o₅ o₆ : 𝒳}
    {gs : o₀ ⟶ o₁} {gm : o₁ ⟶ o₂} {di' : o₂ ⟶ o₃} {hf : o₃ ⟶ o₄} {di : o₁ ⟶ o₅}
    {hgm : o₅ ⟶ o₃} {hs : o₅ ⟶ o₆} {hr : o₆ ⟶ o₄} {si : o₀ ⟶ o₆} {gsm : o₀ ⟶ o₂}
    (hgsm : gsm = gs ≫ gm) (hnat : gm ≫ di' = di ≫ hgm) (h₁ : hgm ≫ hf = hs ≫ hr)
    (h₂ : gs ≫ di ≫ hs = si) : gsm ≫ di' ≫ hf = si ≫ hr := by
  rw [hgsm, Category.assoc, reassoc_of% hnat, h₁, ← reassoc_of% h₂]

/-- **The homology comparison of an exact functor, at the image in the derived category of a
complex concentrated in degree zero.** -/
theorem map_homologyQhSingle_comp_derivedHomologyIso_inv (Y : B) :
    G.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).inv.app Y ≫
        (DerivedCategory.homologyFunctor B 0).map
          ((DerivedCategory.singleFunctorIsoCompQh B 0).hom.app Y)) ≫
      (derivedHomologyIso G 0).inv.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.singleFunctor B 0).obj Y)) ≫
      (DerivedCategory.homologyFunctor D 0).map
        (G.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.singleFunctor B 0).obj Y)) =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).inv.app (G.obj Y) ≫
      (DerivedCategory.homologyFunctor D 0).map
        ((DerivedCategory.singleFunctorIsoCompQh D 0).hom.app (G.obj Y) ≫
          DerivedCategory.Qh.map ((G.mapHomotopyCategorySingleFunctor 0).inv.app Y)) := by
  have hnat := (derivedHomologyIso G 0).inv.naturality
    ((DerivedCategory.singleFunctorIsoCompQh B 0).hom.app Y)
  have h₁ := congrArg (DerivedCategory.homologyFunctor D 0).map
    (mapDerivedCategory_map_singleFunctorIsoCompQh_comp G Y)
  rw [Functor.map_comp, Functor.map_comp] at h₁
  exact e2u_chain (G.map_comp _ _) hnat h₁ (map_singleFunctorCompHomologyFunctorIso_inv_comp G Y)

end

end Single

/-! ### Complexes concentrated in degree zero in the bounded below homotopy category -/

section HomotopyPlus

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]

private theorem cancel_ids {𝒞 : Type*} [Category* 𝒞] {X Y : 𝒞} {a : X ⟶ X} {b : X ⟶ Y}
    {c d : Y ⟶ Y} (ha : a = 𝟙 X) (hc : c = 𝟙 Y) (hd : d = 𝟙 Y) : a ≫ b ≫ c ≫ d = b := by
  rw [ha, hc, hd, Category.id_comp, Category.id_comp, Category.comp_id]

/-- `CategoryTheory.Functor.mapHomotopyCategoryPlusSingleFunctor`, read in the homotopy category,
is the class of `HomologicalComplex.singleMapHomologicalComplex`. -/
theorem ι_map_mapHomotopyCategoryPlusSingleFunctor_inv_app (T : A ⥤ B) [T.Additive] (X : A) :
    (HomotopyCategory.Plus.ι B).map
        ((Functor.mapHomotopyCategoryPlusSingleFunctor T 0).inv.app X) =
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).inv.app X) := by
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.mapHomotopyCategoryPlusSingleFunctor,
    Functor.mapHomotopyCategoryPlusCompιIso, ObjectProperty.liftCompιIso,
    HomotopyCategory.Plus.singleFunctorCompιIso, Functor.fullyFaithfulCancelRight_inv_app,
    Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv, Category.assoc, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app,
    DerivedIndexing.mapHomotopyCategorySingleFunctor_inv_app, Functor.associator_inv_app,
    Category.comp_id, Category.id_comp, ObjectProperty.ι_map]
  exact ((HomotopyCategory.Plus.ι B).map_preimage _).trans
    (cancel_ids rfl ((T.mapHomotopyCategory (ComplexShape.up ℤ)).map_id _) rfl)

end HomotopyPlus

/-! ### The bounded below derived category -/

section Plus

attribute [local instance] HasDerivedCategory.standard

variable {B D : Type*} [Category* B] [Category* D] [Abelian B] [Abelian D] [EnoughInjectives B]
  (G : B ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The comparison `Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso` of an exact functor
with homology, at the image of a bounded below complex and with the derived-functor unit
undone, is the unbounded comparison `Stacks.DerivedFunctor.derivedHomologyIso` followed by the
comparison of the degreewise actions. -/
theorem exactRightDerivedPlusHomologyIso_inv_app_Qh_comp (N : HomotopyCategory.Plus B) :
    (exactRightDerivedPlusHomologyIso G 0).inv.app (DerivedCategory.Plus.Qh.obj N) ≫
        (DerivedCategory.Plus.homologyFunctor D 0).map
          ((Stacks.Cohomology.BaseChange.exactUnitIso G).inv.app N) =
      (derivedHomologyIso G 0).inv.app
          (DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Qh.obj N)) ≫
        (DerivedCategory.homologyFunctor D 0).map
          (G.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.Plus.ι B).obj N)) := by
  have h₁ : (exactRightDerivedPlusHomologyIso G 0).inv.app (DerivedCategory.Plus.Qh.obj N) =
      (derivedHomologyIso G 0).inv.app
          (DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Qh.obj N)) ≫
        (DerivedCategory.Plus.homologyFunctor D 0).map
          ((exactMapDerivedCategoryPlusIso G).hom.app (DerivedCategory.Plus.Qh.obj N)) :=
    rfl
  have h₂ : (exactMapDerivedCategoryPlusIso G).hom.app (DerivedCategory.Plus.Qh.obj N) ≫
      (Stacks.Cohomology.BaseChange.exactUnitIso G).inv.app N =
        G.mapDerivedCategoryPlusFactorsh.hom.app N := by
    rw [exactMapDerivedCategoryPlusIso_hom_app_Qh]
    simp [Stacks.Cohomology.BaseChange.exactUnitIso]
  rw [h₁]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    (((DerivedCategory.Plus.homologyFunctor D 0).map_comp _ _).symm.trans (congrArg _ h₂)))

/-- **An exact functor commutes with the homology of the image of a complex concentrated in
degree zero**, on the bounded below derived category: the comparison
`Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso` with the derived-functor unit undone,
read through the identifications of the homology of `Qh(Y[0])` with `Y`. -/
theorem map_homologyPlusSingle_comp_exactRightDerivedPlusHomologyIso_inv (Y : B) :
    G.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).inv.app Y ≫
        (DerivedCategory.Plus.homologyFunctor B 0).map
          ((Functor.singleFunctorPlusIsoCompQh (A := B) 0).hom.app Y)) ≫
      (exactRightDerivedPlusHomologyIso G 0).inv.app
        (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor B 0).obj Y)) ≫
      (DerivedCategory.Plus.homologyFunctor D 0).map
        ((Stacks.Cohomology.BaseChange.exactUnitIso G).inv.app
          ((HomotopyCategory.Plus.singleFunctor B 0).obj Y)) =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).inv.app (G.obj Y) ≫
      (DerivedCategory.Plus.homologyFunctor D 0).map
        ((Functor.singleFunctorPlusIsoCompQh (A := D) 0).hom.app (G.obj Y) ≫
          DerivedCategory.Plus.Qh.map
            ((Functor.mapHomotopyCategoryPlusSingleFunctor G 0).inv.app Y)) := by
  have e₁ : (DerivedCategory.Plus.homologyFunctor B 0).map
      ((Functor.singleFunctorPlusIsoCompQh (A := B) 0).hom.app Y) =
        (DerivedCategory.homologyFunctor B 0).map
          ((DerivedCategory.singleFunctorIsoCompQh B 0).hom.app Y) :=
    congrArg (DerivedCategory.homologyFunctor B 0).map
      (Stacks.DerivedIndexing.ι_map_singleFunctorPlusIsoCompQh_hom_app 0 Y)
  have e₂ : (DerivedCategory.Plus.homologyFunctor D 0).map
      ((Functor.singleFunctorPlusIsoCompQh (A := D) 0).hom.app (G.obj Y) ≫
          DerivedCategory.Plus.Qh.map
            ((Functor.mapHomotopyCategoryPlusSingleFunctor G 0).inv.app Y)) =
        (DerivedCategory.homologyFunctor D 0).map
          ((DerivedCategory.singleFunctorIsoCompQh D 0).hom.app (G.obj Y) ≫
            DerivedCategory.Qh.map ((G.mapHomotopyCategorySingleFunctor 0).inv.app Y)) := by
    refine congrArg (DerivedCategory.homologyFunctor D 0).map
      ((DerivedCategory.Plus.ι.map_comp _ _).trans ?_)
    rw [Stacks.DerivedIndexing.ι_map_singleFunctorPlusIsoCompQh_hom_app,
      Stacks.DerivedIndexing.ι_map_Plus_Qh_map,
      ι_map_mapHomotopyCategoryPlusSingleFunctor_inv_app,
      Stacks.DerivedIndexing.mapHomotopyCategorySingleFunctor_inv_app]
    rfl
  rw [e₁, e₂, exactRightDerivedPlusHomologyIso_inv_app_Qh_comp]
  exact map_homologyQhSingle_comp_derivedHomologyIso_inv G Y

/-- `Stacks.DerivedFunctor.map_homologyPlusSingle_comp_exactRightDerivedPlusHomologyIso_inv`
through `Stacks.DerivedFunctor.homologyQhSingleIso`. -/
theorem map_homologyQhSingleIso_hom_comp (Y : B) :
    G.map (homologyQhSingleIso Y).hom ≫
      (exactRightDerivedPlusHomologyIso G 0).inv.app
        (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor B 0).obj Y)) ≫
      (DerivedCategory.Plus.homologyFunctor D 0).map
        ((Stacks.Cohomology.BaseChange.exactUnitIso G).inv.app
          ((HomotopyCategory.Plus.singleFunctor B 0).obj Y)) =
    (homologyQhSingleIso (G.obj Y)).hom ≫
      (DerivedCategory.Plus.homologyFunctor D 0).map
        (DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusSingleFunctor G 0).inv.app Y)) :=
  (map_homologyPlusSingle_comp_exactRightDerivedPlusHomologyIso_inv G Y).trans
    (comp_map_comp (DerivedCategory.Plus.homologyFunctor D 0)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).inv.app (G.obj Y))
      ((Functor.singleFunctorPlusIsoCompQh (A := D) 0).hom.app (G.obj Y))
      (DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusSingleFunctor G 0).inv.app Y)))

private theorem s1_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₄ o₅ o₆ : 𝒳}
    {si : o₀ ⟶ o₁} {ex : o₁ ⟶ o₂} {mh : o₁ ⟶ o₃} {eQ : o₃ ⟶ o₄} {rh : o₂ ⟶ o₄}
    {ri : o₄ ⟶ o₂} {fh : o₃ ⟶ o₅} {u : o₅ ⟶ o₄} {s₁ : o₀ ⟶ o₆} {s₂ : o₆ ⟶ o₅}
    (hnat : mh ≫ eQ = ex ≫ rh) (hr : rh ≫ ri = 𝟙 _) (heQ : eQ = fh ≫ u)
    (hs : si ≫ mh ≫ fh = s₁ ≫ s₂) : si ≫ ex = s₁ ≫ s₂ ≫ u ≫ ri := by
  rw [← reassoc_of% hs, ← reassoc_of% heQ, reassoc_of% hnat, hr, Category.comp_id]

/-- **The comparison `E(Y)[0] ≅ RE(Y[0])` of an exact functor is the derived-functor unit at
the complex concentrated in degree zero**, read through the identifications of the single
functors and `CategoryTheory.Functor.mapHomotopyCategoryPlusSingleFunctor`. -/
theorem exactSingleFunctorRightDerivedPlusIso_hom_app (Y : B) :
    (exactSingleFunctorRightDerivedPlusIso G 0).hom.app Y =
      (Functor.singleFunctorPlusIsoCompQh (A := D) 0).hom.app (G.obj Y) ≫
        DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusSingleFunctor G 0).inv.app Y) ≫
        G.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor B 0).obj Y) ≫
        G.rightDerivedFunctorPlus.map
          ((Functor.singleFunctorPlusIsoCompQh (A := B) 0).inv.app Y) := by
  have hnat := (exactMapDerivedCategoryPlusIso G).hom.naturality
    ((Functor.singleFunctorPlusIsoCompQh (A := B) 0).hom.app Y)
  have heQ := exactMapDerivedCategoryPlusIso_hom_app_Qh G
    ((HomotopyCategory.Plus.singleFunctor B 0).obj Y)
  have hs : (exactMapDerivedCategoryPlusSingle G 0).inv.app Y ≫
      G.mapDerivedCategoryPlus.map ((Functor.singleFunctorPlusIsoCompQh (A := B) 0).hom.app Y) ≫
      G.mapDerivedCategoryPlusFactorsh.hom.app ((HomotopyCategory.Plus.singleFunctor B 0).obj Y) =
        (Functor.singleFunctorPlusIsoCompQh (A := D) 0).hom.app (G.obj Y) ≫
          DerivedCategory.Plus.Qh.map
            ((Functor.mapHomotopyCategoryPlusSingleFunctor G 0).inv.app Y) := by
    apply DerivedCategory.Plus.ι.map_injective
    have h := mapDerivedCategory_map_singleFunctorIsoCompQh_comp G Y
    rw [DerivedCategory.Plus.ι.map_comp, DerivedCategory.Plus.ι.map_comp,
      DerivedCategory.Plus.ι.map_comp, ι_map_exactMapDerivedCategoryPlusSingle_inv_app,
      Stacks.DerivedIndexing.ι_map_singleFunctorPlusIsoCompQh_hom_app,
      Stacks.DerivedIndexing.ι_map_Plus_Qh_map,
      ι_map_mapHomotopyCategoryPlusSingleFunctor_inv_app,
      ← Stacks.DerivedIndexing.mapHomotopyCategorySingleFunctor_inv_app]
    have e : DerivedCategory.Plus.ι.map
        (G.mapDerivedCategoryPlus.map ((Functor.singleFunctorPlusIsoCompQh (A := B) 0).hom.app Y)) ≫
        DerivedCategory.Plus.ι.map
          (G.mapDerivedCategoryPlusFactorsh.hom.app
            ((HomotopyCategory.Plus.singleFunctor B 0).obj Y)) =
        G.mapDerivedCategory.map ((DerivedCategory.singleFunctorIsoCompQh B 0).hom.app Y) ≫
          G.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.singleFunctor B 0).obj Y) :=
      congrArg (fun z => G.mapDerivedCategory.map z ≫ _)
        (Stacks.DerivedIndexing.ι_map_singleFunctorPlusIsoCompQh_hom_app 0 Y)
    rw [e, h]
    exact ((G.mapDerivedCategorySingleFunctor 0).app Y).inv_hom_id_assoc _
  exact s1_chain hnat (G.rightDerivedFunctorPlus.mapIso
    ((Functor.singleFunctorPlusIsoCompQh (A := B) 0).app Y)).hom_inv_id heQ hs

end Plus

section ZeroUnit

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C] (T : C ⥤ D) [T.Additive]

omit [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C] in
/-- The class of `Stacks.DerivedIndexing.mapSinglePlus` in the bounded below homotopy category is
`CategoryTheory.Functor.mapHomotopyCategoryPlusSingleFunctor`. -/
theorem quotient_map_mapSinglePlus_app (X : C) :
    (HomotopyCategory.Plus.quotient D).map ((Stacks.DerivedIndexing.mapSinglePlus T 0).app X) =
      (Functor.mapHomotopyCategoryPlusSingleFunctor T 0).inv.app X :=
  (HomotopyCategory.Plus.ι D).map_injective
    (ι_map_mapHomotopyCategoryPlusSingleFunctor_inv_app T X).symm

/-- **The closed form of `Stacks.RightDerivedPlus.rightDerivedZeroUnit`**: the identification of
`T(X)` with the homology of the image of `T(X)[0]`, the comparison of `T` of a complex
concentrated in degree zero with that complex, the derived-functor unit, and the identification
of `X[0]` with its image from the homotopy category. -/
theorem rightDerivedZeroUnit_eq (X : C) :
    Stacks.RightDerivedPlus.rightDerivedZeroUnit T X =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).inv.app (T.obj X) ≫
        (DerivedCategory.Plus.homologyFunctor D 0).map
          ((Functor.singleFunctorPlusIsoCompQh (A := D) 0).hom.app (T.obj X) ≫
            DerivedCategory.Plus.Qh.map
              ((Functor.mapHomotopyCategoryPlusSingleFunctor T 0).inv.app X)) ≫
        (DerivedCategory.Plus.homologyFunctor D 0).map
          (T.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor C 0).obj X)) ≫
        (DerivedCategory.Plus.homologyFunctor D 0).map
          (T.rightDerivedFunctorPlus.map
            ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).inv.app X)) := by
  rw [Stacks.RightDerivedPlus.rightDerivedZeroUnit]
  simp only [Iso.app_inv]
  rw [Stacks.DerivedIndexing.mapSingleFunctorCompQhIso_inv_app_eq, quotient_map_mapSinglePlus_app]
  have h₁ : (((DerivedCategory.Plus.singleFunctor D 0).associator DerivedCategory.Plus.ι
      (DerivedCategory.homologyFunctor D 0)).symm.app (T.obj X) ≪≫
        (DerivedCategory.homologyFunctor D 0).mapIso
          ((DerivedCategory.Plus.singleFunctorιIso D 0).app (T.obj X)) ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).app (T.obj X)).inv =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).inv.app (T.obj X) := by
    simp only [DerivedCategory.Plus.singleFunctorιIso, Iso.trans_inv, Iso.symm_inv,
      Functor.mapIso_inv, Iso.app_inv, Functor.associator_hom_app]
    exact (Category.comp_id _).trans ((congrArg (_ ≫ ·)
      ((DerivedCategory.homologyFunctor D 0).map_id _)).trans (Category.comp_id _))
  rw [h₁]
  rfl

private theorem split_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₄ o₅ : 𝒳}
    {s : o₀ ⟶ o₁} {ha : o₁ ⟶ o₃} {h₁ : o₁ ⟶ o₂} {h₂ : o₂ ⟶ o₃} {hu : o₃ ⟶ o₄}
    {hr : o₄ ⟶ o₅} {hm : o₂ ⟶ o₅} (e₁ : ha = h₁ ≫ h₂) (e₂ : hm = h₂ ≫ hu ≫ hr) :
    s ≫ ha ≫ hu ≫ hr = (s ≫ h₁) ≫ hm := by
  rw [e₁, e₂]
  simp only [Category.assoc]

/-- `Stacks.DerivedFunctor.rightDerivedZeroUnit_eq` through
`Stacks.DerivedFunctor.homologyQhSingleIso`. -/
theorem rightDerivedZeroUnit_eq' (X : C) :
    Stacks.RightDerivedPlus.rightDerivedZeroUnit T X =
      (homologyQhSingleIso (T.obj X)).hom ≫
        (DerivedCategory.Plus.homologyFunctor D 0).map
          (DerivedCategory.Plus.Qh.map
              ((Functor.mapHomotopyCategoryPlusSingleFunctor T 0).inv.app X) ≫
            T.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor C 0).obj X) ≫
            T.rightDerivedFunctorPlus.map
              ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).inv.app X)) :=
  (rightDerivedZeroUnit_eq T X).trans (split_chain
    ((DerivedCategory.Plus.homologyFunctor D 0).map_comp _ _)
    (((DerivedCategory.Plus.homologyFunctor D 0).map_comp _ _).trans
      (congrArg (_ ≫ ·) ((DerivedCategory.Plus.homologyFunctor D 0).map_comp _ _))))

private theorem assoc₄ {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₄ o₅ : 𝒳} (a : o₀ ⟶ o₁)
    (b : o₁ ⟶ o₂) (c : o₂ ⟶ o₃) (d : o₃ ⟶ o₄) (e : o₄ ⟶ o₅) :
    a ≫ b ≫ c ≫ d ≫ e = (a ≫ b ≫ c ≫ d) ≫ e := by
  simp only [Category.assoc]

private theorem nat4_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₃' p₀ p₁ p₂ p₃ q : 𝒳}
    {f : q ⟶ p₀} {s : q ⟶ o₀} {m : o₀ ⟶ o₁} {u : o₁ ⟶ o₂} {r : o₂ ⟶ o₃}
    {s' : p₀ ⟶ p₁} {m' : p₁ ⟶ p₂} {u' : p₂ ⟶ p₃} {r' : p₃ ⟶ o₃'} {Hf : o₃ ⟶ o₃'}
    {a : o₀ ⟶ p₁} {b : o₁ ⟶ p₂} {c : o₂ ⟶ p₃}
    (h₀ : f ≫ s' = s ≫ a) (h₁ : a ≫ m' = m ≫ b) (h₂ : b ≫ u' = u ≫ c) (h₃ : c ≫ r' = r ≫ Hf) :
    f ≫ s' ≫ m' ≫ u' ≫ r' = s ≫ m ≫ u ≫ r ≫ Hf := by
  rw [reassoc_of% h₀, reassoc_of% h₁, reassoc_of% h₂, h₃]

/-- **`Stacks.RightDerivedPlus.rightDerivedZeroUnit` is natural.** -/
theorem rightDerivedZeroUnit_naturality {X Y : C} (f : X ⟶ Y) :
    T.map f ≫ Stacks.RightDerivedPlus.rightDerivedZeroUnit T Y =
      Stacks.RightDerivedPlus.rightDerivedZeroUnit T X ≫ (T.rightDerivedPlus 0).map f := by
  rw [rightDerivedZeroUnit_eq', rightDerivedZeroUnit_eq']
  have h₀ := homologyQhSingleIso_hom_naturality (T.map f)
  have h₁ := congrArg (fun z => (DerivedCategory.Plus.homologyFunctor D 0).map
      (DerivedCategory.Plus.Qh.map z))
    ((Functor.mapHomotopyCategoryPlusSingleFunctor T 0).inv.naturality f)
  have h₂ := congrArg (DerivedCategory.Plus.homologyFunctor D 0).map
    (T.rightDerivedFunctorPlusUnith.naturality ((HomotopyCategory.Plus.singleFunctor C 0).map f))
  have h₃ := congrArg (fun z => (DerivedCategory.Plus.homologyFunctor D 0).map
      (T.rightDerivedFunctorPlus.map z))
    ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).inv.naturality f)
  simp only [Functor.comp_map, Functor.map_comp] at h₁ h₂ h₃
  simp only [Functor.map_comp]
  exact (nat4_chain h₀ h₁ h₂ h₃).trans (assoc₄ _ _ _ _ _)

end ZeroUnit

end Stacks.DerivedFunctor

namespace Stacks.Cohomology.BaseChange

/-! ### The base change comparison at a complex concentrated in degree zero -/

section SingleComplexes

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive] (τ : F ⋙ G ⟶ G' ⋙ F')

/-- **The degreewise transformation at a complex concentrated in degree zero** is the
transformation at the object, read through `HomologicalComplex.singleMapHomologicalComplex`. -/
theorem singleMapHomologicalComplex_comp_mapHomologicalComplex_app (X : A) :
    (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).inv.app (F.obj X) ≫
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app X) ≫
      (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X) =
    (HomologicalComplex.single D (ComplexShape.up ℤ) 0).map (τ.app X) ≫
      (HomologicalComplex.singleMapHomologicalComplex F' (ComplexShape.up ℤ) 0).inv.app
        (G'.obj X) ≫
      (F'.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex G' (ComplexShape.up ℤ) 0).inv.app X) := by
  refine HomologicalComplex.from_single_hom_ext ?_
  simp only [Functor.mapHomologicalComplex_obj_X, Functor.comp_obj, HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    Functor.mapHomologicalComplex_map_f, Functor.map_comp, NatTrans.mapHomologicalComplex_app_f,
    Category.assoc, Iso.inv_hom_id_map_assoc, HomologicalComplex.single_map_f_self,
    Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
  exact τ.naturality _

private theorem map_comp₃ {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Φ : 𝒞 ⥤ 𝒟)
    {X Y Z W : 𝒞} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) :
    Φ.map (a ≫ b ≫ c) = Φ.map a ≫ Φ.map b ≫ Φ.map c := by
  simp

private theorem comp₃_congr {𝒞 : Type*} [Category* 𝒞] {X Y Z W : 𝒞} {a a' : X ⟶ Y}
    {b b' : Y ⟶ Z} {c c' : Z ⟶ W} (ha : a = a') (hb : b = b') (hc : c = c') :
    a ≫ b ≫ c = a' ≫ b' ≫ c' := by
  rw [ha, hb, hc]

/-- The image of `CategoryTheory.Functor.mapHomotopyCategoryPlusSingleFunctor` under
`CategoryTheory.Functor.mapHomotopyCategoryPlus`, read in the homotopy category. -/
private theorem ι_map_mapHomotopyCategoryPlus_map_mapHomotopyCategoryPlusSingleFunctor_inv_app
    {A B D : Type*} [Category* A] [Category* B] [Category* D] [Abelian A] [Abelian B] [Abelian D]
    (Ψ : A ⥤ B) (Φ : B ⥤ D) [Ψ.Additive] [Φ.Additive] (X : A) :
    (HomotopyCategory.Plus.ι D).map
        (Φ.mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusSingleFunctor Ψ 0).inv.app X)) =
      (Φ.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex Ψ (ComplexShape.up ℤ) 0).inv.app X)) :=
  (Stacks.DerivedIndexing.ι_map_mapHomotopyCategoryPlus_map Φ _).trans
    (congrArg (Φ.mapHomotopyCategory (ComplexShape.up ℤ)).map
      (Stacks.DerivedFunctor.ι_map_mapHomotopyCategoryPlusSingleFunctor_inv_app Ψ X))

/-- **The degreewise transformation at a complex concentrated in degree zero**, in the bounded
below homotopy category: read through `CategoryTheory.Functor.mapHomotopyCategoryPlusSingleFunctor`
it is the transformation at the object. -/
theorem mapHomotopyCategoryPlusSingleFunctor_comp_mapPlus (X : A) :
    (Functor.mapHomotopyCategoryPlusSingleFunctor G 0).inv.app (F.obj X) ≫
      G.mapHomotopyCategoryPlus.map
        ((Functor.mapHomotopyCategoryPlusSingleFunctor F 0).inv.app X) ≫
      (mapPlus τ).app ((HomotopyCategory.Plus.singleFunctor A 0).obj X) =
    (HomotopyCategory.Plus.singleFunctor D 0).map (τ.app X) ≫
      (Functor.mapHomotopyCategoryPlusSingleFunctor F' 0).inv.app (G'.obj X) ≫
      F'.mapHomotopyCategoryPlus.map
        ((Functor.mapHomotopyCategoryPlusSingleFunctor G' 0).inv.app X) := by
  apply (HomotopyCategory.Plus.ι D).map_injective
  have h := congrArg (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
    (singleMapHomologicalComplex_comp_mapHomologicalComplex_app F F' G G' τ X)
  simp only [Functor.map_comp] at h
  refine Eq.trans ?_ (Eq.trans h ?_)
  · refine (map_comp₃ _ _ _ _).trans (comp₃_congr
      (Stacks.DerivedFunctor.ι_map_mapHomotopyCategoryPlusSingleFunctor_inv_app G (F.obj X)) ?_ rfl)
    exact ι_map_mapHomotopyCategoryPlus_map_mapHomotopyCategoryPlusSingleFunctor_inv_app F G X
  · refine Eq.trans ?_ (map_comp₃ _ _ _ _).symm
    refine comp₃_congr rfl
      (Stacks.DerivedFunctor.ι_map_mapHomotopyCategoryPlusSingleFunctor_inv_app F'
        (G'.obj X)).symm ?_
    exact (ι_map_mapHomotopyCategoryPlus_map_mapHomotopyCategoryPlusSingleFunctor_inv_app
      G' F' X).symm

end SingleComplexes

section Derived

attribute [local instance] HasDerivedCategory.standard

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] (τ : F ⋙ G ⟶ G' ⋙ F')


private theorem derived_single_chain {𝒳 : Type*} [Category* 𝒳]
    {o₀ o₁ o₂ o₃ o₄ o₅ o₆ p₁ p₂ p₃ p₄ p₅ r₂ r₃ : 𝒳}
    {q₁ : o₀ ⟶ o₁} {uG : o₁ ⟶ o₂} {gq : o₂ ⟶ o₃} {gu : o₃ ⟶ o₄} {der : o₄ ⟶ o₅}
    {last : o₅ ⟶ o₆} {qτ : o₀ ⟶ p₁} {q₂ : p₁ ⟶ p₂} {uF₂ : p₂ ⟶ p₃} {si₂ : p₃ ⟶ p₄}
    {sh₂ : p₄ ⟶ p₃} {fq : p₃ ⟶ p₅} {fu : p₅ ⟶ o₅} {qmp : r₂ ⟶ r₃}
    {uF₁ : r₃ ⟶ p₅} {qgm : o₁ ⟶ r₂} {ugf : r₂ ⟶ o₃} {e' : o₃ ⟶ r₂} {qfm : p₂ ⟶ r₃}
    (ha : gu ≫ der = e' ≫ qmp ≫ uF₁ ≫ fu) (hb : uG ≫ gq = qgm ≫ ugf)
    (hc : ugf ≫ e' = 𝟙 _) (hd : q₁ ≫ qgm ≫ qmp = qτ ≫ q₂ ≫ qfm)
    (he : uF₂ ≫ fq = qfm ≫ uF₁) (hf : si₂ ≫ sh₂ = 𝟙 _) :
    q₁ ≫ uG ≫ gq ≫ gu ≫ der ≫ last =
      qτ ≫ q₂ ≫ uF₂ ≫ si₂ ≫ sh₂ ≫ fq ≫ fu ≫ last := by
  rw [reassoc_of% hf, reassoc_of% he, reassoc_of% ha, reassoc_of% hb, reassoc_of% hc,
    reassoc_of% hd]

/-- **The derived base change comparison at an object placed in degree zero.** Precomposed with
the derived-functor units of `RG` and of `RF` at the complexes concentrated in degree zero, the
comparison `Stacks.Cohomology.BaseChange.derived` at `X[0]` is the transformation `τ` at `X`,
followed by the derived-functor unit of `RF'` and by `RF'` applied to the comparison
`Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso` of the exact functor `G'`. -/
theorem derived_app_singleFunctor (X : A) :
    DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusSingleFunctor G 0).inv.app
        (F.obj X)) ≫
      G.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor B 0).obj (F.obj X)) ≫
      G.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Qh.map
            ((Functor.mapHomotopyCategoryPlusSingleFunctor F 0).inv.app X) ≫
          F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X) ≫
          F.rightDerivedFunctorPlus.map
            ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app X)) ≫
      (derived F F' G G' τ (exactUnitIso G)).app ((DerivedCategory.Plus.singleFunctor A 0).obj X) =
    DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.singleFunctor D 0).map (τ.app X)) ≫
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusSingleFunctor F' 0).inv.app
        (G'.obj X)) ≫
      F'.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj (G'.obj X)) ≫
      F'.rightDerivedFunctorPlus.map
        ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).inv.app (G'.obj X)) ≫
      F'.rightDerivedFunctorPlus.map
        ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso G' 0).hom.app X) := by
  rw [Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso_hom_app]
  have hd := (derived F F' G G' τ (exactUnitIso G)).naturality
    ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app X)
  have hG := (G.rightDerivedFunctorPlusUnith.naturality
    ((Functor.mapHomotopyCategoryPlusSingleFunctor F 0).inv.app X)).symm
  have hF' := (F'.rightDerivedFunctorPlusUnith.naturality
    ((Functor.mapHomotopyCategoryPlusSingleFunctor G' 0).inv.app X)).symm
  simp only [Functor.comp_map] at hd hG hF'
  have ha := (derived_fac_app F F' G G' τ (exactUnitIso G)
    ((HomotopyCategory.Plus.singleFunctor A 0).obj X)).trans
    (onHomotopy_app F F' G G' τ (exactUnitIso G) ((HomotopyCategory.Plus.singleFunctor A 0).obj X))
  have hd' := congrArg DerivedCategory.Plus.Qh.map
    (mapHomotopyCategoryPlusSingleFunctor_comp_mapPlus F F' G G' τ X)
  have hd'' := ((congrArg (_ ≫ ·) (DerivedCategory.Plus.Qh.map_comp _ _)).symm.trans
    ((DerivedCategory.Plus.Qh.map_comp _ _).symm.trans hd')).trans
    ((DerivedCategory.Plus.Qh.map_comp _ _).trans
      (congrArg (_ ≫ ·) (DerivedCategory.Plus.Qh.map_comp _ _)))
  simp only [Functor.map_comp, Category.assoc]
  rw [hd]
  exact derived_single_chain ha hG
    ((exactUnitIso G).hom_inv_id_app _) hd'' hF'
    (F'.rightDerivedFunctorPlus.mapIso
      ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).app (G'.obj X))).inv_hom_id

private theorem cancel_last {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ : 𝒳} {l : o₀ ⟶ o₂}
    {r : o₀ ⟶ o₁} {e : o₁ ⟶ o₂} {e' : o₂ ⟶ o₁} (h : l = r ≫ e) (he : e ≫ e' = 𝟙 _) :
    l ≫ e' = r := by
  rw [h, Category.assoc, he, Category.comp_id]

/-- `Stacks.Cohomology.BaseChange.derived_app_singleFunctor`, with the comparison of the exact
functor `G'` moved to the left. -/
theorem derived_app_singleFunctor' (X : A) :
    (DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusSingleFunctor G 0).inv.app
        (F.obj X)) ≫
      G.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor B 0).obj (F.obj X)) ≫
      G.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Qh.map
            ((Functor.mapHomotopyCategoryPlusSingleFunctor F 0).inv.app X) ≫
          F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X) ≫
          F.rightDerivedFunctorPlus.map
            ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app X)) ≫
      (derived F F' G G' τ (exactUnitIso G)).app ((DerivedCategory.Plus.singleFunctor A 0).obj X)) ≫
      F'.rightDerivedFunctorPlus.map
        ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso G' 0).inv.app X) =
    DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.singleFunctor D 0).map (τ.app X)) ≫
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusSingleFunctor F' 0).inv.app
        (G'.obj X)) ≫
      F'.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj (G'.obj X)) ≫
      F'.rightDerivedFunctorPlus.map
        ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).inv.app (G'.obj X)) := by
  refine cancel_last ((derived_app_singleFunctor F F' G G' τ X).trans ?_)
    (F'.rightDerivedFunctorPlus.mapIso
      ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso G' 0).app X)).hom_inv_id
  simp only [Category.assoc]
  rfl

private theorem zero_chain {𝒳 : Type*} [Category* 𝒳]
    {o₀ o₁ o₂ o₃ o₄ o₅ q₀ q₃ q₅ q₆ q₇ : 𝒳}
    {gall : o₀ ⟶ o₂} {gσ : o₀ ⟶ o₁} {gφ : o₁ ⟶ o₂} {x : o₂ ⟶ o₃} {d : o₃ ⟶ o₄}
    {l : o₄ ⟶ o₅} {x₀ : o₁ ⟶ q₀} {hRφ : q₀ ⟶ o₃} {ei : q₀ ⟶ q₃} {uG : q₃ ⟶ q₀}
    {σD : o₀ ⟶ q₅} {μ : q₅ ⟶ q₃} {τ : o₀ ⟶ q₆} {σD' : q₆ ⟶ q₇} {hτ : q₅ ⟶ q₇}
    {hrest : q₇ ⟶ o₅}
    (hg : gall = gσ ≫ gφ) (hnat : gφ ≫ x = x₀ ≫ hRφ) (hei : ei ≫ uG = 𝟙 _)
    (h₂ : gσ ≫ x₀ ≫ ei = σD ≫ μ) (hD : μ ≫ uG ≫ hRφ ≫ d ≫ l = hτ ≫ hrest)
    (hσ : τ ≫ σD' = σD ≫ hτ) :
    gall ≫ x ≫ d ≫ l = τ ≫ σD' ≫ hrest := by
  have h₂' : gσ ≫ x₀ = σD ≫ μ ≫ uG := by
    rw [← reassoc_of% h₂, hei, Category.comp_id]
  rw [hg, Category.assoc, reassoc_of% hnat, reassoc_of% h₂', hD, reassoc_of% hσ]

private theorem map_comp₅ {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Φ : 𝒞 ⥤ 𝒟)
    {X₀ X₁ X₂ X₃ X₄ X₅ : 𝒞} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄)
    (e : X₄ ⟶ X₅) :
    Φ.map ((a ≫ b ≫ c ≫ d) ≫ e) = Φ.map a ≫ Φ.map b ≫ Φ.map c ≫ Φ.map d ≫ Φ.map e := by
  simp

/-- **The base change map in degree zero, before the comparison of indexings**: the identification
`Stacks.RightDerivedPlus.rightDerivedZeroUnit` of `F` with `R⁰F`, followed by `H⁰` of the derived
base change comparison at `X[0]` read through the two comparisons of the exact functors `G` and
`G'`, is `τ` followed by the identification of `F'` with `R⁰F'`. -/
theorem map_rightDerivedZeroUnit_comp_derived (X : A) :
    G.map (Stacks.RightDerivedPlus.rightDerivedZeroUnit F X) ≫
      (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso G 0).inv.app
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)) ≫
      (DerivedCategory.Plus.homologyFunctor D 0).map
        ((derived F F' G G' τ (exactUnitIso G)).app
          ((DerivedCategory.Plus.singleFunctor A 0).obj X)) ≫
      (DerivedCategory.Plus.homologyFunctor D 0).map (F'.rightDerivedFunctorPlus.map
        ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso G' 0).inv.app X)) =
    τ.app X ≫ Stacks.RightDerivedPlus.rightDerivedZeroUnit F' (G'.obj X) := by
  rw [Stacks.DerivedFunctor.rightDerivedZeroUnit_eq',
    Stacks.DerivedFunctor.rightDerivedZeroUnit_eq']
  have hnat := (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso G 0).inv.naturality
    (DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusSingleFunctor F 0).inv.app X) ≫
      F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X) ≫
      F.rightDerivedFunctorPlus.map ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app X))
  have h₂ := Stacks.DerivedFunctor.map_homologyQhSingleIso_hom_comp G (F.obj X)
  have hD := (map_comp₅ (DerivedCategory.Plus.homologyFunctor D 0) _ _ _ _ _).symm.trans
    ((congrArg (DerivedCategory.Plus.homologyFunctor D 0).map
      (derived_app_singleFunctor' F F' G G' τ X)).trans
      ((DerivedCategory.Plus.homologyFunctor D 0).map_comp _ _))
  have hσ := Stacks.DerivedFunctor.homologyQhSingleIso_hom_naturality (τ.app X)
  exact zero_chain (G.map_comp (Stacks.DerivedFunctor.homologyQhSingleIso (F.obj X)).hom _) hnat
    ((DerivedCategory.Plus.homologyFunctor D 0).mapIso
      ((exactUnitIso G).app ((HomotopyCategory.Plus.singleFunctor B 0).obj (F.obj X)))).inv_hom_id
    h₂ hD hσ

end Derived

end Stacks.Cohomology.BaseChange

namespace Stacks.EtaleCohomology

open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u

section BaseChangeSquare

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

private theorem zero_bc_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₄ o₅ o₆ p₁ : 𝒳}
    {gab : o₀ ⟶ o₂} {ga : o₀ ⟶ o₁} {gb : o₁ ⟶ o₂} {gc : o₂ ⟶ o₁} {ε : o₁ ⟶ o₃}
    {d : o₃ ⟶ o₄} {l : o₄ ⟶ o₅} {r : o₅ ⟶ o₆} {τ : o₀ ⟶ p₁} {μ : p₁ ⟶ o₅}
    (hg : gab = ga ≫ gb) (hb : gb ≫ gc = 𝟙 _) (key : ga ≫ ε ≫ d ≫ l = τ ≫ μ) :
    gab ≫ (gc ≫ ε) ≫ d ≫ (l ≫ r) = τ ≫ μ ≫ r := by
  rw [hg]
  simp only [Category.assoc]
  rw [reassoc_of% hb, reassoc_of% key]

/-- **The base change map on higher direct images in degree zero is the underived base change
map.** Read through the identifications `F ⟶ R⁰F` of the two left exact direct images with
their degree-zero right derived functors — `Stacks.RightDerivedPlus.rightDerivedZeroUnit`
followed by the comparison `Stacks.DerivedIndexing.rightDerivedIso` of the two indexings —
the base change map `Stacks.EtaleCohomology.higherBaseChangeMapAb` in degree `0` is the mate
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb` of the square. -/
theorem map_rightDerivedZeroUnit_comp_higherBaseChangeMapAb_zero
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    (smallEtalePullbackAb f').map
        (Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb g) F ≫
          (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) 0).inv.app F) ≫
      (higherBaseChangeMapAb f' g h e w 0).app F =
    (smallEtaleBaseChangeAb f' g h e w).app F ≫
      Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb h)
        ((smallEtalePullbackAb e).obj F) ≫
      (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb h) 0).inv.app
        ((smallEtalePullbackAb e).obj F) := by
  have key := Stacks.Cohomology.BaseChange.map_rightDerivedZeroUnit_comp_derived
    (smallEtalePushforwardAb g) (smallEtalePushforwardAb h) (smallEtalePullbackAb f')
    (smallEtalePullbackAb e) (smallEtaleBaseChangeAb f' g h e w) F
  have hdef : (higherBaseChangeMapAb f' g h e w 0).app F =
      ((smallEtalePullbackAb f').map
          ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) 0).hom.app F) ≫
        (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (smallEtalePullbackAb f') 0).inv.app
          ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj
              F))) ≫
      (DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0).map
        ((smallEtaleDerivedBaseChangeAb f' g h e w).app
          ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj
            F)) ≫
      ((DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0).map
          ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.map
            ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
              (smallEtalePullbackAb e) 0).inv.app F)) ≫
        (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb h) 0).inv.app
          ((smallEtalePullbackAb e).obj F)) := rfl
  rw [hdef]
  exact zero_bc_chain ((smallEtalePullbackAb f').map_comp _ _)
    ((smallEtalePullbackAb f').mapIso
      ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) 0).app F)).inv_hom_id
    key

end BaseChangeSquare

end Stacks.EtaleCohomology
