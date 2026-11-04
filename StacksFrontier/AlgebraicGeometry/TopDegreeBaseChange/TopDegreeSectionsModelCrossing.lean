module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineOpenCohomologyIndexing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EdgeCompatPreimageSections
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SourceSectionsNormalisation
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDirectImageSectionsDerived

/-!
# The two models of the top higher direct image, on sections over an open

For a quasi-compact quasi-separated morphism of schemes `f : X ⟶ Y`, an affine open `V ⊆ Y`, a
quasi-coherent `𝒪_X`-module `F` and a degree `d` above which `Rf_*(F[0])` has no cohomology, this
file identifies the sections `Γ(V, H^d(Rf_*(F[0])))` of the derived model of the top higher direct
image with the cohomology `H^d(f⁻¹V, F|)` of the restricted situation, and through it with
`Γ(R^d f_* F, V)` ([Stacks, Tag 01XK]). These are the two models met in conclusion (c) of
[Stacks, Tag 0EX3].

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.restrictScalarsSquareObjIso`: restricting scalars
  along either side of a commuting square of ring maps gives isomorphic modules.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.preimageSectionsCohomologyIso`: the two readings
  of the scalars on the cohomology over `f⁻¹V` agree.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPreimageSectionsIsoAffineOpenCohomology`:
  `H^d(RΓ(f⁻¹V, F[0])) ≅ H^d(f⁻¹V, F|)`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDirectImageSectionsIsoAffineOpenCohomology`:
  `Γ(V, H^d(Rf_*(F[0]))) ≅ H^d(f⁻¹V, F|)`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDegreeSectionsModelCrossing`:
  `Γ(V, H^d(Rf_*(F[0]))) ≅ Γ(R^d f_* F, V)`, factored through `H^d(f⁻¹V, F|)`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.app_comp_topIso_inv` and
  `Stacks.AlgebraicGeometry.TopDegreeBaseChange.app_comp_topIso_inv_hom`: the two maps from the
  functions on `V` to the functions on the open subscheme `f⁻¹V`, along `f` and along `f ∣_ V`,
  agree.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDegreeSectionsModelCrossing_hom`: the forward
  map of `topDegreeSectionsModelCrossing` is the composite of its two factors.

## Implementation notes

`derivedPreimageSectionsHomologyIso` restricts scalars on the cohomology over `f⁻¹V` first along
`AlgebraicGeometry.Scheme.Opens.topIso` at `f⁻¹V` and then along `f^♯` at `V`, while
`affineOpenCohomology` restricts first along `(f ∣_ V)^♯` and then along `topIso` at `V`. The two
composites are equal ring maps, so the modules are identified by
`restrictScalarsSquareObjIso`, which is stated for arbitrary ring maps.

The cohomology of the restricted situation is Mathlib's `ℕ`-indexed
`CategoryTheory.Functor.rightDerived`, so the degree is a natural number, and the derived model is
read at `(d : ℤ)`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open DerivedCategory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.Cohomology.DerivedSectionsLeray (derivedPreimageSections sectionsOverOpen)

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Restriction of scalars along two equal composites, at variables -/

/-- If `b ∘ a = b' ∘ a'`, then restricting a `T`-module along `b` and then along `a` gives an
`R`-module isomorphic to restricting it along `b'` and then along `a'`. -/
def restrictScalarsSquareObjIso {R S S' T : Type u} [Ring R] [Ring S] [Ring S'] [Ring T]
    (a : R →+* S) (b : S →+* T) (a' : R →+* S') (b' : S' →+* T) (h : b.comp a = b'.comp a')
    (M : ModuleCat.{u} T) :
    (ModuleCat.restrictScalars a).obj ((ModuleCat.restrictScalars b).obj M) ≅
      (ModuleCat.restrictScalars a').obj ((ModuleCat.restrictScalars b').obj M) :=
  (ModuleCat.restrictScalarsComp'App a b (b.comp a) rfl M).symm ≪≫
    (ModuleCat.restrictScalarsCongr h).app M ≪≫
      ModuleCat.restrictScalarsComp'App a' b' (b'.comp a') rfl M

/-! ### The two routes from the functions on `V` to the functions on `f⁻¹V` -/

variable {X Y : Scheme.{u}}

/-- Pulling a section of `𝒪_Y` over `V` back along `f` and then reading it on the open subscheme
`f⁻¹V` is the same as reading it on the open subscheme `V` and pulling it back along the restricted
morphism `f ∣_ V`. -/
theorem app_comp_topIso_inv (f : X ⟶ Y) (V : Y.Opens) :
    f.app V ≫ (Scheme.Opens.topIso (f ⁻¹ᵁ V)).inv =
      (Scheme.Opens.topIso V).inv ≫ (f ∣_ V).appTop := by
  have h : (f ∣_ V).appTop =
      (Scheme.Opens.topIso V).hom ≫ f.appLE V (f ⁻¹ᵁ V) le_rfl ≫
        (Scheme.Opens.topIso (f ⁻¹ᵁ V)).inv := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  rw [h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp, Scheme.Hom.app_eq_appLE]

/-- `app_comp_topIso_inv` as an equality of ring homomorphisms. -/
theorem app_comp_topIso_inv_hom (f : X ⟶ Y) (V : Y.Opens) :
    ((Scheme.Opens.topIso (f ⁻¹ᵁ V)).inv.hom).comp ((f.app V).hom) =
      ((f ∣_ V).appTop.hom).comp ((Scheme.Opens.topIso V).inv.hom) :=
  congrArg CommRingCat.Hom.hom (app_comp_topIso_inv f V)

/-! ### The crossing -/

/-- The degree-`d` cohomology of the restriction of `F` to the open subscheme `f⁻¹V`, with
scalars restricted first along `AlgebraicGeometry.Scheme.Opens.topIso` at `f⁻¹V` and then along
`f^♯` at `V`, is isomorphic to `affineOpenCohomologyNat f V F d`, where the scalars are restricted
first along `(f ∣_ V)^♯` and then along `topIso` at `V`. -/
def preimageSectionsCohomologyIso (f : X ⟶ Y) (V : Y.Opens) (F : X.Modules) (d : ℕ) :
    (ModuleCat.restrictScalars (f.app V).hom).obj
        ((ModuleCat.restrictScalars (Scheme.Opens.topIso (f ⁻¹ᵁ V)).inv.hom).obj
          (((Stacks.Cohomology.AffineBase.moduleGlobalSections
                (f ⁻¹ᵁ V : Scheme)).rightDerived d).obj
            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F))) ≅
      affineOpenCohomologyNat f V F d :=
  restrictScalarsSquareObjIso _ _ _ _ (app_comp_topIso_inv_hom f V) _

/-- For a morphism of schemes `f : X ⟶ Y`, an open `V ⊆ Y`, a sheaf of `𝒪_X`-modules `F` and a
degree `d`,

> `H^d(RΓ(f⁻¹V, F[0])) ≅ H^d(f⁻¹V, F|_{f⁻¹V})`

as `Γ(Y, V)`-modules, where the left-hand side is
`Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections` ([Stacks, Tag 0D5W]) and the
right-hand side is `affineOpenCohomology f V F d`. -/
def derivedPreimageSectionsIsoAffineOpenCohomology (f : X ⟶ Y) (V : Y.Opens) (F : X.Modules)
    (d : ℕ) :
    (homologyFunctor (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V)))
          (d : ℤ)).obj
        ((derivedPreimageSections f.toLRSHom.toShHom V).obj
          ((singleFunctor X.Modules 0).obj F)) ≅
      affineOpenCohomology f V F d :=
  derivedPreimageSectionsHomologyIso f V F d ≪≫ preimageSectionsCohomologyIso f V F d ≪≫
    affineOpenCohomologyNatIso f V F d

/-- Let `f : X ⟶ Y` be quasi-compact and quasi-separated, let `V ⊆ Y` be an affine open, let `F`
be a quasi-coherent `𝒪_X`-module and let `d` be a degree above which `Rf_*(F[0])` has no
cohomology. Then

> `Γ(V, H^d(Rf_*(F[0]))) ≅ H^d(f⁻¹V, F|_{f⁻¹V})`

as `Γ(Y, V)`-modules. -/
def topDirectImageSectionsIsoAffineOpenCohomology (f : X ⟶ Y) (hqc : QuasiCompact f)
    (hqs : QuasiSeparated f) {V : Y.Opens} (hV : IsAffineOpen V) (F : X.Modules)
    (hF : F.IsQuasicoherent) (d : ℕ)
    (hLE : ((derivedPushforward f.toLRSHom.toShHom).obj
      ((singleFunctor X.Modules 0).obj F)).IsLE (d : ℤ)) :
    (sectionsOverOpen Y.toRingedSpace V).obj
        ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) (d : ℤ)).obj
          ((derivedPushforward f.toLRSHom.toShHom).obj
            ((singleFunctor X.Modules 0).obj F))) ≅
      affineOpenCohomology f V F d :=
  have := hqc
  have := hqs
  have := hF
  topDirectImageSectionsIsoDerivedSections f V hV F (d : ℤ) hLE ≪≫
    derivedPreimageSectionsIsoAffineOpenCohomology f V F d

/-- Let `f : X ⟶ Y` be quasi-compact and quasi-separated, let `V ⊆ Y` be an affine open, let `F`
be a quasi-coherent `𝒪_X`-module and let `d` be a degree above which `Rf_*(F[0])` has no
cohomology. Then

> `Γ(V, H^d(Rf_*(F[0]))) ≅ Γ(R^d f_* F, V)`,

identifying the sections over `V` of the derived model with those of the `ℤ`-indexed
`CategoryTheory.Functor.rightDerivedPlus` model, as the composite of
`topDirectImageSectionsIsoAffineOpenCohomology` and `affineOpenCohomologyIsoSectionsOf`
([Stacks, Tag 01XK]). -/
def topDegreeSectionsModelCrossing (f : X ⟶ Y) (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    {V : Y.Opens} (hV : IsAffineOpen V) (F : X.Modules) (hF : F.IsQuasicoherent) (d : ℕ)
    (hLE : ((derivedPushforward f.toLRSHom.toShHom).obj
      ((singleFunctor X.Modules 0).obj F)).IsLE (d : ℤ)) :
    (sectionsOverOpen Y.toRingedSpace V).obj
        ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) (d : ℤ)).obj
          ((derivedPushforward f.toLRSHom.toShHom).obj
            ((singleFunctor X.Modules 0).obj F))) ≅
      ModuleCat.of Γ(Y, V)
        Γ(((Scheme.Modules.pushforward f).rightDerivedPlus (d : ℤ)).obj F, V) :=
  topDirectImageSectionsIsoAffineOpenCohomology f hqc hqs hV F hF d hLE ≪≫
    affineOpenCohomologyIsoSectionsOf f hqc hqs hV F hF d

/-- The forward map of `topDegreeSectionsModelCrossing` is the forward map of
`topDirectImageSectionsIsoAffineOpenCohomology` followed by that of
`affineOpenCohomologyIsoSectionsOf`. -/
theorem topDegreeSectionsModelCrossing_hom (f : X ⟶ Y) (hqc : QuasiCompact f)
    (hqs : QuasiSeparated f) {V : Y.Opens} (hV : IsAffineOpen V) (F : X.Modules)
    (hF : F.IsQuasicoherent) (d : ℕ)
    (hLE : ((derivedPushforward f.toLRSHom.toShHom).obj
      ((singleFunctor X.Modules 0).obj F)).IsLE (d : ℤ)) :
    (topDegreeSectionsModelCrossing f hqc hqs hV F hF d hLE).hom =
      (topDirectImageSectionsIsoAffineOpenCohomology f hqc hqs hV F hF d hLE).hom ≫
        (affineOpenCohomologyIsoSectionsOf f hqc hqs hV F hF d).hom :=
  rfl

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
