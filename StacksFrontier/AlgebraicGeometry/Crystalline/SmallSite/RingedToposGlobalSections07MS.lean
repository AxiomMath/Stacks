module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeMapSheaf07MS
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusSemilinearAction
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedGlobalSectionsOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsRingHomOnSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.BoundedBelowRestriction
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedAlongEquivalence

/-!
# Derived global sections on the crystalline and Zariski ringed topoi, for 07MS

The base change map (07MT) of [Stacks, Tag 07MS] on global sections is obtained from the
sheaf-level base change map `L(S' → S)^* Rτ_{X'/S', *}F' ⟶ Rτ_{X/S, *}F` by applying derived
global sections on `S`, and reading `RΓ(S, Rτ_{X/S, *}F)` as `RΓ(Cris(X/S), F)`. This file
supplies the three pieces of that passage, in the chapter's vocabulary.

* `zariskiDerivedGlobalSections Z`: unbounded derived global sections on the Zariski ringed topos
  of a scheme `Z`, as `Γ(Z, 𝒪_Z)`-modules, on the chapter's model of `D(Γ(Z, 𝒪_Z))`.
* `tauDerivedGlobalSectionsIso`: `RΓ(S, Rτ_{X/S, *}F) = RΓ(Cris(X/S), F)` in `D(A)`, the right
  hand side the chapter's `...SmallSite.derivedModuleGlobalSections`, by the Leray identification
  of [Stacks, Tag 0D6H] for the structure morphism `τ_{X/S}` of [Stacks, Tag 07IM].
* `zariskiBaseChangeGlobalSectionsMap`: the canonical map
  `RΓ(S', K) ⊗^L_{A'} A ⟶ RΓ(S, Lg^*K)` for the Zariski morphism `g : S ⟶ S'` of a morphism of
  divided power bases, the transpose across `- ⊗^L_{A'} A ⊣ res` ([Stacks, Tag 0GMT]) of
  `RΓ(S', -)` of the unit `K ⟶ Rg_* Lg^*K`, read through the Leray identification for `g`.

## The rings

The Zariski ringed topos of `Z` carries `𝒪_Z` with its sections raised to `Type (u + 1)`, and the
crystalline ringed topos `𝒪_{X/S}` likewise, so their rings of global sections are not `Γ(Z, 𝒪_Z)`
and `Γ(Cris(X/S), 𝒪_{X/S})`; `zariskiBaseRingHom` and `crisBaseRingULift` are the ring maps from
`Γ(Z, 𝒪_Z)`, resp. `A = Γ(S, 𝒪_S)`, through which the chapter's scalars act. The ring map on
global sections of a morphism of ringed topoi is built abstractly
(`Stacks.Cohomology.LerayOfToposHom.toposGlobalSectionsRingHom`); it is computed here on these
generators (`toposGlobalSectionsRingHom_zariskiRingedHom_comp`,
`toposGlobalSectionsRingHom_structureRingedHom_comp`), by
`Stacks.Cohomology.SiteModules.globalSectionsRingHom_val_eq`.

## References

* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 07IM](https://stacks.math.columbia.edu/tag/07IM)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf AlgebraicGeometry
  TopologicalSpace Opposite
open Stacks.Cohomology.DerivedPushforward Stacks.Cohomology.DerivedPullbackOfToposHom

universe u wA wA' wS

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The Zariski ringed topos -/

section Zariski

variable (Z : Scheme.{u})

/-- The sheaf of rings underlying the structure sheaf of the Zariski ringed topos of `Z`: `𝒪_Z`
with its sections raised to `Type (u + 1)`. -/
abbrev zariskiRingSheaf : Sheaf (Opens.grothendieckTopology Z.carrier) RingCat.{u + 1} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u + 1} (J := (zariskiRingedTopos Z).J))
    (zariskiRingedTopos Z).O

/-- **`Γ(Z, 𝒪_Z)` acts on the Zariski ringed topos of `Z`**: a global function is sent to the
compatible family of its restrictions, raised to the universe `u + 1`. -/
def zariskiBaseRingHom :
    Γ(Z, ⊤) →+* RingCat.sectionsSubring (zariskiRingSheaf Z).obj where
  toFun a := ⟨fun V ↦ ULift.up ((Z.presheaf.map (homOfLE le_top).op).hom a), fun {V V'} g ↦
    congrArg ULift.up (by
      change (Z.presheaf.map g).hom ((Z.presheaf.map (homOfLE le_top).op).hom a) =
        (Z.presheaf.map (homOfLE le_top).op).hom a
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl)⟩
  map_one' := Subtype.ext (funext fun V ↦ congrArg ULift.up (map_one _))
  map_mul' a b := Subtype.ext (funext fun V ↦ congrArg ULift.up (map_mul _ a b))
  map_zero' := Subtype.ext (funext fun V ↦ congrArg ULift.up (map_zero _))
  map_add' a b := Subtype.ext (funext fun V ↦ congrArg ULift.up (map_add _ a b))

/-- The section of `zariskiBaseRingHom Z a` over an open `V` is the restriction of `a` to `V`,
raised to the universe `u + 1`. -/
@[simp]
theorem zariskiBaseRingHom_apply_val (a : Γ(Z, ⊤)) (V : (Opens Z.carrier)ᵒᵖ) :
    (zariskiBaseRingHom Z a).1 V = ULift.up ((Z.presheaf.map (homOfLE le_top).op).hom a) :=
  rfl

variable [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(Z, ⊤))]

/-- **Unbounded derived global sections on the Zariski ringed topos of `Z`**,
`RΓ(Z, -) : D(𝒪_Z) ⥤ D(Γ(Z, 𝒪_Z))`: the total right derived functor of global sections of
sheaves of `𝒪_Z`-modules, read as `Γ(Z, 𝒪_Z)`-modules through `zariskiBaseRingHom`, landing on
the model of `D(Γ(Z, 𝒪_Z))` given as instance argument. -/
abbrev zariskiDerivedGlobalSections :
    DerivedCategory (SheafOfModules.{u + 1} (zariskiRingSheaf Z)) ⥤
      DerivedCategory (ModuleCat.{u + 1} Γ(Z, ⊤)) :=
  Stacks.DerivedFunctor.totalRightDerived
    (Stacks.Cohomology.SiteModules.globalSectionsFunctor (zariskiRingSheaf Z) ⋙
      ModuleCat.restrictScalars (zariskiBaseRingHom Z))

end Zariski

/-! ### The ring map of the Zariski morphism of a morphism of schemes -/

section ZariskiHom

variable {Z Z' : Scheme.{u}} (φ : Z ⟶ Z')

/-- Restricting sections of a scheme from `⊤` to `⊤` is the identity. -/
private theorem presheaf_map_homOfLE_top (X : Scheme.{u}) :
    X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ :=
  X.presheaf.map_id _

/-- The sections over `⊤` of the direct image along the Zariski morphism of `φ`, restricted to an
open `V` of `Z`: the direct image is restriction along `Opens.map φ.base`, so its sections over
`⊤` are the sections over `φ⁻¹(⊤) = ⊤`. -/
def zariskiTopSectionsRestrict (V : (Opens Z.carrier)ᵒᵖ) :
    (StacksZariskiSite.opensMapMorphismOfTopoi φ.base).pushforward ⋙
        sectionsFunctor (Opens.grothendieckTopology Z'.carrier) (op ⊤) ⟶
      sectionsFunctor (Opens.grothendieckTopology Z.carrier) V where
  app F := TypeCat.ofHom fun x ↦
    F.obj.map (homOfLE (fun _ _ ↦ Set.mem_univ _) : V.unop ⟶ (Opens.map φ.base).obj ⊤).op x
  naturality F G m := by
    ext x
    exact (NatTrans.naturality_apply m.hom _ x).symm

/-- **The ring map on global sections of the Zariski morphism of `φ : Z ⟶ Z'`** is `φ^♯` on
global functions: read through `zariskiBaseRingHom`, it is `Γ(φ) : Γ(Z', 𝒪_{Z'}) ⟶ Γ(Z, 𝒪_Z)`.
This is `Stacks.Cohomology.SiteModules.globalSectionsRingHom_val_eq` with the restriction of the
sections over `⊤` of the direct image, which are sections over `φ⁻¹(⊤) = ⊤`. -/
theorem toposGlobalSectionsRingHom_zariskiRingedHom_comp :
    (Stacks.Cohomology.LerayOfToposHom.toposGlobalSectionsRingHom (zariskiRingedHom φ)).comp
        (zariskiBaseRingHom Z') =
      (zariskiBaseRingHom Z).comp (Scheme.Γ.map φ.op).hom := by
  refine RingHom.ext fun a ↦ Subtype.ext (funext fun V ↦ ?_)
  refine (Stacks.Cohomology.SiteModules.globalSectionsRingHom_val_eq
    (zariskiRingedHom φ).toModulesHom (zariskiTopSectionsRestrict φ V) _).trans ?_
  show ULift.up ((Z.presheaf.map _).hom ((φ.c.app (op ⊤)).hom
      ((Z'.presheaf.map (homOfLE le_top).op).hom a))) =
    ULift.up ((Z.presheaf.map (homOfLE le_top).op).hom ((Scheme.Γ.map φ.op).hom a))
  rw [presheaf_map_homOfLE_top]
  rfl

end ZariskiHom

/-! ### The crystalline ringed topos -/

section Crystalline

variable (S : GlobalCrystallineSituation.{u})

/-- **`A = Γ(S, 𝒪_S)` acts on the crystalline ringed topos**: `...SmallSite.baseRingHom`, which
sends `a` to the family of its pullbacks along the structure morphisms `T ⟶ S`, with the
sections raised to the universe `u + 1` of `crisRingedTopos S`. -/
def crisBaseRingULift : Γ(S.S.scheme, ⊤) →+* RingCat.sectionsSubring (crisRingSheaf S).obj where
  toFun a := ⟨fun A ↦ ULift.up ((baseRingHom S a).1 A), fun g ↦
    congrArg ULift.up ((baseRingHom S a).2 g)⟩
  map_one' := Subtype.ext (funext fun A ↦ congrArg ULift.up
    (congrArg (fun x : crystallineSectionRing S ↦ x.1 A) (map_one (baseRingHom S))))
  map_mul' a b := Subtype.ext (funext fun A ↦ congrArg ULift.up
    (congrArg (fun x : crystallineSectionRing S ↦ x.1 A) (map_mul (baseRingHom S) a b)))
  map_zero' := Subtype.ext (funext fun A ↦ congrArg ULift.up
    (congrArg (fun x : crystallineSectionRing S ↦ x.1 A) (map_zero (baseRingHom S))))
  map_add' a b := Subtype.ext (funext fun A ↦ congrArg ULift.up
    (congrArg (fun x : crystallineSectionRing S ↦ x.1 A) (map_add (baseRingHom S) a b)))

/-- The section of `crisBaseRingULift S a` at a thickening `A` is the section of
`baseRingHom S a` at `A`, raised to the universe `u + 1`. -/
@[simp]
theorem crisBaseRingULift_apply_val (a : Γ(S.S.scheme, ⊤)) (A : (CrystallineThickening S)ᵒᵖ) :
    (crisBaseRingULift S a).1 A = ULift.up ((baseRingHom S a).1 A) :=
  rfl

/-- **The ring map on global sections of `τ_{X/S}` is the pullback of functions along the
structure morphisms**: read through `zariskiBaseRingHom` and `crisBaseRingULift`, it is the
identity of `A = Γ(S, 𝒪_S)`. This is `Stacks.Cohomology.SiteModules.globalSectionsRingHom_val_eq`
with the projection of the sections over `S` of `τ_{X/S, *}` to an object `(U, T, δ)`, at which
`τ^♯` is the pullback along `T ⟶ S` (`...SmallSite.structureRingedHom_forgetFSharp_proj`). -/
theorem toposGlobalSectionsRingHom_structureRingedHom_comp :
    (Stacks.Cohomology.LerayOfToposHom.toposGlobalSectionsRingHom (structureRingedHom S)).comp
        (zariskiBaseRingHom S.S.scheme) =
      crisBaseRingULift S := by
  refine RingHom.ext fun a ↦ Subtype.ext (funext fun A ↦ ?_)
  have hA : (forgetToOpens S).obj A.unop ≤ sourceToBase S ⁻¹ᵁ ⊤ := fun _ _ ↦ trivial
  let j : StructureIndex S ⊤ := StructuredArrow.mk (Y := A) (homOfLE hA).op
  refine (Stacks.Cohomology.SiteModules.globalSectionsRingHom_val_eq
    (structureRingedHom S).toModulesHom (structureProjection S ⊤ j) _).trans ?_
  refine (structureRingedHom_forgetFSharp_proj S ⊤ _ j).trans ?_
  show ULift.up ((A.unop.obj.toBase.hom.appLE ⊤ ⊤ _).hom
      ((S.S.scheme.presheaf.map (homOfLE le_top).op).hom a)) =
    ULift.up ((Scheme.Γ.map A.unop.obj.toBase.hom.op).hom a)
  rw [presheaf_map_homOfLE_top, Scheme.Hom.appLE, Scheme.Γ_map_op]
  refine congrArg ULift.up ?_
  show (A.unop.obj.thickening.target.scheme.presheaf.map (homOfLE _).op).hom
      ((A.unop.obj.toBase.hom.appTop).hom a) = (A.unop.obj.toBase.hom.appTop).hom a
  rw [presheaf_map_homOfLE_top]
  rfl

end Crystalline

section CrystallineGlobalSections

variable (S : GlobalCrystallineSituation.{u})

/-- **Global sections on the crystalline ringed topos are the chapter's global sections**: for a
sheaf `M` of `𝒪_{X/S}`-modules, `Γ(Cris(X/S), M)` computed on `crisRingedTopos S` (through
`crisModuleEquivalence`, which changes neither the sections nor the maps) and read as an
`A`-module through `crisBaseRingULift` is `...SmallSite.baseModuleGlobalSections S M`. -/
def crisRingedGlobalSectionsIso :
    (crisModuleEquivalence S).functor ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor (crisRingSheaf S) ⋙
          ModuleCat.restrictScalars (crisBaseRingULift S) ≅
      baseModuleGlobalSections S :=
  NatIso.ofComponents (fun M ↦ (AddEquiv.toLinearEquiv
    (M := ↑(((crisModuleEquivalence S).functor ⋙
      Stacks.Cohomology.SiteModules.globalSectionsFunctor (crisRingSheaf S) ⋙
        ModuleCat.restrictScalars (crisBaseRingULift S)).obj M))
    (M₂ := ↑((baseModuleGlobalSections S).obj M)) (by rfl) (fun _ _ ↦ rfl)).toModuleIso)
    (fun _ ↦ rfl)

/-- The equivalence `crisModuleEquivalence S` is additive, its functor being
`...SmallSite.moduleRingULiftUp S`. -/
instance additive_crisModuleEquivalence_functor : (crisModuleEquivalence S).functor.Additive :=
  additive_moduleRingULiftUp S

variable [HasDerivedCategory.{wS} (ModuleSheaf S)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]

/-- **`RΓ(S, Rτ_{X/S, *}F) = RΓ(Cris(X/S), F)`**, for a sheaf `F` of `𝒪_{X/S}`-modules: derived
global sections on the Zariski ringed topos of `S` of the derived direct image along the
structure morphism `τ_{X/S}` of [Stacks, Tag 07IM] are the chapter's `RΓ(Cris(X/S), F)` in
`D(A)`.

It is the Leray identification of [Stacks, Tag 0D6H] for `τ_{X/S}`
(`Stacks.Cohomology.LerayOfToposHom.derivedGlobalSectionsPushforwardIso`), read over `A` through
`toposGlobalSectionsRingHom_structureRingedHom_comp`, followed by the transport of unbounded
derived global sections across `crisModuleEquivalence` and the identification of the bounded below
right derived functor with the restriction of the unbounded one. -/
def tauDerivedGlobalSectionsIso (F : ModuleSheaf S) :
    (zariskiDerivedGlobalSections S.S.scheme).obj (tauDerivedDirectImage S F) ≅
      DerivedCategory.Plus.ι.obj ((derivedModuleGlobalSections S).obj F) :=
  (Stacks.Cohomology.LerayOfToposHom.derivedGlobalSectionsPushforwardIso.{u, u, u, u + 1, u + 1,
      0, u} (structureRingedHom S) (zariskiBaseRingHom S.S.scheme)).app _ ≪≫
    eqToIso (congrArg (fun κ ↦ (Stacks.DerivedFunctor.totalRightDerived
        (Stacks.Cohomology.SiteModules.globalSectionsFunctor (crisRingSheaf S) ⋙
          ModuleCat.restrictScalars κ)).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((crisModuleEquivalence S).functor.obj F)))
      (toposGlobalSectionsRingHom_structureRingedHom_comp S)) ≪≫
    (Stacks.DerivedFunctor.totalRightDerived
        (Stacks.Cohomology.SiteModules.globalSectionsFunctor (crisRingSheaf S) ⋙
          ModuleCat.restrictScalars (crisBaseRingULift S))).mapIso
      (((crisModuleEquivalence S).functor.mapDerivedCategorySingleFunctor 0).symm.app F) ≪≫
    (Stacks.Injectives.derivedPrecompIso (crisModuleEquivalence S).functor
        (Stacks.Cohomology.SiteModules.globalSectionsFunctor (crisRingSheaf S) ⋙
          ModuleCat.restrictScalars (crisBaseRingULift S))).symm.app _ ≪≫
    (Stacks.DerivedFunctor.totalRightDerivedIsoOfIso _ (crisRingedGlobalSectionsIso S)).app _ ≪≫
    (Stacks.DerivedFunctor.rightDerivedFunctorPlusCompιIso (baseModuleGlobalSections S)).symm.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)

end CrystallineGlobalSections

/-! ### The base change map on global sections along a morphism of divided power bases -/

section BaseChange

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

variable {S S' : GlobalCrystallineSituation.{u}}
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA'} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))] (f : S.S ⟶ S'.S)

/-- **The canonical map `RΓ(S', K) ⊗^L_{A'} A ⟶ RΓ(S, Lg^*K)`** in `D(A)`, for `K ∈ D(𝒪_{S'})`,
where `g : S ⟶ S'` is the morphism of schemes underlying a morphism `f` of divided power bases,
`A = Γ(S, 𝒪_S)`, `A' = Γ(S', 𝒪_{S'})`, and `Lg^*` the derived pullback along the Zariski
morphism of ringed topoi `zariskiRingedHom g`.

It is the transpose across the adjunction `- ⊗^L_{A'} A ⊣ res` of [Stacks, Tag 0GMT]
(`...SmallSite.derivedBaseChangeTensorAdjunction`) of `RΓ(S', -)` applied to the unit
`K ⟶ Rg_* Lg^*K`, followed by the Leray identification `RΓ(S', Rg_* -) = RΓ(S, -)` of
[Stacks, Tag 0D6H] read over `A' ⟶ A`; the two ring maps agree by
`toposGlobalSectionsRingHom_zariskiRingedHom_comp`. It is a map, not in general an
isomorphism. -/
def zariskiBaseChangeGlobalSectionsMap
    (K : DerivedCategory (SheafOfModules.{u + 1} (zariskiRingSheaf S'.S.scheme))) :
    (derivedBaseChangeTensor f).obj ((zariskiDerivedGlobalSections S'.S.scheme).obj K) ⟶
      (zariskiDerivedGlobalSections S.S.scheme).obj
        ((derivedPullback (X := zariskiRingedTopos S.S.scheme) (Y := zariskiRingedTopos S'.S.scheme)
          (zariskiRingedHom f.hom)).obj K) :=
  Stacks.Cohomology.LerayOfToposHom.derivedGlobalSectionsBaseChangeMap.{u, u, u, u + 1, 0, 0, u, u}
    (zariskiRingedHom f.hom) (zariskiBaseRingHom S.S.scheme) (zariskiBaseRingHom S'.S.scheme)
    (baseChangeRingHom f) (toposGlobalSectionsRingHom_zariskiRingedHom_comp f.hom)
    (derivedBaseChangeTensorAdjunction f) K

/-- **The base change map is the transpose of the semilinear comparison**: across
`- ⊗^L_{A'} A ⊣ res`, `zariskiBaseChangeGlobalSectionsMap f K` is `RΓ(S', -)` of the unit
`K ⟶ Rg_* Lg^*K` followed by the Leray identification for `g`. -/
theorem homEquiv_zariskiBaseChangeGlobalSectionsMap
    (K : DerivedCategory (SheafOfModules.{u + 1} (zariskiRingSheaf S'.S.scheme))) :
    (derivedBaseChangeTensorAdjunction f).homEquiv _ _ (zariskiBaseChangeGlobalSectionsMap f K) =
      Stacks.Cohomology.LerayOfToposHom.derivedGlobalSectionsSemilinearMap.{u, u, u, u + 1, 0, 0,
          u, u}
        (zariskiRingedHom f.hom) (zariskiBaseRingHom S.S.scheme) (zariskiBaseRingHom S'.S.scheme)
        (baseChangeRingHom f) (toposGlobalSectionsRingHom_zariskiRingedHom_comp f.hom) K :=
  Equiv.apply_symm_apply _ _

end BaseChange

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
