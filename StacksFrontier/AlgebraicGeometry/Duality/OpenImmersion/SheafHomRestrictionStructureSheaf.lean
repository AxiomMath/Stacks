module

public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomRestrictionNaturality
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CompletionUnitRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalenceStructureSheafDerived

/-!
# Restriction of `R𝓗om(𝒪, -) ≅ id` to an open subscheme

Let `S` be a scheme and `U ⊆ S` an open subscheme. This file proves that [Stacks, Tag 08DL] for the
open subscheme, `R𝓗om(K, L)|_U ≅ R𝓗om(K|_U, L|_U)`
(`Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso`), carries the identification
`R𝓗om(𝒪_S, M) ≅ M` to `R𝓗om(𝒪_U, M|_U) ≅ M|_U`, through the canonical morphism
`𝒪_U ⟶ 𝒪_S|_U`. It is assembled from the same statement for the slice site
(`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso_restrict`) and for the equivalence of
ringed sites between the slice site and the open subscheme
(`AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomIsoOfIso_structureSheaf`).

## Main definitions

* `Stacks.SheafOfModules.derivedUnitRestrictHom`: `𝒪_U ⟶ 𝒪_S|_U` in `D(𝒪_U)`.
* `Stacks.SheafOfModules.restrictDerivedSheafHomIso`: [Stacks, Tag 08DL] for an open
  subscheme, in the scheme's spelling of `D(𝒪)`.

## Main results

* `Stacks.SheafOfModules.restrictDerivedSheafHomIso_structureSheaf`.

Standard model: uses `Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso`, which exists
only at `CategoryTheory.HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

namespace Stacks.SheafOfModules

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {S : Scheme.{u}} (U : S.Opens)

/-- Presheaves of commutative rings on the ringed site of `S` admit sheafification. -/
instance : HasWeakSheafify (ringedSite S.sheaf).J CommRingCat.{u} :=
  inferInstanceAs (HasWeakSheafify (Opens.grothendieckTopology S) CommRingCat.{u})

/-- Presheaves of commutative rings on the slice of the ringed site of `S` over `U` admit
sheafification. -/
instance : HasWeakSheafify ((ringedSite S.sheaf).over U).J CommRingCat.{u} :=
  inferInstanceAs (HasWeakSheafify ((Opens.grothendieckTopology S).over U) CommRingCat.{u})

/-- **The canonical morphism `𝒪_U ⟶ 𝒪_S|_U`** in `D(𝒪_U)`. -/
def derivedUnitRestrictHom :
    derivedUnitObject U.toScheme ⟶
      (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj (derivedUnitObject S) :=
  letI := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := S.ringCatSheaf) U
  letI := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := S.ringCatSheaf) U
  RingedSite.siteEquivDerivedStructureSheafHom (X := (ringedSite S.sheaf).over U)
      (Y := ringedSite U.toScheme.sheaf) U.overEquivalence.symm (schemeOpenPhi U)
      (hlim := inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.overEquiv U).functor))
      (hcolim := inferInstanceAs (PreservesFiniteColimits (Scheme.Modules.overEquiv U).functor)) ≫
    ((Scheme.Modules.overEquiv U).functor).mapDerivedCategory.map
      (RingedSite.derivedStructureSheafRestrictIso (ringedSite S.sheaf) U).inv ≫
    (derivedOverFunctorEquiv U).hom.app (derivedUnitObject S)

/-- [Stacks, Tag 08DL] for the open subscheme `U`, `R𝓗om(K, L)|_U ≅ R𝓗om(K|_U, L|_U)`
(`Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso`), with the exactness of restriction to
the slice site supplied. -/
def restrictDerivedSheafHomIso (K L : DerivedCategory S.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
        (((RingedSite.derivedSheafHomBifunctor (ringedSite S.sheaf)).flip.obj L).obj (op K)) ≅
      ((RingedSite.derivedSheafHomBifunctor (ringedSite U.toScheme.sheaf)).flip.obj
        ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj L)).obj
          (op ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K)) :=
  letI := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := S.ringCatSheaf) U
  letI := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := S.ringCatSheaf) U
  derivedSheafHomSchemeRestrictionIso U K L

/-- `R𝓗om(𝒪_S, M) ≅ M` (`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso`), in the
scheme's spelling of `D(𝒪_S)`. -/
def schemeStructureSheafHomIso (T : Scheme.{u}) (M : DerivedCategory T.Modules) :
    ((RingedSite.derivedSheafHomBifunctor (ringedSite T.sheaf)).flip.obj M).obj
        (op (derivedUnitObject T)) ≅ M :=
  RingedSite.derivedStructureSheafHomIso (ringedSite T.sheaf) M

/-- `R𝓗om(𝒪_T, M) ≅ M` is natural in `M`. -/
theorem schemeStructureSheafHomIso_naturality (T : Scheme.{u}) {M N : DerivedCategory T.Modules}
    (φ : M ⟶ N) :
    ((RingedSite.derivedSheafHomBifunctor (ringedSite T.sheaf)).flip.map φ).app
        (op (derivedUnitObject T)) ≫ (schemeStructureSheafHomIso T N).hom =
      (schemeStructureSheafHomIso T M).hom ≫ φ :=
  RingedSite.derivedStructureSheafHomIso_naturality (Z := M) (W := N) (ringedSite T.sheaf) φ

/-- The diagram chase of `Stacks.SheafOfModules.restrictDerivedSheafHomIso_structureSheaf`, in
one abstract category: given the commuting squares `H₁`–`H₇` and `a ≫ βA = 𝟙`, the composite
`((a ≫ G.map s) ≫ c ≫ d ≫ e) ≫ f ≫ g` equals `r`. -/
theorem restrictDerivedSheafHomIso_structureSheaf_chase {𝒜 𝒟 : Type*} [Category 𝒜] [Category 𝒟]
    (G : 𝒜 ⥤ 𝒟) {A₁ A₂ A₃ B : 𝒜} {T₀ T₃ T₄ T₄' T₅ T₅' T₆ T₇ : 𝒟}
    (a : T₀ ⟶ G.obj A₁) (s : A₁ ⟶ A₂) (c : G.obj A₂ ⟶ T₃) (d : T₃ ⟶ T₄) (e : T₄ ⟶ T₅)
    (f : T₅ ⟶ T₆) (g : T₆ ⟶ T₇) (f' : T₄ ⟶ T₅') (e' : T₅' ⟶ T₆) (g' : T₅' ⟶ G.obj B)
    (βB : G.obj B ⟶ T₇) (d' : T₃ ⟶ T₄') (f'' : T₄' ⟶ T₅') (x : A₂ ⟶ A₃) (c' : G.obj A₃ ⟶ T₄')
    (η : A₃ ⟶ B) (η₁ : A₁ ⟶ B) (βA : G.obj A₁ ⟶ T₀) (r : T₀ ⟶ T₇)
    (H₁ : e ≫ f = f' ≫ e') (H₂ : e' ≫ g = g' ≫ βB) (H₃ : d ≫ f' = d' ≫ f'')
    (H₄ : c ≫ d' = G.map x ≫ c') (H₅ : c' ≫ f'' ≫ g' = G.map η) (H₆ : s ≫ x ≫ η = η₁)
    (H₇ : G.map η₁ ≫ βB = βA ≫ r) (Ha : a ≫ βA = 𝟙 T₀) :
    ((a ≫ G.map s) ≫ c ≫ d ≫ e) ≫ f ≫ g = r := by
  simp only [Category.assoc]
  rw [reassoc_of% H₁, H₂, reassoc_of% H₃, reassoc_of% H₄, reassoc_of% H₅, ← G.map_comp_assoc,
    ← G.map_comp_assoc, show (s ≫ x) ≫ η = η₁ by rw [Category.assoc, H₆], H₇,
    reassoc_of% Ha]

/-- Precomposition in the first variable of a bifunctor, along a composite ending in an
isomorphism, in one abstract category. -/
theorem bifunctor_mapIso_symm_op_app_comp {C D E : Type*} [Category C] [Category D] [Category E]
    (H : Cᵒᵖ ⥤ D ⥤ E) {X₁ X₂ Y₀ Y₁ : C} (β : X₁ ≅ X₂) (t : Y₀ ⟶ Y₁) (k : Y₁ ⟶ X₁)
    (ε : Y₀ ⟶ X₂) (hε : ε = t ≫ k ≫ β.hom) (Z : D) :
    ((H.mapIso β.symm.op).app Z).hom ≫ (H.map ε.op).app Z =
      (H.map k.op).app Z ≫ (H.map t.op).app Z := by
  subst hε
  simp only [Iso.app_hom, Functor.mapIso_hom, Iso.op_hom, Iso.symm_hom, ← NatTrans.comp_app,
    ← Functor.map_comp, ← op_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **Restriction to an open subscheme carries `R𝓗om(𝒪_S, M) ≅ M` to `R𝓗om(𝒪_U, M|_U) ≅ M|_U`**,
under [Stacks, Tag 08DL] and the canonical morphism `𝒪_U ⟶ 𝒪_S|_U`. -/
theorem restrictDerivedSheafHomIso_structureSheaf (M : DerivedCategory S.Modules) :
    (restrictDerivedSheafHomIso U (derivedUnitObject S) M).hom ≫
        ((RingedSite.derivedSheafHomBifunctor (ringedSite U.toScheme.sheaf)).flip.obj
          ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj M)).map
            (derivedUnitRestrictHom U).op ≫
        (schemeStructureSheafHomIso U.toScheme
          ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj M)).hom =
      (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.map
        (schemeStructureSheafHomIso S M).hom := by
  let := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := S.ringCatSheaf) U
  let := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := S.ringCatSheaf) U
  let hl : PreservesFiniteLimits (Scheme.Modules.overEquiv U).functor := inferInstance
  let hc : PreservesFiniteColimits (Scheme.Modules.overEquiv U).functor := inferInstance
  let F₁ := derivedRestrict S.sheaf U
  let F₂ := ((Scheme.Modules.overEquiv U).functor).mapDerivedCategory
  let εs := RingedSite.derivedStructureSheafRestrictIso (ringedSite S.sheaf) U
  refine restrictDerivedSheafHomIso_structureSheaf_chase F₂ _ _ _ _ _ _ _
    (((RingedSite.derivedSheafHomBifunctor (ringedSite U.toScheme.sheaf)).map
      (derivedUnitRestrictHom U).op).app (F₂.obj (F₁.obj M)))
    (((RingedSite.derivedSheafHomBifunctor (ringedSite U.toScheme.sheaf)).obj
      (op (derivedUnitObject U.toScheme))).map ((derivedOverFunctorEquiv U).hom.app M))
    (schemeStructureSheafHomIso U.toScheme (F₂.obj (F₁.obj M))).hom
    ((derivedOverFunctorEquiv U).hom.app M)
    (((RingedSite.derivedSheafHomBifunctor (ringedSite U.toScheme.sheaf)).map
      (F₂.map εs.inv).op).app (F₂.obj (F₁.obj M)))
    (((RingedSite.derivedSheafHomBifunctor (ringedSite U.toScheme.sheaf)).map
      (RingedSite.siteEquivDerivedStructureSheafHom (X := (ringedSite S.sheaf).over U)
        (Y := ringedSite U.toScheme.sheaf) U.overEquivalence.symm (schemeOpenPhi U)
        (hlim := hl)
        (hcolim := hc)).op).app
      (F₂.obj (F₁.obj M)))
    (((RingedSite.derivedSheafHomBifunctor ((ringedSite S.sheaf).over U)).map εs.inv.op).app
      (F₁.obj M))
    (RingedSite.siteEquivDerivedSheafHomIsoOfIso (X := (ringedSite S.sheaf).over U)
        (Y := ringedSite U.toScheme.sheaf) U.overEquivalence.symm (schemeOpenPhi U)
        (hφ := isIso_schemeOpenPhi U)
        (hlim := hl)
        (hcolim := hc)
        (RingedSite.derivedStructureSheaf ((ringedSite S.sheaf).over U)) (F₁.obj M)).hom
    (@Iso.hom _ _ _ _ (RingedSite.derivedStructureSheafHomIso ((ringedSite S.sheaf).over U)
      (F₁.obj M)))
    (F₁.map (schemeStructureSheafHomIso S M).hom)
    ((derivedOverFunctorEquiv U).hom.app _) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ((RingedSite.derivedSheafHomBifunctor (ringedSite U.toScheme.sheaf)).map
      (derivedUnitRestrictHom U).op).naturality ((derivedOverFunctorEquiv U).hom.app M)
  · exact RingedSite.derivedStructureSheafHomIso_naturality _ _
  · exact bifunctor_mapIso_symm_op_app_comp _ _ _ _ _ rfl _
  · exact (derivedSheafHomSchemeOpenIso_natural_left U _ εs.inv).symm
  · exact RingedSite.siteEquivDerivedSheafHomIsoOfIso_structureSheaf _ _
      (hφ := isIso_schemeOpenPhi U)
      (hlim := hl)
      (hcolim := hc) _
  · exact RingedSite.derivedStructureSheafHomIso_restrict (ringedSite S.sheaf) U M
  · exact (derivedOverFunctorEquiv U).hom.naturality _
  · exact Iso.inv_hom_id_app (derivedOverFunctorEquiv U) _

end Stacks.SheafOfModules
