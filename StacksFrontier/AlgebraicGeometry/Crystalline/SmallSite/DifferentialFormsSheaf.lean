module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnitULift
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalFirstOrderComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ExteriorPowerComparisonSurjectivity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FormsRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictionCalculus
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SheafifySections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom

/-!
# The sheaf of `𝒪_{X/S}`-modules `Ω^j_{X/S}` on the small crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF].  The library's
`Ω^j_{X/S} = ⋀^j Ω_{X/S}` on `Cris(X/S)` (`...SmallSite.crysDifferentialForms`) is a presheaf of
`𝒪_{X/S}`-modules: its sections over `(U, T, δ)` are the `j`-th exterior power of the divided
power differentials of `Γ(T, 𝒪_T)`, and its restriction to `T` has `Ω^j_{T/S, δ}` as associated
sheaf ([Stacks, Tag 07IZ]).  The sheaf `Ω^j_{X/S}` of the chapter is the sheaf associated with
it.  This file constructs that sheaf as a sheaf of `𝒪_{X/S}`-modules **with sections in
`Type u`**, the universe at which [Stacks, Tag 07JN] and [Stacks, Tag 07LN] are stated, and proves
that it satisfies conditions (1) and (2) of [Stacks, Tag 07JN].

## Implementation notes

The objects of `Cris(X/S)` form a `Type (u + 1)`, so sheafification of presheaves with sections
in `Type u` is not available on `Cris(X/S)`.  The construction therefore sheafifies the universe
lift of `Ω^j_{X/S}` at the module universe `u + 1` (`crysFormsSheafULift`) and shows that its
sections are `u`-small: over `(U, T, δ)` they are the sections over `T` of the Zariski
sheafification of the restriction of `Ω^j_{X/S}` to `T`, by
`...SmallSite.CrystallineThickening.restrictOpenSheafifyIso`.  Its shrinking
`Stacks.SheafOfModules.sheafShrink` is `crysFormsSheaf`, and `toCrysFormsSheaf` is the
sheafification map read at the universe `u`; it is locally injective and locally surjective, so
`crysFormsSheaf` is the sheaf associated with the presheaf `Ω^j_{X/S}`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `crysFormsSheaf` — **the sheaf of `𝒪_{X/S}`-modules `Ω^j_{X/S}`** on `Cris(X/S)`.
* `toCrysFormsSheaf` — the morphism from the presheaf `Ω^j_{X/S}` to it.
* `crysFormsSheafRestrictionHom` — the comparison morphism from the sheaf associated with the
  restriction of the presheaf `Ω^j_{X/S}` to an ambient scheme to the restriction of the sheaf.

## Main results

* `isLocallyInjective_toCrysFormsSheaf` and `isLocallySurjective_toCrysFormsSheaf` —
  `toCrysFormsSheaf` is locally bijective, so `crysFormsSheaf` is the sheafification.
* `isIso_crysFormsSheafRestrictionHom` — the restriction of the sheaf `Ω^j_{X/S}` to the ambient
  scheme `T` of an object is the sheaf associated with the restriction of the presheaf.
* `isLocallyQuasiCoherent_crysFormsSheaf` — **condition (1) of [Stacks, Tag 07JN]** for
  `Ω^j_{X/S}`, from [Stacks, Tag 07IZ] and [Stacks, Tag 07IY].
* `isSurjectiveComparison_crysFormsSheaf` — **condition (2) of [Stacks, Tag 07JN]** for
  `Ω^j_{X/S}`, from [Stacks, Tag 07KM] for the presheaf.
* `CohomologyRestriction.pullback_map_moduleRestrictionMap_comp_moduleComparison` — the comparison
  morphism `c_f` is natural in the presheaf of modules.

## References

* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07KM](https://stacks.math.columbia.edu/tag/07KM)
* [Stacks Project, Tag 07LN](https://stacks.math.columbia.edu/tag/07LN)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-- The presheaf `Ω^j_{X/S}` with its sections raised to `Type (u + 1)`. -/
def crysDifferentialFormsULift (j : ℕ) : PresheafOfModules.{u + 1} (structureSheaf S).obj :=
  (Stacks.SheafOfModules.presheafULift.{u + 1} (structureSheaf S).obj).obj
    (crysDifferentialForms S j)

/-- The sheaf of `𝒪_{X/S}`-modules associated with `Ω^j_{X/S}`, at the module universe `u + 1`. -/
def crysFormsSheafULift (j : ℕ) : ModuleSheaf S :=
  (PresheafOfModules.sheafification (𝟙 (structureSheaf S).obj)).obj (crysDifferentialFormsULift S j)

variable {S}

/-- The restriction of `Ω^j_{X/S}` to the ambient scheme of an object, as an abelian presheaf. -/
abbrev formsRestrictionPresheaf (A : CrystallineThickening S) (j : ℕ) :
    (A.obj.thickening.target.scheme.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (CrystallineThickening.restrictOpenFunctor A).op ⋙ (crysDifferentialForms S j).presheaf

/-- The Zariski sheafification of `formsRestrictionPresheaf`, raised to `AddCommGrpCat.{u + 1}`. -/
abbrev formsRestrictionSheafULift (A : CrystallineThickening S) (j : ℕ) :
    (A.obj.thickening.target.scheme.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  ((presheafToSheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme)
    AddCommGrpCat.{u}).obj (formsRestrictionPresheaf A j)).obj ⋙
      AddCommGrpCat.uliftFunctor.{u + 1}

/-- The Zariski sheafification unit of the restriction of `Ω^j_{X/S}`, raised to
`AddCommGrpCat.{u + 1}`. -/
abbrev formsRestrictionToSheafULift (A : CrystallineThickening S) (j : ℕ) :
    (CrystallineThickening.restrictOpenFunctor A).op ⋙ (crysDifferentialFormsULift S j).presheaf ⟶
      formsRestrictionSheafULift A j :=
  Functor.whiskerRight (toSheafify (Opens.grothendieckTopology A.obj.thickening.target.scheme)
    (formsRestrictionPresheaf A j)) AddCommGrpCat.uliftFunctor.{u + 1}

/-- The map `formsRestrictionToSheafULift A j` is locally injective for the topology of open
covers of the ambient scheme of `A`. -/
instance isLocallyInjective_formsRestrictionToSheafULift (A : CrystallineThickening S) (j : ℕ) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (formsRestrictionToSheafULift A j) :=
  haveI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (toSheafify _ (formsRestrictionPresheaf A j)) :=
    GrothendieckTopology.W.isLocallyInjective (GrothendieckTopology.W_toSheafify _ _)
  Stacks.Sheaves.UniverseLift.isLocallyInjective_uliftFunctor _

/-- The map `formsRestrictionToSheafULift A j` is locally surjective for the topology of open
covers of the ambient scheme of `A`. -/
instance isLocallySurjective_formsRestrictionToSheafULift (A : CrystallineThickening S) (j : ℕ) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (formsRestrictionToSheafULift A j) :=
  haveI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (toSheafify _ (formsRestrictionPresheaf A j)) :=
    GrothendieckTopology.W.isLocallySurjective (GrothendieckTopology.W_toSheafify _ _)
  Stacks.Sheaves.UniverseLift.isLocallySurjective_uliftFunctor _

/-- The restriction of the sheaf `crysFormsSheafULift` to the ambient scheme of an object is the
universe lift of the Zariski sheafification of the restriction of `Ω^j_{X/S}`. -/
def crysFormsSheafULiftRestrictionIso (A : CrystallineThickening S) (j : ℕ) :
    (CrystallineThickening.restrictOpenFunctor A).op ⋙ (crysFormsSheafULift S j).val.presheaf ≅
      formsRestrictionSheafULift A j :=
  haveI := isLocallyInjective_toSheafify (crysDifferentialFormsULift S j).presheaf
  haveI := isLocallySurjective_toSheafify (crysDifferentialFormsULift S j).presheaf
  CrystallineThickening.restrictOpenSheafifyIso A
    (toSheafify (smallTopology S) (crysDifferentialFormsULift S j).presheaf)
    (Presheaf.isSheaf_comp_of_isSheaf _ _ AddCommGrpCat.uliftFunctor
      ((presheafToSheaf _ AddCommGrpCat.{u}).obj (formsRestrictionPresheaf A j)).property)
    (crysFormsSheafULift S j).isSheaf (formsRestrictionToSheafULift A j)

/-- **The sections of `crysFormsSheafULift` are `u`-small**: over `(U, T, δ)` they are, through
the restriction to `(U, T, δ)|_T` of the object itself, the sections over `T` of the universe lift
of a Zariski sheaf with sections in `Type u` (`crysFormsSheafULiftRestrictionIso`). -/
instance small_crysFormsSheafULift_obj (j : ℕ) (X : (CrystallineThickening S)ᵒᵖ) :
    Small.{u} ((crysFormsSheafULift S j).val.obj X) := by
  have := CrystallineThickening.isIso_restrictOpenHom_top X.unop
  let e₁ := (crysFormsSheafULift S j).val.presheaf.mapIso (asIso (X.unop.restrictOpenHom ⊤)).op
  let e₂ := (crysFormsSheafULiftRestrictionIso X.unop j).app (op ⊤)
  have : Small.{u} ((formsRestrictionSheafULift X.unop j).obj (op ⊤)) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1} _))
  exact small_map ((e₁ ≪≫ e₂).addCommGroupIsoToAddEquiv.toEquiv)

variable (S)

/-- **The sheaf of `𝒪_{X/S}`-modules `Ω^j_{X/S}` on the small crystalline site**, the sheaf
associated with the presheaf `Ω^j_{X/S} = ⋀^j Ω_{X/S}` (`toCrysFormsSheaf`), with its sections in
`Type u`.  It is the shrinking of the sheafification `crysFormsSheafULift` taken at the module
universe `u + 1`, whose sections are `u`-small (`small_crysFormsSheafULift_obj`). -/
def crysFormsSheaf (j : ℕ) : SheafOfModules.{u} (structureSheaf S) :=
  Stacks.SheafOfModules.sheafShrink.{u, u + 1} (structureSheaf S) (crysFormsSheafULift S j)

/-- The unit of the sheafification of the lifted presheaf `Ω^j_{X/S}`, as a morphism of presheaves
of modules. -/
abbrev crysFormsSheafULiftUnit (j : ℕ) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheaf S).obj)).unit.app
    (crysDifferentialFormsULift S j)

/-- **The canonical morphism from the presheaf `Ω^j_{X/S}` to the sheaf `Ω^j_{X/S}`**: the
sheafification map, read at the module universe `u`. -/
def toCrysFormsSheaf (j : ℕ) : crysDifferentialForms S j ⟶ (crysFormsSheaf S j).val :=
  letI e := fun X : (CrystallineThickening S)ᵒᵖ ↦
    Shrink.addEquiv (α := ((crysFormsSheafULift S j).val.obj X : Type (u + 1)))
  PresheafOfModules.homMk
    { app X := AddCommGrpCat.ofHom ((e X).symm.toAddMonoidHom.comp
          (((crysFormsSheafULiftUnit S j).app X).hom.toAddMonoidHom.comp
            (AddEquiv.ulift.{u, u + 1}).symm.toAddMonoidHom))
      naturality X Y f := by
        ext x
        apply (e Y).injective
        refine ((e Y).apply_symm_apply _).trans ?_
        refine Eq.trans ?_ ((e Y).apply_symm_apply _).symm
        refine Eq.trans ?_ (congrArg _ ((e X).apply_symm_apply _).symm)
        exact PresheafOfModules.naturality_apply (crysFormsSheafULiftUnit S j) f (ULift.up x) }
    (fun X r m ↦
      (congrArg (Shrink.addEquiv (α := ((crysFormsSheafULift S j).val.obj X : Type (u + 1)))).symm
        (((crysFormsSheafULiftUnit S j).app X).hom.map_smul r (ULift.up m))).trans
      ((Shrink.linearEquiv ((structureSheaf S).obj.obj X)
        ((crysFormsSheafULift S j).val.obj X : Type (u + 1))).symm.map_smul r _))

/-- Raising the universe of a morphism of abelian presheaves reflects local injectivity. -/
private theorem isLocallyInjective_of_whiskerRight_uliftFunctor {C : Type*} [Category C]
    {J : GrothendieckTopology C} {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ Q)
    [h : Presheaf.IsLocallyInjective J
      (Functor.whiskerRight f AddCommGrpCat.uliftFunctor.{u + 1})] :
    Presheaf.IsLocallyInjective J f where
  equalizerSieve_mem {X} x y hxy := by
    have he : Presheaf.equalizerSieve (F := P ⋙ AddCommGrpCat.uliftFunctor.{u + 1})
        (ULift.up x) (ULift.up y) = Presheaf.equalizerSieve x y := by
      ext V i
      simp only [Presheaf.equalizerSieve_apply]
      exact ⟨fun h ↦ congrArg ULift.down h, fun h ↦ congrArg ULift.up h⟩
    rw [← he]
    exact Presheaf.equalizerSieve_mem J
      (Functor.whiskerRight f AddCommGrpCat.uliftFunctor.{u + 1}) _ _ (congrArg ULift.up hxy)

/-- Raising the universe of a morphism of abelian presheaves reflects local surjectivity. -/
private theorem isLocallySurjective_of_whiskerRight_uliftFunctor {C : Type*} [Category C]
    {J : GrothendieckTopology C} {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ Q)
    [h : Presheaf.IsLocallySurjective J
      (Functor.whiskerRight f AddCommGrpCat.uliftFunctor.{u + 1})] :
    Presheaf.IsLocallySurjective J f where
  imageSieve_mem {X} s := by
    have he : Presheaf.imageSieve (Functor.whiskerRight f AddCommGrpCat.uliftFunctor.{u + 1})
        (ULift.up s) = Presheaf.imageSieve f s := by
      ext V i
      simp only [Presheaf.imageSieve_apply]
      exact ⟨fun ⟨x, hx⟩ ↦ ⟨x.down, congrArg ULift.down hx⟩,
        fun ⟨x, hx⟩ ↦ ⟨ULift.up x, congrArg ULift.up hx⟩⟩
    rw [← he]
    exact Presheaf.imageSieve_mem J
      (Functor.whiskerRight f AddCommGrpCat.uliftFunctor.{u + 1}) (U := op X) (ULift.up s)

/-- The universe lift of `toCrysFormsSheaf` is the sheafification map of the lifted presheaf
`Ω^j_{X/S}` followed by the identification of the sheafification with the lift of its shrinking. -/
theorem whiskerRight_toCrysFormsSheaf (j : ℕ) :
    Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map (toCrysFormsSheaf S j))
        AddCommGrpCat.uliftFunctor.{u + 1} =
      toSheafify (smallTopology S) (crysDifferentialFormsULift S j).presheaf ≫
        (PresheafOfModules.toPresheaf _).map
          (Stacks.SheafOfModules.presheafShrinkIso.{u, u + 1} _
            (crysFormsSheafULift S j).val).inv := by
  ext X x
  rfl

/-- A locally injective morphism followed by a sectionwise injective one is locally injective. -/
private theorem isLocallyInjective_comp_of_injective {C : Type*} [Category C]
    {J : GrothendieckTopology C} {F₁ F₂ F₃ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (f : F₁ ⟶ F₂)
    (g : F₂ ⟶ F₃) (hf : Presheaf.IsLocallyInjective J f)
    (hg : ∀ X, Function.Injective (g.app X)) : Presheaf.IsLocallyInjective J (f ≫ g) :=
  have := Presheaf.isLocallyInjective_of_injective J g hg
  inferInstance

/-- A locally surjective morphism followed by a sectionwise surjective one is locally
surjective. -/
private theorem isLocallySurjective_comp_of_surjective {C : Type*} [Category C]
    {J : GrothendieckTopology C} {F₁ F₂ F₃ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (f : F₁ ⟶ F₂)
    (g : F₂ ⟶ F₃) (hf : Presheaf.IsLocallySurjective J f)
    (hg : ∀ X, Function.Surjective (g.app X)) : Presheaf.IsLocallySurjective J (f ≫ g) :=
  have := Presheaf.isLocallySurjective_of_surjective J g hg
  inferInstance

/-- **`toCrysFormsSheaf` is locally injective** for the topology of `Cris(X/S)`: its universe lift
is the sheafification map of the lifted presheaf followed by an isomorphism. -/
theorem isLocallyInjective_toCrysFormsSheaf (j : ℕ) :
    Presheaf.IsLocallyInjective (smallTopology S)
      ((PresheafOfModules.toPresheaf _).map (toCrysFormsSheaf S j)) := by
  have : Presheaf.IsLocallyInjective (smallTopology S)
      (Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map (toCrysFormsSheaf S j))
        AddCommGrpCat.uliftFunctor.{u + 1}) := by
    rw [whiskerRight_toCrysFormsSheaf]
    exact isLocallyInjective_comp_of_injective _ _ (isLocallyInjective_toSheafify _)
      (fun X ↦ (ConcreteCategory.bijective_of_isIso
        (((PresheafOfModules.toPresheaf _).map (Stacks.SheafOfModules.presheafShrinkIso.{u, u + 1} _
          (crysFormsSheafULift S j).val).inv).app X)).1)
  exact isLocallyInjective_of_whiskerRight_uliftFunctor _

/-- **`toCrysFormsSheaf` is locally surjective** for the topology of `Cris(X/S)`: its universe
lift is the sheafification map of the lifted presheaf followed by an isomorphism. -/
theorem isLocallySurjective_toCrysFormsSheaf (j : ℕ) :
    Presheaf.IsLocallySurjective (smallTopology S)
      ((PresheafOfModules.toPresheaf _).map (toCrysFormsSheaf S j)) := by
  have : Presheaf.IsLocallySurjective (smallTopology S)
      (Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map (toCrysFormsSheaf S j))
        AddCommGrpCat.uliftFunctor.{u + 1}) := by
    rw [whiskerRight_toCrysFormsSheaf]
    exact isLocallySurjective_comp_of_surjective _ _ (isLocallySurjective_toSheafify _)
      (fun X ↦ (ConcreteCategory.bijective_of_isIso
        (((PresheafOfModules.toPresheaf _).map (Stacks.SheafOfModules.presheafShrinkIso.{u, u + 1} _
          (crysFormsSheafULift S j).val).inv).app X)).2)
  exact isLocallySurjective_of_whiskerRight_uliftFunctor _

variable {S}

/-- **`toCrysFormsSheaf`, restricted to the ambient scheme of an object, is locally injective.**
The universe lift of the restricted map is the restriction of the sheafification map of the
lifted presheaf, followed by an isomorphism, and restriction to the ambient scheme preserves local
injectivity. -/
theorem isLocallyInjective_restrict_toCrysFormsSheaf (A : CrystallineThickening S) (j : ℕ) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
        ((PresheafOfModules.toPresheaf _).map (toCrysFormsSheaf S j))) where
  equalizerSieve_mem {X} x y hxy := by
    have := isLocallyInjective_toSheafify (crysDifferentialFormsULift S j).presheaf
    have := isLocallySurjective_toSheafify (crysDifferentialFormsULift S j).presheaf
    have := CrystallineThickening.isLocallyInjective_whiskerLeft_restrictOpenFunctor A
      (toSheafify (smallTopology S) (crysDifferentialFormsULift S j).presheaf)
    have hxy' : (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
        (toSheafify (smallTopology S) (crysDifferentialFormsULift S j).presheaf)).app X
          (ULift.up x) =
        (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
          (toSheafify (smallTopology S) (crysDifferentialFormsULift S j).presheaf)).app X
          (ULift.up y) :=
      (Shrink.addEquiv (α := ((crysFormsSheafULift S j).val.obj
        (op (A.restrictOpen X.unop)) : Type (u + 1)))).symm.injective hxy
    have h := Presheaf.equalizerSieve_mem
      (Opens.grothendieckTopology A.obj.thickening.target.scheme) _ _ _ hxy'
    refine (Opens.grothendieckTopology _).superset_covering ?_ h
    intro V i hi
    exact congrArg ULift.down hi

/-- **`toCrysFormsSheaf`, restricted to the ambient scheme of an object, is locally
surjective.** -/
theorem isLocallySurjective_restrict_toCrysFormsSheaf (A : CrystallineThickening S) (j : ℕ) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
        ((PresheafOfModules.toPresheaf _).map (toCrysFormsSheaf S j))) where
  imageSieve_mem {X} s := by
    have := isLocallyInjective_toSheafify (crysDifferentialFormsULift S j).presheaf
    have := isLocallySurjective_toSheafify (crysDifferentialFormsULift S j).presheaf
    have := CrystallineThickening.isLocallySurjective_whiskerLeft_restrictOpenFunctor A
      (toSheafify (smallTopology S) (crysDifferentialFormsULift S j).presheaf)
    refine (Opens.grothendieckTopology _).superset_covering ?_
      (Presheaf.imageSieve_mem _ (Functor.whiskerLeft
        (CrystallineThickening.restrictOpenFunctor A).op
          (toSheafify (smallTopology S) (crysDifferentialFormsULift S j).presheaf))
        (U := op X) (Shrink.addEquiv (α := ((crysFormsSheafULift S j).val.obj
          (op (A.restrictOpen X)) : Type (u + 1))) s))
    rintro V i ⟨t, ht⟩
    refine ⟨t.down, ?_⟩
    apply (Shrink.addEquiv (α := ((crysFormsSheafULift S j).val.obj
      (op (A.restrictOpen V)) : Type (u + 1)))).injective
    refine ((Shrink.addEquiv (α := ((crysFormsSheafULift S j).val.obj
      (op (A.restrictOpen V)) : Type (u + 1)))).apply_symm_apply _).trans (ht.trans ?_)
    exact ((Shrink.addEquiv (α := ((crysFormsSheafULift S j).val.obj
      (op (A.restrictOpen V)) : Type (u + 1)))).apply_symm_apply _).symm

/-- **The comparison morphism `c_f` of [Stacks, Tag 07IQ] is natural in the presheaf of
modules**: both composites are transposes of the two sides of the naturality square of the
`f`-map, `...CohomologyRestriction.moduleFMap_naturality`. -/
theorem CohomologyRestriction.pullback_map_moduleRestrictionMap_comp_moduleComparison
    {M N : PresheafOfModules.{u} (crisRing S)} (φ : M ⟶ N) {A B : CrystallineThickening S}
    (g : A ⟶ B) :
    (PresheafOfModules.pullback (F := Opens.map g.hom.targetHom.hom.base)
        (CohomologyRestriction.restrictionFMap (crisRing S) g)).map
          (CohomologyRestriction.moduleRestrictionMap φ B) ≫
        CohomologyRestriction.moduleComparison N g =
      CohomologyRestriction.moduleComparison M g ≫
        CohomologyRestriction.moduleRestrictionMap φ A := by
  unfold CohomologyRestriction.moduleComparison
  rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm,
    CohomologyRestriction.moduleFMap_naturality]

/-- **Condition (2) of [Stacks, Tag 07JN] for the sheaf `Ω^j_{X/S}`**: for every morphism `f` of
`Cris(X/S)` whose map on ambient schemes is a closed immersion, the comparison morphism
`c_f : f^*(Ω^j_{X/S})_{T'} ⟶ (Ω^j_{X/S})_T` is locally surjective.  The comparison morphisms of the
presheaf `Ω^j_{X/S}` are ([Stacks, Tag 07KM],
`...CohomologyRestriction.isSurjectiveComparison_crysDifferentialForms`), the restriction of
`toCrysFormsSheaf` is locally surjective, and `c_f` is natural in the module. -/
theorem isSurjectiveComparison_crysFormsSheaf (j : ℕ) :
    CohomologyRestriction.IsSurjectiveComparison (crysFormsSheaf S j).val := by
  intro A B g hg
  have := CohomologyRestriction.isSurjectiveComparison_crysDifferentialForms (S := S) j g hg
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      ((PresheafOfModules.toPresheaf _).map
        (CohomologyRestriction.moduleRestrictionMap (toCrysFormsSheaf S j) A)) :=
    isLocallySurjective_restrict_toCrysFormsSheaf A j
  have fac := congrArg (PresheafOfModules.toPresheaf _).map
    (CohomologyRestriction.pullback_map_moduleRestrictionMap_comp_moduleComparison
      (toCrysFormsSheaf S j) g)
  rw [Functor.map_comp, Functor.map_comp] at fac
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      ((PresheafOfModules.toPresheaf _).map
          (CohomologyRestriction.moduleComparison (crysDifferentialForms S j) g) ≫
        (PresheafOfModules.toPresheaf _).map
          (CohomologyRestriction.moduleRestrictionMap (toCrysFormsSheaf S j) A)) :=
    inferInstance
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ fac

/-- The sheafification map followed by the transpose of a morphism into a sheaf is that
morphism. -/
private theorem toSheafify_comp_homEquiv_symm {C : Type*} [Category C]
    {J : GrothendieckTopology C} [HasWeakSheafify J AddCommGrpCat.{u}]
    {P : Cᵒᵖ ⥤ AddCommGrpCat.{u}} {F : Sheaf J AddCommGrpCat.{u}} (φ : P ⟶ F.obj) :
    toSheafify J P ≫ (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv P F).symm φ).hom =
      φ := by
  have h := ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv P F).apply_symm_apply φ
  rwa [Adjunction.homEquiv_unit] at h

/-- **A locally bijective morphism from a presheaf to a sheaf exhibits the sheaf as the
sheafification**: its transpose across the sheafification adjunction is an isomorphism. -/
private theorem isIso_homEquiv_symm_of_isLocallyBijective {T : Scheme.{u}}
    {P : (T.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    {F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}}
    (φ : P ⟶ F.obj)
    (hi : Presheaf.IsLocallyInjective (Opens.grothendieckTopology T) φ)
    (hs : Presheaf.IsLocallySurjective (Opens.grothendieckTopology T) φ) :
    IsIso (((sheafificationAdjunction (Opens.grothendieckTopology T)
      AddCommGrpCat.{u}).homEquiv P F).symm φ) := by
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology T)
      (toSheafify (Opens.grothendieckTopology T) P) :=
    GrothendieckTopology.W.isLocallySurjective (GrothendieckTopology.W_toSheafify _ _)
  have fac := toSheafify_comp_homEquiv_symm (F := F) φ
  refine (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨?_, ?_⟩
  · exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac _ _ fac
  · exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ fac

/-- The restriction of `toCrysFormsSheaf` to the ambient scheme of an object, read as a morphism
into the restriction of the sheaf `Ω^j_{X/S}` viewed as a presheaf of modules. -/
abbrev toCrysFormsSheafRestriction (A : CrystallineThickening S) (j : ℕ) :
    crysDifferentialFormsRestriction S A.obj j ⟶
      (PresheafOfModules.restrictScalars (𝟙 (Thickening.ringRestrictionSheaf A.obj).obj)).obj
        ((SheafOfModules.forget _).obj
          (CohomologyRestriction.moduleRestrictionSheaf (crysFormsSheaf S j) A)) :=
  CohomologyRestriction.moduleRestrictionMap (toCrysFormsSheaf S j) A

/-- `isLocallyInjective_restrict_toCrysFormsSheaf`, read on `toCrysFormsSheafRestriction`. -/
theorem isLocallyInjective_toCrysFormsSheafRestriction (A : CrystallineThickening S) (j : ℕ) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      ((PresheafOfModules.toPresheaf (Thickening.ringRestrictionSheaf A.obj).obj).map
        (toCrysFormsSheafRestriction A j)) :=
  isLocallyInjective_restrict_toCrysFormsSheaf A j

/-- `isLocallySurjective_restrict_toCrysFormsSheaf`, read on `toCrysFormsSheafRestriction`. -/
theorem isLocallySurjective_toCrysFormsSheafRestriction (A : CrystallineThickening S) (j : ℕ) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      ((PresheafOfModules.toPresheaf (Thickening.ringRestrictionSheaf A.obj).obj).map
        (toCrysFormsSheafRestriction A j)) :=
  isLocallySurjective_restrict_toCrysFormsSheaf A j

/-- **The comparison morphism from the sheaf associated with the restriction of the presheaf
`Ω^j_{X/S}` to the restriction of the sheaf `Ω^j_{X/S}`**, on the ambient scheme of an object. -/
def crysFormsSheafRestrictionHom (A : CrystallineThickening S) (j : ℕ) :
    (PresheafOfModules.sheafification (𝟙 (Thickening.ringRestrictionSheaf A.obj).obj)).obj
        (crysDifferentialFormsRestriction S A.obj j) ⟶
      CohomologyRestriction.moduleRestrictionSheaf (crysFormsSheaf S j) A :=
  (PresheafOfModules.sheafificationHomEquiv _).symm (toCrysFormsSheafRestriction A j)

/-- **The restriction of the sheaf `Ω^j_{X/S}` to the ambient scheme `T` of an object is the
sheaf associated with the restriction of the presheaf `Ω^j_{X/S}`**: the comparison morphism
`crysFormsSheafRestrictionHom` is an isomorphism, because the restriction of `toCrysFormsSheaf`
is locally injective and locally surjective. -/
theorem isIso_crysFormsSheafRestrictionHom (A : CrystallineThickening S) (j : ℕ) :
    IsIso (crysFormsSheafRestrictionHom A j) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _), crysFormsSheafRestrictionHom,
    PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  refine isIso_homEquiv_symm_of_isLocallyBijective _ ?_ ?_
  · exact isLocallyInjective_toCrysFormsSheafRestriction A j
  · exact isLocallySurjective_toCrysFormsSheafRestriction A j

/-- **Condition (1) of [Stacks, Tag 07JN] for the sheaf `Ω^j_{X/S}`: it is locally
quasi-coherent.**  Its restriction to the ambient scheme `T` of an object is the sheaf associated
with the restriction of the presheaf `Ω^j_{X/S}` (`isIso_crysFormsSheafRestrictionHom`), which is
`Ω^j_{T/S, δ}` and quasi-coherent (`isQuasicoherentOnSite_crysDifferentialFormsRestriction`). -/
theorem isLocallyQuasiCoherent_crysFormsSheaf (j : ℕ) :
    IsLocallyQuasiCoherent (crysFormsSheaf S j) := by
  intro A
  refine ⟨(CohomologyRestriction.moduleRestrictionSheaf (crysFormsSheaf S j) A).isSheaf, ?_⟩
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (@asIso _ _ _ _ (crysFormsSheafRestrictionHom A j) (isIso_crysFormsSheafRestrictionHom A j))
    (isQuasicoherentOnSite_crysDifferentialFormsRestriction S A.obj j)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
