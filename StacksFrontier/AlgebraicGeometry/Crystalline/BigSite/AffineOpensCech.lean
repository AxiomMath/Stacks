module

public import StacksFrontier.AlgebraicGeometry.AffineChartLocalization.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TrivialThickeningFunctor
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Local
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.DeRhamTypeComplexCech
public import StacksFrontier.CategoryTheory.Sites.CechComplexComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FinalCoverReindex

/-!
# The Čech complex of a module on the affine opens of a proper scheme

Let `f : X ⟶ S` be a morphism to an affine scheme and let `U_i`, `i ∈ ι`, be a finite family of
affine opens covering `X`, which on a scheme with affine diagonal have products in
`AffineOpens X` (their intersections).  For a sheaf of `𝒪_X`-modules `M`, the sections
`V ↦ Γ(V, M)` over the affine opens, read as `Γ(S, 𝒪_S)`-modules, form a presheaf on
`AffineOpens X` (`AffineOpens.moduleSections`), and its Čech complex along `U` in the sense of
`Stacks.CechSite.FinalCover.complexFunctor` is the Čech complex of `M` for the cover of `X`
by the `U_i`, read over `Γ(S, 𝒪_S)` (`AffineOpens.cechComplexIso`).  Hence:

* if `f` is proper, `S` is Noetherian and `M` is coherent, its cohomology is a finite
  `Γ(S, 𝒪_S)`-module in every degree (by [Stacks, Tag 01XD] and [Stacks, Tag 02O6]);
* if `X` has affine diagonal and `M` is quasi-coherent, its cohomology vanishes in every degree
  `≥ #ι` (by [Stacks, Tag 01XD] and [Stacks, Tag 01XI]).

## Main definitions

* `Crystalline.GlobalCrystallineSituation.AffineOpens.toOverTop` — an affine open `V` as an object
  of the slice `Over ⊤` of the opens of `X`.
* `Crystalline.GlobalCrystallineSituation.AffineOpens.moduleSections` — `V ↦ Γ(V, M)` over
  `Γ(S, 𝒪_S)`.
* `Crystalline.GlobalCrystallineSituation.AffineOpens.cechComplexIso` — the comparison of Čech
  complexes.

## Main results

* `Crystalline.GlobalCrystallineSituation.AffineOpens.moduleFinite_homology_moduleSections`
* `Crystalline.GlobalCrystallineSituation.AffineOpens.isZero_homology_moduleSections`

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe w u

namespace Crystalline.GlobalCrystallineSituation.AffineOpens

open Stacks.CechSite.FinalCover

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- `f^♯ : Γ(S, 𝒪_S) ⟶ Γ(X, 𝒪_X)`, with its target read as the ring of sections of the sheaf of
rings `X.ringCatSheaf`, over which the sections of an `𝒪_X`-module are modules. -/
abbrev baseHom : Γ(S, ⊤) →+* ↑(X.ringCatSheaf.obj.obj (op ⊤)) :=
  f.appTop.hom

/-- An affine open `V` of `X`, as the object `V ⟶ ⊤` of the slice of the opens of `X` over the
whole space. -/
def toOverTop (X : Scheme.{u}) : AffineOpens X ⥤ Over (⊤ : X.Opens) where
  obj V := Over.mk (homOfLE le_top)
  map g := Over.homMk g.hom

/-- **The sections of a sheaf of `𝒪_X`-modules over the affine opens of `X`, read as
`Γ(S, 𝒪_S)`-modules** through `f^♯ : Γ(S, 𝒪_S) ⟶ Γ(X, 𝒪_X)` and restriction. -/
abbrev moduleSections (M : X.Modules) : (AffineOpens X)ᵒᵖ ⥤ ModuleCat.{u} Γ(S, ⊤) :=
  (toOverTop X).op ⋙ Stacks.Cohomology.CechSheaf.sectionsPresheaf ⊤ M ⋙
    ModuleCat.restrictScalars (baseHom f)

section Cover

variable [IsAffineHom (pullback.diagonal (terminal.from X))] {ι : Type u} [Finite ι]
  (U : ι → AffineOpens X) (hU : ⨆ i, (U i).obj = ⊤)

/-- The members of the cover, as opens. -/
abbrev opens : ι → X.Opens := fun i ↦ (U i).obj

/-- The comparison maps `toOverTop (U i) ⟶ coverObject` (identities). -/
def coverComparison (i : ι) :
    (toOverTop X).obj (U i) ⟶
      Stacks.Cohomology.CechSheaf.coverObject (opens U) hU.symm i :=
  Over.homMk (𝟙 _)

omit [Finite ι] in
/-- The products of the members of the cover in `AffineOpens X` are carried to their products
in `Over ⊤`. -/
theorem isIso_interComparison (n : ℕ) (x : Fin (n + 1) → ι) :
    IsIso (interComparison (toOverTop X) (coverComparison U hU) x) := by
  have hle : (inter (Stacks.Cohomology.CechSheaf.coverObject (opens U) hU.symm) x).left ≤
      ((toOverTop X).obj (inter U x)).left :=
    le_trans (le_iInf fun a ↦ leOfHom
      (interπ (Stacks.Cohomology.CechSheaf.coverObject (opens U) hU.symm) x a).left)
      (piObj_obj fun a ↦ U (x a)).ge
  refine ⟨Over.homMk (homOfLE hle), ?_, ?_⟩ <;>
    exact Over.OverMorphism.ext (Subsingleton.elim _ _)

/-- **The Čech complex of `V ↦ Γ(V, M)` along the cover by the `U_i` is the Čech complex of `M`
for the cover of `X` by the `U_i`, read over `Γ(S, 𝒪_S)`.** -/
def cechComplexIso (M : X.Modules) :
    (complexFunctor U (ModuleCat.{u} Γ(S, ⊤))).obj (moduleSections f M) ≅
      ((ModuleCat.restrictScalars (baseHom f)).mapHomologicalComplex _).obj
        (Stacks.Cohomology.CechSheaf.cechComplex.{u, u, u, u} ⊤ (opens U) hU.symm M) :=
  have := isIso_complexComparison_app (A := ModuleCat.{u} Γ(S, ⊤)) (toOverTop X)
    (coverComparison U hU) (isIso_interComparison U hU)
    (Stacks.Cohomology.CechSheaf.sectionsPresheaf ⊤ M ⋙
      ModuleCat.restrictScalars (baseHom f))
  (asIso ((complexComparison (ModuleCat.{u} Γ(S, ⊤)) (toOverTop X)
      (coverComparison U hU)).app
    (Stacks.Cohomology.CechSheaf.sectionsPresheaf ⊤ M ⋙
      ModuleCat.restrictScalars (baseHom f)))).symm ≪≫
    ((Functor.mapHomologicalComplexIdIso _ _).app _).symm ≪≫
    (Stacks.CategoryTheory.CechComplex.cechComparisonIsoOfAdditive
      (Stacks.Cohomology.CechSheaf.coverObject (opens U) hU.symm)
      (Stacks.Cohomology.CechSheaf.coverObject (opens U) hU.symm)
      (Stacks.Cohomology.CechSheaf.sectionsPresheaf ⊤ M)
      (Stacks.Cohomology.CechSheaf.sectionsPresheaf ⊤ M ⋙
        ModuleCat.restrictScalars (baseHom f))
      (ModuleCat.restrictScalars (baseHom f)) (𝟭 _)
      (fun _ ↦ Iso.refl _) (fun _ _ ↦ by simp)).symm

omit [Finite ι] in
/-- The affine opens selected by a tuple intersect in an affine open. -/
theorem isAffineOpen_iInf_opens (r : ℕ) (s : Fin (r + 1) → ι) :
    IsAffineOpen (⨅ j, opens U (s j)) :=
  IsAffineOpen.iInf fun j ↦ (U (s j)).property

/-- **The cohomology of the Čech complex of `V ↦ Γ(V, M)` is the cohomology of `M`**, for a
quasi-coherent `M`, read over `Γ(S, 𝒪_S)`: [Stacks, Tag 01XD]. -/
def homologyIso (M : X.Modules) [M.IsQuasicoherent] (r : ℕ) :
    ((complexFunctor U (ModuleCat.{u} Γ(S, ⊤))).obj (moduleSections f M)).homology r ≅
      (ModuleCat.restrictScalars (baseHom f)).obj
        (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived r).obj M) :=
  haveI := Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars (baseHom f)
  (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) r).mapIso
      (cechComplexIso f U hU M) ≪≫
    ((Stacks.Cohomology.CechSheaf.cechComplex.{u, u, u, u} ⊤ (opens U) hU.symm M).sc
      r).mapHomologyIso (ModuleCat.restrictScalars (baseHom f)) ≪≫
    (ModuleCat.restrictScalars (baseHom f)).mapIso
      (rightDerivedEvaluationCechHomologyIso X ⊤ (opens U) hU.symm
        (isAffineOpen_iInf_opens U) M r).symm

include hU in
/-- **The Čech cohomology of `V ↦ Γ(V, M)` along a finite affine cover vanishes in degrees
`≥ #ι`**, for `M` quasi-coherent on a scheme with affine diagonal: it is `H^r(X, M)`, which
vanishes there by [Stacks, Tag 01XI]. -/
theorem isZero_homology_moduleSections (M : X.Modules) [M.IsQuasicoherent] (r : ℕ)
    (hr : Nat.card ι ≤ r) :
    IsZero (((complexFunctor U (ModuleCat.{u} Γ(S, ⊤))).obj (moduleSections f M)).homology r) := by
  refine IsZero.of_iso (Functor.map_isZero _ ?_) (homologyIso f U hU M r)
  let e := Finite.equivFin ι
  refine Stacks.Cohomology.Cech.isZero_rightDerived_evaluation_of_isZero_hgroup X ⊤ M r ?_
  refine Stacks.Cohomology.AffineCover.isZero_cohomology_of_finite_affine_cover X
    (opens U ∘ e.symm) (fun i ↦ (U (e.symm i)).property) ?_ M r hr
  rw [← hU]
  exact e.symm.iSup_comp

include hU in
/-- **The Čech cohomology of `V ↦ Γ(V, M)` along a finite affine cover is finite**, for `M`
coherent on a scheme proper over a Noetherian affine scheme: it is `H^r(X, M)`, which is a finite
`Γ(S, 𝒪_S)`-module by [Stacks, Tag 02O6]. -/
theorem moduleFinite_homology_moduleSections [IsAffine S] [IsLocallyNoetherian S] [IsProper f]
    (M : X.Modules) [M.IsCoherent] (r : ℕ) :
    Module.Finite Γ(S, ⊤)
      (((complexFunctor U (ModuleCat.{u} Γ(S, ⊤))).obj (moduleSections f M)).homology r) := by
  have : M.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent M
  have hfin := ProperCoherenceWitness.moduleFinite_cohomology f M r
  exact @Module.Finite.equiv _ _ _ _ _ _ _ _ hfin (homologyIso f U hU M r).symm.toLinearEquiv

end Cover

/-! ### Presheaves of modules which localize on the basic opens -/

section Localizing

open Stacks.AlgebraicGeometry.AffineChartLocalization
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

attribute [local instance] sectionsModule

variable (P : PresheafOfModules.{u} X.ringCatSheaf.obj)

/-- **A presheaf of `𝒪_X`-modules localizes on the basic opens of the affine opens** when, for
every affine open `V` and `g ∈ Γ(V, 𝒪_X)`, the restriction map `P(V) → P(D(g))` is a localization
away from `g`. -/
def IsLocalizing : Prop :=
  ∀ (V : X.Opens), IsAffineOpen V → ∀ (g : Γ(X, V)) {W : X.Opens} (_ : W = X.basicOpen g)
    (hWV : W ≤ V),
    letI := presheafModuleOfLE P hWV
    IsLocalizedModule.Away g (presheafRestrictₗ P hWV)

/-- The sections of a presheaf of `𝒪_X`-modules over every affine open are finite modules. -/
def IsFiniteOnAffines : Prop :=
  ∀ V : X.Opens, IsAffineOpen V → Module.Finite Γ(X, V) (P.obj (op V))

/-- The sheaf of `𝒪_X`-modules associated with a presheaf of `𝒪_X`-modules. -/
abbrev sheafify : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P

variable {P}

/-- **Over an affine open, the sections of the associated sheaf of a localizing presheaf are its
sections**: the sheafification unit is bijective there
(`Stacks.AlgebraicGeometry.AffineChartLocalization.bijective_sheafifyUnit_app_of_isAffineOpen`). -/
theorem bijective_sheafifyUnit_app (hP : IsLocalizing P) {V : X.Opens} (hV : IsAffineOpen V) :
    Function.Bijective (PresheafOfModules.Hom.app
      (PresheafOfModules.sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) P) (op V)) :=
  bijective_sheafifyUnit_app_of_isAffineOpen P hV fun g _ hW hWV ↦ hP V hV g hW hWV

/-- The sheafification unit over an affine open, as a linear equivalence. -/
def sheafifyEquiv (hP : IsLocalizing P) {V : X.Opens} (hV : IsAffineOpen V) :
    P.obj (op V) ≃ₗ[Γ(X, V)] Γ(sheafify P, V) :=
  { AddEquiv.ofBijective (PresheafOfModules.Hom.app
        (PresheafOfModules.sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) P)
          (op V)).hom.toAddMonoidHom (bijective_sheafifyUnit_app hP hV) with
    map_smul' := fun r x ↦ (PresheafOfModules.Hom.app
        (PresheafOfModules.sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) P)
          (op V)).hom.map_smul r x }

/-- `sheafifyEquiv` is the sheafification unit. -/
theorem sheafifyEquiv_apply (hP : IsLocalizing P) {V : X.Opens} (hV : IsAffineOpen V)
    (x : P.obj (op V)) :
    sheafifyEquiv hP hV x = PresheafOfModules.Hom.app
      (PresheafOfModules.sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) P) (op V) x :=
  rfl

/-- The sheafification unit commutes with restriction. -/
theorem sheafifyUnit_restrict {V W : X.Opens} (h : W ≤ V) (x : P.obj (op V)) :
    (sheafify P).presheaf.map (homOfLE h).op (PresheafOfModules.Hom.app
      (PresheafOfModules.sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) P) (op V) x) =
      PresheafOfModules.Hom.app
        (PresheafOfModules.sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) P) (op W)
        (P.map (homOfLE h).op x) :=
  (PresheafOfModules.naturality_apply
    (PresheafOfModules.sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) P)
    (homOfLE h).op x).symm

/-- **The sheaf associated with a localizing presheaf is quasi-coherent**: over an affine open
its sections are those of the presheaf, compatibly with restriction to the basic opens, so they
localize. -/
theorem isQuasicoherent_sheafify (hP : IsLocalizing P) : (sheafify P).IsQuasicoherent := by
  refine
    Stacks.AlgebraicGeometry.TorsionQuasicoherent.isQuasicoherent_of_isLocalizedModule_restrictₗ
      _ fun U hU a ↦ ?_
  let := moduleOfLE (sheafify P) (X.basicOpen_le a)
  let := presheafModuleOfLE P (X.basicOpen_le a)
  have hloc := hP U hU a rfl (X.basicOpen_le a)
  let eD : P.obj (op (X.basicOpen a)) ≃ₗ[Γ(X, U)] Γ(sheafify P, X.basicOpen a) :=
    { sheafifyEquiv hP (hU.basicOpen a) with
      map_smul' := fun r x ↦ (sheafifyEquiv hP (hU.basicOpen a)).map_smul
        (X.presheaf.map (homOfLE (X.basicOpen_le a)).op r) x }
  have h1 := IsLocalizedModule.of_linearEquiv (Submonoid.powers a)
    (presheafRestrictₗ P (X.basicOpen_le a)) eD
  have h2 := IsLocalizedModule.of_linearEquiv_right (Submonoid.powers a)
    (eD.toLinearMap ∘ₗ presheafRestrictₗ P (X.basicOpen_le a)) (sheafifyEquiv hP hU).symm
  convert h2 using 1
  refine LinearMap.ext fun y ↦ ?_
  obtain ⟨x, rfl⟩ := (sheafifyEquiv hP hU).surjective y
  change (sheafify P).presheaf.map _ (sheafifyEquiv hP hU x) = eD _
  simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [sheafifyEquiv_apply, sheafifyUnit_restrict]
  rfl

/-- **The sheaf associated with a localizing presheaf whose sections over the affine opens are
finite is of finite type.** -/
theorem isFiniteType_sheafify (hP : IsLocalizing P) (hfin : IsFiniteOnAffines P) :
    (sheafify P).IsFiniteType :=
  have := isQuasicoherent_sheafify hP
  Stacks.AlgebraicGeometry.TopDegreeFiniteType.isFiniteType_of_forall_moduleFinite_sections _
    fun V ↦ have := hfin V.1 V.2
    Module.Finite.equiv (sheafifyEquiv hP V.2)

/-- **The sheaf associated with a localizing presheaf whose sections over the affine opens are
finite is coherent**, on a locally Noetherian scheme ([Stacks, Tag 01XZ]). -/
theorem isCoherent_sheafify [IsLocallyNoetherian X] (hP : IsLocalizing P)
    (hfin : IsFiniteOnAffines P) :
    (sheafify P).IsCoherent :=
  have := isQuasicoherent_sheafify hP
  have := isFiniteType_sheafify hP hfin
  Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType _

end Localizing

section LocalizingSections

open Stacks.AlgebraicGeometry.AffineChartLocalization

variable {P : PresheafOfModules.{u} X.ringCatSheaf.obj}

variable (P) in
/-- **The sections of a presheaf of `𝒪_X`-modules over the affine opens of `X`, read as
`Γ(S, 𝒪_S)`-modules** through `f^♯` and restriction. -/
abbrev presheafSections : (AffineOpens X)ᵒᵖ ⥤ ModuleCat.{u} Γ(S, ⊤) :=
  (AffineOpens.ι X).op ⋙
    (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj P ⋙
      ModuleCat.restrictScalars (baseHom f)

/-- The sections over the affine opens of the sheaf associated with a presheaf of modules, read
over `Γ(X, 𝒪_X)`, in the two spellings of the library: through
`PresheafOfModules.forgetToPresheafModuleCat` and through the slice over `⊤`. -/
def sheafifySectionsIso :
    (AffineOpens.ι X).op ⋙
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (PresheafOfModules.sheafifyRestrict (𝟙 X.ringCatSheaf.obj) P) ≅
      (toOverTop X).op ⋙ Stacks.Cohomology.CechSheaf.sectionsPresheaf ⊤ (sheafify P) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

variable (P) in
/-- The sheafification unit on the sections over the affine opens, read over `Γ(X, 𝒪_X)`. -/
def sheafifyUnitSections :
    (AffineOpens.ι X).op ⋙
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj P ⟶
      (AffineOpens.ι X).op ⋙
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (PresheafOfModules.sheafifyRestrict (𝟙 X.ringCatSheaf.obj) P) :=
  Functor.whiskerLeft _ ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
    (PresheafOfModules.sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) P))

/-- For a localizing presheaf the sheafification unit is an isomorphism on the sections over the
affine opens. -/
theorem isIso_sheafifyUnitSections (hP : IsLocalizing P) : IsIso (sheafifyUnitSections P) := by
  have (V : (AffineOpens X)ᵒᵖ) : IsIso ((sheafifyUnitSections P).app V) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_sheafifyUnit_app hP V.unop.property)
  exact NatIso.isIso_of_isIso_app _

/-- **The sections of a localizing presheaf over the affine opens are the sections of its
associated sheaf**, naturally, as `Γ(X, 𝒪_X)`-modules. -/
def presheafSectionsTopIso (hP : IsLocalizing P) :
    (AffineOpens.ι X).op ⋙
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj P ≅
      (toOverTop X).op ⋙ Stacks.Cohomology.CechSheaf.sectionsPresheaf ⊤ (sheafify P) :=
  haveI := isIso_sheafifyUnitSections hP
  asIso (sheafifyUnitSections P) ≪≫ sheafifySectionsIso

/-- **The sections of a localizing presheaf over the affine opens are the sections of its
associated sheaf**, naturally, as `Γ(S, 𝒪_S)`-modules. -/
def presheafSectionsIso (hP : IsLocalizing P) :
    presheafSections f P ≅ moduleSections f (sheafify P) :=
  Functor.isoWhiskerRight (presheafSectionsTopIso hP) (ModuleCat.restrictScalars (baseHom f))

end LocalizingSections

/-! ### The Čech complex of a localizing presheaf on the affine opens -/

section CechLocalizing

variable [IsAffineHom (pullback.diagonal (terminal.from X))] {ι : Type w} [Finite ι]
  [HasProducts.{w} (ModuleCat.{u} Γ(S, ⊤))]
  (U : ι → AffineOpens X) (hU : ⨆ i, (U i).obj = ⊤)
  {P : PresheafOfModules.{u} X.ringCatSheaf.obj}

/-- The Čech complex of the sections of a localizing presheaf along `U`, reindexed by
`Shrink ι`, is that of the sections of its associated sheaf. -/
def presheafSectionsCechIso (hP : IsLocalizing P) :
    (complexFunctor U (ModuleCat.{u} Γ(S, ⊤))).obj (presheafSections f P) ≅
      (complexFunctor (fun j ↦ U ((equivShrink.{u} ι).symm j)) (ModuleCat.{u} Γ(S, ⊤))).obj
        (moduleSections f (sheafify P)) :=
  (complexFunctor U (ModuleCat.{u} Γ(S, ⊤))).mapIso (presheafSectionsIso f hP) ≪≫
    reindexIso U (equivShrink.{u} ι).symm _

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
include hU in
/-- The members of the reindexed cover cover `X`. -/
theorem iSup_shrink_eq_top : ⨆ j, (U ((equivShrink.{u} ι).symm j)).obj = ⊤ :=
  ((equivShrink.{u} ι).symm.iSup_comp (g := fun i ↦ (U i).obj)).trans hU

include hU in
/-- **The Čech cohomology of the sections over the affine opens of a localizing presheaf of
`𝒪_X`-modules, along a finite affine cover, vanishes in degrees `≥ #ι`.** -/
theorem isZero_homology_presheafSections (hP : IsLocalizing P) (r : ℕ) (hr : Nat.card ι ≤ r) :
    IsZero (((complexFunctor U (ModuleCat.{u} Γ(S, ⊤))).obj (presheafSections f P)).homology r) :=
  have := isQuasicoherent_sheafify hP
  IsZero.of_iso (isZero_homology_moduleSections f _ (iSup_shrink_eq_top U hU) (sheafify P) r
      ((Nat.card_congr (equivShrink.{u} ι).symm).trans_le hr))
    (HomologicalComplex.homologyMapIso (presheafSectionsCechIso f U hP) r)

include hU in
/-- **The Čech cohomology of the sections over the affine opens of a localizing presheaf of
`𝒪_X`-modules with finite sections, along a finite affine cover of a scheme proper over a
Noetherian affine scheme, is finite**: the presheaf is the sections of a coherent module. -/
theorem moduleFinite_homology_presheafSections [IsAffine S] [IsLocallyNoetherian S] [IsProper f]
    (hP : IsLocalizing P) (hfin : IsFiniteOnAffines P) (r : ℕ) :
    Module.Finite Γ(S, ⊤)
      (((complexFunctor U (ModuleCat.{u} Γ(S, ⊤))).obj (presheafSections f P)).homology r) :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := isCoherent_sheafify hP hfin
  @Module.Finite.equiv _ _ _ _ _ _ _ _
    (moduleFinite_homology_moduleSections f _ (iSup_shrink_eq_top U hU) (sheafify P) r)
    (HomologicalComplex.homologyMapIso (presheafSectionsCechIso f U hP) r).symm.toLinearEquiv

end CechLocalizing

end Crystalline.GlobalCrystallineSituation.AffineOpens
