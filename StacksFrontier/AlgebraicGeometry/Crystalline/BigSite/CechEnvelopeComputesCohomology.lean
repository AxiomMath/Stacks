module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeCovering
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeProducts
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BigModuleAbelianComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleRestrictionAcyclicity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleRestrictionCohomologyULift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FinalCoverDerived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedSectionsOnABigSite

/-!
# The Čech complex of the smooth-lift objects computes crystalline cohomology

Fix a global crystalline situation `(p, (S, I, γ), X)` with `S` affine, `A = Γ(S, 𝒪_S)`, `p`
nilpotent in `A` and `X` separated, a family `{U_i}` of affine opens covering `X` and smooth lifts
`L_i` of the `U_i`, with objects `D_i = (U_i, Spec B_i, γ_i)` of `CRIS(X/S)`
(`CechEnvelope.cechObjects`). For a quasi-coherent `𝒪_{X/S}`-module `N` this file proves that the
Čech complex `Č(D, N)`, `Č^n(D, N) = ∏_{x : Fin (n + 1) → ι} N(D_{x 0} × ⋯ × D_{x n})`, computes
`RΓ(CRIS(X/S), N)` in the bounded below derived category of `A`-modules
(`CechEnvelope.cechEnvelopeDerivedIso`), and hence that the two have the same cohomology
`A`-modules (`CechEnvelope.cechEnvelopeHomologyIso`).

This is `Stacks.CechSite.FinalCover.cechDerivedIso`, the Čech-to-derived comparison for a family
covering the final object, applied to the family `{D_i}`. Its three inputs are:

* the family covers the final object (`CechEnvelope.coversTop_object`);
* the finite products `D_x` exist and are the divided power envelopes of
  `U_{x 0} ∩ ⋯ ∩ U_{x n} ⟶ Y_{x 0} ×_S ⋯ ×_S Y_{x n}` (`CechEnvelope.hasProduct_object`,
  `CechEnvelope.interIsoEnvelopeObject`);
* the higher module-valued cohomology of `N` vanishes over each `D_x`
  (`CechEnvelope.isZero_rightDerived_evaluation_inter`). The vanishing proved in
  `CechEnvelopeProducts.lean` is that of the *abelian* sections functor; it is transported to the
  module-valued sections functor by [Stacks, Tag 03FD] over an object of `CRIS(X/S)`
  (`CechEnvelope.isZero_rightDerived_evaluation_of_isZero`), the sections over `T` being
  corepresented on abelian sheaves by the free abelian sheaf on the representable at `T`, which is
  sectionwise torsion free.

The derived global sections of the comparison,
`Stacks.CechSite.FinalCover.derivedGlobalSectionsFunctor` at the ring map
`bigBaseRingHom : A ⟶ Γ(CRIS(X/S), 𝒪_{X/S})`, are by definition the derived global sections
`SmallSite.derivedBigModuleGlobalSections` of the chapter
(`CechEnvelope.derivedGlobalSectionsFunctor_eq`).

## Main results

* `CechEnvelope.isZero_rightDerived_evaluation_of_isZero` — [Stacks, Tag 03FD] over an object of
  `CRIS(X/S)`, in the form of a vanishing transfer.
* `CechEnvelope.cechEnvelopeToDerived` — the comparison `Č(D, -) ⟶ RΓ(CRIS(X/S), -)`.
* **`CechEnvelope.cechEnvelopeDerivedIso`** — `Č(D, N) ≅ RΓ(CRIS(X/S), N)` in `D⁺(A)` for `N`
  quasi-coherent.
* `CechEnvelope.cechEnvelopeHomologyIso`, `CechEnvelope.cechEnvelopeComplexHomologyIso` —
  `H^j(Č(D, N)) ≅ H^j(CRIS(X/S), N)` as `A`-modules, the left side read in `D⁺(A)` or as the
  cohomology of the Čech complex itself.

## References

* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 03F7](https://stacks.math.columbia.edu/tag/03F7)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite CategoryTheory.Abelian

universe v₂ v₃ u

namespace Crystalline.GlobalCrystallineSituation.CechEnvelope

open SmallSite

/-! ### 03FD over an object of the big crystalline site -/

section ObjectSections

variable (S : GlobalCrystallineSituation.{u})

/-- Sections over an object of the big crystalline site are additive. -/
instance (priority := high) additive_sheafSections_obj_thickening (T : Thickening S) :
    ((sheafSections (topology S) AddCommGrpCat.{u + 1}).obj (op T)).Additive where
  map_add := rfl

/-- Sections over an object of the big crystalline site preserve finite limits of abelian
sheaves: they are evaluation of the underlying presheaf. -/
instance preservesFiniteLimits_sheafSections_obj_thickening (T : Thickening S) :
    PreservesFiniteLimits ((sheafSections (topology S) AddCommGrpCat.{u + 1}).obj (op T)) :=
  inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf (topology S) AddCommGrpCat.{u + 1} ⋙
    (evaluation _ _).obj (op T)))

/-- The free abelian presheaf on the representable at `T`, at the coefficient universe `u + 1`. -/
abbrev freeRepresentable (T : Thickening S) : (Thickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  Presheaf.freeAbelian.obj (uliftYoneda.{u + 1}.obj T)

/-- The free abelian presheaf on a representable is sectionwise torsion free. -/
theorem isTorsionFree_freeRepresentable (T : Thickening S) (A : (Thickening S)ᵒᵖ) :
    Module.IsTorsionFree ℤ ((freeRepresentable S T).obj A) := by
  change Module.IsTorsionFree ℤ (FreeAbelianGroup (ULift.{u + 1} (A.unop ⟶ T)))
  exact Module.Flat.isTorsionFree

/-- **[Stacks, Tag 03FD] over an object of `CRIS(X/S)`, as a vanishing transfer.** If the higher
cohomology over `T` of the underlying abelian sheaf of a sheaf of `𝒪_{X/S}`-modules `M` vanishes in
degree `q + 1`, so does the `(q + 1)`-st right derived functor of module-valued sections over `T`
at `M`.

Sections over `T` are corepresented on abelian sheaves by the sheafified free abelian presheaf on
the representable at `T`, and on modules by its sheafified extension of scalars; the underlying
abelian sheaf of an injective module is `Ext`-acyclic against it, the presheaf being sectionwise
torsion free. `ModuleSheafCohomology.comparisonIso` then identifies the right derived functors of
the composite with those of the abelian sections functor, and the composite is the module-valued
sections functor followed by the forgetful functor, which reflects exactness. -/
theorem isZero_rightDerived_evaluation_of_isZero (T : Thickening S) (M : BigModuleSheaf S)
    (q : ℕ)
    (hM : IsZero ((((sheafSections (topology S) AddCommGrpCat.{u + 1}).obj (op T)).rightDerived
      (q + 1)).obj ((bigToAbelianSheaf S).obj M))) :
    IsZero (((SheafOfModules.evaluation (crystallineStructureSheaf S) (op T)).rightDerived
      (q + 1)).obj M) := by
  let G := (sheafSections (topology S) AddCommGrpCat.{u + 1}).obj (op T)
  let P := freeRepresentable S T
  let X : Sheaf (topology S) AddCommGrpCat.{u + 1} :=
    (presheafToSheaf (topology S) AddCommGrpCat.{u + 1}).obj P
  let α : G ≅ preadditiveCoyoneda.obj (op X) :=
    (Stacks.Cohomology.DerivedLowerShriek.BigSite.abelianSectionsCorepresentation.{0}
      (topology S) T).symm
  let β := Stacks.SheafOfModules.tensorSheafHomIso.{u + 1, u, u, u + 1} (topology S)
    (crystallineStructureSheaf S) P
  have h : ∀ (I : BigModuleSheaf S) [Injective I] (n : ℕ)
      (e : Ext.{u + 1} X ((bigToAbelianSheaf S).obj I) (n + 1)), e = 0 :=
    fun I _ n e ↦ Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree.{u + 1, u + 1, u, u, u + 1}
      (topology S) (crystallineStructureSheaf S) I X
      (ModuleSheafCohomology.isTorsionFree_sheafify (topology S) P
        (isTorsionFree_freeRepresentable S T)) n e
  have h1 : IsZero (((bigToAbelianSheaf S ⋙ G).rightDerived (q + 1)).obj M) :=
    hM.of_iso ((ModuleSheafCohomology.comparisonIso (bigToAbelianSheaf S) G X α _ β h
      (q + 1)).app M)
  let I := injectiveResolution M
  have h2 : IsZero ((((bigToAbelianSheaf S ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex).homology (q + 1)) :=
    h1.of_iso (I.isoRightDerivedObj (bigToAbelianSheaf S ⋙ G) (q + 1)).symm
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff] at h2
  let E := SheafOfModules.evaluation (crystallineStructureSheaf S) (op T)
  have hex : ((E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).ExactAt (q + 1) := by
    rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    exact fun x hx ↦ h2 x hx
  exact hex.isZero_homology.of_iso (I.isoRightDerivedObj E (q + 1))

end ObjectSections

/-! ### The smooth-lift objects and their products -/

section Objects

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) [S.X.IsSeparated] {ι : Type}
  {U : ι → S.X.Opens} [∀ i, IsAffine (U i)] (L : ∀ i, SmoothLift S (U i).ι)

/-- The objects `D_i = (U_i, Spec B_i, γ_i)` of `CRIS(X/S)` of the smooth lifts `L_i`. -/
abbrev cechObjects : ι → Thickening S := fun i ↦ (L i).object hp

/-- The finite nonempty products `D_x = D_{x 0} × ⋯ × D_{x n}` of the smooth-lift objects exist. -/
instance hasProduct_cechObjects (n : ℕ) (x : Fin (n + 1) → ι) :
    HasProduct (fun a ↦ cechObjects hp L (x a)) :=
  hasProduct_object hp (fun a ↦ L (x a))

/-- **The product `D_x` is the divided power envelope object** of
`U_{x 0} ∩ ⋯ ∩ U_{x n} ⟶ Y_{x 0} ×_S ⋯ ×_S Y_{x n}`. -/
def interIsoEnvelopeObject {n : ℕ} (x : Fin (n + 1) → ι) :
    Stacks.CechSite.FinalCover.inter (cechObjects hp L) x ≅
      envelopeObject hp (fun a ↦ L (x a)) :=
  piIsoEnvelopeObject hp (fun a ↦ L (x a))

/-- The identification of `D_x` with the envelope object is compatible with the projections. -/
@[reassoc (attr := simp)]
theorem interIsoEnvelopeObject_hom_proj {n : ℕ} (x : Fin (n + 1) → ι) (a : Fin (n + 1)) :
    (interIsoEnvelopeObject hp L x).hom ≫ proj hp (fun a ↦ L (x a)) a =
      Stacks.CechSite.FinalCover.interπ (cechObjects hp L) x a :=
  piIsoEnvelopeObject_hom_proj hp (fun a ↦ L (x a)) a

/-- **A quasi-coherent module has no higher module-valued cohomology over the products `D_x`.**
The abelian vanishing `isZero_bigRightDerivedSections_pi` transported along 03FD over an
object. -/
theorem isZero_rightDerived_evaluation_inter
    (N : SheafOfModules.{u} (crystallineStructureSheaf S)) (hN : N.IsQuasicoherentOnSite)
    (n : ℕ) (x : Fin (n + 1) → ι) (m : ℕ) (hm : 0 < m) :
    IsZero (((SheafOfModules.evaluation (crystallineStructureSheaf S)
      (op (Stacks.CechSite.FinalCover.inter (cechObjects hp L) x))).rightDerived m).obj
        ((bigModuleULift S).obj N)) := by
  obtain ⟨q, rfl⟩ : ∃ q, m = q + 1 := ⟨m - 1, by lia⟩
  exact isZero_rightDerived_evaluation_of_isZero S _ _ q
    (isZero_bigRightDerivedSections_pi hp (fun a ↦ L (x a)) N hN (q + 1) (by lia))

end Objects

/-! ### The comparison -/

section Comparison

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) [S.X.IsSeparated] {ι : Type}
  {U : ι → S.X.Opens} [∀ i, IsAffine (U i)] (hU : ∀ x, ∃ i, x ∈ U i)
  (L : ∀ i, SmoothLift S (U i).ι)
  [HasDerivedCategory.{v₂} (BigModuleSheaf S)]
  [HasDerivedCategory.{v₃} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]

omit [IsAffine S.S.scheme] [S.X.IsSeparated] in
variable (S) in
/-- **The derived global sections of the Čech comparison are those of the chapter**: at the ring
map `bigBaseRingHom : A ⟶ Γ(CRIS(X/S), 𝒪_{X/S})`, the derived global sections functor of
`Stacks.CechSite.FinalCover` is `derivedBigModuleGlobalSections`, on the nose. -/
theorem derivedGlobalSectionsFunctor_eq :
    Stacks.CechSite.FinalCover.derivedGlobalSectionsFunctor.{0, u, u + 1, u, u}
      (crystallineStructureSheaf S) (bigBaseRingHom S) = derivedBigModuleGlobalSections S :=
  rfl

/-- **The Čech comparison `Č(D, -) ⟶ RΓ(CRIS(X/S), -)`** for the family of smooth-lift objects,
natural in the sheaf of `𝒪_{X/S}`-modules: `Stacks.CechSite.FinalCover.cechToDerivedGlobalSections`
for the covering of the final object of `CRIS(X/S)` by the `D_i`. -/
def cechEnvelopeToDerived :
    Stacks.CechSite.FinalCover.cechDerivedFunctor (crystallineStructureSheaf S)
        (bigBaseRingHom S) (cechObjects hp L) ⟶
      derivedBigModuleGlobalSections S :=
  Stacks.CechSite.FinalCover.cechToDerivedGlobalSections (crystallineStructureSheaf S)
    (bigBaseRingHom S) (cechObjects hp L) (coversTop_object hp U hU L)

/-- **The Čech comparison is an isomorphism at a quasi-coherent module.** -/
theorem isIso_cechEnvelopeToDerived_app
    (N : SheafOfModules.{u} (crystallineStructureSheaf S)) (hN : N.IsQuasicoherentOnSite) :
    IsIso ((cechEnvelopeToDerived hp hU L).app ((bigModuleULift S).obj N)) :=
  Stacks.CechSite.FinalCover.isIso_cechToDerivedGlobalSections_app _ _ _ _ _
    (isZero_rightDerived_evaluation_inter hp L N hN)

/-- **The Čech complex of the smooth-lift objects computes crystalline cohomology**: for a
quasi-coherent `𝒪_{X/S}`-module `N`, `Č(D, N) ≅ RΓ(CRIS(X/S), N)` in the bounded below derived
category of `A`-modules, `A = Γ(S, 𝒪_S)`; it is the component at `N` of the natural comparison
`cechEnvelopeToDerived`. -/
def cechEnvelopeDerivedIso
    (N : SheafOfModules.{u} (crystallineStructureSheaf S)) (hN : N.IsQuasicoherentOnSite) :
    (Stacks.CechSite.FinalCover.cechDerivedFunctor (crystallineStructureSheaf S)
        (bigBaseRingHom S) (cechObjects hp L)).obj ((bigModuleULift S).obj N) ≅
      (derivedBigModuleGlobalSections S).obj ((bigModuleULift S).obj N) :=
  haveI := isIso_cechEnvelopeToDerived_app hp hU L N hN
  asIso ((cechEnvelopeToDerived hp hU L).app ((bigModuleULift S).obj N))

/-- `cechEnvelopeDerivedIso` is the component of the natural comparison. -/
@[simp]
theorem cechEnvelopeDerivedIso_hom
    (N : SheafOfModules.{u} (crystallineStructureSheaf S)) (hN : N.IsQuasicoherentOnSite) :
    (cechEnvelopeDerivedIso hp hU L N hN).hom =
      (cechEnvelopeToDerived hp hU L).app ((bigModuleULift S).obj N) :=
  rfl

/-- **The cohomology of the Čech complex of the smooth-lift objects is crystalline cohomology**:
`H^j(Č(D, N)) ≅ H^j(CRIS(X/S), N)` as `A`-modules, for `N` quasi-coherent and every `j : ℤ`. -/
def cechEnvelopeHomologyIso
    (N : SheafOfModules.{u} (crystallineStructureSheaf S)) (hN : N.IsQuasicoherentOnSite)
    (j : ℤ) :
    (DerivedCategory.Plus.homologyFunctor _ j).obj
        ((Stacks.CechSite.FinalCover.cechDerivedFunctor (crystallineStructureSheaf S)
          (bigBaseRingHom S) (cechObjects hp L)).obj ((bigModuleULift S).obj N)) ≅
      (DerivedCategory.Plus.homologyFunctor _ j).obj
        ((derivedBigModuleGlobalSections S).obj ((bigModuleULift S).obj N)) :=
  (DerivedCategory.Plus.homologyFunctor _ j).mapIso (cechEnvelopeDerivedIso hp hU L N hN)

/-- **Čech cohomology of the smooth-lift objects is crystalline cohomology**: for `N`
quasi-coherent and `j : ℕ`, the `j`-th cohomology `A`-module of the Čech complex
`Č(D, N)`, `Č^n(D, N) = ∏_{x : Fin (n + 1) → ι} N(D_{x 0} × ⋯ × D_{x n})`, is
`H^j(CRIS(X/S), N)`. The Čech complex is read in `D⁺(A)` through its extension by zero to
integer degrees, which does not change its cohomology. -/
def cechEnvelopeComplexHomologyIso
    (N : SheafOfModules.{u} (crystallineStructureSheaf S)) (hN : N.IsQuasicoherentOnSite)
    (j : ℕ) :
    ((Stacks.CechSite.FinalCover.cechFunctor (crystallineStructureSheaf S) (bigBaseRingHom S)
        (cechObjects hp L)).obj ((bigModuleULift S).obj N)).homology j ≅
      (DerivedCategory.Plus.homologyFunctor _ (j : ℤ)).obj
        ((derivedBigModuleGlobalSections S).obj ((bigModuleULift S).obj N)) :=
  (HomologicalComplex.extendHomologyIso _ ComplexShape.embeddingUpNat
      (ComplexShape.embeddingUpNat_f j)).symm ≪≫
    ((DerivedCategory.homologyFunctorFactors _ (j : ℤ)).app _).symm ≪≫
      cechEnvelopeHomologyIso hp hU L N hN j

end Comparison

end Crystalline.GlobalCrystallineSituation.CechEnvelope

end
