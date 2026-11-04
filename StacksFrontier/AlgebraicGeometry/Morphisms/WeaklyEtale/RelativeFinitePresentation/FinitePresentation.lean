module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.FinitePresentationRel.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FpqcFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeFinitePresentation.Affine
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.RingTheory.FinitePresentation.Relative

/-!
# Relative finite presentation for a locally finitely presented morphism

For a locally finitely presented morphism of schemes, a quasi-coherent sheaf of modules is
finitely presented relative to the base exactly when it is finitely presented as a sheaf of
modules.

## Main results

* `AlgebraicGeometry.isFinitelyPresentedRelative_iff_isFinitePresentation`: relative finite
  presentation agrees with finite presentation for quasi-coherent modules over a locally
  finitely presented morphism.

## Implementation notes

Relative finite presentation is expressed by `AlgebraicGeometry.IsFinitelyPresentedRelative`,
while finite presentation of a sheaf is Mathlib's `SheafOfModules.IsFinitePresentation`.

One direction turns a finite presentation of the module of sections over an affine open into a
finite presentation of the restricted sheaf, transports it across the slice-category
equivalence, and glues over an affine open cover. The other reads off a finite presentation of
the sections from one of the sheaf.

## References

* [Stacks Project, Tag 09T8](https://stacks.math.columbia.edu/tag/09T8)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry



private theorem finitePresentation_sections_of_openImmersion
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    {R : CommRingCat.{u}} (j : Spec R ⟶ X) [IsOpenImmersion j] :
    Module.FinitePresentation R
      ((modulesSpecToSheaf.obj (F.restrict j)).presheaf.obj (.op ⊤)) := by
  let G := F.restrict j
  have : G.IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback j).app F).symm
      (@Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _
        j.toLRSHom.toShHom F ‹_›)
  have : G.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor j F
  exact finitePresentation_sections_of_affine G

private noncomputable def affineSectionEquiv
    {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U) :
    Γ(M.restrict hU.fromSpec, ⊤) ≃ₗ[Γ(X, U)] Γ(M, U) := by
  let j := hU.fromSpec
  letI : IsOpenImmersion j := hU.isOpenImmersion_fromSpec
  let N := M.restrict j
  have hImage : U = j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  let eTopAb : Γ(N, ⊤) ≅ Γ(M, U) :=
    M.restrictAppIso j ⊤ ≪≫ M.presheaf.mapIso (eqToIso hImage).op
  let eRing : Γ(X, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) ≅ Γ(X, U) :=
    X.presheaf.mapIso (eqToIso hImage).op
  have hR (a : Γ(X, U)) :
      eRing.hom ((j.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U)).inv a)) = a := by
    have hAEq : eRing.hom ≫ (Scheme.ΓSpecIso Γ(X, U)).inv = (j.appIso ⊤).hom := by
      simp only [eRing, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appIso_hom']
      have hAppLE : hU.fromSpec.appLE U ⊤ (by simp [hU.fromSpec_preimage_self]) =
          (Scheme.ΓSpecIso Γ(X, U)).inv := by
        simp only [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc,
          ← Functor.map_comp]
        simp
      rw [← hAppLE]
      simpa only [eqToIso.hom] using
        (hU.fromSpec.map_appLE' (V := ⊤) (by
          rw [← hImage]
          exact hU.fromSpec_preimage_self.ge) hImage)
    have hAEq' : eRing.hom =
        (j.appIso ⊤).hom ≫ (Scheme.ΓSpecIso Γ(X, U)).hom := by
      rw [← hAEq, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simp only [hAEq', ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  let eTop0 : Γ(N, ⊤) ≃+ Γ(M, U) := eTopAb.addCommGroupIsoToAddEquiv
  have htop (a : Γ(X, U)) (m : Γ(N, ⊤)) : eTop0 (a • m) = a • eTop0 m := by
    change eTopAb.hom (a • m) = a • eTopAb.hom m
    rw [Scheme.Modules.smul_Spec_def]
    simp only [eTopAb, Iso.trans_hom, ConcreteCategory.comp_apply]
    rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
    simp only [Functor.mapIso_hom, Iso.op_hom]
    rw [M.map_smul]
    congr 1
    exact hR a
  exact { eTop0 with map_smul' := htop }

private theorem affineSections_of_isFinitePresentation
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] [M.IsFinitePresentation]
    {U : X.Opens} (hU : IsAffineOpen U) :
    Module.FinitePresentation Γ(X, U) Γ(M, U) :=
  (affineSectionEquiv M hU).finitePresentation_iff.mp
    (finitePresentation_sections_of_openImmersion M hU.fromSpec)

private noncomputable def affineOpenRange {X : Scheme.{u}} (U : X.affineOpens) : X.Opens := by
  let hU := U.property
  letI : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  exact hU.fromSpec.opensRange

private theorem finitePresentation_of_affineSections
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U)
    (hM : Module.FinitePresentation Γ(X, U) Γ(M, U)) :
    (M.over (hU.fromSpec).opensRange).IsFinitePresentation := by
  classical
  let j := hU.fromSpec
  let : IsOpenImmersion j := hU.isOpenImmersion_fromSpec
  let N := M.restrict j
  let A : ModuleCat Γ(X, U) := (modulesSpecToSheaf.obj N).presheaf.obj (.op ⊤)
  have : Module.FinitePresentation Γ(X, U) A :=
    (affineSectionEquiv M hU).finitePresentation_iff.mpr hM
  have : N.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor j M
  let eN : tilde A ≅ N := asIso N.fromTildeΓ
  obtain ⟨P₀, hP₀⟩ := tilde_has_finite_presentation A
  let P := @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ eN.hom eN.isIso_hom P₀
  have hP : P.IsFinite :=
    ⟨⟨hP₀.isFiniteType_generators.finite⟩, ⟨hP₀.isFiniteType_relations.finite⟩⟩
  let fU := j.isoOpensRange
  have hfU : fU.inv ≫ j = (j.opensRange).ι := Scheme.Hom.isoOpensRange_inv_comp j
  let eF : N.restrict fU.inv ≅ M.restrict (j.opensRange).ι :=
    ((Scheme.Modules.restrictFunctorIsoPullback fU.inv).app N) ≪≫
      ((Scheme.Modules.pullback fU.inv).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback j).app M)) ≪≫
      ((Scheme.Modules.pullbackComp fU.inv j).app M) ≪≫
      ((Scheme.Modules.pullbackCongr hfU).app M) ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback (j.opensRange).ι).app M).symm
  let P' := Scheme.Modules.presentationRestrict fU.inv P
  have hP' : P'.IsFinite :=
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩
  let P'' := @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _
    eF.hom eF.isIso_hom P'
  have : P''.IsFinite :=
    ⟨⟨hP'.isFiniteType_generators.finite⟩, ⟨hP'.isFiniteType_relations.finite⟩⟩
  exact over_isFinitePresentation_of_finite_global (j.opensRange) M P''

/-- **Stacks Project, Tag 09T8.** For a locally finitely presented morphism of schemes, a
quasi-coherent sheaf of modules is finitely presented relative to the base if and only if it is
finitely presented. -/
@[stacks 09T8 "relative_iff_finite_presentation"]
theorem isFinitelyPresentedRelative_iff_isFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (M : X.Modules) [M.IsQuasicoherent] :
    IsFinitelyPresentedRelative f M ↔ M.IsFinitePresentation := by
  have key (U : X.Opens) (V : S.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
      (hUV : U ≤ f ⁻¹ᵁ V) :
      let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
      Module.FinitePresentationRel Γ(S, V) Γ(X, U) Γ(M, U) ↔
        Module.FinitePresentation Γ(X, U) Γ(M, U) := by
    let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    have : Algebra.FinitePresentation Γ(S, V) Γ(X, U) :=
      RingHom.finitePresentation_algebraMap.mp (f.finitePresentation_appLE hV hU hUV)
    exact Module.finitePresentationRel_iff (R := Γ(S, V)) (A := Γ(X, U)) (M := Γ(M, U))
  refine ⟨fun hrel => ?_, fun hM => (isFinitelyPresentedRelative_iff_affine f M).mpr
    fun U hU V hV hUV => (key U V hU hV hUV).mpr (affineSections_of_isFinitePresentation M hU)⟩
  have hAff := (isFinitelyPresentedRelative_iff_affine f M).mp hrel
  let I : Type u :=
    { p : X.affineOpens × S.affineOpens // (p.1 : X.Opens) ≤ f ⁻¹ᵁ (p.2 : S.Opens) }
  let W : I → X.Opens := fun i => affineOpenRange i.1.1
  have hWopen : IsOpenCover W := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨V, hV, hfxV, _⟩ :=
      exists_isAffineOpen_mem_and_subset (U := ⊤) (x := f x) (by simp)
    obtain ⟨U, hU, hxU, hUV⟩ :=
      exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ V) (x := x) hfxV
    refine Opens.mem_iSup.mpr ⟨⟨⟨⟨U, hU⟩, ⟨V, hV⟩⟩, hUV⟩, ?_⟩
    change x ∈ affineOpenRange ⟨U, hU⟩
    simp [affineOpenRange, hU.opensRange_fromSpec, hxU]
  have hlocal (i : I) : (M.over (W i)).IsFinitePresentation :=
    finitePresentation_of_affineSections M i.1.1.property
      ((key _ _ i.1.1.property i.1.2.property i.2).mp
        (hAff _ i.1.1.property _ i.1.2.property i.2))
  exact isFinitePresentation_of_coversTop M W ((Opens.coversTop_iff X W).2 hWopen)

end AlgebraicGeometry
