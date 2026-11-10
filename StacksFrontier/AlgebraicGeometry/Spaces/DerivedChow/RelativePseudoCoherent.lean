module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDerivedSectionsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedChow.ChartAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedChow.ChartPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
public import StacksFrontier.Homology.PseudoCoherent.Relative.Surjection
import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherence relative to the base from pseudo-coherent derived sections

Let `X` be an algebraic space separated and of finite presentation over a ring `A` and `K` an
object of `D_QCoh(𝒪_X)` such that `RΓ(X, E ⊗^𝐋 K)` is pseudo-coherent over `A` for every
pseudo-coherent `E`. This file proves that `K` is pseudo-coherent relative to `A`, following
the proof of Stacks 0CTT: for every affine étale chart `U` of `X`, a datum of the derived Chow
lemma whose `W` is `U` and whose `V` is affine, flat and of finite presentation over `A` shows
that `RΓ(U, K)` is pseudo-coherent over `Γ(V)`, which surjects onto `Γ(U)`; this is relative
pseudo-coherence over `A`, and then over every étale `A`-algebra by Stacks 067D.

The proof uses, through
`AlgebraicGeometry.Space.DerivedChowDatum.isPseudoCoherent_derivedPushforward_productSnd`,
pseudo-coherence of the derived pushforward along a flat proper morphism of finite presentation
(Stacks 0A1P for algebraic spaces) and (5) ⟹ (1) of Stacks 0CSG on `ℙⁿ_A`.

## Main results

* `AlgebraicGeometry.Space.isRelativelyPseudoCoherent_of_isPseudoCoherent_derivedSections_tensor`:
  **Stacks 0CTT**.
* `DerivedCategory.isZero_of_subsingleton`: a complex of modules over the zero ring is zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open AlgebraicGeometry.Space.DerivedChow

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  SmallEtale.instHasSheafifyOver SmallEtale.instWEqualsLocallyBijectiveOver

/-- A complex of modules over the zero ring is zero. -/
theorem _root_.DerivedCategory.isZero_of_subsingleton {R : Type u} [Ring R] [Subsingleton R]
    (K : DerivedCategory (ModuleCat.{u} R)) : IsZero K := by
  refine (DerivedCategory.Q.map_isZero ?_).of_iso (DerivedCategory.Q.objObjPreimageIso K).symm
  refine ⟨fun Y => ⟨⟨0⟩, fun f => ?_⟩, fun Y => ⟨⟨0⟩, fun f => ?_⟩⟩ <;>
  · ext i x
    exact @Subsingleton.elim _ (Module.subsingleton R _) _ _

/-- Global sections of a composite of schemes are computed by composing the maps. -/
private theorem appTop_comp_apply {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z}
    (hh : f ≫ g = h) (r : Γ(Z, ⊤)) : h.appTop r = f.appTop (g.appTop r) := by
  subst hh
  rw [Scheme.Hom.comp_appTop]
  rfl

variable (B : BigFppfSite.{u}) {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))

/-- **Stacks 0CTT.** Let `X` be an algebraic space separated and of finite presentation over `A`
and `K ∈ D_QCoh(𝒪_X)` with `RΓ(X, E ⊗^𝐋 K)` pseudo-coherent over `A` for every pseudo-coherent
`E`. Then `K` is pseudo-coherent relative to `A`. -/
@[stacks 0CTT]
theorem isRelativelyPseudoCoherent_of_isPseudoCoherent_derivedSections_tensor
    {X : AlgebraicSpaces B (Spec (CommRingCat.of A)) hA}
    (hsep : IsSeparated B _ hA (toBase B _ hA X).hom)
    (hfp : IsFinitePresentation B _ hA (toBase B _ hA X).hom)
    (K : DerivedCategory (Modules.{u, u} B _ hA X.1 X.2)) (hK : QcohDerived B _ hA X K)
    (h : ∀ E : DerivedCategory (Modules.{u, u} B _ hA X.1 X.2),
      (smallEtaleRingedSite B _ hA X.1 X.2).IsPseudoCoherent E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((representedAffineDerivedSections B _ hA (baseSiteObj B _ hA)).obj
            ((derivedModulePushforward B _ hA (toBase B _ hA X)).obj
              (((smallEtaleDerivedTensor B _ hA X).obj E).obj K)))) :
    IsRelativelyPseudoCoherent B _ hA X.1 X.2 (toBase B _ hA X).hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B _ hA hfp.1) ⟨K, hK⟩ := by
  intro m U V g hc hU hV
  let Q := BigFppfOver.toScheme B (Spec (CommRingCat.of A)) hA
  let U₀ := (SmallEtale.toOver B _ hA X.1).obj U
  let V₁ := (SmallEtale.toOver B _ hA _).obj V
  let RU := (structurePresheaf B _ hA X.1).obj (op U)
  let RV := (structurePresheaf B _ hA (yoneda.obj (Over.mk (𝟙 (B.obj hA))))).obj (op V)
  let RA := Γ(Q.obj (baseSiteObj B _ hA), ⊤)
  have : IsAffine (Q.obj U₀) := hU
  have : IsAffine (Q.obj V₁) := hV
  let : Algebra RV RU := ((Q.map g).appTop.hom).toAlgebra
  have : LocallyOfFiniteType (Q.map g) :=
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B _ hA hfp.1) _ _ U.obj.hom
      V.obj.hom g U.property V.property hc
  have : Algebra.FiniteType RV RU :=
    HasRingHomProperty.appTop (@LocallyOfFiniteType) (Q.map g) inferInstance
  let M := chartDerivedSections B _ hA X.1 X.2 U ⟨K, hK⟩
  change _root_.PseudoCoherence.IsRelativelyPseudoCoherentFrom (R := RV) M m
  by_cases hE : IsEmpty (Q.obj U₀)
  · have : Subsingleton RU := inferInstanceAs (Subsingleton Γ(Q.obj U₀, ⊤))
    intro n f _
    exact (StacksDraft.PseudoCoherence.pseudoCoherent_of_isZero _
      (Functor.map_isZero _ (DerivedCategory.isZero_of_subsingleton M))).2 m
  obtain ⟨y⟩ := not_isEmpty_iff.1 hE
  obtain ⟨u, -⟩ := surjective_pointsToScheme B _ hA U₀ y
  have hb := (isEtale_iff_presheaf_of_yoneda B _ hA U.obj.hom).1 (isEtale_chartToSpace B _ hA X U)
  obtain ⟨x, D, V₀, hV₀, eV, eW, gU, hg, hbW, hflat, hlfp, hcl⟩ :=
    exists_derivedChowDatum_of_affine_chart B hA X hsep hfp hU U.obj.hom hb u
  have hpc := D.isPseudoCoherent_restrictScalars_representedAffineDerivedSections B hA
    hfp K hK h eV eW gU hg
  -- `M ≅ RΓ(U₀, K|_{U₀})`.
  have hbW' : eW.hom ≫ overOpenι D.i D.v ≫ D.i ≫ productFst X D.n D.contains =
      chartToSpace B _ hA X U := ObjectProperty.hom_ext _ hbW
  obtain ⟨e₁⟩ := nonempty_derivedSections_iso_representedAffineDerivedSections X U K
  let e₂ := (representedAffineDerivedSections B _ hA U₀).mapIso
      ((smallEtaleDerivedModulePullbackCongr B _ hA hbW').app K ≪≫
        (smallEtaleDerivedModulePullbackIsoEtale B _ hA (chartToSpace B _ hA X U)
          (isEtale_chartToSpace B _ hA X U)).app K)
  let e : M ≅ _ := e₁ ≪≫ e₂.symm
  -- Relative pseudo-coherence over `A` through `Γ(V₀) ↠ Γ(U₀)`.
  let P := Γ(Q.obj V₀, ⊤)
  let base := baseSiteObj B (Spec (CommRingCat.of A)) hA
  let tV₀ : V₀ ⟶ base := Over.mkIdTerminal.from V₀
  let tV : V₁ ⟶ base := Over.mkIdTerminal.from V₁
  let : Algebra P RU := ((Q.map gU).appTop.hom).toAlgebra
  let : Algebra RA P := ((Q.map tV₀).appTop.hom).toAlgebra
  let : Algebra RA RV := ((Q.map tV).appTop.hom).toAlgebra
  let : Algebra RA RU := ((Q.map (gU ≫ tV₀)).appTop.hom).toAlgebra
  have htw : gU ≫ tV₀ = g ≫ tV := Over.mkIdTerminal.hom_ext _ _
  have : IsScalarTower RA P RU := .of_algebraMap_eq (appTop_comp_apply _ _ rfl)
  have : IsScalarTower RA RV RU :=
    .of_algebraMap_eq (appTop_comp_apply _ _ (by rw [← Functor.map_comp, ← htw]))
  have htV₀ : Q.map tV₀ = B.inclusion.map V₀.hom := by
    have h₁ : tV₀.left = V₀.hom := by simpa [base, baseSiteObj] using Over.w tV₀
    exact congrArg B.inclusion.map h₁
  have : Flat (Q.map tV₀) := htV₀ ▸ hflat
  have : LocallyOfFinitePresentation (Q.map tV₀) := htV₀ ▸ hlfp
  have : Module.Flat RA P := HasRingHomProperty.appTop @Flat (Q.map tV₀) inferInstance
  have : Algebra.FinitePresentation RA P :=
    HasRingHomProperty.appTop @LocallyOfFinitePresentation (Q.map tV₀) inferInstance
  have : _root_.AlgebraicGeometry.IsClosedImmersion (Q.map gU) := hcl
  have : IsAffine (Q.obj V₀) := hV₀
  have hs : Function.Surjective (algebraMap P RU) :=
    (_root_.AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine (Q.map gU)).2
  have hres : StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
      ((ModuleCat.restrictScalars.{u} (algebraMap P RU)).mapDerivedCategory.obj M) m :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).1
      (hpc.ofIso ((ModuleCat.restrictScalars.{u} (algebraMap P RU)).mapDerivedCategory.mapIso
        e.symm)) m
  have h₆ := _root_.PseudoCoherence.isRelativelyPseudoCoherentFrom_of_surjective
    (R := RA) (P := P) (B := RU) hs M m hres
  -- From `A` to `Γ(V)`, étale over `A` (Stacks 067D).
  have hVe : Etale (Q.map tV) := by
    have hV' : V.obj.hom = yoneda.map tV :=
      (isTerminal_yoneda_obj_base B _ hA).hom_ext _ _
    have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (CommRingCat.of A)) hA)).presheaf V.obj.hom := V.property
    rw [hV'] at this
    exact (presheaf_yoneda_map_etale_iff B _ hA tV).1 this
  have : Module.Flat RA RV := HasRingHomProperty.appTop @Flat (Q.map tV) inferInstance
  have : Algebra.FinitePresentation RA RV :=
    HasRingHomProperty.appTop @LocallyOfFinitePresentation (Q.map tV) inferInstance
  obtain ⟨hft, hAV⟩ :=
    Algebra.pseudoCoherent_iff_exists_isModuleRelativelyPseudoCoherent.mp
      (RingHom.isPerfectRingMap_of_flat_of_finitePresentation RA RV).1
  exact ((_root_.PseudoCoherence.relativelyPseudoCoherent_iff_of_comp (R := RA) (A := RV)
    (B := RU) hAV M m).1).2 h₆

end AlgebraicGeometry.Space

end
