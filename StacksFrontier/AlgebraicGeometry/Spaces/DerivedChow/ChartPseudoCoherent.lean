module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedChow.PushforwardPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePseudoCoherentSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactAffineMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiPushforwardSections

/-!
# The derived sections of `K` over an affine chart of a datum of the derived Chow lemma

Let `(n, Z, V, E)` be a datum of Stacks 0CTR for `X` over `A` with `V` affine, and let
`W = c⁻¹(V)` be identified with an affine scheme `U` over `X`, so that `W ⟶ V` is a morphism
`g : U ⟶ V` of affine schemes. Under the hypotheses of Stacks 0CTT, `RΓ(U, K|_U)` restricted to
`Γ(V, 𝒪_V)` along `g` is pseudo-coherent: by Stacks 0CTS
`Rq_*(Lp^*K ⊗^𝐋 E)|_V = Rg_*(K|_U)`, which is pseudo-coherent on `V`, and its derived sections
over `V` are those of `K|_U` over `U`. This is the step of the proof of Stacks 0CTT that the
source reads as "`K|_W` is pseudo-coherent relative to `A`".

## Main results

* `DerivedChowDatum.isPseudoCoherent_restrictScalars_representedAffineDerivedSections`
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

variable (B : BigFppfSite.{u}) {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))

/-- Pseudo-coherence of an object of `D(𝒪_X)` is invariant under isomorphism. -/
private theorem isPseudoCoherent_of_iso_smallEtale {S : Type u} [CommRing S]
    {hS : B.Contains (Spec (CommRingCat.of S))} {X : AlgebraicSpaces B _ hS}
    {E E' : DerivedCategory (Modules.{u, u} B _ hS X.1 X.2)}
    (h : (smallEtaleRingedSite B _ hS X.1 X.2).IsPseudoCoherent E) (e : E' ≅ E) :
    (smallEtaleRingedSite B _ hS X.1 X.2).IsPseudoCoherent E' :=
  (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).2 fun m =>
    RingedSite.isPseudoCoherentFrom_of_iso _ m
      ((RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).1 h m) e

/-- **The derived sections of `K` over an affine chart of a derived Chow datum.** Let `D` be a
datum of Stacks 0CTR whose open `V` is the affine scheme `V₀` and whose `W = c⁻¹(V)` is the
affine scheme `U₀`, with `g : U₀ ⟶ V₀` the morphism `W ⟶ V`. Under the hypotheses of
`AlgebraicGeometry.Space.DerivedChowDatum.isPseudoCoherent_derivedPushforward_productSnd`,
`RΓ(U₀, K|_{U₀})`, with scalars restricted along `Γ(V₀) ⟶ Γ(U₀)`, is pseudo-coherent. -/
theorem DerivedChowDatum.isPseudoCoherent_restrictScalars_representedAffineDerivedSections
    {X : AlgebraicSpaces B (Spec (CommRingCat.of A)) hA}
    (hfp : IsFinitePresentation B _ hA (toBase B _ hA X).hom)
    (K : DerivedCategory (Modules.{u, u} B _ hA X.1 X.2)) (hK : QcohDerived B _ hA X K)
    (h : ∀ E : DerivedCategory (Modules.{u, u} B _ hA X.1 X.2),
      (smallEtaleRingedSite B _ hA X.1 X.2).IsPseudoCoherent E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((representedAffineDerivedSections B _ hA (baseSiteObj B _ hA)).obj
            ((derivedModulePushforward B _ hA (toBase B _ hA X)).obj
              (((smallEtaleDerivedTensor B _ hA X).obj E).obj K))))
    {x : points B _ hA X.1} (D : DerivedChowDatum X x)
    {U₀ V₀ : BigFppfOver B (Spec (CommRingCat.of A)) hA}
    [IsAffine ((BigFppfOver.toScheme B _ hA).obj U₀)]
    [IsAffine ((BigFppfOver.toScheme B _ hA).obj V₀)]
    (eV : D.V ≅ schemeSpace V₀) (eW : schemeSpace U₀ ≅ overOpen D.i D.v)
    (g : U₀ ⟶ V₀)
    (hg : representedSpaceMap B _ hA g = eW.hom ≫ overOpenToOpen D.i D.v ≫ eV.hom) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((ModuleCat.restrictScalars.{u} ((B.inclusion.map g.left).app ⊤).hom).mapDerivedCategory.obj
        ((representedAffineDerivedSections B _ hA U₀).obj
          ((smallEtaleDerivedModulePullback B _ hA
            (eW.hom ≫ overOpenι D.i D.v ≫ D.i ≫ productFst X D.n D.contains)).obj K))) := by
  have hM := D.isPseudoCoherent_derivedPushforward_productSnd B hA hfp K hK h
  have hvM := isPseudoCoherent_smallEtaleDerivedModulePullback D.v _ hM
  obtain ⟨e₀⟩ := D.nonempty_restrict_derivedPushforward_tensor_iso K hK
  let w := overOpenι D.i D.v ≫ D.i ≫ productFst X D.n D.contains
  let c := overOpenToOpen D.i D.v
  let N := (smallEtaleDerivedModulePullback B _ hA w).obj K
  have hN : QcohDerived B _ hA _ N :=
    derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ w K hK
  -- `Rc_* N` is pseudo-coherent on `V`, hence `L(eV⁻¹)^* Rc_* N` on `V₀`.
  have hcN : (smallEtaleRingedSite B _ hA D.V.1 D.V.2).IsPseudoCoherent
      ((derivedModulePushforward B _ hA c).obj N) :=
    isPseudoCoherent_of_iso_smallEtale B hvM e₀.symm
  have h₁ := isPseudoCoherent_smallEtaleDerivedModulePullback eV.inv _ hcN
  -- `L(eV⁻¹)^* Rc_* N ≅ Rg_*(L eW^* N)`.
  let e₁ : (smallEtaleDerivedModulePullback B _ hA eV.inv).obj
        ((derivedModulePushforward B _ hA c).obj N) ≅
      (derivedModulePushforward B _ hA (representedSpaceMap B _ hA g)).obj
        ((smallEtaleDerivedModulePullback B _ hA eW.hom).obj N) :=
    ((Adjunction.rightAdjointUniq (smallEtaleDerivedModuleAdjunction B _ hA eV.hom)
        (smallEtaleDerivedModulePullbackModulesEquivalence eV).toAdjunction).app _).symm ≪≫
      (smallEtaleDerivedPushforwardCompIsoToposHom B _ hA c eV.hom).app N ≪≫
      (derivedModulePushforwardCompPullbackIso eW (c ≫ eV.hom) N).symm ≪≫
      eqToIso (congrArg (fun f => (derivedModulePushforward B _ hA f).obj
        ((smallEtaleDerivedModulePullback B _ hA eW.hom).obj N)) hg.symm)
  have hg' : (representedSpaceMap B _ hA g).hom = yoneda.map g := rfl
  have hqc : IsQuasiCompact B _ hA (representedSpaceMap B _ hA g).hom :=
    hg' ▸ isQuasiCompact_yoneda_map_of_isAffineHom B _ hA g inferInstance
  have hqs : IsQuasiSeparated B _ hA (representedSpaceMap B _ hA g).hom :=
    hg' ▸ (isQuasiSeparated_yoneda_map_iff B _ hA g).2 inferInstance
  have hN' : QcohDerived B _ hA _ ((smallEtaleDerivedModulePullback B _ hA eW.hom).obj N) :=
    derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ eW.hom N hN
  have hgN := qcohDerived_derivedModulePushforward_obj B _ hA (representedSpaceMap B _ hA g)
    hqc hqs _ hN'
  have h₂ : (smallEtaleRingedSite B _ hA (yoneda.obj V₀)
      (isAlgebraicSpace_yoneda B _ hA V₀)).IsPseudoCoherent
      ((derivedModulePushforward B _ hA (representedSpaceMap B _ hA g)).obj
        ((smallEtaleDerivedModulePullback B _ hA eW.hom).obj N)) :=
    isPseudoCoherent_of_iso_smallEtale B h₁ e₁.symm
  have h₃ : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((representedAffineDerivedSections B _ hA V₀).obj
        ((derivedModulePushforward B _ hA (representedSpaceMap B _ hA g)).obj
          ((smallEtaleDerivedModulePullback B _ hA eW.hom).obj N))) :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).2 fun m =>
      (isPseudoCoherentFrom_iff_representedAffineDerivedSections B _ hA V₀ _ hgN m).1
        ((RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).1 h₂ m)
  obtain ⟨e₂⟩ := nonempty_representedAffineDerivedSections_representedSpaceMap_iso g hqc hqs _ hN'
  exact (h₃.ofIso e₂).ofIso
    ((ModuleCat.restrictScalars.{u} ((B.inclusion.map g.left).app ⊤).hom).mapDerivedCategory.mapIso
      ((representedAffineDerivedSections B _ hA U₀).mapIso
        ((smallEtaleDerivedModulePullbackCompIso B _ hA eW.hom w).app K)))

end AlgebraicGeometry.Space

end
