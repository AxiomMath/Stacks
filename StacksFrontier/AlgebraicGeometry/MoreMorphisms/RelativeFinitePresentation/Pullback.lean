module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.FinitePresentationRel.BaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeFinitePresentation.AffinePullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeFinitePresentation.Affine

/-!
# Pullback of relatively finitely presented modules

Pulling a quasi-coherent module back along a morphism that is locally of finite presentation
preserves finite presentation relative to a base: if `G` on `Y` is finitely presented relative
to `g : Y ⟶ S` and `f : X ⟶ Y` is locally of finite presentation, then `f^* G` is finitely
presented relative to `f ≫ g`.

On affine charts `V` of `S`, `W` of `Y` and `U` of `X` with `W ≤ g⁻¹ V` and `U ≤ f⁻¹ W`, the
algebra `Γ(X, U)` is of finite presentation over `Γ(Y, W)`, so the base-change theorem for
relatively finitely presented modules applies; the resulting module is the sections of `f^* G`
over `U` because pullback along `Spec` of a ring map agrees with extension of scalars.

## Main results

* `AlgebraicGeometry.isFinitelyPresentedRelative_pullback`: relative finite presentation is
  preserved by pullback along a morphism locally of finite presentation.

## Implementation notes

The charts of `X` are indexed by triples consisting of an affine open `W` of `Y` inside the
inverse image of the chosen affine open of `S` and an affine open `U` of `X` inside the inverse
image of `W`; that these cover `(f ≫ g)⁻¹ V` is the existence of such refinements through
`Scheme.isBasis_affineOpens`.

Comparing the sections of a module over an affine open with the global sections of its
restriction along `IsAffineOpen.fromSpec` is `AlgebraicGeometry.affineSectionsLinearEquiv`, and
the identification of the restriction of a pullback with the pullback of a restriction uses
`Scheme.Modules.restrictFunctorIsoPullback` together with
`Scheme.Modules.pullbackComp` and `Scheme.Modules.pullbackCongr`.

## References

* [Stacks Project, Tag 09TB](https://stacks.math.columbia.edu/tag/09TB)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Affine form of Stacks 09TB: for a finitely presented ring map `B → A`, relative finite
presentation over `B` of a module presenting a quasi-coherent module `G` on `Spec B` gives
relative finite presentation over `A` of the global sections of the pullback of `G`. -/
private theorem finitePresentationRel_pullback_spec_of_iso
    {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A]
    (G : (Spec (.of B)).Modules) [G.IsQuasicoherent]
    (M : ModuleCat B) (eG : (tilde.functor (R := .of B)).obj M ≅ G)
    (hM : Module.FinitePresentationRel R B M)
    [Algebra.FinitePresentation B A] :
    Module.FinitePresentationRel R A
      ((moduleSpecΓFunctor (R := .of A)).obj
        ((Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap B A)))).obj G)) :=
  finitePresentationRel_pullback_specMap_of_baseChange G M eG
    (finitelyPresentedRelative_baseChange R B A M hM)

/-- If `W ≤ g⁻¹ V` and `U ≤ f⁻¹ W` then `U ≤ (f ≫ g)⁻¹ V`. -/
private theorem le_comp_preimage {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    {V : S.Opens} {W : Y.Opens} {U : X.Opens} (hWV : W ≤ g ⁻¹ᵁ V) (hUW : U ≤ f ⁻¹ᵁ W) :
    U ≤ (f ≫ g) ⁻¹ᵁ V := by
  rw [Scheme.Hom.comp_preimage]
  exact hUW.trans (f.preimage_mono hWV)

/-- Stacks 09TB on one chart: over compatible affine opens `V` of `S`, `W` of `Y` and `U` of
`X`, relative finite presentation of the sections of `G` over `W` gives relative finite
presentation of the sections of `f^* G` over `U`. -/
private theorem finitePresentationRel_pullback_chart
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [LocallyOfFinitePresentation f]
    (G : Y.Modules) [G.IsQuasicoherent]
    (V : S.Opens) (_hV : IsAffineOpen V)
    (W : Y.Opens) (hW : IsAffineOpen W) (hWV : W ≤ g ⁻¹ᵁ V)
    (U : X.Opens) (hU : IsAffineOpen U) (hUW : U ≤ f ⁻¹ᵁ W)
    (hG : letI : Algebra Γ(S, V) Γ(Y, W) :=
        (g.appLE V W hWV).hom.toAlgebra
      Module.FinitePresentationRel Γ(S, V) Γ(Y, W) Γ(G, W)) :
    letI : Algebra Γ(S, V) Γ(X, U) :=
      ((f ≫ g).appLE V U (le_comp_preimage hWV hUW)).hom.toAlgebra
    Module.FinitePresentationRel Γ(S, V) Γ(X, U)
      Γ(((Scheme.Modules.pullback f).obj G), U) := by
  classical
  have : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  let : Algebra Γ(S, V) Γ(Y, W) := (g.appLE V W hWV).hom.toAlgebra
  let : Algebra Γ(Y, W) Γ(X, U) := (f.appLE W U hUW).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(X, U) :=
    ((f ≫ g).appLE V U (le_comp_preimage hWV hUW)).hom.toAlgebra
  have : IsScalarTower Γ(S, V) Γ(Y, W) Γ(X, U) :=
    .of_algebraMap_eq' (by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
        Scheme.Hom.appLE_comp_appLE])
  have : Algebra.FinitePresentation Γ(Y, W) Γ(X, U) :=
    RingHom.finitePresentation_algebraMap.mp
      (by simpa only [RingHom.algebraMap_toAlgebra] using f.finitePresentation_appLE hW hU hUW)
  let k : Spec (.of Γ(X, U)) ⟶ Spec (.of Γ(Y, W)) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, W) Γ(X, U)))
  let GS : (Spec (.of Γ(Y, W))).Modules := (Scheme.Modules.restrictFunctor hW.fromSpec).obj G
  let N : ModuleCat Γ(Y, W) := ModuleCat.of Γ(Y, W) Γ(G, W)
  let eGS : (moduleSpecΓFunctor (R := .of Γ(Y, W))).obj GS ≃ₗ[Γ(Y, W)] N := by
    change Γ(G.restrict hW.fromSpec, ⊤) ≃ₗ[Γ(Y, W)] Γ(G, W)
    exact affineSectionsLinearEquiv G hW
  let eSheaf : (tilde.functor (R := .of Γ(Y, W))).obj N ≅ GS :=
    (tilde.functor (R := .of Γ(Y, W))).mapIso eGS.symm.toModuleIso ≪≫
      @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ (R := .of Γ(Y, W)) GS)
        (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent GS)
  have hbase : Module.FinitePresentationRel Γ(S, V) Γ(X, U)
      ((moduleSpecΓFunctor (R := .of Γ(X, U))).obj
        ((Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, W) Γ(X, U))))).obj GS)) :=
    finitePresentationRel_pullback_spec_of_iso
      (R := Γ(S, V)) (B := Γ(Y, W)) (A := Γ(X, U)) GS N eSheaf hG
  let H := (Scheme.Modules.pullback f).obj G
  have : H.IsQuasicoherent := Stacks.Modules.isQuasicoherent_pullback f G ‹G.IsQuasicoherent›
  let HS := (Scheme.Modules.restrictFunctor hU.fromSpec).obj H
  let eSource : (Scheme.Modules.pullback k).obj GS ≅
      (Scheme.Modules.pullback (k ≫ hW.fromSpec)).obj G :=
    ((Scheme.Modules.pullback k).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback hW.fromSpec).app G)) ≪≫
      (Scheme.Modules.pullbackComp k hW.fromSpec).app G
  let eTarget : HS ≅ (Scheme.Modules.pullback (hU.fromSpec ≫ f)).obj G :=
    ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app H) ≪≫
      (Scheme.Modules.pullbackComp hU.fromSpec f).app G
  let ePullback : (Scheme.Modules.pullback k).obj GS ≅ HS := eSource ≪≫
    (Scheme.Modules.pullbackCongr (IsAffineOpen.SpecMap_appLE_fromSpec f hW hU hUW)).app G ≪≫
    eTarget.symm
  simpa [H] using Module.FinitePresentationRel.of_linearEquiv
    (((moduleSpecΓFunctor (R := .of Γ(X, U))).mapIso ePullback).toLinearEquiv.trans
      (affineSectionsLinearEquiv H hU)) hbase

/-- **Stacks Project, Tag 09TB.** Relative finite presentation of a quasi-coherent module is
preserved by pullback along a morphism locally of finite presentation. -/
@[stacks 09TB]
theorem isFinitelyPresentedRelative_pullback
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [LocallyOfFiniteType g]
    [LocallyOfFinitePresentation f]
    (G : Y.Modules) [G.IsQuasicoherent]
    (hG : IsFinitelyPresentedRelative g G) :
    IsFinitelyPresentedRelative (f ≫ g) ((Scheme.Modules.pullback f).obj G) := by
  classical
  refine ⟨S.affineOpens, (·.1), iSup_affineOpens_eq_top S, (·.2), fun V => ?_⟩
  let I := {p : Y.affineOpens × X.affineOpens //
    p.1.1 ≤ g ⁻¹ᵁ V.1 ∧ p.2.1 ≤ f ⁻¹ᵁ p.1.1}
  let U : I → X.Opens := fun i => i.1.2.1
  have hcover : (⨆ i, U i) = (f ≫ g) ⁻¹ᵁ V.1 := by
    refine le_antisymm (iSup_le fun i => le_comp_preimage i.2.1 i.2.2) fun x hx => ?_
    obtain ⟨_, ⟨W, hW, rfl⟩, hfxW, hWV⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hx (g ⁻¹ᵁ V.1).2
    obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hxU, hUW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hfxW (f ⁻¹ᵁ W).2
    exact le_iSup U ⟨(⟨W, hW⟩, ⟨U₀, hU₀⟩), hWV, hUW⟩ hxU
  exact ⟨I, U, hcover, fun i => i.1.2.2, fun ⟨⟨⟨W, hW⟩, ⟨U₀, hU₀⟩⟩, hWV, hUW⟩ =>
    finitePresentationRel_pullback_chart f g G V.1 V.2 W hW hWV U₀ hU₀ hUW
      ((isFinitelyPresentedRelative_iff_affine g G).mp hG W hW V.1 V.2 hWV)⟩

end AlgebraicGeometry
