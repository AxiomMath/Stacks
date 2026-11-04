module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiOver

/-!
# Coherent subsheaves and quotients on a locally Noetherian scheme

On a locally Noetherian scheme a quasi-coherent sheaf of modules sitting inside, or
received as a quotient of, a coherent sheaf of modules is itself coherent. Neither
direction is formal: coherence asks for a finite-type condition on the kernels of maps out
of finite free modules, and on a general ringed space a quasi-coherent subsheaf of a
coherent sheaf need not be of finite type. The Noetherian hypothesis enters through the
five equivalent conditions of [Stacks, Tag 01XZ], which are available as
`Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae`.

## Main results

* `Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_epi`: the target of an
  epimorphism out of a coherent sheaf of modules is coherent as soon as it is
  quasi-coherent.
* `Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono`: the source of a
  monomorphism into a coherent sheaf of modules is coherent as soon as it is
  quasi-coherent.

## Implementation notes

A submodule is represented by a monomorphism and a quotient module by an epimorphism in the
category of sheaves of modules, so the statements do not depend on a choice of
representative for the subobject or the quotient.

For the quotient the local generators of the ambient sheaf push forward along the
epimorphism, which gives finite type directly, and condition (2) of [Stacks, Tag 01XZ] then
gives coherence. For the submodule there is no such push-forward, so the proof goes through
condition (4) instead: over an affine open `U = Spec A` with `A` Noetherian the ambient
sheaf is `M ~` for a finite `A`-module `M`, the subsheaf is `N ~` for `N` its module of
sections, and `N` embeds in `M` because `Γ` preserves monomorphisms. A submodule of a
finite module over a Noetherian ring is finite, so the subsheaf satisfies condition (4) at
every affine open.

## References

* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherenceCriteria
open Stacks.AlgebraicGeometry.CoherentTFAE

universe u

namespace Stacks.AlgebraicGeometry.CoherentSubquotients

/-! ### Quotients -/

/-- **[Stacks, Tag 01Y1].** A quasi-coherent quotient of a coherent sheaf of modules on a
locally Noetherian scheme is coherent. -/
@[stacks 01Y1 "quasi_coherent_quotient", ega "I 9.6.4" "quotient, B = O_X"]
theorem isCoherent_of_epi {X : Scheme.{u}} [IsLocallyNoetherian X]
    {F G : X.Modules} [hF : F.IsCoherent] [G.IsQuasicoherent]
    (f : F ⟶ G) [Epi f] : G.IsCoherent := by
  obtain ⟨σ, hσ⟩ := hF.isFiniteType.exists_localGeneratorsData
  have hepi (i : σ.I) : Epi (f.over (σ.X i)) :=
    Stacks.SheafOfModules.EpiMono.epi_over (hp := ‹Epi f›) f (σ.X i)
  let τ : G.LocalGeneratorsData.{u, u, u, u} := {
    I := σ.I, X := σ.X, coversTop := σ.coversTop
    generators := fun i => have := hepi i; (σ.generators i).ofEpi (f.over (σ.X i))
  }
  have hτ : τ.IsFiniteType := by
    constructor; intro i; dsimp [τ]
    have := hepi i
    have : (σ.generators i).IsFiniteType := hσ.isFiniteType i; infer_instance
  have : G.IsFiniteType := by constructor; exact ⟨τ, hτ⟩
  apply ((coherent_tfae X G).out 2 1).mp; exact ⟨inferInstance, inferInstance⟩

/-! ### Submodules -/

/-- A monomorphism of modules on a scheme is a monomorphism in the category of sheaves of
modules over the structure sheaf. The two categories are definitionally equal but carry
different instance paths, so the transport is spelled out. -/
private theorem mono_as_sheaf {X : Scheme.{u}} {F G : X.Modules}
    (f : G ⟶ F) [Mono f] :
    @Mono (SheafOfModules X.ringCatSheaf) (inferInstance) G F f := by
  refine ⟨?_⟩
  intro Z g h hcomp
  exact (‹Mono f›).right_cancellation g h hcomp

/-- Restriction along an open immersion preserves monomorphisms: on sections over an open
`V` of the source it is the map on sections over the image of `V`, which is injective. -/
private theorem restrictMap_mono {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsOpenImmersion i] {F G : Y.Modules} (f : G ⟶ F) [Mono f] :
    Mono ((Scheme.Modules.restrictFunctor i).map f) := by
  apply Functor.mono_of_mono_map (Scheme.Modules.toPresheaf X)
  apply (NatTrans.mono_iff_mono_app _).2
  intro V
  let W := Opposite.op (i ''ᵁ V.unop)
  have hApp : Mono (((Scheme.Modules.toPresheaf Y).map f).app W) :=
    (NatTrans.mono_iff_mono_app _).mp (Functor.map_mono (Scheme.Modules.toPresheaf Y) f) W
  have heq :
      ((Scheme.Modules.toPresheaf X).map ((Scheme.Modules.restrictFunctor i).map f)).app V =
        ((Scheme.Modules.toPresheaf Y).map f).app W := by
    ext x; rfl
  rw [heq]
  exact (AddCommGrpCat.mono_iff_injective _).mpr
    ((AddCommGrpCat.mono_iff_injective _).mp hApp)

/-- **Condition (4) of [Stacks, Tag 01XZ] for a quasi-coherent subsheaf.** Over an affine
open `U = Spec A` of a locally Noetherian scheme, a quasi-coherent subsheaf `G` of a
coherent sheaf `F` is the sheaf associated with a finite `A`-module, namely its own module
of sections: `F` restricts to `M ~` for some finite `M`, and `Γ(U, G)` embeds in `M` because
`moduleSpecΓFunctor` preserves monomorphisms, so it is a submodule of a finite module over a
Noetherian ring. -/
private theorem mono_quasicoherent_isFiniteTildeOn {X : Scheme.{u}}
    [IsLocallyNoetherian X] {F G : X.Modules} [hF : F.IsCoherent]
    [G.IsQuasicoherent] (f : G ⟶ F) [Mono f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsFiniteTildeOn G U hU := by
  let A := Γ(X, U)
  let R := CommRingCat.of A
  let e := hU.isoSpec
  let G₀ := (Scheme.Modules.restrictFunctor U.ι).obj G
  let F₀ := (Scheme.Modules.restrictFunctor U.ι).obj F
  let G₁ := (Scheme.Modules.restrictFunctor e.inv).obj G₀
  let F₁ := (Scheme.Modules.restrictFunctor e.inv).obj F₀
  let g : G₁ ⟶ F₁ := (Scheme.Modules.restrictFunctor e.inv).map
    ((Scheme.Modules.restrictFunctor U.ι).map f)
  have hFtildeAll := ((coherent_tfae X F).out 1 4).mp hF
  obtain ⟨M, hM, ⟨eM⟩⟩ := hFtildeAll U hU
  have : Module.Finite A M := hM
  have eM' : F₀ ≅ (Scheme.Modules.restrictFunctor e.hom).obj (tilde M) :=
    eM ≪≫ ((Scheme.Modules.restrictFunctorIsoPullback e.hom).app (tilde M)).symm
  let eF : F₁ ≅ tilde M :=
    (Scheme.Modules.restrictFunctor e.inv).mapIso eM' ≪≫
      ((Scheme.Modules.restrictFunctorComp e.inv e.hom).app (tilde M)).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.inv_hom_id).app (tilde M) ≪≫
      (Scheme.Modules.restrictFunctorId (X := Spec R)).app (tilde M)
  have : G₁.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor e.inv G₀
  have hfrom : IsIso G₁.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent G₁
  let N := moduleSpecΓFunctor.obj G₁
  let eN : M ≅ moduleSpecΓFunctor.obj F₁ :=
    (AlgebraicGeometry.tilde.toTildeΓNatIso.app M) ≪≫
      (moduleSpecΓFunctor.mapIso eF).symm
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hFsec : Module.Finite A (moduleSpecΓFunctor.obj F₁) :=
    Module.Finite.of_surjective eN.hom.hom
      (ConcreteCategory.bijective_of_isIso eN.hom).2
  have : Mono g := by
    dsimp [g]
    have : Mono ((Scheme.Modules.restrictFunctor U.ι).map f) :=
      restrictMap_mono U.ι f
    exact restrictMap_mono e.inv ((Scheme.Modules.restrictFunctor U.ι).map f)
  let L : (↑N) →ₗ[A] ↑(moduleSpecΓFunctor.obj F₁) :=
    (moduleSpecΓFunctor.map g).hom
  have hLinj : Function.Injective L := by
    have : @Mono (SheafOfModules (Spec R).ringCatSheaf) (inferInstance) G₁ F₁ g :=
      mono_as_sheaf g
    have : (moduleSpecΓFunctor (R := R)).IsRightAdjoint :=
      (tilde.adjunction (R := R)).isRightAdjoint
    have : CategoryTheory.Limits.PreservesLimitsOfShape
        CategoryTheory.Limits.WalkingCospan (moduleSpecΓFunctor (R := R)) := inferInstance
    have hEm : (moduleSpecΓFunctor (R := R)).PreservesMonomorphisms :=
      CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
    have hNmap : Mono (moduleSpecΓFunctor.map g) := hEm.preserves g
    have hAppInj := (ModuleCat.mono_iff_injective (moduleSpecΓFunctor.map g)).mp hNmap
    intro x y hxy
    change (ConcreteCategory.hom (moduleSpecΓFunctor.map g)) x =
      (ConcreteCategory.hom (moduleSpecΓFunctor.map g)) y at hxy
    exact hAppInj hxy
  have hN : Module.Finite A (↑N) := Module.Finite.of_injective L hLinj
  let eG : tilde N ≅ G₁ := @CategoryTheory.asIso _ _ _ _ G₁.fromTildeΓ hfrom
  let eBack : (Scheme.Modules.restrictFunctor e.hom).obj G₁ ≅ G₀ :=
    ((Scheme.Modules.restrictFunctorComp e.hom e.inv).app G₀).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.hom_inv_id).app G₀ ≪≫
      (Scheme.Modules.restrictFunctorId (X := U.toScheme)).app G₀
  exact ⟨N, hN, ⟨eBack.symm ≪≫
    (Scheme.Modules.restrictFunctor e.hom).mapIso eG.symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback e.hom).app (tilde N)⟩⟩

/-- **[Stacks, Tag 01Y1].** A quasi-coherent submodule of a coherent sheaf of modules on a
locally Noetherian scheme is coherent. -/
@[stacks 01Y1 "quasi_coherent_submodule"]
theorem isCoherent_of_mono {X : Scheme.{u}} [IsLocallyNoetherian X]
    {F G : X.Modules} [F.IsCoherent] [G.IsQuasicoherent]
    (f : G ⟶ F) [Mono f] : G.IsCoherent :=
  ((coherent_tfae X G).out 1 4).mpr
    (mono_quasicoherent_isFiniteTildeOn f)

end Stacks.AlgebraicGeometry.CoherentSubquotients

end
