module

public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FreeSections
public import StacksFrontier.AlgebraicGeometry.Modules.TildePullbackBaseChange

/-!
# Global sections of a quasi-coherent module on an affine scheme

Let `T` be an affine scheme with ring of functions `A = Γ(T, ⊤)`. The global-sections functor
identifies quasi-coherent `𝒪_T`-modules with `A`-modules, inversely to `M ↦ M^~` read through
`T ≅ Spec A`. This file makes that identification usable on *maps*: for a morphism `φ : M ⟶ N`
of quasi-coherent modules on `T`, properties of the induced map of global sections
`Γ(φ, ⊤)` are read off from properties of `φ`.

The route taken is the direct image along `T.isoSpec.hom`, not the pullback along
`T.isoSpec.inv`: the sections of a direct image over `⊤` are *literally* the sections of the
original module over `⊤`, and the induced map of sections is literally the original one, so no
comparison of modules of sections has to be constructed. The two functors are identified once
and for all by `AlgebraicGeometry.Scheme.Modules.pullbackIsoPushforward`, which is where the
geometric hypotheses — stated for pullbacks, as a residue field or a fibre is — are transferred.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pushforwardEquivOfIso` and
  `AlgebraicGeometry.Scheme.Modules.pullbackIsoPushforward`: the direct image along an
  isomorphism of schemes is an equivalence, and is the inverse image along the inverse
  isomorphism.
* `AlgebraicGeometry.specΓSectionsEquiv`: the `Γ(T, ⊤)`-module which the Spec–Γ dictionary
  attaches to the direct image of `M` along `T.isoSpec.hom` is the module of global sections of
  `M`. The underlying map is the identity.

## Main results

* `LinearMap.bijective_baseChange_comp`: bijectivity of a base change is invariant under
  composing with a linear equivalence on each side.
* `AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_pullback_map`: the inverse image along an
  isomorphism of schemes reflects isomorphisms.
* `AlgebraicGeometry.bijective_baseChange_sectionsLinearMap_of_isIso_pullback`: **if `φ` becomes
  an isomorphism after pullback to the residue field of a point `t` of an affine scheme, then the
  base change of `Γ(φ, ⊤)` to the residue field of the corresponding prime is bijective.** This
  is the translation of a generic-fibre condition on a map of sheaves into the bijectivity
  condition on a map of modules that `Module.CompleteDevissage` asks for.
* `AlgebraicGeometry.surjective_sectionsLinearMap_of_epi`: an epimorphism of quasi-coherent
  modules on an affine scheme is a surjection on global sections.
* `AlgebraicGeometry.cokernelSpecΓIso` and `AlgebraicGeometry.sectionsCokernelEquiv`: **the
  global sections of the cokernel of a map of quasi-coherent modules on an affine scheme are the
  cokernel of the induced map of global sections**, on a spectrum and on an arbitrary affine
  scheme.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.pullbackIsoPushforward` is obtained from uniqueness of left
adjoints: the direct images along `e.hom` and along `e.inv` are quasi-inverse, so the first is a
left adjoint of the second, as is the inverse image along `e.inv`.

The proof of the main result is a chain of four identifications. The canonical map from the
spectrum of the residue field of `t` factors as an isomorphism followed by
`Spec κ(p) ⟶ Spec A ≅ T`, so the hypothesis is an invertibility statement about the pullback
along the second factor, hence — the first factor being an isomorphism — about the pullback of
the direct image along `T.isoSpec.hom`. Naturality of the counit
`AlgebraicGeometry.Scheme.Modules.fromTildeΓNatTrans` of the tilde–sections adjunction, whose
two vertical maps are invertible because both modules are quasi-coherent, turns that into
invertibility of the pullback of `Γ(φ, ⊤)^~`, which
`AlgebraicGeometry.bijective_rTensor_of_isIso_pullback_map_tilde` converts into bijectivity of a
base change. The `Γ(T, ⊤)`-module structure the Spec–Γ dictionary puts on the sections is
restriction of scalars along `(ΓSpecIso A).inv ≫ T.isoSpec.hom.appTop`, which is the identity,
so `AlgebraicGeometry.specΓSectionsEquiv` is the identity map and the two spellings of the map
of sections differ by nothing.

`LinearMap.bijective_baseChange_comp` is a statement of pure linear algebra; it lives here
because both main results are obtained from a statement about the Spec–Γ module of sections by
composing with `AlgebraicGeometry.specΓSectionsEquiv` on each side, and this is what transports
the conclusion across that composition.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

universe u

namespace LinearMap

/-- **Bijectivity of a base change is invariant under isomorphisms of source and target.** A map
obtained from another by composing with a linear equivalence on each side has bijective base
change as soon as the other one does. -/
public theorem bijective_baseChange_comp {R : Type u} [CommRing R] (κ : Type u) [CommRing κ]
    [Algebra R κ] {M₁ M₂ M₁' M₂' : Type u} [AddCommGroup M₁] [AddCommGroup M₂]
    [AddCommGroup M₁'] [AddCommGroup M₂'] [Module R M₁] [Module R M₂] [Module R M₁']
    [Module R M₂'] (ψ : M₁ →ₗ[R] M₂) (ψ' : M₁' →ₗ[R] M₂') (u : M₁' ≃ₗ[R] M₁)
    (v : M₂ ≃ₗ[R] M₂')
    (hψ' : ψ' = (v : M₂ →ₗ[R] M₂') ∘ₗ (ψ ∘ₗ (u : M₁' →ₗ[R] M₁)))
    (h : Function.Bijective (ψ.baseChange κ)) : Function.Bijective (ψ'.baseChange κ) := by
  have hu : Function.Bijective ((u : M₁' →ₗ[R] M₁).baseChange κ) :=
    (LinearEquiv.baseChange R κ M₁' M₁ u).bijective
  have hv : Function.Bijective ((v : M₂ →ₗ[R] M₂').baseChange κ) :=
    (LinearEquiv.baseChange R κ M₂ M₂' v).bijective
  rw [hψ', LinearMap.baseChange_comp, LinearMap.baseChange_comp]
  exact hv.comp (h.comp hu)

end LinearMap

namespace AlgebraicGeometry

namespace Scheme.Modules

/-- The direct image of modules along an isomorphism of schemes is an equivalence of categories,
with the direct image along the inverse isomorphism as its inverse. -/
public def pushforwardEquivOfIso {X Y : Scheme.{u}} (e : X ≅ Y) : X.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (pushforward e.hom) (pushforward e.inv)
    ((pushforwardComp e.hom e.inv) ≪≫ pushforwardCongr e.hom_inv_id ≪≫ pushforwardId X).symm
    ((pushforwardComp e.inv e.hom) ≪≫ pushforwardCongr e.inv_hom_id ≪≫ pushforwardId Y)

/-- **The inverse image along an isomorphism of schemes is the direct image along its inverse.**
Both are left adjoint to the direct image along `e.inv`, the second because the direct images
along `e.hom` and `e.inv` are quasi-inverse. -/
public def pullbackIsoPushforward {X Y : Scheme.{u}} (e : X ≅ Y) :
    pullback e.inv ≅ pushforward e.hom :=
  (pullbackPushforwardAdjunction e.inv).leftAdjointUniq (pushforwardEquivOfIso e).toAdjunction

/-- **The inverse image of modules along an isomorphism of schemes reflects isomorphisms**: it is
the direct image along an open immersion, which is fully faithful. -/
public theorem isIso_of_isIso_pullback_map {X Y : Scheme.{u}} (ρ : X ⟶ Y) [IsIso ρ]
    {M N : Y.Modules} (ψ : M ⟶ N) (h : IsIso ((pullback ρ).map ψ)) : IsIso ψ := by
  have h2 : IsIso ((pushforward (asIso ρ).inv).map ψ) :=
    (NatIso.isIso_map_iff (pullbackIsoPushforward (asIso ρ).symm) ψ).mp h
  have := (pushforward (asIso ρ).inv).Full
  have := (pushforward (asIso ρ).inv).Faithful
  have : (pushforward (asIso ρ).inv).ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_full_and_faithful _
  exact let := h2; isIso_of_reflects_iso ψ (pushforward (asIso ρ).inv)

end Scheme.Modules

/-- **The `Γ(T, ⊤)`-module attached by the Spec–Γ dictionary to the direct image of `M` along
`T.isoSpec.hom` is the module of global sections of `M`.** Both are the same type; the scalar
structures agree because the composite `A ⟶ Γ(Spec A, ⊤) ⟶ Γ(T, ⊤)` of
`(ΓSpecIso A).inv` with `T.isoSpec.hom.appTop` is the identity. -/
public def specΓSectionsEquiv (T : Scheme.{u}) [IsAffine T] (M : T.Modules) :
    ↥(moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward T.isoSpec.hom).obj M)) ≃ₗ[Γ(T, ⊤)]
      Γ(M, (⊤ : T.Opens)) where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' a x := by
    change (T.isoSpec.hom.appTop ((Scheme.ΓSpecIso Γ(T, (⊤ : T.Opens))).inv a)) •
      (show Γ(M, (⊤ : T.Opens)) from x) = a • _
    rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
    simp
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl

/-- The map of global sections induced by `φ`, read through the Spec–Γ dictionary, is the map of
global sections induced by `φ`. -/
public theorem specΓSectionsEquiv_naturality {T : Scheme.{u}} [IsAffine T] {M N : T.Modules}
    (φ : M ⟶ N) :
    Scheme.Modules.sectionsLinearMap φ ⊤ =
      ((specΓSectionsEquiv T N) : _ →ₗ[Γ(T, ⊤)] Γ(N, (⊤ : T.Opens))) ∘ₗ
        ((moduleSpecΓFunctor.map ((Scheme.Modules.pushforward T.isoSpec.hom).map φ)).hom ∘ₗ
          ((specΓSectionsEquiv T M).symm : Γ(M, (⊤ : T.Opens)) →ₗ[Γ(T, ⊤)] _)) := by
  ext x
  rfl

/-- The direct image of a quasi-coherent module along `T.isoSpec.hom` is quasi-coherent. -/
private theorem isQuasicoherent_pushforward_isoSpec (T : Scheme.{u}) [IsAffine T] (M : T.Modules)
    [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward T.isoSpec.hom).obj M).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_pushforward_of_isIso T.isoSpec M

/-- The counit of the tilde–sections adjunction is invertible at a quasi-coherent module. -/
private theorem isIso_fromTildeΓNatTrans_app {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] : IsIso (Scheme.Modules.fromTildeΓNatTrans.app M) :=
  (inferInstance : IsIso (Scheme.Modules.fromTildeΓ M))

/-- The canonical morphism from the spectrum of the residue field of a point `t` of an affine
scheme `T` factors through the spectrum of the residue field of the prime of `Γ(T, ⊤)`
corresponding to `t`, by an isomorphism followed by `Spec κ(p) ⟶ Spec Γ(T, ⊤) ≅ T`. -/
public theorem fromSpecResidueField_eq_comp {T : Scheme.{u}} [IsAffine T] (t : T)
    [h : (T.isoSpec.hom t).asIdeal.IsPrime] :
    T.fromSpecResidueField t =
      Spec.map ((Scheme.Spec.residueFieldIso Γ(T, (⊤ : T.Opens)) (T.isoSpec.hom t)).inv ≫
          T.isoSpec.hom.residueFieldMap t) ≫
        (Spec.map (CommRingCat.ofHom
            (algebraMap Γ(T, (⊤ : T.Opens)) (T.isoSpec.hom t).asIdeal.ResidueField)) ≫
          T.isoSpec.inv) := by
  rw [Spec.map_comp, Category.assoc,
    Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField_assoc,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]
  simp

/-- **A map of quasi-coherent modules on an affine scheme which becomes an isomorphism over the
residue field of a point induces, on global sections, a map whose base change to the residue
field of the corresponding prime is bijective.**

This is the converse direction of the affine dictionary used by the translation of a
scheme-theoretic complete dévissage into a ring-theoretic one: the generic-fibre condition of
`AlgebraicGeometry.DevissageStage` becomes the condition
`Module.CompleteDevissage.fiber_bijective`. -/
public theorem bijective_baseChange_sectionsLinearMap_of_isIso_pullback {T : Scheme.{u}}
    [IsAffine T] {M N : T.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) (t : T)
    (p : Ideal Γ(T, (⊤ : T.Opens))) [p.IsPrime] (hp : (T.isoSpec.hom t).asIdeal = p)
    (h : IsIso ((Scheme.Modules.pullback (T.fromSpecResidueField t)).map φ)) :
    Function.Bijective
      ((Scheme.Modules.sectionsLinearMap φ (⊤ : T.Opens)).baseChange p.ResidueField) := by
  subst hp
  set A := Γ(T, (⊤ : T.Opens)) with hA
  set q := T.isoSpec.hom t with hq
  set c : Spec (CommRingCat.of q.asIdeal.ResidueField) ⟶ Spec A :=
    Spec.map (CommRingCat.ofHom (algebraMap A q.asIdeal.ResidueField)) with hc
  set ρ : Spec (T.residueField t) ⟶ Spec (CommRingCat.of q.asIdeal.ResidueField) :=
    Spec.map ((Scheme.Spec.residueFieldIso A q).inv ≫ T.isoSpec.hom.residueFieldMap t) with hρ
  rw [fromSpecResidueField_eq_comp t] at h
  have h1 : IsIso ((Scheme.Modules.pullback ρ).map
      ((Scheme.Modules.pullback (c ≫ T.isoSpec.inv)).map φ)) :=
    (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp ρ (c ≫ T.isoSpec.inv)) φ).mpr h
  have h2 : IsIso ((Scheme.Modules.pullback (c ≫ T.isoSpec.inv)).map φ) :=
    Scheme.Modules.isIso_of_isIso_pullback_map ρ _ h1
  have h3 : IsIso ((Scheme.Modules.pullback c).map
      ((Scheme.Modules.pullback T.isoSpec.inv).map φ)) :=
    (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp c T.isoSpec.inv) φ).mpr h2
  have h4 : IsIso ((Scheme.Modules.pullback c).map
      ((Scheme.Modules.pushforward T.isoSpec.hom).map φ)) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerRight
      (Scheme.Modules.pullbackIsoPushforward T.isoSpec) (Scheme.Modules.pullback c)) φ).mp h3
  have := isQuasicoherent_pushforward_isoSpec T M
  have := isQuasicoherent_pushforward_isoSpec T N
  set ψ := (Scheme.Modules.pushforward T.isoSpec.hom).map φ with hψ
  set Q := Scheme.Modules.pullback c with hQ
  have key := congrArg Q.map (Scheme.Modules.fromTildeΓNatTrans.naturality ψ)
  rw [Q.map_comp, Q.map_comp] at key
  have := isIso_fromTildeΓNatTrans_app ((Scheme.Modules.pushforward T.isoSpec.hom).obj M)
  have := isIso_fromTildeΓNatTrans_app ((Scheme.Modules.pushforward T.isoSpec.hom).obj N)
  have hcomp : IsIso (Q.map ((moduleSpecΓFunctor ⋙ tilde.functor A).map ψ) ≫
      Q.map (Scheme.Modules.fromTildeΓNatTrans.app
        ((Scheme.Modules.pushforward T.isoSpec.hom).obj N))) := by
    rw [key]
    exact let := h4; IsIso.comp_isIso' inferInstance h4
  have h5 : IsIso (Q.map ((tilde.functor A).map (moduleSpecΓFunctor.map ψ))) :=
    let := hcomp
    IsIso.of_isIso_comp_right (Q.map ((moduleSpecΓFunctor ⋙ tilde.functor A).map ψ))
      (Q.map (Scheme.Modules.fromTildeΓNatTrans.app _))
  have h6 := bijective_rTensor_of_isIso_pullback_map_tilde ↥A q.asIdeal.ResidueField
    (algebraMap ↥A q.asIdeal.ResidueField) _ _ (moduleSpecΓFunctor.map ψ) h5
  have hm : @Algebra.toModule ↥A q.asIdeal.ResidueField _ _
      (algebraMap ↥A q.asIdeal.ResidueField).toAlgebra =
      (inferInstance : Module ↥A q.asIdeal.ResidueField) :=
    Module.ext' _ _ fun b x => (Algebra.smul_def b x).symm
  rw [hm] at h6
  have h7 : Function.Bijective
      ((moduleSpecΓFunctor.map ψ).hom.baseChange q.asIdeal.ResidueField) := by
    have hl := (LinearMap.lTensor_bij_iff_rTensor_bij q.asIdeal.ResidueField
      (moduleSpecΓFunctor.map ψ).hom).2 h6
    rwa [← LinearMap.baseChange_eq_lTensor] at hl
  exact LinearMap.bijective_baseChange_comp _ _ _ (specΓSectionsEquiv T M).symm
    (specΓSectionsEquiv T N) (specΓSectionsEquiv_naturality φ) h7

/-- On the spectrum of a ring, the global-sections functor preserves epimorphisms between
quasi-coherent modules: the counit of the tilde–sections adjunction is invertible at both
modules, so `tilde.functor` carries the induced map to an epimorphism, and `tilde.functor` is
faithful, hence reflects epimorphisms. -/
public theorem epi_moduleSpecΓFunctor_map {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (ψ : M ⟶ N) [Epi ψ] :
    Epi (moduleSpecΓFunctor.map ψ) := by
  have := isIso_fromTildeΓNatTrans_app M
  have := isIso_fromTildeΓNatTrans_app N
  have hlhs : Epi ((moduleSpecΓFunctor ⋙ tilde.functor R).map ψ ≫
      Scheme.Modules.fromTildeΓNatTrans.app N) := by
    rw [Scheme.Modules.fromTildeΓNatTrans.naturality ψ]
    exact epi_comp _ _
  exact (tilde.functor R).epi_of_epi_map
    ((epi_comp_iff_of_isIso _ (Scheme.Modules.fromTildeΓNatTrans.app N)).mp hlhs)

/-- **An epimorphism of quasi-coherent modules on an affine scheme induces a surjection on
global sections.** -/
public theorem surjective_sectionsLinearMap_of_epi {T : Scheme.{u}} [IsAffine T]
    {M N : T.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) [Epi φ] :
    Function.Surjective (Scheme.Modules.sectionsLinearMap φ (⊤ : T.Opens)) := by
  have hpe : (Scheme.Modules.pushforward T.isoSpec.hom).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (Scheme.Modules.pushforwardEquivOfIso T.isoSpec).toAdjunction
  have hepi : Epi ((Scheme.Modules.pushforward T.isoSpec.hom).map φ) := hpe.preserves φ
  have := isQuasicoherent_pushforward_isoSpec T M
  have := isQuasicoherent_pushforward_isoSpec T N
  have h3 := epi_moduleSpecΓFunctor_map ((Scheme.Modules.pushforward T.isoSpec.hom).map φ)
  have h4 : Function.Surjective
      (moduleSpecΓFunctor.map ((Scheme.Modules.pushforward T.isoSpec.hom).map φ)).hom :=
    LinearMap.range_eq_top.1 (let := h3; ModuleCat.range_eq_top_of_epi _)
  intro y
  obtain ⟨x, hx⟩ := h4 ((specΓSectionsEquiv T N).symm y)
  refine ⟨specΓSectionsEquiv T M x, ?_⟩
  have hnat : (Scheme.Modules.sectionsLinearMap φ (⊤ : T.Opens)) ((specΓSectionsEquiv T M) x) =
      specΓSectionsEquiv T N ((moduleSpecΓFunctor.map
        ((Scheme.Modules.pushforward T.isoSpec.hom).map φ)).hom x) :=
    DFunLike.congr_fun (specΓSectionsEquiv_naturality φ) x
  rw [hnat, hx]
  exact (specΓSectionsEquiv T N).apply_symm_apply y

/-- On the spectrum of a ring, the global-sections functor carries the cokernel of a map of
quasi-coherent modules to the cokernel of the induced map of modules of sections:
`tilde.functor` is a left adjoint, hence preserves cokernels, and the naturality square of the
counit at the map has invertible verticals. -/
public def cokernelSpecΓIso {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (ψ : M ⟶ N) :
    cokernel (moduleSpecΓFunctor.map ψ) ≅ moduleSpecΓFunctor.obj (cokernel ψ) :=
  let iM := asIso (Scheme.Modules.fromTildeΓ M)
  let iN := asIso (Scheme.Modules.fromTildeΓ N)
  tilde.toTildeΓNatIso.app (cokernel (moduleSpecΓFunctor.map ψ)) ≪≫
    moduleSpecΓFunctor.mapIso (PreservesCokernel.iso (tilde.functor R) _ ≪≫
      cokernel.mapIso _ ψ iM iN (Scheme.Modules.fromTildeΓNatTrans.naturality ψ))

/-- **On an affine scheme the global sections of the cokernel of a map of quasi-coherent modules
are the cokernel of the induced map of global sections.** -/
public def sectionsCokernelEquiv {T : Scheme.{u}} [IsAffine T] {M N : T.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) :
    (Γ(N, (⊤ : T.Opens)) ⧸ LinearMap.range (Scheme.Modules.sectionsLinearMap φ (⊤ : T.Opens)))
      ≃ₗ[Γ(T, ⊤)] Γ(cokernel φ, (⊤ : T.Opens)) :=
  letI : (Scheme.Modules.pushforward T.isoSpec.hom).IsLeftAdjoint :=
    (Scheme.Modules.pushforwardEquivOfIso T.isoSpec).toAdjunction.isLeftAdjoint
  haveI : ((Scheme.Modules.pushforward T.isoSpec.hom).obj M).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_pushforward_of_isIso T.isoSpec M
  haveI : ((Scheme.Modules.pushforward T.isoSpec.hom).obj N).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_pushforward_of_isIso T.isoSpec N
  have hrange : Submodule.map (specΓSectionsEquiv T N).toLinearMap
      (LinearMap.range (moduleSpecΓFunctor.map
        ((Scheme.Modules.pushforward T.isoSpec.hom).map φ)).hom) =
      LinearMap.range (Scheme.Modules.sectionsLinearMap φ (⊤ : T.Opens)) := by
    rw [specΓSectionsEquiv_naturality φ, LinearMap.range_comp, LinearMap.range_comp]
    simp
  (Submodule.Quotient.equiv _ _ (specΓSectionsEquiv T N) hrange).symm.trans
    (((ModuleCat.cokernelIsoRangeQuotient
          (moduleSpecΓFunctor.map ((Scheme.Modules.pushforward T.isoSpec.hom).map φ))).symm ≪≫
        cokernelSpecΓIso ((Scheme.Modules.pushforward T.isoSpec.hom).map φ) ≪≫
        moduleSpecΓFunctor.mapIso
          (PreservesCokernel.iso (Scheme.Modules.pushforward T.isoSpec.hom) φ).symm)
      |>.toLinearEquiv.trans (specΓSectionsEquiv T (cokernel φ)))

end AlgebraicGeometry

end
