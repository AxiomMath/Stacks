module

public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsFlatAtPoint
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraExistence
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraicFlatness
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffinePullbackSections
public import StacksFrontier.AlgebraicGeometry.Smooth.TildeTransport

/-!
# Projectivity of a base change after an elementary étale localization

Stacks 05ID is a statement about schemes; this file reads it on affines, where it becomes a
statement about rings. Let `R → S` be of finite presentation, let `N` be a finitely presented
`S`-module which is flat over `R`, and let `q` be a prime of `S`. Then there is an elementary
étale localization `R → R'`, `S → S'`, `q'`, `p'` of `R → S` at `q` in the sense of Stacks 05HW
(`Algebra.ElementaryEtaleLocalization`) such that `S' ⊗_S N` is a *projective* `R'`-module.

The derivation is the Spec/Γ dictionary and nothing else, exactly as Stacks 05I1 is the ring-level
reading of Stacks 05HR. On `Spec S` the module `N` becomes `Ñ`, which is of finite presentation by
Stacks 01PC and flat over `Spec R` at the point of `q` because every localization of a module flat
over `R` is again flat over `R`; the geometric statement then produces a square of affine
elementary étale neighbourhoods on which the global sections of the pullback of `Ñ` are projective
over the functions on the lower neighbourhood. Taking rings of functions turns that square into an
elementary étale localization — this is `AlgebraicGeometry.elementaryEtaleLocalizationOfSquare`,
which is built so that its `R' → S'` *is* the map on global sections of the vertical morphism, so
the module structure of the geometric conclusion is already the one the localization carries — and
the affine pullback dictionary of Stacks 01I9 identifies those global sections with `S' ⊗_S N`.

## Main results

* `Module.exists_elementaryEtaleLocalization_projective_baseChange`: **Stacks 05ID in its
  ring-theoretic form.**

## Implementation notes

Everything lives in a single universe, for the reason it does in Stacks 05I1: the rings of
functions of a `Scheme.{u}` are in `Type u`, so the two upper rings of the localization land in
the universe of `R` and `S` whatever universes those are given, and the module has to be in that
universe too because `AlgebraicGeometry.tilde` of a module over `R : CommRingCat.{u}` is a
`Scheme.{u}`-module only for a module in `Type u`.

The upper neighbourhood of the geometric statement is merely *affine*, not literally a spectrum,
so the affine pullback dictionary is not applicable to it directly; it is applied after the
neighbourhood has been identified with the spectrum of its own ring of functions, which is what
`AlgebraicGeometry.sectionsPullbackIsoSpecEquiv` below is for. Pulling a sheaf of modules back
along an isomorphism is an equivalence of categories, so the unit of the pullback--pushforward
adjunction is an isomorphism there, and that is the comparison of sections being used.

Restriction of the identification of sections from `S'` to `R'` needs no work: both module
structures over `R'` are restrictions of the `S'`-structures along `algebraMap R' S'`, so the
`S'`-linear equivalence is already `R'`-linear on the nose.

## References

* [Stacks Project, Tag 05ID](https://stacks.math.columbia.edu/tag/05ID)
* [Stacks Project, Tag 05HW](https://stacks.math.columbia.edu/tag/05HW)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01PC](https://stacks.math.columbia.edu/tag/01PC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### Sections of a pullback along an isomorphism -/

/-- The global sections of a sheaf of modules on `Y` and of its pullback along an isomorphism
`f : X ≅ Y` agree, linearly over the functions on `Y` acting on the pullback through `f`.

The comparison is the unit of the pullback--pushforward adjunction, which is an isomorphism
because the pullback is an equivalence of categories. -/
def sectionsPullbackIsoOfIsIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (F : Y.Modules) :
    letI : Module Γ(Y, ⊤) Γ((Scheme.Modules.pullback f).obj F, ⊤) :=
      Module.compHom _ f.appTop.hom
    Γ(F, ⊤) ≃ₗ[Γ(Y, ⊤)] Γ((Scheme.Modules.pullback f).obj F, ⊤) := by
  have : (Scheme.Modules.pullback f).IsEquivalence :=
    Scheme.Modules.isEquivalence_pullback_of_isIso f
  let η := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F
  have : IsIso η := inferInstance
  let e := asIso η
  letI : Module Γ(Y, ⊤) Γ((Scheme.Modules.pullback f).obj F, ⊤) :=
    Module.compHom _ f.appTop.hom
  exact
    { toFun := e.hom.val.app (.op ⊤)
      invFun := e.inv.val.app (.op ⊤)
      left_inv := fun t => congr($(e.hom_inv_id).val.app (.op ⊤) t)
      right_inv := fun t => congr($(e.inv_hom_id).val.app (.op ⊤) t)
      map_add' := fun t t' => map_add _ t t'
      map_smul' := fun r t => (e.hom.val.app (.op ⊤)).hom.map_smul r t }

/-- The global sections of a sheaf of modules on an affine scheme `X`, read as a module over
`Γ(X, ⊤)` through the identification of `X` with the spectrum of `Γ(X, ⊤)`.

This is `AlgebraicGeometry.sectionsPullbackIsoOfIsIso` for `X.isoSpec.inv`, with the action
rewritten through `Stacks.Modules.isoSpec_inv_appTop`: on the spectrum of a ring the canonical
action is the one of the ring itself rather than the one of the functions on `X`. -/
def sectionsPullbackIsoSpecEquiv {X : Scheme.{u}} [IsAffine X] (F : X.Modules) :
    Γ(F, ⊤) ≃ₗ[Γ(X, ⊤)]
      (moduleSpecΓFunctor (R := Γ(X, ⊤))).obj
        ((Scheme.Modules.pullback X.isoSpec.inv).obj F) := by
  letI : Module Γ(X, ⊤) Γ((Scheme.Modules.pullback X.isoSpec.inv).obj F, ⊤) :=
    Module.compHom _ X.isoSpec.inv.appTop.hom
  let e : Γ(F, ⊤) ≃ₗ[Γ(X, ⊤)] Γ((Scheme.Modules.pullback X.isoSpec.inv).obj F, ⊤) :=
    sectionsPullbackIsoOfIsIso X.isoSpec.inv F
  exact
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := fun r t => by
        rw [RingHom.id_apply]
        refine (e.map_smul r t).trans ?_
        exact congrArg (fun φ : Γ(X, ⊤) ⟶ Γ(Spec Γ(X, ⊤), ⊤) =>
          (CommRingCat.Hom.hom φ) r • e t) (Stacks.Modules.isoSpec_inv_appTop (T := X)) }

/-- **The affine pullback dictionary over an affine scheme which is not a spectrum.** For a
morphism `f : X ⟶ Spec A` from an affine scheme and an `A`-module `M`, the global sections of the
pullback of `M̃` along `f` are `Γ(X, ⊤) ⊗_A M`, linearly over `Γ(X, ⊤)`, where `Γ(X, ⊤)` is an
`A`-algebra through the map on global sections of `f`.

This is Stacks 01I9 (`AlgebraicGeometry.pullbackTildeIso`) read on `X` instead of on
`Spec Γ(X, ⊤)`, the comparison of the two being
`AlgebraicGeometry.sectionsPullbackIsoSpecEquiv`. -/
def affineSectionsPullbackTildeEquiv {A : CommRingCat.{u}} {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec A) (M : ModuleCat.{u} A) :
    letI : Algebra A Γ(X, ⊤) := ((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom.toAlgebra
    Γ((Scheme.Modules.pullback f).obj (tilde M), ⊤) ≃ₗ[Γ(X, ⊤)] (Γ(X, ⊤) ⊗[A] M) := by
  let φ : A ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso A).inv ≫ f.appTop
  letI : Algebra A Γ(X, ⊤) := φ.hom.toAlgebra
  have hf : X.isoSpec.inv ≫ f = Spec.map φ := by
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  let e := sectionsPullbackIsoSpecEquiv ((Scheme.Modules.pullback f).obj (tilde M))
  let e' := (Scheme.Modules.pullbackComp X.isoSpec.inv f ≪≫
      Scheme.Modules.pullbackCongr hf).app (tilde M) ≪≫
    (pullbackTildeIso A Γ(X, ⊤) φ).app M
  let e'' := (moduleSpecΓFunctor (R := Γ(X, ⊤))).mapIso e' ≪≫
    (tilde.toTildeΓNatIso (R := Γ(X, ⊤))).symm.app ((ModuleCat.extendScalars φ.hom).obj M)
  exact e.trans e''.toLinearEquiv

end AlgebraicGeometry

namespace Module

open AlgebraicGeometry

/-- **Stacks Project, Tag 05ID, ring-theoretic form.** Let `R → S` be a ring map of finite
presentation, let `N` be a finitely presented `S`-module which is flat over `R` and let `q` be a
prime of `S`. There is an elementary étale localization of `R → S` at `q` — rings `R'` and `S'`,
primes `p'` and `q'` — such that the base change `S' ⊗_S N` is projective as an `R'`-module.

This is the scheme-level Tag 05ID,
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt`,
specialised to `Spec S → Spec R` and `Ñ` and read through the affine dictionary: the square of
affine elementary étale neighbourhoods becomes an elementary étale localization by
`AlgebraicGeometry.elementaryEtaleLocalizationOfSquare`, and the projective module of global
sections becomes `S' ⊗_S N` by `AlgebraicGeometry.affineSectionsPullbackTildeEquiv`. -/
theorem exists_elementaryEtaleLocalization_projective_baseChange
    (R S N : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.FinitePresentation S N] [Module.Flat R N]
    (q : Ideal S) [q.IsPrime] :
    ∃ E : Algebra.ElementaryEtaleLocalization.{u, u, u, u} R S (q.under R) q,
      letI : Module E.R' (TensorProduct S E.S' N) :=
        Module.compHom _ (algebraMap E.R' E.S')
      Module.Projective E.R' (TensorProduct S E.S' N) := by
  let f : Spec (.of S) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let Nm : ModuleCat.{u} (CommRingCat.of S) := ModuleCat.of S N
  let F : (Spec (.of S)).Modules := tilde Nm
  let x : Spec (.of S) := ⟨q, inferInstance⟩
  have : LocallyOfFinitePresentation f :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have : F.IsFinitePresentation := (tilde_isFinitePresentation_iff Nm).mpr inferInstance
  have hflat : IsFlatOverAt f.toLRSHom.toShHom F x :=
    isFlatOver_spec_tilde_of_flat (CommRingCat.ofHom (algebraMap R S)) Nm rfl inferInstance x
  obtain ⟨V, U, h, hVel, hUel, hsq, hpt, hUa, hVa, hproj⟩ :=
    exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt f F x hflat
  let : IsAffine U.scheme := hUa
  let : IsAffine V.scheme := hVa
  let : Algebra ↥Γ(V.scheme, ⊤) ↥Γ(U.scheme, ⊤) := h.appTop.hom.toAlgebra
  let : Algebra (CommRingCat.of S) ↥Γ(U.scheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of S)).inv ≫ U.toBase.appTop).hom.toAlgebra
  let : Module ↥Γ(V.scheme, ⊤) Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤) :=
    Module.compHom _ h.appTop.hom
  let : Module ↥Γ(V.scheme, ⊤) (↥Γ(U.scheme, ⊤) ⊗[S] N) := Module.compHom _ h.appTop.hom
  refine ⟨elementaryEtaleLocalizationOfSquare q U V h hUel hVel hsq.symm hpt, ?_⟩
  change Module.Projective ↥Γ(V.scheme, ⊤) (↥Γ(U.scheme, ⊤) ⊗[S] N)
  have hprojS : Module.Projective ↥Γ(V.scheme, ⊤)
      Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤) := hproj
  let eS := affineSectionsPullbackTildeEquiv U.toBase Nm
  exact Module.Projective.of_equiv'
    (M := Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤))
    { toFun := eS
      invFun := eS.symm
      left_inv := eS.left_inv
      right_inv := eS.right_inv
      map_add' := eS.map_add
      map_smul' := fun r t => eS.map_smul (h.appTop.hom r) t }

end Module

end
