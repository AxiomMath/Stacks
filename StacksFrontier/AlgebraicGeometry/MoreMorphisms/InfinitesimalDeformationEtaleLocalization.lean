module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationAction
public import StacksFrontier.RingTheory.Kaehler.EtaleTransport
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Infinitesimal deformations of maps and étale localization

Consider a commutative diagram of first order thickenings together with a commutative square of
schemes,
```
(T₂ ⊂ T₂') --(a₂, a₂')--> (X₂ ⊂ X₂')        X₂' --> S₂
   |                          |               |       |
 (h, h')                   (f, f')            v       v
   v                          v              X₁' --> S₁
(T₁ ⊂ T₁') --(a₁, a₁')--> (X₁ ⊂ X₁')
```
with `f : X₂ ⟶ X₁` and `S₂ ⟶ S₁` étale. [Stacks Project, Tag 04BY] transports an
`𝒪_{T₁}`-linear map `θ₁ : a₁^*Ω_{X₁/S₁} ⟶ 𝒞_{T₁/T₁'}` to a map
`θ₂ : a₂^*Ω_{X₂/S₂} ⟶ 𝒞_{T₂/T₂'}` along the identification
`a₂^*Ω_{X₂/S₂} = h^*a₁^*Ω_{X₁/S₁}` of [Stacks Project, Tag 04BX], and asserts that the two
actions of [Stacks Project, Tag 0CK1] are then compatible with the vertical maps:
`(θ₂ ⬝ a₂') ≫ f' = h' ≫ (θ₁ ⬝ a₁')`.

This file proves that statement on global sections over affine ambient schemes, with the action
of [Stacks Project, Tag 0CK1] in its affine form `Stacks.Thickenings.derivationAction`. The
action is in fact available for arbitrary schemes, as
`Stacks.Thickenings.derivationActionSheaf`; the affineness here is a restriction of this
development, not of the library.

## Main definitions

* `Stacks.Thickenings.conormalTransport`: the map `h^*𝒞_{T₁/T₁'} ⟶ 𝒞_{T₂/T₂'}` induced by
  `(h, h')` on global sections, read `Γ(X₁, ⊤)`-linearly.
* `Stacks.Thickenings.localizedDerivation`: the transported datum `θ₂`.

## Main results

* `Stacks.Thickenings.conormalTransport_apply`: on underlying sections the transport is `h'^♯`.
* `Stacks.Thickenings.formallyEtale_appTop`: global sections of an étale morphism of affine
  schemes form a formally étale algebra.
* `Stacks.Thickenings.localizedDerivation_apply`: the compatibility
  `h'(D₁(y)) = D₂(f^♯ y)` of the source's proof.
* `Stacks.Thickenings.derivationAction_comp_etaleLocalization`: the affine case of
  [Stacks Project, Tag 04BY]; the unrestricted statement, which carries the tag, is
  `Stacks.Thickenings.derivationActionSheaf_comp_etaleLocalization`.

## Implementation notes

With all ambient schemes and both bases affine, the objects of the source become rings and
modules: `𝒞_{T_n/T_n'}` is the ideal `RingHom.ker i_n.appTop.hom`, `Ω_{X_n/S_n}` is
`Ω[Γ(X_n, ⊤)⁄Γ(S_n, ⊤)]`, and the datum `θ_n` is a `Γ(X_n, ⊤)`-linear map between them, as in
`Stacks.Thickenings.derivationAction`.

The identification of [Stacks Project, Tag 04BX] becomes
`Stacks.KaehlerDifferential.etaleTransport`: the étale hypotheses give
`Algebra.FormallyEtale Γ(X₁, ⊤) Γ(X₂, ⊤)` and `Algebra.FormallyUnramified Γ(S₁, ⊤) Γ(S₂, ⊤)`,
and an `Γ(X₁, ⊤)`-linear map out of `Ω[Γ(X₁, ⊤)⁄Γ(S₁, ⊤)]` into a `Γ(X₂, ⊤)`-module then
extends uniquely along them. So `θ₂` is *constructed*, not characterised by an existence
statement, and the compatibility of the source's proof,
`h'(D₁(x)) = D₂(f^♯ x)`, is its defining property.

Three scalar towers are needed to run that extension and all three hold on the nose, because
every algebra and module structure in sight is restriction of scalars along a map of global
sections and `Stacks.Thickenings.appTop_comp_apply` is a definitional equality. The only one
that needs the commutativity of the square of bases is `Γ(S₁, ⊤) → Γ(S₂, ⊤) → Γ(X₂, ⊤)`.

The conormal module of `i₂` receives its `Γ(X₁, ⊤)`-module structure along `a₂ ≫ f` rather than
along the equal `h ≫ a₁`, because that is the spelling for which restriction of scalars from
`Γ(X₂, ⊤)` along `f^♯` is an identity.

This is the affine case only.

### No `@[stacks 04BY]`

[Stacks Project, Tag 04BY] is proved for arbitrary schemes by
`Stacks.Thickenings.derivationActionSheaf_comp_etaleLocalization` in the module
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationEtaleLocalizationSheaf`,
which carries the tag. The statement below is the same assertion restricted to affine ambient
schemes and affine bases, so it is no longer a statement of the whole tag and no longer carries
it; what it still contributes is the affine *model* of the construction, in which `𝒞_{T_n/T_n'}`
is an ideal of a ring, `Ω_{X_n/S_n}` is a module of Kähler differentials and `θ₂` is obtained by
the universal property of the formally étale square rather than as a composite of sheaf
comparisons.

The three ingredients that were recorded here as missing for the unrestricted statement are all
proved now:

* the map of [Stacks Project, Tag 01R4] for the square `i₂ ≫ h' = h ≫ i₁`, read inside the
  ambient structure sheaves through
  `Stacks.Thickenings.firstOrderImmersionConormalSheafι`, is the ring map `(h')^♯`:
  `Stacks.Thickenings.conormalTransportSheaf_eq`, the sheaf-level form of
  `Stacks.Thickenings.conormalTransport_apply`, in
  `StacksFrontier/AlgebraicGeometry/Thickenings/FirstOrderConormalTransport.lean`;
* `d` carries `d_{X₁/S₁} y` to `d_{X₂/S₂} (f^♯ y)` through the unit of `f^* ⊣ f_*`, which is its
  defining property `AlgebraicGeometry.Scheme.Hom.IsRelativeDifferentialsMap` read on sections:
  that is how `Stacks.Thickenings.app_localizedDerivationSheaf` is proved;
* the transposition of the three pseudofunctoriality isomorphisms of the module pullback across
  the adjunctions `a₂^* ⊣ a_{2,*}`, `f^* ⊣ f_*` and `h^* ⊣ h_*`, which turns the sheaf-level
  composite into a single map `Ω_{X₁/S₁} ⟶ (a₂ ≫ f)_*𝒞_{T₂/T₂'}`:
  `RingedSpaceModuleAdjunction.homEquiv_modulePullbackSquareIso_inv_comp`, which identifies that
  transpose with the *pushforward* comparison of the square.

The *existence* half of [Stacks Project, Tag 02H5] is not needed either, on two counts. First,
the unrestricted [Stacks Project, Tag 04BZ] shows that the conclusion does not need it. Second,
it is in any case available: it is `Stacks.Thickenings.derivationActionSheaf` together with
`Stacks.Thickenings.isDerivationAction_derivationActionSheaf`, in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/InfinitesimalDeformationSheafAction.lean`.

## References

* [Stacks Project, Tag 02H5](https://stacks.math.columbia.edu/tag/02H5)
* [Stacks Project, Tag 04BX](https://stacks.math.columbia.edu/tag/04BX)
* [Stacks Project, Tag 04BY](https://stacks.math.columbia.edu/tag/04BY)
* [Stacks Project, Tag 0CK1](https://stacks.math.columbia.edu/tag/0CK1)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Thickenings

variable {S₁ S₂ T₁ T₁' T₂ T₂' X₁ X₁' X₂ X₂' : Scheme.{u}}
  {i₁ : T₁ ⟶ T₁'} {i₂ : T₂ ⟶ T₂'} {j₁ : X₁ ⟶ X₁'} {j₂ : X₂ ⟶ X₂'}
  {a₁ : T₁ ⟶ X₁} {a₁' : T₁' ⟶ X₁'} {a₂ : T₂ ⟶ X₂} {a₂' : T₂' ⟶ X₂'}
  {h : T₂ ⟶ T₁} {h' : T₂' ⟶ T₁'} {f : X₂ ⟶ X₁} {f' : X₂' ⟶ X₁'}
  {p₁ : X₁' ⟶ S₁} {p₂ : X₂' ⟶ S₂} {k : S₂ ⟶ S₁}

/-! ### The conormal transport -/

/-- **The conormal module map of a morphism of thickenings, read over the target of the lower
horizontal map.** For first-order thickenings `i₁ : T₁ ⟶ T₁'` and `i₂ : T₂ ⟶ T₂'` with affine
ambient schemes, a morphism of thickenings `(h, h')` from `i₂` to `i₁`, and morphisms
`a₁ : T₁ ⟶ X₁`, `a₂ : T₂ ⟶ X₂`, `f : X₂ ⟶ X₁` with `a₂ ≫ f = h ≫ a₁`, the ring map `h'^♯`
carries the conormal module of `i₁` into that of `i₂`, linearly over `Γ(X₁, ⊤)` acting on the
source through `a₁` and on the target through `a₂ ≫ f`.

This is the composite `h^*𝒞_{T₁/T₁'} ⟶ 𝒞_{T₂/T₂'}` appearing in the construction of `θ₂` in
[Stacks Project, Tag 04BY]. -/
noncomputable def conormalTransport [IsAffine T₁'] [IsAffine T₂']
    (hi₁ : IsFirstOrderThickening i₁) (hi₂ : IsFirstOrderThickening i₂)
    (cT : i₂ ≫ h' = h ≫ i₁) (cf : a₂ ≫ f = h ≫ a₁) :
    letI := conormalModuleAlong hi₁ a₁
    letI := conormalModuleAlong hi₂ (a₂ ≫ f)
    RingHom.ker i₁.appTop.hom →ₗ[Γ(X₁, (⊤ : X₁.Opens))] RingHom.ker i₂.appTop.hom :=
  letI := conormalModuleAlong hi₁ a₁
  letI := conormalModuleAlong hi₂ (a₂ ≫ f)
  { toFun := fun y ↦
      ⟨h'.appTop.hom (y : Γ(T₁', (⊤ : T₁'.Opens))), mem_ker_appTop_of_comm cT y.2⟩
    map_add' := fun y z ↦ Subtype.ext (by
      simp only [AddMemClass.coe_add]
      exact map_add _ _ _)
    map_smul' := fun c y ↦ Subtype.ext (by
      obtain ⟨x, hx⟩ := Smooth.surjective_appTop_of_isFirstOrderThickening hi₁
        (a₁.appTop.hom c)
      have hx' : i₂.appTop.hom (h'.appTop.hom x) = (a₂ ≫ f).appTop.hom c := by
        rw [appTop_comm_of_comm cT, hx, appTop_comp_apply, ← cf]
      rw [RingHom.id_apply, conormalModuleAlong_smul hi₂ (a₂ ≫ f) c hx',
        Submodule.coe_smul, smul_eq_mul]
      change h'.appTop.hom ((c • y : RingHom.ker i₁.appTop.hom) :
        Γ(T₁', (⊤ : T₁'.Opens))) = _
      rw [conormalModuleAlong_smul hi₁ a₁ c hx, Submodule.coe_smul, smul_eq_mul, map_mul]) }

/-- On underlying sections `Stacks.Thickenings.conormalTransport` is the ring map `h'^♯` of the
ambient schemes. -/
theorem conormalTransport_apply [IsAffine T₁'] [IsAffine T₂']
    (hi₁ : IsFirstOrderThickening i₁) (hi₂ : IsFirstOrderThickening i₂)
    (cT : i₂ ≫ h' = h ≫ i₁) (cf : a₂ ≫ f = h ≫ a₁) (y : RingHom.ker i₁.appTop.hom) :
    letI := conormalModuleAlong hi₁ a₁
    letI := conormalModuleAlong hi₂ (a₂ ≫ f)
    ((conormalTransport hi₁ hi₂ cT cf y : RingHom.ker i₂.appTop.hom) :
        Γ(T₂', (⊤ : T₂'.Opens)))
      = h'.appTop.hom (y : Γ(T₁', (⊤ : T₁'.Opens))) :=
  rfl

/-! ### Étale morphisms of affine schemes on global sections -/

/-- **Global sections of an étale morphism of affine schemes form a formally étale algebra.**
This is the affine dictionary for the étale hypotheses of [Stacks Project, Tag 04BY]. -/
theorem formallyEtale_appTop {W W' : Scheme.{u}} (g : W ⟶ W') [IsAffine W] [IsAffine W']
    [AlgebraicGeometry.Etale g] :
    letI := appTopAlgebra g
    Algebra.FormallyEtale Γ(W', (⊤ : W'.Opens)) Γ(W, (⊤ : W.Opens)) :=
  let := appTopAlgebra g
  let : Algebra.Etale Γ(W', (⊤ : W'.Opens)) Γ(W, (⊤ : W.Opens)) :=
    RingHom.Etale.toAlgebra
      (HasRingHomProperty.appTop (P := @AlgebraicGeometry.Etale) g ‹AlgebraicGeometry.Etale g›)
  inferInstance

/-! ### The transported datum -/

section Localized

variable [IsAffine S₁] [IsAffine S₂] [IsAffine T₁'] [IsAffine T₂'] [IsAffine X₁']
  [IsAffine X₂'] [AlgebraicGeometry.Etale f] [AlgebraicGeometry.Etale k]

omit [IsAffine S₁] [IsAffine S₂] [IsAffine X₁'] [IsAffine X₂'] [AlgebraicGeometry.Etale f]
  [AlgebraicGeometry.Etale k] in
/-- **The square of bases gives a tower of algebras of global sections.** The two routes
`Γ(S₁, ⊤) → Γ(X₁, ⊤) → Γ(X₂, ⊤)` and `Γ(S₁, ⊤) → Γ(S₂, ⊤) → Γ(X₂, ⊤)` agree, so `Γ(X₂, ⊤)` is a
`Γ(S₂, ⊤)`-algebra over `Γ(S₁, ⊤)`. -/
theorem isScalarTower_base (cS : f ≫ j₁ ≫ p₁ = (j₂ ≫ p₂) ≫ k) :
    letI := appTopAlgebra (j₂ ≫ p₂)
    letI := appTopAlgebra k
    letI := appTopAlgebra (f ≫ j₁ ≫ p₁)
    IsScalarTower Γ(S₁, (⊤ : S₁.Opens)) Γ(S₂, (⊤ : S₂.Opens)) Γ(X₂, (⊤ : X₂.Opens)) :=
  let := appTopAlgebra (j₂ ≫ p₂)
  let := appTopAlgebra k
  let := appTopAlgebra (f ≫ j₁ ≫ p₁)
  IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [algebraMap_appTopAlgebra, algebraMap_appTopAlgebra, algebraMap_appTopAlgebra,
      appTop_comp_apply, ← cS]

/-- **The transported derivation datum of [Stacks Project, Tag 04BY].** The map `θ₂` built from
`θ₁` as the composite
`a₂^*Ω_{X₂/S₂} = h^*a₁^*Ω_{X₁/S₁} ⟶ h^*𝒞_{T₁/T₁'} ⟶ 𝒞_{T₂/T₂'}`, on global sections: the
`Γ(X₁, ⊤)`-linear map `θ₁` followed by `Stacks.Thickenings.conormalTransport`, extended along
the formally étale square by `Stacks.KaehlerDifferential.etaleTransport`. -/
noncomputable def localizedDerivation (hi₁ : IsFirstOrderThickening i₁)
    (hi₂ : IsFirstOrderThickening i₂) (hj₁ : IsFirstOrderThickening j₁)
    (hj₂ : IsFirstOrderThickening j₂) (cT : i₂ ≫ h' = h ≫ i₁) (cf : a₂ ≫ f = h ≫ a₁)
    (cS : f ≫ j₁ ≫ p₁ = (j₂ ≫ p₂) ≫ k) :
    letI := appTopAlgebra (j₁ ≫ p₁)
    letI := conormalModuleAlong hi₁ a₁
    letI := appTopAlgebra (j₂ ≫ p₂)
    letI := conormalModuleAlong hi₂ a₂
    (Ω[Γ(X₁, (⊤ : X₁.Opens))⁄Γ(S₁, (⊤ : S₁.Opens))] →ₗ[Γ(X₁, (⊤ : X₁.Opens))]
        RingHom.ker i₁.appTop.hom) →
      (Ω[Γ(X₂, (⊤ : X₂.Opens))⁄Γ(S₂, (⊤ : S₂.Opens))] →ₗ[Γ(X₂, (⊤ : X₂.Opens))]
        RingHom.ker i₂.appTop.hom) :=
  letI := appTopAlgebra (j₁ ≫ p₁)
  letI := conormalModuleAlong hi₁ a₁
  letI := appTopAlgebra (j₂ ≫ p₂)
  letI := conormalModuleAlong hi₂ a₂
  letI := appTopAlgebra f
  letI := appTopAlgebra k
  letI := appTopAlgebra (f ≫ j₁ ≫ p₁)
  letI := conormalModuleAlong hi₂ (a₂ ≫ f)
  letI := hj₁.1
  letI := hj₂.1
  haveI : IsAffine X₁ := isAffine_of_isAffineHom j₁
  haveI : IsAffine X₂ := isAffine_of_isAffineHom j₂
  haveI : IsScalarTower Γ(S₁, (⊤ : S₁.Opens)) Γ(X₁, (⊤ : X₁.Opens)) Γ(X₂, (⊤ : X₂.Opens)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := isScalarTower_base cS
  haveI : IsScalarTower Γ(X₁, (⊤ : X₁.Opens)) Γ(X₂, (⊤ : X₂.Opens))
      (RingHom.ker i₂.appTop.hom) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  haveI := formallyEtale_appTop f
  haveI := formallyEtale_appTop k
  fun θ₁ ↦ Stacks.KaehlerDifferential.etaleTransport Γ(S₁, (⊤ : S₁.Opens))
    Γ(S₂, (⊤ : S₂.Opens)) Γ(X₁, (⊤ : X₁.Opens)) Γ(X₂, (⊤ : X₂.Opens))
    ((conormalTransport hi₁ hi₂ cT cf).comp θ₁)

/-- **The compatibility between the original and the transported datum**, the equation
`h'(D₁(x)) = D₂(f^♯ x)` of the proof of [Stacks Project, Tag 04BY]. On the differential of a
section coming from `X₁` the transported datum takes the image under `h'^♯` of the value of the
original datum. -/
theorem localizedDerivation_apply (hi₁ : IsFirstOrderThickening i₁)
    (hi₂ : IsFirstOrderThickening i₂) (hj₁ : IsFirstOrderThickening j₁)
    (hj₂ : IsFirstOrderThickening j₂) (cT : i₂ ≫ h' = h ≫ i₁) (cf : a₂ ≫ f = h ≫ a₁)
    (cS : f ≫ j₁ ≫ p₁ = (j₂ ≫ p₂) ≫ k) :
    letI := appTopAlgebra (j₁ ≫ p₁)
    letI := conormalModuleAlong hi₁ a₁
    letI := appTopAlgebra (j₂ ≫ p₂)
    letI := conormalModuleAlong hi₂ a₂
    ∀ (θ₁ : Ω[Γ(X₁, (⊤ : X₁.Opens))⁄Γ(S₁, (⊤ : S₁.Opens))] →ₗ[Γ(X₁, (⊤ : X₁.Opens))]
        RingHom.ker i₁.appTop.hom) (y : Γ(X₁, (⊤ : X₁.Opens))),
      ((localizedDerivation hi₁ hi₂ hj₁ hj₂ cT cf cS θ₁
            (KaehlerDifferential.D _ _ (f.appTop.hom y)) : RingHom.ker i₂.appTop.hom) :
          Γ(T₂', (⊤ : T₂'.Opens)))
        = h'.appTop.hom ((θ₁ (KaehlerDifferential.D _ _ y) : RingHom.ker i₁.appTop.hom) :
          Γ(T₁', (⊤ : T₁'.Opens))) := by
  let := appTopAlgebra (j₁ ≫ p₁)
  let := conormalModuleAlong hi₁ a₁
  let := appTopAlgebra (j₂ ≫ p₂)
  let := conormalModuleAlong hi₂ a₂
  let := appTopAlgebra f
  let := appTopAlgebra k
  let := appTopAlgebra (f ≫ j₁ ≫ p₁)
  let := conormalModuleAlong hi₂ (a₂ ≫ f)
  have := hj₁.1
  have := hj₂.1
  have : IsAffine X₁ := isAffine_of_isAffineHom j₁
  have : IsAffine X₂ := isAffine_of_isAffineHom j₂
  have : IsScalarTower Γ(S₁, (⊤ : S₁.Opens)) Γ(X₁, (⊤ : X₁.Opens)) Γ(X₂, (⊤ : X₂.Opens)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have := isScalarTower_base cS
  have : IsScalarTower Γ(X₁, (⊤ : X₁.Opens)) Γ(X₂, (⊤ : X₂.Opens))
      (RingHom.ker i₂.appTop.hom) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have := formallyEtale_appTop f
  have := formallyEtale_appTop k
  intro θ₁ y
  refine Eq.trans ?_
    (conormalTransport_apply hi₁ hi₂ cT cf (θ₁ (KaehlerDifferential.D _ _ y)))
  refine congrArg (fun z : RingHom.ker i₂.appTop.hom ↦ (z : Γ(T₂', (⊤ : T₂'.Opens)))) ?_
  exact Stacks.KaehlerDifferential.etaleTransport_D Γ(S₁, (⊤ : S₁.Opens))
    Γ(S₂, (⊤ : S₂.Opens)) Γ(X₁, (⊤ : X₁.Opens)) Γ(X₂, (⊤ : X₂.Opens))
    ((conormalTransport hi₁ hi₂ cT cf).comp θ₁) y

/-! ### The compatibility of the actions -/

/-- **Acting by a derivation commutes with an étale localization**, the affine case of
[Stacks Project, Tag 04BY]. Let `(h, h') : (T₂ ⊂ T₂') ⟶ (T₁ ⊂ T₁')` and
`(f, f') : (X₂ ⊂ X₂') ⟶ (X₁ ⊂ X₁')` be morphisms of first-order thickenings with affine ambient
schemes, let `(a₁, a₁')` and `(a₂, a₂')` be morphisms of thickenings compatible with them, and
let `p₁ : X₁' ⟶ S₁`, `p₂ : X₂' ⟶ S₂` and `k : S₂ ⟶ S₁` form a commutative square with `f` and
affine bases. Assume `f` and `k` are étale. Then for every `Γ(X₁, ⊤)`-linear map
`θ₁ : Ω[Γ(X₁, ⊤)⁄Γ(S₁, ⊤)] ⟶ 𝒞_{T₁/T₁'}`, acting by `θ₁` on `a₁'` and acting by the transported
datum `Stacks.Thickenings.localizedDerivation` on `a₂'` give a commutative square:
```
(θ₂ ⬝ a₂') ≫ f' = h' ≫ (θ₁ ⬝ a₁').
```

Both sides are morphisms into the affine scheme `X₁'`, so they are compared on global sections:
the terms coming from `a₁'` and `a₂'` agree because `a₂' ≫ f' = h' ≫ a₁'`, and the terms coming
from the two data agree by `Stacks.Thickenings.localizedDerivation_apply`.

This covers [Stacks Project, Tag 04BY] over affine ambient schemes and affine bases only, so it
does not carry the tag: the unrestricted statement is
`Stacks.Thickenings.derivationActionSheaf_comp_etaleLocalization`, which does. See the
`### No @[stacks 04BY]` section of the implementation notes of this file. -/
theorem derivationAction_comp_etaleLocalization (hi₁ : IsFirstOrderThickening i₁)
    (hi₂ : IsFirstOrderThickening i₂) (hj₁ : IsFirstOrderThickening j₁)
    (hj₂ : IsFirstOrderThickening j₂) (ca₁ : i₁ ≫ a₁' = a₁ ≫ j₁)
    (ca₂ : i₂ ≫ a₂' = a₂ ≫ j₂) (cT : i₂ ≫ h' = h ≫ i₁) (cj : j₂ ≫ f' = f ≫ j₁)
    (cf : a₂ ≫ f = h ≫ a₁) (cA : a₂' ≫ f' = h' ≫ a₁')
    (cS : f ≫ j₁ ≫ p₁ = (j₂ ≫ p₂) ≫ k) :
    letI := appTopAlgebra (j₁ ≫ p₁)
    letI := conormalModuleAlong hi₁ a₁
    letI := appTopAlgebra (j₂ ≫ p₂)
    letI := conormalModuleAlong hi₂ a₂
    ∀ θ₁ : Ω[Γ(X₁, (⊤ : X₁.Opens))⁄Γ(S₁, (⊤ : S₁.Opens))] →ₗ[Γ(X₁, (⊤ : X₁.Opens))]
        RingHom.ker i₁.appTop.hom,
      derivationAction hi₂ ca₂ p₂ (localizedDerivation hi₁ hi₂ hj₁ hj₂ cT cf cS θ₁) ≫ f' =
        h' ≫ derivationAction hi₁ ca₁ p₁ θ₁ := by
  let := appTopAlgebra (j₁ ≫ p₁)
  let := conormalModuleAlong hi₁ a₁
  let := appTopAlgebra (j₂ ≫ p₂)
  let := conormalModuleAlong hi₂ a₂
  intro θ₁
  refine AlgebraicGeometry.ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_))
  rw [← appTop_comp_apply, ← appTop_comp_apply, derivationAction_appTop,
    derivationAction_appTop, map_add, appTop_comm_of_comm cA x, appTop_comm_of_comm cj x,
    localizedDerivation_apply hi₁ hi₂ hj₁ hj₂ cT cf cS]

end Localized

end Stacks.Thickenings

end
