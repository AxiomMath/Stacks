module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationEtaleLocalization

/-!
# Infinitesimal deformations of maps: compatible derivation data in place of étaleness

Consider the commutative diagrams of [Stacks Project, Tag 04BY],
```
(T₂ ⊂ T₂') --(a₂, a₂')--> (X₂ ⊂ X₂')        X₂' --> S₂
   |                          |               |       |
 (h, h')                   (f, f')            v       v
   v                          v              X₁' --> S₁
(T₁ ⊂ T₁') --(a₁, a₁')--> (X₁ ⊂ X₁')
```
but *drop* the assumption that `f : X₂ ⟶ X₁` and `k : S₂ ⟶ S₁` are étale.
[Stacks Project, Tag 04BZ] observes that the conclusion of [Stacks Project, Tag 04BY] still
holds as soon as one is given both data `θ₁ : a₁^*Ω_{X₁/S₁} ⟶ 𝒞_{T₁/T₁'}` and
`θ₂ : a₂^*Ω_{X₂/S₂} ⟶ 𝒞_{T₂/T₂'}` whose associated derivations `D_n = θ_n ∘ d_{X_n/S_n}` of
Equation [Stacks Project, Tag 04BV] make the square
```
f_*𝒪_{X₂} ---f_*D₂---> f_*a_{2,*}𝒞_{T₂/T₂'}
    ^                           ^
   f^♯               induced by (h')^♯
    |                           |
  𝒪_{X₁} -----D₁------> a_{1,*}𝒞_{T₁/T₁'}
```
commute. The étale hypotheses of [Stacks Project, Tag 04BY] serve only to construct such a `θ₂`
from `θ₁`, which is what `Stacks.Thickenings.localizedDerivation` does.

This file proves that statement on global sections over affine ambient schemes, with the action
of [Stacks Project, Tag 0CK1] in its affine form `Stacks.Thickenings.derivationAction`. The
action is in fact available for arbitrary schemes, as
`Stacks.Thickenings.derivationActionSheaf`; the affineness here is a restriction of this
development, not of the library.

## Main results

* `Stacks.Thickenings.derivationAction_comp_of_derivation_comm`: the affine case of
  [Stacks Project, Tag 04BZ]. Two data `θ₁`, `θ₂` whose derivations make the square above
  commute act compatibly with the vertical maps: `(θ₂ ⬝ a₂') ≫ f' = h' ≫ (θ₁ ⬝ a₁')`.
* `Stacks.Thickenings.derivationAction_comp_localizedDerivation`: the affine case of
  [Stacks Project, Tag 04BY] recovered from it, by taking for `θ₂` the étale transport
  `Stacks.Thickenings.localizedDerivation` of `θ₁`.

## Implementation notes

With all ambient schemes affine the objects of the source become rings and modules exactly as in
`Stacks.Thickenings.derivationAction`: `𝒞_{T_n/T_n'}` is the ideal `RingHom.ker i_n.appTop.hom`,
`Ω_{X_n/S_n}` is `Ω[Γ(X_n, ⊤)⁄Γ(S_n, ⊤)]`, and `θ_n` is a `Γ(X_n, ⊤)`-linear map between them.
Since `D_n = θ_n ∘ d_{X_n/S_n}` by Equation [Stacks Project, Tag 04BV], the commuting square of
the source is, on global sections, the single equation
```
θ₂ (d (f^♯ y)) = (h')^♯ (θ₁ (d y))  for all y ∈ Γ(X₁, ⊤)
```
inside `Γ(T₂', ⊤)`, and that is the hypothesis `hθ` below. Both sides are sections of the
defining ideal of `i₂` and of `i₁` respectively, compared after the inclusions into the ambient
global sections, since `(h')^♯` is only a ring map of ambient sections.

The proof is the proof of [Stacks Project, Tag 04BY] with its last step replaced: comparing the
two morphisms into the affine `X₁'` on global sections splits the goal into the term coming from
the lifts `a₁'`, `a₂'`, which agree because `a₂' ≫ f' = h' ≫ a₁'`, and the term coming from the
data, which is `hθ` after `j₂ ≫ f' = f ≫ j₁`. In [Stacks Project, Tag 04BY] that second term is
closed by `Stacks.Thickenings.localizedDerivation_apply`, the defining property of the
transported datum; here it is closed by the hypothesis instead. So étaleness is not weakened to
something else, it is simply not used.

Three hypotheses of [Stacks Project, Tag 04BY] are therefore not needed either, and are omitted
rather than carried unused: the commutativity `i₂ ≫ h' = h ≫ i₁` and `a₂ ≫ f = h ≫ a₁` of the
left-hand squares and the commutativity `f ≫ j₁ ≫ p₁ = (j₂ ≫ p₂) ≫ k` of the square of bases.
They enter [Stacks Project, Tag 04BY] only through the construction of `θ₂`, so the morphisms
`h : T₂ ⟶ T₁` and `k : S₂ ⟶ S₁` themselves disappear from the statement, as do the affineness of
`S₁` and `S₂` and the first-order thickening hypotheses on `j₁` and `j₂`. What remains is the
right-hand half of the diagram: `i₁ ≫ a₁' = a₁ ≫ j₁`, `i₂ ≫ a₂' = a₂ ≫ j₂`,
`j₂ ≫ f' = f ≫ j₁` and `a₂' ≫ f' = h' ≫ a₁'`.

This is the affine case. The remark for arbitrary schemes is proved too, as
`Stacks.Thickenings.derivationActionSheaf_comp_of_derivationSection_comm` in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/InfinitesimalDeformationSheafAction.lean`: there no
scheme is affine, `θ₁` and `θ₂` are morphisms of sheaves of modules, and the two actions of
[Stacks Project, Tag 0CK1] are the constructed `Stacks.Thickenings.derivationActionSheaf`. What
this file keeps is the affine construction `Stacks.Thickenings.derivationAction` of the action,
whose existence half is `Stacks.Thickenings.existsUnique_derivationAction`.

## References

* [Stacks Project, Tag 02H5](https://stacks.math.columbia.edu/tag/02H5)
* [Stacks Project, Tag 04BV](https://stacks.math.columbia.edu/tag/04BV)
* [Stacks Project, Tag 04BY](https://stacks.math.columbia.edu/tag/04BY)
* [Stacks Project, Tag 04BZ](https://stacks.math.columbia.edu/tag/04BZ)
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

/-! ### The compatibility of the actions for given data -/

/-- **Acting by compatible derivation data commutes with the vertical maps**, the affine case of
[Stacks Project, Tag 04BZ]. Let `(h, h')` and `(f, f')` be the vertical maps of a diagram of
first-order thickenings with affine ambient schemes as in [Stacks Project, Tag 04BY], let
`(a₁, a₁')` and `(a₂, a₂')` be morphisms of thickenings compatible with them, and let
`p₁ : X₁' ⟶ S₁` and `p₂ : X₂' ⟶ S₂` be the structure morphisms. Nothing is assumed étale.
Given `Γ(X₁, ⊤)`-linear `θ₁ : Ω[Γ(X₁, ⊤)⁄Γ(S₁, ⊤)] ⟶ 𝒞_{T₁/T₁'}` and `Γ(X₂, ⊤)`-linear
`θ₂ : Ω[Γ(X₂, ⊤)⁄Γ(S₂, ⊤)] ⟶ 𝒞_{T₂/T₂'}` whose derivations `D_n = θ_n ∘ d_{X_n/S_n}` of
Equation [Stacks Project, Tag 04BV] satisfy `D₂ (f^♯ y) = (h')^♯ (D₁ y)` — the commuting square
of the source — acting by `θ₁` on `a₁'` and by `θ₂` on `a₂'` gives a commutative square:
```
(θ₂ ⬝ a₂') ≫ f' = h' ≫ (θ₁ ⬝ a₁').
```

In [Stacks Project, Tag 04BY] the second datum is built from the first out of the étale
hypotheses, and the hypothesis `hθ` here is then its defining property
`Stacks.Thickenings.localizedDerivation_apply`; see
`Stacks.Thickenings.derivationAction_comp_localizedDerivation`. -/
@[stacks 04BZ "affine case, with the two actions of Tag 0CK1 constructed by \
Stacks.Thickenings.derivationAction; the remark for arbitrary schemes is \
Stacks.Thickenings.derivationActionSheaf_comp_of_derivationSection_comm"]
theorem derivationAction_comp_of_derivation_comm [IsAffine T₁'] [IsAffine T₂'] [IsAffine X₁']
    [IsAffine X₂'] (hi₁ : IsFirstOrderThickening i₁) (hi₂ : IsFirstOrderThickening i₂)
    (ca₁ : i₁ ≫ a₁' = a₁ ≫ j₁) (ca₂ : i₂ ≫ a₂' = a₂ ≫ j₂) (cj : j₂ ≫ f' = f ≫ j₁)
    (cA : a₂' ≫ f' = h' ≫ a₁') :
    letI := appTopAlgebra (j₁ ≫ p₁)
    letI := conormalModuleAlong hi₁ a₁
    letI := appTopAlgebra (j₂ ≫ p₂)
    letI := conormalModuleAlong hi₂ a₂
    ∀ (θ₁ : Ω[Γ(X₁, (⊤ : X₁.Opens))⁄Γ(S₁, (⊤ : S₁.Opens))] →ₗ[Γ(X₁, (⊤ : X₁.Opens))]
        RingHom.ker i₁.appTop.hom)
      (θ₂ : Ω[Γ(X₂, (⊤ : X₂.Opens))⁄Γ(S₂, (⊤ : S₂.Opens))] →ₗ[Γ(X₂, (⊤ : X₂.Opens))]
        RingHom.ker i₂.appTop.hom),
      (∀ y : Γ(X₁, (⊤ : X₁.Opens)),
          ((θ₂ (KaehlerDifferential.D _ _ (f.appTop.hom y)) : RingHom.ker i₂.appTop.hom) :
              Γ(T₂', (⊤ : T₂'.Opens)))
            = h'.appTop.hom ((θ₁ (KaehlerDifferential.D _ _ y) : RingHom.ker i₁.appTop.hom) :
              Γ(T₁', (⊤ : T₁'.Opens)))) →
        derivationAction hi₂ ca₂ p₂ θ₂ ≫ f' = h' ≫ derivationAction hi₁ ca₁ p₁ θ₁ := by
  let := appTopAlgebra (j₁ ≫ p₁)
  let := conormalModuleAlong hi₁ a₁
  let := appTopAlgebra (j₂ ≫ p₂)
  let := conormalModuleAlong hi₂ a₂
  intro θ₁ θ₂ hθ
  refine AlgebraicGeometry.ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_))
  rw [← appTop_comp_apply, ← appTop_comp_apply, derivationAction_appTop,
    derivationAction_appTop, map_add, appTop_comm_of_comm cA x, appTop_comm_of_comm cj x, hθ]

/-- **The étale localization of [Stacks Project, Tag 04BY] is the case of a transported datum.**
Taking for `θ₂` the étale transport `Stacks.Thickenings.localizedDerivation` of `θ₁` and
discharging the commuting square of [Stacks Project, Tag 04BZ] by its defining property
`Stacks.Thickenings.localizedDerivation_apply` recovers the affine case of
[Stacks Project, Tag 04BY], which is proved directly in
`Stacks.Thickenings.derivationAction_comp_etaleLocalization`. The tag itself is carried by the
unrestricted `Stacks.Thickenings.derivationActionSheaf_comp_etaleLocalization`. -/
theorem derivationAction_comp_localizedDerivation [IsAffine S₁] [IsAffine S₂] [IsAffine T₁']
    [IsAffine T₂'] [IsAffine X₁'] [IsAffine X₂'] [AlgebraicGeometry.Etale f]
    [AlgebraicGeometry.Etale k] (hi₁ : IsFirstOrderThickening i₁)
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
  exact derivationAction_comp_of_derivation_comm hi₁ hi₂ ca₁ ca₂ cj cA θ₁
    (localizedDerivation hi₁ hi₂ hj₁ hj₂ cT cf cS θ₁)
    (localizedDerivation_apply hi₁ hi₂ hj₁ hj₂ cT cf cS θ₁)

end Stacks.Thickenings

end
