module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.Affine

/-!
# Two out of three for quasi-coherence in a short exact sequence

Let `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` be a short exact sequence of `𝒪_X`-modules on an affine scheme
`X = Spec R`. If two of the three terms are quasi-coherent then so is the third. This is
[Stacks, Tag 01IE].

The two outer cases are formal: `F₁` is the kernel of `F₂ ⟶ F₃` and `F₃` is the cokernel of
`F₁ ⟶ F₂`, and kernels and cokernels of morphisms of quasi-coherent modules are quasi-coherent
([Stacks, Tag 01IC]).

The middle case uses the vanishing of `H¹` of a quasi-coherent module on an affine,
[Stacks, Tag 01XB], in the form `Stacks.CechElementChase.epi_secF_map_g`:

* global sections on `Spec R` are exact on the sequence, the only non-formal point being
  surjectivity of `Γ(F₂) ⟶ Γ(F₃)`, which is the `H¹`-vanishing for the quasi-coherent `F₁`;
* `M ↦ M̃` is exact (`AlgebraicGeometry.tilde.preservesFiniteLimits` together with its
  left-adjointness), so the sequence of `R`-modules `0 ⟶ Γ(F₁) ⟶ Γ(F₂) ⟶ Γ(F₃) ⟶ 0` gives a
  short exact sequence of sheaves `0 ⟶ Γ(F₁)̃ ⟶ Γ(F₂)̃ ⟶ Γ(F₃)̃ ⟶ 0`;
* the counit `Γ(F)̃ ⟶ F` of the tilde–sections adjunction is a morphism of short exact
  sequences which is invertible at `F₁` and at `F₃`, because a module on `Spec R` is
  quasi-coherent exactly when that counit is invertible there; so it is invertible at `F₂` by
  the five lemma, which is the content of
  `CategoryTheory.ShortComplex.isIso₂_of_shortExact_of_isIso₁₃'`.

The last section globalizes the middle case to an arbitrary scheme: quasi-coherence is local,
restriction along an open immersion is exact, and every affine open is the image of an open
immersion from a spectrum.

## Main results

* `Stacks.AlgebraicGeometry.QcohExtension.surjective_app_of_shortExact`: for a short exact
  sequence of `𝒪_X`-modules whose first term is quasi-coherent, `Γ(U, -)` is surjective on the
  last map over an affine open `U`. No hypothesis on the other two terms.
* `Stacks.AlgebraicGeometry.QcohExtension.shortExact_map_moduleSpecΓFunctor`: the induced
  sequence of `R`-modules of global sections on `Spec R` is short exact.
* `Stacks.AlgebraicGeometry.QcohExtension.isQuasicoherent_X₂_of_shortExact_spec`,
  `isQuasicoherent_X₁_of_shortExact_spec`, `isQuasicoherent_X₃_of_shortExact_spec`:
  **[Stacks, Tag 01IE]**, the three cases of two out of three on `Spec R`.
* `Stacks.AlgebraicGeometry.QcohExtension.isQuasicoherent_X₂_of_shortExact`: the middle case on
  an arbitrary scheme.

## Implementation notes

`AlgebraicGeometry.moduleSpecΓFunctor`, global sections on `Spec R` valued in `R`-modules, is
the right adjoint of `AlgebraicGeometry.tilde.functor`, which gives it preservation of finite
limits; its additivity is not found by instance search and is installed here from preservation
of binary products, for which
`CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts` has to be a local
instance.

The epimorphism half of `shortExact_map_moduleSpecΓFunctor` crosses from `AddCommGrpCat`, where
[Stacks, Tag 01EU] delivers it, to `ModuleCat R`. No comparison is needed: both
`ModuleCat.epi_iff_surjective` and `AddCommGrpCat.epi_iff_surjective` unfold to surjectivity of
one and the same function `S.g.val.app (op ⊤)`.

Two short complexes that differ only by the associativity of functor composition —
`S.map (F ⋙ G)` and `(S.map F).map G` — are definitionally equal but not syntactically so, and
unifying them is expensive enough to exhaust the heartbeat budget. Everything below is therefore
written with the iterated form `(S.map F).map G`, and the field `mono_f` of the resulting
`ShortExact` is supplied by hand rather than by its autoparameter, which would otherwise look
for `Mono ((S.map F).map G).f` and not find the proof of `Mono (G.map (S.map F).f)`.

## References

* [Stacks Project, Tag 01IE](https://stacks.math.columbia.edu/tag/01IE)
* [Stacks Project, Tag 01IC](https://stacks.math.columbia.edu/tag/01IC)
* [Stacks Project, Tag 01EU](https://stacks.math.columbia.edu/tag/01EU)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.QcohExtension

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts

/-! ### Sections over an affine open -/

/-- **Global sections over an affine open are surjective on the last map of a short exact
sequence whose first term is quasi-coherent.** This is [Stacks, Tag 01EU] fed with the Čech
vanishing of [Stacks, Tag 01XB] for the quasi-coherent first term; neither of the other two terms
is assumed quasi-coherent. -/
theorem surjective_app_of_shortExact {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (h₁ : S.X₁.IsQuasicoherent) (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (S.g.val.app (op U)) :=
  let := h₁
  (AddCommGrpCat.epi_iff_surjective _).1
    (Stacks.CechElementChase.epi_secF_map_g X.ringCatSheaf S hS
      (Stacks.SectionEpiAffine.hasVanishingHigherCech_standardCovers X S.X₁) U
      (Stacks.SectionEpiAffine.exists_standardCover_refines X U hU))

/-- A finite-limit-preserving additive functor sends a short exact sequence to a short exact
sequence as soon as it preserves the epimorphism `S.g`. -/
private theorem shortExact_map_of_preservesFiniteLimits {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (S : ShortComplex C) (hS : S.ShortExact) (hg : Epi (F.map S.g)) : (S.map F).ShortExact :=
  let hL := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono F).1 inferInstance S hS
  { exact := hL.1, mono_f := hL.2, epi_g := hg }

/-! ### Global sections on a spectrum -/

section Spec

variable {R : CommRingCat.{u}}

/-- Global sections on `Spec R`, valued in `R`-modules, is the right adjoint of `M ↦ M̃`. -/
instance isRightAdjoint_moduleSpecΓFunctor : (moduleSpecΓFunctor (R := R)).IsRightAdjoint :=
  ⟨_, ⟨tilde.adjunction⟩⟩

/-- Global sections on `Spec R` is additive: it preserves finite limits, hence binary products,
hence binary biproducts. -/
instance additive_moduleSpecΓFunctor : (moduleSpecΓFunctor (R := R)).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

/-- **Global sections on `Spec R` carry a short exact sequence with quasi-coherent first term to
a short exact sequence of `R`-modules.** Left exactness is adjointness and the surjectivity is
`surjective_app_of_shortExact` at the affine open `⊤`. -/
theorem shortExact_map_moduleSpecΓFunctor (S : ShortComplex (Spec R).Modules)
    (hS : S.ShortExact) (h₁ : S.X₁.IsQuasicoherent) :
    (S.map (moduleSpecΓFunctor (R := R))).ShortExact := by
  refine shortExact_map_of_preservesFiniteLimits _ S hS ((ModuleCat.epi_iff_surjective _).2 ?_)
  exact surjective_app_of_shortExact S hS h₁ ⊤ (isAffineOpen_top _)

/-- **[Stacks, Tag 01IE], the extension case.** If the two outer terms of a short exact sequence
of `𝒪_{Spec R}`-modules are quasi-coherent then so is the middle one. -/
@[stacks 01IE, ega "III 1.4.17" "affine case"]
theorem isQuasicoherent_X₂_of_shortExact_spec (S : ShortComplex (Spec R).Modules)
    (hS : S.ShortExact) (h₁ : S.X₁.IsQuasicoherent) (h₃ : S.X₃.IsQuasicoherent) :
    S.X₂.IsQuasicoherent := by
  have hΓ := shortExact_map_moduleSpecΓFunctor S hS h₁
  have := hΓ.epi_g
  have hT : ((S.map (moduleSpecΓFunctor (R := R))).map (tilde.functor R)).ShortExact :=
    shortExact_map_of_preservesFiniteLimits _ _ hΓ inferInstance
  let φ : (S.map (moduleSpecΓFunctor (R := R))).map (tilde.functor R) ⟶ S :=
    { τ₁ := Scheme.Modules.fromTildeΓ S.X₁
      τ₂ := Scheme.Modules.fromTildeΓ S.X₂
      τ₃ := Scheme.Modules.fromTildeΓ S.X₃
      comm₁₂ := ((Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality S.f).symm
      comm₂₃ := ((Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality S.g).symm }
  rw [isQuasicoherent_iff_isIso_fromTildeΓ]
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃' φ hT hS
    ((isQuasicoherent_iff_isIso_fromTildeΓ _).1 h₁)
    ((isQuasicoherent_iff_isIso_fromTildeΓ _).1 h₃)

/-- **[Stacks, Tag 01IE], the kernel case.** If the last two terms of a short exact sequence of
`𝒪_{Spec R}`-modules are quasi-coherent then so is the first: it is the kernel of the last
map. -/
@[stacks 01IE]
theorem isQuasicoherent_X₁_of_shortExact_spec (S : ShortComplex (Spec R).Modules)
    (hS : S.ShortExact) (h₂ : S.X₂.IsQuasicoherent) (h₃ : S.X₃.IsQuasicoherent) :
    S.X₁.IsQuasicoherent :=
  let := h₂
  let := h₃
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (IsLimit.conePointUniqueUpToIso (limit.isLimit _) hS.fIsKernel)
    (Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel S.g)

/-- **[Stacks, Tag 01IE], the cokernel case.** If the first two terms of a short exact sequence
of `𝒪_{Spec R}`-modules are quasi-coherent then so is the last: it is the cokernel of the first
map, and [Stacks, Tag 01IC] applies because `Spec R` is affine. -/
@[stacks 01IE]
theorem isQuasicoherent_X₃_of_shortExact_spec (S : ShortComplex (Spec R).Modules)
    (hS : S.ShortExact) (h₁ : S.X₁.IsQuasicoherent) (h₂ : S.X₂.IsQuasicoherent) :
    S.X₃.IsQuasicoherent :=
  let := h₁
  let := h₂
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hS.gIsCokernel)
    (Scheme.Modules.isQuasicoherent_cokernel S.f)

end Spec

/-! ### The extension case on an arbitrary scheme -/

/-- **An extension of quasi-coherent modules on an arbitrary scheme is quasi-coherent.** This is
the global form of the extension case of [Stacks, Tag 01IE]. -/
theorem isQuasicoherent_X₂_of_shortExact {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (h₁ : S.X₁.IsQuasicoherent) (h₃ : S.X₃.IsQuasicoherent) :
    S.X₂.IsQuasicoherent := by
  have := h₁
  have := h₃
  refine QuasicoherentColimits.isQuasicoherent_of_restrict_affineOpens _ fun V ↦ ?_
  obtain ⟨U, hU'⟩ := V
  have hU : IsAffineOpen U := hU'
  have hexact : PreservesFiniteLimits (Scheme.Modules.restrictFunctor hU.fromSpec) :=
    _root_.AlgebraicGeometry.Modules.preservesFiniteLimits_restrictFunctor hU.fromSpec
  have hadd : (Scheme.Modules.restrictFunctor hU.fromSpec).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  have := hS.epi_g
  have hSpec : (S.map (Scheme.Modules.restrictFunctor hU.fromSpec)).ShortExact :=
    shortExact_map_of_preservesFiniteLimits _ S hS (Functor.map_epi _ S.g)
  have h1 : (S.X₂.restrict hU.fromSpec).IsQuasicoherent :=
    isQuasicoherent_X₂_of_shortExact_spec _ hSpec
      (Scheme.Modules.isQuasicoherent_restrictFunctor hU.fromSpec S.X₁)
      (Scheme.Modules.isQuasicoherent_restrictFunctor hU.fromSpec S.X₃)
  have := h1
  have h2 : ((S.X₂.restrict hU.fromSpec).restrict hU.isoSpec.hom).IsQuasicoherent :=
    inferInstance
  have iso : (S.X₂.restrict hU.fromSpec).restrict hU.isoSpec.hom ≅ S.X₂.restrict U.ι :=
    ((Scheme.Modules.restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app S.X₂).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec).app S.X₂
  exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso iso h2

end Stacks.AlgebraicGeometry.QcohExtension

end
