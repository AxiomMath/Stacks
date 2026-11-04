module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Affine
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.ModulesOverOpen
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.PushforwardStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.PullbackSections.SpecStalkSections
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Stalk

/-!
# Degree-zero flat base change along the spectrum of a local ring of the base

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes, let `ℱ` be a
quasi-coherent `𝒪_X`-module, let `y` be a point of `Y` and let

  `X' = X ×_Y Spec 𝒪_{Y,y}`

be the base change of `f` along the canonical morphism `c : Spec 𝒪_{Y,y} ⟶ Y`, which is flat.
This file proves that the canonical comparison

  `Γ(X', (g')^* ℱ) ≅ (f_* ℱ)_y`,  `g' : X' ⟶ X` the first projection,

is an isomorphism of `𝒪_{Y,y}`-modules, carrying the pullback along `g'` of a section of `ℱ`
over `f ⁻¹ᵁ U` to its germ at `y`.

This is the reduction of a general base to the local ring `𝒪_{Y,y}` that the first paragraph of
the proof of [Stacks, Tag 0D2M] performs, in degree zero: it is what turns a statement about
`H ⁰(X', (g')^* ℱ)` over the local base into one about the stalk `(f_* ℱ)_y` over `Y`, which is
the shape clause (2) of that tag — the surjectivity of
`f_*(ℱ ⊗ ℒ ^⊗ d)_y ⟶ H ⁰(X_y, ℱ_y ⊗ ℒ_y ^⊗ d)` — is stated in, and the only clause
[Stacks, Tag 0D2N] consumes.

## Main results

* `Stacks.AlgebraicGeometry.FlatBaseChange.exists_linearEquiv_trans_of_normalisation`:
  transport of a linear equivalence normalised on a family of elements along another such.
* `Stacks.AlgebraicGeometry.FlatBaseChange.exists_linearEquiv_pushforwardStalk_stalkBaseChange`:
  **the reduction.** The comparison above, together with the normalisation that identifies it.

## The route

The whole statement is a composition of results available in the library, and the composition
is the content.

* Flat base change for the direct image in degree zero over an arbitrary base is
  `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat`, the
  fragment of [Stacks, Tag 02KH] already registered for part (1) at `i = 0` over an arbitrary
  base for the canonical morphism. Applied at the cartesian square of `c`, flat by
  `AlgebraicGeometry.flat_fromSpecStalk`, with `f_* ℱ` quasi-coherent by
  `isQuasicoherent_pushforward_of_qcqs`, it makes `c^* f_* ℱ ⟶ f'_* (g')^* ℱ` invertible; read
  over `⊤` — where the sections of a direct image are the sections upstairs — it is the
  comparison of the two groups wanted.
* The identification of `Γ(Spec 𝒪_{Y,y}, c^* 𝒢)` with `𝒢_y` for quasi-coherent `𝒢` on `Y` is
  `AlgebraicGeometry.exists_fromSpecStalkSectionsStalkLinearEquiv`, applied at `𝒢 = f_* ℱ`.
* The step that was missing is the **normalisation over an arbitrary open of the base**. The
  germ at `y` is a colimit over the neighbourhoods of `y`, so the comparison has to be known on
  the pullback of a section over `f ⁻¹ᵁ U` for a small `U`; on `main` the normalisation of
  `AffinePushforward.baseChangeNatTrans` existed only over the whole space, as
  `baseChangeNatTrans_app_top_pullbackUnitSections`. It is now generalised in place, in
  `../FlatBaseChangeCohomology/AffineDegreeZero/Modules.lean`, to
  `pushforwardSquareIso_hom_app_app`, `baseChangeNatTrans_app_pullbackUnitSections` and the
  `appLE` form `baseChangeNatTrans_app_pullbackSection`, with the two `_top` statements kept.

## What this file does not do, and no attribute

**No `@[stacks 02KH]` attribute is attached, and none is owed.** Tag 02KH already carries
attributes on six fragments, and the fragment this file composes — part (1) at `i = 0` over an
arbitrary base for the canonical morphism — is one of them, at
`../FlatBaseChangeCohomology/AffineDegreeZero/Modules.lean`. What is here is a *specialisation*
of it, at the one flat morphism `Spec 𝒪_{Y,y} ⟶ Y`, in the shape the reduction consumes; a
specialisation of an already-registered fragment earns no attribute, and the audit scanner
matches the bare four characters of a tag and treats a suffix as free text, so a seventh site
would report the whole tag formalized off a special case. The reason is recorded at length in
`../PullbackSections/Qcqs.lean`.

**Positive degrees are not treated.** The general statement of part (1) is about the higher
direct images `R ⁱ f_*`, and `../FlatPullbackStalk/Basic.lean` records that its content in
positive degrees lies entirely in the non-affine case. That case is reachable from available
material — quasi-coherence of `R ᵖ f_*` in every degree is [Stacks, Tag 01XJ]
(`Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_higherDirectImage`), the
identification over an affine base is [Stacks, Tag 01XK]
(`sectionsRightDerivedPushforwardIso`), locality on the target is [Stacks, Tag 01E5]
(`AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictObjIso`), and part (2) in
every degree is `AlgebraicGeometry.nonempty_cohomologyBaseChangeIso` — but that last holds for
`f` **separated** and quasi-compact rather than quasi-separated, so the route would still not
state the tag, and [Stacks, Tag 0D2N] does not use positive degrees at all. It is recorded here
for whoever completes 02KH rather than pursued.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.FlatBaseChange

variable {X Y : Scheme.{u}}

/-- **Transporting a normalised linear equivalence along another.**  If `eβ : M ≃ₗ[R] N` carries
a family `p` of elements of `M` to a family `q` of elements of `N`, then a linear equivalence
`M ≃ₗ[R] P` normalised by `p i ↦ g i` becomes one `N ≃ₗ[R] P` normalised by `q i ↦ g i`.

It is stated at abstract modules on purpose.  At the scalar structures its application below
carries — restrictions of scalars supplied as `letI`s — the coercion of a `≃ₗ` to a function is
not synthesised, so a composite cannot be applied to an argument there;  here the instances are
ordinary ones and it can, and the application only has to match an already elaborated
statement. -/
theorem exists_linearEquiv_trans_of_normalisation {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    {ι : Type*} (eβ : M ≃ₗ[R] N) (p : ι → M) (q : ι → N) (hq : ∀ i, eβ (p i) = q i)
    (g : ι → P) (h : ∃ e : M ≃ₗ[R] P, ∀ i, e (p i) = g i) :
    ∃ e : N ≃ₗ[R] P, ∀ i, e (q i) = g i := by
  obtain ⟨e, he⟩ := h
  refine ⟨eβ.symm.trans e, fun i => ?_⟩
  rw [LinearEquiv.trans_apply, ← hq i, eβ.symm_apply_apply, he i]

/-- **Degree-zero flat base change along `Spec 𝒪_{Y,y} ⟶ Y`, in the shape the reduction to a
local base consumes.**  For `f : X ⟶ Y` quasi-compact and quasi-separated, `ℱ` a quasi-coherent
`𝒪_X`-module and `y` a point of `Y` lying in an affine open `U₀`, there is an `𝒪_{Y,y}`-linear
isomorphism

  `Γ(X ×_Y Spec 𝒪_{Y,y}, (g')^* ℱ) ≅ (f_* ℱ)_y`

carrying the pullback along the first projection of a section of `ℱ` over `f ⁻¹ᵁ U₀` to its germ
at `y`.  The normalisation is what makes this usable: it identifies the isomorphism as the
canonical comparison rather than as some isomorphism of the two sides, and it is how a statement
proved over the local base `Spec 𝒪_{Y,y}` is transported to the stalk over `Y` — the first
paragraph of the proof of [Stacks, Tag 0D2M], in degree zero.

The left-hand side is written as the sections of the direct image along the second projection,
which is the same group as the global sections on the base change, because that is the spelling
in which the `𝒪_{Y,y}`-action is found by instance search.

This is the specialisation of [Stacks, Tag 02KH] part (1) at `i = 0`
(`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat`) at the
flat morphism `AlgebraicGeometry.Scheme.fromSpecStalk`; no `@[stacks]` attribute is attached,
for the reason in the module docstring. -/
theorem exists_linearEquiv_pushforwardStalk_stalkBaseChange
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (y : Y) {U₀ : Y.Opens} (hU₀ : IsAffineOpen U₀) (hy₀ : y ∈ U₀) :
    letI := AlgebraicGeometry.specStalkAppTopModule y
      ((Scheme.Modules.pushforward (pullback.snd f (Y.fromSpecStalk y))).obj
        ((Scheme.Modules.pullback (pullback.fst f (Y.fromSpecStalk y))).obj ℱ))
    letI : Module (Y.presheaf.stalk y)
        (((Scheme.Modules.pushforward f).obj ℱ).presheaf.stalk y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Y.presheaf) ((Scheme.Modules.pushforward f).obj ℱ).val y
    ∃ e : Γ((Scheme.Modules.pushforward (pullback.snd f (Y.fromSpecStalk y))).obj
          ((Scheme.Modules.pullback (pullback.fst f (Y.fromSpecStalk y))).obj ℱ), ⊤)
        ≃ₗ[Y.presheaf.stalk y] ((Scheme.Modules.pushforward f).obj ℱ).presheaf.stalk y,
      ∀ a : Γ((Scheme.Modules.pushforward f).obj ℱ, U₀),
        e (Scheme.Modules.pullbackSection (pullback.fst f (Y.fromSpecStalk y)) ℱ (f ⁻¹ᵁ U₀)
            (pullback.snd f (Y.fromSpecStalk y) ⁻¹ᵁ ⊤)
            (Stacks.FormalFunctions.top_le_preimage_pullbackFst f y U₀ hy₀) a) =
          ((Scheme.Modules.pushforward f).obj ℱ).presheaf.germ U₀ y hy₀ a := by
  let := AlgebraicGeometry.specStalkAppTopModule y
    ((Scheme.Modules.pushforward (pullback.snd f (Y.fromSpecStalk y))).obj
      ((Scheme.Modules.pullback (pullback.fst f (Y.fromSpecStalk y))).obj ℱ))
  let : Module (Y.presheaf.stalk y)
      (((Scheme.Modules.pushforward f).obj ℱ).presheaf.stalk y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) ((Scheme.Modules.pushforward f).obj ℱ).val y
  have : ((Scheme.Modules.pushforward f).obj ℱ).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_qcqs f ℱ
  have : Flat (Y.fromSpecStalk y) := AlgebraicGeometry.flat_fromSpecStalk Y y
  have H : IsPullback (pullback.fst f (Y.fromSpecStalk y))
      (pullback.snd f (Y.fromSpecStalk y)) f (Y.fromSpecStalk y) :=
    IsPullback.of_hasPullback f (Y.fromSpecStalk y)
  have : IsIso ((AffinePushforward.baseChangeNatTrans H.w).app ℱ) :=
    FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat H ℱ
  have : IsIso (Scheme.Modules.Hom.app ((AffinePushforward.baseChangeNatTrans H.w).app ℱ)
      (⊤ : (Spec (Y.presheaf.stalk y)).Opens)) :=
    Scheme.Modules.Hom.isIso_iff_isIso_app.mp inferInstance ⊤
  let lβ : Γ((Scheme.Modules.pullback (Y.fromSpecStalk y)).obj
        ((Scheme.Modules.pushforward f).obj ℱ), ⊤) →ₗ[Y.presheaf.stalk y]
      Γ((Scheme.Modules.pushforward (pullback.snd f (Y.fromSpecStalk y))).obj
        ((Scheme.Modules.pullback (pullback.fst f (Y.fromSpecStalk y))).obj ℱ), ⊤) :=
    { toFun := (Scheme.Modules.Hom.app ((AffinePushforward.baseChangeNatTrans H.w).app ℱ)
        (⊤ : (Spec (Y.presheaf.stalk y)).Opens)).hom
      map_add' := fun z w => map_add _ z w
      map_smul' := fun r z => Scheme.Modules.Hom.app_smul _ _ z }
  have hpre : pullback.snd f (Y.fromSpecStalk y) ⁻¹ᵁ (Y.fromSpecStalk y ⁻¹ᵁ U₀) ≤
      pullback.fst f (Y.fromSpecStalk y) ⁻¹ᵁ (f ⁻¹ᵁ U₀) := by
    intro z hz
    have hz' : ((pullback.snd f (Y.fromSpecStalk y) ≫ Y.fromSpecStalk y).base z) ∈ U₀ := hz
    rwa [← Limits.pullback.condition] at hz'
  exact exists_linearEquiv_trans_of_normalisation
    (LinearEquiv.ofBijective lβ (ConcreteCategory.bijective_of_isIso
      (Scheme.Modules.Hom.app ((AffinePushforward.baseChangeNatTrans H.w).app ℱ)
        (⊤ : (Spec (Y.presheaf.stalk y)).Opens))))
    (fun a => Scheme.Modules.pullbackSection (Y.fromSpecStalk y)
      ((Scheme.Modules.pushforward f).obj ℱ) U₀ ⊤
      (AlgebraicGeometry.le_preimage_fromSpecStalk_of_mem y U₀ hy₀) a)
    (fun a => Scheme.Modules.pullbackSection (pullback.fst f (Y.fromSpecStalk y)) ℱ (f ⁻¹ᵁ U₀)
      (pullback.snd f (Y.fromSpecStalk y) ⁻¹ᵁ ⊤)
      (Stacks.FormalFunctions.top_le_preimage_pullbackFst f y U₀ hy₀) a)
    (fun a => FlatBaseChangeCohomology.baseChangeNatTrans_app_pullbackSection H.w ℱ U₀ ⊤
      (AlgebraicGeometry.le_preimage_fromSpecStalk_of_mem y U₀ hy₀) hpre
      (Stacks.FormalFunctions.top_le_preimage_pullbackFst f y U₀ hy₀) a)
    (fun a => ((Scheme.Modules.pushforward f).obj ℱ).presheaf.germ U₀ y hy₀ a)
    (AlgebraicGeometry.exists_fromSpecStalkSectionsStalkLinearEquiv
      ((Scheme.Modules.pushforward f).obj ℱ) y hU₀ hy₀)

end Stacks.AlgebraicGeometry.FlatBaseChange

end
