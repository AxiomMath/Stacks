module

public import StacksFrontier.AlgebraicGeometry.Duality.DualizingBaseChange.MakeshiftBaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexCoverCriterion
public import StacksFrontier.RingTheory.Dualizing.IsDualizingComplexModels
public import StacksFrontier.RingTheory.Dualizing.LocalizationTransport
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift

/-!
# A normalized dualizing model on an affine scheme with local ring of global sections

Let `S` be an affine locally Noetherian scheme whose ring of global sections `A = Γ(S, ⊤)` is
local, and suppose `A` has a dualizing complex ([Stacks, Tag 0A7I]). Then there is a complex
`ω_A^•` over `A` which is a *normalized* dualizing complex in the sense of
`Dualizing.IsNormalizedDualizingComplex` ([Stacks, Tag 0AX1]), together with a complex `ω_S^•` of
`𝒪_S`-modules with quasi-coherent cohomology which `ω_A^•` models on `⊤` in the sense of
`Stacks.Duality.IsTildeModelOnAnyModel`.

This is the input the statements of
`StacksFrontier/AlgebraicGeometry/Duality/SurfaceDualizingDegree/NormalizedUpperShriek.lean` ask for.
They take the *normalized* complex over the global sections of the base together with its sheaf
model, whereas [Stacks, Tag 0AXD] and its neighbours hypothesise only that the local ring `A`
itself has a dualizing complex. The two are joined here, so that no consumer has to carry a
normalization hypothesis of its own.

There are two steps, and neither normalizes anything on the `A` side of the `Γ`–`Spec`
adjunction.

1. Over the Noetherian local ring `Γ(S, ⊤)` every dualizing complex becomes normalized after one
   shift, which is `Dualizing.exists_isNormalizedDualizingComplex_shift` ([Stacks, Tag 0A7L]
   read through [Stacks, Tag 0AX1]); the shift is unique, by
   `Dualizing.isNormalizedDualizingComplex_shift_iff_eq`, but uniqueness is not needed.
2. A complex over `Γ(S, ⊤)` is modelled on `⊤` by the complex of sheaves obtained by sheafifying
   it over `Spec Γ(S, ⊤)` and carrying the result to `S` along `S ≅ ⊤ ≅ Spec Γ(S, ⊤)`. That is
   `Stacks.Duality.topTildeComplex` below.

So the transport across `AlgebraicGeometry.Scheme.ΓSpecIso` is needed only for the *unnormalized*
statement `Dualizing.IsDualizingComplex`, where `Dualizing.isDualizingComplex_of_ringEquiv`
([Stacks, Tag 0A7G] for an isomorphism) already provides it. That is what
`Stacks.Duality.exists_isNormalizedDualizingComplex_isTildeModelOnAnyModel_spec` does, in the
shape `Spec A` with `A` a Noetherian local ring, which is the shape of [Stacks, Tag 0AXD].

## Main definitions

* `Stacks.Duality.topTildeComplex` — the complex of `𝒪_S`-modules associated with a complex over
  `Γ(S, ⊤)` on an affine scheme `S`: sheafify over `Spec Γ(S, ⊤)`, restrict along
  `⊤ ≅ Spec Γ(S, ⊤)` and then along `S ≅ ⊤`.

## Main results

* `Stacks.Duality.isTildeModelOnAnyModel_topTildeComplex` — `ω` models
  `Stacks.Duality.topTildeComplex ω` on `⊤`.
* `Stacks.Duality.exists_isNormalizedDualizingComplex_isTildeModelOnAnyModel_top` — from a
  dualizing complex over `Γ(S, ⊤)`, a normalized one together with its sheaf model.
* `Stacks.Duality.exists_isNormalizedDualizingComplex_isTildeModelOnAnyModel_spec` — the same on
  `Spec A` from the bare hypothesis that the Noetherian local ring `A` has a dualizing complex.

## Implementation notes

`D(𝒪_S)` is a free `CategoryTheory.HasDerivedCategory` binder, so the results can be read at the
locally small model, which is where `Stacks.Duality.quasiCoherentDerivedCategory` and the twisted
inverse image live. The model of `D(A)` in which the caller's dualizing complex over `A` is given
is a free binder too, `Dualizing.exists_isDualizingComplex_iff_of_models` moving the hypothesis
between models. The derived category of `Γ(S, ⊤)`-modules, on the other hand, must be the
standard model: that is the one baked into `Dualizing.IsNormalizedDualizingComplex` and into the
model `Stacks.Duality.IsTildeModelOnAnyModel` compares against. It is installed by removing the
locally small instance for modules over a ring, rather than by raising the priority of
`CategoryTheory.HasDerivedCategory.standard`, which would also displace the locally small model
of `D(𝒪_S)`.

The quasi-coherence of the cohomology sheaves of `Stacks.Duality.topTildeComplex ω` is read off
the model rather than computed: a complex carrying a dualizing model on an affine open cover has
quasi-coherent cohomology, by
`Stacks.Duality.isQuasicoherent_homology_of_hasDualizingModelOn_cover`, and `⊤` alone covers.

## References

* [Stacks Project, Tag 0A7I](https://stacks.math.columbia.edu/tag/0A7I)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0A7L](https://stacks.math.columbia.edu/tag/0A7L)
* [Stacks Project, Tag 0AX1](https://stacks.math.columbia.edu/tag/0AX1)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0AXD](https://stacks.math.columbia.edu/tag/0AXD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe w w' u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Duality

variable {S : Scheme.{u}} [IsAffine S] [HasDerivedCategory.{w} S.Modules]

/-- **The complex of sheaves on an affine scheme associated with a complex over its global
sections.** Sheafify `ω ∈ D(Γ(S, ⊤))` over `Spec Γ(S, ⊤)`, restrict the result to `⊤` along
`⊤ ≅ Spec Γ(S, ⊤)` and then to `S` along the isomorphism `S ≅ ⊤`.

The first two steps are exactly the right-hand side of `Stacks.Duality.IsTildeModelOnAnyModel`,
which is why `ω` models this complex on `⊤`
(`Stacks.Duality.isTildeModelOnAnyModel_topTildeComplex`). -/
def topTildeComplex (ω : DerivedCategory (ModuleCat.{u} Γ(S, ⊤))) : DerivedCategory S.Modules :=
  ((tilde.functor Γ(S, ⊤) ⋙
      Scheme.Modules.restrictFunctor (isAffineOpen_top S).isoSpec.hom) ⋙
    Scheme.Modules.restrictFunctor (Scheme.topIso S).inv).mapDerivedCategory.obj ω

/-- **A complex over `Γ(S, ⊤)` models its own sheafification on `⊤`.** Restricting
`Stacks.Duality.topTildeComplex ω` back to `⊤` undoes the last of the three steps defining it,
because restriction along `S ≅ ⊤` followed by restriction along `⊤ ≅ S` is the identity. -/
theorem isTildeModelOnAnyModel_topTildeComplex
    (ω : DerivedCategory (ModuleCat.{u} Γ(S, ⊤))) :
    IsTildeModelOnAnyModel (topTildeComplex ω) ⊤ (isAffineOpen_top S) ω := by
  let := HasDerivedCategory.standard (⊤ : S.Opens).toScheme.Modules
  have h : (⊤ : S.Opens).ι ≫ (Scheme.topIso S).inv = 𝟙 _ := (Scheme.topIso S).hom_inv_id
  have e : ((tilde.functor Γ(S, ⊤) ⋙
        Scheme.Modules.restrictFunctor (isAffineOpen_top S).isoSpec.hom) ⋙
        Scheme.Modules.restrictFunctor (Scheme.topIso S).inv) ⋙
        Scheme.Modules.restrictFunctor (⊤ : S.Opens).ι ≅
      tilde.functor Γ(S, ⊤) ⋙
        Scheme.Modules.restrictFunctor (isAffineOpen_top S).isoSpec.hom :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        ((Scheme.Modules.restrictFunctorComp (⊤ : S.Opens).ι (Scheme.topIso S).inv).symm ≪≫
          Scheme.Modules.restrictFunctorCongr h ≪≫ Scheme.Modules.restrictFunctorId) ≪≫
      Functor.rightUnitor _
  exact ⟨(Functor.mapDerivedCategoryCompIso e).app ω⟩

/-- **A normalized dualizing complex over the global sections of an affine base, with its sheaf
model.** Let `S` be affine and locally Noetherian with `Γ(S, ⊤)` local, and let `ω₀` be a
dualizing complex over `Γ(S, ⊤)`. Then some shift of `ω₀` is a normalized dualizing complex, and
it models a complex of `𝒪_S`-modules with quasi-coherent cohomology on `⊤`.

The shift is `Dualizing.exists_isNormalizedDualizingComplex_shift`; the model is
`Stacks.Duality.topTildeComplex`; and the cohomology of the latter is quasi-coherent because the
model is a dualizing model and `⊤` is an affine open cover of `S`. -/
theorem exists_isNormalizedDualizingComplex_isTildeModelOnAnyModel_top [IsLocallyNoetherian S]
    [IsNoetherianRing Γ(S, ⊤)] [IsLocalRing Γ(S, ⊤)]
    (ω₀ : DerivedCategory (ModuleCat.{u} Γ(S, ⊤)))
    (hω₀ : Dualizing.IsDualizingComplex ω₀) :
    ∃ (ωS : quasiCoherentDerivedCategory S) (ω : DerivedCategory (ModuleCat.{u} Γ(S, ⊤))),
      Dualizing.IsNormalizedDualizingComplex.{u, u} ω ∧
      IsTildeModelOnAnyModel ωS.obj ⊤ (isAffineOpen_top S) ω := by
  obtain ⟨m, hm⟩ := Dualizing.exists_isNormalizedDualizingComplex_shift.{u, u} ω₀ hω₀
  refine ⟨⟨topTildeComplex (ω₀⟦-m⟧), fun i => ?_⟩, ω₀⟦-m⟧, hm,
    isTildeModelOnAnyModel_topTildeComplex _⟩
  exact isQuasicoherent_homology_of_hasDualizingModelOn_cover (fun _ : Unit => (⊤ : S.Opens))
    (fun _ => isAffineOpen_top S) (by simp)
    (fun _ => hasDualizingModelOn_of_isTildeModelOnAnyModel hm.1
      (isTildeModelOnAnyModel_topTildeComplex _)) i

/-- **The normalized dualizing model on the spectrum of a Noetherian local ring with a dualizing
complex.** This is the form the hypothesis of [Stacks, Tag 0AXD] provides: `A` is a Noetherian
local ring having a dualizing complex, with no normalization assumed and nothing said about
`Γ(Spec A, ⊤)`. The conclusion is a normalized dualizing complex over `Γ(Spec A, ⊤)` together
with its sheaf model on `Spec A`, which is what the dualizing-degree statements consume.

The hypothesis is read at whatever model of `D(A)` the caller works in,
`Dualizing.exists_isDualizingComplex_iff_of_models` carrying it to the standard model where the
normalization convention is stated.

The transport across `AlgebraicGeometry.Scheme.ΓSpecIso` is applied to that complex before any
normalization: `Dualizing.isDualizingComplex_of_ringEquiv` carries it to a dualizing complex over
`Γ(Spec A, ⊤)`, and the normalizing shift is then taken there, by
`Stacks.Duality.exists_isNormalizedDualizingComplex_isTildeModelOnAnyModel_top`. -/
theorem exists_isNormalizedDualizingComplex_isTildeModelOnAnyModel_spec (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A]
    [HasDerivedCategory.{w} (Spec (CommRingCat.of A)).Modules]
    [hA : HasDerivedCategory.{w'} (ModuleCat.{u} A)]
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) :
    letI : IsNoetherianRing Γ(Spec (CommRingCat.of A), ⊤) :=
      IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
    letI : IsLocalRing Γ(Spec (CommRingCat.of A), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.isLocalRing
    ∃ (ωS : quasiCoherentDerivedCategory (Spec (CommRingCat.of A)))
      (ω : DerivedCategory (ModuleCat.{u} Γ(Spec (CommRingCat.of A), ⊤))),
      Dualizing.IsNormalizedDualizingComplex.{u, u} ω ∧
      IsTildeModelOnAnyModel ωS.obj ⊤ (isAffineOpen_top (Spec (CommRingCat.of A))) ω := by
  obtain ⟨K, hK⟩ := (Dualizing.exists_isDualizingComplex_iff_of_models hA
    (HasDerivedCategory.standard (ModuleCat.{u} A))).mp hdual
  let : IsNoetherianRing Γ(Spec (CommRingCat.of A), ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let e : A ≃+* Γ(Spec (CommRingCat.of A), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
  let : IsLocalRing Γ(Spec (CommRingCat.of A), ⊤) := e.isLocalRing
  let : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (e : A →+* Γ(Spec (CommRingCat.of A), ⊤))) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
      (RingHom.Flat.of_bijective e.bijective)
  exact exists_isNormalizedDualizingComplex_isTildeModelOnAnyModel_top _
    (Dualizing.isDualizingComplex_of_ringEquiv e K hK)

end Stacks.Duality

end
