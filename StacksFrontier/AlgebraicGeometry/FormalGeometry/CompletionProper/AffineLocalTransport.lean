module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AffineLocalSolution
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionToClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.CompletionProjectionQuotient

/-!
# The restricted characterization of Stacks 088B, from a solution for `π ∣_ V`

Let `π : X' ⟶ X` be a proper morphism of Noetherian schemes, let `𝒥 ⊆ 𝒪_X` be a quasi-coherent
sheaf of ideals, let `(𝒢_n)` be an object of `Coh(X, 𝒥)`, let `𝓕` be a coherent
`𝒪_{X'}`-module and `β : π^*(𝒢_n) ≅ 𝓕 ^∧`. Over an open `V ⊆ X` the localization of
[Stacks, Tag 088B] asks for a morphism `ψ` of the *restricted* systems satisfying the
*restricted* characterization
`Stacks.Algebraization.HasAffineLocalDirectImageSolution`, and what the second paragraph of the
source produces is instead a solution of the problem for the *restricted morphism*
`π ∣_ V : π ⁻¹ V ⟶ V`. Translating the second into the first is
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/AffineLocalSolution.lean`'s
"piece 2", of which that file supplies only the target half. This file supplies the source half
and the transport of the equation, and so discharges piece 2.

## The two identifications, and what is needed

The restricted characterization is an equation between morphisms of inverse systems of
`𝒪_V`-modules. Its target is `((π_*𝓕) ^∧)|_V`, and the target of the characterization for
`π ∣_ V` is `((π ∣_ V)_*(𝓕|_{π ⁻¹ V})) ^∧`; the two are identified as systems by
`Stacks.Coherent.completedDirectImageRestrictIso`. Its source is `(𝒢_n)|_V`, which is literally
the source of the characterization for `π ∣_ V`, so nothing is needed there — but the `γ_n` side
of the equation for `π ∣_ V` is written with an isomorphism

`β' : (π ∣_ V)^*((𝒢_n)|_V) ≅ (𝓕|_{π ⁻¹ V}) ^∧`

over `V`, and that isomorphism has to be *produced from `β`*, as a morphism of systems, with
level-`n` component the one `Stacks.Coherent.directImageComparison_app_restrict_unit` names. That
is `Stacks.Coherent.restrictDirectImageIso` below.

## Main definitions

* `Stacks.Coherent.completionRestrictMorphismRestrictIso` — **the completion of `𝓕` restricted to
  `π ⁻¹ V`, as a system over the ideal sheaf `(𝒥|_V)|_{π ⁻¹ V}` that `π ∣_ V` lives over.** The
  isomorphism `Stacks.Algebraization.completionRestrictOpenIso` identifies `(𝓕 ^∧)|_{π ⁻¹ V}` with
  the completion of `𝓕|_{π ⁻¹ V}` along `(π^{-1}𝒥)|_{π ⁻¹ V}`, and
  `Stacks.Coherent.comap_comap_morphismRestrict` says that ideal sheaf is `(𝒥|_V)|_{π ⁻¹ V}`;
  the transport along that equality is `Stacks.Algebraization.completionCongrIso`.
* `Stacks.Coherent.restrictDirectImageIso` — **the restriction `β'` of `β`**, as an isomorphism
  in `Coh(π ⁻¹ V, (𝒥|_V)|_{π ⁻¹ V})`: the inverse-image base-change comparison
  `Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso`, then `β` restricted, then the
  comparison above. Its components are the conjugates of the `β_n`, which is what
  `Stacks.Coherent.directImageComparison_app_restrict_unit` exhibits the restricted `γ_n` as
  being built from.

## Main results

* `Stacks.Coherent.completionProjection_comp_completionRestrictMorphismRestrictIso` and
  `Stacks.Coherent.completionRestrictMorphismRestrictIso_hom_app_eq` — the normalization of the
  source-side comparison against the projections out of `𝓕`, and the resulting identification of
  its level-`n` component with
  `Stacks.Algebraization.restrictIdealPowerQuotientCongrIso`, the comparison the `δ` side of the
  equation is stated with.
* `Stacks.Coherent.directImageComparison_app_restrictDirectImageIso` — **`γ_n` for `π ∣_ V` at
  `β'` is the restriction of `γ_n` for `π`**, followed by the direct-image base-change
  comparison and the source-side comparison. This is
  `Stacks.Coherent.directImageComparison_app_restrict_unit` with the named `β'` put in.
* `Stacks.Coherent.restrictFunctor_map_eqToHom_comp_directImageQuotientRestrictTargetIso` — the
  same identification read on the target of `γ_n`, against
  `Stacks.Coherent.directImageQuotientRestrictTargetIso`.
* `Stacks.Coherent.restrictedCharacterization_of_isDirectImageCharacterized` — **piece 2.** A
  morphism `ψ` over `V` which is characterized in the sense of
  `Stacks.Coherent.IsDirectImageCharacterized` for `π ∣_ V` and `β'` becomes, after composing
  with `Stacks.Coherent.completedDirectImageRestrictIso`, a morphism of the restricted systems
  satisfying the restricted characterization over `V`.
* `Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_morphismRestrict` — **the local
  solution of Stacks 088B over an affine open of the base, reduced to a solution of the problem
  for the restricted morphism.** `Stacks.Algebraization.HasAffineLocalDirectImageSolution` —
  the single remaining binder behind [Stacks, Tag 088C], `hDev` and the first input of
  [Stacks, Tag 088E] — follows from the existence, over each affine open `V` of the base, of a
  morphism characterized for `π ∣_ V` with its levelwise kernels and cokernels annihilated by a
  power of `𝒦|_V`. The annihilation transports for free
  (`Stacks.Coherent.isKernelCokernelAnnihilatedByPower_comp_iso_iff`).

## What remains

Two of the three things `AffineLocalSolution.lean` records are still open, and neither is
addressed here.

**The geometric half of piece 1** — the transport of `π ∣_ V`, `𝓕|_{π ⁻¹ V}`, `(𝒢_n)|_V` and
`β'` across `AlgebraicGeometry.IsAffineOpen.isoSpec` to data over `Spec Γ(X, V)`, which is the
shape `Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicCompletionPullback` and
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicBaseChangeSquares` are stated
for. The ideal-sheaf half is
`Stacks.Algebraization.comap_adicIdealSheaf_isoSpec`; the rest is not here. With the hypothesis
of `Stacks.Algebraization.hasAffineLocalDirectImageSolution_of_morphismRestrict` this is now the
*only* geometric step between the affine solutions and the local data of the glueing.

**The sheafification of piece 3** — turning
`Stacks.Algebraization.smul_top_eq_bot_of_baseChange_adicCompletion` into the sheaf statement
`Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower` asks for, which needs exactness of
pullback along the flat `Spec B ^∧ ⟶ Spec B` on the levelwise kernels and cokernels and the
identification of the sections of a pullback with a base change.

The residual `hγ` of
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicBaseChangeGamma` is also
untouched.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules _`, agreeing with it only at
default transparency, so the ambient category of `CategoryTheory.Category.assoc` and of
`CategoryTheory.Category.comp_id` is named explicitly with `(obj := _)` and the composites are
assembled in term mode out of `congrArg`, as in `AffineLocalSolution.lean`.

The one place where that discipline is not enough is the level-`n` component of a composite of
two natural isomorphisms. `(Φ ≪≫ Ψ).hom.app n = Φ.hom.app n ≫ Ψ.hom.app n` is `rfl`, but
checking that `rfl` asks the kernel to reduce the composition of the two natural
transformations, which means reducing the category structure of `ℕᵒᵖ ⥤ (π ⁻¹ V).Modules` through
that `def`, and the kernel times out — as it does on
`CategoryTheory.NatTrans.comp_app` with its arguments left to unification, which solves them by
reducing the same term. Splitting the step in two fixes it:
`completionRestrictMorphismRestrictIso_hom` is the equality of the two natural transformations,
which is `rfl` at the level of the functor category and needs no reduction of the composition,
and `CategoryTheory.NatTrans.comp_app` is then applied to a composite that is already written as
one.

No `stacks` attribute is attached. Nothing here is a statement of the source: the results are
transports of the source's characterization along identifications the library already has, and
the tag for the localization step is registered on
`Stacks.Coherent.exists_isDirectImageCharacterized_isKernelCokernel_of_affineLocalSolutions`.

## References

* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Coherent

open Stacks.Algebraization Stacks.AlgebraicGeometry.AffinePushforward

section RestrictBeta

variable {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] (π : X' ⟶ X) (V : X.Opens)
  [IsNoetherian V.toScheme] [IsNoetherian (π ⁻¹ᵁ V).toScheme] (J : X.IdealSheafData)
  (G : CoherentAdicSystems J)
  (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)

/-- **The completion of `𝓕|_{π ⁻¹ V}` along the ideal sheaf `(𝒥|_V)|_{π ⁻¹ V}` of `π ∣_ V`.**
The restriction to `π ⁻¹ V` of the completion of `𝓕` along `π^{-1}𝒥` is the completion of
`𝓕|_{π ⁻¹ V}`, as an isomorphism of inverse systems; the ideal sheaf the latter is taken along is
named by `π ∣_ V` rather than by `π`, the two being equal by
`Stacks.Coherent.comap_comap_morphismRestrict`.

This is `Stacks.Algebraization.completionRestrictOpenIso` followed by
`Stacks.Algebraization.completionCongrIso`. It is the comparison the target of `β'` is read
through. -/
public def completionRestrictMorphismRestrictIso :
    ((completionFunctor X' (J.comap π)).obj 𝓕).obj ⋙
        Scheme.Modules.restrictFunctor (π ⁻¹ᵁ V).ι ≅
      ((completionFunctor (π ⁻¹ᵁ V).toScheme ((J.comap V.ι).comap (π ∣_ V))).obj
        (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕)).obj :=
  completionRestrictOpenIso (π ⁻¹ᵁ V).ι (J.comap π) 𝓕 ≪≫
    completionCongrIso (comap_comap_morphismRestrict π V J).symm
      (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕)

variable (β : (coherentAdicPullback π J).obj G ≅ (completionFunctor X' (J.comap π)).obj 𝓕)

/-- **The restriction `β'` of the isomorphism `β` of Stacks 088B to an open of the base.** For
`π : X' ⟶ X`, an object `(𝒢_n)` of `Coh(X, 𝒥)`, a coherent `𝓕` on `X'` and
`β : π^*(𝒢_n) ≅ 𝓕 ^∧`, this is the isomorphism

`β' : (π ∣_ V)^*((𝒢_n)|_V) ≅ (𝓕|_{π ⁻¹ V}) ^∧`

in `Coh(π ⁻¹ V, (𝒥|_V)|_{π ⁻¹ V})`: the inverse-image base-change comparison
`Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso` read backwards, then `β`
restricted to `π ⁻¹ V`, then `Stacks.Coherent.completionRestrictMorphismRestrictIso`.

This is the isomorphism `Stacks.Coherent.directImageComparison_app_restrict_unit` names: the
restricted `γ_n` is the `γ_n` of `π ∣_ V` at the conjugate of `β_n`, and that conjugate is the
level-`n` component of `β'` (`Stacks.Coherent.restrictDirectImageIso_hom_hom_app`). Its existence
as a morphism of *systems*, rather than one level at a time, is what lets a solution of the
problem for `π ∣_ V` be read as a solution of the restricted problem. -/
public def restrictDirectImageIso :
    (coherentAdicPullback (π ∣_ V) (J.comap V.ι)).obj
        ((Stacks.Coherent.restrictFunctor J V.ι).obj G) ≅
      (completionFunctor (π ⁻¹ᵁ V).toScheme ((J.comap V.ι).comap (π ∣_ V))).obj
        (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕) :=
  ObjectProperty.isoMk _
    (Functor.isoWhiskerLeft G.obj (pullbackRestrictIso π V).symm ≪≫
      Functor.isoWhiskerRight ((ObjectProperty.ι (IsCoherentAdicSystem (J.comap π))).mapIso β)
          (Scheme.Modules.restrictFunctor (π ⁻¹ᵁ V).ι) ≪≫
        completionRestrictMorphismRestrictIso π V J 𝓕)

/-- **The components of `Stacks.Coherent.restrictDirectImageIso` are the conjugates of the `β_n`
by the inverse-image base-change comparison**, which is exactly the shape
`Stacks.Coherent.directImageComparison_app_restrict_unit` exhibits the restricted `γ_n` in. -/
public theorem restrictDirectImageIso_hom_hom_app (n : ℕᵒᵖ) :
    (restrictDirectImageIso π V J G 𝓕 β).hom.hom.app n =
      (pullbackRestrictIso π V).inv.app (G.obj.obj n) ≫
        (Scheme.Modules.restrictFunctor (π ⁻¹ᵁ V).ι).map (β.hom.hom.app n) ≫
          (completionRestrictMorphismRestrictIso π V J 𝓕).hom.app n :=
  rfl

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian V.toScheme]
  [AlgebraicGeometry.IsNoetherian (π ⁻¹ᵁ V).toScheme] in
/-- `Stacks.Coherent.completionRestrictMorphismRestrictIso` as a composite of natural
transformations. This is the step that must be taken *before* reading the level-`n` component:
see the module docstring. -/
private theorem completionRestrictMorphismRestrictIso_hom :
    (completionRestrictMorphismRestrictIso π V J 𝓕).hom =
      (completionRestrictOpenIso (π ⁻¹ᵁ V).ι (J.comap π) 𝓕).hom ≫
        (completionCongrIso (comap_comap_morphismRestrict π V J).symm
          (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕)).hom :=
  rfl

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian V.toScheme]
  [AlgebraicGeometry.IsNoetherian (π ⁻¹ᵁ V).toScheme] in
/-- **The components of `Stacks.Coherent.completionRestrictMorphismRestrictIso`**: the
restriction comparison of Stacks 0880 followed by the transport along the equality of the two
inverse images of `𝒥` on `π ⁻¹ V`. -/
public theorem completionRestrictMorphismRestrictIso_hom_app (n : ℕ) :
    (completionRestrictMorphismRestrictIso π V J 𝓕).hom.app (op n) =
      (completionRestrictOpenIso (π ⁻¹ᵁ V).ι (J.comap π) 𝓕).hom.app (op n) ≫
        (completionCongrIso (comap_comap_morphismRestrict π V J).symm
          (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕)).hom.app (op n) :=
  (congrArg (fun t => NatTrans.app t (op n))
      (completionRestrictMorphismRestrictIso_hom π V J 𝓕)).trans
    (NatTrans.comp_app _ _ _)

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian V.toScheme]
  [AlgebraicGeometry.IsNoetherian (π ⁻¹ᵁ V).toScheme] in
/-- The two known normalizations of the projections, chained. The reassociation is
`Stacks.Coherent.completionProjection_comp_completionRestrictMorphismRestrictIso`. -/
private theorem completionProjection_comp_factors (n : ℕ) :
    ((Scheme.Modules.restrictFunctor (π ⁻¹ᵁ V).ι).map
          (completionProjection X' (J.comap π) 𝓕 n) ≫
        (completionRestrictOpenIso (π ⁻¹ᵁ V).ι (J.comap π) 𝓕).hom.app (op n)) ≫
        (completionCongrIso (comap_comap_morphismRestrict π V J).symm
          (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕)).hom.app (op n) =
      completionProjection (π ⁻¹ᵁ V).toScheme ((J.comap V.ι).comap (π ∣_ V))
        (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕) n :=
  (congrArg (fun z => z ≫ (completionCongrIso (comap_comap_morphismRestrict π V J).symm
        (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕)).hom.app (op n))
      (completionProjection_comp_completionRestrictOpenIso (π ⁻¹ᵁ V).ι (J.comap π) 𝓕 n)).trans
    (completionProjection_comp_completionCongrIso (comap_comap_morphismRestrict π V J).symm
      (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕) n)

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian V.toScheme]
  [AlgebraicGeometry.IsNoetherian (π ⁻¹ᵁ V).toScheme] in
/-- **`Stacks.Coherent.completionRestrictMorphismRestrictIso` carries projections to
projections**: the restriction to `π ⁻¹ V` of the projection of `𝓕` onto the `n`-th level of its
completion, read through the comparison, is the projection of `𝓕|_{π ⁻¹ V}` onto the `n`-th level
of its own completion. The projections being epimorphisms, this determines the comparison, and it
is how `Stacks.Coherent.completionRestrictMorphismRestrictIso_hom_app_eq` is proved. -/
public theorem completionProjection_comp_completionRestrictMorphismRestrictIso (n : ℕ) :
    (Scheme.Modules.restrictFunctor (π ⁻¹ᵁ V).ι).map
          (completionProjection X' (J.comap π) 𝓕 n) ≫
        (completionRestrictMorphismRestrictIso π V J 𝓕).hom.app (op n) =
      completionProjection (π ⁻¹ᵁ V).toScheme ((J.comap V.ι).comap (π ∣_ V))
        (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕) n :=
  (congrArg (fun z => (Scheme.Modules.restrictFunctor (π ⁻¹ᵁ V).ι).map
        (completionProjection X' (J.comap π) 𝓕 n) ≫ z)
      (completionRestrictMorphismRestrictIso_hom_app π V J 𝓕 n)).trans
    ((Category.assoc (obj := (π ⁻¹ᵁ V).toScheme.Modules) _ _ _).symm.trans
      (completionProjection_comp_factors π V J 𝓕 n))

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian V.toScheme]
  [AlgebraicGeometry.IsNoetherian (π ⁻¹ᵁ V).toScheme] in
/-- **The level-`n` component of `Stacks.Coherent.completionRestrictMorphismRestrictIso` is the
restriction comparison of the adic quotient.** Read against the object formula of Stacks 0880 at
both ends, the comparison of the two completions is
`Stacks.Algebraization.restrictIdealPowerQuotientCongrIso`, the comparison that
`Stacks.Coherent.directImageQuotientRestrictTargetIso` — and hence the `δ` side of the restricted
characterization — is stated with. Both sides are computed after the restricted projection of
`𝓕`, which is an epimorphism. -/
public theorem completionRestrictMorphismRestrictIso_hom_app_eq [𝓕.obj.IsQuasicoherent]
    (n : ℕ) :
    (Scheme.Modules.restrictFunctor (π ⁻¹ᵁ V).ι).map
          (eqToHom (completionFunctor_obj X' (J.comap π) 𝓕 n)) ≫
        (restrictIdealPowerQuotientCongrIso (π ⁻¹ᵁ V).ι (J.comap π) (n + 1) 𝓕.obj
          (comap_comap_morphismRestrict π V J)).hom =
      (completionRestrictMorphismRestrictIso π V J 𝓕).hom.app (op n) ≫
        eqToHom (completionFunctor_obj (π ⁻¹ᵁ V).toScheme ((J.comap V.ι).comap (π ∣_ V))
          (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕) n) := by
  have hepi : Epi ((Scheme.Modules.restrictFunctor (π ⁻¹ᵁ V).ι).map
      (completionProjection X' (J.comap π) 𝓕 n)) :=
    let := Stacks.Coherent.epi_completionProjection (J.comap π) 𝓕 n
    (Scheme.Modules.restrictFunctor (π ⁻¹ᵁ V).ι).map_epi _
  refine (@cancel_epi _ _ _ _ _ ((Scheme.Modules.restrictFunctor (π ⁻¹ᵁ V).ι).map
    (completionProjection X' (J.comap π) 𝓕 n)) hepi _ _).mp ?_
  have hL : (Scheme.Modules.restrictFunctor (π ⁻¹ᵁ V).ι).map
        (completionProjection X' (J.comap π) 𝓕 n) ≫
      (Scheme.Modules.restrictFunctor (π ⁻¹ᵁ V).ι).map
        (eqToHom (completionFunctor_obj X' (J.comap π) 𝓕 n)) =
      (Scheme.Modules.restrictFunctor (π ⁻¹ᵁ V).ι).map
        (cokernel.π (C := X'.Modules)
          (idealPowerMultiple (J.comap π) (n + 1) 𝓕.obj).ι) :=
    ((Scheme.Modules.restrictFunctor (π ⁻¹ᵁ V).ι).map_comp _ _).symm.trans
      (congrArg (Scheme.Modules.restrictFunctor (π ⁻¹ᵁ V).ι).map
        (Stacks.Algebraization.completionProjection_comp_eqToHom_cokernelπ (J.comap π) 𝓕 n))
  refine Eq.trans (Category.assoc (obj := (π ⁻¹ᵁ V).toScheme.Modules) _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫
    (restrictIdealPowerQuotientCongrIso (π ⁻¹ᵁ V).ι (J.comap π) (n + 1) 𝓕.obj
      (comap_comap_morphismRestrict π V J)).hom) hL) ?_
  refine Eq.trans (restrictIdealPowerQuotientCongrIso_π (π ⁻¹ᵁ V).ι (J.comap π) (n + 1) 𝓕.obj
    (comap_comap_morphismRestrict π V J)) ?_
  refine Eq.trans (Stacks.Algebraization.completionProjection_comp_eqToHom_cokernelπ
    ((J.comap V.ι).comap (π ∣_ V)) (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕) n).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ eqToHom
    (completionFunctor_obj (π ⁻¹ᵁ V).toScheme ((J.comap V.ι).comap (π ∣_ V))
      (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕) n))
    (completionProjection_comp_completionRestrictMorphismRestrictIso π V J 𝓕 n).symm) ?_
  exact Category.assoc (obj := (π ⁻¹ᵁ V).toScheme.Modules) _ _ _

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian V.toScheme]
  [AlgebraicGeometry.IsNoetherian (π ⁻¹ᵁ V).toScheme] in
/-- **The target of `γ_n` under restriction to `V`, read through the completion of the restricted
module.** The restriction to `V` of the object formula for the `n`-th level of `π_*(𝓕 ^∧)`,
followed by `Stacks.Coherent.directImageQuotientRestrictTargetIso`, is the direct-image
base-change comparison followed by the direct image along `π ∣_ V` of
`Stacks.Coherent.completionRestrictMorphismRestrictIso` and the object formula over `V`.

Only the naturality of
`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso` at the object formula is
used, together with `Stacks.Coherent.completionRestrictMorphismRestrictIso_hom_app_eq`. -/
public theorem restrictFunctor_map_eqToHom_comp_directImageQuotientRestrictTargetIso
    [𝓕.obj.IsQuasicoherent] (n : ℕ) :
    (Scheme.Modules.restrictFunctor V.ι).map
          (eqToHom (pushforward_completion_obj π J 𝓕 n)) ≫
        (directImageQuotientRestrictTargetIso π V J (n + 1) 𝓕.obj).hom =
      (restrictPushforwardIso π V).hom.app
          (((completionFunctor X' (J.comap π)).obj 𝓕).obj.obj (op n)) ≫
        (Scheme.Modules.pushforward (π ∣_ V)).map
            ((completionRestrictMorphismRestrictIso π V J 𝓕).hom.app (op n)) ≫
          eqToHom (pushforward_completion_obj (π ∣_ V) (J.comap V.ι)
            (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕) n) := by
  have hT : (directImageQuotientRestrictTargetIso π V J (n + 1) 𝓕.obj).hom =
      (restrictPushforwardIso π V).hom.app (idealPowerQuotient (J.comap π) (n + 1) 𝓕.obj) ≫
        (Scheme.Modules.pushforward (π ∣_ V)).map
          (restrictIdealPowerQuotientCongrIso (π ⁻¹ᵁ V).ι (J.comap π) (n + 1) 𝓕.obj
            (comap_comap_morphismRestrict π V J)).hom :=
    rfl
  have hnat := (restrictPushforwardIso π V).hom.naturality
    (eqToHom (completionFunctor_obj X' (J.comap π) 𝓕 n))
  refine Eq.trans (congrArg (fun z => (Scheme.Modules.restrictFunctor V.ι).map z ≫
      (directImageQuotientRestrictTargetIso π V J (n + 1) 𝓕.obj).hom)
    (eqToHom_map (Scheme.Modules.pushforward π)
      (completionFunctor_obj X' (J.comap π) 𝓕 n)).symm) ?_
  refine Eq.trans (congrArg (fun z => (Scheme.Modules.restrictFunctor V.ι).map
      ((Scheme.Modules.pushforward π).map
        (eqToHom (completionFunctor_obj X' (J.comap π) 𝓕 n))) ≫ z) hT) ?_
  refine Eq.trans (Category.assoc (obj := V.toScheme.Modules) _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ (Scheme.Modules.pushforward (π ∣_ V)).map
      (restrictIdealPowerQuotientCongrIso (π ⁻¹ᵁ V).ι (J.comap π) (n + 1) 𝓕.obj
        (comap_comap_morphismRestrict π V J)).hom) hnat) ?_
  refine Eq.trans (Category.assoc (obj := V.toScheme.Modules) _ _ _) ?_
  refine congrArg (fun z => (restrictPushforwardIso π V).hom.app
      (((completionFunctor X' (J.comap π)).obj 𝓕).obj.obj (op n)) ≫ z) ?_
  refine Eq.trans ((Scheme.Modules.pushforward (π ∣_ V)).map_comp _ _).symm ?_
  refine Eq.trans (congrArg (Scheme.Modules.pushforward (π ∣_ V)).map
    (completionRestrictMorphismRestrictIso_hom_app_eq π V J 𝓕 n)) ?_
  refine Eq.trans ((Scheme.Modules.pushforward (π ∣_ V)).map_comp _ _) ?_
  exact congrArg (fun z => (Scheme.Modules.pushforward (π ∣_ V)).map
    ((completionRestrictMorphismRestrictIso π V J 𝓕).hom.app (op n)) ≫ z)
    (eqToHom_map (Scheme.Modules.pushforward (π ∣_ V))
      (completionFunctor_obj (π ⁻¹ᵁ V).toScheme ((J.comap V.ι).comap (π ∣_ V))
        (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕) n))

/-- **`γ_n` for `π ∣_ V` at `β'` is the restriction of `γ_n` for `π`**, followed by the
direct-image base-change comparison and the direct image along `π ∣_ V` of
`Stacks.Coherent.completionRestrictMorphismRestrictIso`.

This is `Stacks.Coherent.directImageComparison_app_restrict_unit` with the named
`Stacks.Coherent.restrictDirectImageIso` substituted for the `β'` that theorem leaves
anonymous: its components are precisely the conjugates that theorem produces
(`Stacks.Coherent.restrictDirectImageIso_hom_hom_app`), so nothing is left to check beyond
splitting the direct image of the triple composite. -/
public theorem directImageComparison_app_restrictDirectImageIso (n : ℕᵒᵖ) :
    (directImageComparison (π ∣_ V) (J.comap V.ι)
          ((Stacks.Coherent.restrictFunctor J V.ι).obj G)
          (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕)
          (restrictDirectImageIso π V J G 𝓕 β)).app n =
      (Scheme.Modules.restrictFunctor V.ι).map
          ((directImageComparison π J G 𝓕 β).app n) ≫
        (restrictPushforwardIso π V).hom.app
            (((completionFunctor X' (J.comap π)).obj 𝓕).obj.obj n) ≫
          (Scheme.Modules.pushforward (π ∣_ V)).map
            ((completionRestrictMorphismRestrictIso π V J 𝓕).hom.app n) := by
  refine Eq.trans (directImageComparison_app (π ∣_ V) (J.comap V.ι)
    ((Stacks.Coherent.restrictFunctor J V.ι).obj G)
    (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕) (restrictDirectImageIso π V J G 𝓕 β) n) ?_
  refine Eq.trans (congrArg (fun z =>
      (Scheme.Modules.pullbackPushforwardAdjunction (π ∣_ V)).unit.app
          ((Scheme.Modules.restrictFunctor V.ι).obj (G.obj.obj n)) ≫
        (Scheme.Modules.pushforward (π ∣_ V)).map z)
    ((restrictDirectImageIso_hom_hom_app π V J G 𝓕 β n).trans
      (Category.assoc (obj := (π ⁻¹ᵁ V).toScheme.Modules) _ _ _).symm)) ?_
  refine Eq.trans (congrArg (fun z =>
      (Scheme.Modules.pullbackPushforwardAdjunction (π ∣_ V)).unit.app
        ((Scheme.Modules.restrictFunctor V.ι).obj (G.obj.obj n)) ≫ z)
    ((Scheme.Modules.pushforward (π ∣_ V)).map_comp
      ((pullbackRestrictIso π V).inv.app (G.obj.obj n) ≫
        (Scheme.Modules.restrictFunctor (π ⁻¹ᵁ V).ι).map (β.hom.hom.app n))
      ((completionRestrictMorphismRestrictIso π V J 𝓕).hom.app n))) ?_
  refine Eq.trans (Category.assoc (obj := V.toScheme.Modules) _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ (Scheme.Modules.pushforward (π ∣_ V)).map
      ((completionRestrictMorphismRestrictIso π V J 𝓕).hom.app n))
    (directImageComparison_app_restrict_unit π V J G 𝓕 β n).symm) ?_
  exact Category.assoc (obj := V.toScheme.Modules) _ _ _

end RestrictBeta

/-! ### The transport of the characterizing equation -/

section Transport

variable {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] (π : X' ⟶ X) [IsProper π]
  (V : X.Opens) [IsNoetherian V.toScheme] [IsNoetherian (π ⁻¹ᵁ V).toScheme]
  (J : X.IdealSheafData) (G : CoherentAdicSystems J)
  (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
  (β : (coherentAdicPullback π J).obj G ≅ (completionFunctor X' (J.comap π)).obj 𝓕)

section Delta

variable [𝓕.obj.IsQuasicoherent]
  [((Scheme.Modules.pushforward π).obj 𝓕.obj).IsQuasicoherent]

omit [𝓕.obj.IsQuasicoherent] [AlgebraicGeometry.IsNoetherian (π ⁻¹ᵁ V).toScheme] in
/-- The level-`n` component of `Stacks.Coherent.completedDirectImageRestrictIso`, read against
the object formula of Stacks 0880 at the base `V`. -/
private theorem completedDirectImageRestrictIso_hom_app_comp_eqToHom (n : ℕ) :
    (completedDirectImageRestrictIso π V J 𝓕).hom.app (op n) ≫
        eqToHom (completionFunctor_obj V.toScheme (J.comap V.ι)
          (properPushforwardCoherent (π ∣_ V)
            (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕)) n) =
      (Scheme.Modules.restrictFunctor V.ι).map
          (eqToHom (completionFunctor_obj X J (properPushforwardCoherent π 𝓕) n)) ≫
        (directImageQuotientRestrictSourceIso π V J (n + 1) 𝓕.obj).hom := by
  have hΦ : (completedDirectImageRestrictIso π V J 𝓕).hom.app (op n) =
      (Scheme.Modules.restrictFunctor V.ι).map
          (eqToHom (completionFunctor_obj X J (properPushforwardCoherent π 𝓕) n)) ≫
        (directImageQuotientRestrictSourceIso π V J (n + 1) 𝓕.obj).hom ≫
          eqToHom (completionFunctor_obj V.toScheme (J.comap V.ι)
            (properPushforwardCoherent (π ∣_ V)
              (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕)) n).symm :=
    rfl
  have hid : eqToHom (completionFunctor_obj V.toScheme (J.comap V.ι)
          (properPushforwardCoherent (π ∣_ V)
            (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕)) n).symm ≫
        eqToHom (completionFunctor_obj V.toScheme (J.comap V.ι)
          (properPushforwardCoherent (π ∣_ V)
            (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕)) n) = 𝟙 _ :=
    (eqToIso (completionFunctor_obj V.toScheme (J.comap V.ι)
      (properPushforwardCoherent (π ∣_ V)
        (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕)) n)).inv_hom_id
  refine Eq.trans (congrArg (fun z => z ≫ eqToHom (completionFunctor_obj V.toScheme
    (J.comap V.ι) (properPushforwardCoherent (π ∣_ V)
      (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕)) n)) hΦ) ?_
  refine Eq.trans (Category.assoc (obj := V.toScheme.Modules) _ _ _) ?_
  refine congrArg (fun z => (Scheme.Modules.restrictFunctor V.ι).map
      (eqToHom (completionFunctor_obj X J (properPushforwardCoherent π 𝓕) n)) ≫ z) ?_
  refine Eq.trans (Category.assoc (obj := V.toScheme.Modules) _ _ _) ?_
  refine Eq.trans (congrArg (fun z =>
    (directImageQuotientRestrictSourceIso π V J (n + 1) 𝓕.obj).hom ≫ z) hid) ?_
  exact Category.comp_id (obj := V.toScheme.Modules) _

omit [AlgebraicGeometry.IsNoetherian (π ⁻¹ᵁ V).toScheme] in
/-- **The inverse of `Stacks.Coherent.completedDirectImageRestrictIso` carries the restricted `δ`
to the `δ` of `π ∣_ V`.** -/
private theorem completedDirectImageRestrictIso_inv_app_comp (n : ℕ) :
    (completedDirectImageRestrictIso π V J 𝓕).inv.app (op n) ≫
        (Scheme.Modules.restrictFunctor V.ι).map
          (eqToHom (completionFunctor_obj X J (properPushforwardCoherent π 𝓕) n) ≫
            directImageQuotientComparison π J (n + 1) 𝓕.obj) =
      eqToHom (completionFunctor_obj V.toScheme (J.comap V.ι)
          (properPushforwardCoherent (π ∣_ V)
            (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕)) n) ≫
        directImageQuotientComparison (π ∣_ V) (J.comap V.ι) (n + 1)
            ((Scheme.Modules.restrictFunctor (π ⁻¹ᵁ V).ι).obj 𝓕.obj) ≫
          (directImageQuotientRestrictTargetIso π V J (n + 1) 𝓕.obj).inv := by
  refine (Iso.inv_comp_eq ((completedDirectImageRestrictIso π V J 𝓕).app (op n))).2 ?_
  refine Eq.trans ((Scheme.Modules.restrictFunctor V.ι).map_comp
    (eqToHom (completionFunctor_obj X J (properPushforwardCoherent π 𝓕) n))
    (directImageQuotientComparison π J (n + 1) 𝓕.obj)) ?_
  refine Eq.trans (congrArg (fun z => (Scheme.Modules.restrictFunctor V.ι).map
      (eqToHom (completionFunctor_obj X J (properPushforwardCoherent π 𝓕) n)) ≫ z)
    (directImageQuotientComparison_restrict π V J (n + 1) 𝓕.obj)) ?_
  refine Eq.trans (Category.assoc (obj := V.toScheme.Modules) _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫
      (directImageQuotientComparison (π ∣_ V) (J.comap V.ι) (n + 1)
          ((Scheme.Modules.restrictFunctor (π ⁻¹ᵁ V).ι).obj 𝓕.obj) ≫
        (directImageQuotientRestrictTargetIso π V J (n + 1) 𝓕.obj).inv))
    (completedDirectImageRestrictIso_hom_app_comp_eqToHom π V J 𝓕 n).symm) ?_
  exact Category.assoc (obj := V.toScheme.Modules) _ _ _

omit [IsProper π] [((Scheme.Modules.pushforward π).obj 𝓕.obj).IsQuasicoherent] in
/-- **`γ_n` for `π ∣_ V` at `β'`, read against the object formula of the direct image of a
completion, is the restriction of `γ_n` for `π` followed by the target identification.** -/
private theorem directImageComparison_restrict_comp_eqToHom (n : ℕ) :
    (directImageComparison (π ∣_ V) (J.comap V.ι)
          ((Stacks.Coherent.restrictFunctor J V.ι).obj G)
          (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕)
          (restrictDirectImageIso π V J G 𝓕 β)).app (op n) ≫
        eqToHom (pushforward_completion_obj (π ∣_ V) (J.comap V.ι)
          (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕) n) =
      (Scheme.Modules.restrictFunctor V.ι).map
          ((directImageComparison π J G 𝓕 β).app (op n)) ≫
        (Scheme.Modules.restrictFunctor V.ι).map
            (eqToHom (pushforward_completion_obj π J 𝓕 n)) ≫
          (directImageQuotientRestrictTargetIso π V J (n + 1) 𝓕.obj).hom := by
  refine Eq.trans (congrArg (fun z => z ≫ eqToHom (pushforward_completion_obj (π ∣_ V)
      (J.comap V.ι) (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕) n))
    (directImageComparison_app_restrictDirectImageIso π V J G 𝓕 β (op n))) ?_
  refine Eq.trans (Category.assoc (obj := V.toScheme.Modules) _ _ _) ?_
  refine congrArg (fun z => (Scheme.Modules.restrictFunctor V.ι).map
      ((directImageComparison π J G 𝓕 β).app (op n)) ≫ z) ?_
  refine Eq.trans (Category.assoc (obj := V.toScheme.Modules) _ _ _) ?_
  exact (restrictFunctor_map_eqToHom_comp_directImageQuotientRestrictTargetIso
    π V J 𝓕 n).symm

omit [IsProper π] [AlgebraicGeometry.IsNoetherian V.toScheme]
  [AlgebraicGeometry.IsNoetherian (π ⁻¹ᵁ V).toScheme]
  [((Scheme.Modules.pushforward π).obj 𝓕.obj).IsQuasicoherent] in
/-- The last reassociation of
`Stacks.Coherent.restrictedCharacterization_of_isDirectImageCharacterized`: the target
identification cancels. -/
private theorem comp_directImageQuotientRestrictTargetIso_inv (n : ℕ) :
    ((Scheme.Modules.restrictFunctor V.ι).map
          ((directImageComparison π J G 𝓕 β).app (op n)) ≫
        (Scheme.Modules.restrictFunctor V.ι).map
            (eqToHom (pushforward_completion_obj π J 𝓕 n)) ≫
          (directImageQuotientRestrictTargetIso π V J (n + 1) 𝓕.obj).hom) ≫
        (directImageQuotientRestrictTargetIso π V J (n + 1) 𝓕.obj).inv =
      (Scheme.Modules.restrictFunctor V.ι).map
        ((directImageComparison π J G 𝓕 β).app (op n) ≫
          eqToHom (pushforward_completion_obj π J 𝓕 n)) := by
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id, ← Functor.map_comp]

end Delta

/-- **The source side of the localization of Stacks 088B over an open of the base.** Let
`π : X' ⟶ X` be proper between Noetherian schemes, `𝒥 ⊆ 𝒪_X` a quasi-coherent sheaf of ideals,
`(𝒢_n)` an object of `Coh(X, 𝒥)`, `𝓕` a coherent `𝒪_{X'}`-module and
`β : π^*(𝒢_n) ≅ 𝓕 ^∧`. Let `V ⊆ X` be open with `V` and `π ⁻¹ V` Noetherian. A morphism `ψ` of
the systems over `V` which is characterized in the sense of
`Stacks.Coherent.IsDirectImageCharacterized` **for the restricted morphism `π ∣_ V`** and the
restriction `β'` of `β` (`Stacks.Coherent.restrictDirectImageIso`) becomes, after composing with
`Stacks.Coherent.completedDirectImageRestrictIso`, a morphism of the *restricted* systems
satisfying the *restricted* characterization of Stacks 088B over `V`.

This is the step the localization of Stacks 088B was missing: the characterization is an equation
between morphisms of inverse systems, and a solution of the problem for `π ∣_ V` over `V` is a
solution of the restricted problem only after the two presentations of the source and of the
target have been identified as systems. The target is identified by
`Stacks.Coherent.completedDirectImageRestrictIso`, the source by
`Stacks.Coherent.restrictDirectImageIso`, and the equation is carried across by
`Stacks.Coherent.directImageQuotientComparison_restrict` on the `δ` side and by
`Stacks.Coherent.directImageComparison_app_restrict_unit` on the `γ_n` side.

No `stacks` attribute is attached: this is the transport of the source's characterization along
two identifications, not a statement of the source. -/
public theorem restrictedCharacterization_of_isDirectImageCharacterized
    (ψ : ((Stacks.Coherent.restrictFunctor J V.ι).obj G).obj ⟶
      ((completionFunctor V.toScheme (J.comap V.ι)).obj
        (properPushforwardCoherent (π ∣_ V)
          (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕))).obj)
    (hψ : IsDirectImageCharacterized (π ∣_ V) (J.comap V.ι)
      ((Stacks.Coherent.restrictFunctor J V.ι).obj G)
      (restrictCoherentModules (π ⁻¹ᵁ V).ι 𝓕) (restrictDirectImageIso π V J G 𝓕 β) ψ)
    (n : ℕ) :
    (ψ ≫ (completedDirectImageRestrictIso π V J 𝓕).inv).app (op n) ≫
        (Scheme.Modules.restrictFunctor V.ι).map
          (eqToHom (completionFunctor_obj X J (properPushforwardCoherent π 𝓕) n) ≫
            directImageQuotientComparison π J (n + 1) 𝓕.obj) =
      (Scheme.Modules.restrictFunctor V.ι).map
        ((directImageComparison π J G 𝓕 β).app (op n) ≫
          eqToHom (pushforward_completion_obj π J 𝓕 n)) := by
  have : 𝓕.obj.IsCoherent := 𝓕.property
  have : 𝓕.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent 𝓕.obj
  have : ((Scheme.Modules.pushforward π).obj 𝓕.obj).IsCoherent :=
    (properPushforwardCoherent π 𝓕).property
  have : ((Scheme.Modules.pushforward π).obj 𝓕.obj).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent ((Scheme.Modules.pushforward π).obj 𝓕.obj)
  refine Eq.trans (congrArg (fun z => z ≫ (Scheme.Modules.restrictFunctor V.ι).map
      (eqToHom (completionFunctor_obj X J (properPushforwardCoherent π 𝓕) n) ≫
        directImageQuotientComparison π J (n + 1) 𝓕.obj))
    (NatTrans.comp_app ψ (completedDirectImageRestrictIso π V J 𝓕).inv (op n))) ?_
  refine Eq.trans (Category.assoc (obj := V.toScheme.Modules) _ _ _) ?_
  refine Eq.trans (congrArg (fun z => ψ.app (op n) ≫ z)
    (completedDirectImageRestrictIso_inv_app_comp π V J 𝓕 n)) ?_
  refine Eq.trans (congrArg (fun z => ψ.app (op n) ≫ z)
    (Category.assoc (obj := V.toScheme.Modules) _ _ _).symm) ?_
  refine Eq.trans (Category.assoc (obj := V.toScheme.Modules) _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫
    (directImageQuotientRestrictTargetIso π V J (n + 1) 𝓕.obj).inv) (hψ n)) ?_
  refine Eq.trans (congrArg (fun z => z ≫
      (directImageQuotientRestrictTargetIso π V J (n + 1) 𝓕.obj).inv)
    (directImageComparison_restrict_comp_eqToHom π V J G 𝓕 β n)) ?_
  exact comp_directImageQuotientRestrictTargetIso_inv π V J G 𝓕 β n

end Transport

end Stacks.Coherent

namespace Stacks.Algebraization

open Stacks.Coherent

/-! ### The local solution of Stacks 088B, reduced to a solution for the restricted morphism -/

/-- **The local solution of Stacks 088B over an affine open of the base, reduced to a solution of
the problem for the restricted morphism.**
`Stacks.Algebraization.HasAffineLocalDirectImageSolution` — the single remaining binder behind
[Stacks, Tag 088C], the binder `hDev` of [Stacks, Tag 088E] and the first input of
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver_of_isDirectImageComparison` —
follows from the following datum: over every affine open `V` of the base, a morphism `ψ` of the
systems over `V` which

* is characterized in the sense of `Stacks.Coherent.IsDirectImageCharacterized` for the
  *restricted* morphism `π ∣_ V`, the restricted system `(𝒢_n)|_V`, the restricted module
  `𝓕|_{π ⁻¹ V}` and the restricted isomorphism
  `Stacks.Coherent.restrictDirectImageIso`, and
* has its levelwise kernels and cokernels annihilated by a power of `𝒦|_V`.

That is: a solution *of the problem of Stacks 088B for `π ∣_ V` over `V`*, which is what the
second paragraph of the source produces, rather than a solution of the restricted problem, which
is what the glueing of the first paragraph consumes. Translating one into the other is piece 2 of
the three things `AffineLocalSolution.lean` records as missing, and it is
`Stacks.Coherent.restrictedCharacterization_of_isDirectImageCharacterized` together with
`Stacks.Coherent.completedDirectImageRestrictIso`; the annihilation half costs nothing, since
composing with an isomorphism of systems changes no levelwise kernel or cokernel
(`Stacks.Coherent.isKernelCokernelAnnihilatedByPower_comp_iso_iff`).

The two Noetherian hypotheses the transport needs are automatic: every open of a Noetherian
scheme is Noetherian (`AlgebraicGeometry.Scheme.Opens.isNoetherian`), so `V` and `π ⁻¹ V` are,
and no quasi-compactness has to be supplied by hand.

No `stacks` attribute is attached: this is a reduction of a hypothesis, not a statement of the
source. -/
public theorem hasAffineLocalDirectImageSolution_of_morphismRestrict
    (h : ∀ {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] (π : X' ⟶ X) [IsProper π]
      (J K : X.IdealSheafData) (G : CoherentAdicSystems J)
      (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
      (β : (coherentAdicPullback π J).obj G ≅ (completionFunctor X' (J.comap π)).obj 𝓕),
      IsIso (π ∣_ K.support.compl) →
        ∀ V : X.affineOpens,
          ∃ ψ : ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G).obj ⟶
            ((completionFunctor V.1.toScheme (J.comap V.1.ι)).obj
              (properPushforwardCoherent (π ∣_ V.1)
                (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕))).obj,
            IsDirectImageCharacterized (π ∣_ V.1) (J.comap V.1.ι)
                ((Stacks.Coherent.restrictFunctor J V.1.ι).obj G)
                (restrictCoherentModules (π ⁻¹ᵁ V.1).ι 𝓕)
                (restrictDirectImageIso π V.1 J G 𝓕 β) ψ ∧
              IsKernelCokernelAnnihilatedByPower (K.comap V.1.ι) ψ) :
    HasAffineLocalDirectImageSolution.{u} := by
  intro X' X _ _ π _ J K G 𝓕 β hiso V
  obtain ⟨ψ, hchar, hann⟩ := h π J K G 𝓕 β hiso V
  exact ⟨ψ ≫ (completedDirectImageRestrictIso π V.1 J 𝓕).inv,
    fun n => restrictedCharacterization_of_isDirectImageCharacterized π V.1 J G 𝓕 β ψ hchar n,
    (isKernelCokernelAnnihilatedByPower_comp_iso_iff (K.comap V.1.ι) ψ
      (completedDirectImageRestrictIso π V.1 J 𝓕).symm).2 hann⟩

end Stacks.Algebraization

end
