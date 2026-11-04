module

public import StacksFrontier.AlgebraicGeometry.Divisors.DepthOneQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtension
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksCore.Tactic.StacksAttribute

import all StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtension

/-!
# Existence of the depth-two extension along a specialization-stable subset

Let `X` be a Noetherian scheme and let `T ⊆ X` be stable under specialization.  A coherent
`𝒪_X`-module `F` has a *depth-two extension along `T`*: a map `F → F''` of coherent modules
which is an isomorphism on stalks away from `T` and whose target has stalks of depth at least
two at every point of `T`.  That is `AlgebraicGeometry.IsDepthTwoExtension`, and this module
assembles the map out of the two steps of the source's construction.

The construction has two steps.  First `F` is replaced by its depth-one quotient along `T`,
which is `AlgebraicGeometry.depthOneQuotient`.  Then the quotient is extended across `T` by
taking sections over the opens whose complement lies inside `T`: the system of pushforwards
`j_{V,*}(F'|_V)` for such opens `V` is filtered by reverse inclusion, and its colimit is the
depth-two extension.  The second step is recorded here as
`AlgebraicGeometry.IsStabilizedOpenExtension`, the property of a map out of `F'` of being that
colimit after it has stabilized, and the theorems below derive the three clauses of
`AlgebraicGeometry.IsDepthTwoExtension` from it.

## Main definitions

* `AlgebraicGeometry.LocallyHasDualizingComplex`: the affine-local existential form of the
  hypothesis that a scheme locally has a dualizing complex.
* `AlgebraicGeometry.IsStabilizedOpenExtension`: a coherent target which, near every point, is
  the pushforward of its own restriction to an open whose complement lies in the subset, and
  over which the given map is an isomorphism.

## Main results

* `AlgebraicGeometry.isIso_unit_of_isDepthTwoExtension`: the target of a depth-two extension is
  the pushforward of its own restriction to any open whose complement lies in the subset.
* `AlgebraicGeometry.isDepthTwoExtension_comp_of_isStabilizedOpenExtension`: composing a map
  which is a stalkwise isomorphism away from the subset with a stabilized open extension gives
  a depth-two extension.
* `AlgebraicGeometry.exists_isDepthTwoExtension`: a coherent module admits a depth-two
  extension along a specialization-stable subset.

## Implementation notes

The scalar action on a stalk is spelled out wherever a depth appears, because the stalk of
an `𝒪_X`-module is built as an abelian group and carries no such instance by default.  The
spelling is the one of `AlgebraicGeometry.IsDepthTwoExtension` and of
`AlgebraicGeometry.isIso_unit_restrict_pushforward_of_depth_ge_two`, so the statements below fit
together with the existing depth results without transport.

Two inputs of the source's existence proof are absent from this library and are carried as
hypotheses rather than discharged.  Both are named precisely in the statements, and neither is a
restatement of the conclusion.

* **Coherence of the extension.**  The source proves that the colimit of the pushforwards is
  coherent by computing, on an affine open `Spec(A)` with `F' ↔ M'`, a short exact sequence
  `0 → M' → M'' → H¹_T(M') → 0` and applying Faltings' finiteness criterion
  [Stacks, Tag 0EFD] — now available as
  `Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_iff_depth_add_dim` — to the
  dualizing complex supplied by `AlgebraicGeometry.LocallyHasDualizingComplex`.  Neither the
  short exact sequence nor the colimit of pushforwards is built in this library, so coherence of
  the extension is part of `AlgebraicGeometry.IsStabilizedOpenExtension` instead of being
  deduced.  This is why the dualizing hypothesis and the depth hypothesis on immediate
  specializations of [Stacks, Tag 0EI3] do not appear below: they enter the source's argument
  only through that finiteness, so the statements here are correspondingly stronger.
* **The depth bound outside an open.**  That a coherent module which is the pushforward of its
  own restriction to an open `V` has stalks of depth at least two outside `V` is
  [Stacks, Tag 0EY0] part (3), the converse of
  `AlgebraicGeometry.isIso_unit_restrict_pushforward_of_depth_ge_two`.  Its proof uses flat base
  change [Stacks, Tag 02KH], which this library does not have in the required form, so the bound
  is carried as the hypothesis `hdepthOutside`, stated for every open and every coherent module
  on `X`.  The same gap is carried in the same way by
  `AlgebraicGeometry.existsUnique_iso_pullback_pushforward_restrict_of_depth`.

`AlgebraicGeometry.LocallyHasDualizingComplex` asks every affine open of `X` to carry a
dualizing complex over its ring of sections, which is the form [Stacks, Tag 0EFD] consumes.  The
source's hypothesis is the weaker one that the affine opens of *some* cover do; the equivalence
of the two is the ring-theoretic content behind [Stacks, Tag 0A86], which is proved in this
library only for a single global object of `D(𝒪_X)`
(`Stacks.Duality.isDualizingComplex_iff_exists_affineOpenCover`) and not for the existential form
used here.  So the two are not interchangeable, and
`AlgebraicGeometry.LocallyHasDualizingComplex` is also not interchangeable with
`Stacks.Duality.IsDualizingComplex`, which asserts a single dualizing complex on all of `X`.

## References

* [Stacks Project, Tag 0EI3](https://stacks.math.columbia.edu/tag/0EI3)
* [Stacks Project, Tag 0DX3](https://stacks.math.columbia.edu/tag/0DX3)
* [Stacks Project, Tag 0DX4](https://stacks.math.columbia.edu/tag/0DX4)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
* [Stacks Project, Tag 0EFD](https://stacks.math.columbia.edu/tag/0EFD)
* [Stacks Project, Tag 0EY0](https://stacks.math.columbia.edu/tag/0EY0)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-! ### Locally having a dualizing complex -/

/-- A locally Noetherian scheme *locally has a dualizing complex* when the ring of sections of
every affine open admits one.

This is the affine-local existential form of the hypothesis: the dualizing complexes are not
asked to be compatible, nor to come from a single object of `D(𝒪_X)`.  It is therefore not
interchangeable with `Stacks.Duality.IsDualizingComplex`, which asserts one global dualizing
complex, and it is stronger than the source's hypothesis that the members of some affine open
cover have dualizing complexes, since the passage between the two forms is not available in this
library.  See the implementation notes of this module. -/
public def LocallyHasDualizingComplex (X : Scheme.{u}) [IsLocallyNoetherian X] : Prop :=
  ∀ U : X.affineOpens,
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U.1)), Dualizing.IsDualizingComplex ω

/-! ### The stabilized extension across the subset -/

/-- A map `ψ : F ⟶ G` of modules on `X` is a *stabilized open extension along `T`* when `G` is
coherent and, for every point `x` of `X`, there is an open `V` such that

* the complement of `V` lies in `T`,
* `x ∉ V` whenever `x ∈ T`,
* `ψ` is an isomorphism on the stalks at the points of `V`, and
* `G` is the pushforward of its own restriction to `V`.

These are the properties of the colimit of the pushforwards `j_{V,*}(F|_V)` over the opens `V`
whose complement lies in `T`, once that colimit has stabilized: the colimit restricts to `F` on
each such `V`, and it agrees with `j_{V,*}(F|_V)` for `V` small enough, which for a point `x` of
`T` may be arranged to avoid `x`.  That family of opens is filtered by reverse inclusion exactly
because `T` is stable under specialization.

Note that the complement of any such `V` lying in `T` forces `V` to contain the complement of
`T`, so the third clause pins `ψ` down on the stalks away from `T` whatever the choice of `V`. -/
public def IsStabilizedOpenExtension {X : Scheme.{u}} (T : Set X) {F G : X.Modules}
    (ψ : F ⟶ G) : Prop :=
  G.IsCoherent ∧
    ∀ x : X, ∃ V : X.Opens, ((V : Set X)ᶜ ⊆ T) ∧ (x ∈ T → x ∉ (V : Set X)) ∧
      (∀ y : X, y ∈ (V : Set X) →
        IsIso (AlgebraicGeometry.SheafOfModules.stalkMap X.ringCatSheaf y ψ)) ∧
      IsIso ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app G)

/-! ### The depth-two extension -/

/-- The stalk map of a morphism of sheaves of modules, read in `ModuleCat` over the stalk of
`𝒪_X`, is invertible as soon as the induced map of abelian-group stalks is: the two are the same
function. -/
private lemma isIso_stalkMap_of_isIso_stalkFunctor {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (x : X)
    (h : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map f.mapPresheaf)) :
    IsIso (AlgebraicGeometry.SheafOfModules.stalkMap X.ringCatSheaf x f) := by
  rw [ConcreteCategory.isIso_iff_bijective] at h ⊢
  exact h


/-! ### The depth-two extension -/

/-- An isomorphism of abelian-group stalks is one of stalks over the local ring. -/
private lemma isIso_stalkMap_of_isIso_stalkAb {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (x : X) (h : IsIso ((stalkAb X x).map f)) :
    IsIso (AlgebraicGeometry.SheafOfModules.stalkMap X.ringCatSheaf x f) := by
  rw [ConcreteCategory.isIso_iff_bijective] at h ⊢
  exact h

/-- The target of a depth-two extension along `T` is the pushforward of its own restriction to
any open whose complement lies in `T`.

This is the step `F'' = j_*(F''|_V)` of the source's uniqueness argument, and it is the converse
of the depth bound carried below: the complement of such an open consists of points of `T`,
where the depth of the stalk is at least two, so the Hartogs-type isomorphism
[Stacks, Tag 0E9I] applies. -/
@[ega "IV 19.9.9" "Case k = 2", ega "IV 21.13.4" "partial", sga "6 II 2.2.7.2" "more general"]
public theorem isIso_unit_of_isDepthTwoExtension {X : Scheme.{u}} [IsLocallyNoetherian X]
    {T : Set X} {F G : X.Modules} (φ : F ⟶ G) (hφ : IsDepthTwoExtension T φ)
    (V : X.Opens) (hVT : ((V : Set X))ᶜ ⊆ T) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app G) :=
  letI : G.IsCoherent := hφ.1
  isIso_unit_restrict_pushforward_of_depth_ge_two X G V fun x hx => hφ.2.2 x (hVT hx)

/-- Composing a map which is an isomorphism on the stalks away from `T` with a stabilized open
extension along `T` gives a depth-two extension along `T`.

The clause away from `T` is the composite of the two stalk isomorphisms, since the open
furnished by the stabilized extension contains the complement of `T`.  The clause on `T` is the
depth bound outside an open, applied at an open avoiding the given point of `T`, which is
[Stacks, Tag 0EY0] part (3); that part is absent from this library, so it is the hypothesis
`hdepthOutside` rather than a theorem.  Coherence is part of the stabilized extension. -/
public theorem isDepthTwoExtension_comp_of_isStabilizedOpenExtension
    {X : Scheme.{u}} [IsNoetherian X] (T : Set X)
    {F F' G : X.Modules} (ρ : F ⟶ F') (ψ : F' ⟶ G)
    (hρ : ∀ x : X, x ∉ T →
      IsIso (AlgebraicGeometry.SheafOfModules.stalkMap X.ringCatSheaf x ρ))
    (hψ : IsStabilizedOpenExtension T ψ)
    (hdepthOutside : ∀ (V : X.Opens) (H : X.Modules), H.IsCoherent →
      IsIso ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app H) →
      ∀ y : X, y ∉ (V : Set X) →
        letI : Module (X.presheaf.stalk y)
            (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf y) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) H.val y
        (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
          (IsLocalRing.maximalIdeal (X.presheaf.stalk y))
          (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf y)) :
    IsDepthTwoExtension T (ρ ≫ ψ) := by
  unfold IsDepthTwoExtension
  refine ⟨hψ.1, ?_, ?_⟩
  · intro x hx
    obtain ⟨V, hVT, -, hψV, -⟩ := hψ.2 x
    have hxV : x ∈ (V : Set X) := by
      by_contra h
      exact hx (hVT h)
    have h1 : IsIso ((stalkAb X x).map ρ) := isIso_stalkAb_of_isIso_stalkMap ρ x (hρ x hx)
    have h2 : IsIso ((stalkAb X x).map ψ) :=
      isIso_stalkAb_of_isIso_stalkMap ψ x (hψV x hxV)
    have hcomp : (stalkAb X x).map (ρ ≫ ψ) =
        (stalkAb X x).map ρ ≫ (stalkAb X x).map ψ := Functor.map_comp _ _ _
    exact isIso_stalkMap_of_isIso_stalkAb (ρ ≫ ψ) x (hcomp ▸ inferInstance)
  · intro x hx
    obtain ⟨V, -, hxV, -, hunit⟩ := hψ.2 x
    exact hdepthOutside V G hψ.1 hunit x (hxV hx)

/-- **Stacks Project, Tag 0EI3, existence.** A coherent module on a Noetherian scheme admits a
map to a coherent module which is an isomorphism on the stalks away from a
specialization-stable subset and whose stalks on that subset have depth at least two.

Two inputs of the source's proof are carried as hypotheses, because this library does not have
them.

* `hext` asks for the extension of the depth-one quotient of `F` across `T` by sections over the
  opens whose complement lies in `T` — the colimit of the pushforwards `j_{V,*}(F'|_V)` — as a
  coherent module.  Its coherence is what the source derives from Faltings' finiteness criterion
  [Stacks, Tag 0EFD] applied to a dualizing complex, using the hypothesis that `X` locally has
  one and the hypothesis on the depth of `F` at the immediate specializations into `T`.  Those
  two hypotheses of [Stacks, Tag 0EI3] therefore do not appear here.
* `hdepthOutside` is [Stacks, Tag 0EY0] part (3), the converse of
  `AlgebraicGeometry.isIso_unit_restrict_pushforward_of_depth_ge_two`.

The map itself, the clause away from `T` and the depth clause on `T` are proved.  See the
implementation notes of this module. -/
@[stacks 0EI3 "existence, conditional on a coherent stabilized open extension of the depth-one \
quotient along the subset and on Tag 0EY0 part (3)"]
public theorem exists_isDepthTwoExtension
    (X : Scheme.{u}) [IsNoetherian X] (T : Set X) (hT : StableUnderSpecialization T)
    (F : X.Modules) [F.IsCoherent]
    (hdepthOutside : ∀ (V : X.Opens) (H : X.Modules), H.IsCoherent →
      IsIso ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app H) →
      ∀ y : X, y ∉ (V : Set X) →
        letI : Module (X.presheaf.stalk y)
            (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf y) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) H.val y
        (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
          (IsLocalRing.maximalIdeal (X.presheaf.stalk y))
          (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf y))
    (hext : ∃ (G : X.Modules) (ψ : depthOneQuotient X T hT F ⟶ G),
      IsStabilizedOpenExtension T ψ) :
    ∃ (G : X.Modules) (φ : F ⟶ G), IsDepthTwoExtension T φ := by
  obtain ⟨G, ψ, hψ⟩ := hext
  refine ⟨G, toDepthOneQuotient X T hT F ≫ ψ, ?_⟩
  exact isDepthTwoExtension_comp_of_isStabilizedOpenExtension T _ ψ
    (fun x hx => isIso_stalkMap_of_isIso_stalkAb _ x
      ((depthOneQuotient_spec X T hT F).2.2.1 x hx)) hψ hdepthOutside

end AlgebraicGeometry

end
