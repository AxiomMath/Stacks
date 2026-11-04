module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCechVanishingFreeIndexUniverse
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleFaithful
public import StacksFrontier.AlgebraicGeometry.Topologies.AmbientTensorPresheafCechVanishing

/-!
# Čech vanishing at an affine chart for the coefficient presheaf of a bare module

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `W` be an
*affine* étale chart of `F`, let `R = Γ(chartScheme W, 𝒪)` and let `M` be an `R`-module **at an
arbitrary universe `m`**.  This file proves that the higher Čech cohomology of a finite affine
covering family of `W` vanishes, for coefficients an abelian presheaf on the small étale site of
`F` whose restriction to the slice at `W` is identified with the ambient coefficient presheaf
`V ↦ Γ(V.left, 𝒪) ⊗_R M` of `AlgebraicGeometry.overTensorPresheaf`, read on the slice through
`AlgebraicGeometry.Space.SmallEtale.sliceToOver`.

It is `AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_succ_of_associatedPresheafIso`
with the coefficient universe freed.  **That is the whole point.**  That statement is pinned to
`AddCommGrpCat.{u}`, because its coefficients downstairs are the presheaf `𝓕ᵃ` of
[Stacks, Tag 03DS] of a `AlgebraicGeometry.Scheme.Modules`, whose sections live at the universe
`u` of the schemes.  An `𝒪_F`-module at the enlarged module universe `max (u + 1) m` — the
universe in which the tensor products of [Stacks, Tag 09LX] are formed, and at which the
closure clauses of [Stacks, Tag 03M1] are stated — has no such presheaf, and
`AlgebraicGeometry.overTensorPresheaf` is what replaces it: it is built from a *bare* module and
is free in its universe.

## The shape of the transport

It is the one of
`AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_succ_of_associatedPresheafIso`,
verbatim.  The family `{V_i → W}` is lifted one slice by
`AlgebraicGeometry.Space.SmallEtale.sliceHypercoverFreeIndex`, becoming a family in `Over W`
with target the terminal object `Over.mk (𝟙 W)`; `Stacks.CechSite.cechCohomologyIsoOfFunctor`
carries its Čech cohomology down along `CategoryTheory.Over.forget W`, where it is the Čech
cohomology of the original family with coefficients `P`, and over along
`AlgebraicGeometry.Space.SmallEtale.sliceToOver`, where it is the Čech cohomology of a standard
étale covering of schemes over `chartScheme W`.  Both hypotheses of that comparison are
instances of `Stacks.Sites.preservesLimit_fibreProducts_overPost`.

Downstairs the vanishing is
`AlgebraicGeometry.isZero_cechCohomology_succ_overTensorPresheaf`, [Stacks, Tag 03FJ] for these
coefficients, applied at the covered object `sliceToOver` produces.  That object is
`CategoryTheory.Over.mk` of `(-) ⋙ (-)` applied to `𝟙 W`, which is the identity of
`chartScheme W` by the functor law
`AlgebraicGeometry.Space.SmallEtale.sliceToOver_obj_mk_id_hom` and *not* definitionally; the
vanishing downstairs carries exactly that equality as its hypothesis `hg`, so no transport is
needed here.

## The index universe

The covering family is a `CategoryTheory.PreZeroHypercover.{max u m}`, not a
`PreZeroHypercover.{u}`: the Čech complex of a family indexed by `I` is built from products of
the coefficient category of size `I`, and `AddCommGrpCat.{max u m}` has those exactly for index
types in `max u m`.  That is no restriction on a consumer — the Čech criterion of
[Stacks, Tag 03F9] is applied to a cofinal system of coverings which the consumer chooses, and
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_preZeroHypercover_freeIndex` presents
its refinements at whatever index universe is asked for; the slice reading of the family and its
standard étale form are `AlgebraicGeometry.Space.SmallEtale.sliceHypercoverFreeIndex` and
`AlgebraicGeometry.Space.SmallEtale.isStandardCovering_sliceHypercoverFreeIndex_map`, at a free
index universe.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_succ_of_overTensorPresheafIso`:
  **the Čech vanishing**, for an abelian presheaf identified on the slice at `W` with the
  ambient coefficient presheaf of a bare module.

## Implementation notes

**The coefficients enter through an isomorphism, not through a module**, as in the statement
this generalizes: the Čech complex is a functor of the coefficient presheaf on the slice
(`Stacks.CechSite.cechComplexFunctor`), so taking the identification as a hypothesis costs
nothing and is what lets a module form be a corollary.  Producing that identification for the
abelian presheaf underlying an `𝒪_F`-module at the enlarged universe is the remaining step: it
is the comparison `Γ(-, 𝒪) ⊗_R M ⟶ sections` of `Stacks.Sites.tensorToSections`, whose
isomorphism clause at the affine charts is `AlgebraicGeometry.Space.IsCartesianOnAffineCharts`
— `AlgebraicGeometry.Space.sectionsBaseChange` is bijective there — and both of those are still
stated only for the associated presheaf of a `AlgebraicGeometry.Scheme.Modules`.

**No `@[stacks]` attribute is claimed**, for the reason the statement this generalizes gives:
[Stacks, Tag 03FJ] is stated for the three cases of [Stacks, Tag 03FI], all three of which are
already registered in this tree, and the small étale site of an algebraic space is not one of
them.

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 09LX](https://stacks.math.columbia.edu/tag/09LX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CechSite

universe m u

namespace Stacks.CechSite

universe w₀ v₀ u₀ v₁ u₁

variable {C : Type u₀} [Category.{v₀} C] {X : C} (E : PreZeroHypercover.{w₀} X)

/-- **A morphism of coefficient presheaves which is invertible at the iterated fibre products of
the family induces an isomorphism of Čech complexes.**

The degree-`n` term of the Čech complex is the product, over the `(n+1)`-tuples of members, of the
value of the presheaf at the corresponding iterated fibre product, so a comparison of coefficients
invertible *there* is enough and no isomorphism of presheaves on all of `C` is needed.  The
coefficient comparison `Γ(-, 𝒪) ⊗_R M ⟶ ℱ` used below is genuinely not an isomorphism at a
non-affine object of a slice, but it is one at these objects, which are affine. -/
theorem isIso_cechComplexFunctor_map
    {A : Type u₁} [Category.{v₁} A] [HasProducts.{w₀} A] [Preadditive A]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    {P Q : CategoryTheory.Functor Cᵒᵖ A} (τ : P ⟶ Q)
    (h : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      IsIso (τ.app (op ((Over.forget X).obj (∏ᶜ fun a ↦ Over.mk (E.f (i a))))))) :
    IsIso ((cechComplexFunctor E).map τ) := by
  have hdeg : ∀ n : ℕ, IsIso (((cechComplexFunctor E).map τ).f n) := by
    intro n
    have : ∀ i : Fin (n + 1) → E.I₀,
        IsIso (τ.app (op ((Over.forget X).obj (∏ᶜ fun a ↦ Over.mk (E.f (i a)))))) := h n
    exact inferInstanceAs (IsIso (CategoryTheory.Limits.Pi.map
      fun i : Fin (n + 1) → E.I₀ ↦
        τ.app (op ((Over.forget X).obj (∏ᶜ fun a ↦ Over.mk (E.f (i a)))))))
  exact HomologicalComplex.Hom.isIso_of_components _

end Stacks.CechSite

namespace AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (W : SmallEtale B S hS F)

/-- **An iterated fibre product, in the slice at `W`, of a family of affine charts over an
affine chart is again an affine chart.**

This is `AlgebraicGeometry.Space.isAffine_chartScheme_piObj` one slice up: the family is the
slice reading `AlgebraicGeometry.Space.SmallEtale.sliceHypercoverFreeIndex` of `E`, whose fibre
products are taken in `Over (Over.mk (𝟙 W))`, and what comes out affine is the scheme of the
chart two `CategoryTheory.Over.left` projections down.

It is the hypothesis `hτ` of
`AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_succ_of_overTensorPresheafIso` is
applied at, and it is why that hypothesis may be asked only at the affine objects: the Čech
complex of the lifted family evaluates its coefficients exactly at these objects.

The argument is the one of `isAffine_chartScheme_piObj`: the functor taking an object of the
slice to the scheme of its chart preserves the fibre products of the family, by
`Stacks.Sites.preservesLimit_fibreProducts_overPost`, so the product is carried to a finite
product of schemes affine over the affine `chartScheme W`, which is affine. -/
theorem isAffine_chartScheme_sliceHypercover_piObj (hW : IsAffine (chartScheme W))
    (E : PreZeroHypercover.{max u m} W) (haff : ∀ i, IsAffine (chartScheme (E.X i)))
    (p : ℕ) (i : Fin (p + 1) → E.I₀) :
    letI : HasFiniteLimits (Over W) := hasFiniteLimits_of_hasTerminal_and_pullbacks
    letI : HasFiniteLimits (Over (Over.mk (𝟙 W))) :=
      hasFiniteLimits_of_hasTerminal_and_pullbacks
    IsAffine (chartScheme
      (∏ᶜ (fun a ↦ Over.mk ((sliceHypercoverFreeIndex B S hS F W E).f (i a)))).left.left) := by
  let : HasFiniteLimits (Over W) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : HasFiniteLimits (Over (Over.mk (𝟙 W))) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  let v : Over W ⥤ Scheme.{u} :=
    Over.forget W ⋙ SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS
  let A : Fin (p + 1) → Over (Over.mk (𝟙 W)) :=
    fun a ↦ Over.mk ((sliceHypercoverFreeIndex B S hS F W E).f (i a))
  let _ : IsAffine (v.obj (Over.mk (𝟙 W))) := hW
  let _ : PreservesLimit (Discrete.functor A) (Over.post (X := Over.mk (𝟙 W)) v) :=
    Stacks.Sites.preservesLimit_fibreProducts_overPost v (sliceHypercoverFreeIndex B S hS F W E)
      (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) p i
  have haffhom : ∀ a, IsAffineHom ((Over.post (X := Over.mk (𝟙 W)) v).obj (A a)).hom := fun a ↦ by
    let _ : IsAffine ((Over.post (X := Over.mk (𝟙 W)) v).obj (A a)).left := haff (i a)
    exact isAffineHom_of_isAffine _
  let _ : IsAffineHom (∏ᶜ (fun a ↦ (Over.post (X := Over.mk (𝟙 W)) v).obj (A a))).hom :=
    isAffineHom_over_finiteProduct _ haffhom
  have haffprod : IsAffine (∏ᶜ (fun a ↦ (Over.post (X := Over.mk (𝟙 W)) v).obj (A a))).left :=
    isAffine_of_isAffineHom (∏ᶜ (fun a ↦ (Over.post (X := Over.mk (𝟙 W)) v).obj (A a))).hom
  have e : chartScheme (∏ᶜ A).left.left ≅
      (∏ᶜ (fun a ↦ (Over.post (X := Over.mk (𝟙 W)) v).obj (A a))).left :=
    (Over.forget (v.obj (Over.mk (𝟙 W)))).mapIso
      (PreservesProduct.iso (Over.post (X := Over.mk (𝟙 W)) v) A)
  exact IsAffine.of_isIso e.hom

/-- The comparison map of a functor preserving the pullbacks along a family is invertible. -/
private theorem isIso_cechProductMapOfFunctor_of_pullbacks {C D : Type*} [Category* C]
    [Category* D] (u : C ⥤ D) {U : C} (E : PreZeroHypercover U)
    [∀ (j : E.I₀) ⦃W : C⦄ (g : W ⟶ U), HasPullback (E.f j) g]
    [∀ (j : E.I₀) ⦃W : C⦄ (g : W ⟶ U), PreservesLimit (cospan (E.f j) g) u]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [∀ (n : ℕ) (i : Fin (n + 1) → (E.map u).I₀),
      HasProduct (fun a ↦ Over.mk ((E.map u).f (i a)))]
    (n : ℕ) (i : Fin (n + 1) → E.I₀) :
    IsIso (cechProductMapOfFunctor u E n i) :=
  have := Stacks.Sites.preservesLimit_fibreProducts_overPost u E
    (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) n i
  isIso_cechProductMapOfFunctor u E n i

/-- **Čech vanishing in positive degrees for a finite affine covering family of an affine étale
chart of an algebraic space, with coefficients the ambient presheaf `Γ(-, 𝒪) ⊗_R M` of a bare
module.**

This is
`AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_succ_of_associatedPresheafIso` with
the coefficient universe freed: `M` is an `R`-module at an arbitrary universe `m` and the
coefficients are at `AddCommGrpCat.{max u m}`, where that statement has the presheaf `𝓕ᵃ` of a
`AlgebraicGeometry.Scheme.Modules` and hence coefficients at `u`.

The transport is unchanged — the family is lifted one slice by
`AlgebraicGeometry.Space.SmallEtale.sliceHypercoverFreeIndex` and
`Stacks.CechSite.cechCohomologyIsoOfFunctor` carries its Čech cohomology both down along
`CategoryTheory.Over.forget W` and over along
`AlgebraicGeometry.Space.SmallEtale.sliceToOver` — and the vanishing downstairs is
`AlgebraicGeometry.isZero_cechCohomology_succ_overTensorPresheaf`, whose hypothesis that the
covered object's structure morphism is the identity is
`AlgebraicGeometry.Space.SmallEtale.sliceToOver_obj_mk_id_hom`.

**The coefficient comparison is asked for pointwise, at the affine objects of the slice only,
and not as an isomorphism of presheaves.**  That is forced: the comparison
`Γ(-, 𝒪) ⊗_R M ⟶ ℱ` is genuinely not an isomorphism at a non-affine object étale over an
affine one, so a hypothesis in the shape of a `CategoryTheory.NatIso` on the whole slice would
be unavailable to the module form (see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSections.lean` for the example, and
`AlgebraicGeometry.Space.SmallEtale.tensorToChartSections` for the comparison).  Nothing is
lost: the Čech complex of the lifted family evaluates its coefficients only at the iterated
fibre products of the members, those are affine by
`AlgebraicGeometry.Space.SmallEtale.isAffine_chartScheme_sliceHypercover_piObj`, and
`Stacks.CechSite.isIso_cechComplexFunctor_map` turns the pointwise invertibility into the
isomorphism of Čech complexes that the transport needs. -/
theorem isZero_cechCohomology_succ_of_overTensorPresheafIso
    (hW : IsAffine (chartScheme W))
    (E : PreZeroHypercover.{max u m} W) (hfin : Finite E.I₀)
    (haff : ∀ i, IsAffine (chartScheme (E.X i)))
    (hcov : E.sieve₀ ∈ topology B S hS F W)
    (M : Type m) [AddCommGroup M]
    [Module (Scheme.Γ.obj (op (chartScheme W)) : Type u) M]
    (P : (SmallEtale B S hS F)ᵒᵖ ⥤ AddCommGrpCat.{max u m})
    (τ : (sliceToOver B S hS F W).op ⋙ overTensorPresheaf (chartScheme W) M ⟶
      (Over.forget W).op ⋙ P)
    (hτ : ∀ Z : Over W, IsAffine (chartScheme Z.left) → IsIso (τ.app (op Z)))
    (p : ℕ) (hp : 0 < p) :
    letI : HasFiniteLimits (Over W) := hasFiniteLimits_of_hasTerminal_and_pullbacks
    IsZero (cechCohomology E P p) := by
  let : HasFiniteLimits (Over W) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : IsAffine (chartScheme W) := hW
  let : HasFiniteLimits (Over (Over.mk (𝟙 W))) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : IsAffine ((sliceToOver B S hS F W).obj (Over.mk (𝟙 W))).left := hW
  let : HasFiniteLimits (Over ((sliceToOver B S hS F W).obj (Over.mk (𝟙 W)))) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  -- The products the Čech complex of the pushed-down family needs sit over
  -- `(Over.forget W).obj (Over.mk (𝟙 W))`, which is `W` but not syntactically so.
  let hpW : ∀ (n : ℕ)
      (i : Fin (n + 1) → ((sliceHypercoverFreeIndex B S hS F W E).map (Over.forget W)).I₀),
      HasProduct (fun a ↦
        Over.mk (((sliceHypercoverFreeIndex B S hS F W E).map (Over.forget W)).f (i a))) :=
    fun n i ↦ (inferInstance : HasProduct (fun a ↦ Over.mk (E.f (i a))))
  have hforget := isIso_cechProductMapOfFunctor_of_pullbacks (Over.forget W)
    (sliceHypercoverFreeIndex B S hS F W E)
  have hslice := isIso_cechProductMapOfFunctor_of_pullbacks (sliceToOver B S hS F W)
    (sliceHypercoverFreeIndex B S hS F W E)
  have hslicezero : IsZero (cechCohomology (sliceHypercoverFreeIndex B S hS F W E)
      ((sliceToOver B S hS F W).op ⋙ overTensorPresheaf (chartScheme W) M) p) :=
    (isZero_cechCohomology_succ_overTensorPresheaf (chartScheme W) M
      (sliceToOver_obj_mk_id_hom B S hS F W) .etale
      ((sliceHypercoverFreeIndex B S hS F W E).map (sliceToOver B S hS F W))
      (isStandardCovering_sliceHypercoverFreeIndex_map B S hS F W hW E hfin haff hcov) p
      hp).of_iso (cechCohomologyIsoOfFunctor (sliceToOver B S hS F W)
      (sliceHypercoverFreeIndex B S hS F W E)
      (overTensorPresheaf (chartScheme W) M) hslice p).symm
  have hτiso : IsIso ((Stacks.CechSite.cechComplexFunctor
      (sliceHypercoverFreeIndex B S hS F W E)).map τ) :=
    isIso_cechComplexFunctor_map (sliceHypercoverFreeIndex B S hS F W E) τ fun n i ↦
      hτ _ (isAffine_chartScheme_sliceHypercover_piObj B S hS F W hW E haff n i)
  have hcoeff : IsZero (cechCohomology (sliceHypercoverFreeIndex B S hS F W E)
      ((Over.forget W).op ⋙ P) p) :=
    hslicezero.of_iso
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u m} (ComplexShape.up ℕ) p).mapIso
        (asIso ((Stacks.CechSite.cechComplexFunctor
          (sliceHypercoverFreeIndex B S hS F W E)).map τ))).symm
  exact hcoeff.of_iso (cechCohomologyIsoOfFunctor (Over.forget W)
    (sliceHypercoverFreeIndex B S hS F W E) P hforget p)

end AlgebraicGeometry.Space.SmallEtale

end
