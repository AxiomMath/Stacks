module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.AdicSheaves
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorTriangleShortExact
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers
public import StacksFrontier.Homology.DerivedComplete.NormalizedDerivedLimitMilnor
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.Equivalence
public import StacksFrontier.RingTheory.LocalCohomology.AffineLocalizationTriangle
import StacksFrontier.RingTheory.Dualizing.TorsionComplete.AdicQuotientComparison
import StacksFrontier.RingTheory.LocalCohomology.CechFormula.Basic

/-!
# Completed local cohomology as a derived limit of the local cohomology of the adic quotients

Let `I` and `J` be ideals of a Noetherian ring `A`, let `M` be a finite `A`-module and let
`Z = V(J)`. The derived `I`-adic completion of `RΓ_Z(M)` is the derived inverse limit of the
tower `n ↦ RΓ_Z(M/IⁿM)`. Two different ideals occur: `J` cuts out the support `Z` and hence
determines `RΓ_Z`, while `I` is the ideal with respect to which the completion is taken.

This file records the tower `n ↦ RΓ_Z(M/IⁿM)` and the two consequences of the derived-limit
identification. The Milnor short exact sequences
`0 → R¹lim H^{i-1}_Z(M/IⁿM) → Hⁱ(RΓ_Z(M)^∧) → lim Hⁱ_Z(M/IⁿM) → 0`
come from the long exact cohomology sequence of the triangle presenting a derived limit, and the
vanishing of `Hⁱ(RΓ_Z(M)^∧)` for `i < 0` follows because every term of the tower has no
cohomology in negative degrees, so neither does the product of the terms, and the first map of
the presenting triangle is a monomorphism on cohomology in those degrees.

## Main definitions

* `Dualizing.adicQuotientLocalCohomologySystem` — the tower `n ↦ RΓ_Z(M/IⁿM)` in `D(A)`.
* `Dualizing.adicQuotientLocalCohomologyCone` — the cone on `n ↦ Hⁱ_Z(M/IⁿM)` induced by a cone
  of maps into the tower.
* `Dualizing.completedLocalCohomologyToLimit` — the comparison map
  `Hⁱ(RΓ_Z(M)^∧) ⟶ lim Hⁱ_Z(M/IⁿM)` of a derived limit of the tower.
* `Dualizing.completedLocalCohomologyToLimitOfProjections` — the same map, as the canonical map
  into the limit determined by given projections of the derived limit.

## Main results

* `Dualizing.exists_isDerivedLimit_adicQuotientLocalCohomologySystem` — the tower has a derived
  limit, so the two results below are statements about `R lim RΓ_Z(M/IⁿM)`.
* `Dualizing.isGE_adicQuotientLocalCohomologySystem_obj` — every term of the tower has vanishing
  cohomology in negative degrees.
* `Dualizing.exists_milnor_shortExact_of_isDerivedLimit` — the Milnor short exact sequences of
  Tag 0EEW part (2), for any derived limit of the tower.
* `Dualizing.completedLocalCohomologyToLimit_shortExact` — the same sequence, with its right-hand
  map named.
* `Dualizing.completedLocalCohomologyToLimit_comp_limit_π` — the characterizing property of that
  map: its composites with the limit projections are the projections of the derived limit.
* `Dualizing.map_comp_completedLocalCohomologyToLimit` and
  `Dualizing.map_comp_completedLocalCohomologyToLimit_eq_limitLift` — the comparison map
  normalized against a map `X ⟶ R lim RΓ_Z(M/IⁿM)`: precomposed with `Hʳ` of that map it is the
  canonical map into the limit induced by the composites with the projections.
* `Dualizing.isZero_homology_of_isDerivedLimit_of_neg` — the negative-degree vanishing of
  Tag 0EEW.
* `Dualizing.isDerivedLimit_completedLocalCohomology` — Tag 0EEW part (1): `RΓ_Z(M)^∧` is a
  derived limit of the tower.
* `Dualizing.exists_milnor_shortExact_completedLocalCohomology` and
  `Dualizing.isZero_homology_completedLocalCohomology_of_neg` — the same two conclusions for
  `RΓ_Z(M)^∧` itself, under the hypotheses of the tag.

## Implementation notes

Part (1) is proved by `Dualizing.isDerivedLimit_completedLocalCohomology`, through the Čech
formula for `RΓ_Z` and the pro-isomorphism between the ideal-power tensor tower and the tower of
ordinary quotients recorded in
`StacksFrontier/RingTheory/Dualizing/TorsionComplete/AdicQuotientComparison.lean`. Parts (2) and
(3) are proved here for every derived limit of the tower, so they are unconditional statements
about `R lim RΓ_Z(M/IⁿM)`. The statements that mention `Dualizing.derivedCompletion` still carry
the derived-limit identification as the hypothesis `hcompletion`, because that is the shape their
consumers use; `Dualizing.isDerivedLimit_completedLocalCohomology` is exactly what discharges it.

The comparison map of part (2) takes the projections of the derived limit as an explicit
argument, and is then the canonical map into the limit that they determine; it is not a function
of the derived-limit property alone. Two defining triangles over the same object differ by an
automorphism of it, and `-1` is such an automorphism, so the derived-limit property does not
determine the projections even up to sign, and hence does not determine this map. That is why
`Dualizing.completedLocalCohomologyToLimitOfProjections` and the normalization lemmas take the
projections they are about as an argument.

The results about an abstract derived limit of the tower need neither `A` Noetherian nor `M`
finite; those hypotheses are what part (1) consumes, and they are carried by the two statements
about `RΓ_Z(M)^∧`, which are the tag's own. The module universe equals the ring universe, which
is where the Čech model of `RΓ_Z` lives.

## References

* [Stacks Project, Tag 0EEW](https://stacks.math.columbia.edu/tag/0EEW)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 07KY](https://stacks.math.columbia.edu/tag/07KY)
* [Stacks Project, Tag 0922](https://stacks.math.columbia.edu/tag/0922)
* [Stacks Project, Tag 0EET](https://stacks.math.columbia.edu/tag/0EET)
* [Stacks Project, Tag 0911](https://stacks.math.columbia.edu/tag/0911)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-! ### Countable limits and products

Every section below needs countable limits in `ModuleCat A` to be exact and countable products
to exist in `D(A)`. Exactness of countable limits comes from the global instance
`moduleCat_hasExactLimitsOfShape_discrete`; countable products in `D(A)` are declared once below,
with explicit binders rather than section variables, so that the three sections share them.
-/

attribute [local instance] Dualizing.AdicQuotientComparison.derivedCategoryHasProductsNat
section Tower

variable (A : Type u) [CommRing A]

/-- The tower `n ↦ RΓ_Z(M/IⁿM)` of local cohomology with support in `Z = V(J)` of the `I`-adic
quotients of `M`, as an inverse system in `D(A)`. -/
def adicQuotientLocalCohomologySystem (I J : Ideal A) (hJ : J.FG) (M : ModuleCat.{u} A) :
    ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
  AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M ⋙
    DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
      Stacks.LocalCohomology.localCohomologyDerived A J hJ

/-- The tower `n ↦ RΓ_Z(M/IⁿM)` has a derived limit: countable products exist in `D(A)`, so the
difference map `1 - shift` on the product of the terms sits in a distinguished triangle. -/
@[stacks 0EEW "the tower of local cohomologies has a derived limit"]
theorem exists_isDerivedLimit_adicQuotientLocalCohomologySystem (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) :
    ∃ K : DerivedCategory (ModuleCat.{u} A),
      IsDerivedLimit (adicQuotientLocalCohomologySystem A I J hJ M) K :=
  exists_isDerivedLimit _

/-- **Local cohomology of a module has no negative cohomology.** Every term of the tower
`n ↦ RΓ_Z(M/IⁿM)` is supported in degrees `≥ 0`. -/
theorem isGE_adicQuotientLocalCohomologySystem_obj (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) (n : ℕᵒᵖ) :
    ((adicQuotientLocalCohomologySystem A I J hJ M).obj n).IsGE 0 :=
  (DerivedCategory.isGE_iff _ 0).2 fun i hi ↦
    Stacks.LocalCohomology.isZero_localCohomologyModule_of_neg A J hJ
      ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M).obj n) i hi

/-- The product of the terms of the tower has no cohomology in negative degrees, since the
comparison map from the cohomology of a countable product in `D(A)` to the product of the
cohomologies is invertible. -/
theorem isZero_homology_pi_adicQuotientLocalCohomologySystem (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) (i : ℤ) (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (∏ᶜ fun n : ℕ ↦ (adicQuotientLocalCohomologySystem A I J hJ M).obj ⟨n⟩)) := by
  set X : ℕ → DerivedCategory (ModuleCat.{u} A) := fun n ↦
    (adicQuotientLocalCohomologySystem A I J hJ M).obj ⟨n⟩ with hX
  have := Stacks.DerivedProducts.isIso_piComparison_homologyFunctor X i
  refine IsZero.of_iso ?_ (asIso (piComparison (DerivedCategory.homologyFunctor _ i) X))
  rw [IsZero.iff_id_eq_zero]
  refine Pi.hom_ext _ _ fun n ↦ ?_
  have := isGE_adicQuotientLocalCohomologySystem_obj A I J hJ M ⟨n⟩
  exact (DerivedCategory.isZero_of_isGE (X n) 0 i hi).eq_of_tgt _ _

end Tower

section Consequences

variable (A : Type u) [CommRing A]

/-- **Stacks 0EEW, part (2), for an arbitrary derived limit of the tower.** The cohomology of a
derived limit of `n ↦ RΓ_Z(M/IⁿM)` sits in a short exact sequence between the first derived
limit `R¹lim H^{r-1}_Z(M/IⁿM)`, presented as the cokernel of one minus shift, and the inverse
limit `lim Hʳ_Z(M/IⁿM)`. The inclusion is the connecting morphism of the presenting triangle and
the projection is characterized by its composites with the limit projections. -/
@[stacks 0EEW "the Milnor short exact sequence for the tower"]
theorem exists_milnor_shortExact_of_isDerivedLimit (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsDerivedLimit (adicQuotientLocalCohomologySystem A I J hJ M) K) :
    let F := adicQuotientLocalCohomologySystem A I J hJ M
    let X : ℕ → DerivedCategory (ModuleCat.{u} A) := fun n ↦ F.obj (Opposite.op n)
    let d : (∏ᶜ X) ⟶ ∏ᶜ X := Pi.lift fun n : ℕ ↦
      Pi.π X n - Pi.π X (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
    ∃ (a : K ⟶ ∏ᶜ X) (b : (∏ᶜ X) ⟶ K⟦(1 : ℤ)⟧),
      let T := Pretriangulated.Triangle.mk a d b
      T ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) ∧
        ∀ r : ℤ,
          let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) r
          let H₁ := DerivedCategory.homologyFunctor (ModuleCat.{u} A) (r - 1)
          let homologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A := F ⋙ H
          let shiftedHomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A := F ⋙ H₁
          let P : ModuleCat.{u} A :=
            ∏ᶜ fun n : ℕ ↦ shiftedHomologySystem.obj (Opposite.op n)
          let δ : P ⟶ P := Pi.lift fun n : ℕ ↦
            Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (Opposite.op n)) n -
              Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (Opposite.op n)) (n + 1) ≫
                shiftedHomologySystem.map (homOfLE (Nat.le_succ n)).op
          ∃ (e : H₁.obj (∏ᶜ X) ≅ P)
            (i : cokernel δ ⟶ H.obj K) (q : H.obj K ⟶ limit homologySystem)
            (w : i ≫ q = 0),
            e.hom = piComparison H₁ X ∧
              cokernel.π δ ≫ i = e.inv ≫
                DerivedCategory.HomologySequence.δ T (r - 1) r ∧
              (∀ n : ℕ, q ≫ limit.π homologySystem (Opposite.op n) =
                H.map a ≫ H.map (Pi.π X n)) ∧
              (ShortComplex.mk i q w).ShortExact :=
  DerivedCategory.isDerivedLimit_homology_shortExact _ K hK

/-- A family of maps `X ⟶ RΓ_Z(M/IⁿM)` compatible with the transition maps of the tower induces,
on degree-`r` cohomology, a cone on the tower `n ↦ Hʳ_Z(M/IⁿM)`. -/
def adicQuotientLocalCohomologyCone (I J : Ideal A) (hJ : J.FG) (M : ModuleCat.{u} A)
    {X : DerivedCategory (ModuleCat.{u} A)}
    (γ : ∀ n : ℕ, X ⟶ (adicQuotientLocalCohomologySystem A I J hJ M).obj ⟨n⟩)
    (hγ : ∀ n : ℕ, γ (n + 1) ≫
      (adicQuotientLocalCohomologySystem A I J hJ M).map (homOfLE (Nat.le_succ n)).op = γ n)
    (r : ℤ) :
    Cone (adicQuotientLocalCohomologySystem A I J hJ M ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) r) :=
  DerivedCategory.derivedLimitHomologyCone (adicQuotientLocalCohomologySystem A I J hJ M) γ hγ r

/-- The `n`-th leg of `adicQuotientLocalCohomologyCone` is the map induced by `γ n` on degree-`r`
cohomology. -/
@[simp]
theorem adicQuotientLocalCohomologyCone_π (I J : Ideal A) (hJ : J.FG) (M : ModuleCat.{u} A)
    {X : DerivedCategory (ModuleCat.{u} A)}
    (γ : ∀ n : ℕ, X ⟶ (adicQuotientLocalCohomologySystem A I J hJ M).obj ⟨n⟩)
    (hγ : ∀ n : ℕ, γ (n + 1) ≫
      (adicQuotientLocalCohomologySystem A I J hJ M).map (homOfLE (Nat.le_succ n)).op = γ n)
    (r : ℤ) (n : ℕ) :
    (adicQuotientLocalCohomologyCone A I J hJ M γ hγ r).π.app (Opposite.op n) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map (γ n) :=
  rfl

/-- **The comparison map of Stacks 0EEW, part (2).** The map from the degree-`r` cohomology of a
derived limit of `n ↦ RΓ_Z(M/IⁿM)` to the inverse limit of the modules `Hʳ_Z(M/IⁿM)`. -/
def completedLocalCohomologyToLimit (I J : Ideal A) (hJ : J.FG) (M : ModuleCat.{u} A)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsDerivedLimit (adicQuotientLocalCohomologySystem A I J hJ M) K) (r : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).obj K ⟶
      limit (adicQuotientLocalCohomologySystem A I J hJ M ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) r) := by
  classical
  let h := exists_milnor_shortExact_of_isDerivedLimit A I J hJ M K hK
  let hb := Classical.choose_spec h
  let hdata := (Classical.choose_spec hb).2 r
  let he := Classical.choose_spec hdata
  let hi := Classical.choose_spec he
  exact Classical.choose hi


/-- **The comparison map of Stacks 0EEW, part (2).** The map from the degree-`r` cohomology of a
derived limit of `n ↦ RΓ_Z(M/IⁿM)` to the inverse limit of the modules `Hʳ_Z(M/IⁿM)`: the
canonical map into the limit induced by the projections of the derived limit.

The projections are an explicit argument. A derived limit is unique only up to non-unique
isomorphism, and two defining triangles over the same object differ by an automorphism of it —
for instance `-1`, which negates the projections and hence this map. So the projections, and not
merely the derived-limit property, are what a statement identifying this map must fix. -/
def completedLocalCohomologyToLimitOfProjections (I J : Ideal A) (hJ : J.FG) (M : ModuleCat.{u} A)
    {K : DerivedCategory (ModuleCat.{u} A)}
    (p : ∀ n : ℕ, K ⟶ (adicQuotientLocalCohomologySystem A I J hJ M).obj ⟨n⟩)
    (hp : ∀ n : ℕ, p (n + 1) ≫
      (adicQuotientLocalCohomologySystem A I J hJ M).map (homOfLE (Nat.le_succ n)).op = p n)
    (r : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).obj K ⟶
      limit (adicQuotientLocalCohomologySystem A I J hJ M ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) r) :=
  DerivedCategory.derivedLimitHomologyToLimit
    (adicQuotientLocalCohomologySystem A I J hJ M) p hp r

/-- **The characterizing property of the comparison map of Stacks 0EEW, part (2).** Its composite
with the `n`-th projection of the limit is the `n`-th projection of the derived limit, on
degree-`r` cohomology. -/
@[reassoc]
theorem completedLocalCohomologyToLimit_comp_limit_π (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) {K : DerivedCategory (ModuleCat.{u} A)}
    (p : ∀ n : ℕ, K ⟶ (adicQuotientLocalCohomologySystem A I J hJ M).obj ⟨n⟩)
    (hp : ∀ n : ℕ, p (n + 1) ≫
      (adicQuotientLocalCohomologySystem A I J hJ M).map (homOfLE (Nat.le_succ n)).op = p n)
    (r : ℤ) (n : ℕ) :
    completedLocalCohomologyToLimitOfProjections A I J hJ M p hp r ≫
        limit.π (adicQuotientLocalCohomologySystem A I J hJ M ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) r) (Opposite.op n) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map (p n) :=
  DerivedCategory.derivedLimitHomologyToLimit_comp_limit_π
    (adicQuotientLocalCohomologySystem A I J hJ M) p hp r n

/-- **Stacks 0EEW, part (2), normalized against a map into the derived limit.** For any
`η : X ⟶ K`, the comparison map precomposed with `Hʳ(η)` is *the* map into the limit whose
composite with the `n`-th limit projection is `Hʳ(η ≫ pₙ)`.

With `K = RΓ_Z(M)^∧`, `η` the completion unit and `η ≫ pₙ` the map `RΓ_Z(M) ⟶ RΓ_Z(M/IⁿM)`
induced by `M ↠ M/IⁿM`, this is the normalization of the comparison map against the completion
unit: the left-hand side is `Hʳ` of the unit followed by the comparison map, and `c` is the
canonical map `Hʳ_Z(M) ⟶ lim Hʳ_Z(M/IⁿM)` induced by the quotient projections. -/
theorem map_comp_completedLocalCohomologyToLimit (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) {K : DerivedCategory (ModuleCat.{u} A)}
    (p : ∀ n : ℕ, K ⟶ (adicQuotientLocalCohomologySystem A I J hJ M).obj ⟨n⟩)
    (hp : ∀ n : ℕ, p (n + 1) ≫
      (adicQuotientLocalCohomologySystem A I J hJ M).map (homOfLE (Nat.le_succ n)).op = p n) (r : ℤ)
    {X : DerivedCategory (ModuleCat.{u} A)} (η : X ⟶ K)
    (γ : ∀ n : ℕ, X ⟶ (adicQuotientLocalCohomologySystem A I J hJ M).obj ⟨n⟩)
    (c : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).obj X ⟶
      limit (adicQuotientLocalCohomologySystem A I J hJ M ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) r))
    (hc : ∀ n : ℕ, c ≫ limit.π (adicQuotientLocalCohomologySystem A I J hJ M ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) r) (Opposite.op n) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map (γ n))
    (hη : ∀ n : ℕ, η ≫ p n = γ n) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map η ≫
        completedLocalCohomologyToLimitOfProjections A I J hJ M p hp r = c :=
  DerivedCategory.map_comp_derivedLimitHomologyToLimit
    (adicQuotientLocalCohomologySystem A I J hJ M) p hp r η γ c hc hη

/-- **Stacks 0EEW, part (2), normalized against a map into the derived limit**, with the map into
the limit written as the lift of the cone of the composites `η ≫ pₙ`. -/
theorem map_comp_completedLocalCohomologyToLimit_eq_limitLift (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) {K : DerivedCategory (ModuleCat.{u} A)}
    (p : ∀ n : ℕ, K ⟶ (adicQuotientLocalCohomologySystem A I J hJ M).obj ⟨n⟩)
    (hp : ∀ n : ℕ, p (n + 1) ≫
      (adicQuotientLocalCohomologySystem A I J hJ M).map (homOfLE (Nat.le_succ n)).op = p n) (r : ℤ)
    {X : DerivedCategory (ModuleCat.{u} A)} (η : X ⟶ K)
    (γ : ∀ n : ℕ, X ⟶ (adicQuotientLocalCohomologySystem A I J hJ M).obj ⟨n⟩)
    (hγ : ∀ n : ℕ, γ (n + 1) ≫
      (adicQuotientLocalCohomologySystem A I J hJ M).map (homOfLE (Nat.le_succ n)).op = γ n)
    (hη : ∀ n : ℕ, η ≫ p n = γ n) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map η ≫
        completedLocalCohomologyToLimitOfProjections A I J hJ M p hp r =
      limit.lift _ (adicQuotientLocalCohomologyCone A I J hJ M γ hγ r) :=
  map_comp_completedLocalCohomologyToLimit A I J hJ M p hp r η γ _
    (fun n ↦ limit.lift_π (adicQuotientLocalCohomologyCone A I J hJ M γ hγ r) (Opposite.op n)) hη

/-- The named comparison map is the right-hand map of a short exact sequence whose left-hand term
is the first derived limit `R¹lim H^{r-1}_Z(M/IⁿM)`. -/
theorem completedLocalCohomologyToLimit_shortExact (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsDerivedLimit (adicQuotientLocalCohomologySystem A I J hJ M) K) (r : ℤ) :
    let F := adicQuotientLocalCohomologySystem A I J hJ M
    let H₁ := DerivedCategory.homologyFunctor (ModuleCat.{u} A) (r - 1)
    let P : ModuleCat.{u} A := ∏ᶜ fun n : ℕ ↦ (F ⋙ H₁).obj (Opposite.op n)
    let δ : P ⟶ P := Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ (F ⋙ H₁).obj (Opposite.op n)) n -
        Pi.π (fun n : ℕ ↦ (F ⋙ H₁).obj (Opposite.op n)) (n + 1) ≫
          (F ⋙ H₁).map (homOfLE (Nat.le_succ n)).op
    ∃ (i : cokernel δ ⟶ (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).obj K)
      (w : i ≫ completedLocalCohomologyToLimit A I J hJ M K hK r = 0),
      (ShortComplex.mk i (completedLocalCohomologyToLimit A I J hJ M K hK r) w).ShortExact := by
  classical
  let h := exists_milnor_shortExact_of_isDerivedLimit A I J hJ M K hK
  let hb := Classical.choose_spec h
  let hdata := (Classical.choose_spec hb).2 r
  let he := Classical.choose_spec hdata
  let hi := Classical.choose_spec he
  let hw := Classical.choose_spec hi
  exact ⟨Classical.choose he, Classical.choose hw, (Classical.choose_spec hw).2.2.2⟩


/-- The named comparison map is the right-hand map of a short exact sequence whose left-hand term
is the first derived limit `R¹lim H^{r-1}_Z(M/IⁿM)`. -/
theorem completedLocalCohomologyToLimitOfProjections_shortExact (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) {K : DerivedCategory (ModuleCat.{u} A)}
    (p : ∀ n : ℕ, K ⟶ (adicQuotientLocalCohomologySystem A I J hJ M).obj ⟨n⟩)
    (hK : NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (adicQuotientLocalCohomologySystem A I J hJ M) K p) (r : ℤ) :
    let q := completedLocalCohomologyToLimitOfProjections A I J hJ M p
      (NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_map_succ hK) r
    let F := adicQuotientLocalCohomologySystem A I J hJ M
    let H₁ := DerivedCategory.homologyFunctor (ModuleCat.{u} A) (r - 1)
    let P : ModuleCat.{u} A := ∏ᶜ fun n : ℕ ↦ (F ⋙ H₁).obj (Opposite.op n)
    let δ : P ⟶ P := Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ (F ⋙ H₁).obj (Opposite.op n)) n -
        Pi.π (fun n : ℕ ↦ (F ⋙ H₁).obj (Opposite.op n)) (n + 1) ≫
          (F ⋙ H₁).map (homOfLE (Nat.le_succ n)).op
    ∃ (i : cokernel δ ⟶ (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).obj K)
      (w : i ≫ q = 0), (ShortComplex.mk i q w).ShortExact := by
  obtain ⟨-, -, -, i, w, -, -, hse⟩ :=
    DerivedCategory.exists_milnor_shortExact_of_isDerivedLimitWithProjections
      (adicQuotientLocalCohomologySystem A I J hJ M) p hK r
  exact ⟨i, w, hse⟩

/-- **Stacks 0EEW, the negative-degree vanishing, for an arbitrary derived limit of the tower.**
A derived limit of `n ↦ RΓ_Z(M/IⁿM)` has no cohomology in negative degrees. -/
@[stacks 0EEW "vanishing in negative degrees"]
theorem isZero_homology_of_isDerivedLimit_of_neg (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsDerivedLimit (adicQuotientLocalCohomologySystem A I J hJ M) K) (i : ℤ) (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) := by
  obtain ⟨a, b, hT⟩ := hK
  have hP : ∀ j : ℤ, j < 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
        (∏ᶜ fun n : ℕ ↦ (adicQuotientLocalCohomologySystem A I J hJ M).obj ⟨n⟩)) := fun j hj ↦
    isZero_homology_pi_adicQuotientLocalCohomologySystem A I J hJ M j hj
  have hmono : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map a) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hT (i - 1) i (by omega)).2
      ((hP (i - 1) (by omega)).eq_of_src _ _)
  exact (hP i hi).of_mono ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map a)

end Consequences

section Completion

variable (A : Type u) [CommRing A]

/-- The derived `I`-adic completion of `RΓ_Z(M)`, as an object of `D(A)`: the object denoted
`RΓ_Z(M)^∧` in Tag 0EEW. -/
def completedLocalCohomology (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (M : ModuleCat.{u} A) :
    DerivedCategory (ModuleCat.{u} A) :=
  (derivedCompleteProperty A I).ι.obj ((derivedCompletion A I hI).obj
    ((Stacks.LocalCohomology.localCohomologyDerived A J hJ).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)))

/-- **Stacks 0EEW, part (1).** The derived `I`-adic completion of `RΓ_Z(M)` is a derived limit
of the tower `n ↦ RΓ_Z(M/IⁿM)`.

The Čech formula for local cohomology replaces `RΓ_Z` by `C(g) ⊗ᴸ -`, where `C(g)` is the
extended alternating Čech complex of a finite generating family of `J`. Derived `I`-adic
completion of `C(g) ⊗ᴸ M` is the derived limit of the tower `n ↦ (C(g) ⊗ᴸ M) ⊗ᴸ A/Iⁿ`
(Tag 0EET), and associativity of the derived tensor product rewrites that tower as
`n ↦ C(g) ⊗ᴸ (M ⊗ᴸ A/Iⁿ)`. The comparison with the tower of ordinary quotients
`n ↦ C(g) ⊗ᴸ (M/IⁿM)` is a pro-isomorphism, because the fibres only carry the Tor modules
`Torᵢ(M, A/Iⁿ)` and those are pro-zero over a Noetherian ring for a finite module
(Tag 0911). -/
@[stacks 0EEW "part (1): the derived I-adic completion of RΓ_J(M) is R lim RΓ_J(M/IⁿM)"]
theorem isDerivedLimit_completedLocalCohomology [IsNoetherianRing A]
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (M : ModuleCat.{u} A) [Module.Finite A M] :
    IsDerivedLimit (adicQuotientLocalCohomologySystem A I J hJ M)
      (completedLocalCohomology A I J hI hJ M) := by
  classical
  obtain ⟨s, fJ, hfJ⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hJ
  change Ideal.span (Set.range fJ) = J at hfJ
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  let C := Stacks.LocalCohomology.CechFormula.cechRegularObject.{u, u} fJ
  let eCech := Stacks.LocalCohomology.CechFormula.localCohomologyCechIso A J hJ fJ hfJ
  let K₀ := (T.tensor.obj C).obj (S.obj M)
  obtain ⟨L, ⟨adjL⟩, hL, -, -⟩ :=
    AdicCompletionTor.derivedCompletion_homology_shortExact A I T
  have e₁ : (derivedCompleteProperty A I).ι.obj (L.obj K₀) ≅
      (derivedCompleteProperty A I).ι.obj ((derivedCompletion A I hI).obj K₀) :=
    (derivedCompleteProperty A I).ι.mapIso
      ((adjL.leftAdjointUniq (derivedCompletionReflection A I hI).2).app K₀)
  have e₂ : completedLocalCohomology A I J hI hJ M ≅
      (derivedCompleteProperty A I).ι.obj ((derivedCompletion A I hI).obj K₀) :=
    (derivedCompletion A I hI ⋙ (derivedCompleteProperty A I).ι).mapIso (eCech.app (S.obj M))
  have hlim : IsDerivedLimit
      (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K₀)
      (completedLocalCohomology A I J hI hJ M) :=
    AdicQuotientComparison.isDerivedLimit_of_iso (e₁ ≪≫ e₂.symm) (hL K₀)
  have hmain := AdicQuotientComparison.isDerivedLimit_tensor_adicQuotient A I hI M C
    (completedLocalCohomology A I J hI hJ M) hlim
  exact AdicQuotientComparison.isDerivedLimit_of_natIso
    (Functor.isoWhiskerLeft (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M)
      (Functor.isoWhiskerLeft S eCech.symm)) hmain

/-- **Stacks 0EEW, part (2), for the completion.** Granting part (1) in the form
`hcompletion`, the cohomology of `RΓ_Z(M)^∧` sits in the Milnor short exact sequence between
`R¹lim H^{r-1}_Z(M/IⁿM)` and `lim Hʳ_Z(M/IⁿM)`. -/
theorem exists_milnor_shortExact_completedLocalCohomology [IsNoetherianRing A]
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (M : ModuleCat.{u} A) [Module.Finite A M]
    (hcompletion : IsDerivedLimit (adicQuotientLocalCohomologySystem A I J hJ M)
      (completedLocalCohomology A I J hI hJ M)) (r : ℤ) :
    let F := adicQuotientLocalCohomologySystem A I J hJ M
    let K := completedLocalCohomology A I J hI hJ M
    let H₁ := DerivedCategory.homologyFunctor (ModuleCat.{u} A) (r - 1)
    let P : ModuleCat.{u} A := ∏ᶜ fun n : ℕ ↦ (F ⋙ H₁).obj (Opposite.op n)
    let δ : P ⟶ P := Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ (F ⋙ H₁).obj (Opposite.op n)) n -
        Pi.π (fun n : ℕ ↦ (F ⋙ H₁).obj (Opposite.op n)) (n + 1) ≫
          (F ⋙ H₁).map (homOfLE (Nat.le_succ n)).op
    ∃ (i : cokernel δ ⟶ (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).obj K)
      (w : i ≫ completedLocalCohomologyToLimit A I J hJ M K hcompletion r = 0),
      (ShortComplex.mk i
        (completedLocalCohomologyToLimit A I J hJ M K hcompletion r) w).ShortExact :=
  completedLocalCohomologyToLimit_shortExact A I J hJ M _ hcompletion r


/-- **Stacks 0EEW, the negative-degree vanishing, for the completion.** Granting part (1) in the
form `hcompletion`, the completion `RΓ_Z(M)^∧` has vanishing cohomology in negative degrees. -/
theorem isZero_homology_completedLocalCohomology_of_neg [IsNoetherianRing A]
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (M : ModuleCat.{u} A) [Module.Finite A M]
    (hcompletion : IsDerivedLimit (adicQuotientLocalCohomologySystem A I J hJ M)
      (completedLocalCohomology A I J hI hJ M)) (i : ℤ) (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (completedLocalCohomology A I J hI hJ M)) :=
  isZero_homology_of_isDerivedLimit_of_neg A I J hJ M _ hcompletion i hi

end Completion

end Dualizing

end
