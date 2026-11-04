module

public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.GradedSplitting
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerQuotient
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleKernel
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Topology.Algebra.AdicLimitTopology

/-!
# The limit topology on the cohomology of an adic inverse system: the module-theoretic engine

Let `I` be an ideal of a Noetherian ring `A`, let `X` be a Noetherian scheme over `Spec A` and
let `(F_n)` be an inverse system of coherent `𝒪_X`-modules with `F_n = F_{n+1} / I^n F_{n+1}`,
that is, a `Stacks.Algebraization.AdicInverseSystem` along `I · 𝒪_X`. [Stacks, Tag 0EH7] states
that when `cd(A, I) = 1` the limit topology on `lim_n H^p(X, F_n)` is the `I`-adic topology.

That statement is
`Stacks.Algebraization.AdicInverseSystem.limitIntCohomologyTopology_eq_adicModuleTopology`.

This file proves the module-theoretic part of the argument for an arbitrary functor `H` in place
of `H^p(X, -)`, and defines the concrete functor
`Stacks.Algebraization.AdicInverseSystem.moduleCohomologyFunctor X p`, the `p`-th right derived
functor of global sections taken in `Γ(X, 𝒪_X)`-modules, so that `lim_n H^p(X, F_n)` carries the
module structure the `I`-adic topology needs. The following inputs of the source's argument are
hypotheses of the engine rather than supplied:

* the **graded splitting** of [Stacks, Tag 0EH6]. The declaration
  `Stacks.Coherent.gradedSplitting_unique` carries that tag for the uniqueness of the graded map
  and its attribute records that the existence of the map is not proved there, so
  `Stacks.Coherent.existsUnique_gradedSplitting_of_exists` already takes that existence as a
  hypothesis. The same precedent is followed here.
* the **exactness** of `H^p(X, -)` in the middle of `0 → I^{m+1} F → F → F_m → 0`, where
  `F = lim F_n`.
* the **annihilation** of `H^p(X, F_n)` by `I^{n+1}`.

* the **Milnor surjection** `H^p(X, lim F_n) → lim_n H^p(X, F_n)` of [Stacks, Tag 0EI8]. This is
  a hypothesis too: it is not proved in this library in either model of cohomology. See the
  section "The Milnor surjection" below for the two routes that were tried and why each fails.

Everything else is genuinely derived: the hard inclusion is obtained by transporting the graded
splitting through the Milnor surjection, and the comparison of the two topologies is
`Stacks.AdicLimit.iInf_induced_eq_adicModuleTopology`.

## Main definitions

* `Stacks.Algebraization.AdicInverseSystem.moduleCohomologyFunctor` — `H^p(X, -)` as a functor
  into `Γ(X, 𝒪_X)`-modules.
* `Stacks.Algebraization.AdicInverseSystem.cohomologySystem` — the inverse system `n ↦ H(F_n)`.
* `Stacks.Algebraization.AdicInverseSystem.cohomologyLimit` — its limit `lim_n H(F_n)`.
* `Stacks.Algebraization.AdicInverseSystem.limitComparison` — the canonical comparison map
  `H(lim F_n) ⟶ lim_n H(F_n)`, the Milnor map.

## Main results

* `Stacks.Algebraization.AdicInverseSystem.limitTopology_eq_adicModuleTopology_of_gradedSplitting`
  — the module-theoretic content of [Stacks, Tag 0EH7], for an arbitrary functor `H` in place of
  `H^p(X, -)`. It carries no tag: for an arbitrary `H` the statement is not about cohomology.
* `Stacks.Algebraization.AdicInverseSystem.limitComparison` — the comparison map
  `H^p(X, lim F_n) ⟶ lim_n H^p(X, F_n)` whose surjectivity is the carried Milnor hypothesis.
* `Stacks.Algebraization.AdicInverseSystem.ker_le_pow_smul_of_surjective` — transport of a
  kernel bound along a surjection, the step that moves the graded splitting from `H(lim F_n)` to
  `lim_n H(F_n)`.
* `Stacks.Algebraization.AdicInverseSystem.ker_limitProjection_antitone` — the kernels of the
  projections out of a limit of modules are antitone.

## Implementation notes

`AdicInverseSystem.system` is indexed by `ℕᵒᵖ` and zero-indexed, so its object at `n` is the
source's `F_{n+1}` and the exponent `n` of the source appears as `n + 1`.

Taking `H = H^p(X, -)`, the hypotheses of
`limitTopology_eq_adicModuleTopology_of_gradedSplitting` that [Stacks, Tag 0EH7] does not have
are exactly the Milnor surjection `hmilnor` and:

* `hann`: `I^{n+1}` annihilates `H^p(X, F_n)`. This is the easy direction of the comparison, and
  follows from `F_n` being annihilated by `I^{n+1}` together with the `Γ(X, 𝒪_X)`-linearity of
  the derived functor; neither the multiplication-by-a-global-section endomorphism of
  `X.Modules` nor that linearity is available here.
* `hexact`: the kernel of `H^p(X, lim F_n) → H^p(X, F_m)` is contained in the image of
  `H^p(X, I^{m+1} F) → H^p(X, lim F_n)`; this is the exactness of `H^p(X, -)` in the middle of
  the sequence `0 → I^{m+1} F → F → F_m → 0` supplied by
  `Stacks.Algebraization.AdicInverseSystem.exists_idealPowerQuotientIso`. It is *not* a
  consequence of the Milnor hypothesis `hmilnor`, whose short exact sequence is
  `0 → R¹ lim H^p(X, F_n) → H^{p+1}(X, F) → lim_n H^{p+1}(X, F_n) → 0` and so says nothing about
  `I^{m+1} F`; what it needs is the long exact cohomology sequence of a short exact sequence of
  sheaves, which is a different input.
* `Ψ` and `hsplit`: the graded splitting of [Stacks, Tag 0EH6], transported through `H^p(X, -)`.
  The components `Ψ n σ` are the components of a `Stacks.Coherent.GradedSplittingComponents`,
  and `hsplit` is the identity `∑_{|σ| = n} f^σ · Ψ_σ = ι` of the source, applied to the functor.

The degree runs over `ℕ`, not the `ℤ` of the source: `moduleCohomologyFunctor` is a right derived
functor, so the negative degrees of the source are the zero module and carry no information.

The ideal of global functions generated by `I` is written
`I.map (f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom)`, the spelling the conclusion of the
tag needs; it agrees with `Stacks.Cohomology.FormalFunctions.baseIdeal A I f`.

Monomials of a fixed degree in `r` variables form a finite type, which is what makes the sum in
`hsplit` meaningful; the instances are supplied here from `Finsupp.finite_of_degree_eq`.

## References

* [Stacks Project, Tag 0EH7](https://stacks.math.columbia.edu/tag/0EH7)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization.AdicInverseSystem

/-! ### Monomials of a fixed degree

The graded splitting of [Stacks, Tag 0EH6] is a family indexed by the monomials of a given
degree in the chosen generators of `I`, and the splitting identity is a sum over that family. -/

/-- The monomials of degree `n` in `r` variables form a finite type. -/
public instance finite_finsuppDegreeEq (r n : ℕ) :
    Finite {σ : Fin r →₀ ℕ // σ.degree = n} :=
  Set.Finite.to_subtype (Finsupp.finite_of_degree_eq n)

/-- The monomials of degree `n` in `r` variables, as a `Fintype`, so that sums over them are
available. -/
public instance fintype_finsuppDegreeEq (r n : ℕ) :
    Fintype {σ : Fin r →₀ ℕ // σ.degree = n} :=
  Fintype.ofFinite _

/-! ### The cohomology system and its limit -/

variable {R : Type u} [CommRing R]

/-- The inverse system `n ↦ H(F_n)` obtained by applying a functor `H` to an adic inverse
system. For `H = H^p(X, -)` this is the system of cohomology modules of [Stacks, Tag 0EH7]. -/
public abbrev cohomologySystem (S : AdicInverseSystem.{u})
    (H : S.X.Modules ⥤ ModuleCat.{u} R) : ℕᵒᵖ ⥤ ModuleCat.{u} R :=
  S.system ⋙ H

/-- The limit `lim_n H(F_n)` of the cohomology system of an adic inverse system. -/
public abbrev cohomologyLimit (S : AdicInverseSystem.{u})
    (H : S.X.Modules ⥤ ModuleCat.{u} R) : ModuleCat.{u} R :=
  limit (cohomologySystem S H)

/-- The canonical comparison map `H(lim F_n) ⟶ lim_n H(F_n)`, induced by the images under `H` of
the limit projections. Its surjectivity is the content of the Milnor sequence of
[Stacks, Tag 0EI8]. -/
public def limitComparison (S : AdicInverseSystem.{u})
    (H : S.X.Modules ⥤ ModuleCat.{u} R) : H.obj S.limitModule ⟶ cohomologyLimit S H :=
  limit.lift (cohomologySystem S H) (H.mapCone (limit.cone S.system))

/-- The comparison map followed by a limit projection is the image under `H` of the
corresponding limit projection of the system. -/
@[simp]
public lemma limitComparison_comp_π (S : AdicInverseSystem.{u})
    (H : S.X.Modules ⥤ ModuleCat.{u} R) (n : ℕᵒᵖ) :
    limitComparison S H ≫ limit.π (cohomologySystem S H) n = H.map (limit.π S.system n) :=
  limit.lift_π _ _

/-- The comparison map followed by a limit projection, evaluated on an element. -/
public lemma limitComparison_π_apply (S : AdicInverseSystem.{u})
    (H : S.X.Modules ⥤ ModuleCat.{u} R) (n : ℕᵒᵖ) (w : H.obj S.limitModule) :
    (limit.π (cohomologySystem S H) n).hom ((limitComparison S H).hom w) =
      (H.map (limit.π S.system n)).hom w := by
  rw [← ModuleCat.comp_apply, limitComparison_comp_π]

/-! ### Two elementary lemmas about limits of modules -/

/-- The kernels of the projections out of a limit of an `ℕᵒᵖ`-indexed system of modules are
antitone: an element killed by the projection to the `j`-th term is killed by the projection to
every earlier term. -/
public lemma ker_limitProjection_antitone (F : ℕᵒᵖ ⥤ ModuleCat.{u} R) [HasLimit F]
    {i j : ℕ} (hij : i ≤ j) :
    LinearMap.ker (limit.π F (op j)).hom ≤ LinearMap.ker (limit.π F (op i)).hom := by
  intro x hx
  have h := congrArg (fun t : limit F ⟶ F.obj (op i) => t.hom x)
    (limit.w F (homOfLE hij).op)
  change (F.map (homOfLE hij).op).hom ((limit.π F (op j)).hom x) =
    (limit.π F (op i)).hom x at h
  rw [LinearMap.mem_ker.mp hx, map_zero] at h
  exact LinearMap.mem_ker.mpr h.symm

/-- Transport of a kernel bound along a surjection. If `q : W → M` is surjective, if `p : M → N`
and `g : W → N` satisfy `p ∘ q = g` and if the kernel of `g` lies in `J ^ k W`, then the kernel
of `p` lies in `J ^ k M`.

This is the step that moves the graded splitting of [Stacks, Tag 0EH6], which lives on
`H(lim F_n)`, onto the limit `lim_n H(F_n)` along the Milnor surjection. -/
public lemma ker_le_pow_smul_of_surjective (J : Ideal R) (k : ℕ)
    {W M N : Type u} [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (q : W →ₗ[R] M) (hq : Function.Surjective q)
    (p : M →ₗ[R] N) (g : W →ₗ[R] N) (hcomp : ∀ w, p (q w) = g w)
    (hg : LinearMap.ker g ≤ J ^ k • (⊤ : Submodule R W)) :
    LinearMap.ker p ≤ J ^ k • (⊤ : Submodule R M) := by
  intro x hx
  obtain ⟨w, rfl⟩ := hq x
  have hw : w ∈ LinearMap.ker g :=
    LinearMap.mem_ker.mpr ((hcomp w).symm.trans (LinearMap.mem_ker.mp hx))
  have hmem : q w ∈ Submodule.map q (J ^ k • (⊤ : Submodule R W)) :=
    Submodule.mem_map_of_mem (hg hw)
  rwa [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hq] at hmem

/-! ### The engine: the comparison for an arbitrary functor out of `X.Modules`

The topological content of [Stacks, Tag 0EH7] is module-theoretic, and this is it, stated for an
arbitrary functor `H` in place of `H^p(X, -)`. It carries **no tag**: for an arbitrary `H` the
statement is not about cohomology — `H` constant at the zero module satisfies every hypothesis.
The tag is carried by
`Stacks.Algebraization.AdicInverseSystem.limitIntCohomologyTopology_eq_adicModuleTopology`, where
`H` is cohomology in integer degrees. -/

/-- The module-theoretic content of [Stacks, Tag 0EH7], for an arbitrary functor `H` out of
`X.Modules`.

Let `I` be an ideal of a Noetherian ring `A`, let `X` be a Noetherian scheme over `Spec A` and
let `(F_n)` be an adic inverse system of coherent `𝒪_X`-modules along `I · 𝒪_X`, so that
`F_n = F_{n+1} / I^{n+1} F_{n+1}`. Let `H` be any functor taking `𝒪_X`-modules to
`Γ(X, 𝒪_X)`-modules. Assume

* `I^{n+1}` annihilates `H(F_n)`;
* the comparison map `H(lim F_n) → lim_n H(F_n)` is surjective;
* `H` is exact in the middle of `0 → I^{m+1} F → F → F_m → 0`, where `F = lim F_n`;
* the graded splitting `∑_{|σ| = n} f^σ · Ψ_σ = ι` of [Stacks, Tag 0EH6] exists and is carried
  through `H`.

Then the limit topology on `lim_n H(F_n)` — the infimum of the topologies induced from the
discrete modules `H(F_n)` — is the `I`-adic topology. -/
public theorem limitTopology_eq_adicModuleTopology_of_gradedSplitting
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (S : AdicInverseSystem.{u}) [AlgebraicGeometry.IsNoetherian S.X]
    (f : S.X ⟶ Spec (.of A))
    (_hSI : S.I = Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f)
    (_hcoh : ∀ n : ℕ, SheafOfModules.IsCoherent.{u} (S.system.obj (op n)))
    (_hcd : Stacks.LocalCohomology.cohomologicalDimension A I (IsNoetherian.noetherian I) = 1)
    (H : S.X.Modules ⥤ ModuleCat.{u} Γ(S.X, ⊤))
    (hann : ∀ (n : ℕ) (a : Γ(S.X, ⊤)),
      a ∈ (I.map (f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom)) ^ (n + 1) →
      ∀ x : (cohomologySystem S H).obj (op n), a • x = 0)
    (hmilnor : Function.Surjective (limitComparison S H).hom)
    (hexact : ∀ m : ℕ, LinearMap.ker (H.map (limit.π S.system (op m))).hom ≤
      LinearMap.range (H.map (idealPowerMultiple S.I (m + 1) S.limitModule).ιModules).hom)
    (r d : ℕ) (hd : 1 ≤ d) (gen : Fin r → A) (hgen : I = Ideal.span (Set.range gen))
    (Ψ : ∀ n : ℕ, {σ : Fin r →₀ ℕ // σ.degree = n} →
      ((idealPowerMultiple S.I (n * d) S.limitModule).asModules ⟶ S.limitModule))
    (hsplit : ∀ (n : ℕ)
        (z : H.obj (idealPowerMultiple S.I (n * d) S.limitModule).asModules),
      (H.map (idealPowerMultiple S.I (n * d) S.limitModule).ιModules).hom z =
        ∑ σ : {σ : Fin r →₀ ℕ // σ.degree = n},
          (f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom) (∏ j, gen j ^ σ.1 j) •
            (H.map (Ψ n σ)).hom z) :
    (⨅ n : ℕ, TopologicalSpace.induced
        (fun x : cohomologyLimit S H => (limit.π (cohomologySystem S H) (op n)).hom x) ⊥) =
      (I.map (f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom)).adicModuleTopology
        (cohomologyLimit S H) := by
  classical
  set β : A →+* Γ(S.X, ⊤) := f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom with hβ
  set J : Ideal Γ(S.X, ⊤) := I.map β with hJ
  -- A monomial of degree `n` in the generators of `I` lies in `J ^ n`.
  have hmonomial (n : ℕ) (σ : {σ : Fin r →₀ ℕ // σ.degree = n}) :
      β (∏ j, gen j ^ σ.1 j) ∈ J ^ n := by
    rw [hJ, show (I.map β) ^ n = (I ^ n).map β from (Ideal.map_pow β I n).symm]
    refine Ideal.mem_map_of_mem _ ?_
    have hprod : (∏ j, gen j ^ σ.1 j) ∈ ∏ j, I ^ σ.1 j := by
      refine Ideal.prod_mem_prod fun j _ => Ideal.pow_mem_pow ?_ _
      rw [hgen]
      exact Ideal.subset_span (Set.mem_range_self j)
    simpa only [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum, σ.2] using hprod
  refine Stacks.AdicLimit.iInf_induced_eq_adicModuleTopology J
    (fun n => (limit.π (cohomologySystem S H) (op n)).hom) ?_ ?_ ?_
  · exact fun i j hij => ker_limitProjection_antitone (cohomologySystem S H) hij
  · -- The easy direction: `J ^ (n + 1)` kills `H(F_n)`.
    intro n
    refine ⟨n + 1, Submodule.smul_le.mpr fun a ha x _ => LinearMap.mem_ker.mpr ?_⟩
    rw [map_smul]
    exact hann n a ha _
  · -- The substantial direction: the graded splitting, transported along the Milnor surjection.
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · exact ⟨0, by simp [hk]⟩
    have hkd : 1 ≤ k * d := by simpa using Nat.mul_le_mul hk hd
    have hmd : k * d - 1 + 1 = k * d := Nat.sub_add_cancel hkd
    refine ⟨k * d - 1, ?_⟩
    refine ker_le_pow_smul_of_surjective J k (limitComparison S H).hom hmilnor
      (limit.π (cohomologySystem S H) (op (k * d - 1))).hom
      (H.map (limit.π S.system (op (k * d - 1)))).hom
      (limitComparison_π_apply S H (op (k * d - 1))) ?_
    intro w hw
    have hrange : w ∈ LinearMap.range
        (H.map (idealPowerMultiple S.I (k * d) S.limitModule).ιModules).hom := by
      have h := hexact (k * d - 1) hw
      rwa [hmd] at h
    obtain ⟨z, rfl⟩ := hrange
    rw [hsplit k z]
    exact Submodule.sum_mem _ fun σ _ =>
      Submodule.smul_mem_smul (hmonomial k σ) Submodule.mem_top

/-! ### Cohomology with its module structure, and the Milnor surjection

`Hfunctor`, the cohomology functor of the 0EI8 clauses in this directory, lands in abelian
groups, so `lim_n H^p(X, F_n)` has no module structure there and the `I`-adic topology cannot be
stated. `moduleCohomologyFunctor` is the same derived functor taken in `Γ(X, 𝒪_X)`-modules, which
is the model this file works in throughout and the one in which the Milnor surjection is
assumed. -/

/-- Forgetting the module structure of a module is additive. -/
public instance forget₂ModuleCat_additive (R : Type u) [CommRing R] :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).Additive :=
  ⟨by intros; rfl⟩

/-- **Cohomology as a functor into `Γ(X, 𝒪_X)`-modules**: the `p`-th right derived functor of
global sections, taken in modules rather than in abelian groups.

This is the model of `H^p(X, -)` that [Stacks, Tag 0EH7] needs, since its conclusion is about the
`I`-adic topology on the `Γ(X, 𝒪_X)`-module `lim_n H^p(X, F_n)`. -/
public abbrev moduleCohomologyFunctor (X : Scheme.{u}) (p : ℕ) :
    X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
  (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived p

/-! ### The Milnor surjection

[Stacks, Tag 0EH7] uses the surjectivity of the comparison map
`H^p(X, lim F_n) → lim_n H^p(X, F_n)` of [Stacks, Tag 0EI8]. That surjectivity is **not** proved
in this library, in either of the two models of cohomology, so the engine above carries it as
the explicit hypothesis `hmilnor`, in the module-valued model it actually consumes.

Two natural routes do not close. Deriving it from the general
derived-limit statement [Stacks, Tag 0D60]
(`Stacks.Cohomology.DerivedLimits.exists_shortExact_limOne_cohomology_derivedLimit_moduleCat`)
needs the derived-category product theorem transported to `Functor.rightDerived`, which nothing
in this library or Mathlib provides — `StacksDraft.Topology.Sheaves.Cohomology.ModuleComparison`
`.CohomologyOfAProduct` has only degree `0` (an isomorphism) and degree `1` (a monomorphism).
Taking instead the abelian-group form as a hypothesis and transporting it along
`Functor.rightDerivedCompIso` runs into an instance-path divergence: `Hfunctor`/`Hgroup`
elaborate `S.X.ringCatSheaf` at `TopCat.Sheaf RingCat`, while the products around them want
`Sheaf (Opens.grothendieckTopology _) RingCat`, so the composite is not type-correct under
`implicit` transparency and the rewrites that would assemble it fail. Carrying the surjection in
the module-valued model avoids both and assumes no more than the source does. -/

end Stacks.Algebraization.AdicInverseSystem

end

end
