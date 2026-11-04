module

public import StacksFrontier.AlgebraicGeometry.Scheme.FiniteAffineCoverOfQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartMapFinitePresentationClause
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartMapMainClauseAffineTest
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# Stacks 083K for a quasi-compact test object

Let `S = \Spec(R)` be an affine scheme of a big fppf site, let `X` be an algebraic space over
`S` and let `u : ℱ ⟶ 𝒢` be a map of quasi-coherent `𝒪_X`-modules with `𝒢` flat over `S` — the
standing data of Stacks 0CWA.  Let `T ⟶ S` be a **quasi-compact** morphism of schemes at which
the base change `u_T` vanishes.  This file proves both clauses of Stacks 083K at that
hypothesis: a closed subscheme `Z ⊆ S` through which `T ⟶ S` factors and at which `u_Z = 0`,
and — when `ℱ` is of finite type with quasi-compact scheme theoretic support — one with
`Z ⟶ S` of finite presentation.

Both clauses are already proved for an *affine* test object
(`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.exists_closedSubscheme_isZeroAt_of_isZeroAt`
and, from the chartwise ring-level reading of `u_T = 0`,
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.exists_fg_ideal_isZeroAt_specQuotient`).
What this file adds is the source's own reduction — *"choose a finite affine open covering
`T = T_1 ∪ … ∪ T_m`; it is clear that we may replace `T` by `⨿_j T_j`"* — and with it the two
registrations of the tag.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_finite_affine_cover_appTop_injective`: a quasi-compact
  object of the big fppf category over `S` is covered by finitely many **affine objects of that
  category**, and its global functions inject into the product of theirs.

The remaining results are in the namespace `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation`.

* `val_app_mem_ker_smul_top_of_isZeroAt_of_quasiCompact`:
  **the reduction.**  For a quasi-compact test object `T`, every value of `u` over an affine
  étale chart of `X` lies in `\ker(\Gamma(S, ⊤) ⟶ \Gamma(T, ⊤)) · 𝒢(V)`.
* `exists_closedSubscheme_isZeroAt_of_isZeroAt_of_quasiCompact`:
  **the main clause of Stacks 083K.**
* `exists_fg_ideal_isZeroAt_specQuotient_of_quasiCompact`:
  the finite-presentation clause of Stacks 083K, as a finitely generated ideal.
* `exists_closedSubscheme_isZeroAt_locallyOfFinitePresentation_of_isZeroAt_of_quasiCompact`:
  **the finite-presentation clause of Stacks 083K**, as the closed subscheme that ideal cuts
  out.

## Implementation notes

**Where the covering is used, and where it is not.**  The source replaces `T` by the coproduct
of the members of a finite affine open covering.  Neither the coproduct nor the identification
of its functions with the product of the members' functions is needed: the only property of the
replacement that the argument uses is that a global function on `T` vanishing on every member is
zero, and that holds for `\Gamma(T, ⊤)` itself because the structure sheaf is separated.  This
is `AlgebraicGeometry.Scheme.exists_finite_affine_cover_appTop_injective`, lifted here to
objects of the site: the members of the covering are opens of a scheme contained in the site,
hence contained in it (`AlgebraicGeometry.BigFppfSite.contains_of_isOpenImmersion`), and their
open immersions into `T` are morphisms over `S` by construction.

**The ideal is not assembled from the members' ideals.**  The kernel of `\Gamma(S, ⊤) ⟶
\Gamma(T, ⊤)` is *not* the intersection of the kernels of `\Gamma(S, ⊤) ⟶ \Gamma(T_j, ⊤)` in any
useful sense, so the reduction cannot be carried out at the level of ideals.  It is carried out
one step earlier, at the tensor product: for each member the affine case gives
`u(V)(m) ∈ \ker(\Gamma(S, ⊤) ⟶ \Gamma(T_j, ⊤)) · 𝒢(V)`, hence
`u(V)(m) ⊗ 1 = 0` in `𝒢(V) ⊗_{\Gamma(S, ⊤)} \Gamma(T_j, ⊤)` by
`Stacks.Flattening.tmul_eq_zero_of_mem_smul_top`;
`Stacks.Flattening.tmul_one_eq_zero_of_forall_tmul_one_eq_zero` assembles those into
`u(V)(m) ⊗ 1 = 0` in `𝒢(V) ⊗_{\Gamma(S, ⊤)} \Gamma(T, ⊤)` — this is where flatness of `𝒢(V)`
and finiteness of the covering are spent — and
`Stacks.Flattening.mem_ker_smul_top_of_tmul_eq_zero` reads that back as membership in the single
ideal `\ker(\Gamma(S, ⊤) ⟶ \Gamma(T, ⊤)) · 𝒢(V)`.

**Transferring the hypothesis to the members.**  The vanishing `u_T = 0` is
`AlgebraicGeometry.Space.ModuleMapSituation.IsZeroAt` at the test scheme
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.baseTest`, and
`AlgebraicGeometry.Space.ModuleMapSituation.isZeroAt_of_hom` carries it along a morphism of test
schemes.  The test schemes over the final algebraic space are costructured arrows whose codomain
is terminal, so a morphism `T_j ⟶ T` of the site *is* such a morphism of test schemes: the
triangle commutes because both of its sides are morphisms into a terminal object.

**The quasi-compactness hypothesis.**  The source asks for `T ⟶ S` quasi-compact; the base `S`
is affine, hence quasi-compact, so `T` itself is a quasi-compact scheme
(`AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace`).  That is the form the finite
affine covering consumes, and the only consequence of the hypothesis used.

**The finite-presentation clause.**  Its formalized form takes `u_T = 0` in the chartwise ring-level
reading: the extension of scalars of `u(Z₀)` along `\Gamma(S, ⊤) ⟶ \Gamma(T, ⊤)` vanishes over
every affine étale chart `Z₀`.  That reading follows from the membership proved here, because an
element of `I · 𝒢(Z₀)` dies against *every* element of an algebra killed by `I`, not just
against `1` — so no separate bridge is required and the registration is unconditional.

## References

* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
* [Stacks Project, Tag 0CWA](https://stacks.math.columbia.edu/tag/0CWA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An element of `\ker(R ⟶ A) • N` dies in `N ⊗[R] A`. -/
private theorem tmul_eq_zero_of_mem_ker_smul_top {R A N : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup N] [Module R N] {n : N}
    (hn : n ∈ RingHom.ker (algebraMap R A) • (⊤ : Submodule R N)) (q : A) :
    n ⊗ₜ[R] q = 0 :=
  Stacks.Flattening.tmul_eq_zero_of_mem_smul_top
    (fun _ ha q => by rw [Algebra.smul_def, RingHom.mem_ker.mp ha, zero_mul]) hn q

/-! ### Finite affine coverings inside the site -/

/-- The pullback of global functions along a morphism of the big fppf category over `S` is a
morphism of algebras over the functions on the base: the morphism commutes with the structure
morphisms to `S`. -/
theorem BigFppfOver.appTop_appTop {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (r : Γ(S, ⊤)) :
    ((BigFppfOver.toScheme B S hS).map g).appTop.hom
        ((show Γ(S, ⊤) →+* (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u) from
          (B.inclusion.map T.hom).appTop.hom) r) =
      (show Γ(S, ⊤) →+* (Γ((BigFppfOver.toScheme B S hS).obj T', ⊤) : Type u) from
        (B.inclusion.map T'.hom).appTop.hom) r := by
  have hw : (BigFppfOver.toScheme B S hS).map g ≫ B.inclusion.map T.hom =
      B.inclusion.map T'.hom := by
    change B.inclusion.map g.left ≫ B.inclusion.map T.hom = B.inclusion.map T'.hom
    rw [← Functor.map_comp, Over.w]
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
    congrArg (fun k : (BigFppfOver.toScheme B S hS).obj T' ⟶ B.inclusion.obj (B.obj hS) =>
      k.appTop.hom r) hw

/-- **A quasi-compact object of the big fppf category over `S` is covered by finitely many
affine objects of that category.**  There are finitely many affine objects of the category
mapping to `T` such that a global function on `T` pulling back to zero on each of them is zero.

This is `AlgebraicGeometry.Scheme.exists_finite_affine_cover_appTop_injective` inside the site:
the members of the canonical finite affine open covering are opens of the scheme of `T`, hence
contained in the site, and their open immersions are morphisms over `S`. -/
theorem BigFppfOver.exists_finite_affine_cover_appTop_injective (T : BigFppfOver B S hS)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj T)] :
    ∃ (ι : Type u) (_ : Fintype ι) (A : ι → BigFppfOver B S hS)
      (_ : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (A i)))
      (g : ∀ i, A i ⟶ T),
      ∀ x : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤),
        (∀ i, ((BigFppfOver.toScheme B S hS).map (g i)).appTop.hom x = 0) → x = 0 := by
  classical
  let 𝒰 : Scheme.OpenCover.{u, u} ((BigFppfOver.toScheme B S hS).obj T) :=
    ((BigFppfOver.toScheme B S hS).obj T).affineCover.finiteSubcover
  have hc : ∀ i, B.Contains (𝒰.X i) := fun i =>
    B.contains_of_isOpenImmersion (𝒰.f i) T.left.2
  exact ⟨𝒰.I₀, inferInstance,
    fun i => BigFppfOver.mk B S hS (hc i) (𝒰.f i ≫ B.inclusion.map T.hom),
    fun i => show IsAffine (𝒰.X i) from inferInstance,
    fun i => Over.homMk (ObjectProperty.homMk (X := B.obj (hc i)) (Y := T.left) (𝒰.f i))
      (by apply ObjectProperty.hom_ext; rfl),
    fun x hx => Scheme.zero_of_zero_cover x 𝒰 hx⟩

namespace Space

namespace ModuleMapFlatTargetSituation

variable [IsAffine S] (D : ModuleMapFlatTargetSituation B S hS)

/-! ### Transferring the vanishing along a morphism of the site -/

/-- A morphism of objects of the big fppf category over `S`, read as a morphism of the test
schemes over the final algebraic space they give.  The triangle commutes because both of its
sides are morphisms into the final algebraic space. -/
def baseTestMap {T T' : BigFppfOver B S hS} (g : T' ⟶ T) :
    D.baseTest B S hS T' ⟶ D.baseTest B S hS T :=
  CostructuredArrow.homMk g ((terminalSpace_isTerminal B S hS).hom_ext _ _)

/-- **Vanishing of the base change at a test object passes to any object of the site over
it.**  `AlgebraicGeometry.Space.ModuleMapSituation.isZeroAt_of_hom` at
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.baseTestMap`. -/
theorem isZeroAt_baseTest_of_hom {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (hzero : (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
      (D.baseTest B S hS T)) :
    (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
      (D.baseTest B S hS T') :=
  ModuleMapSituation.isZeroAt_of_hom _ _ (D.baseTestMap B S hS g) hzero

/-- The pullback of global functions along a morphism of the big fppf category over `S`, as a
morphism of `\Gamma(S, ⊤)`-algebras. -/
def siteObjectBaseAlgHom {T T' : BigFppfOver B S hS} (g : T' ⟶ T) :
    letI := siteObjectBaseAlgebra B S hS T
    letI := siteObjectBaseAlgebra B S hS T'
    (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u) →ₐ[Γ(S, ⊤)]
      (Γ((BigFppfOver.toScheme B S hS).obj T', ⊤) : Type u) :=
  letI := siteObjectBaseAlgebra B S hS T
  letI := siteObjectBaseAlgebra B S hS T'
  { ((BigFppfOver.toScheme B S hS).map g).appTop.hom with
    commutes' := BigFppfOver.appTop_appTop B S hS g }

/-! ### The reduction to an affine test object -/

/-- **The main clause's payload of Stacks 083K for a quasi-compact test object.**

In the situation of Stacks 0CWA over an affine base `S`, let `T ⟶ S` be a quasi-compact
morphism at which the base change of `u` vanishes.  Then over every affine étale chart `V` of
`X`, every value of `u` lies in `I · 𝒢(V)`, where
`I = \ker(\Gamma(S, ⊤) ⟶ \Gamma(T, ⊤))`.

This is the source's reduction to the affine case.  `T` is quasi-compact as a scheme because
the affine base is, so it carries a finite covering by affine objects of the site
(`AlgebraicGeometry.BigFppfOver.exists_finite_affine_cover_appTop_injective`); the vanishing
passes to each member by
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.isZeroAt_baseTest_of_hom`, and the affine
case
(`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.val_app_mem_ker_smul_top_of_isZeroAt`)
puts each value of `u` in the member's kernel ideal times `𝒢(V)`.  The members' ideals are not
combined: the statement is moved to the tensor product, where
`Stacks.Flattening.tmul_one_eq_zero_of_forall_tmul_one_eq_zero` assembles the vanishings over
the members into the vanishing over `T`, and
`Stacks.Flattening.mem_ker_smul_top_of_tmul_eq_zero` reads it back as membership in the single
ideal of `T`. -/
theorem val_app_mem_ker_smul_top_of_isZeroAt_of_quasiCompact (T : BigFppfOver B S hS)
    (hqc : QuasiCompact (B.inclusion.map T.hom)) (V : SmallEtale B S hS D.X.1)
    (hV : IsAffine (chartScheme V))
    (hzero : (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
      (D.baseTest B S hS T)) :
    letI : Module Γ(S, ⊤) (D.G.val.obj (op V) : Type u) :=
      Module.compHom _ (chartToBaseRingHom B S hS D.X V)
    ∀ m : D.F.val.obj (op V),
      (D.u.val.app (op V)).hom m ∈
        RingHom.ker (show Γ(S, ⊤) →+*
            (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u) from
          (B.inclusion.map T.hom).appTop.hom) •
          (⊤ : Submodule Γ(S, ⊤) (D.G.val.obj (op V) : Type u)) := by
  let : Module Γ(S, ⊤) (D.G.val.obj (op V) : Type u) :=
    Module.compHom _ (chartToBaseRingHom B S hS D.X V)
  have : Module.Flat Γ(S, ⊤) (D.G.val.obj (op V) : Type u) := flat_sections_G B S hS D V hV
  have : IsAffine (B.inclusion.obj (B.obj hS)) := ‹IsAffine S›
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj T) :=
    QuasiCompact.compactSpace_of_compactSpace (B.inclusion.map T.hom)
  obtain ⟨ι, hι, A, hAaff, g, hginj⟩ :=
    BigFppfOver.exists_finite_affine_cover_appTop_injective B S hS T
  let : Algebra Γ(S, ⊤) (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u) :=
    siteObjectBaseAlgebra B S hS T
  let : ∀ i : ι, Algebra Γ(S, ⊤)
      (Γ((BigFppfOver.toScheme B S hS).obj (A i), ⊤) : Type u) :=
    fun i => siteObjectBaseAlgebra B S hS (A i)
  intro m
  refine Stacks.Flattening.mem_ker_smul_top_of_tmul_eq_zero
    (R' := (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u)) ?_
  refine Stacks.Flattening.tmul_one_eq_zero_of_forall_tmul_one_eq_zero
    (fun i => siteObjectBaseAlgHom B S hS (g i)) hginj fun i => ?_
  exact tmul_eq_zero_of_mem_ker_smul_top
    (val_app_mem_ker_smul_top_of_isZeroAt B S hS D (A i) V
      (D.isZeroAt_baseTest_of_hom B S hS (g i) hzero) (hAaff i) hV m) 1

/-! ### The two clauses of Stacks 083K -/

/-- **The main clause of Stacks 083K.**

In Situation 0CWA — `S = \Spec(R)` affine, `X` an algebraic space over `S`, `u : ℱ ⟶ 𝒢` a map
of quasi-coherent `𝒪_X`-modules with `𝒢` flat over `S` — let `T ⟶ S` be a quasi-compact
morphism of schemes such that the base change `u_T` is zero.  Then there is a closed subscheme
`Z ⊆ S` such that (a) `T ⟶ S` factors through `Z` and (b) the base change `u_Z` is zero.

The subscheme is `Z = \Spec(\Gamma(S, ⊤)/I)` for `I = \ker(\Gamma(S, ⊤) ⟶ \Gamma(T, ⊤))`, the
smallest closed subscheme of `S` through which `T ⟶ S` factors; the factorisation is therefore
`AlgebraicGeometry.Space.exists_hom_specQuotientOver` at an equality of ideals.  That `I` kills
the image of `u` over every affine chart is
`val_app_mem_ker_smul_top_of_isZeroAt_of_quasiCompact`,
and
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.isZeroAt_specQuotient_of_forall_mem_smul_top`
turns that into `u_Z = 0`. -/
@[stacks 083K "main clause"]
theorem exists_closedSubscheme_isZeroAt_of_isZeroAt_of_quasiCompact (T : BigFppfOver B S hS)
    (hqc : QuasiCompact (B.inclusion.map T.hom))
    (hzero : (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
      (D.baseTest B S hS T)) :
    ∃ Z : BigFppfOver B S hS,
      _root_.AlgebraicGeometry.IsClosedImmersion (B.inclusion.map Z.hom) ∧ Nonempty (T ⟶ Z) ∧
        (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
          (D.baseTest B S hS Z) :=
  ⟨specQuotientOver B S hS
      (RingHom.ker (show Γ(S, ⊤) →+*
          (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u) from
        (B.inclusion.map T.hom).appTop.hom)),
    isClosedImmersion_specQuotientToBase S _,
    exists_hom_specQuotientOver B S hS _ T le_rfl,
    isZeroAt_specQuotient_of_forall_mem_smul_top B S hS D _ fun V hV =>
      D.val_app_mem_ker_smul_top_of_isZeroAt_of_quasiCompact B S hS T hqc V hV hzero⟩

/-- **The finite-presentation clause of Stacks 083K.**

In Situation 0CWA, assume in addition that `ℱ` is a finite type `𝒪_X`-module whose scheme
theoretic support is quasi-compact, and let `T ⟶ S` be a quasi-compact morphism of schemes such
that the base change `u_T` is zero.  Then the closed subscheme of the main clause can be taken
with `Z ⟶ S` of finite presentation: there is a finitely generated ideal `J` of the functions on
the base such that `Z = \Spec(\Gamma(S, ⊤)/J)` is locally of finite presentation over `S` — and
affine, hence quasi-compact and quasi-separated, so of finite presentation — `T ⟶ S` factors
through `Z`, and `u_Z = 0`.

This is
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.exists_fg_ideal_isZeroAt_specQuotient`,
whose hypothesis is the chartwise ring-level reading of `u_T = 0`.  That reading follows from
`val_app_mem_ker_smul_top_of_isZeroAt_of_quasiCompact`
by `Stacks.Flattening.tmul_eq_zero_of_mem_smul_top`: the values of `u` lie in
`\ker(\Gamma(S, ⊤) ⟶ \Gamma(T, ⊤)) · 𝒢(Z₀)`, and that ideal annihilates `\Gamma(T, ⊤)`, so
every `u(m) ⊗ x` vanishes and not merely `u(m) ⊗ 1`.

`exists_closedSubscheme_isZeroAt_locallyOfFinitePresentation_of_isZeroAt_of_quasiCompact`
is this statement with the ideal replaced by the closed subscheme it cuts out, which is the
shape the source states. -/
theorem exists_fg_ideal_isZeroAt_specQuotient_of_quasiCompact
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hcpt : CompactSpace (points B S hS (schemeTheoreticSupport B S hS D.X D.F).toFunctor))
    (T : BigFppfOver B S hS) (hqc : QuasiCompact (B.inclusion.map T.hom))
    (hzero : (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
      (D.baseTest B S hS T)) :
    ∃ J : Ideal Γ(S, ⊤), J.FG ∧
      LocallyOfFinitePresentation (specQuotientToBase S J) ∧
      Nonempty (T ⟶ specQuotientOver B S hS J) ∧
      (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
        (D.specQuotientTest B S hS J) := by
  refine exists_fg_ideal_isZeroAt_specQuotient B S hS D hFft hcpt T fun Z₀ hZ₀ => ?_
  let := chartBaseAlgebra B S hS D.X Z₀
  let := testSchemeBaseAlgebra B S hS T
  let : Module Γ(S, ⊤) (D.F.val.obj (op Z₀) : Type u) :=
    Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
  let : Module Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u) :=
    Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
  have := isScalarTower_chartRing_sections B S hS D.X D.F Z₀
  have := isScalarTower_chartRing_sections B S hS D.X D.G Z₀
  refine TensorProduct.ext' fun m x => ?_
  rw [LinearMap.rTensor_tmul, LinearMap.zero_apply]
  exact tmul_eq_zero_of_mem_ker_smul_top
    (D.val_app_mem_ker_smul_top_of_isZeroAt_of_quasiCompact B S hS T hqc Z₀ hZ₀ hzero m) x

/-- **The finite-presentation clause of Stacks 083K, in the shape the source states it.**

In Situation 0CWA, assume in addition that `ℱ` is a finite type `𝒪_X`-module whose scheme
theoretic support is quasi-compact, and let `T ⟶ S` be a quasi-compact morphism of schemes such
that the base change `u_T` is zero.  Then there is a closed subscheme `Z ⊆ S`, locally of finite
presentation over `S` — and affine, hence quasi-compact and quasi-separated, so of finite
presentation — through which `T ⟶ S` factors and at which `u_Z = 0`.

This is
`exists_fg_ideal_isZeroAt_specQuotient_of_quasiCompact`
with `Z = \Spec(\Gamma(S, ⊤)/J)`, whose closed immersion into `S` is
`AlgebraicGeometry.Space.isClosedImmersion_specQuotientToBase`. -/
@[stacks 083K "finite presentation clause"]
theorem exists_closedSubscheme_isZeroAt_locallyOfFinitePresentation_of_isZeroAt_of_quasiCompact
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hcpt : CompactSpace (points B S hS (schemeTheoreticSupport B S hS D.X D.F).toFunctor))
    (T : BigFppfOver B S hS) (hqc : QuasiCompact (B.inclusion.map T.hom))
    (hzero : (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
      (D.baseTest B S hS T)) :
    ∃ Z : BigFppfOver B S hS,
      _root_.AlgebraicGeometry.IsClosedImmersion (B.inclusion.map Z.hom) ∧
        LocallyOfFinitePresentation (B.inclusion.map Z.hom) ∧ Nonempty (T ⟶ Z) ∧
        (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
          (D.baseTest B S hS Z) := by
  obtain ⟨J, -, hJfp, hJT, hJ⟩ :=
    D.exists_fg_ideal_isZeroAt_specQuotient_of_quasiCompact B S hS hFft hcpt T hqc hzero
  exact ⟨specQuotientOver B S hS J, isClosedImmersion_specQuotientToBase S J, hJfp, hJT, hJ⟩

end ModuleMapFlatTargetSituation

end Space

end AlgebraicGeometry

end
