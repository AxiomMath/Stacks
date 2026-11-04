module

public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.FlatCriterion
public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.FunctorialGraded
public import StacksFrontier.AlgebraicGeometry.CardinalGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonShortExact
public import StacksFrontier.AlgebraicGeometry.Modules.UnitPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic

/-!
# The filtration of a family read through a direct image

[Stacks, Tag 0E3X] builds the target `V` of a deformation of a morphism as a scheme whose
structure sheaf is `g_* 𝒪_U` for `g : U ⟶ V` over `Spec A`, and then has to prove that `𝒪_V` is
*flat* over `A` *with reduction* `𝒪_V/𝔪𝒪_V = 𝒪_Y` — the sentence "reading the references given
above backwards (and using induction) one concludes that `𝒪_V` is flat over `A` with reduction
`𝒪_V/𝔪_A 𝒪_V = 𝒪_Y`".

Running the filtration machinery on `V` itself is circular: the comparison for `𝒪_V` needs the
stalks of `𝒪_V` to be flat over `A`, which is the flatness being proved.  Both conclusions
therefore come from `U`, through the morphisms

```
𝒪_V ⟶ g_*(𝒪_U/𝔪ⁿ𝒪_U)
```

one for each `n`, whose kernels on the sections over an affine open of `V` are the filtration
that `Stacks.Flatness.flat_and_eq_smul_top_of_ladder` consumes.  The target is the direct image of
`Stacks.BaseAdicFiltration.adicQuotient` of `𝒪_U`, not the adic quotient of `𝒪_V`: nothing here is
a statement about the filtration of `𝒪_V`; every statement is about `𝒪_U`, pushed forward.

## Main definitions

* `Stacks.BaseAdicFiltration.pushforwardAdicProj`: the comparison `𝒪_V ⟶ g_*(𝒪_U/𝔪ⁿ𝒪_U)`.

## Main results

* `Stacks.BaseAdicFiltration.isIso_pushforwardAdicProj_of_pow_eq_bot`: at the top of the
  filtration, where `Iⁿ = 0`, the comparison is invertible — so its kernel on sections is zero,
  which is the ladder's base case.
* `Stacks.BaseAdicFiltration.smul_app_pushforwardAdicProj_eq_zero`: `Iⁿ` kills the target, so
  `Iⁿ` times a section of `𝒪_V` is in the kernel — the ladder's hypothesis `Iⁿ M ≤ K n`.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open scoped AlgebraicGeometry

universe u

namespace Stacks.BaseAdicFiltration

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice
attribute [local instance] hasFiniteBiproducts_schemeModules

variable {A : Type u} [CommRing A] {U V : Scheme.{u}}
  (p : U ⟶ Spec (CommRingCat.of A)) (pV : V ⟶ Spec (CommRingCat.of A)) (g : U ⟶ V)

/-- **The comparison `𝒪_V ⟶ g_*(𝒪_U/Iⁿ𝒪_U)`**: the structure-sheaf comparison of `g` followed by
the direct image of the projection out of `𝒪_U`.

For `n` at the top of the filtration this is invertible, and for `n = 1` it is the map whose
kernel the reduction statement of [Stacks, Tag 0E3X] computes. -/
def pushforwardAdicProj (I : Ideal A) (n : ℕ) :
    Scheme.unitModule V ⟶
      (Scheme.Modules.pushforward g).obj (adicQuotient p I n (Scheme.unitModule U)) :=
  Scheme.Modules.unitToPushforwardUnit g ≫
    (Scheme.Modules.pushforward g).map (adicProj p I n (Scheme.unitModule U))

/-- Equal morphisms of module sheaves have equal values on sections. -/
private theorem app_apply_congr {X : Scheme.{u}} {M N : X.Modules} {φ ψ : M ⟶ N} (h : φ = ψ)
    (O : X.Opens) (x : Γ(M, O)) : φ.app O x = ψ.app O x := by
  rw [h]

/-- **At the top of the filtration the comparison is invertible.**  If `Iⁿ = 0` then
`Iⁿ𝒪_U = 0`, so the projection `𝒪_U ⟶ 𝒪_U/Iⁿ𝒪_U` is invertible, and the comparison is that
followed by the structure-sheaf comparison of `g`, invertible by hypothesis.

This is the base case of the ladder: the kernel of the comparison on sections is zero. -/
theorem isIso_pushforwardAdicProj_of_pow_eq_bot
    (hc : IsIso (C := V.Modules) (Scheme.Modules.unitToPushforwardUnit g))
    (I : Ideal A) {n : ℕ} (hI : I ^ n = ⊥) :
    IsIso (C := V.Modules) (pushforwardAdicProj p g I n) := by
  have := hc
  have : IsIso (C := U.Modules) (adicProj p I n (Scheme.unitModule U)) :=
    isIso_cokernel_π_of_idealPowerMultiple_eq_bot (baseIdeal p I) n _
      (adicFiltration_eq_bot p (Scheme.unitModule U) hI)
  have : IsIso (C := V.Modules) ((Scheme.Modules.pushforward g).map
      (adicProj p I n (Scheme.unitModule U))) := inferInstance
  have hcomp : IsIso (C := V.Modules) (Scheme.Modules.unitToPushforwardUnit g ≫
      (Scheme.Modules.pushforward g).map (adicProj p I n (Scheme.unitModule U))) :=
    inferInstance
  exact hcomp

/-- **`Iⁿ` kills `g_*(𝒪_U/Iⁿ𝒪_U)`.**  Upstairs `Iⁿ` kills `𝒪_U/Iⁿ𝒪_U`, by
`Stacks.Algebraization.sectionSmul_eq_zero` applied to
`Stacks.Algebraization.idealPowerMultiple_idealPowerQuotient_eq_bot`; the direct image of
multiplication by the function `a` determines on `U` is multiplication by the function it
determines on `V`, so the same holds downstairs. -/
theorem sectionSmul_pushforward_adicQuotient_eq_zero {g : U ⟶ V} (hg : g ≫ pV = p)
    (I : Ideal A) (n : ℕ) {a : A} (ha : a ∈ I ^ n) :
    sectionSmul (baseScalarMap pV a)
        ((Scheme.Modules.pushforward g).obj (adicQuotient p I n (Scheme.unitModule U))) = 0 := by
  have hup : sectionSmul (baseScalarMap p a) (adicQuotient p I n (Scheme.unitModule U)) = 0 :=
    sectionSmul_eq_zero _
      (idealPowerMultiple_idealPowerQuotient_eq_bot (baseIdeal p I) n (Scheme.unitModule U))
      (fun W => restrictMemIdealPow_baseScalarMap p n ha W)
  calc sectionSmul (baseScalarMap pV a)
        ((Scheme.Modules.pushforward g).obj (adicQuotient p I n (Scheme.unitModule U)))
      = (Scheme.Modules.pushforward g).map
          (sectionSmul (baseScalarMap p a) (adicQuotient p I n (Scheme.unitModule U))) :=
        (pushforward_sectionSmul pV hg a (adicQuotient p I n (Scheme.unitModule U))).symm
    _ = 0 := by rw [hup]; exact (Scheme.Modules.pushforward g).map_zero _ _

/-- **`Iⁿ` times a section of `𝒪_V` is killed by the comparison.**  This is the hypothesis
`IⁿM ≤ K n` of `Stacks.Flatness.flat_and_eq_smul_top_of_ladder`, for `M` the sections of `𝒪_V`
over an open and `K n` the kernel of the comparison on them: the comparison is linear over the
sections of `𝒪_V`, and the scalar `a` acts on the target as the zero map by
`Stacks.BaseAdicFiltration.sectionSmul_pushforward_adicQuotient_eq_zero`. -/
theorem smul_app_pushforwardAdicProj_eq_zero {g : U ⟶ V} (hg : g ≫ pV = p)
    (I : Ideal A) (n : ℕ) {a : A} (ha : a ∈ I ^ n) (O : V.Opens) (s : Γ(V, O)) :
    letI := sectionsAlgebra pV O
    (pushforwardAdicProj p g I n).app O (a • s) = 0 := by
  let := sectionsAlgebra pV O
  have hz := sectionSmul_pushforward_adicQuotient_eq_zero p pV hg I n ha
  -- the `A`-action on a section of `𝒪_V` is multiplication by the global function `a`
  -- determines, so moving it across the comparison is the naturality of that multiplication
  have hnat := sectionSmul_naturality (baseScalarMap pV a) (pushforwardAdicProj p g I n)
  have h2 : (pushforwardAdicProj p g I n).app O (a • s) =
      (sectionSmul (baseScalarMap pV a) ((Scheme.Modules.pushforward g).obj
        (adicQuotient p I n (Scheme.unitModule U)))).app O
          ((pushforwardAdicProj p g I n).app O s) :=
    app_apply_congr hnat O s
  refine h2.trans ?_
  rw [hz]
  rfl

/-! ### The comparisons are surjective on the sections over an affine open -/

/-- **The comparisons are compatible with the projections down the filtration.**  Composing the
`n+1`-st comparison with the direct image of the drop map `𝒪_U/Iⁿ⁺¹𝒪_U ⟶ 𝒪_U/Iⁿ𝒪_U` gives the
`n`-th. -/
theorem pushforwardAdicProj_comp_gradedShortComplex_g (I : Ideal A) (n : ℕ) :
    pushforwardAdicProj p g I (n + 1) ≫
        (Scheme.Modules.pushforward g).map
          ((gradedShortComplex p I n (Scheme.unitModule U)).g) =
      pushforwardAdicProj p g I n := by
  refine (Category.assoc _ _ _).trans
    (congrArg (fun φ => Scheme.Modules.unitToPushforwardUnit g ≫ φ) ?_)
  refine ((Scheme.Modules.pushforward g).map_comp _ _).symm.trans ?_
  exact congrArg (Scheme.Modules.pushforward g).map
    (adicProj_comp_gradedShortComplex_g p I n (Scheme.unitModule U))

/-- **Every comparison up to the top of the filtration is an epimorphism.**  At the top it is
invertible; one step down is the direct image of the drop map, an epimorphism exactly because the
direct image of the filtration sequence is short exact — which is where the tag's hypothesis
`R¹f_*𝒪_X = 0` is spent, through
`Stacks.BaseAdicFiltration.shortExact_map_pushforward_gradedShortComplex_unit`. -/
theorem epi_pushforwardAdicProj_of_shortExact
    (hc : IsIso (C := V.Modules) (Scheme.Modules.unitToPushforwardUnit g))
    (I : Ideal A) (N : ℕ) (hI : I ^ (N + 1) = ⊥)
    (hSE : ∀ n, ((gradedShortComplex p I n (Scheme.unitModule U)).map
      (Scheme.Modules.pushforward g)).ShortExact) :
    ∀ n, n ≤ N + 1 → Epi (C := V.Modules) (pushforwardAdicProj p g I n) := by
  have := isIso_pushforwardAdicProj_of_pow_eq_bot p g hc I hI
  have key : ∀ j n, n + j = N + 1 → Epi (C := V.Modules) (pushforwardAdicProj p g I n) := by
    intro j
    induction j with
    | zero =>
      intro n hn
      rw [Nat.add_zero] at hn
      subst hn
      infer_instance
    | succ j ih =>
      intro n hn
      -- the two `Epi`s are pinned at `V.Modules` and fed to `epi_comp` explicitly: instance
      -- search does not cross between the `Scheme.Modules` and `SheafOfModules` instances
      have he1 : Epi (C := V.Modules) (pushforwardAdicProj p g I (n + 1)) :=
        ih (n + 1) (by omega)
      have he2 : Epi (C := V.Modules) ((Scheme.Modules.pushforward g).map
          ((gradedShortComplex p I n (Scheme.unitModule U)).g)) := (hSE n).epi_g
      have hcomp : Epi (C := V.Modules) (pushforwardAdicProj p g I (n + 1) ≫
          (Scheme.Modules.pushforward g).map
            ((gradedShortComplex p I n (Scheme.unitModule U)).g)) :=
        @epi_comp V.Modules _ _ _ _ _ he1 _ he2
      exact (congrArg (fun φ : Scheme.unitModule V ⟶ (Scheme.Modules.pushforward g).obj
            (adicQuotient p I n (Scheme.unitModule U)) => Epi φ)
          (pushforwardAdicProj_comp_gradedShortComplex_g p g I n)).mp hcomp
  exact fun n hn => key (N + 1 - n) n (by omega)

/-- **The comparison is surjective on the sections over an affine open.**  This is the one
cohomological input of the whole argument: an epimorphism of quasi-coherent modules is surjective
on the sections over an affine open, by
`Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen`. -/
theorem surjective_app_pushforwardAdicProj
    (hc : IsIso (C := V.Modules) (Scheme.Modules.unitToPushforwardUnit g))
    (I : Ideal A) (N : ℕ) (hI : I ^ (N + 1) = ⊥)
    (hSE : ∀ n, ((gradedShortComplex p I n (Scheme.unitModule U)).map
      (Scheme.Modules.pushforward g)).ShortExact)
    (n : ℕ) (hn : n ≤ N + 1)
    (hqc : ((Scheme.Modules.pushforward g).obj
      (adicQuotient p I n (Scheme.unitModule U))).IsQuasicoherent)
    (O : V.Opens) (hO : IsAffineOpen O) :
    Function.Surjective ((pushforwardAdicProj p g I n).app O) := by
  have := hqc
  have := epi_pushforwardAdicProj_of_shortExact p g hc I N hI hSE n hn
  exact Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen V
    (pushforwardAdicProj p g I n) O hO

/-- **At the top of the filtration the comparison is injective on sections.**  It is invertible
there, hence a monomorphism, hence injective on the sections over every open.

This is the base case `K (N+1) = 0` of `Stacks.Flatness.flat_and_eq_smul_top_of_ladder`. -/
theorem injective_app_pushforwardAdicProj_of_pow_eq_bot
    (hc : IsIso (C := V.Modules) (Scheme.Modules.unitToPushforwardUnit g))
    (I : Ideal A) {n : ℕ} (hI : I ^ n = ⊥) (O : V.Opens) :
    Function.Injective ((pushforwardAdicProj p g I n).app O) := by
  have := isIso_pushforwardAdicProj_of_pow_eq_bot p g hc I hI
  exact Stacks.AlgebraicGeometry.CardinalGeneration.injective_app_of_mono _ O

/-! ### The components of the graded comparison are multiplication -/

/-- The `i`-th component of `Stacks.BaseAdicFiltration.gradedDesc`, followed by the inclusion of
the graded piece into `ℱ/Iⁿ⁺¹ℱ`: the map `ℱ/Iℱ ⟶ ℱ/Iⁿ⁺¹ℱ` that multiplies by `a`. -/
def gradedComponent (I : Ideal A) (n : ℕ) {a : A} (ha : a ∈ I ^ n)
    (e : adicQuotient p I 1 (adicQuotient p I (n + 1) (Scheme.unitModule U)) ≅
      specialFibre p I (Scheme.unitModule U)) :
    specialFibre p I (Scheme.unitModule U) ⟶
      adicQuotient p I (n + 1) (Scheme.unitModule U) :=
  idealPowerComponent (adicQuotient p I (n + 1) (Scheme.unitModule U)) n
      (adicFiltration_adicQuotient_eq_bot p I n (Scheme.unitModule U))
      (fun W => restrictMemIdealPow_baseScalarMap p n ha W) e ≫
    (gradedPiece p I n (Scheme.unitModule U)).ι

/-- **The component is multiplication by `a`, read from `ℱ` rather than from `ℱ/Iℱ`.**  Composing
the projection `ℱ ⟶ ℱ/Iℱ` with the component gives multiplication by `a` followed by the
projection `ℱ ⟶ ℱ/Iⁿ⁺¹ℱ`.

This is `Stacks.Algebraization.comp_idealPowerComponent_comp_ι` — which states the component is
multiplication on `ℱ/Iⁿ⁺¹ℱ` — precomposed with `ℱ ⟶ ℱ/Iⁿ⁺¹ℱ`, the hypothesis `he` identifying
the two routes to `ℱ/Iℱ` and `Stacks.BaseAdicFiltration.sectionSmul_naturality` moving the
multiplication past the projection. -/
theorem adicProj_one_comp_gradedComponent (I : Ideal A) (n : ℕ) {a : A} (ha : a ∈ I ^ n)
    (e : adicQuotient p I 1 (adicQuotient p I (n + 1) (Scheme.unitModule U)) ≅
      specialFibre p I (Scheme.unitModule U))
    (he : adicProj p I (n + 1) (Scheme.unitModule U) ≫
        adicProj p I 1 (adicQuotient p I (n + 1) (Scheme.unitModule U)) ≫ e.hom =
      adicProj p I 1 (Scheme.unitModule U)) :
    adicProj p I 1 (Scheme.unitModule U) ≫ gradedComponent p I n ha e =
      sectionSmul (baseScalarMap p a) (Scheme.unitModule U) ≫
        adicProj p I (n + 1) (Scheme.unitModule U) := by
  have hkey : (adicProj p I 1 (adicQuotient p I (n + 1) (Scheme.unitModule U)) ≫ e.hom) ≫
      gradedComponent p I n ha e =
      sectionSmul (baseScalarMap p a) (adicQuotient p I (n + 1) (Scheme.unitModule U)) :=
    comp_idealPowerComponent_comp_ι (adicQuotient p I (n + 1) (Scheme.unitModule U)) n
      (adicFiltration_adicQuotient_eq_bot p I n (Scheme.unitModule U))
      (fun W => restrictMemIdealPow_baseScalarMap p n ha W) e rfl
  calc adicProj p I 1 (Scheme.unitModule U) ≫ gradedComponent p I n ha e
      = (adicProj p I (n + 1) (Scheme.unitModule U) ≫
          (adicProj p I 1 (adicQuotient p I (n + 1) (Scheme.unitModule U)) ≫ e.hom)) ≫
            gradedComponent p I n ha e :=
        congrArg (fun φ => φ ≫ gradedComponent p I n ha e) he.symm
    _ = adicProj p I (n + 1) (Scheme.unitModule U) ≫
          ((adicProj p I 1 (adicQuotient p I (n + 1) (Scheme.unitModule U)) ≫ e.hom) ≫
            gradedComponent p I n ha e) := Category.assoc _ _ _
    _ = adicProj p I (n + 1) (Scheme.unitModule U) ≫
          sectionSmul (baseScalarMap p a)
            (adicQuotient p I (n + 1) (Scheme.unitModule U)) :=
        congrArg (fun φ => adicProj p I (n + 1) (Scheme.unitModule U) ≫ φ) hkey
    _ = sectionSmul (baseScalarMap p a) (Scheme.unitModule U) ≫
          adicProj p I (n + 1) (Scheme.unitModule U) :=
        (sectionSmul_naturality (baseScalarMap p a)
          (adicProj p I (n + 1) (Scheme.unitModule U))).symm

/-- **The component, pushed down to `V`.**  Composing the comparison at `n = 1` with the direct
image of the component gives multiplication by `a` followed by the comparison at `n + 1`.

This is `Stacks.BaseAdicFiltration.adicProj_one_comp_gradedComponent` pushed forward along `g`
and precomposed with the structure-sheaf comparison, using
`Stacks.BaseAdicFiltration.pushforward_sectionSmul` to turn the direct image of multiplication by
the function `a` determines on `U` into multiplication by the one it determines on `V`, and
`Stacks.BaseAdicFiltration.sectionSmul_naturality` to move that past the comparison. -/
theorem pushforwardAdicProj_one_comp_pushforward_gradedComponent {g : U ⟶ V}
    (hg : g ≫ pV = p) (I : Ideal A) (n : ℕ) {a : A} (ha : a ∈ I ^ n)
    (e : adicQuotient p I 1 (adicQuotient p I (n + 1) (Scheme.unitModule U)) ≅
      specialFibre p I (Scheme.unitModule U))
    (he : adicProj p I (n + 1) (Scheme.unitModule U) ≫
        adicProj p I 1 (adicQuotient p I (n + 1) (Scheme.unitModule U)) ≫ e.hom =
      adicProj p I 1 (Scheme.unitModule U)) :
    pushforwardAdicProj p g I 1 ≫
        (Scheme.Modules.pushforward g).map (gradedComponent p I n ha e) =
      sectionSmul (baseScalarMap pV a) (Scheme.unitModule V) ≫
        pushforwardAdicProj p g I (n + 1) := by
  calc pushforwardAdicProj p g I 1 ≫
        (Scheme.Modules.pushforward g).map (gradedComponent p I n ha e)
      = Scheme.Modules.unitToPushforwardUnit g ≫
          ((Scheme.Modules.pushforward g).map (adicProj p I 1 (Scheme.unitModule U)) ≫
            (Scheme.Modules.pushforward g).map (gradedComponent p I n ha e)) :=
        Category.assoc _ _ _
    _ = Scheme.Modules.unitToPushforwardUnit g ≫
          (Scheme.Modules.pushforward g).map
            (adicProj p I 1 (Scheme.unitModule U) ≫ gradedComponent p I n ha e) :=
        congrArg (fun φ => Scheme.Modules.unitToPushforwardUnit g ≫ φ)
          ((Scheme.Modules.pushforward g).map_comp _ _).symm
    _ = Scheme.Modules.unitToPushforwardUnit g ≫
          (Scheme.Modules.pushforward g).map
            (sectionSmul (baseScalarMap p a) (Scheme.unitModule U) ≫
              adicProj p I (n + 1) (Scheme.unitModule U)) :=
        congrArg (fun φ => Scheme.Modules.unitToPushforwardUnit g ≫
            (Scheme.Modules.pushforward g).map φ)
          (adicProj_one_comp_gradedComponent p I n ha e he)
    _ = Scheme.Modules.unitToPushforwardUnit g ≫
          ((Scheme.Modules.pushforward g).map
              (sectionSmul (baseScalarMap p a) (Scheme.unitModule U)) ≫
            (Scheme.Modules.pushforward g).map
              (adicProj p I (n + 1) (Scheme.unitModule U))) :=
        congrArg (fun φ => Scheme.Modules.unitToPushforwardUnit g ≫ φ)
          ((Scheme.Modules.pushforward g).map_comp _ _)
    _ = Scheme.Modules.unitToPushforwardUnit g ≫
          (sectionSmul (baseScalarMap pV a)
              ((Scheme.Modules.pushforward g).obj (Scheme.unitModule U)) ≫
            (Scheme.Modules.pushforward g).map
              (adicProj p I (n + 1) (Scheme.unitModule U))) :=
        congrArg (fun φ => Scheme.Modules.unitToPushforwardUnit g ≫ φ ≫
            (Scheme.Modules.pushforward g).map
              (adicProj p I (n + 1) (Scheme.unitModule U)))
          (pushforward_sectionSmul pV hg a (Scheme.unitModule U))
    _ = (Scheme.Modules.unitToPushforwardUnit g ≫
            sectionSmul (baseScalarMap pV a)
              ((Scheme.Modules.pushforward g).obj (Scheme.unitModule U))) ≫
          (Scheme.Modules.pushforward g).map
            (adicProj p I (n + 1) (Scheme.unitModule U)) := (Category.assoc _ _ _).symm
    _ = (sectionSmul (baseScalarMap pV a) (Scheme.unitModule V) ≫
            Scheme.Modules.unitToPushforwardUnit g) ≫
          (Scheme.Modules.pushforward g).map
            (adicProj p I (n + 1) (Scheme.unitModule U)) :=
        congrArg (fun φ => φ ≫ (Scheme.Modules.pushforward g).map
            (adicProj p I (n + 1) (Scheme.unitModule U)))
          (sectionSmul_naturality (baseScalarMap pV a)
            (Scheme.Modules.unitToPushforwardUnit g)).symm
    _ = sectionSmul (baseScalarMap pV a) (Scheme.unitModule V) ≫
          pushforwardAdicProj p g I (n + 1) := Category.assoc _ _ _

/-- **Multiplying a section by `a` and comparing at `n + 1` is comparing at `1` and applying the
component.**  The element form of
`Stacks.BaseAdicFiltration.pushforwardAdicProj_one_comp_pushforward_gradedComponent`. -/
theorem app_pushforwardAdicProj_succ_smul {g : U ⟶ V} (hg : g ≫ pV = p) (I : Ideal A) (n : ℕ)
    {a : A} (ha : a ∈ I ^ n)
    (e : adicQuotient p I 1 (adicQuotient p I (n + 1) (Scheme.unitModule U)) ≅
      specialFibre p I (Scheme.unitModule U))
    (he : adicProj p I (n + 1) (Scheme.unitModule U) ≫
        adicProj p I 1 (adicQuotient p I (n + 1) (Scheme.unitModule U)) ≫ e.hom =
      adicProj p I 1 (Scheme.unitModule U))
    (O : V.Opens) (m : Γ(V, O)) :
    letI := sectionsAlgebra pV O
    (pushforwardAdicProj p g I (n + 1)).app O (a • m) =
      ((Scheme.Modules.pushforward g).map (gradedComponent p I n ha e)).app O
        ((pushforwardAdicProj p g I 1).app O m) := by
  let := sectionsAlgebra pV O
  exact (app_apply_congr
    (pushforwardAdicProj_one_comp_pushforward_gradedComponent p pV hg I n ha e he) O m).symm

/-! ### Decomposing a section of the biproduct -/

/-- **A section of a finite biproduct is the sum of the injections of its projections.**  This is
`CategoryTheory.Limits.biproduct.total` read on the sections over an open, using that taking
sections is additive in the morphism (`Stacks.SheafOfModules.app_sum`). -/
theorem app_eq_sum_biproduct_ι_π {X : Scheme.{u}} {k : ℕ} (f : Fin k → X.Modules)
    (O : X.Opens) (x : Γ(⨁ f, O)) :
    x = ∑ i, (biproduct.ι f i).app O ((biproduct.π f i).app O x) := by
  calc x = (𝟙 (⨁ f) : (⨁ f) ⟶ (⨁ f)).app O x := rfl
    _ = (∑ i, biproduct.π f i ≫ biproduct.ι f i).app O x :=
        app_apply_congr (biproduct.total (f := f)).symm O x
    _ = ∑ i, ((biproduct.π f i ≫ biproduct.ι f i).app O x) :=
        Stacks.SheafOfModules.app_sum Finset.univ _ (op O) x
    _ = ∑ i, (biproduct.ι f i).app O ((biproduct.π f i).app O x) := rfl

/-- **The `i`-th component of the graded comparison, followed by the inclusion of the graded
piece, is the multiplication component.**  `Stacks.BaseAdicFiltration.gradedDesc` is
`CategoryTheory.Limits.biproduct.desc` of the components, so this is `biproduct.ι_desc`. -/
theorem biproduct_ι_comp_gradedDesc_comp_ι (I : Ideal A) (n : ℕ) {k : ℕ} (a : Fin k → A)
    (ha : ∀ i, a i ∈ I ^ n)
    (e : adicQuotient p I 1 (adicQuotient p I (n + 1) (Scheme.unitModule U)) ≅
      specialFibre p I (Scheme.unitModule U)) (i : Fin k) :
    biproduct.ι (fun _ : Fin k => specialFibre p I (Scheme.unitModule U)) i ≫
        (gradedDesc p I n (Scheme.unitModule U) a ha e ≫
          (gradedPiece p I n (Scheme.unitModule U)).ι) =
      gradedComponent p I n (ha i) e :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun φ => φ ≫ (gradedPiece p I n (Scheme.unitModule U)).ι)
      (biproduct.ι_desc _ i))

/-! ### The graded condition -/

/-- `Stacks.BaseAdicFiltration.gradedDesc` followed by the inclusion of the graded piece: the
comparison `⨁_{i<k} ℱ/Iℱ ⟶ ℱ/Iⁿ⁺¹ℱ` whose `i`-th component is multiplication by `a i`. -/
def gradedDescToQuotient (I : Ideal A) (n : ℕ) {k : ℕ} (a : Fin k → A)
    (ha : ∀ i, a i ∈ I ^ n)
    (e : adicQuotient p I 1 (adicQuotient p I (n + 1) (Scheme.unitModule U)) ≅
      specialFibre p I (Scheme.unitModule U)) :
    (⨁ fun _ : Fin k => specialFibre p I (Scheme.unitModule U)) ⟶
      adicQuotient p I (n + 1) (Scheme.unitModule U) :=
  gradedDesc p I n (Scheme.unitModule U) a ha e ≫
    (gradedPiece p I n (Scheme.unitModule U)).ι

/-- The comparison into `ℱ/Iⁿ⁺¹ℱ` is a monomorphism as soon as the comparison onto the graded
piece is invertible: the inclusion of a subsheaf is a monomorphism. -/
theorem mono_gradedDescToQuotient (I : Ideal A) (n : ℕ) {k : ℕ} (a : Fin k → A)
    (ha : ∀ i, a i ∈ I ^ n)
    (e : adicQuotient p I 1 (adicQuotient p I (n + 1) (Scheme.unitModule U)) ≅
      specialFibre p I (Scheme.unitModule U))
    (hiso : IsIso (C := U.Modules) (gradedDesc p I n (Scheme.unitModule U) a ha e)) :
    Mono (C := U.Modules) (gradedDescToQuotient p I n a ha e) := by
  have := hiso
  have h1 : Mono (C := U.Modules) (gradedDesc p I n (Scheme.unitModule U) a ha e) :=
    IsIso.mono_of_iso _
  have h2 : Mono (C := U.Modules) (gradedPiece p I n (Scheme.unitModule U)).ι :=
    inferInstance
  exact @mono_comp U.Modules _ _ _ _ _ h1 _ h2

/-- **Projecting the sum of the injections recovers the component.**  The biproduct identities
`biproduct.ι_π_self` and `biproduct.ι_π_ne`, read on sections. -/
theorem app_biproduct_π_sum_ι {X : Scheme.{u}} {k : ℕ} (f : Fin k → X.Modules) (O : X.Opens)
    (z : ∀ i, Γ(f i, O)) (j : Fin k) :
    (biproduct.π f j).app O (∑ i, (biproduct.ι f i).app O (z i)) = z j := by
  classical
  rw [map_sum]
  refine (Finset.sum_eq_single_of_mem j (Finset.mem_univ j) ?_).trans ?_
  · intro i _ hij
    exact (app_apply_congr (biproduct.ι_π_ne f hij) O (z i)).trans rfl
  · exact (app_apply_congr (biproduct.ι_π_self f j) O (z j)).trans rfl

/-- The sum of the multiples `a i • m i` compared at `n + 1` is the graded comparison applied to
the sum of the injections of the values of the `m i` at `1`. -/
private theorem app_pushforwardAdicProj_succ_sum_smul {g : U ⟶ V} (hg : g ≫ pV = p)
    (I : Ideal A) (n : ℕ) {k : ℕ} (a : Fin k → A) (ha : ∀ i, a i ∈ I ^ n)
    (e : adicQuotient p I 1 (adicQuotient p I (n + 1) (Scheme.unitModule U)) ≅
      specialFibre p I (Scheme.unitModule U))
    (he : adicProj p I (n + 1) (Scheme.unitModule U) ≫
        adicProj p I 1 (adicQuotient p I (n + 1) (Scheme.unitModule U)) ≫ e.hom =
      adicProj p I 1 (Scheme.unitModule U))
    (O : V.Opens) (m : Fin k → Γ(V, O)) :
    letI := sectionsAlgebra pV O
    (pushforwardAdicProj p g I (n + 1)).app O (∑ i, a i • m i) =
      (gradedDescToQuotient p I n a ha e).app (g ⁻¹ᵁ O)
        (∑ i, (biproduct.ι (fun _ : Fin k => specialFibre p I (Scheme.unitModule U)) i).app
          (g ⁻¹ᵁ O) ((pushforwardAdicProj p g I 1).app O (m i))) := by
  let := sectionsAlgebra pV O
  refine (map_sum _ _ Finset.univ).trans ((Finset.sum_congr rfl fun i _ => ?_).trans
    (map_sum _ _ Finset.univ).symm)
  refine (app_pushforwardAdicProj_succ_smul p pV hg I n (ha i) e he O (m i)).trans ?_
  exact app_apply_congr (biproduct_ι_comp_gradedDesc_comp_ι p I n a ha e i).symm _ _

/-- **The graded condition of [Stacks, Tag 0E3X].**  If the multiples `a i • m i` of sections of
`𝒪_V` by representatives of a basis of `Iⁿ/Iⁿ⁺¹` add up into the kernel of the comparison at
`n + 1`, then every `m i` is already in the kernel of the comparison at `1`.

This is the hypothesis `hgr` of `Stacks.Flatness.flat_and_eq_smul_top_of_ladder`, and it is where
the identification of the graded piece is spent: by
`Stacks.BaseAdicFiltration.app_pushforwardAdicProj_succ_smul` each summand is the `i`-th
component of the graded comparison applied to the value at `1`, so the sum is that comparison
applied to the sum of the injections; the comparison is a monomorphism, hence injective on
sections, so the sum of the injections vanishes, and projecting recovers each value. -/
theorem app_pushforwardAdicProj_one_eq_zero_of_sum_smul {g : U ⟶ V} (hg : g ≫ pV = p)
    (I : Ideal A) (n : ℕ) {k : ℕ} (a : Fin k → A) (ha : ∀ i, a i ∈ I ^ n)
    (e : adicQuotient p I 1 (adicQuotient p I (n + 1) (Scheme.unitModule U)) ≅
      specialFibre p I (Scheme.unitModule U))
    (he : adicProj p I (n + 1) (Scheme.unitModule U) ≫
        adicProj p I 1 (adicQuotient p I (n + 1) (Scheme.unitModule U)) ≫ e.hom =
      adicProj p I 1 (Scheme.unitModule U))
    (hiso : IsIso (C := U.Modules) (gradedDesc p I n (Scheme.unitModule U) a ha e))
    (O : V.Opens) (m : Fin k → Γ(V, O))
    (hm : letI := sectionsAlgebra pV O
      (pushforwardAdicProj p g I (n + 1)).app O (∑ i, a i • m i) = 0) (j : Fin k) :
    (pushforwardAdicProj p g I 1).app O (m j) = 0 := by
  let := sectionsAlgebra pV O
  have := mono_gradedDescToQuotient p I n a ha e hiso
  have hsum := app_pushforwardAdicProj_succ_sum_smul p pV hg I n a ha e he O m
  -- the comparison is injective on sections, so the sum of the injections vanishes
  have hzero : (∑ i, (biproduct.ι (fun _ : Fin k => specialFibre p I (Scheme.unitModule U)) i).app
      (g ⁻¹ᵁ O) ((pushforwardAdicProj p g I 1).app O (m i))) = 0 := by
    refine Stacks.AlgebraicGeometry.CardinalGeneration.injective_app_of_mono
      (gradedDescToQuotient p I n a ha e) (g ⁻¹ᵁ O) ?_
    refine Eq.trans (hsum.symm.trans hm) ?_
    exact (map_zero _).symm
  -- projecting recovers the value at `j`
  refine Eq.trans ?_ ((congrArg (fun z => (biproduct.π
    (fun _ : Fin k => specialFibre p I (Scheme.unitModule U)) j).app (g ⁻¹ᵁ O) z) hzero).trans
      (map_zero _))
  exact (app_biproduct_π_sum_ι (fun _ : Fin k => specialFibre p I (Scheme.unitModule U))
    (g ⁻¹ᵁ O) (fun i => (pushforwardAdicProj p g I 1).app O (m i)) j).symm

/-- **A multiple of a section, as a value of the graded comparison.**  The summand identity behind
both the graded condition and the decomposition below: multiplying by `a i` and comparing at
`n + 1` is injecting into the `i`-th summand and applying the graded comparison. -/
theorem app_pushforwardAdicProj_succ_smul_eq_gradedDescToQuotient {g : U ⟶ V}
    (hg : g ≫ pV = p) (I : Ideal A) (n : ℕ) {k : ℕ} (a : Fin k → A) (ha : ∀ i, a i ∈ I ^ n)
    (e : adicQuotient p I 1 (adicQuotient p I (n + 1) (Scheme.unitModule U)) ≅
      specialFibre p I (Scheme.unitModule U))
    (he : adicProj p I (n + 1) (Scheme.unitModule U) ≫
        adicProj p I 1 (adicQuotient p I (n + 1) (Scheme.unitModule U)) ≫ e.hom =
      adicProj p I 1 (Scheme.unitModule U))
    (O : V.Opens) (m : Γ(V, O)) (i : Fin k) :
    letI := sectionsAlgebra pV O
    (pushforwardAdicProj p g I (n + 1)).app O (a i • m) =
      (gradedDescToQuotient p I n a ha e).app (g ⁻¹ᵁ O)
        ((biproduct.ι (fun _ : Fin k => specialFibre p I (Scheme.unitModule U)) i).app
          (g ⁻¹ᵁ O) ((pushforwardAdicProj p g I 1).app O m)) := by
  let := sectionsAlgebra pV O
  refine (app_pushforwardAdicProj_succ_smul p pV hg I n (ha i) e he O m).trans ?_
  exact app_apply_congr (biproduct_ι_comp_gradedDesc_comp_ι p I n a ha e i).symm _ _

/-! ### The decomposition step of the ladder -/

/-- **The decomposition step of [Stacks, Tag 0E3X].**  A section of `𝒪_V` killed by the comparison
at `n` is, modulo the kernel of the comparison at `n + 1`, a combination `∑ aᵢ mᵢ` of the
representatives of a basis of `Iⁿ/Iⁿ⁺¹`.

This is the hypothesis `hsup` of `Stacks.Flatness.flat_and_eq_smul_top_of_ladder`.  The section's
value at `n + 1` is killed by the drop map, so by exactness of sections on the direct image of the
filtration sequence it comes from the graded piece; the graded comparison being invertible, it
comes from the biproduct, and there it is the sum of the injections of its projections.  Each
projection lifts to a section of `𝒪_V` along the surjection at `n = 1` — the one cohomological
input — and
`Stacks.BaseAdicFiltration.app_pushforwardAdicProj_succ_smul_eq_gradedDescToQuotient` identifies
the multiple `aᵢ mᵢ` with the corresponding summand. -/
theorem exists_sum_smul_app_pushforwardAdicProj_succ_eq_zero {g : U ⟶ V} (hg : g ≫ pV = p)
    (I : Ideal A) (n : ℕ) {k : ℕ} (a : Fin k → A) (ha : ∀ i, a i ∈ I ^ n)
    (e : adicQuotient p I 1 (adicQuotient p I (n + 1) (Scheme.unitModule U)) ≅
      specialFibre p I (Scheme.unitModule U))
    (he : adicProj p I (n + 1) (Scheme.unitModule U) ≫
        adicProj p I 1 (adicQuotient p I (n + 1) (Scheme.unitModule U)) ≫ e.hom =
      adicProj p I 1 (Scheme.unitModule U))
    (hiso : IsIso (C := U.Modules) (gradedDesc p I n (Scheme.unitModule U) a ha e))
    (hSE : ((gradedShortComplex p I n (Scheme.unitModule U)).map
      (Scheme.Modules.pushforward g)).ShortExact)
    (O : V.Opens)
    (hsurj : Function.Surjective ((pushforwardAdicProj p g I 1).app O))
    (s : Γ(V, O)) (hs : (pushforwardAdicProj p g I n).app O s = 0) :
    letI := sectionsAlgebra pV O
    ∃ m : Fin k → Γ(V, O),
      (pushforwardAdicProj p g I (n + 1)).app O (s - ∑ i, a i • m i) = 0 := by
  let := sectionsAlgebra pV O
  have := hiso
  -- the value at `n + 1` is killed by the drop map
  have hdrop : ((gradedShortComplex p I n (Scheme.unitModule U)).map
      (Scheme.Modules.pushforward g)).g.app O
        ((pushforwardAdicProj p g I (n + 1)).app O s) = 0 :=
    (app_apply_congr (pushforwardAdicProj_comp_gradedShortComplex_g p g I n) O s).trans hs
  -- so it comes from the graded piece
  obtain ⟨y, hy⟩ := exists_app_eq_of_shortExact _ hSE O
    ((pushforwardAdicProj p g I (n + 1)).app O s) hdrop
  -- and from the biproduct, the graded comparison being invertible
  set σ := (inv (gradedDesc p I n (Scheme.unitModule U) a ha e)).app (g ⁻¹ᵁ O) y with hσdef
  have hσ : (gradedDesc p I n (Scheme.unitModule U) a ha e).app (g ⁻¹ᵁ O) σ = y :=
    app_apply_congr (IsIso.inv_hom_id (gradedDesc p I n (Scheme.unitModule U) a ha e)) _ y
  -- lift the projections, at the spelling `Γ(V, O)` that carries the `A`-action
  have hlift : ∀ i : Fin k, ∃ w : Γ(V, O), (pushforwardAdicProj p g I 1).app O w =
      (biproduct.π (fun _ : Fin k => specialFibre p I (Scheme.unitModule U)) i).app
        (g ⁻¹ᵁ O) σ := fun i => hsurj _
  choose m hm using hlift
  refine ⟨m, ?_⟩
  have hstep1 := app_pushforwardAdicProj_succ_sum_smul p pV hg I n a ha e he O m
  have hstep2 : (∑ i, (biproduct.ι
        (fun _ : Fin k => specialFibre p I (Scheme.unitModule U)) i).app
          (g ⁻¹ᵁ O) ((pushforwardAdicProj p g I 1).app O (m i))) = σ :=
    (congrArg (fun z : Fin k → Γ(specialFibre p I (Scheme.unitModule U), g ⁻¹ᵁ O) =>
        ∑ i, (biproduct.ι (fun _ : Fin k => specialFibre p I (Scheme.unitModule U)) i).app
          (g ⁻¹ᵁ O) (z i)) (funext hm)).trans
      (app_eq_sum_biproduct_ι_π
        (fun _ : Fin k => specialFibre p I (Scheme.unitModule U)) (g ⁻¹ᵁ O) σ).symm
  have hcomb : (pushforwardAdicProj p g I (n + 1)).app O (∑ i, a i • m i : Γ(V, O)) =
      (pushforwardAdicProj p g I (n + 1)).app O s := by
    refine hstep1.trans ?_
    refine Eq.trans
      (congrArg (fun z => (gradedDescToQuotient p I n a ha e).app (g ⁻¹ᵁ O) z) hstep2) ?_
    refine Eq.trans ?_ hy
    exact congrArg
      (fun z => Scheme.Modules.Hom.app
        ((gradedPiece p I n (Scheme.unitModule U)).ι :
          ((gradedPiece p I n (Scheme.unitModule U)).toSheafOfModules : U.Modules) ⟶
            adicQuotient p I (n + 1) (Scheme.unitModule U)) (g ⁻¹ᵁ O) z) hσ
  have hfin : (pushforwardAdicProj p g I (n + 1)).app O (s - ∑ i, a i • m i : Γ(V, O)) =
      (pushforwardAdicProj p g I (n + 1)).app O s -
        (pushforwardAdicProj p g I (n + 1)).app O (∑ i, a i • m i : Γ(V, O)) :=
    map_sub _ _ _
  rw [hfin, hcomb, sub_self]

end Stacks.BaseAdicFiltration

end
