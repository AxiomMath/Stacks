module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPrime
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicityAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.RingTheory.Length.LocalizationModelIndependence

/-!
# The length of a quasi-coherent module at a point of an affine chart

Let `X` be an algebraic space, `F` a quasi-coherent `𝒪_X`-module, `W` an étale chart of `X`
whose scheme is affine, and `u` a point of that scheme lying over the image of a geometric point
`x̄`.  The length of `F` at `x̄` is the length of the localization of the sections `F(W)` at the
prime `AlgebraicGeometry.Space.chartPrimeAt` of `Γ(W, 𝒪)` cut out by `u`, over the localization of
`Γ(W, 𝒪)` at that prime.

## Main results

* `AlgebraicGeometry.length_stalk_eq_length_localizedModule`: on a scheme, the length of the
  stalk at `x` of a quasi-coherent module is the length of the localization at the prime of `x`
  of its sections over an affine open containing `x` — or of any module semilinearly isomorphic
  to the sections of a module isomorphic to it.
* `AlgebraicGeometry.Space.geometricLength_eq_length_localizedModule_chartPrimeAt`: the statement
  above for algebraic spaces.

## Implementation notes

By `AlgebraicGeometry.Space.geometricLength_eq_length_stalk_restrictToChart` the length at `x̄`
is the length of the stalk at `u` of the chart restriction `F|_W`.  That restriction is
isomorphic to `AlgebraicGeometry.Space.chartRestrictionSheaf`, whose sections over `⊤` are the
sections of `F` over the chart cut out by `⊤`, which is `W` itself
(`AlgebraicGeometry.Space.chartOpensTopHom`).  On the scheme side the stalk is a localization of
the sections over the affine open `⊤` (`Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ`),
and `Module.length_eq_of_isLocalization_of_isLocalizedModule` turns this into the length
statement.

The scheme-level lemma takes the isomorphism `N ≅ M` and the semilinear identification of `E`
with the sections of `N` as hypotheses, rather than the sections of `M` themselves, so that the
module structure on the sections of the chart restriction is only ever used in a context where
both modules are variables: in the context of the chart, matching the two module structures on
the sections of `AlgebraicGeometry.Space.restrictToChart` unfolds its sheafification and times
out.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- **The length of a stalk of a quasi-coherent module is the length of a localized module of
sections.**  Let `M` be a quasi-coherent module on a scheme `Y`, let `x` be a point of an affine
open `U`, and let `E` be a `Γ(Y, U)`-module with a semilinear additive isomorphism onto the
sections over `U` of a module `N` isomorphic to `M`.  Then the length of the stalk `M_x` over
`𝒪_{Y, x}` is the length of `E` localized at the prime of `x`, over the localization of
`Γ(Y, U)` at that prime. -/
theorem length_stalk_eq_length_localizedModule {Y : Scheme.{u}} {M N : Y.Modules}
    [M.IsQuasicoherent] (ι : N ≅ M) {U : Y.Opens} (hU : IsAffineOpen U) {x : Y} (hx : x ∈ U)
    {E : Type u} [AddCommGroup E] [Module Γ(Y, U) E] (e : E ≃+ Γ(N, U))
    (he : ∀ (c : Γ(Y, U)) (y : E), e (c • y) = c • e y) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule M x
    Module.length (Y.presheaf.stalk x) (M.presheaf.stalk x) =
      Module.length (Localization.AtPrime (Ideal.comap (Y.presheaf.germ U x hx).hom
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk x))))
        (LocalizedModule (Ideal.comap (Y.presheaf.germ U x hx).hom
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk x))).primeCompl E) := by
  let := (Y.presheaf.germ U x hx).hom.toAlgebra
  let := Stacks.ModuleStalkSpecialization.stalkModule M x
  let := Stacks.ModuleStalkSpecialization.sectionsStalkModule M hx
  have := Stacks.ModuleStalkSpecialization.isScalarTower_sectionsStalk M hx
  have hloc₀ : IsLocalization.AtPrime (Y.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  have hP : (hU.primeIdealOf ⟨x, hx⟩).asIdeal = Ideal.comap (Y.presheaf.germ U x hx).hom
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk x)) :=
    (IsLocalization.AtPrime.under_maximalIdeal (Y.presheaf.stalk x) _).symm
  have hS : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl = (Ideal.comap
      (Y.presheaf.germ U x hx).hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk x))).primeCompl :=
    Submonoid.ext fun a => by rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hP]
  have : IsLocalization (Ideal.comap (Y.presheaf.germ U x hx).hom
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk x))).primeCompl (Y.presheaf.stalk x) := by
    rwa [← hS]
  let ψ : E ≃ₗ[Γ(Y, U)] Γ(M, U) :=
    { e.trans (((Scheme.Modules.toPresheaf Y).mapIso ι).app (op U)).addCommGroupIsoToAddEquiv with
      map_smul' := fun c y => (congrArg (ι.hom.app U) (he c y)).trans
        (Scheme.Modules.Hom.app_smul ι.hom c (e y)) }
  have : IsLocalizedModule (Ideal.comap (Y.presheaf.germ U x hx).hom
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk x))).primeCompl
      (Stacks.ModuleStalkSpecialization.germₗ M hx ∘ₗ ψ.toLinearMap) := by
    rw [← hS]
    have : IsLocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
        (Stacks.ModuleStalkSpecialization.germₗ M hx) :=
      Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ M hU hx
    exact IsLocalizedModule.of_linearEquiv_right _ _ ψ
  exact (Module.length_eq_of_isLocalization_of_isLocalizedModule _ (Y.presheaf.stalk x)
    (Stacks.ModuleStalkSpecialization.germₗ M hx ∘ₗ ψ.toLinearMap)).symm

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The length of a quasi-coherent module at a geometric point, on an affine chart.**  Let `F`
be a quasi-coherent `𝒪_X`-module, let `W` be an étale chart of `X` whose scheme is affine, and
let `u` be a point of that scheme lying over the image of the geometric point `x̄`.  Then the
length of `F` at `x̄` is the length of `F(W)` localized at the prime
`AlgebraicGeometry.Space.chartPrimeAt` of `u`, over the localization of `Γ(W, 𝒪)` at that prime.

The length at `x̄` is the length of the stalk of the chart restriction at `u`
(`AlgebraicGeometry.Space.geometricLength_eq_length_stalk_restrictToChart`), and the chart
restriction is a quasi-coherent module on the affine scheme of `W` whose sections over `⊤` are
`F(W)`, so `AlgebraicGeometry.length_stalk_eq_length_localizedModule` applies. -/
theorem geometricLength_eq_length_localizedModule_chartPrimeAt (X : AlgebraicSpaces B S hS)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (xbar : GeometricPoint B S hS X.1) (W : SmallEtale B S hS X.1)
    (hW : IsAffine (chartScheme W)) (u : chartScheme W)
    (hu : chartSchemeToPoints B S hS X.1 W u = xbar.image) :
    geometricLength B S hS X xbar F =
      Module.length (Localization.AtPrime (chartPrimeAt B S hS X.2 W u))
        (LocalizedModule (chartPrimeAt B S hS X.2 W u).primeCompl (F.val.obj (op W))) := by
  rw [geometricLength_eq_length_stalk_restrictToChart B S hS X F xbar W u hu]
  let M : (chartScheme W).Modules := restrictToChart B S hS X.2 F W
  have : M.IsQuasicoherent := isQuasicoherent_restrictToChart B S hS X F inferInstance W
  let e : (F.val.obj (op W) : Type u) ≃+
      (Γ(chartRestrictionSheaf B S hS X F W, ⊤) : Type u) :=
    (F.val.presheaf.mapIso
        (asIso (chartOpensTopHom B S hS X W)).op).addCommGroupIsoToAddEquiv.trans
      AddEquiv.ulift.symm
  have he : ∀ (c : Γ(chartScheme W, ⊤)) (y : (F.val.obj (op W) : Type u)),
      e (c • y) = c • e y :=
    fun c y => congrArg ULift.up (F.val.map_smul (chartOpensTopHom B S hS X W).op c y)
  exact length_stalk_eq_length_localizedModule (M := M)
    (restrictToChartIsoChartRestrictionSheaf B S hS X F W).symm (isAffineOpen_top _)
    (x := u) trivial e he

end AlgebraicGeometry.Space

end
