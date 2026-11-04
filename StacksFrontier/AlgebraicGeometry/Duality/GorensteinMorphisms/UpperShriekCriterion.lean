module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.GorensteinFibresLocalization
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModelTargetIso
public import StacksFrontier.AlgebraicGeometry.Discriminant.GorensteinLocus
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.AffineConservative
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingBaseChange.FibreDualizing
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.OpenLocus
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.DerivedTildeInvertible
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.StalkwiseInvertible
public import
  StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.StalkwiseInvertibleLocalization
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekStructureSheafChartsPredicate
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreLocalRing
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeRestriction
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsSelfIso
public import StacksFrontier.RingTheory.Dualizing.LocalizationAwayDualizing
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.GorensteinFibres
import all StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulayLocus
import all StacksFrontier.RingTheory.Dualizing.InvertibleHomologySingle

/-!
# Gorenstein points of a flat morphism and invertibility of `f^!𝒪_Y`

Let `S` be a Noetherian scheme and `f : X ⟶ Y` a flat morphism of `AlgebraicGeometry.FTS S`
([Stacks, Tag 0F42]). This file proves that `f` is Gorenstein at a point `x` exactly when the
relative dualizing complex `ω^•_{X/Y} = f^!𝒪_Y` is invertible on a neighbourhood of `x`, given the
affine chart description of `f^!𝒪_Y` over affine opens.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isGorensteinAt_fromSpec_iff`: on an affine chart, Gorensteinness of
  `f` at a point is Gorensteinness of the local ring of the fibre algebra at the matching prime.
* `Stacks.Duality.isGorensteinRing_fiber_of_isGorensteinLocalRing_affineFiberPoint`: the fibre
  algebras of a chart are Gorenstein when the local rings at the matching primes all are.
* `Stacks.Duality.isInvertible_derivedStalkFunctor_of_isInvertible_restrict`: an object of
  `D(𝒪_X)` invertible on an open `W` has invertible derived stalks at the points of `W`.
* `Stacks.Duality.isGorensteinAt_iff_exists_isInvertible_of_charts`: the criterion, given the
  chart description.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-! ### Gorenstein points on an affine chart -/

/-- The chart algebra of a flat, locally finitely presented morphism over affine opens is flat and
finitely presented, and admits a polynomial presentation. -/
private theorem chart_algebra_flat_finitePresentation {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [LocallyOfFinitePresentation f] {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens}
    (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) :
    letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    Module.Flat Γ(Y, V) Γ(X, U) ∧ Algebra.FinitePresentation Γ(Y, V) Γ(X, U) ∧
      Nonempty (Dualizing.PolynomialPresentation (algebraMap Γ(Y, V) Γ(X, U))) := by
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have hfp : Algebra.FinitePresentation Γ(Y, V) Γ(X, U) :=
    HasRingHomProperty.appLE @LocallyOfFinitePresentation f inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV
  exact ⟨HasRingHomProperty.appLE @Flat f inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV, hfp,
    Dualizing.nonempty_polynomialPresentation _ (RingHom.finiteType_algebraMap.mpr inferInstance)⟩

namespace AlgebraicGeometry.Scheme.Hom

/-- **Gorensteinness at a point of an affine chart is Gorensteinness of a fibre local ring.** Let
`f` be flat and locally of finite presentation, `U ⊆ f⁻¹(V)` affine opens. Then `f` is Gorenstein
at the point of `U` given by a prime `z` of `Γ(X, U)` exactly when the localization of the fibre
algebra `κ(z ∩ Γ(S, V)) ⊗ Γ(X, U)` at the prime matching `z` is Gorenstein. -/
theorem isGorensteinAt_fromSpec_iff {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens}
    (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) (z : PrimeSpectrum Γ(X, U)) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    ∀ [IsNoetherianRing (Localization.AtPrime (affineFiberPoint (R := Γ(S, V)) z).asIdeal)],
      f.IsGorensteinAt (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f)
          (hU.fromSpec z) ↔
        Dualizing.IsGorensteinLocalRing
          (Localization.AtPrime (affineFiberPoint (R := Γ(S, V)) z).asIdeal) := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  intro _
  obtain ⟨_, _, -⟩ := chart_algebra_flat_finitePresentation f hU hV hUV
  let f' : Spec (.of Γ(X, U)) ⟶ Spec (.of Γ(S, V)) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, U)))
  have : LocallyOfFinitePresentation f' :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have w : hU.fromSpec ≫ f = f' ≫ hV.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV).symm
  exact (isGorensteinAt_iff_of_comp_eq hU.fromSpec hV.fromSpec f f' w _
    (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f')
    (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation _) z).trans
    (isGorensteinAt_specMap_iff _ z)

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Duality

/-! ### Fibre algebras from fibre local rings -/

/-- **The fibre algebras of a chart are Gorenstein when the fibre local rings at the matching
primes are.** For `R → A` of finite type, if for every prime `z` of `A` the localization of the
fibre algebra over `z ∩ R` at the prime matching `z` is Gorenstein, then every fibre algebra
`κ(P) ⊗_R A` is a Gorenstein ring: each of its primes matches the prime of `A` it contracts to. -/
theorem isGorensteinRing_fiber_of_isGorensteinLocalRing_affineFiberPoint {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A] (p : Dualizing.PolynomialPresentation (algebraMap R A))
    (h : ∀ z : PrimeSpectrum A,
      letI := Dualizing.isNoetherianRing_baseChange
        (PrimeSpectrum.comap (algebraMap R A) z).asIdeal.ResidueField p
      Dualizing.IsGorensteinLocalRing
        (Localization.AtPrime (affineFiberPoint (R := R) z).asIdeal))
    (P : Ideal R) [P.IsPrime] :
    letI := Dualizing.isNoetherianRing_baseChange P.ResidueField p
    Dualizing.IsGorensteinRing (P.Fiber A) := by
  let := Dualizing.isNoetherianRing_baseChange P.ResidueField p
  intro Q _
  let z₀ := (PrimeSpectrum.preimageEquivFiber R A ⟨P, inferInstance⟩).symm ⟨Q, inferInstance⟩
  have key : ∀ (P₁ : PrimeSpectrum R) (_ : P₁ = PrimeSpectrum.comap (algebraMap R A) z₀.1)
      (Q₁ : Ideal (P₁.asIdeal.Fiber A)) [Q₁.IsPrime],
      Q₁.comap (Algebra.TensorProduct.includeRight :
        A →ₐ[R] P₁.asIdeal.Fiber A).toRingHom = z₀.1.asIdeal →
      letI := Dualizing.isNoetherianRing_baseChange P₁.asIdeal.ResidueField p
      Dualizing.IsGorensteinLocalRing (Localization.AtPrime Q₁) := by
    intro P₁ hP₁ Q₁ _ hQ₁
    subst hP₁
    have hQ := Stacks.Discriminant.fiber_prime_eq_of_comap_eq _ Q₁
      (affineFiberPoint (R := R) z₀.1).asIdeal (hQ₁.trans (affineFiberPoint_comap z₀.1).symm)
    subst hQ
    exact h z₀.1
  exact key ⟨P, inferInstance⟩ z₀.2.symm Q rfl

/-! ### From invertibility on an open to invertibility of derived stalks -/

section Restrict

attribute [local instance 10000] HasDerivedCategory.standard

/-- **An object invertible on an open has invertible derived stalks there.** If the restriction of
`E ∈ D(𝒪_X)` to an open `W` is invertible, then for `x ∈ W` the derived stalk `E_x` is an
invertible object of `D(𝒪_{X,x})`: the derived stalk at `x` of `E|_W` is invertible, and it is the
extension of scalars of `E_x` along the isomorphism `𝒪_{X,x} ≅ 𝒪_{W,x}`. -/
theorem isInvertible_derivedStalkFunctor_of_isInvertible_restrict {X : Scheme.{u}}
    (W : X.Opens) (E : DerivedCategory X.Modules) (x : W.toScheme)
    (h : letI := Scheme.Modules.derivedMonoidal W.toScheme
      MonoidalCategory.IsInvertible
        ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj E)) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
      (X.presheaf.stalk (W.ι.base x))).choose
    MonoidalCategory.IsInvertible ((derivedStalkFunctor (W.ι.base x)).obj E) := by
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    (X.presheaf.stalk (W.ι.base x))).choose
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    (W.toScheme.presheaf.stalk x)).choose
  have h₁ : MonoidalCategory.IsInvertible ((derivedStalkFunctor x).obj
      ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj E)) :=
    isInvertible_derivedStalkFunctor_of_isInvertible (X := W.toScheme) x _ h
  let σ : X.presheaf.stalk (W.ι.base x) ≃+* W.toScheme.presheaf.stalk x :=
    stalkRingEquivOfIsOpenImmersion W.ι x
  let M := (derivedStalkFunctor (W.ι.base x)).obj E
  let e₁ : (derivedStalkFunctor x).obj
        ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj E) ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        σ.toRingHom).functor.obj M :=
    (derivedStalkFunctor x).mapIso
      ((Scheme.Modules.derivedRestrictIsoDerivedPullback W.ι).app E) ≪≫
    (derivedPullbackStalkIso W.ι x).app E
  obtain ⟨n, ⟨e₂⟩⟩ := (Dualizing.isInvertible_iff_exists_iso_single _).1
    (MonoidalCategory.isInvertible_of_iso e₁ h₁)
  refine (Dualizing.isInvertible_iff_exists_iso_single M).2 ⟨n, ⟨?_⟩⟩
  exact ((CochainComplex.DerivedExtensionScalars.totalDerivedExtendRestrictScalarsSelfIso.{u, u}
      σ).app M).symm ≪≫
    (ModuleCat.restrictScalars σ.toRingHom).mapDerivedCategory.mapIso e₂ ≪≫
    Dualizing.restrictScalarsEquivSingleIso σ n

end Restrict

/-! ### The criterion -/

section Criterion

variable {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] {X Y : AlgebraicGeometry.FTS S}
  (f : X ⟶ Y) (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The fibres of a morphism of `AlgebraicGeometry.FTS S` are locally Noetherian. -/
theorem isLocallyNoetherian_fiber_left (f : X ⟶ Y) :
    ∀ y : Y.left, IsLocallyNoetherian (f.left.fiber y) := fun _ => inferInstance

variable {f j}

/-- **The Gorenstein criterion, from the chart description.** For a flat morphism `f` of
`AlgebraicGeometry.FTS S` whose `f^!𝒪_Y` has the affine chart description, `f` is Gorenstein at
`x` exactly when `f^!𝒪_Y` is an invertible object of `D(𝒪_W)` on some open neighbourhood `W` of
`x`.

If `f` is Gorenstein at `x`, it is Gorenstein on an affine neighbourhood `U` of `x` over an affine
`V` ([Stacks, Tag 0C09]), so all fibre algebras of `Γ(Y, V) → Γ(X, U)` are Gorenstein and
`ω_{Γ(X, U)/Γ(Y, V)}` is invertible ([Stacks, Tag 0E4C]); its associated sheaf, which is `f^!𝒪_Y`
on `U`, is then invertible. Conversely an object invertible near `x` has invertible derived stalk
at `x`; on a chart this is the localization of `ω_{Γ(X, U)/Γ(Y, V)}` at the prime of `x`, and that
being invertible makes the local ring of the fibre at `x` Gorenstein. -/
theorem isGorensteinAt_iff_exists_isInvertible_of_charts [Flat f.left]
    (hchart : UpperShriekStructureSheafCharts f j) (x : X.left) :
    f.left.IsGorensteinAt (isLocallyNoetherian_fiber_left f) x ↔
      ∃ W : X.left.Opens, x ∈ W ∧
        letI := Scheme.Modules.derivedMonoidal W.toScheme
        MonoidalCategory.IsInvertible
          ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj
            (relativeDualizingComplexObj f j)) := by
  have hYn : IsLocallyNoetherian Y.left := by
    have : IsLocallyNoetherian ((Functor.fromPUnit S).obj Y.right) :=
      inferInstanceAs (IsLocallyNoetherian S)
    exact LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have hXn : IsLocallyNoetherian X.left := by
    have : IsLocallyNoetherian ((Functor.fromPUnit S).obj X.right) :=
      inferInstanceAs (IsLocallyNoetherian S)
    exact LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_left f
  have : LocallyOfFinitePresentation f.left := inferInstance
  -- an affine chart through `x`, inside a given open neighbourhood
  have chart : ∀ G : X.left.Opens, x ∈ G → ∃ (V : Y.left.Opens) (hV : IsAffineOpen V)
      (U : X.left.Opens) (hU : IsAffineOpen U) (hUV : U ≤ f.left ⁻¹ᵁ V), x ∈ U ∧ U ≤ G := by
    intro G hxG
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      Y.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.left x)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUsub⟩ :=
      X.left.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ ((f.left ⁻¹ᵁ V ⊓ G : X.left.Opens) : Set X.left) from ⟨hxV, hxG⟩)
        (f.left ⁻¹ᵁ V ⊓ G).isOpen
    exact ⟨V, hV, U, hU, fun z hz => (hUsub hz).1, hxU, fun z hz => (hUsub hz).2⟩
  constructor
  · intro hG
    let G : X.left.Opens := ⟨{z | f.left.IsGorensteinAt
      (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f.left) z},
      Scheme.Hom.isOpen_setOf_isGorensteinAt f.left⟩
    obtain ⟨V, hV, U, hU, hUV, hxU, hUG⟩ := chart G hG
    let : Algebra Γ(Y.left, V) Γ(X.left, U) := (f.left.appLE V U hUV).hom.toAlgebra
    have : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    have : IsNoetherianRing Γ(X.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    obtain ⟨_, hfp, ⟨p⟩⟩ := chart_algebra_flat_finitePresentation f.left hU hV hUV
    have hfib := isGorensteinRing_fiber_of_isGorensteinLocalRing_affineFiberPoint p
      (fun z => by
        let := Dualizing.isNoetherianRing_baseChange
          (PrimeSpectrum.comap (algebraMap Γ(Y.left, V) Γ(X.left, U)) z).asIdeal.ResidueField p
        exact (Scheme.Hom.isGorensteinAt_fromSpec_iff f.left hU hV hUV z).1
          (hUG (hU.range_fromSpec.le ⟨z, rfl⟩)))
    obtain ⟨e⟩ := hchart V hV U hU hUV p
    exact ⟨U, hxU, @MonoidalCategory.isInvertible_of_iso _ _
      (Scheme.Modules.derivedMonoidal U.toScheme) _ _ e.symm
      (isInvertible_tilde_restrict_of_isInvertible hU
        ((Dualizing.isGorensteinRing_fiber_iff_isInvertible_upperShriekFunctor_unit p).1 hfib))⟩
  · rintro ⟨W, hxW, hW⟩
    let ω := relativeDualizingComplexObj f j
    let Φ := StacksDraft.DerivedModel.schemeModulesComparison W.toScheme
    -- the restriction to `W`, read at the standard model
    let Mstd := @Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _
      (HasDerivedCategory.standard _) (Scheme.Modules.restrictFunctor W.ι) _ _ _ |>.obj ω
    let c : Φ.functor.obj Mstd ≅ Φ.functor.obj
        ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj ω) :=
      (Stacks.Injectives.mapDerivedCategoryTargetModelIso W.toScheme.Modules
          (hd₁ := HasDerivedCategory.standard _) (Scheme.Modules.restrictFunctor W.ι)).app ω ≪≫
        Stacks.Injectives.mapDerivedCategoryObjIso X.left.Modules
          (Scheme.Modules.restrictFunctor W.ι) ω
    have hstd := (Scheme.Modules.isInvertible_standard_iff W.toScheme _).2 hW
    have hMstd : @MonoidalCategory.IsInvertible _ _
        (@Scheme.Modules.derivedMonoidal W.toScheme (HasDerivedCategory.standard _)) Mstd :=
      @MonoidalCategory.isInvertible_of_iso _ _
        (@Scheme.Modules.derivedMonoidal W.toScheme (HasDerivedCategory.standard _)) _ _
        (Φ.functor.preimageIso c).symm hstd
    have hstalk := @isInvertible_derivedStalkFunctor_of_isInvertible_restrict X.left W ω
      ⟨x, hxW⟩ hMstd
    -- an affine chart through `x`
    obtain ⟨V, hV, U, hU, hUV, hxU, -⟩ := chart ⊤ trivial
    let : Algebra Γ(Y.left, V) Γ(X.left, U) := (f.left.appLE V U hUV).hom.toAlgebra
    have : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    have : IsNoetherianRing Γ(X.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    obtain ⟨_, hfp, ⟨p⟩⟩ := chart_algebra_flat_finitePresentation f.left hU hV hUV
    let K := p.upperShriekFunctor.{u, 0}.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Y.left, V)) 0).obj
        (ModuleCat.of Γ(Y.left, V) Γ(Y.left, V)))
    obtain ⟨e⟩ := hchart V hV U hU hUV p
    let e' := Stacks.Injectives.mapDerivedCategoryObjIso X.left.Modules
      (Scheme.Modules.restrictFunctor U.ι) ω ≪≫ e
    -- the cohomology sheaves of `ω`, at the standard model, are quasi-coherent
    have hQ : ∀ i : ℤ, ((@DerivedCategory.homologyFunctor X.left.Modules _ _
        (HasDerivedCategory.standard _) i).obj ω).IsQuasicoherent := fun i =>
      isQuasicoherent_of_iso _ _ _ ((homologyFunctorModelIso X.left.Modules i).app ω)
        (((upperShriek f j).obj (DerivedPushforward.derivedStructureSheaf Y.left)).property i)
    have hω : ∀ i : ℤ, Nonempty (Stacks.AlgebraicGeometry.CoherentTFAE.specModule
        ((@DerivedCategory.homologyFunctor X.left.Modules _ _
        (HasDerivedCategory.standard _) i).obj ω) hU ≅
        (@DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X.left, U)) _ _
          (HasDerivedCategory.standard _) i).obj K) := fun i =>
      ⟨specModuleIsoOfTildeIso _ hU _
        (@homologyRestrictIsoTilde X.left (HasDerivedCategory.standard _) ω U hU K e' i)⟩
    have hloc := (@isInvertible_derivedStalk_iff_of_specModule_iso X.left
      (HasDerivedCategory.standard _) ω hQ U hU x hxU K hω).1 hstalk
    -- the pointwise criterion at the local ring of `x`
    let z := hU.primeIdealOf ⟨x, hxU⟩
    let : Algebra Γ(X.left, U) (X.left.presheaf.stalk x) :=
      X.left.presheaf.algebra_section_stalk ⟨x, hxU⟩
    have : IsLocalization.AtPrime (X.left.presheaf.stalk x) z.asIdeal :=
      hU.isLocalization_stalk ⟨x, hxU⟩
    let := Dualizing.isNoetherianRing_baseChange
      (PrimeSpectrum.comap (algebraMap Γ(Y.left, V) Γ(X.left, U)) z).asIdeal.ResidueField p
    let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X.left, U))
    let := HasDerivedCategory.standard (ModuleCat.{u} (X.left.presheaf.stalk x))
    have hInv := @MonoidalCategory.isInvertible_of_iso _ _
      (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
        (X.left.presheaf.stalk x)).choose _ _
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap Γ(X.left, U) (X.left.presheaf.stalk x))).functor.mapIso
          ((Dualizing.uliftDerivedSelfIso Γ(X.left, U)).app K)) hloc
    have hR := Dualizing.isGorensteinLocalRing_fiber_of_isInvertible_localization p z.asIdeal
      (X.left.presheaf.stalk x) _ _ (affineFiberPoint_comap z) hInv
    have hGz := (Scheme.Hom.isGorensteinAt_fromSpec_iff f.left hU hV hUV z).2 hR
    rwa [hU.fromSpec_primeIdealOf] at hGz

end Criterion

end Stacks.Duality

end
