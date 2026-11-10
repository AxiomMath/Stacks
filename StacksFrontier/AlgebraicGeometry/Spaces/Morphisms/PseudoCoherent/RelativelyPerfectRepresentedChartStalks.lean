module

public import StacksFrontier.AlgebraicGeometry.Perfect.InverseImageTorAmplitudeStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBridge
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectTorDimensionLocality
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictFunctorAlongIso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentZariskiTorTranslation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectEtaleLocalProof
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RepresentedDerivedPullbackComparisonConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfectSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineNoetherianEtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpensOfOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBranchCodimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquareCover

/-!
# Relative Tor amplitude at the points of a scheme, read on affine charts

Let `r : X ⟶ Y` be a morphism of schemes and `E ∈ D(𝒪_X)`.  The Tor clause of Stacks 0DI0,
`E` read over `r⁻¹𝒪_Y` locally has finite Tor dimension, is a local uniform bound on the Tor
amplitude of the stalks `E_y` over the local rings `𝒪_{Y, r(y)}`
(`AlgebraicGeometry.Space.exists_relStalkTorAmp_of_locallyHasFiniteTorDimension`,
`AlgebraicGeometry.Space.locallyHasFiniteTorDimension_of_forall_exists_relStalkTorAmp`).  On an
affine chart `j : Spec A ⟶ X` over an affine chart `k : Spec R ⟶ Y` (open immersions with
`j ≫ r = Spec(R → A) ≫ k`), the bound at `j(q)` is the Tor amplitude over `R_{q ∩ R}` of the
localisation at `q` of a complex `M` of `A`-modules with `j^*E ≅ M~`
(`AlgebraicGeometry.Space.relStalkTorAmp_openImmersionSquare_iff`,
`AlgebraicGeometry.Space.relStalkTorAmp_specMap_iff`).

For a morphism `g : T ⟶ T'` of the big fppf site such charts exist around every point
(`AlgebraicGeometry.Space.exists_representedAffineChartPiece`), and on the represented algebraic
space `h_T` the geometric stalks of the pullback of `ε^*E₀` to such a chart, read over the base,
have the same Tor amplitudes (Stacks 04KF, 05VL, 05V5, 04NG):
`AlgebraicGeometry.Space.exists_relStalkTorAmp_representedAffineChartPiece` and
`AlgebraicGeometry.Space.geometricStalkTorAmplitude_representedAffineChartPiece`.  These are the
inputs of Stacks 0DKQ at a represented chart
(`AlgebraicGeometry.Space.RelativelyPerfectRepresentedChart`), proved in
`RelativelyPerfectRepresentedChartProof.lean`.

Nothing here is registered.

## References

* [Stacks Project, Tag 0DKQ](https://stacks.math.columbia.edu/tag/0DKQ)
* [Stacks Project, Tag 0DI0](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 0DHY](https://stacks.math.columbia.edu/tag/0DHY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open StacksDraft.TorAmplitude
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry.Space

section SchemeStalks

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y Z : Scheme.{u}}

/-- The stalk of `E ∈ D(𝒪_X)` at `x`, read over the local ring `𝒪_{Y, r(x)}` along the stalk
map of `r : X ⟶ Y`, has Tor amplitude in `[a, b]`. -/
abbrev RelStalkTorAmp (r : X ⟶ Y) (E : DerivedCategory X.Modules) (x : X) (a b : ℤ) : Prop :=
  HasTorAmplitudeCanonicalLift.{u, u, u}
    ((ModuleCat.restrictScalars.{u} (r.stalkMap x).hom).mapDerivedCategory.obj
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategory.obj E)) a b

/-- The relative stalk bound is read on any complex representing the object. -/
theorem relStalkTorAmp_iff_relativeStalkComplex (r : X ⟶ Y) (K : CochainComplex X.Modules ℤ)
    {E : DerivedCategory X.Modules} (eK : DerivedCategory.Q.obj K ≅ E) (x : X) (a b : ℤ) :
    RelStalkTorAmp r E x a b ↔
      HasTorAmplitudeCanonicalLift.{u, u, u}
        (DerivedCategory.Q.obj (relativeStalkComplex r K x)) a b := by
  let e : DerivedCategory.Q.obj (relativeStalkComplex r K x) ≅
      (ModuleCat.restrictScalars.{u} (r.stalkMap x).hom).mapDerivedCategory.obj
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategory.obj E) :=
    relativeStalkComplexDerivedIso r K x ≪≫
      (ModuleCat.restrictScalars.{u} (r.stalkMap x).hom).mapDerivedCategory.mapIso
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategory.mapIso eK)
  exact ⟨fun h => hasTorAmplitudeCanonicalLift_of_iso e.symm a b h,
    fun h => hasTorAmplitudeCanonicalLift_of_iso e a b h⟩

/-- The relative stalk bound depends only on the isomorphism class of the object. -/
theorem relStalkTorAmp_of_iso (r : X ⟶ Y) {E E' : DerivedCategory X.Modules} (e : E ≅ E')
    (x : X) (a b : ℤ) (h : RelStalkTorAmp r E x a b) : RelStalkTorAmp r E' x a b :=
  hasTorAmplitudeCanonicalLift_of_iso
    ((ModuleCat.restrictScalars.{u} (r.stalkMap x).hom).mapDerivedCategory.mapIso
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategory.mapIso e)) a b h

/-- **The relative stalk bound is unchanged by composing the base morphism with an open
immersion**: the local rings of the base change by the stalk isomorphisms of the open
immersion. -/
theorem relStalkTorAmp_comp_openImmersion_iff (r : X ⟶ Y) (k : Y ⟶ Z)
    [_root_.AlgebraicGeometry.IsOpenImmersion k]
    (E : DerivedCategory X.Modules) (x : X) (a b : ℤ) :
    RelStalkTorAmp (r ≫ k) E x a b ↔ RelStalkTorAmp r E x a b := by
  let K := DerivedCategory.Q.objPreimage E
  let eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  rw [relStalkTorAmp_iff_relativeStalkComplex (r ≫ k) K eK,
    relStalkTorAmp_iff_relativeStalkComplex r K eK]
  exact hasTorAmplitudeCanonicalLift_restrictScalars_comp_iff (r.stalkMap x).hom
    (k.stalkMap (r.base x)).hom ((r ≫ k).stalkMap x).hom
    (asIso (k.stalkMap (r.base x))).commRingCatIsoToRingEquiv rfl
    (Stacks.ModuleSkyscraper.stalkMap_hom_comp r k x) _ a b

/-- **The derived pullback along an open immersion of schemes is restriction**, objectwise:
`Lj^*E ≅ E|_U`.  The derived pullback along an open immersion of ringed spaces is the functor
induced by degreewise inverse image
(`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso`), which is
restriction (`AlgebraicGeometry.Scheme.Modules.mapDerivedCategoryRestrictFunctorIsoPullback`). -/
def derivedPullbackObjIsoRestrictFunctorOfIsOpenImmersion {U : Scheme.{u}} (j : U ⟶ X)
    [_root_.AlgebraicGeometry.IsOpenImmersion j] (E : DerivedCategory X.Modules) :
    (derivedPullback j.toLRSHom.toShHom).obj E ≅
      (Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj E :=
  (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso
      j.toLRSHom.toShHom).app E ≪≫
    ((Scheme.Modules.mapDerivedCategoryRestrictFunctorIsoPullback j).app E).symm

/-- **The relative stalk bound on an open-immersion square.**  Let `j : U ⟶ X` and `k : V ⟶ Y` be
open immersions with `j ≫ r = t ≫ k`, and let `L ≅ E|_U`.  At a point `q` of `U` the stalk of `L`
read over `𝒪_{V, t(q)}` has Tor amplitude in `[a, b]` exactly when the stalk of `E` at `j(q)` read
over `𝒪_{Y, r(j(q))}` has. -/
theorem relStalkTorAmp_openImmersionSquare_iff {U V : Scheme.{u}} (r : X ⟶ Y) (j : U ⟶ X)
    [_root_.AlgebraicGeometry.IsOpenImmersion j] (t : U ⟶ V) (k : V ⟶ Y)
    [_root_.AlgebraicGeometry.IsOpenImmersion k] (h : j ≫ r = t ≫ k)
    (E : DerivedCategory X.Modules) (L : DerivedCategory U.Modules)
    (eL : (Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj E ≅ L) (q : U) (a b : ℤ) :
    RelStalkTorAmp t L q a b ↔ RelStalkTorAmp r E (j.base q) a b := by
  refine Iff.trans ⟨fun H => relStalkTorAmp_of_iso t eL.symm q a b H,
    fun H => relStalkTorAmp_of_iso t eL q a b H⟩ ?_
  refine (relStalkTorAmp_comp_openImmersion_iff t k _ q a b).symm.trans ?_
  rw [← h]
  exact Scheme.Hom.relativeStalkHasTorAmplitude_restrictFunctor_iff r j E a b q

/-- **The Tor clause of Stacks 0DI0 gives local uniform stalk bounds**: if `E`, read over
`r⁻¹𝒪_Y`, locally has finite Tor dimension, then every point of `X` has an open neighbourhood on
which one interval bounds the Tor amplitude of the stalks of `E` over the local rings of `Y`. -/
theorem exists_relStalkTorAmp_of_locallyHasFiniteTorDimension (r : X ⟶ Y)
    (E : DerivedCategory X.Modules)
    (h : RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage Y.toRingedSpace r.base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u} _)
      ((Scheme.Hom.derivedScalarRestriction r).obj E)) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ a b : ℤ, ∀ y ∈ U, RelStalkTorAmp r E y a b := by
  obtain ⟨I, U, hU, hI⟩ := h
  have hx : x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨a, b, hab⟩ := (Scheme.Hom.chartHasFiniteTorDimension_canonical_iff r E (U i)).1 (hI i)
  exact ⟨U i, hi, a, b, fun y hy => hab y hy⟩

/-- **Local uniform stalk bounds give the Tor clause of Stacks 0DI0**: if every point of `X` has
an open neighbourhood on which one interval bounds the Tor amplitude of the stalks of `E` over the
local rings of `Y`, then `E`, read over `r⁻¹𝒪_Y`, locally has finite Tor dimension. -/
theorem locallyHasFiniteTorDimension_of_forall_exists_relStalkTorAmp (r : X ⟶ Y)
    (E : DerivedCategory X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ a b : ℤ, ∀ y ∈ U, RelStalkTorAmp r E y a b) :
    RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage Y.toRingedSpace r.base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u} _)
      ((Scheme.Hom.derivedScalarRestriction r).obj E) := by
  choose U hxU a b hab using h
  refine Scheme.Hom.locallyHasFiniteTorDimension_of_isOpenCover r _ E X U ?_ fun x => ?_
  · exact le_antisymm le_top fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩
  · exact (Scheme.Hom.chartHasFiniteTorDimension_canonical_iff r E (U x)).2
      ⟨a x, b x, fun y hy => hab x y hy⟩

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- **The relative stalk bound on `Spec A ⟶ Spec R` of `M~`** is the Tor amplitude over
`R_{q ∩ R}` of the localisation of `M` at `q` (Stacks 0DHY at a prime). -/
theorem relStalkTorAmp_specMap_iff (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : DerivedCategory (Spec (CommRingCat.of A)).Modules)
    (eM : L ≅ DerivedCategory.Q.obj (Stacks.AffineTilde.tildeComplex M)) (q : PrimeSpectrum A)
    (a b : ℤ) :
    RelStalkTorAmp (AffineRelativeTorAmplitude.specMap R A) L q a b ↔
      HasTorAmplitudeAt R M q.asIdeal a b :=
  (relStalkTorAmp_iff_relativeStalkComplex _ _ eM.symm q a b).trans
    (AffineRelativeTorAmplitude.hasTorAmplitudeCanonicalLift_relativeStalkComplex_tilde_iff
      R A q M a b)

end SchemeStalks

/-! ### Affine charts of a morphism of the site -/

section ChartPiece

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An affine chart of a morphism `g : T ⟶ T'` of the big fppf site.**  Objects `Spec A` and
`Spec R` of the site with open immersions `α : Spec A ⟶ T` and `κ : Spec R ⟶ T'` on underlying
schemes, and an `R`-algebra structure on `A` with `α ≫ g = Spec(R → A) ≫ κ`. -/
structure RepresentedAffineChartPiece {T T' : BigFppfOver B S hS} (g : T ⟶ T') where
  /-- The ring of the chart of the target. -/
  R : Type u
  /-- The ring of the chart of the source. -/
  A : Type u
  [instCommRingR : CommRing R]
  [instCommRingA : CommRing A]
  [instAlgebra : Algebra R A]
  /-- `Spec R` lies in the site. -/
  hR : B.Contains (Spec (CommRingCat.of R))
  /-- The structure morphism of `Spec R`. -/
  gR : B.obj hR ⟶ B.obj hS
  /-- `Spec A` lies in the site. -/
  hA : B.Contains (Spec (CommRingCat.of A))
  /-- The structure morphism of `Spec A`. -/
  gA : B.obj hA ⟶ B.obj hS
  /-- `Spec A ⟶ Spec R` lies over `S`. -/
  w : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    B.obj hA ⟶ B.obj hR) ≫ gR = gA
  /-- The chart of the source. -/
  α : specFppfOver B S hS hA gA ⟶ T
  /-- The chart of the target. -/
  κ : specFppfOver B S hS hR gR ⟶ T'
  isOpenImmersion_α : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map α)
  isOpenImmersion_κ : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map κ)
  comm : α ≫ g = specFppfOverMap B S hS hR gR hA gA w ≫ κ

attribute [instance] RepresentedAffineChartPiece.instCommRingR
  RepresentedAffineChartPiece.instCommRingA RepresentedAffineChartPiece.instAlgebra
  RepresentedAffineChartPiece.isOpenImmersion_α RepresentedAffineChartPiece.isOpenImmersion_κ

/-- **Affine charts exist around every point.**  For `g : T ⟶ T'`, a point `x` of the scheme
underlying `T` and an open neighbourhood `N` of `x`, there is an affine chart of `g` whose chart
of the source contains `x` and lies in `N`: affine opens `U ∋ x` inside `N ∩ g⁻¹(V)` for an affine
open `V ∋ g(x)`, read as `Spec Γ(U) ⟶ Spec Γ(V)` along `g.appLE`. -/
theorem exists_representedAffineChartPiece {T T' : BigFppfOver B S hS} (g : T ⟶ T')
    {x : (BigFppfOver.toScheme B S hS).obj T} {N : ((BigFppfOver.toScheme B S hS).obj T).Opens}
    (hx : x ∈ N) :
    ∃ c : RepresentedAffineChartPiece g,
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map c.α) ∧
        Set.range ((BigFppfOver.toScheme B S hS).map c.α) ⊆ N := by
  let r := (BigFppfOver.toScheme B S hS).map g
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show r x ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj T').Opens) from trivial)
  obtain ⟨U, hU, hxU, hUN⟩ := exists_isAffineOpen_mem_and_subset
    (U := N ⊓ r ⁻¹ᵁ V) ⟨hx, hyV⟩
  have e : U ≤ r ⁻¹ᵁ V := fun z hz => (hUN hz).2
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj T', V)
      Γ((BigFppfOver.toScheme B S hS).obj T, U) := (r.appLE V U e).hom.toAlgebra
  have hA : B.Contains (Spec (CommRingCat.of Γ((BigFppfOver.toScheme B S hS).obj T, U))) :=
    Scheme.size_lt_of_isOpenImmersion hU.fromSpec T.left.2
  have hR : B.Contains (Spec (CommRingCat.of Γ((BigFppfOver.toScheme B S hS).obj T', V))) :=
    Scheme.size_lt_of_isOpenImmersion hV.fromSpec T'.left.2
  have hg : r ≫ B.inclusion.map T'.hom = B.inclusion.map T.hom :=
    (B.inclusion.map_comp g.left T'.hom).symm.trans (congrArg B.inclusion.map (Over.w g))
  let gA : B.obj hA ⟶ B.obj hS := ObjectProperty.homMk (hU.fromSpec ≫ B.inclusion.map T.hom)
  let gR : B.obj hR ⟶ B.obj hS := ObjectProperty.homMk (hV.fromSpec ≫ B.inclusion.map T'.hom)
  have hsq : Spec.map (r.appLE V U e) ≫ hV.fromSpec = hU.fromSpec ≫ r :=
    IsAffineOpen.SpecMap_appLE_fromSpec r hV hU e
  have w : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap
      Γ((BigFppfOver.toScheme B S hS).obj T', V) Γ((BigFppfOver.toScheme B S hS).obj T, U)))) :
      B.obj hA ⟶ B.obj hR) ≫ gR = gA := by
    apply ObjectProperty.hom_ext
    change Spec.map (r.appLE V U e) ≫ hV.fromSpec ≫ B.inclusion.map T'.hom =
      hU.fromSpec ≫ B.inclusion.map T.hom
    rw [← Category.assoc, hsq, Category.assoc, hg]
  let α : specFppfOver B S hS hA gA ⟶ T :=
    Over.homMk (ObjectProperty.homMk hU.fromSpec : B.obj hA ⟶ T.left) (by rfl)
  let κ : specFppfOver B S hS hR gR ⟶ T' :=
    Over.homMk (ObjectProperty.homMk hV.fromSpec : B.obj hR ⟶ T'.left) (by rfl)
  have hα : (BigFppfOver.toScheme B S hS).map α = hU.fromSpec := rfl
  have hκ : (BigFppfOver.toScheme B S hS).map κ = hV.fromSpec := rfl
  have : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map α) := by
    rw [hα]; infer_instance
  have : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map κ) := by
    rw [hκ]; infer_instance
  have comm : α ≫ g = specFppfOverMap B S hS hR gR hA gA w ≫ κ := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact hsq.symm
  refine ⟨⟨_, _, hR, gR, hA, gA, w, α, κ, inferInstance, inferInstance, comm⟩, ?_, ?_⟩
  · change x ∈ Set.range hU.fromSpec
    rwa [IsAffineOpen.range_fromSpec]
  · change Set.range hU.fromSpec ⊆ N
    rw [IsAffineOpen.range_fromSpec]
    exact fun z hz => (hUN hz).1

end ChartPiece

/-! ### The geometric stalks on the space side -/

section SpaceStalks

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The geometric-stalk Tor bound does not see an étale morphism of the base**: for `ψ` étale,
the geometric stalk of `E` at `x̄` has Tor amplitude in `[a, b]` over the stalk of
`(f' ≫ ψ)⁻¹𝒪` exactly when it has over the stalk of `f'⁻¹𝒪`, the stalk ring map along `ψ` being
bijective (Stacks 05V5, 04NG). -/
theorem geometricStalkTorAmplitude_comp_etale_iff {X Y Y' : AlgebraicSpaces B S hS}
    (f' : X ⟶ Y') (ψ : Y' ⟶ Y) (hψ : IsEtale B S hS ψ.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (x : GeometricPoint B S hS X.1)
    (a b : ℤ) :
    GeometricStalkTorAmplitude B S hS (f' ≫ ψ) E x a b ↔
      GeometricStalkTorAmplitude B S hS f' E x a b := by
  rw [stalkTorAmplitude_iff_stalkStructureMap, stalkTorAmplitude_iff_stalkStructureMap]
  have hb : Function.Bijective
      (stalkStructureMap B S hS ψ (geometricPointMap f'.hom x)).hom := by
    rw [stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap]
    exact bijective_smallEtaleStalkPullbackRingMap B S hS ψ hψ _
  refine (hasTorAmplitudeCanonical_restrictScalars_iff_of_ringEquiv (RingEquiv.ofBijective _ hb)
    (stalkStructureMap B S hS f' x).hom (stalkStructureMap B S hS (f' ≫ ψ) x).hom ?_ _ a b).symm
  refine RingHom.ext fun z => ?_
  change (stalkStructureMap B S hS (f' ≫ ψ) x).hom z = (stalkStructureMap B S hS f' x).hom
    ((stalkStructureMap B S hS ψ (geometricPointMap f'.hom x)).hom z)
  rw [stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap,
    stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap,
    stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap, smallEtaleStalkPullbackRingMap_comp_eq]
  rfl

variable {R : Type u} [CommRing R] (hR : B.Contains (Spec (CommRingCat.of R)))
  (gR : B.obj hR ⟶ B.obj hS) {A : Type u} [CommRing A] [Algebra R A]
  (hA : B.Contains (Spec (CommRingCat.of A))) (gA : B.obj hA ⟶ B.obj hS)
  (w : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    B.obj hA ⟶ B.obj hR) ≫ gR = gA)

/-- **The geometric-stalk Tor bound on `h_{Spec A} ⟶ h_{Spec R}`.**  For `E ≅ ε^*(P~)`, the
geometric stalk of `E` at `ū`, read over the stalk of `t⁻¹𝒪_{h_{Spec R}}`, has Tor amplitude in
`[a, b]` exactly when `P_q` has over `R_{q ∩ R}`, `q` the prime under `ū` (the chart reading of
`AlgebraicGeometry.Space.hasTorAmplitudeCanonical_geometricStalk_iff_hasTorAmplitudeAt` at the
identity chart). -/
theorem geometricStalkTorAmplitude_specFppfOverMap_iff
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj (specFppfOver B S hS hA gA))
      (isAlgebraicSpace_yoneda B S hS _)))
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (eP : E ≅ (representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA gA)).obj
      ((tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor (Iso.refl
        ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA))).hom).mapDerivedCategory.obj
          (DerivedCategory.Q.obj P)))
    (ū : GeometricPoint B S hS (yoneda.obj (specFppfOver B S hS hA gA))) (a b : ℤ) :
    GeometricStalkTorAmplitude B S hS
        (representedSpaceMap B S hS (specFppfOverMap B S hS hR gR hA gA w)) E ū a b ↔
      HasTorAmplitudeAt R P (identityChartPrime B S hS hA gA ū).asIdeal a b := by
  let X : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj (specFppfOver B S hS hA gA), isAlgebraicSpace_yoneda B S hS _⟩
  have hid : IsEtale B S hS (𝟙 X : X ⟶ X).hom := isEtale_of_isIso B S hS _
  exact hasTorAmplitudeCanonical_geometricStalk_iff_hasTorAmplitudeAt B S hS hR gR hA gA
    (representedSpaceMap B S hS (specFppfOverMap B S hS hR gR hA gA w)) (𝟙 X) w
    (Category.id_comp _).symm ū hid E P
    (etaleModulePullbackIdDerivedObjIso B S hS X hid E ≪≫ eP) a b

end SpaceStalks

/-! ### The tilde model of an object of `D_QCoh(𝒪_{Spec A})` -/

section TildeModel

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
  (gA : B.obj hA ⟶ B.obj hS)

/-- **An object of `D_QCoh(𝒪_{Spec A})` is `M~`** (Stacks 06Z0), read both on the Zariski site and,
through `ε^*`, on the small étale site of `h_{Spec A}`. -/
theorem exists_tildeModel_specFppfOver
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing
      ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA)).toRingedSpace)))
    (hLqc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA)).Modules n).obj
        L).IsQuasicoherent) :
    ∃ M : CochainComplex (ModuleCat.{u} A) ℤ,
      Nonempty (L ≅ DerivedCategory.Q.obj (Stacks.AffineTilde.tildeComplex M)) ∧
        Nonempty ((zariskiEtaleDerived B S hS _).obj L ≅
          (representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA gA)).obj
            ((tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
              (Iso.refl ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA))).hom
              ).mapDerivedCategory.obj (DerivedCategory.Q.obj M))) := by
  obtain ⟨M, ⟨eM⟩⟩ := AlgebraicGeometry.exists_tildeComplex_iso (CommRingCat.of A) L hLqc
  let T : ModuleCat.{u} A ⥤
      ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA)).Modules :=
    tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
      (Iso.refl ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA))).hom
  let c : (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj M ≅
      ((tilde.functor (CommRingCat.of A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj M :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i => (Scheme.Modules.restrictFunctorId (X := Spec (CommRingCat.of A))).app
        ((tilde.functor (CommRingCat.of A)).obj (M.X i)))
      (fun i j _ => (Scheme.Modules.restrictFunctorId
        (X := Spec (CommRingCat.of A))).hom.naturality
        ((tilde.functor (CommRingCat.of A)).map (M.d i j)))
  let eT : T.mapDerivedCategory.obj (DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj (((tilde.functor (CommRingCat.of A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M) :=
    T.mapDerivedCategoryFactors.app M ≪≫ DerivedCategory.Q.mapIso c
  exact ⟨M, ⟨eM⟩, ⟨(zariskiEtaleDerived B S hS _).mapIso (eM ≪≫ eT.symm)⟩⟩

end TildeModel

/-! ### The relative Tor bound on an affine chart, across `ε^*` -/

section ChartTor

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The represented morphism of a morphism of the site which is an open immersion on underlying
schemes is étale. -/
theorem isEtale_yoneda_map_of_isOpenImmersion {V U : BigFppfOver B S hS} (u : V ⟶ U)
    [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map u)] :
    IsEtale B S hS (yoneda.map u) := by
  have h := @isEtale_yoneda_map_comp_of_isOpenImmersion B S hS (yoneda.obj U)
    (idEtaleChart B S hS U) V u ‹_›
  exact (show yoneda.map u ≫ (idEtaleChart B S hS U).obj.hom = yoneda.map u from
    Category.comp_id _) ▸ h

variable {T T' : BigFppfOver B S hS} {Y : AlgebraicSpaces B S hS} {g : T ⟶ T'}
  (c : RepresentedAffineChartPiece g)

/-- The square of represented morphisms of an affine chart of `g`, followed by `b`. -/
theorem representedAffineChartPiece_sq (b : yoneda.obj T' ⟶ Y.1) :
    representedSpaceMap B S hS c.α ≫
        (ObjectProperty.homMk (yoneda.map g ≫ b) :
          (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y) =
      representedSpaceMap B S hS (specFppfOverMap B S hS c.hR c.gR c.hA c.gA c.w) ≫
        (representedSpaceMap B S hS c.κ ≫ ObjectProperty.homMk b) := by
  apply ObjectProperty.hom_ext
  change yoneda.map c.α ≫ yoneda.map g ≫ b =
    yoneda.map (specFppfOverMap B S hS c.hR c.gR c.hA c.gA c.w) ≫ yoneda.map c.κ ≫ b
  rw [← Category.assoc, ← Functor.map_comp, c.comm, Functor.map_comp, Category.assoc]

/-- The square of underlying morphisms of schemes of an affine chart of `g`. -/
theorem representedAffineChartPiece_toScheme_comm :
    (BigFppfOver.toScheme B S hS).map c.α ≫ (BigFppfOver.toScheme B S hS).map g =
      (BigFppfOver.toScheme B S hS).map (specFppfOverMap B S hS c.hR c.gR c.hA c.gA c.w) ≫
        (BigFppfOver.toScheme B S hS).map c.κ := by
  rw [← Functor.map_comp, c.comm, Functor.map_comp]

/-- **The relative Tor bound at the points of an affine chart, read on a tilde model.**  For
`E₀ ∈ D_QCoh(𝒪_T)` and a complex `M` of `A`-modules with `Lα^*E₀ ≅ M~`, the stalk of `E₀` at
`α(q)` has Tor amplitude in `[a, b]` over `𝒪_{T', g(α(q))}` exactly when `M_q` has over
`R_{q ∩ R}`. -/
theorem relStalkTorAmp_representedAffineChartPiece_iff
    (E₀ : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)))
    (M : CochainComplex (ModuleCat.{u} c.A) ℤ)
    (eM : (derivedPullback ((BigFppfOver.toScheme B S hS).map c.α).toLRSHom.toShHom).obj E₀ ≅
      DerivedCategory.Q.obj (Stacks.AffineTilde.tildeComplex M))
    (q : PrimeSpectrum c.A) (a b : ℤ) :
    RelStalkTorAmp ((BigFppfOver.toScheme B S hS).map g) E₀
        ((BigFppfOver.toScheme B S hS).map c.α q) a b ↔
      HasTorAmplitudeAt c.R M q.asIdeal a b :=
  (relStalkTorAmp_openImmersionSquare_iff ((BigFppfOver.toScheme B S hS).map g)
    ((BigFppfOver.toScheme B S hS).map c.α)
    ((BigFppfOver.toScheme B S hS).map (specFppfOverMap B S hS c.hR c.gR c.hA c.gA c.w))
    ((BigFppfOver.toScheme B S hS).map c.κ) (representedAffineChartPiece_toScheme_comm c) E₀ _
    (derivedPullbackObjIsoRestrictFunctorOfIsOpenImmersion _ E₀).symm q a b).symm.trans
    (relStalkTorAmp_specMap_iff c.R c.A M _ eM q a b)

/-- The geometric-stalk Tor bound of the pullback to an affine chart, over the chart of the base,
is the relative stalk bound of `E₀` at the corresponding point of the chart. -/
private theorem geometricStalkTorAmplitude_specFppfOverMap_iff_relStalkTorAmp
    (E₀ : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)))
    (hE₀ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)) i).obj
        E₀).IsQuasicoherent)
    (ū : GeometricPoint B S hS (yoneda.obj (specFppfOver B S hS c.hA c.gA))) (a₀ b₀ : ℤ) :
    GeometricStalkTorAmplitude B S hS
        (representedSpaceMap B S hS (specFppfOverMap B S hS c.hR c.gR c.hA c.gA c.w))
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS c.α)).obj
          ((zariskiEtaleDerived B S hS T).obj E₀)) ū a₀ b₀ ↔
      RelStalkTorAmp ((BigFppfOver.toScheme B S hS).map g) E₀
        ((BigFppfOver.toScheme B S hS).map c.α (identityChartPrime B S hS c.hA c.gA ū)) a₀ b₀ := by
  let j := (BigFppfOver.toScheme B S hS).map c.α
  obtain ⟨M, ⟨eM⟩, ⟨eP⟩⟩ := exists_tildeModel_specFppfOver B S hS c.hA c.gA
    ((derivedPullback j.toLRSHom.toShHom).obj E₀)
    (Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel j E₀ hE₀)
  exact (geometricStalkTorAmplitude_specFppfOverMap_iff B S hS c.hR c.gR c.hA c.gA c.w _ M
    ((representedDerivedPullbackComparisonIso c.α).app E₀ ≪≫ eP) ū a₀ b₀).trans
    (relStalkTorAmp_representedAffineChartPiece_iff c E₀ M eM _ a₀ b₀).symm

/-- **From the Tor clause along `f = h_g ≫ b` to a uniform relative stalk bound on an affine
chart** (the direction (1) ⇒ (2) of Stacks 0DKQ, Tor clause, on one chart).  If `ε^*E₀`, read
over `f⁻¹𝒪_Y`, locally has finite Tor dimension, with `b` étale and `E₀ ∈ D_QCoh(𝒪_T)`, then one
interval bounds the Tor amplitude of the stalks of `E₀` over the local rings of `T'` at all the
points of the chart `α` of `c`.  The chart is quasi-compact (Stacks 0DJJ (1)), the bound moves to
the geometric stalks over `h_{Spec R}` across the étale square of `c` (Stacks 05V5, 04NG), and
there it is the Tor amplitude of the localisations of a tilde model of `Lα^*E₀` (Stacks 04KF,
05VL, 06Z0), which is the relative stalk bound of `E₀` at the points of the chart. -/
theorem exists_relStalkTorAmp_representedAffineChartPiece (b : yoneda.obj T' ⟶ Y.1)
    (hb : IsEtale B S hS b)
    (E₀ : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)))
    (hE₀ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)) i).obj
        E₀).IsQuasicoherent)
    (hE : HasLocallyFiniteTorDimensionAlong
      (ObjectProperty.homMk (yoneda.map g ≫ b) :
        (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y)
      ((zariskiEtaleDerived B S hS T).obj E₀)) :
    ∃ a₀ b₀ : ℤ, ∀ q : PrimeSpectrum c.A,
      RelStalkTorAmp ((BigFppfOver.toScheme B S hS).map g) E₀
        ((BigFppfOver.toScheme B S hS).map c.α q) a₀ b₀ := by
  let a := representedSpaceMap B S hS c.α
  have ha : IsEtale B S hS a.hom := isEtale_yoneda_map_of_isOpenImmersion c.α
  have hψ : IsEtale B S hS (representedSpaceMap B S hS c.κ ≫ ObjectProperty.homMk b).hom :=
    isEtale_comp B S hS (isEtale_yoneda_map_of_isOpenImmersion c.κ) hb
  obtain ⟨a₀, b₀, hbound⟩ := exists_geometricStalkTorAmplitude_of_hasLocallyFiniteTorDimensionAlong
    _ _ hE (specFppfOver B S hS c.hA c.gA)
    (inferInstanceAs (IsAffine (Spec (CommRingCat.of c.A)))) a.hom ha
  refine ⟨a₀, b₀, fun q => ?_⟩
  obtain ⟨ū, hū⟩ := exists_chartPoint_yonedaIdentityNeighborhood_eq B S hS
    (specFppfOver B S hS c.hA c.gA) q
  let := etaleModulePullback_additive.{u, u} B S hS a ha
  let := preservesFiniteLimits_etaleModulePullback B S hS a ha
  let := preservesFiniteColimits_etaleModulePullback B S hS a ha
  have h₁ := geometricStalkTorAmplitude_etaleModulePullback_of_etaleSquare B S hS _
    (representedSpaceMap B S hS (specFppfOverMap B S hS c.hR c.gR c.hA c.gA c.w)) a ha
    (representedSpaceMap B S hS c.κ ≫ ObjectProperty.homMk b) hψ
    (representedAffineChartPiece_sq c b) _ ū a₀ b₀ (hbound ū)
  have h₂ := geometricStalkTorAmplitude_of_iso B S hS _
    ((smallEtaleDerivedModulePullbackIsoEtale B S hS a ha).app _).symm ū a₀ b₀ h₁
  have hq : (identityChartPrime B S hS c.hA c.gA ū) = q := hū
  have h₃ := (geometricStalkTorAmplitude_specFppfOverMap_iff_relStalkTorAmp c E₀ hE₀ ū a₀ b₀).1 h₂
  rwa [hq] at h₃

/-- **From a uniform relative stalk bound on an affine chart to the geometric-stalk bound over
`h_{Spec R}`.**  If one interval bounds the Tor amplitude of the stalks of `E₀ ∈ D_QCoh(𝒪_T)` over
the local rings of `T'` at the points of the chart `α` of `c`, then it bounds the Tor amplitude
of the geometric stalks of `Lα^*ε^*E₀` over `h_{Spec A → Spec R}⁻¹𝒪` at every geometric point of
the chart. -/
theorem geometricStalkTorAmplitude_specFppfOverMap_representedAffineChartPiece
    (E₀ : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)))
    (hE₀ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)) i).obj
        E₀).IsQuasicoherent)
    (a₀ b₀ : ℤ) (h : ∀ q : PrimeSpectrum c.A,
      RelStalkTorAmp ((BigFppfOver.toScheme B S hS).map g) E₀
        ((BigFppfOver.toScheme B S hS).map c.α q) a₀ b₀)
    (ū : GeometricPoint B S hS (yoneda.obj (specFppfOver B S hS c.hA c.gA))) :
    GeometricStalkTorAmplitude B S hS
      (representedSpaceMap B S hS (specFppfOverMap B S hS c.hR c.gR c.hA c.gA c.w))
      ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS c.α)).obj
        ((zariskiEtaleDerived B S hS T).obj E₀)) ū a₀ b₀ := by
  exact (geometricStalkTorAmplitude_specFppfOverMap_iff_relStalkTorAmp c E₀ hE₀ ū a₀ b₀).2
    (h _)

/-- A geometric-stalk bound along a morphism is one along any morphism equal to it. -/
theorem geometricStalkTorAmplitude_of_eq {X Y' : AlgebraicSpaces B S hS} {f₁ f₂ : X ⟶ Y'}
    (hf : f₁ = f₂) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (x : GeometricPoint B S hS X.1) (a b : ℤ)
    (H : GeometricStalkTorAmplitude B S hS f₂ E x a b) :
    GeometricStalkTorAmplitude B S hS f₁ E x a b := by
  subst hf
  exact H

/-- **From a uniform relative stalk bound on an affine chart to the geometric-stalk bound of the
pullback to the chart** (the direction (2) ⇒ (1) of Stacks 0DKQ, Tor clause, on one chart).  If
one interval bounds the Tor amplitude of the stalks of `E₀ ∈ D_QCoh(𝒪_T)` over the local rings
of `T'` at the points of the chart `α` of `c`, then it bounds the Tor amplitude of the geometric
stalks of `Lα^*ε^*E₀` over `(α ≫ f)⁻¹𝒪_Y` at every geometric point of the chart, for
`f = h_g ≫ b` with `b` étale: the base change along the étale `h_κ ≫ b` is invisible at the
geometric stalks (Stacks 05V5, 04NG). -/
theorem geometricStalkTorAmplitude_representedAffineChartPiece (b : yoneda.obj T' ⟶ Y.1)
    (hb : IsEtale B S hS b)
    (E₀ : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)))
    (hE₀ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)) i).obj
        E₀).IsQuasicoherent)
    (a₀ b₀ : ℤ) (h : ∀ q : PrimeSpectrum c.A,
      RelStalkTorAmp ((BigFppfOver.toScheme B S hS).map g) E₀
        ((BigFppfOver.toScheme B S hS).map c.α q) a₀ b₀)
    (ū : GeometricPoint B S hS (yoneda.obj (specFppfOver B S hS c.hA c.gA))) :
    GeometricStalkTorAmplitude B S hS
      (representedSpaceMap B S hS c.α ≫
        (ObjectProperty.homMk (yoneda.map g ≫ b) :
          (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y))
      ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS c.α)).obj
        ((zariskiEtaleDerived B S hS T).obj E₀)) ū a₀ b₀ := by
  have hψ : IsEtale B S hS (representedSpaceMap B S hS c.κ ≫ ObjectProperty.homMk b).hom :=
    isEtale_comp B S hS (isEtale_yoneda_map_of_isOpenImmersion c.κ) hb
  refine geometricStalkTorAmplitude_of_eq (representedAffineChartPiece_sq c b) _ ū a₀ b₀ ?_
  exact (geometricStalkTorAmplitude_comp_etale_iff B S hS
    (representedSpaceMap B S hS (specFppfOverMap B S hS c.hR c.gR c.hA c.gA c.w)) _ hψ _ ū
    a₀ b₀).2 (geometricStalkTorAmplitude_specFppfOverMap_representedAffineChartPiece c E₀ hE₀
      a₀ b₀ h ū)

end ChartTor

end AlgebraicGeometry.Space

end
