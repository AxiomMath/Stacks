module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleRankOneFreeLocusDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwistDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSeparator
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# The twist `𝒪_P(1)` of the projective bundle of an algebraic space

Let `X` be an algebraic space with its étale presentation `X = U/R`, and `ℰ` a finite locally
free `𝒪_X`-module, with projective bundle `π : P = 𝐏(ℰ) ⟶ X` presented as `P = P_U/P_R` by its
chart bundles.  This file constructs the quasi-coherent `𝒪_P`-module `𝒪_P(1)` together with its
tautological surjection `π^*ℰ ⟶ 𝒪_P(1)`, whose restriction to `P_U = 𝐏(ℰ|_U)` is the
tautological quotient `π_U^*ℰ|_U ⟶ 𝒪_{P_U}(1)`.

The construction is descent of a quotient (Stacks 03M3).  The module `φ^*π^*ℰ` on `P_U`, with
its canonical transition morphism, is a quasi-coherent module on the groupoid `(P_U, P_R)`.  The
tautological quotient `q : φ^*π^*ℰ ⟶ 𝒪_{P_U}(1)` is compatible with the two pullbacks to `P_R`
(`AlgebraicGeometry.Space.projectiveBundleChartQuotient_descends`, from Stacks 01O3), so there is
`β : t^*𝒪_{P_U}(1) ⟶ s^*𝒪_{P_U}(1)` with `t^*q ≫ β = α ≫ s^*q`.  Since `q` is an epimorphism
and inverse images preserve epimorphisms, the cocycle and unit conditions for `β` follow from those
of `α`, so `(𝒪_{P_U}(1), β)` is a quasi-coherent module on the groupoid; by Stacks 03M3 it comes
from a quasi-coherent `𝒪_P`-module, and `q` from a morphism `π^*ℰ ⟶ 𝒪_P(1)`, which is surjective
because its inverse image along the surjective étale atlas is.  It is invertible because its
inverse image to `P_U` reads on the scheme as the invertible module `𝒪_{P_U}(1)`, and
invertibility descends along the surjective étale atlas.

## Main definitions

* `AlgebraicGeometry.Space.QuasicoherentModule.ofEpi`: the quasi-coherent module on a groupoid
  carried by a quotient of one, with a compatible transition morphism.
* `AlgebraicGeometry.Space.projectiveBundleTwist`: the module `𝒪_P(1)`.
* `AlgebraicGeometry.Space.projectiveBundleTautological`: the surjection `π^*ℰ ⟶ 𝒪_P(1)`.
* `AlgebraicGeometry.Space.projectiveBundleTwistAtlasIso`: the restriction of `𝒪_P(1)` to the
  presenting chart bundle is `𝒪_{P_U}(1)`.

## Main results

* `AlgebraicGeometry.Space.epi_of_epi_representedZariski_map`: surjectivity of a morphism into a
  quasi-coherent module on a represented algebraic space is read on the scheme.
* `AlgebraicGeometry.Space.exists_epi_modulePullback_map_eq_of_comp_eq_spaceBaseDescent`:
  **descent of a quotient** along an étale covering with its kernel pair.
* `AlgebraicGeometry.Space.exists_projectiveBundleTwist`: the twist exists.
* `AlgebraicGeometry.Space.epi_projectiveBundleTautological`: the tautological map is surjective.
* `AlgebraicGeometry.Space.modulePullback_map_projectiveBundleTautological`: it restricts on the
  presenting chart bundle to the tautological quotient.
* `AlgebraicGeometry.Space.isInvertibleModule_projectiveBundleTwist`: **`𝒪_P(1)` is
  invertible.**

## Implementation notes

The compatibility conditions are packaged as the propositions
`AlgebraicGeometry.Space.DescentCompatible` and
`AlgebraicGeometry.Space.QuotientTransitionCompatible`, so that the groupoid of the presentation
and its fields, which are the represented morphisms of the presentation by definition, are
matched argument by argument rather than through the unfolding of the inverse-image functors.

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Surjectivity read on the scheme -/

section Epi

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A morphism of modules on a represented algebraic space whose reading on the scheme is an
epimorphism is an epimorphism**, for a quasi-coherent target: the reading is injective on the
morphisms out of a quasi-coherent module (Stacks 03DX (2)). -/
theorem epi_of_epi_representedZariski_map {T : BigFppfOver B S hS}
    {M N : SheafOfModules.{u} (representedStructureRingSheaf B S hS T)}
    (hN : N.IsQuasicoherentOnSite) (f : M ⟶ N)
    (hf : Epi ((SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map f))) :
    Epi f where
  left_cancellation {Z} g h e := by
    refine (QuasiCoherentDescent.bijective_representedZariski_map B S hS N Z hN).1 ?_
    have e' := congrArg (fun k => (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map k)) e
    simp only [Functor.map_comp] at e'
    exact (cancel_epi _).1 e'

end Epi

/-! ### A transition morphism through an epimorphism from a module on the groupoid -/

section OfEpi

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {A : AlgebraicSpaces B S hS}
  {G : GroupoidInAlgebraicSpaces B S hS A}

/-- **A quotient of a quasi-coherent module on a groupoid, with a compatible transition, is a
quasi-coherent module on the groupoid.**  For `Z` a quasi-coherent module on `(U, R, s, t, c)`,
an epimorphism `q : Z ⟶ L` onto a quasi-coherent `𝒪_U`-module and a morphism `β : t^*L ⟶ s^*L`
with `t^*q ≫ β = α_Z ≫ s^*q`, the cocycle and unit conditions for `β` follow from those of
`α_Z`: inverse images preserve epimorphisms, being left adjoints. -/
def QuasicoherentModule.ofEpi (Z : QuasicoherentModule B S hS G)
    (L : QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property)
    (q : Z.F.obj ⟶ L.obj) [hq : Epi q]
    (β : (modulePullback B S hS G.target).obj L.obj ⟶ (modulePullback B S hS G.source).obj L.obj)
    (hβ : (modulePullback B S hS G.target).map q ≫ β =
      Z.alpha ≫ (modulePullback B S hS G.source).map q) :
    QuasicoherentModule B S hS G where
  F := L
  alpha := β
  cocycle := by
    have := Functor.preservesEpimorphisms_of_adjunction
      (modulePullbackAdjunction B S hS (G.comp ≫ G.target))
    rw [← cancel_epi ((modulePullback B S hS (G.comp ≫ G.target)).map q),
      groupoidPullbackTransition_naturality B S hS G q hβ.symm, Z.cocycle,
      groupoidTransitionComposite_naturality B S hS G q hβ.symm]
  unit := by
    have := Functor.preservesEpimorphisms_of_adjunction
      (modulePullbackAdjunction B S hS (G.identityArrow ≫ G.target))
    rw [← cancel_epi ((modulePullback B S hS (G.identityArrow ≫ G.target)).map q),
      groupoidPullbackTransition_naturality B S hS G q hβ.symm, Z.unit,
      pullbackTransport_naturality]

/-- The underlying `𝒪_U`-module of `QuasicoherentModule.ofEpi Z L q β hβ` is `L`. -/
@[simp]
theorem QuasicoherentModule.ofEpi_F (Z : QuasicoherentModule B S hS G)
    (L : QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property)
    (q : Z.F.obj ⟶ L.obj) [hq : Epi q]
    (β : (modulePullback B S hS G.target).obj L.obj ⟶ (modulePullback B S hS G.source).obj L.obj)
    (hβ : (modulePullback B S hS G.target).map q ≫ β =
      Z.alpha ≫ (modulePullback B S hS G.source).map q) :
    (QuasicoherentModule.ofEpi Z L q β hβ).F = L :=
  rfl

/-- The transition morphism of `QuasicoherentModule.ofEpi Z L q β hβ` is `β`. -/
@[simp]
theorem QuasicoherentModule.ofEpi_alpha (Z : QuasicoherentModule B S hS G)
    (L : QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property)
    (q : Z.F.obj ⟶ L.obj) [hq : Epi q]
    (β : (modulePullback B S hS G.target).obj L.obj ⟶ (modulePullback B S hS G.source).obj L.obj)
    (hβ : (modulePullback B S hS G.target).map q ≫ β =
      Z.alpha ≫ (modulePullback B S hS G.source).map q) :
    (QuasicoherentModule.ofEpi Z L q β hβ).alpha = β :=
  rfl

/-- The epimorphism `q`, as a morphism of quasi-coherent modules on the groupoid. -/
def QuasicoherentModule.toOfEpi (Z : QuasicoherentModule B S hS G)
    (L : QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property)
    (q : Z.F.obj ⟶ L.obj) [hq : Epi q]
    (β : (modulePullback B S hS G.target).obj L.obj ⟶ (modulePullback B S hS G.source).obj L.obj)
    (hβ : (modulePullback B S hS G.target).map q ≫ β =
      Z.alpha ≫ (modulePullback B S hS G.source).map q) :
    Z ⟶ QuasicoherentModule.ofEpi Z L q β hβ where
  hom := q
  comm := hβ.symm

end OfEpi

/-! ### Descent of a quotient -/

section DescendQuotient

attribute [local instance 10000] smallEtaleModulesAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {A : AlgebraicSpaces B S hS}
  (G : GroupoidInAlgebraicSpaces B S hS A) {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X)
  (hφet : IsEtale B S hS φ.hom) (hφ : G.target ≫ φ = G.source ≫ φ)
  (hcov : IsEtaleCovering B S hS (fun _ : Unit => G.objects.1) (fun _ => φ.hom))
  (hrep : yoneda.relativelyRepresentable φ.hom)
  (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom)

omit hφ in
/-- A morphism `q : φ^*M ⟶ L` out of the inverse image of an `𝒪_X`-module to the space of
objects of a groupoid is **compatible with the canonical transition morphism** of Stacks 03M3:
there is `β : t^*L ⟶ s^*L` with `t^*q ≫ β = α ≫ s^*q`. -/
def QuotientTransitionCompatible (hφ : G.target ≫ φ = G.source ≫ φ)
    (M : Modules.{u, u} B S hS X.1 X.2)
    {L : Modules.{u, u} B S hS G.objects.1 G.objects.2} (q : (modulePullback B S hS φ).obj M ⟶ L) :
    Prop :=
  ∃ β : (modulePullback B S hS G.target).obj L ⟶ (modulePullback B S hS G.source).obj L,
    (modulePullback B S hS G.target).map q ≫ β =
      spaceBaseDescent B S hS G φ hφ M ≫ (modulePullback B S hS G.source).map q

include hφet hcov hrep hpb in
/-- **Descent of a quotient along an étale covering with its kernel pair (Stacks 03M3).**  Let
`φ : U ⟶ X` be as in Stacks 03M3, `M` a quasi-coherent `𝒪_X`-module and `q : φ^*M ⟶ L` an
epimorphism onto a quasi-coherent `𝒪_U`-module whose two pullbacks to `R` are compatible with the
canonical transition morphism of `φ^*M` through some `β : t^*L ⟶ s^*L`.  Then `q` is the inverse
image of an epimorphism `χ : M ⟶ F` of quasi-coherent `𝒪_X`-modules, up to an isomorphism
`φ^*F ≅ L`. -/
theorem exists_epi_modulePullback_map_eq_of_comp_eq_spaceBaseDescent
    (M : QuasicoherentSheaves.{u, u} B S hS X.obj X.property)
    (L : QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property)
    (q : (modulePullback B S hS φ).obj M.obj ⟶ L.obj) [Epi q]
    (h : QuotientTransitionCompatible G φ hφ M.obj q) :
    ∃ (F : QuasicoherentSheaves.{u, u} B S hS X.obj X.property) (χ : M ⟶ F)
      (e : (modulePullback B S hS φ).obj F.obj ≅ L.obj),
      Epi χ.hom ∧ (modulePullback B S hS φ).map χ.hom ≫ e.hom = q := by
  obtain ⟨β, hβ⟩ := h
  let Z := QuasicoherentModule.ofEpi
    (quasicoherentModuleOfSpaceBase B S hS G φ hφ M.obj M.property) L q (hq := ‹Epi q›) β hβ
  obtain ⟨F, ⟨i⟩⟩ := exists_spaceBaseObj_iso B S hS G φ hφet hφ hcov hrep hpb Z
  have := full_quasicoherentFromSpaceBase_of_isPullback B S hS G φ hφet hφ hrep hpb hcov
  obtain ⟨χ, hχ⟩ := (quasicoherentFromSpaceBase B S hS G φ hφ).map_surjective
    (QuasicoherentModule.toOfEpi (quasicoherentModuleOfSpaceBase B S hS G φ hφ M.obj M.property)
      L q (hq := ‹Epi q›) β hβ ≫ i.inv)
  let e : (modulePullback B S hS φ).obj F.obj ≅ L.obj := (QuasicoherentModule.forget G).mapIso i
  have hχ' : (modulePullback B S hS φ).map χ.hom = q ≫ e.inv :=
    congrArg QuasicoherentModule.Hom.hom hχ
  refine ⟨F, χ, e, ?_, ?_⟩
  · refine epi_of_forall_epi_modulePullback_map_of_isFlat B S hS (fun _ : Unit => φ)
      (fun _ => isFlat_of_isEtale B S hS hφet) hcov.jointly_surjective χ.hom fun _ => ?_
    rw [hχ']
    refine ⟨fun g h w => ?_⟩
    have w' : e.inv ≫ g = e.inv ≫ h :=
      Epi.left_cancellation (f := q) _ _ (by simpa only [Category.assoc] using w)
    simpa only [Iso.hom_inv_id_assoc] using congrArg (e.hom ≫ ·) w'
  · rw [hχ', Category.assoc, Iso.inv_hom_id, Category.comp_id]

end DescendQuotient

/-! ### The canonical transition morphism through a factorization of the atlas -/

section Bridge

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism `q : φ^*M ⟶ L` is **compatible with the canonical comparison** along a pair
`a, b` with `a ≫ φ = b ≫ φ`: there is a morphism `β : a^*L ⟶ b^*L` with
`a^*q ≫ β = c_{a,b} ≫ b^*q`, for `c_{a,b} : a^*φ^*M ≅ b^*φ^*M` the canonical comparison of
Stacks 04W5. -/
def DescentCompatible {A A' X : AlgebraicSpaces B S hS} (a b : A' ⟶ A) (φ : A ⟶ X)
    (h : a ≫ φ = b ≫ φ) (M : Modules.{u, u} B S hS X.1 X.2) {L : Modules.{u, u} B S hS A.1 A.2}
    (q : (modulePullback B S hS φ).obj M ⟶ L) : Prop :=
  IsoCompatible a b (QuasiCoherentDescent.canonicalComparison a b φ φ h M) q

/-- **A quotient of a pulled-back module which descends along a pair of morphisms of the site is
compatible with the canonical comparison.** -/
theorem descentCompatible_of_quotientDescends {T' T : BigFppfOver B S hS} (g g' : T' ⟶ T)
    {P X : AlgebraicSpaces B S hS} (φ : representedAlgebraicSpace B S hS T ⟶ P) (π : P ⟶ X)
    (E : Modules.{u, u} B S hS X.1 X.2)
    (h : representedSpaceMap B S hS g ≫ φ = representedSpaceMap B S hS g' ≫ φ)
    {ψR : representedAlgebraicSpace B S hS T' ⟶ X}
    (wg : representedSpaceMap B S hS g ≫ (φ ≫ π) = ψR)
    (wg' : representedSpaceMap B S hS g' ≫ (φ ≫ π) = ψR)
    {L : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (q : (modulePullback B S hS φ).obj ((modulePullback B S hS π).obj E) ⟶ L)
    (hq : QuotientDescends E g g' wg wg' q
      (QuasiCoherentDescent.pullbackComparison B S hS φ π _ rfl E).symm) :
    DescentCompatible (representedSpaceMap B S hS g) (representedSpaceMap B S hS g') φ h
      ((modulePullback B S hS π).obj E) q := by
  unfold QuotientDescends at hq
  unfold DescentCompatible
  rwa [canonicalComparison_modulePullback_eq _ _ _ _ _ rfl wg wg' E]

variable {Fp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hFp : IsAlgebraicSpace B S hS Fp}
  (Pp : Presentation B S hS Fp hFp) {X : AlgebraicSpaces B S hS}
  (π : (⟨Fp, hFp⟩ : AlgebraicSpaces B S hS) ⟶ X) (E : Modules.{u, u} B S hS X.1 X.2)

/-- **A morphism out of the inverse image of a module along the atlas of a presentation which is
compatible with the canonical comparison of the two legs is compatible with the canonical
transition morphism of Stacks 03M3.** -/
theorem exists_comp_eq_spaceBaseDescent_of_descentCompatible
    {L : Modules.{u, u} B S hS (presentationGroupoid Pp).objects.1
      (presentationGroupoid Pp).objects.2}
    (q : (modulePullback B S hS (presentationAtlas Pp)).obj ((modulePullback B S hS π).obj E) ⟶ L)
    (h : DescentCompatible (presentationGroupoid Pp).target (presentationGroupoid Pp).source
      (presentationAtlas Pp) (presentationAtlas_comm Pp) ((modulePullback B S hS π).obj E) q) :
    QuotientTransitionCompatible (presentationGroupoid Pp) (presentationAtlas Pp)
      (presentationAtlas_comm Pp) ((modulePullback B S hS π).obj E) q := by
  unfold DescentCompatible IsoCompatible at h
  unfold QuotientTransitionCompatible
  rwa [spaceBaseDescent_eq_unflatten, ← canonicalComparison_hom_eq_unflatten]

end Bridge

/-! ### The twist of the projective bundle -/

section Twist

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

omit hE in
/-- A composite of an epimorphism with isomorphisms on either side is an epimorphism. -/
private theorem epi_iso_hom_comp_iso_inv_comp {C : Type*} [Category C] {a b c d e : C}
    (e₁ : a ≅ b) (e₂ : c ≅ b) (f : c ⟶ d) (hf : Epi f) (e₃ : e ≅ d) :
    Epi (e₁.hom ≫ e₂.inv ≫ f ≫ e₃.inv) := by
  infer_instance

/-- The tautological quotient of the presenting chart bundle is an epimorphism: its reading on
the scheme `P_U` is the tautological quotient of `𝐏(ℰ|_U)` up to isomorphisms. -/
instance epi_projectiveBundleChartQuotient : Epi (projectiveBundleChartQuotient E hfree) :=
  epi_of_epi_representedZariski_map (isQuasicoherentOnSite_projectiveBundleChartTwist E hfree) _
    (by
      rw [representedZariski_map_projectiveBundleChartQuotient]
      unfold projectiveBundleChartQuotientReading quotientReadingOf
      exact epi_iso_hom_comp_iso_inv_comp _ _ _
        (Stacks.RelativeProj.epi_tautologicalDatumUniv (chartBundleModule E (bundleBaseChart X)))
        _)

/-- The tautological quotient of the presenting chart bundle is compatible with the canonical
comparison of the two pullbacks of `π^*ℰ` to the relation chart bundle. -/
theorem descentCompatible_projectiveBundleChartQuotient :
    DescentCompatible (projectiveBundleGroupoid E hfree).target
      (projectiveBundleGroupoid E hfree).source (projectiveBundleAtlas E hfree)
      (presentationAtlas_comm _) ((modulePullback B S hS (projectiveBundleProj E hfree)).obj E)
      (projectiveBundleChartQuotient E hfree) :=
  descentCompatible_of_quotientDescends
    ((projectiveBundleChartFamily E hfree).siteMap
      (presentationRelationTargetHom (projectiveBundlePresentation X)))
    ((projectiveBundleChartFamily E hfree).siteMap
      (presentationRelationSourceHom (projectiveBundlePresentation X)))
    (projectiveBundleAtlas E hfree) (projectiveBundleProj E hfree) E (presentationAtlas_comm _)
    (ψR := representedSpaceMap B S hS
      ((projectiveBundleChartFamily E hfree).siteToChart (bundleRelationChart X)) ≫
        chartToSpace B S hS X (bundleRelationChart X))
    (representedSpaceMap_bundleRelationTarget_comp E hfree)
    (representedSpaceMap_bundleRelationSource_comp E hfree)
    (projectiveBundleChartQuotient E hfree) (projectiveBundleChartQuotient_descends E hfree)

/-- The inverse image `π^*ℰ` of `ℰ` to the projective bundle, as a quasi-coherent module. -/
abbrev projectiveBundlePullback :
    QuasicoherentSheaves.{u, u} B S hS (projectiveBundle E hfree).obj
      (projectiveBundle E hfree).property :=
  ⟨(modulePullback B S hS (projectiveBundleProj E hfree)).obj E,
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ E hE⟩

/-- **The twist `𝒪_P(1)` of the projective bundle exists**: there is a quasi-coherent
`𝒪_P`-module with an epimorphism `π^*ℰ ⟶ 𝒪_P(1)` whose inverse image to the presenting chart
bundle `P_U = 𝐏(ℰ|_U)` is the tautological quotient `π_U^*ℰ|_U ⟶ 𝒪_{P_U}(1)`. -/
theorem exists_projectiveBundleTwist :
    ∃ (F : QuasicoherentSheaves.{u, u} B S hS (projectiveBundle E hfree).obj
        (projectiveBundle E hfree).property) (χ : projectiveBundlePullback E hfree ⟶ F)
      (e : (modulePullback B S hS (projectiveBundleAtlas E hfree)).obj F.obj ≅
        projectiveBundleChartTwist E hfree),
      Epi χ.hom ∧ (modulePullback B S hS (projectiveBundleAtlas E hfree)).map χ.hom ≫ e.hom =
        projectiveBundleChartQuotient E hfree :=
  exists_epi_modulePullback_map_eq_of_comp_eq_spaceBaseDescent
    (projectiveBundleGroupoid E hfree) (projectiveBundleAtlas E hfree)
    (presentationAtlas_isEtale _) (presentationAtlas_comm _) (presentationAtlas_isEtaleCovering _)
    (presentationAtlas_relativelyRepresentable _) (presentationGroupoid_isPullback _)
    (projectiveBundlePullback E hfree)
    ⟨projectiveBundleChartTwist E hfree, isQuasicoherentOnSite_projectiveBundleChartTwist E hfree⟩
    (projectiveBundleChartQuotient E hfree)
    (exists_comp_eq_spaceBaseDescent_of_descentCompatible
      (projectiveBundleChartPresentation E hfree) (projectiveBundleProj E hfree) E
      (projectiveBundleChartQuotient E hfree)
      (descentCompatible_projectiveBundleChartQuotient E hfree))

/-- **The twist `𝒪_P(1)` of the projective bundle `π : P = 𝐏(ℰ) ⟶ X`**: the quasi-coherent
`𝒪_P`-module descended from the twists `𝒪_{P_U}(1)` of the chart bundles. -/
def projectiveBundleTwist :
    QuasicoherentSheaves.{u, u} B S hS (projectiveBundle E hfree).obj
      (projectiveBundle E hfree).property :=
  (exists_projectiveBundleTwist E hfree).choose

/-- **The tautological surjection `π^*ℰ ⟶ 𝒪_P(1)`.** -/
def projectiveBundleTautological :
    projectiveBundlePullback E hfree ⟶ projectiveBundleTwist E hfree :=
  (exists_projectiveBundleTwist E hfree).choose_spec.choose

/-- **The restriction of `𝒪_P(1)` to the presenting chart bundle is `𝒪_{P_U}(1)`**: the inverse
image of `𝒪_P(1)` along the atlas `P_U ⟶ P` is the twist of `P_U = 𝐏(ℰ|_U)`. -/
def projectiveBundleTwistAtlasIso :
    (modulePullback B S hS (projectiveBundleAtlas E hfree)).obj
        (projectiveBundleTwist E hfree).obj ≅
      projectiveBundleChartTwist E hfree :=
  (exists_projectiveBundleTwist E hfree).choose_spec.choose_spec.choose

/-- **The tautological map `π^*ℰ ⟶ 𝒪_P(1)` is surjective.** -/
instance epi_projectiveBundleTautological : Epi (projectiveBundleTautological E hfree).hom :=
  (exists_projectiveBundleTwist E hfree).choose_spec.choose_spec.choose_spec.1

/-- **The tautological map restricts on the presenting chart bundle to the tautological quotient**
`π_U^*ℰ|_U ⟶ 𝒪_{P_U}(1)`, through `AlgebraicGeometry.Space.projectiveBundleTwistAtlasIso`. -/
theorem modulePullback_map_projectiveBundleTautological :
    (modulePullback B S hS (projectiveBundleAtlas E hfree)).map
        (projectiveBundleTautological E hfree).hom ≫ (projectiveBundleTwistAtlasIso E hfree).hom =
      projectiveBundleChartQuotient E hfree :=
  (exists_projectiveBundleTwist E hfree).choose_spec.choose_spec.choose_spec.2

/-- **The reading of `𝒪_P(1)` on the scheme `P_U` is the twist `𝒪_{P_U}(1)` of the chart bundle
`𝐏(ℰ|_U)`.** -/
def projectiveBundleTwistChartReadingIso :
    representedZariskiModule B S hS (projectiveBundleChartPresentation E hfree).U
        ((modulePullback B S hS (projectiveBundleAtlas E hfree)).obj
          (projectiveBundleTwist E hfree).obj) ≅
      chartBundleTwist E (bundleBaseChart X) :=
  (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
      (projectiveBundleChartPresentation E hfree).U.left.property).mapIso
    ((representedSmallEtaleModuleEquivalence B S hS
      (projectiveBundleChartPresentation E hfree).U).inverse.mapIso
      (projectiveBundleTwistAtlasIso E hfree)) ≪≫ projectiveBundleChartTwistReadingIso E hfree

/-- The twist `𝒪(1)` of a chart bundle `𝐏(ℰ|_V)` is invertible (Stacks 01OB). -/
instance isInvertibleModule_chartBundleTwist (V : SmallEtale B S hS X.1) :
    Stacks.Ample.IsInvertibleModule (chartBundle E V) (chartBundleTwist E V) :=
  Stacks.RelativeProj.isInvertible_tautologicalDatumTwist (chartBundleModule E V)

/-- The atlas `P_U ⟶ P` of the projective bundle is surjective on points. -/
theorem surjective_pointsMap_projectiveBundleAtlas :
    Function.Surjective (pointsMap B S hS (projectiveBundleGroupoid E hfree).objects.1
      (projectiveBundleAtlas E hfree).hom) := by
  intro x
  have hx := (presentationAtlas_isEtaleCovering
    (projectiveBundleChartPresentation E hfree)).jointly_surjective ▸ Set.mem_univ x
  obtain ⟨_, y, hy⟩ := Set.mem_iUnion.1 hx
  exact ⟨y, hy⟩

/-- **The twist `𝒪_P(1)` of the projective bundle is invertible.**  Its inverse image along the
surjective étale atlas `P_U ⟶ P` reads on the scheme `P_U = 𝐏(ℰ|_U)` as the twist
`𝒪_{P_U}(1)` (`AlgebraicGeometry.Space.projectiveBundleTwistChartReadingIso`), which is
invertible, so the inverse image is invertible
(`AlgebraicGeometry.Space.isInvertibleModule_of_idChartRestriction_iso`), and invertibility
descends along a surjective étale morphism
(`AlgebraicGeometry.Space.isInvertibleModule_of_isInvertibleModule_modulePullback`). -/
theorem isInvertibleModule_projectiveBundleTwist :
    IsInvertibleModule (projectiveBundle E hfree) (projectiveBundleTwist E hfree).obj :=
  isInvertibleModule_of_isInvertibleModule_modulePullback B S hS (projectiveBundleAtlas E hfree)
    (presentationAtlas_isEtale _) (surjective_pointsMap_projectiveBundleAtlas E hfree) _
    (isInvertibleModule_of_idChartRestriction_iso B S hS
      (projectiveBundleChartPresentation E hfree).U _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _
        (projectiveBundleTwist E hfree).property)
      (chartBundleTwist E (bundleBaseChart X)) (hL := isInvertibleModule_chartBundleTwist E _)
      (projectiveBundleTwistChartReadingIso E hfree))

end Twist

end AlgebraicGeometry.Space

end
