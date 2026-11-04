module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackNoetherianDescent
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalDirectImagePerfect
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalSubstackFlatClosed
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalTensorPowerProductsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingProperness

/-!
# Numerical conditions that are locally pulled back from a locally Noetherian scheme

Let `f : X ⟶ Y` be a separated morphism of finite presentation of algebraic spaces with perfect
objects `E_i` on `X`, the data of Situation 0DNC.  The numerical invariants
`χ_i : |T| → ℤ` of an object `(T, 𝓕)` of `Coh_{X/Y}` are compatible with pullback along the
morphisms of `Coh_{X/Y}` and locally constant.  When the index set is infinite this does not make
the locus `χ_i = P(i)` open; what the proof of Stacks 0DNE shows is that near every point of `T`
the family `(χ_i)` is pulled back, along a map continuous at that point, from a family of locally
constant functions on a locally Noetherian scheme, whose connected components are open.

This file isolates that property of a family of functions on the points of a scheme, records
how it is inherited, proves it when the base `Y` is locally Noetherian, and shows that it makes
`Coh^P_{X/Y}` an open and closed substack of `Coh_{X/Y}`.

## Main definitions

* `AlgebraicGeometry.IsLocallyNoetherianPullbackAt`: a family of functions on the points of a
  scheme is, near a point, pulled back from a family of locally constant functions on a locally
  Noetherian scheme, after an open base change hitting the point.

## Main results

* `AlgebraicGeometry.IsLocallyNoetherianPullbackAt.of_comp`: the property descends along a
  morphism of schemes that is open on points.
* `Space.NumericalSituation.isLocallyNoetherianPullbackAt_of_isLocallyNoetherian`: over a locally
  Noetherian base the numerical invariants have the property at every point.
* `Space.NumericalSituation.exists_affine_baseChange_numericalEuler` and
  `Space.NumericalSituation.isLocallyNoetherianPullbackAt_of_affine_baseChange`: for the data of
  Stacks 0DNE the numerical invariants of an object are, étale locally on its test scheme, those of
  an object of `Coh_{X_W/W}` for an affine scheme `W` étale over `Y`, so the property may be
  checked after base change to affine schemes.
* `Space.NumericalSituation.isOpenAndClosedCondition_of_isLocallyNoetherianPullbackAt`: if the
  numerical invariants have the property at every point of every test scheme, then `Coh^P_{X/Y}` is
  an open and closed substack of `Coh_{X/Y}`, however large the index set.

## References

* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
* [Stacks Project, Tag 0DND](https://stacks.math.columbia.edu/tag/0DND)
-/

@[expose] public noncomputable section

open CategoryTheory Topology

universe u v

namespace AlgebraicGeometry

/-- **A family of functions on the points of a scheme is locally pulled back from a locally
Noetherian scheme at a point `t`**: there is a morphism of schemes `p : T' ⟶ T`, open on points,
and a point `t'` over `t`, such that near `t'` the family `χ ∘ p` is the pullback, along a map
continuous at `t'`, of a family of locally constant functions on a locally Noetherian scheme. -/
def IsLocallyNoetherianPullbackAt {ι : Sort*} {β : Type*} {T : Scheme.{u}} (χ : ι → T → β)
    (t : T) : Prop :=
  ∃ (T' : Scheme.{u}) (p : T' ⟶ T) (t' : T'), p t' = t ∧ IsOpenMap p ∧ ∃ V ∈ 𝓝 t',
    ∃ (T₀ : Scheme.{u}) (_ : IsLocallyNoetherian T₀) (g : T' → T₀) (χ₀ : ι → T₀ → β),
      ContinuousAt g t' ∧ (∀ i, IsLocallyConstant (χ₀ i)) ∧
        ∀ i, ∀ y ∈ V, χ i (p y) = χ₀ i (g y)

namespace IsLocallyNoetherianPullbackAt

variable {ι : Sort*} {β : Type*}

/-- **The property descends along a morphism open on points**: if `χ ∘ q = χ₁` for a morphism
of schemes `q : T₁ ⟶ T` that is open on points, and `χ₁` is locally pulled back from a locally
Noetherian scheme at `t₁`, then so is `χ` at `q t₁`. -/
theorem of_comp {T T₁ : Scheme.{u}} {χ : ι → T → β} {χ₁ : ι → T₁ → β} (q : T₁ ⟶ T)
    (hq : IsOpenMap q) (hχ : ∀ i y, χ i (q y) = χ₁ i y) {t₁ : T₁}
    (h : IsLocallyNoetherianPullbackAt χ₁ t₁) : IsLocallyNoetherianPullbackAt χ (q t₁) := by
  obtain ⟨T', p, t', hpt, hp, V, hV, T₀, hT₀, g, χ₀, hg, hχ₀, hfac⟩ := h
  refine ⟨T', p ≫ q, t', by rw [Scheme.Hom.comp_apply, hpt], ?_, V, hV, T₀, hT₀, g, χ₀, hg,
    hχ₀, fun i y hy => ?_⟩
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp]
    exact hq.comp hp
  · rw [Scheme.Hom.comp_apply, hχ i, hfac i y hy]

/-- The property only depends on the family of functions. -/
theorem congr {T : Scheme.{u}} {χ χ' : ι → T → β} (hχ : ∀ i y, χ i y = χ' i y) {t : T}
    (h : IsLocallyNoetherianPullbackAt χ t) : IsLocallyNoetherianPullbackAt χ' t :=
  of_comp (𝟙 T) IsOpenMap.id (fun i y => (hχ i y).symm) h

/-- **A family that is, after an open base change hitting the point, the pullback of locally
constant functions on a locally Noetherian scheme along a morphism of schemes, has the
property.** -/
theorem of_hom {T T' T₀ : Scheme.{u}} [IsLocallyNoetherian T₀] {χ : ι → T → β} (p : T' ⟶ T)
    (hp : IsOpenMap p) (q : T' ⟶ T₀) (χ₀ : ι → T₀ → β) (hχ₀ : ∀ i, IsLocallyConstant (χ₀ i))
    (hfac : ∀ i y, χ i (p y) = χ₀ i (q y)) (t' : T') :
    IsLocallyNoetherianPullbackAt χ (p t') :=
  ⟨T', p, t', rfl, hp, Set.univ, Filter.univ_mem, T₀, inferInstance, q, χ₀,
    q.continuous.continuousAt, hχ₀, fun i y _ => hfac i y⟩

end IsLocallyNoetherianPullbackAt

namespace Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

/-- The base change of a separated morphism of the standing data is separated (Stacks 03KL). -/
theorem CoherentSituation.isSeparated_baseChange (hf : IsSeparated B S hS D.f.hom)
    {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ D.Y) : IsSeparated B S hS (D.baseChange g).f.hom :=
  isSeparated_baseChange_of_isPullback (IsPullback.of_hasPullback D.f.hom g.hom) hf

namespace NumericalSituation

open CoherentSituation

variable (N : NumericalSituation.{u, v, u} B S hS D)

/-- **Over a locally Noetherian base the numerical invariants are locally pulled back from a
locally Noetherian scheme**: near every point of its test scheme an object of `Coh_{X/Y}` is
pulled back from one over a locally Noetherian test scheme
(`AlgebraicGeometry.Space.CoherentSituation.exists_noetherianDescent_of_isLocallyNoetherian`),
and the invariants are compatible with pullback and locally constant. -/
theorem isLocallyNoetherianPullbackAt_of_isLocallyNoetherian
    (hY : IsLocallyNoetherian B S hS D.Y.1) (A : CoherentObject D) (t : A.testScheme) :
    IsLocallyNoetherianPullbackAt (schemePointsFunction N.numericalEuler A) t := by
  obtain ⟨A', A₀, p, q, t', hpt, hp, hA₀⟩ :=
    D.exists_noetherianDescent_of_isLocallyNoetherian hY A t
  rw [← hpt]
  exact IsLocallyNoetherianPullbackAt.of_hom p.baseScheme hp q.baseScheme
    (schemePointsFunction N.numericalEuler A₀)
    (fun i => (N.isLocallyConstant_numericalEuler A₀ i).comp_continuous
      (schemePointsHomeomorph B S hS A₀.T.left).symm.continuous)
    (fun i y => by
      rw [← schemePointsFunction_hom (N.numericalEuler_eq_of_hom) p i y,
        schemePointsFunction_hom (N.numericalEuler_eq_of_hom) q i y])
    t'

/-- **`Coh^P_{X/Y}` is an open and closed substack as soon as the numerical invariants are
everywhere locally pulled back from a locally Noetherian scheme**, however large the index set:
on every test scheme the locus `χ_i = P(i)` is then open and closed. -/
theorem isOpenAndClosedCondition_of_isLocallyNoetherianPullbackAt
    (h : ∀ (A : CoherentObject D) (t : A.testScheme),
      IsLocallyNoetherianPullbackAt (schemePointsFunction N.numericalEuler A) t) :
    IsOpenAndClosedCondition D N.HasNumericalInvariants := by
  convert isOpenAndClosedCondition_of_locally_factors (schemePointsFunction N.numericalEuler) N.P
    (schemePointsFunction_hom N.numericalEuler_eq_of_hom) h using 2 with A
  exact (forall_schemePointsFunction_eq_iff N.P A).symm

section EtaleLocalization

variable (hf : IsSeparated B S hS D.f.hom) {r : ℕ}
  (E : Fin r → @DerivedCategory (Modules.{u, u} B S hS D.X.1 D.X.2) _ _
    (HasDerivedCategory.standard _))
  (hE : ∀ j, letI := HasDerivedCategory.standard (Modules.{u, u} B S hS D.X.1 D.X.2)
    (smallEtaleRingedSite B S hS D.X.1 D.X.2).IsPerfect (E j))
  (P : (Fin r → ℤ) → ℤ)

/-- **The numerical invariants are étale locally on the base those of a base change to an
affine scheme.**  Let `A = (T, 𝓕)` be an object of `Coh_{X/Y}` and `t` a point of `T`.  There
are an affine scheme `W` of the site with a morphism `g : W ⟶ Y`, an object `A'` of
`Coh_{X_W/W}`, `X_W = X ×_Y W`, and a morphism of schemes `q` from the test scheme of `A'` to
`T`, open on points and with `t` in its image, such that the numerical invariants of `A'` for the
perfect objects `E_{j,W}` are those of `A` read along `q`.

The test scheme of `A'` is an affine étale neighbourhood `V` of `t` on which `T ⟶ Y` factors
through an affine étale chart `W` of `Y`, and its module is that of `A` restricted to `V` and
read on `X_W ×_W V ≅ X ×_Y V`. -/
theorem exists_affine_baseChange_numericalEuler (A : CoherentObject D) (t : A.testScheme) :
    ∃ (W : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
      (g : (schemeSpaceFunctor B S hS).obj W ⟶ D.Y) (A' : CoherentObject (D.baseChange g))
      (q : A'.testScheme ⟶ A.testScheme) (t' : A'.testScheme),
      q t' = t ∧ IsOpenMap q ∧ ∀ n y,
        schemePointsFunction (ofDerivedTensorPowerProducts (isSeparated_baseChange hf g)
          (baseChangeObjects D g E) (isPerfect_baseChangeObjects D g E hE) P).numericalEuler
            A' n y =
          schemePointsFunction (ofDerivedTensorPowerProducts hf E hE P).numericalEuler A n
            (q y) := by
  classical
  let G := BigFppfOver.toScheme B S hS
  obtain ⟨U, f, ι, W, j, e, hfS, hfE, hWaff, hιe, hjopen, hjf, -⟩ :=
    IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS D.Y.1 D.Y.2
  let x : D.Y.1.obj (Opposite.op A.T.left) := yonedaEquiv A.T.hom.hom
  obtain ⟨V, ev, i, m, -, hev, ht, hfac⟩ :=
    exists_affine_etale_nbhd_through_atlas f hfS hfE j hjopen
      (isOpenImmersion_cover_disjoint_of_iso_sigma e hιe).2.1 x t
  let gW : (schemeSpaceFunctor B S hS).obj (W i) ⟶ D.Y :=
    ObjectProperty.homMk (yoneda.map (j i) ≫ f)
  let T₀ : SchemesOver (D.baseChange gW).Y :=
    CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map m)
  have hw : (schemeSpaceFunctor B S hS).map ev ≫ A.T.hom =
      ((D.overBase gW).obj T₀).hom := by
    apply ObjectProperty.hom_ext
    show yoneda.map ev ≫ A.T.hom.hom = yoneda.map m ≫ (yoneda.map (j i) ≫ f)
    apply yonedaEquiv.injective
    exact ((yonedaEquiv_comp _ _).trans (congrArg _ (yonedaEquiv_yoneda_map ev))).trans
      ((yonedaEquiv_naturality _ _).symm.trans (hfac.symm.trans
        ((congrArg (fun y => f.app (Opposite.op V) (y ≫ j i))
          (yonedaEquiv_yoneda_map m).symm).trans
          (yonedaEquiv_comp (yoneda.map m) (yoneda.map (j i) ≫ f)).symm)))
  let h : (D.overBase gW).obj T₀ ⟶ A.T := CostructuredArrow.homMk ev hw
  let hst := modulePullbackStabilityOfFinitePresentation B S hS
  let hc := modulePushforwardCoherence B S hS
  let A₁ := pullbackObject' hst A h
  let L := D.baseChangeLift' hc hst gW A₁ T₀ rfl
  let φ : CoherentHom (D.baseChangeObject' hst gW L.obj) A :=
    L.hom.comp (pullbackHom' hst A h)
  let b := (pullbackHom' hst A h).base.left
  have hφ : φ.baseScheme = G.map L.hom.base.left ≫ G.map b := G.map_comp _ _
  have : IsIso (G.map L.hom.base.left) := by rw [L.hom_base_left]; infer_instance
  have : Etale (G.map b) := hev
  have hφopen : IsOpenMap φ.baseScheme := by
    rw [hφ, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact (G.map b).isOpenMap.comp (G.map L.hom.base.left).isOpenMap
  obtain ⟨v, hv⟩ : t ∈ Set.range (G.map b) := ht
  refine ⟨W i, hWaff i, gW, L.obj, φ.baseScheme, inv (G.map L.hom.base.left) v, ?_, hφopen,
    fun n y => ?_⟩
  · have key : (G.map L.hom.base.left ≫ G.map b) (inv (G.map L.hom.base.left) v) = t := by
      have hinv : G.map L.hom.base.left (inv (G.map L.hom.base.left) v) = v := by
        rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
        rfl
      rw [Scheme.Hom.comp_apply, hinv, hv]
    exact (congrArg (fun k : G.obj (D.baseChangeObject' hst gW L.obj).T.left ⟶ G.obj A.T.left =>
      k (inv (G.map L.hom.base.left) v)) hφ).trans key
  · exact (congrFun (numericalEuler_baseChange D gW hf (isSeparated_baseChange hf gW) E hE P
      L.obj n) _).trans (schemePointsFunction_hom
        ((ofDerivedTensorPowerProducts hf E hE P).numericalEuler_eq_of_hom) φ n y)

/-- **Étale localisation on the base of the local Noetherian model property.**  If for every
affine scheme `W` of the site with a morphism `g : W ⟶ Y` the numerical invariants of the objects
of `Coh_{X_W/W}` for the perfect objects `E_{j,W}` are everywhere locally pulled back from a
locally Noetherian scheme, then so are those of the objects of `Coh_{X/Y}`. -/
theorem isLocallyNoetherianPullbackAt_of_affine_baseChange
    (h : ∀ (W : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
      (g : (schemeSpaceFunctor B S hS).obj W ⟶ D.Y) (A' : CoherentObject (D.baseChange g))
      (t' : A'.testScheme),
      IsLocallyNoetherianPullbackAt (schemePointsFunction (ofDerivedTensorPowerProducts
        (isSeparated_baseChange hf g) (baseChangeObjects D g E)
        (isPerfect_baseChangeObjects D g E hE) P).numericalEuler A') t')
    (A : CoherentObject D) (t : A.testScheme) :
    IsLocallyNoetherianPullbackAt
      (schemePointsFunction (ofDerivedTensorPowerProducts hf E hE P).numericalEuler A) t := by
  obtain ⟨W, hW, g, A', q, t', hqt, hq, hχ⟩ :=
    exists_affine_baseChange_numericalEuler hf E hE P A t
  rw [← hqt]
  exact (h W hW g A' t').of_comp q hq fun i y => (hχ i y).symm

end EtaleLocalization

end NumericalSituation

end Space

end AlgebraicGeometry

end
