module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalDirectImagePerfect
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismsNumericalSubspace
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerFiniteProjectiveModel
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitPreservingNoetherianDescent
public import StacksFrontier.Topology.Connected.ClopenIntersectionLocallyConnected
public import StacksFrontier.Topology.Noetherian.LocallyConnected

/-!
# Relative morphisms with prescribed numerical invariants (Stacks 0DPQ)

Let `z : Z ⟶ Q` be flat, proper and of finite presentation and `x : X ⟶ Q` separated and of
finite presentation, morphisms of algebraic spaces over a scheme `S` of a big fppf site.  Let `I`
be a set, `E_i ∈ D(𝒪_{Z ×_Q X})` perfect for `i ∈ I` and `P : I → ℤ`: the standing data
`AlgebraicGeometry.Space.NumericalSituation` of Situation 0DNC on `Z ×_Q X ⟶ Q`.  Since
`Mor_Q(Z, X) ⊆ Hilb_{Z ×_Q X / Q}` is an open subspace through the graph transformation
(Stacks 0D1A, 0D1B), Stacks 0DPQ defines

`Mor^P_Q(Z, X) = Mor_Q(Z, X) ∩ Hilb^P_{Z ×_Q X / Q}`,

the relative morphisms over `T` whose graph `W ⊆ (Z ×_Q X)_T` has
`χ_i(t) = χ(K_i ⊗^𝐋 κ(t)) = P(i)` for all `i ∈ I` and all points `t` of `T`, where
`K_i = Rf_{T,*}(E_{i,T} ⊗^𝐋 𝒪_W)`, and asserts that `Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is a flat
closed immersion, which is an open and closed immersion if `I` is finite, or `Q` is locally
Noetherian, or `I = ℤ` and `E_i = L^{⊗ i}` for an invertible `𝒪_{Z ×_Q X}`-module `L`.

## Main definitions

* `AlgebraicGeometry.Space.numericalSituationRelativeHom`: the subfunctor `Mor^P_Q(Z, X)` of
  `Mor_Q(Z, X)`.
* `AlgebraicGeometry.Space.hilbertPolynomialSituationRelativeHom`: the subfunctor
  `Mor^{P, L}_Q(Z, X)`, the case `I = ℤ`, `E_n = L^{⊗ n}`.
* `AlgebraicGeometry.Space.graphNumericalInvariant`: the invariants of the graph of a relative
  morphism, read on the points of the test scheme.

## Main results

* `AlgebraicGeometry.Space.isCutOutByPoints_isClopen_of_isClopen`: a subfunctor cut out by
  prescribed values of functions compatible with restriction is cut out by open and closed sets
  as soon as every locus is open and closed.
* `AlgebraicGeometry.Space.isClopen_setOf_forall_eq_of_isLocallyNoetherian`: over a locally
  Noetherian base the locus on which locally constant invariants of relative morphisms, compatible
  with restriction, take prescribed values is open and closed.
* In the namespace `AlgebraicGeometry.Space`,
  `isFlat_and_isClosedImmersion_numericalSituationRelativeHom_ι`,
  `isOpenImmersion_and_isClosedImmersion_numericalSituationRelativeHom_ι`,
  `isOpenImmersion_and_isClosedImmersion_numericalSituationRelativeHom_ι_of_isLocallyNoetherian`
  and `isOpenImmersion_and_isClosedImmersion_hilbertPolynomialSituationRelativeHom_ι`:
  `Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is a flat closed immersion, and it is an open and closed
  immersion if `I` is finite, or `Q` is locally Noetherian, or for `Mor^{P, L}_Q(Z, X)`.

## Implementation notes

In the case `I = ℤ`, `E_n = L^{⊗ n}` the invariant is taken in the first form in which
Situation 0DNC writes it, `χ(X_t, E_{n,t} ⊗^𝐋 𝒪_{W_t}) = χ(X_t, 𝒪_{W_t} ⊗ L_t^{⊗ n})` for the
invertible `L_t^{⊗ n}`, which is `AlgebraicGeometry.Space.CoherentObject.twistedEuler`; the
subfunctor `Mor^{P, L}_Q(Z, X)` is the pull-back along the graph transformation of the subfunctor
of `Hilb_{Z ×_Q X / Q}` cut out by `AlgebraicGeometry.Space.CoherentObject.HasHilbertPolynomial`,
the condition defining `Coh^{P, L}_{Z ×_Q X / Q}` in Stacks 0DNF.

## References

* [Stacks Project, Tag 0DPQ](https://stacks.math.columbia.edu/tag/0DPQ)
* [Stacks Project, Tag 0DPG](https://stacks.math.columbia.edu/tag/0DPG)
* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 0DND](https://stacks.math.columbia.edu/tag/0DND)
* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 0DN4](https://stacks.math.columbia.edu/tag/0DN4)
* [Stacks Project, Tag 0A1P](https://stacks.math.columbia.edu/tag/0A1P)
* [Stacks Project, Tag 0A1Q](https://stacks.math.columbia.edu/tag/0A1Q)
* [Stacks Project, Tag 0D1B](https://stacks.math.columbia.edu/tag/0D1B)
* [Stacks Project, Tag 0D1C](https://stacks.math.columbia.edu/tag/0D1C)
* [Stacks Project, Tag 0D1Z](https://stacks.math.columbia.edu/tag/0D1Z)
* [Stacks Project, Tag 04MF](https://stacks.math.columbia.edu/tag/04MF)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Topology

namespace AlgebraicGeometry.Space

universe w v u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Suppose every section `x ∈ F(U)` carries functions `χ_x i : |U| → β`, compatible with
restriction, and that `x` lies in `G` exactly when `χ_x i t = P i` for all `i` and `t`. If for
every section the locus where all `χ_x i` take the prescribed values is open and closed, then `G`
is cut out by open and closed sets of points. -/
theorem isCutOutByPoints_isClopen_of_isClopen {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    {I : Type*} {β : Type*} (G : Subfunctor F) (P : I → β)
    (χ : ∀ (U : BigFppfOver B S hS), F.obj (op U) → I → (BigFppfOver.toScheme B S hS).obj U → β)
    (hbc : ∀ ⦃U W : BigFppfOver B S hS⦄ (h : W ⟶ U) (x : F.obj (op U)) (i : I)
      (t : (BigFppfOver.toScheme B S hS).obj W),
      χ W (F.map h.op x) i t = χ U x i ((BigFppfOver.toScheme B S hS).map h t))
    (hG : ∀ U x, x ∈ G.obj (op U) ↔ ∀ i t, χ U x i t = P i)
    (hclopen : ∀ U x, IsClopen {t | ∀ i, χ U x i t = P i}) :
    IsCutOutByPoints G fun _ Z => IsClopen Z := by
  intro U x
  refine ⟨{t | ∀ i, χ U x i t = P i}, hclopen U x, fun W h => ?_⟩
  rw [hG]
  constructor
  · rintro hx _ ⟨t, rfl⟩ i
    exact (hbc h x i t).symm.trans (hx i t)
  · intro hx i t
    exact (hbc h x i t).trans (hx ⟨t, rfl⟩ i)

section Relative

variable (B S hS) (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q) (x : X ⟶ Q)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)

/-- Over a locally Noetherian base, locally constant invariants of relative morphisms compatible
with restriction take prescribed values on an open and closed locus, whatever the index set. -/
theorem isClopen_setOf_forall_eq_of_isLocallyNoetherian
    (hfp : IsFinitePresentation B S hS z) (hxfp : IsFinitePresentation B S hS x)
    (hQN : IsLocallyNoetherian B S hS Q) {I : Type*} {β : Type*}
    (χ : ∀ (T : BigFppfOver B S hS), (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T) → I →
      (BigFppfOver.toScheme B S hS).obj T → β)
    (hlc : ∀ T s i, IsLocallyConstant (χ T s i))
    (hbc : ∀ ⦃T T' : BigFppfOver B S hS⦄ (g : T' ⟶ T)
      (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) (i : I)
      (t : (BigFppfOver.toScheme B S hS).obj T'),
      χ T' ((relativeHom B S hS Z X Q z x hZ hX hQ).map g.op s) i t =
        χ T s i ((BigFppfOver.toScheme B S hS).map g t))
    (P : I → β) (T : BigFppfOver B S hS)
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    IsClopen {t | ∀ i, χ T s i t = P i} := by
  refine isClopen_setOf_forall_eq_of_locally_factors (fun t => ?_) P
  obtain ⟨T', T₀, p, q, s₀, t', hpt, hpo, hN, hs⟩ :=
    exists_noetherianDescent_of_relativelyLimitPreserving
      (relativeHomProjection B S hS Z X Q z x hZ hX hQ) hQ hQN
      (relativelyLimitPreserving_relativeHomProjection z x hZ hX hQ hfp hxfp.1) T s t
  refine ⟨(BigFppfOver.toScheme B S hS).obj T', inferInstance,
    ⇑((BigFppfOver.toScheme B S hS).map p), t', hpt, hpo, Set.univ,
    Filter.univ_mem, (BigFppfOver.toScheme B S hS).obj T₀, inferInstance,
    TopologicalSpace.IsLocallyNoetherianSpace.locallyConnectedSpace _
      (@AlgebraicGeometry.isLocallyNoetherianSpace_of_isLocallyNoetherian _ hN),
    ⇑((BigFppfOver.toScheme B S hS).map q), fun i => χ T₀ s₀ i,
    ((BigFppfOver.toScheme B S hS).map q).continuous.continuousAt,
    fun i => hlc T₀ s₀ i, fun i y _ => ?_⟩
  rw [← hbc p s i y, ← hs, hbc q s₀ i y]

end Relative

section Numerical

variable (B S hS) {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}
    {hZ : IsAlgebraicSpace B S hS Z} {hX : IsAlgebraicSpace B S hS X}
    {hQ : IsAlgebraicSpace B S hS Q}
    (hsep : IsSeparated B S hS x) (hx_fp : IsFinitePresentation B S hS x)
    (hfp : IsFinitePresentation B S hS z) (hflat : IsFlat B S hS z) (hproper : IsProper B S hS z)
    (N : NumericalSituation.{u, v, u} B S hS
      (structureSheafQuotSituation (graphAmbientMap B S hS z x hZ hX hQ)
        (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hx_fp)).toCoherentSituation)

/-- The subfunctor `Mor^P_Q(Z, X) = Mor_Q(Z, X) ∩ Hilb^P_{Z ×_Q X / Q}`. For the standing data `N`
of Situation 0DNC on `Z ×_Q X ⟶ Q` (a set `I`, perfect objects `E_i` of `D(𝒪_{Z ×_Q X})` and
`P : I → ℤ`), the subfunctor of `Mor_Q(Z, X)` of the relative morphisms over `T` whose graph `W`, a
point of `Hilb_{Z ×_Q X / Q}` by Stacks 0D1A and 0D1B, lies in `Hilb^P_{Z ×_Q X / Q}` of Stacks
0DPG: `χ(K_i ⊗^𝐋 κ(t)) = P(i)` for `K_i = Rf_{T,*}(E_{i,T} ⊗^𝐋 𝒪_W)`, every `i ∈ I` and every point
`t` of `T`. -/
@[stacks 0DPQ "the definition `Mor^P_B(Y, X) = Mor_B(Y, X) ∩ Hilb^P_{Y ×_B X/B}`, for the \
numerical invariants `χ(K_i ⊗^𝐋 κ(t))` of Situation 0DNC on `Y ×_B X ⟶ B`"]
abbrev numericalSituationRelativeHom : Subfunctor (relativeHom B S hS Z X Q z x hZ hX hQ) :=
  prescribedRelativeHom hsep hx_fp hfp hflat hproper N
    (fun φ i t => N.numericalEuler_eq_of_hom φ i t)

/-- The invariants of the graph of a relative morphism, read on the points of the test
scheme: the function `χ_i` of Situation 0DNC on the object `(T, 𝒪_W)` of `Coh_{Z ×_Q X / Q}` of
the graph `W`, transported along the homeomorphism of Stacks 03BX. -/
def graphNumericalInvariant (T : BigFppfOver B S hS)
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) (i : N.I)
    (t : (BigFppfOver.toScheme B S hS).obj T) : ℤ :=
  CoherentSituation.schemePointsFunction N.numericalEuler
    (hilbertCohObject _ (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hx_fp)
      (graphFamilyOfSection B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper T s)) i t

/-- The invariants of the graph of a relative morphism are locally constant on the test scheme
(Stacks 0A1P, 0D1Z). -/
theorem isLocallyConstant_graphNumericalInvariant (T : BigFppfOver B S hS)
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) (i : N.I) :
    IsLocallyConstant (graphNumericalInvariant B S hS hsep hx_fp hfp hflat hproper N T s i) :=
  (N.isLocallyConstant_numericalEuler _ i).comp_continuous
    (schemePointsHomeomorph B S hS _).symm.continuous

/-- The invariants of the graph of a restricted relative morphism are those of the graph at the
image points (Stacks 0A1P). -/
theorem graphNumericalInvariant_map {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) (i : N.I)
    (t : (BigFppfOver.toScheme B S hS).obj T') :
    graphNumericalInvariant B S hS hsep hx_fp hfp hflat hproper N T'
        ((relativeHom B S hS Z X Q z x hZ hX hQ).map g.op s) i t =
      graphNumericalInvariant B S hS hsep hx_fp hfp hflat hproper N T s i
        ((BigFppfOver.toScheme B S hS).map g t) := by
  simp only [graphNumericalInvariant]
  rw [graphFamilyOfSection_map B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper g s]
  exact hilbertCohObject_baseChange_apply _ _ _
    (fun φ i t => CoherentSituation.schemePointsFunction_hom
      (fun φ i t => N.numericalEuler_eq_of_hom φ i t) φ i t) g _ i t

/-- A relative morphism lies in `Mor^P_Q(Z, X)` exactly when the invariants of its graph take the
prescribed values at every point of the test scheme. -/
theorem mem_numericalSituationRelativeHom_iff (T : BigFppfOver B S hS)
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    s ∈ (numericalSituationRelativeHom B S hS hsep hx_fp hfp hflat hproper N).obj (op T) ↔
      ∀ i t, graphNumericalInvariant B S hS hsep hx_fp hfp hflat hproper N T s i t = N.P i :=
  (mem_prescribedRelativeHom_iff hsep hx_fp hfp hflat hproper N
    (fun φ i t => N.numericalEuler_eq_of_hom φ i t) s).trans
    (CoherentSituation.forall_schemePointsFunction_eq_iff N.P _).symm

/-- The morphism `Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is a flat closed immersion. -/
@[stacks 0DPQ "`Mor^P_B(Y, X) ⟶ Mor_B(Y, X)` is a flat closed immersion"]
theorem isFlat_and_isClosedImmersion_numericalSituationRelativeHom_ι :
    IsFlat B S hS (numericalSituationRelativeHom B S hS hsep hx_fp hfp hflat hproper N).ι ∧
      IsClosedImmersion B S hS
        (numericalSituationRelativeHom B S hS hsep hx_fp hfp hflat hproper N).ι :=
  isFlat_and_isClosedImmersion_prescribedRelativeHom_ι hsep hx_fp hfp hflat hproper N
    (fun φ i t => N.numericalEuler_eq_of_hom φ i t)
    (fun A i => N.isLocallyConstant_numericalEuler A i)

/-- For `I` finite the morphism `Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is an open and closed immersion. -/
@[stacks 0DPQ "for `I` finite, `Mor^P_B(Y, X) ⟶ Mor_B(Y, X)` is an open and closed immersion"]
theorem isOpenImmersion_and_isClosedImmersion_numericalSituationRelativeHom_ι [Finite N.I] :
    IsOpenImmersion B S hS (numericalSituationRelativeHom B S hS hsep hx_fp hfp hflat hproper N).ι ∧
      IsClosedImmersion B S hS
        (numericalSituationRelativeHom B S hS hsep hx_fp hfp hflat hproper N).ι :=
  isOpenImmersion_and_isClosedImmersion_prescribedRelativeHom_ι hsep hx_fp hfp hflat hproper N
    (fun φ i t => N.numericalEuler_eq_of_hom φ i t)
    (fun A i => N.isLocallyConstant_numericalEuler A i)

/-- If `Q` is locally Noetherian, then for any index set `I` the morphism
`Mor^P_Q(Z, X) ⟶ Mor_Q(Z, X)` is an open and closed immersion. -/
@[stacks 0DPQ "for `B` locally Noetherian, `Mor^P_B(Y, X) ⟶ Mor_B(Y, X)` is an open and closed \
immersion, for an arbitrary index set `I`"]
theorem isOpenImmersion_and_isClosedImmersion_numericalSituationRelativeHom_ι_of_isLocallyNoetherian
    (hQN : IsLocallyNoetherian B S hS Q) :
    IsOpenImmersion B S hS (numericalSituationRelativeHom B S hS hsep hx_fp hfp hflat hproper N).ι ∧
      IsClosedImmersion B S hS
        (numericalSituationRelativeHom B S hS hsep hx_fp hfp hflat hproper N).ι := by
  have hcut : IsCutOutByPoints.{0}
      (numericalSituationRelativeHom B S hS hsep hx_fp hfp hflat hproper N)
      fun _ W => IsClopen W :=
    isCutOutByPoints_isClopen_of_isClopen _ N.P
      (graphNumericalInvariant B S hS hsep hx_fp hfp hflat hproper N)
      (fun _ _ => graphNumericalInvariant_map B S hS hsep hx_fp hfp hflat hproper N)
      (mem_numericalSituationRelativeHom_iff B S hS hsep hx_fp hfp hflat hproper N)
      (isClopen_setOf_forall_eq_of_isLocallyNoetherian B S hS Z X Q z x hZ hX hQ hfp hx_fp hQN
        (graphNumericalInvariant B S hS hsep hx_fp hfp hflat hproper N)
        (isLocallyConstant_graphNumericalInvariant B S hS hsep hx_fp hfp hflat hproper N)
        (fun _ _ => graphNumericalInvariant_map B S hS hsep hx_fp hfp hflat hproper N) N.P)
  exact ⟨MorphismProperty.relative_monotone (fun _ _ _ h => h.1) _
      ((MorphismProperty.presheaf_iff_relative_uliftYoneda _ _).2
        (relative_openImmersion_closedImmersion_ι _ hcut)),
    (isFlat_and_isClosedImmersion_numericalSituationRelativeHom_ι B S hS hsep hx_fp hfp hflat
      hproper N).2⟩

end Numerical

section HilbertPolynomial

variable (B S hS) {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}
    {hZ : IsAlgebraicSpace B S hS Z} {hX : IsAlgebraicSpace B S hS X}
    {hQ : IsAlgebraicSpace B S hS Q}
    (hsep : IsSeparated B S hS x) (hx_fp : IsFinitePresentation B S hS x)
    (hfp : IsFinitePresentation B S hS z) (hflat : IsFlat B S hS z) (hproper : IsProper B S hS z)
    (L : Modules.{u, u} B S hS
      (structureSheafQuotSituation (graphAmbientMap B S hS z x hZ hX hQ)
        (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hx_fp)).toCoherentSituation.X.1
      (structureSheafQuotSituation (graphAmbientMap B S hS z x hZ hX hQ)
        (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hx_fp)).toCoherentSituation.X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS
      (structureSheafQuotSituation (graphAmbientMap B S hS z x hZ hX hQ)
        (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hx_fp)).toCoherentSituation.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (structureSheafQuotSituation (graphAmbientMap B S hS z x hZ hX hQ)
          (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hx_fp)).toCoherentSituation.X.1
        (structureSheafQuotSituation (graphAmbientMap B S hS z x hZ hX hQ)
          (isFinitePresentation_graphAmbientMap z x hZ hX hQ
            hfp hx_fp)).toCoherentSituation.X.2).O)).property
      L]
    (P : ℤ → ℤ)

/-- The subfunctor `Mor^{P, L}_Q(Z, X)`: `Mor^P_Q(Z, X)` for `I = ℤ` and `E_n = L^{⊗ n}`, an
invertible `𝒪_{Z ×_Q X}`-module `L`. Its sections over `T` are the relative morphisms whose graph
`W ⊆ (Z ×_Q X)_T` has `χ((Z ×_Q X)_t, 𝒪_{W_t} ⊗ L_t^{⊗ n}) = P(n)` for every `n ∈ ℤ` and every
point `t` of `T`, the invariants `χ(X_t, E_{n,t} ⊗^𝐋 𝒪_{W_t})` of Situation 0DNC for
`E_n = L^{⊗ n}`: the pull-back along the graph transformation of the subfunctor of
`Hilb_{Z ×_Q X / Q}` corresponding to `Coh^{P, L}_{Z ×_Q X / Q}` (Stacks 0DNF). -/
@[stacks 0DPQ "the notation `Mor^{P, L}_B(Y, X)`: `Mor^P_B(Y, X)` for `I = ℤ` and \
`E_i = L^{⊗ i}`, the relative morphisms whose graph `W` has \
`χ((Y ×_B X)_t, 𝒪_{W_t} ⊗ L_t^{⊗ i}) = P(i)` for all `i` and `t`"]
def hilbertPolynomialSituationRelativeHom : Subfunctor (relativeHom B S hS Z X Q z x hZ hX hQ) :=
  relativeHomGraphPreimage B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper
    (hilbertCondition _ (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hx_fp)
      (CoherentObject.HasHilbertPolynomial L P)
      fun φ h => (CoherentSituation.isOpenAndClosedCondition_hasHilbertPolynomial L P).of_hom φ h)

/-- A relative morphism lies in `Mor^{P, L}_Q(Z, X)` exactly when the object `(T, 𝒪_W)` of
`Coh_{Z ×_Q X / Q}` of its graph `W` has `χ((Z ×_Q X)_t, 𝒪_{W_t} ⊗ L_t^{⊗ n}) = P(n)` for all `n`
and `t`. -/
theorem mem_hilbertPolynomialSituationRelativeHom_iff (T : BigFppfOver B S hS)
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    s ∈ (hilbertPolynomialSituationRelativeHom B S hS hsep hx_fp hfp hflat hproper L P).obj
        (op T) ↔
      CoherentObject.HasHilbertPolynomial L P
        (hilbertCohObject _ (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hx_fp)
          (graphFamilyOfSection B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper T s)) :=
  Iff.rfl

/-- For an invertible `𝒪_{Z ×_Q X}`-module `L` and any `P : ℤ → ℤ`, the morphism
`Mor^{P, L}_Q(Z, X) ⟶ Mor_Q(Z, X)` is an open and closed immersion. -/
@[stacks 0DPQ "for `I = ℤ` and `E_i = L^{⊗ i}` with `L` an invertible module on `Y ×_B X`, \
`Mor^{P, L}_B(Y, X) ⟶ Mor_B(Y, X)` is an open and closed immersion"]
theorem isOpenImmersion_and_isClosedImmersion_hilbertPolynomialSituationRelativeHom_ι :
    IsOpenImmersion B S hS
        (hilbertPolynomialSituationRelativeHom B S hS hsep hx_fp hfp hflat hproper L P).ι ∧
      IsClosedImmersion B S hS
        (hilbertPolynomialSituationRelativeHom B S hS hsep hx_fp hfp hflat hproper L P).ι :=
  isOpenImmersion_and_isClosedImmersion_graphPreimage_hilbertCondition_ι B S hS Z X Q z x hZ hX
    hQ hsep hfp hflat hproper hx_fp
    (fun φ h => (CoherentSituation.isOpenAndClosedCondition_hasHilbertPolynomial L P).of_hom φ h)
    (CoherentSituation.isOpenAndClosedCondition_hasHilbertPolynomial L P).isCutOutOnTestSchemes

end HilbertPolynomial

end AlgebraicGeometry.Space

end
