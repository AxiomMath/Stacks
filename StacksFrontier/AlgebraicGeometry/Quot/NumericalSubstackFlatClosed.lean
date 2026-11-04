module

public import StacksFrontier.AlgebraicGeometry.Quot.NumericalDirectImage
public import StacksFrontier.AlgebraicGeometry.Quot.QuotCoherentCondition

/-!
# Flat closed conditions on the objects of `Coh_{X/Y}`

Let `f : X ⟶ Y` be a finitely presented morphism of algebraic spaces, the standing data of
Stacks 08KB, and let `Q` be a condition on the objects `(T, g, 𝓕)` of `Coh_{X/Y}`.  The strictly
full subcategory `Coh^Q ⊆ Coh_{X/Y}` cut out by `Q` is a *flat closed substack* when its inclusion
is representable by flat closed immersions: for every object `A = (T, g, 𝓕)` the 2-fibre product
`T ×_{Coh_{X/Y}} Coh^Q` is represented by a flat closed immersion `V ⟶ T`.  Since `Coh_{X/Y}` is
fibred in groupoids (Stacks 08W5), an object of that 2-fibre product over a scheme `T'` is a
morphism `A' ⟶ A` of `Coh_{X/Y}` with `Q A'`, so the condition says: a morphism `A' ⟶ A` lying
over `h : T' ⟶ T` has `Q A'` exactly when `h` factors through `V`.

By Stacks 04PW a flat closed immersion into `T` is determined by its image, a closed subset of
`|T|` stable under generalization, and every morphism of schemes landing in that image factors
through it.  So `Q` is a flat closed condition exactly when it is cut out on every test scheme by
a closed subset stable under generalization.  This is the form of the first assertion of
Stacks 0DND: the locus where the locally constant functions `χ_i` of Situation 0DNC take the
values `P(i)` is an intersection of open and closed sets, hence closed and stable under
generalization, and it is open and closed when there are finitely many of them.

## Main definitions

Except where another namespace is given, the names below are in `AlgebraicGeometry.Space`.

* `CoherentSituation.IsFlatClosedCondition`: a condition on the objects
  of `Coh_{X/Y}` cuts out a flat closed substack.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_comp_eq_of_range_subset_of_flat`: a morphism of schemes
  whose image lies in the image of a flat, quasi-compact monomorphism factors through it.
* `CoherentSituation.isFlatClosedCondition_iff_isCutOutOnTestSchemes`:
  a condition is flat closed exactly when it is cut out on the test schemes by closed subsets
  stable under generalization.
* `CoherentSituation.isOpenAndClosedCondition_iff_isCutOutOnTestSchemes`:
  and open and closed exactly when it is cut out by open and closed subsets.
* `CoherentSituation.IsOpenAndClosedCondition.isFlatClosedCondition`: an
  open and closed condition is a flat closed condition.
* `CoherentSituation.isFlatClosedCondition_of_isLocallyConstant` and
  `CoherentSituation.isOpenAndClosedCondition_of_isLocallyConstant`: a
  condition "`χ_A i t = P i` for all `i` and `t`", for locally constant functions compatible
  with pullback, is a flat closed condition, and an open and closed condition when the index set
  is finite; with the variants `_points` for functions on the points of the represented test
  spaces.
* `CoherentSituation.isOpenAndClosedCondition_of_noetherianDescent`:
  for any index set, the condition is open and closed when every object is, near every point of
  its test scheme, pulled back from an object over a locally Noetherian test scheme.
* `NumericalSituation.isFlatClosedCondition_hasNumericalInvariants` and
  `NumericalSituation.isOpenAndClosedCondition_hasNumericalInvariants`:
  for the functions `χ_i` of Situation 0DNC, the inclusion `Coh^P_{X/B} ⊆ Coh_{X/B}` is a flat
  closed immersion, and an open and closed immersion for finite `I`, as soon as each `χ_i` is
  locally constant and compatible with pullback along the morphisms of `Coh_{X/B}`.
* `NumericalSituation.isOpenAndClosedCondition_hasNumericalInvariants_of_noetherianDescent`:
  for an arbitrary `I`, an open and closed immersion when moreover every object is, near every
  point of its test scheme, pulled back from one over a locally Noetherian test scheme; this is
  the form in which the source concludes for `B` locally Noetherian.

## Implementation notes

`AlgebraicGeometry.Space.CoherentSituation.IsFlatClosedCondition` is the condition of Stacks 04XB
for the property "flat closed immersion" and the inclusion of a strictly full subcategory of
`Coh_{X/Y}`, written out on the objects and morphisms of Stacks 08KB, exactly as
`AlgebraicGeometry.Space.CoherentSituation.IsOpenAndClosedCondition` is for "open and closed
immersion".  It does not presuppose that `Coh_{X/Y}` is algebraic.

The two properties of the functions `χ_i` used for Situation 0DNC — compatibility with pullback
along the morphisms of `Coh_{X/B}` and local constancy — are what the source deduces from the
perfectness of `K_i = Rf_{T,*}(E_{i,T} ⊗^𝐋 𝓕)` and the base change property of its formation
(Stacks 0A1P), together with Stacks 0D1Z; they enter here as hypotheses.

## References

* [Stacks Project, Tag 0DND](https://stacks.math.columbia.edu/tag/0DND)
* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 04PW](https://stacks.math.columbia.edu/tag/04PW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 08W5](https://stacks.math.columbia.edu/tag/08W5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.Hom

/-- **Factorization through a flat monomorphism.**  A morphism of schemes `g : Y ⟶ X` whose image
lies in the image of a flat, quasi-compact monomorphism `s : V ⟶ X` factors through `s`: the base
change of `s` along `g` is a flat, quasi-compact, surjective monomorphism, hence an isomorphism. -/
theorem exists_comp_eq_of_range_subset_of_flat {X Y V : Scheme.{u}} (s : V ⟶ X) [Flat s]
    [QuasiCompact s] [Mono s] (g : Y ⟶ X) (hg : Set.range g ⊆ Set.range s) :
    ∃ l : Y ⟶ V, l ≫ s = g := by
  have : Surjective (pullback.fst g s) := by
    rwa [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_fst,
      Set.preimage_eq_univ_iff]
  have : IsIso (pullback.fst g s) := Flat.isIso_of_surjective_of_mono (pullback.fst g s)
  exact ⟨inv (pullback.fst g s) ≫ pullback.snd g s, by simp [← pullback.condition]⟩

/-- A morphism of schemes factors through a flat closed immersion exactly when its image lies in
the image of that immersion. -/
theorem exists_comp_eq_iff_range_subset_of_flat {X Y V : Scheme.{u}} (s : V ⟶ X)
    [IsClosedImmersion s] [Flat s] (g : Y ⟶ X) :
    (∃ l : Y ⟶ V, l ≫ s = g) ↔ Set.range g ⊆ Set.range s := by
  refine ⟨?_, exists_comp_eq_of_range_subset_of_flat s g⟩
  rintro ⟨l, rfl⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp]
  exact Set.range_comp_subset_range _ _

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

namespace CoherentSituation

variable (D) in
/-- A condition `Q` on the objects of `Coh_{X/Y}` cuts out a **flat closed substack**: for every
object `A = (T, g, 𝓕)` there is a flat closed immersion `s : V ⟶ T` such that a morphism `A' ⟶ A`
of `Coh_{X/Y}` has `Q A'` exactly when its morphism of test schemes factors through `s`.

This says that the inclusion of the strictly full subcategory cut out by `Q` is representable by
flat closed immersions: the 2-fibre product `T ×_{Coh_{X/Y}} Coh^Q` is represented by `V`. -/
def IsFlatClosedCondition (Q : CoherentObject D → Prop) : Prop :=
  ∀ A : CoherentObject D, ∃ (V : Scheme.{u}) (s : V ⟶ A.testScheme),
    _root_.AlgebraicGeometry.IsClosedImmersion s ∧ Flat s ∧
      ∀ (A' : CoherentObject D) (φ : CoherentHom A' A),
        Q A' ↔ ∃ l : A'.testScheme ⟶ V, l ≫ s = φ.baseScheme

/-- **A flat closed condition is one cut out on the test schemes by closed subsets stable under
generalization**: on each object, by the image of the flat closed immersion representing it
(Stacks 04PW). -/
theorem isFlatClosedCondition_iff_isCutOutOnTestSchemes {Q : CoherentObject D → Prop} :
    IsFlatClosedCondition D Q ↔
      IsCutOutOnTestSchemes D Q fun _ Z => IsClosed Z ∧ StableUnderGeneralization Z := by
  constructor
  · intro hQ A
    obtain ⟨V, s, hcl, hfl, hQs⟩ := hQ A
    refine ⟨Set.range s, ⟨(hcl.isClosedEmbedding).isClosed_range,
      (Flat.generalizingMap s).stableUnderGeneralization_range⟩,
      fun A' φ => (hQs A' φ).trans (Scheme.Hom.exists_comp_eq_iff_range_subset_of_flat s _)⟩
  · intro hQ A
    obtain ⟨Z, ⟨hZ, hgen⟩, hQZ⟩ := hQ A
    obtain ⟨I, hIflat, hIsupp⟩ :=
      (support_bijOn_flat_closedImmersions A.testScheme).surjOn
        (show (⟨Z, hZ⟩ : TopologicalSpace.Closeds A.testScheme) ∈
          {C : TopologicalSpace.Closeds A.testScheme |
            StableUnderGeneralization (C : Set A.testScheme)} from hgen)
    have : Flat I.subschemeι := hIflat
    have hrange : Set.range I.subschemeι = Z := by
      rw [I.range_subschemeι]
      exact congrArg (fun C : TopologicalSpace.Closeds A.testScheme => (C : Set A.testScheme))
        hIsupp
    refine ⟨I.subscheme, I.subschemeι, inferInstance, this, fun A' φ => ?_⟩
    rw [hQZ A' φ, Scheme.Hom.exists_comp_eq_iff_range_subset_of_flat, hrange]

/-- **An open and closed condition is one cut out on the test schemes by open and closed
subsets.** -/
theorem isOpenAndClosedCondition_iff_isCutOutOnTestSchemes {Q : CoherentObject D → Prop} :
    IsOpenAndClosedCondition D Q ↔ IsCutOutOnTestSchemes D Q fun _ Z => IsClopen Z := by
  refine ⟨IsOpenAndClosedCondition.isCutOutOnTestSchemes, fun hQ A => ?_⟩
  obtain ⟨Z, hZ, hQZ⟩ := hQ A
  exact ⟨⟨Z, hZ.isOpen⟩, hZ.isClosed, fun A' φ => (hQZ A' φ).trans
    (Scheme.Opens.exists_comp_ι_eq_iff_range_subset ⟨Z, hZ.isOpen⟩ _).symm⟩

/-- **An open and closed condition is a flat closed condition**: an open and closed subscheme is
a flat closed subscheme. -/
theorem IsOpenAndClosedCondition.isFlatClosedCondition {Q : CoherentObject D → Prop}
    (hQ : IsOpenAndClosedCondition D Q) : IsFlatClosedCondition D Q := by
  rw [isFlatClosedCondition_iff_isCutOutOnTestSchemes]
  intro A
  obtain ⟨Z, hZ, hQZ⟩ := isOpenAndClosedCondition_iff_isCutOutOnTestSchemes.1 hQ A
  exact ⟨Z, ⟨hZ.isClosed, hZ.isOpen.stableUnderGeneralization⟩, hQZ⟩

/-- A flat closed condition is inherited along every morphism of `Coh_{X/Y}`; in particular the
subcategory it cuts out is strictly full. -/
theorem IsFlatClosedCondition.of_hom {Q : CoherentObject D → Prop}
    (hQ : IsFlatClosedCondition D Q) {A' A : CoherentObject D} (φ : CoherentHom A' A)
    (hA : Q A) : Q A' :=
  (isFlatClosedCondition_iff_isCutOutOnTestSchemes.1 hQ).of_hom φ hA

section Numerical

variable {I : Type*} {β : Type*}

/-- **A numerical condition with locally constant functions is a flat closed condition.**  If `χ`
attaches to every object `A = (T, 𝒢)` of `Coh_{X/Y}` locally constant functions
`χ_A i : |T| → β` compatible with pullback, the condition "`χ_A i t = P i` for all `i` and `t`"
cuts out a flat closed substack, represented on `A` by the flat closed subscheme supported on the
locus where every `χ_A i` takes its prescribed value. -/
theorem isFlatClosedCondition_of_isLocallyConstant
    (χ : ∀ A : CoherentObject D, I → A.testScheme → β) (P : I → β)
    (hχ : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : I) (t : A'.testScheme),
      χ A' i t = χ A i (φ.baseScheme t))
    (hlc : ∀ A i, IsLocallyConstant (χ A i)) :
    IsFlatClosedCondition D fun A => ∀ i t, χ A i t = P i :=
  isFlatClosedCondition_iff_isCutOutOnTestSchemes.2
    (isCutOutOnTestSchemes_of_isLocallyConstant χ P hχ hlc)

/-- **The finite case.**  For a finite index set, a numerical condition with locally constant
functions compatible with pullback is an open and closed condition. -/
theorem isOpenAndClosedCondition_of_isLocallyConstant [Finite I]
    (χ : ∀ A : CoherentObject D, I → A.testScheme → β) (P : I → β)
    (hχ : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : I) (t : A'.testScheme),
      χ A' i t = χ A i (φ.baseScheme t))
    (hlc : ∀ A i, IsLocallyConstant (χ A i)) :
    IsOpenAndClosedCondition D fun A => ∀ i t, χ A i t = P i :=
  isOpenAndClosedCondition_iff_isCutOutOnTestSchemes.2
    (isCutOutOnTestSchemes_isClopen_of_isLocallyConstant χ P hχ hlc)

/-- **The Noetherian case.**  Let `χ` attach locally constant functions, compatible with pullback,
to the objects of `Coh_{X/Y}`.  Suppose every object `A` is, near every point of its test scheme,
pulled back from an object over a locally Noetherian test scheme: there are morphisms
`A ⟵ A' ⟶ A₀` of `Coh_{X/Y}` whose first morphism of test schemes is open on points and hits the
given point, and whose target `A₀` has a locally Noetherian test scheme.  Then the condition
"`χ_A i t = P i` for all `i` and `t`" is an open and closed condition, however large the index
set: on `A₀` the locus is an intersection of unions of connected components of a locally
Noetherian scheme, hence open. -/
theorem isOpenAndClosedCondition_of_noetherianDescent
    (χ : ∀ A : CoherentObject D, I → A.testScheme → β) (P : I → β)
    (hχ : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : I) (t : A'.testScheme),
      χ A' i t = χ A i (φ.baseScheme t))
    (hlc : ∀ A i, IsLocallyConstant (χ A i))
    (hloc : ∀ (A : CoherentObject D) (t : A.testScheme), ∃ (A' A₀ : CoherentObject D)
      (p : CoherentHom A' A) (_ : CoherentHom A' A₀) (t' : A'.testScheme),
        p.baseScheme t' = t ∧ IsOpenMap p.baseScheme ∧ IsLocallyNoetherian A₀.testScheme) :
    IsOpenAndClosedCondition D fun A => ∀ i t, χ A i t = P i := by
  refine isOpenAndClosedCondition_of_locally_factors χ P hχ fun A t => ?_
  obtain ⟨A', A₀, p, q, t', hpt, hp, hA₀⟩ := hloc A t
  refine ⟨A'.testScheme, p.baseScheme, t', hpt, hp, Set.univ, Filter.univ_mem, A₀.testScheme,
    hA₀, q.baseScheme, χ A₀, q.baseScheme.continuous.continuousAt, hlc A₀, fun i y _ => ?_⟩
  rw [← hχ p i y, hχ q i y]

attribute [local instance] pointTopology

/-- **A numerical condition read on points is a flat closed condition** when its functions on the
points of the represented test spaces are locally constant and compatible with pullback. -/
theorem isFlatClosedCondition_of_isLocallyConstant_points
    (χ : ∀ A : CoherentObject D, I → points B S hS (yoneda.obj A.T.left) → β) (P : I → β)
    (hχ : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : I)
      (t : points B S hS (yoneda.obj A'.T.left)),
      χ A' i t = χ A i (pointsMap B S hS _ (yoneda.map φ.base.left) t))
    (hlc : ∀ A i, IsLocallyConstant (χ A i)) :
    IsFlatClosedCondition D fun A => ∀ i t, χ A i t = P i :=
  isFlatClosedCondition_iff_isCutOutOnTestSchemes.2
    (isCutOutOnTestSchemes_of_isLocallyConstant_points P hχ hlc)

/-- **The finite case, read on points.** -/
theorem isOpenAndClosedCondition_of_isLocallyConstant_points [Finite I]
    (χ : ∀ A : CoherentObject D, I → points B S hS (yoneda.obj A.T.left) → β) (P : I → β)
    (hχ : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : I)
      (t : points B S hS (yoneda.obj A'.T.left)),
      χ A' i t = χ A i (pointsMap B S hS _ (yoneda.map φ.base.left) t))
    (hlc : ∀ A i, IsLocallyConstant (χ A i)) :
    IsOpenAndClosedCondition D fun A => ∀ i t, χ A i t = P i :=
  isOpenAndClosedCondition_iff_isCutOutOnTestSchemes.2
    (isCutOutOnTestSchemes_isClopen_of_isLocallyConstant_points P hχ hlc)

end Numerical

end CoherentSituation

namespace NumericalSituation

attribute [local instance] pointTopology

variable (N : NumericalSituation.{u, v, u} B S hS D)

/-- **`Coh^P_{X/B} ⊆ Coh_{X/B}` is a flat closed immersion**, as soon as the functions `χ_i` of
Situation 0DNC are compatible with pullback along the morphisms of `Coh_{X/B}` and locally
constant: `Coh^P_{X/B}` is the intersection of the open and closed substacks `Coh^{P|_J}_{X/B}`
over the finite subsets `J ⊆ I`. -/
theorem isFlatClosedCondition_hasNumericalInvariants
    (hbc : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : N.I)
      (t : points B S hS (yoneda.obj A'.T.left)),
      N.numericalEuler A' i t =
        N.numericalEuler A i (pointsMap B S hS _ (yoneda.map φ.base.left) t))
    (hlc : ∀ A i, IsLocallyConstant (N.numericalEuler A i)) :
    CoherentSituation.IsFlatClosedCondition D N.HasNumericalInvariants :=
  CoherentSituation.isFlatClosedCondition_of_isLocallyConstant_points N.numericalEuler N.P hbc hlc

/-- **For finite `I`, `Coh^P_{X/B}` is an open and closed substack of `Coh_{X/B}`**, as soon as
the functions `χ_i` of Situation 0DNC are compatible with pullback along the morphisms of
`Coh_{X/B}` and locally constant. -/
theorem isOpenAndClosedCondition_hasNumericalInvariants [Finite N.I]
    (hbc : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : N.I)
      (t : points B S hS (yoneda.obj A'.T.left)),
      N.numericalEuler A' i t =
        N.numericalEuler A i (pointsMap B S hS _ (yoneda.map φ.base.left) t))
    (hlc : ∀ A i, IsLocallyConstant (N.numericalEuler A i)) :
    CoherentSituation.IsOpenAndClosedCondition D N.HasNumericalInvariants :=
  CoherentSituation.isOpenAndClosedCondition_of_isLocallyConstant_points N.numericalEuler N.P hbc
    hlc

/-- **For `B` locally Noetherian, `Coh^P_{X/B}` is an open and closed substack of `Coh_{X/B}`**
in the form in which the source concludes, as soon as the functions `χ_i` of Situation 0DNC are
compatible with pullback and locally constant, and every object of `Coh_{X/B}` is, near every
point of its test scheme, pulled back from an object over a locally Noetherian test scheme. -/
theorem isOpenAndClosedCondition_hasNumericalInvariants_of_noetherianDescent
    (hbc : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : N.I)
      (t : points B S hS (yoneda.obj A'.T.left)),
      N.numericalEuler A' i t =
        N.numericalEuler A i (pointsMap B S hS _ (yoneda.map φ.base.left) t))
    (hlc : ∀ A i, IsLocallyConstant (N.numericalEuler A i))
    (hloc : ∀ (A : CoherentObject D) (t : A.testScheme), ∃ (A' A₀ : CoherentObject D)
      (p : CoherentHom A' A) (_ : CoherentHom A' A₀) (t' : A'.testScheme),
        p.baseScheme t' = t ∧ IsOpenMap p.baseScheme ∧ IsLocallyNoetherian A₀.testScheme) :
    CoherentSituation.IsOpenAndClosedCondition D N.HasNumericalInvariants := by
  convert CoherentSituation.isOpenAndClosedCondition_of_noetherianDescent
    (CoherentSituation.schemePointsFunction N.numericalEuler) N.P
    (CoherentSituation.schemePointsFunction_hom hbc)
    (fun A i => (hlc A i).comp_continuous (schemePointsHomeomorph B S hS A.T.left).symm.continuous)
    hloc using 2 with A
  exact (CoherentSituation.forall_schemePointsFunction_eq_iff N.P A).symm

end NumericalSituation

end AlgebraicGeometry.Space

end
