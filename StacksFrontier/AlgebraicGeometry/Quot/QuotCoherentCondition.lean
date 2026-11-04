module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertQuotFunctorEquality
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalSubstackLocus
public import StacksFrontier.AlgebraicGeometry.Quot.QuotToCoherentStack
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatClosedLocus

/-!
# Conditions on `Coh_{X/B}` pulled back to `Quot_{F/X/B}` and to `Hilb_{X/B}`

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation and `F` a
quasi-coherent `𝒪_X`-module.  The morphism `Quot_{F/X/B} ⟶ Coh_{X/B}` of Stacks 0DP6 sends a
quotient `F_T ⟶ 𝒬` to the object `(T, 𝒬)`.  A condition `Q` on the objects of `Coh_{X/B}`
which is inherited along the morphisms of `Coh_{X/B}` cuts out a strictly full subcategory
`Coh^Q_{X/B}`, and the fibre product `Quot_{F/X/B} ×_{Coh_{X/B}} Coh^Q_{X/B}` is the subfunctor
of `Quot_{F/X/B}` of quotients whose object of `Coh_{X/B}` satisfies `Q`.  For `F = 𝒪_X`,
composing with the identification `Hilb_{X/B} = Quot_{𝒪_X/X/B}` of Stacks 0D00 gives the
subfunctor of `Hilb_{X/B}` of families `Z ⊆ X_T` for which `(T, 𝒪_Z)` satisfies `Q`.

If on every object `(T, 𝒢)` of `Coh_{X/B}` the condition is cut out by a subset of `|T|` which is
closed and stable under generalization — a morphism `(T', 𝒢') ⟶ (T, 𝒢)` has `Q(T', 𝒢')` exactly
when `T' ⟶ T` maps into that subset — then the inclusions of both fibre products are
representable by flat closed immersions; if the subsets are open and closed, by open and closed
immersions.  This is how the source passes from Lemmas 0DND and 0DNE about `Coh^P_{X/B}` to
Remarks 0DP6 and 0DPG about `Quot^P_{F/X/B}` and `Hilb^P_{X/B}`: by base change.

## Main definitions

* `AlgebraicGeometry.Space.QuotFamilyOver.cohObject`: the object of `Coh_{X/B}` attached to a
  section of the Quot presheaf, and `AlgebraicGeometry.Space.QuotFamilyOver.cohHomBaseChange` the
  morphism of `Coh_{X/B}` from the object of a base change to the object of the section.
* `AlgebraicGeometry.Space.CoherentSituation.IsCutOutOnTestSchemes`: a condition on the objects
  of `Coh_{X/B}` is cut out, on every object, by a set of points of its test scheme with a
  prescribed property.
* `AlgebraicGeometry.Space.QuotSituation.quotCondition`: the fibre product
  `Quot_{F/X/B} ×_{Coh_{X/B}} Coh^Q_{X/B}`, as a subfunctor of the Quot presheaf.
* `AlgebraicGeometry.Space.hilbertCondition`: the subfunctor of the Hilbert presheaf
  corresponding to it under Stacks 0D00.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isCutOutOnTestSchemes_of_isLocallyConstant` and
  `AlgebraicGeometry.Space.CoherentSituation.isCutOutOnTestSchemes_isClopen_of_isLocallyConstant`:
  a condition "`χ_i = P i` for all `i`", for locally constant functions compatible with pullback,
  is cut out on the test schemes by closed sets stable under generalization, and by open and
  closed sets when the index set is finite.
* `AlgebraicGeometry.Space.QuotSituation.relative_closedImmersion_flat_quotCondition_ι` and
  `AlgebraicGeometry.Space.QuotSituation.relative_openImmersion_closedImmersion_quotCondition_ι`:
  the inclusion of `Quot_{F/X/B} ×_{Coh_{X/B}} Coh^Q_{X/B}` is representable by flat closed
  immersions, respectively by open and closed immersions.
* `AlgebraicGeometry.Space.relative_closedImmersion_flat_hilbertCondition_ι` and
  `AlgebraicGeometry.Space.relative_openImmersion_closedImmersion_hilbertCondition_ι`: the same
  for the corresponding subfunctor of `Hilb_{X/B}`.

## References

* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
* [Stacks Project, Tag 0DPG](https://stacks.math.columbia.edu/tag/0DPG)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- The modules here have their sections in the universe of the schemes; left in place, this
-- instance is selected ahead of `SheafOfModules.instAbelian` and leaves module universes unsolved.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The object of `Coh_{X/B}` of a section of the Quot presheaf -/

namespace QuotFamilyOver

variable {D : QuotSituation B S hS}

/-- The object `(T, 𝒬)` of `Coh_{X/B}` attached to a section `F_T ⟶ 𝒬` of the Quot presheaf over
a scheme `T` of the site: the image of the section under the morphism
`Quot_{F/X/B} ⟶ Coh_{X/B}` of Stacks 0DP6. -/
abbrev cohObject {T : BigFppfOver B S hS} (x : QuotFamilyOver D T) :
    CoherentObject D.toCoherentSituation :=
  D.cohObject _ x.subobject x.mem

/-- The morphism of `Coh_{X/B}` from the object attached to the base change of a section of the
Quot presheaf to the object attached to the section: the action of Stacks 0DP6 on the morphism of
test schemes. -/
abbrev cohHomBaseChange {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (x : QuotFamilyOver D T) :
    CoherentHom (x.baseChange g).cohObject x.cohObject :=
  D.cohHom (restrict g x.toBase) x.mem

/-- The morphism of test schemes underlying that morphism of `Coh_{X/B}` is the given morphism of
schemes of the site. -/
@[simp]
theorem baseScheme_cohHomBaseChange {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (x : QuotFamilyOver D T) :
    (x.cohHomBaseChange g).baseScheme = (BigFppfOver.toScheme B S hS).map g :=
  rfl

end QuotFamilyOver

/-! ### Conditions cut out on the test schemes -/

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

/-- A condition `Q` on the objects of `Coh_{X/B}` is *cut out on the test schemes by sets with
property `p`* when for every object `A = (T, 𝒢)` there is a subset `Z ⊆ |T|` with property `p`
such that a morphism `A' ⟶ A` of `Coh_{X/B}` has `Q A'` exactly when its morphism of test schemes
maps into `Z`.

For `p` "open and closed" this says that the inclusion of the strictly full subcategory cut out by
`Q` is representable by open and closed immersions; for `p` "closed and stable under
generalization", by flat closed immersions (Stacks 04PW). -/
def IsCutOutOnTestSchemes (Q : CoherentObject D → Prop) (p : ∀ A : CoherentObject D,
    Set A.testScheme → Prop) : Prop :=
  ∀ A : CoherentObject D, ∃ Z : Set A.testScheme, p A Z ∧
    ∀ (A' : CoherentObject D) (φ : CoherentHom A' A), Q A' ↔ Set.range φ.baseScheme ⊆ Z

variable {D}

/-- A condition cut out on the test schemes is inherited along the morphisms of `Coh_{X/B}`.
The identity of an object is a morphism of `Coh_{X/B}`, so `Q A` says that `|T|` maps into the
subset cutting out `Q` on `A`, and then so does every morphism into `A`. -/
theorem IsCutOutOnTestSchemes.of_hom {Q : CoherentObject D → Prop}
    {p : ∀ A : CoherentObject D, Set A.testScheme → Prop} (hQ : IsCutOutOnTestSchemes D Q p)
    {A' A : CoherentObject D} (φ : CoherentHom A' A) (hA : Q A) : Q A' := by
  obtain ⟨Z, -, hZ⟩ := hQ A
  have hid := (hZ A (CoherentHom.id (modulePushforwardCoherence B S hS) A)).1 hA
  refine (hZ A' φ).2 ?_
  rintro _ ⟨t, rfl⟩
  exact hid ⟨φ.baseScheme t, by simp [CoherentHom.id]⟩

/-- An open and closed condition in the sense of
`AlgebraicGeometry.Space.CoherentSituation.IsOpenAndClosedCondition` is cut out on the test
schemes by open and closed sets. -/
theorem IsOpenAndClosedCondition.isCutOutOnTestSchemes {Q : CoherentObject D → Prop}
    (hQ : IsOpenAndClosedCondition D Q) :
    IsCutOutOnTestSchemes D Q fun _ Z => IsClopen Z := by
  intro A
  obtain ⟨U, hU, hQU⟩ := hQ A
  exact ⟨U, ⟨hU, U.2⟩, fun A' φ => (hQU A' φ).trans
    (Scheme.Opens.exists_comp_ι_eq_iff_range_subset U _)⟩

section Numerical

variable {I : Type*} {β : Type*} (χ : ∀ A : CoherentObject D, I → A.testScheme → β) (P : I → β)

/-- **A numerical condition is inherited along the morphisms of `Coh_{X/B}`** when its functions
are compatible with pullback. -/
theorem numerical_of_hom
    (hχ : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : I) (t : A'.testScheme),
      χ A' i t = χ A i (φ.baseScheme t))
    {A' A : CoherentObject D} (φ : CoherentHom A' A) (hA : ∀ i t, χ A i t = P i) :
    ∀ i t, χ A' i t = P i :=
  fun i t => (hχ φ i t).trans (hA i _)

/-- A numerical condition is cut out on `A` by the locus where all the `χ_A i` take the prescribed
values, as soon as that locus has the required property. -/
private theorem isCutOutOnTestSchemes_of_iInter_fiber
    (hχ : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : I) (t : A'.testScheme),
      χ A' i t = χ A i (φ.baseScheme t))
    {p : ∀ A : CoherentObject D, Set A.testScheme → Prop}
    (hp : ∀ A, p A (⋂ i, {t | χ A i t = P i})) :
    IsCutOutOnTestSchemes D (fun A => ∀ i t, χ A i t = P i) p := fun A =>
  ⟨_, hp A, fun A' φ => by
    constructor
    · rintro hx _ ⟨t, rfl⟩
      exact Set.mem_iInter.2 fun i => (hχ φ i t).symm.trans (hx i t)
    · intro hx i t
      exact (hχ φ i t).trans (Set.mem_iInter.1 (hx ⟨t, rfl⟩) i)⟩

/-- **A numerical condition with locally constant functions is cut out on the test schemes by
closed sets stable under generalization.**  If `χ` attaches to every object `A = (T, 𝒢)` of
`Coh_{X/B}` locally constant functions `χ_A i : |T| → β` compatible with pullback, the condition
"`χ_A i t = P i` for all `i` and `t`" is cut out on `A` by the locus where all the `χ_A i` take the
prescribed values, an intersection of open and closed sets. -/
theorem isCutOutOnTestSchemes_of_isLocallyConstant
    (hχ : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : I) (t : A'.testScheme),
      χ A' i t = χ A i (φ.baseScheme t))
    (hlc : ∀ A i, IsLocallyConstant (χ A i)) :
    IsCutOutOnTestSchemes D (fun A => ∀ i t, χ A i t = P i)
      fun _ Z => IsClosed Z ∧ StableUnderGeneralization Z := by
  exact isCutOutOnTestSchemes_of_iInter_fiber χ P hχ fun A =>
    isClosed_and_stableUnderGeneralization_iInter_isClopen fun i =>
      (hlc A i).isClopen_fiber (P i)

/-- **The finite case.**  When the index set is finite, a numerical condition with locally
constant functions compatible with pullback is cut out on the test schemes by open and closed
sets: a finite intersection of open and closed sets is open and closed. -/
theorem isCutOutOnTestSchemes_isClopen_of_isLocallyConstant [Finite I]
    (hχ : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : I) (t : A'.testScheme),
      χ A' i t = χ A i (φ.baseScheme t))
    (hlc : ∀ A i, IsLocallyConstant (χ A i)) :
    IsCutOutOnTestSchemes D (fun A => ∀ i t, χ A i t = P i) fun _ Z => IsClopen Z := by
  exact isCutOutOnTestSchemes_of_iInter_fiber χ P hχ fun A =>
    isClopen_iInter_of_finite fun i => (hlc A i).isClopen_fiber (P i)

end Numerical

section Points

attribute [local instance] pointTopology

variable {I : Type*} {β : Type*}
  (χ : ∀ A : CoherentObject D, I → points B S hS (yoneda.obj A.T.left) → β) (P : I → β)

/-- The functions on the points of the test schemes read on the points of the represented
presheaves, transported to the points of the schemes along the homeomorphism of Stacks 03BX. -/
def schemePointsFunction (A : CoherentObject D) (i : I) (t : A.testScheme) : β :=
  χ A i ((schemePointsHomeomorph B S hS A.T.left).symm t)

variable {χ}

/-- Compatibility with pullback transports along the homeomorphisms of Stacks 03BX. -/
theorem schemePointsFunction_hom
    (hχ : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : I)
      (t : points B S hS (yoneda.obj A'.T.left)),
      χ A' i t = χ A i (pointsMap B S hS _ (yoneda.map φ.base.left) t))
    {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : I) (t : A'.testScheme) :
    schemePointsFunction χ A' i t = schemePointsFunction χ A i (φ.baseScheme t) := by
  rw [schemePointsFunction, hχ φ i, schemePointsHomeomorph_symm_naturality]
  rfl

/-- The condition "`χ_A i t = P i` for all `i` and all points `t`" reads the same on the points
of the represented presheaf and on the points of the scheme. -/
theorem forall_schemePointsFunction_eq_iff (A : CoherentObject D) :
    (∀ i t, schemePointsFunction χ A i t = P i) ↔ ∀ i t, χ A i t = P i := by
  refine ⟨fun h i t => ?_, fun h i t => h i _⟩
  simpa [schemePointsFunction] using h i (schemePointsHomeomorph B S hS A.T.left t)

/-- A condition cut out on the test schemes for the transported functions is cut out for the
original functions. -/
private theorem isCutOutOnTestSchemes_of_schemePointsFunction
    {p : ∀ A : CoherentObject D, Set A.testScheme → Prop}
    (h : IsCutOutOnTestSchemes D (fun A => ∀ i t, schemePointsFunction χ A i t = P i) p) :
    IsCutOutOnTestSchemes D (fun A => ∀ i t, χ A i t = P i) p := fun A =>
  let ⟨Z, hZ, hQ⟩ := h A
  ⟨Z, hZ, fun A' φ => (forall_schemePointsFunction_eq_iff P A').symm.trans (hQ A' φ)⟩

/-- A numerical condition on the points of the represented test spaces is inherited along the
morphisms of `Coh_{X/B}` when its functions are compatible with pullback. -/
theorem numerical_points_of_hom
    (hχ : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : I)
      (t : points B S hS (yoneda.obj A'.T.left)),
      χ A' i t = χ A i (pointsMap B S hS _ (yoneda.map φ.base.left) t))
    {A' A : CoherentObject D} (φ : CoherentHom A' A) (hA : ∀ i t, χ A i t = P i) :
    ∀ i t, χ A' i t = P i :=
  fun i t => (hχ φ i t).trans (hA i _)

/-- **A numerical condition with locally constant functions on the points of the represented
test spaces is cut out on the test schemes by closed sets stable under generalization.** -/
theorem isCutOutOnTestSchemes_of_isLocallyConstant_points
    (hχ : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : I)
      (t : points B S hS (yoneda.obj A'.T.left)),
      χ A' i t = χ A i (pointsMap B S hS _ (yoneda.map φ.base.left) t))
    (hlc : ∀ A i, IsLocallyConstant (χ A i)) :
    IsCutOutOnTestSchemes D (fun A => ∀ i t, χ A i t = P i)
      fun _ Z => IsClosed Z ∧ StableUnderGeneralization Z := by
  have h := isCutOutOnTestSchemes_of_isLocallyConstant (D := D) (schemePointsFunction χ) P
    (schemePointsFunction_hom hχ) fun A i =>
      (hlc A i).comp_continuous (schemePointsHomeomorph B S hS A.T.left).symm.continuous
  exact isCutOutOnTestSchemes_of_schemePointsFunction (χ := χ) P h

/-- **The finite case**, on the points of the represented test spaces. -/
theorem isCutOutOnTestSchemes_isClopen_of_isLocallyConstant_points [Finite I]
    (hχ : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : I)
      (t : points B S hS (yoneda.obj A'.T.left)),
      χ A' i t = χ A i (pointsMap B S hS _ (yoneda.map φ.base.left) t))
    (hlc : ∀ A i, IsLocallyConstant (χ A i)) :
    IsCutOutOnTestSchemes D (fun A => ∀ i t, χ A i t = P i) fun _ Z => IsClopen Z := by
  have h := isCutOutOnTestSchemes_isClopen_of_isLocallyConstant (D := D)
    (schemePointsFunction χ) P (schemePointsFunction_hom hχ) fun A i =>
      (hlc A i).comp_continuous (schemePointsHomeomorph B S hS A.T.left).symm.continuous
  exact isCutOutOnTestSchemes_of_schemePointsFunction (χ := χ) P h

end Points

end CoherentSituation

/-! ### The fibre product with `Quot_{F/X/B}` -/

namespace QuotSituation

variable (D : QuotSituation B S hS) (Q : CoherentObject D.toCoherentSituation → Prop)

/-- **The fibre product `Quot_{F/X/B} ×_{Coh_{X/B}} Coh^Q_{X/B}`.**  For a condition `Q` on the
objects of `Coh_{X/B}` inherited along its morphisms, the subfunctor of the Quot presheaf of the
quotients `F_T ⟶ 𝒬` whose object `(T, 𝒬)` of `Coh_{X/B}` satisfies `Q`.  It is a subfunctor
because the object of a base change maps to the object of the section by
`AlgebraicGeometry.Space.QuotFamilyOver.cohHomBaseChange`. -/
def quotCondition
    (hQ : ∀ {A' A : CoherentObject D.toCoherentSituation}, CoherentHom A' A → Q A → Q A') :
    Subfunctor D.quotSitePresheaf where
  obj _ := {x | Q x.cohObject}
  map g x hx := hQ (x.cohHomBaseChange g.unop) hx

/-- Membership in the fibre product, unfolded. -/
theorem mem_quotCondition_iff
    (hQ : ∀ {A' A : CoherentObject D.toCoherentSituation}, CoherentHom A' A → Q A → Q A')
    {T : (BigFppfOver B S hS)ᵒᵖ} (x : D.quotSitePresheaf.obj T) :
    x ∈ (D.quotCondition Q hQ).obj T ↔ Q x.cohObject :=
  Iff.rfl

variable {Q} {p : ∀ U : BigFppfOver B S hS, Set ((BigFppfOver.toScheme B S hS).obj U) → Prop}

/-- If the condition is cut out on the test schemes of `Coh_{X/B}` by sets with property `p`, then
the fibre product is cut out by the same sets after base change to every scheme of the site. -/
theorem isCutOutByPoints_quotCondition
    (hQ : ∀ {A' A : CoherentObject D.toCoherentSituation}, CoherentHom A' A → Q A → Q A')
    (hcut : CoherentSituation.IsCutOutOnTestSchemes D.toCoherentSituation Q
      fun A Z => p A.T.left Z) :
    IsCutOutByPoints.{u + 1} (D.quotCondition Q hQ) p := by
  intro U x
  obtain ⟨Z, hpZ, hZ⟩ := hcut x.cohObject
  exact ⟨Z, hpZ, fun W h => hZ _ (x.cohHomBaseChange h)⟩

/-- **The fibre product with a flat closed substack is a flat closed subfunctor.**  If the
condition `Q` is cut out on the test schemes of `Coh_{X/B}` by closed sets stable under
generalization, the inclusion of `Quot_{F/X/B} ×_{Coh_{X/B}} Coh^Q_{X/B}` into `Quot_{F/X/B}`
is representable by flat closed immersions. -/
theorem relative_closedImmersion_flat_quotCondition_ι
    (hQ : ∀ {A' A : CoherentObject D.toCoherentSituation}, CoherentHom A' A → Q A → Q A')
    (hcut : CoherentSituation.IsCutOutOnTestSchemes D.toCoherentSituation Q
      fun _ Z => IsClosed Z ∧ StableUnderGeneralization Z) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} ⊓ @Flat.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} (D.quotCondition Q hQ).ι :=
  relative_closedImmersion_flat_ι _ (D.isCutOutByPoints_quotCondition hQ hcut)

/-- **The fibre product with an open and closed substack is an open and closed subfunctor.**  If
the condition `Q` is cut out on the test schemes of `Coh_{X/B}` by open and closed sets, the
inclusion of `Quot_{F/X/B} ×_{Coh_{X/B}} Coh^Q_{X/B}` into `Quot_{F/X/B}` is representable by
morphisms which are open and closed immersions. -/
theorem relative_openImmersion_closedImmersion_quotCondition_ι
    (hQ : ∀ {A' A : CoherentObject D.toCoherentSituation}, CoherentHom A' A → Q A → Q A')
    (hcut : CoherentSituation.IsCutOutOnTestSchemes D.toCoherentSituation Q
      fun _ Z => IsClopen Z) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} ⊓
        @_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} (D.quotCondition Q hQ).ι :=
  relative_openImmersion_closedImmersion_ι _ (D.isCutOutByPoints_quotCondition hQ hcut)

end QuotSituation

/-! ### The corresponding subfunctor of `Hilb_{X/B}` -/

section Hilbert

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)

/-- The object `(T, 𝒪_Z)` of `Coh_{X/B}` attached to a family `Z ⊆ X_T` classified by the
Hilbert functor: the object of its quotient `𝒪_{X_T} ⟶ 𝒪_Z` under Stacks 0D00 and Stacks 0DP6. -/
abbrev hilbertCohObject {T : BigFppfOver B S hS} (x : HilbertFamilyOver f T) :
    CoherentObject (structureSheafQuotSituation f hf).toCoherentSituation :=
  (quotFamilyOfHilbertFamilyOver f hf x).cohObject

variable (Q : CoherentObject (structureSheafQuotSituation f hf).toCoherentSituation → Prop)
  (hQ : ∀ {A' A : CoherentObject (structureSheafQuotSituation f hf).toCoherentSituation},
    CoherentHom A' A → Q A → Q A')

/-- **The subfunctor of `Hilb_{X/B}` corresponding to `Quot_{𝒪_X/X/B} ×_{Coh_{X/B}} Coh^Q_{X/B}`**
under the identification `Hilb_{X/B} = Quot_{𝒪_X/X/B}` of Stacks 0D00: the families `Z ⊆ X_T`
whose object `(T, 𝒪_Z)` of `Coh_{X/B}` satisfies `Q`. -/
def hilbertCondition : Subfunctor (hilbertPresheaf f) :=
  ((structureSheafQuotSituation f hf).quotCondition Q hQ).preimage
    (hilbertPresheafIsoQuotSitePresheaf f hf).hom

/-- A family lies in the subfunctor exactly when its object of `Coh_{X/B}` satisfies `Q`. -/
theorem mem_hilbertCondition_iff {T : (BigFppfOver B S hS)ᵒᵖ} (x : (hilbertPresheaf f).obj T) :
    x ∈ (hilbertCondition f hf Q hQ).obj T ↔ Q (hilbertCohObject f hf x) :=
  Iff.rfl

variable {Q}

/-- **The subfunctor of `Hilb_{X/B}` cut out by a flat closed condition on `Coh_{X/B}` is a flat
closed subfunctor**: its inclusion is representable by flat closed immersions. -/
theorem relative_closedImmersion_flat_hilbertCondition_ι
    (hcut : CoherentSituation.IsCutOutOnTestSchemes
      (structureSheafQuotSituation f hf).toCoherentSituation Q
      fun _ Z => IsClosed Z ∧ StableUnderGeneralization Z) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} ⊓ @Flat.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
        (hilbertCondition f hf Q hQ).ι :=
  relative_closedImmersion_flat_ι _
    (((structureSheafQuotSituation f hf).isCutOutByPoints_quotCondition hQ hcut).preimage _)

/-- **The subfunctor of `Hilb_{X/B}` cut out by an open and closed condition on `Coh_{X/B}` is an
open and closed subfunctor**: its inclusion is representable by morphisms which are open and
closed immersions. -/
theorem relative_openImmersion_closedImmersion_hilbertCondition_ι
    (hcut : CoherentSituation.IsCutOutOnTestSchemes
      (structureSheafQuotSituation f hf).toCoherentSituation Q fun _ Z => IsClopen Z) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} ⊓
        @_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
        (hilbertCondition f hf Q hQ).ι :=
  relative_openImmersion_closedImmersion_ι _
    (((structureSheafQuotSituation f hf).isCutOutByPoints_quotCondition hQ hcut).preimage _)

/-- **Transport to models.**  If the inclusion of a subfunctor `G` of the Hilbert presheaf is
representable by morphisms of schemes with a property `P` respecting isomorphisms, then so is the
morphism of models it induces: for a model `M` of the Hilbert presheaf in `Type u` and a presheaf
`F` of `Type u` whose universe lift is identified with `G`, the induced morphism `F ⟶ M` has
`P` after every represented base change.  This is the form in which properties of morphisms of
algebraic spaces (Stacks 02YU) are stated for the Hilbert functor. -/
theorem HilbertPresheafModel.presheaf_mapFrom_of_relative_ι (M : HilbertPresheafModel f)
    {P : MorphismProperty (BigFppfOver B S hS)} [P.RespectsIso] {G : Subfunctor (hilbertPresheaf f)}
    (hG : P.relative uliftYoneda.{u + 1} G.ι) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : F ⋙ uliftFunctor.{u + 1, u} ≅ G.toFunctor) :
    P.presheaf (M.mapFrom (e.hom ≫ G.ι)) :=
  M.relative_mapFrom P _ (MorphismProperty.RespectsIso.precomp _ e.hom G.ι hG)

end Hilbert

end AlgebraicGeometry.Space

end
