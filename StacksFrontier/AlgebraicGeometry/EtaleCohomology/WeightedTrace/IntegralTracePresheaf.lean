module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.FibreIntegralBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.FiniteSupportChart
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FibreSumOpenShrink
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.ConstantSheafAbelian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The integral trace map on the finite-support direct image of the constant sheaf

Let `f : X ⟶ Y` be a morphism of a big étale site which is locally of finite type and locally
quasi-finite as a morphism of schemes, and let `w` be a weighting of it. Let `Z` be the constant
abelian sheaf with value `ULift ℤ` on the small étale site of `X`, realised as the sheaf of
locally constant `ULift ℤ`-valued maps. This file builds the morphism of abelian presheaves
`f_{p!}Z ⟶ Z` of Stacks 0GKG by integrating a finite-support section against `w`, and sheafifies
it to a morphism `f_!Z ⟶ Z` of abelian sheaves.

A section of `f_{p!}Z` over an étale `Y`-scheme `V` is, by the colimit formula of Stacks 0F6M, a
section of `Z` over the canonical open of a support `E` of `X_V` finite over `V`, subject to the
condition that it vanishes off `E`. Such a section is an integer-valued locally constant function
with support finite over `V`, so the fibre integral of
`AlgebraicGeometry.fibreIntegral` applies to it; the resulting function on `V` is locally
constant, additive in the section, unchanged when `E` is enlarged, and compatible with base
change of `V`. Those four facts are exactly a cocone on the colimit diagram, natural in `V`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.TraceCoeff` — the coefficient group `ULift ℤ` in the universe in
  which this library computes étale cohomology, and
  `AlgebraicGeometry.SmallEtale.asLocallyConstant` a section of the constant abelian sheaf read
  as a locally constant function.
* `AlgebraicGeometry.SmallEtale.integralTraceSections` — the group `H_E(Z)` of sections of the
  constant sheaf supported on a finite support `E`, and
  `AlgebraicGeometry.SmallEtale.integralTraceSectionFun` the integer-valued function on the
  canonical open of `E` underlying such a section.
* `AlgebraicGeometry.SmallEtale.integralTraceGenerator` — the fibre integral of such a section,
  as a locally constant function on `V`, and
  `AlgebraicGeometry.SmallEtale.integralTraceStageHom` the additive map it defines out of
  `H_E(Z)`.
* `AlgebraicGeometry.SmallEtale.integralTraceCocone` — the cocone on the diagram of supported
  sections whose legs are those additive maps.
* `AlgebraicGeometry.SmallEtale.integralTracePresheafApp` and
  `AlgebraicGeometry.SmallEtale.integralTracePresheafMap` — **the morphism of presheaves
  `f_{p!}Z ⟶ Z`**, over one test object and as a whole.
* `AlgebraicGeometry.SmallEtale.integralTrace` — **the morphism of sheaves `Tr : f_!Z ⟶ Z`**,
  obtained from it by sheafification.

## Main results

* `AlgebraicGeometry.SmallEtale.supportSection_locallyConstantSheafAb` — the support of a
  section of the constant abelian sheaf is its nonvanishing locus, with
  `AlgebraicGeometry.SmallEtale.mem_preimage_of_supportedSections_apply_ne_zero` the consequence
  used to feed the fibre integral.
* `AlgebraicGeometry.SmallEtale.integralTraceGenerator_apply` and
  `AlgebraicGeometry.SmallEtale.integralTraceGenerator_add` — the value of the generator and its
  additivity.
* `AlgebraicGeometry.SmallEtale.fibreIntegral_shrink` and
  `AlgebraicGeometry.SmallEtale.integralTraceStageHom_compatible` — the fibre integral does not
  change when the support is enlarged, which is the cocone condition.
* `AlgebraicGeometry.SmallEtale.isPullback_of_opens_preimage` — a cartesian square stays
  cartesian after restricting its horizontal maps to an open and its preimage.
* `AlgebraicGeometry.SmallEtale.integralTraceGenerator_baseChange`,
  `AlgebraicGeometry.SmallEtale.integralTraceStageHom_baseChange` and
  `AlgebraicGeometry.SmallEtale.integralTracePresheafApp_naturality` — the fibre integral is
  compatible with base change of the étale test object, which is naturality in `V`.
* `AlgebraicGeometry.SmallEtale.colimit_ι_eqToHom_desc`,
  `AlgebraicGeometry.SmallEtale.colimit_ι_eqToHom_desc_comp` and
  `AlgebraicGeometry.SmallEtale.colimit_ι_eqToHom_map_desc` — the three pieces of colimit
  bookkeeping needed to read a map out of a value identified with a colimit on a generator.
* `AlgebraicGeometry.SmallEtale.integralTracePresheafMap_ι` — **the value of the presheaf
  morphism on a colimit generator**, which is what every statement about the trace map is proved
  from.
* `AlgebraicGeometry.SmallEtale.toSheafify_integralTrace` — the sheafified trace map restricts
  along the sheafification unit to the morphism of presheaves.

## Implementation notes

The coefficient group is `ULift ℤ` rather than `ℤ` because the constant sheaf of this library
takes its value in the universe `max (u + 1) v` in which étale cohomology is computed, whereas
the fibre integral is an honest integer. The two are related by `ULift.up` and `ULift.down`,
which are additive, so the only cost is that every computation lemma carries an `ULift.up`.

A section of the constant sheaf over an object of the site is *definitionally* a locally
constant function, but a type ascription does not make the function coercion available: the
ascription produces no cast, so the elaborated term keeps the type of a section of a presheaf of
abelian groups. `asLocallyConstant` is the one-line abbreviation whose declared type carries the
function coercion, and every computation below goes through it.

Naturality in the test object is the base-change statement
`AlgebraicGeometry.fibreIntegral_comp_of_isPullback`, which needs the square relating the
canonical open of a support to the canonical open of its inverse image to be cartesian. That
square is obtained from the cartesian square of the base changes of `f` by restricting to an
open and its preimage, which is `isPullback_of_opens_preimage`; its hypothesis that the one open
is the preimage of the other is the equality `coborder (k⁻¹ E) = k⁻¹ (coborder E)`, which holds
because the base-change morphism is étale, hence open, so that it commutes with closures of
preimages.

The cocone condition is the other direction: enlarging the support *shrinks* the canonical open
`coborder E`, by `AlgebraicGeometry.SmallEtale.supportOpen_antitone`, and a section supported on
`E` vanishes off `E`, which lies in both opens. So the weighted fibre sum computing the integral
is unchanged, by
`AlgebraicGeometry.separableDegreeWeightedFiberSum_comp_isOpenImmersion_of_support_subset`.

Every composite appearing here is kept in the `baseChangeChartProj` and
`finiteSupportChartProj` spellings of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/WeightedTrace/FiniteSupportChart.lean`; writing
the open immersion followed by the projection out by hand produces a term which elaborates but
which instance synthesis cannot decompose.

## References

* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

/-- The coefficient group of the integral trace map: the integers, lifted to the universe in
which this library computes étale cohomology. -/
public abbrev TraceCoeff : Type (max (u + 1) v) := ULift.{max (u + 1) v} ℤ

/-! ### Generators of a value identified with a colimit -/

/-- The map out of a colimit, read on a colimit generator through an identification of the
colimit with another object. -/
public theorem colimit_ι_eqToHom_desc {J : Type*} [Category J] {A : Type*} [Category A]
    (D : J ⥤ A) [HasColimit D] {T : A} (hT : T = colimit D) (c : Cocone D) (j : J) :
    colimit.ι D j ≫ eqToHom hT.symm ≫ eqToHom hT ≫ colimit.desc D c = c.ι.app j := by
  rw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact colimit.ι_desc c j

/-- The map out of a colimit followed by a further morphism, read on a colimit generator through
an identification of the colimit with another object. -/
public theorem colimit_ι_eqToHom_desc_comp {J : Type*} [Category J] {A : Type*} [Category A]
    (D : J ⥤ A) [HasColimit D] {T : A} (hT : T = colimit D) (c : Cocone D) (j : J) {R : A}
    (q : c.pt ⟶ R) :
    colimit.ι D j ≫ eqToHom hT.symm ≫ (eqToHom hT ≫ colimit.desc D c) ≫ q =
      c.ι.app j ≫ q := by
  rw [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, ← Category.assoc,
    colimit.ι_desc]

/-- A morphism between two objects identified with colimits, followed by a map out of the second
colimit, read on a generator whose image is known to be a generator. -/
public theorem colimit_ι_eqToHom_map_desc {J J' : Type*} [Category J] [Category J']
    {A : Type*} [Category A] (D : J ⥤ A) (D' : J' ⥤ A) [HasColimit D] [HasColimit D']
    {T T' : A} (hT : T = colimit D) (hT' : T' = colimit D') (p : T ⟶ T') (c' : Cocone D')
    (j : J) (j' : J') (n : D.obj j ⟶ D'.obj j')
    (hs : colimit.ι D j ≫ eqToHom hT.symm ≫ p ≫ eqToHom hT' = n ≫ colimit.ι D' j') :
    colimit.ι D j ≫ eqToHom hT.symm ≫ p ≫ eqToHom hT' ≫ colimit.desc D' c' =
      n ≫ c'.ι.app j' := by
  rw [reassoc_of% hs, colimit.ι_desc]

/-! ### The support of a section of the constant abelian sheaf -/

section ConstantSheaf

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (A : Type (max (u + 1) v)) [AddCommGroup A]

/-- A section of the constant abelian sheaf over an object of the small étale site, read as a
locally constant function on that object. -/
public abbrev asLocallyConstant (W : SmallEtale B S hS)
    (a : ↥((locallyConstantSheafAb.{u, v} B S hS A).obj.obj (op W))) :
    LocallyConstant ((SmallEtale.toScheme B S hS).obj W) A := a

/-- Restriction in the constant abelian sheaf is precomposition of functions. -/
public theorem locallyConstantSheafAb_map_apply {W W' : SmallEtale B S hS} (g : W' ⟶ W)
    (a : ↥((locallyConstantSheafAb.{u, v} B S hS A).obj.obj (op W)))
    (y : (SmallEtale.toScheme B S hS).obj W') :
    asLocallyConstant.{u, v} B S hS A W'
        ((locallyConstantSheafAb.{u, v} B S hS A).obj.map g.op a) y =
      asLocallyConstant.{u, v} B S hS A W a (((SmallEtale.toScheme B S hS).map g).base y) := rfl

/-- A locally constant section restricts to zero along an arrow of the small étale site exactly
when it vanishes at every point of the image of that arrow. -/
public theorem locallyConstantSheafAb_map_eq_zero_iff {W W' : SmallEtale B S hS} (g : W' ⟶ W)
    (a : LocallyConstant ((SmallEtale.toScheme B S hS).obj W) A) :
    (locallyConstantSheafAb.{u, v} B S hS A).obj.map g.op a = 0 ↔
      ∀ y, a (((SmallEtale.toScheme B S hS).map g).base y) = 0 := by
  constructor
  · intro h y
    exact congrArg
      (fun t : LocallyConstant ((SmallEtale.toScheme B S hS).obj W') A => t y) h
  · intro h
    exact LocallyConstant.ext h

/-- The maximal zero open of a section of the constant abelian sheaf is its vanishing locus:
that locus is open because the section is locally constant, and the section restricts to zero on
it, while on any open along which the section dies it vanishes pointwise. -/
public theorem zeroOpen_locallyConstantSheafAb (W : SmallEtale B S hS)
    (a : LocallyConstant ((SmallEtale.toScheme B S hS).obj W) A) :
    ((zeroOpen B S hS (locallyConstantSheafAb.{u, v} B S hS A) W a :
        ((SmallEtale.toScheme B S hS).obj W).Opens) :
      Set ((SmallEtale.toScheme B S hS).obj W)) = {x | a x = 0} := by
  have hopen : IsOpen {x : (SmallEtale.toScheme B S hS).obj W | a x = 0} :=
    a.isLocallyConstant.isOpen_fiber 0
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    have hx' : x ∈
        sSup {W₁ | IsZeroOpen B S hS (locallyConstantSheafAb.{u, v} B S hS A) W a W₁} := hx
    obtain ⟨W₁, hW₁, hxW₁⟩ := TopologicalSpace.Opens.mem_sSup.mp hx'
    obtain ⟨V, g, hg, hrange, hzero⟩ := hW₁
    have hxW₁' : x ∈ (W₁ : Set ((SmallEtale.toScheme B S hS).obj W)) := hxW₁
    rw [hrange] at hxW₁'
    obtain ⟨y, rfl⟩ := hxW₁'
    exact (locallyConstantSheafAb_map_eq_zero_iff.{u, v} B S hS A g a).1 hzero y
  · intro x hx
    have hmem : (⟨_, hopen⟩ : ((SmallEtale.toScheme B S hS).obj W).Opens) ∈
        {W₁ | IsZeroOpen B S hS (locallyConstantSheafAb.{u, v} B S hS A) W a W₁} := by
      refine ⟨openObject B S hS W ⟨_, hopen⟩, openObjectι B S hS W ⟨_, hopen⟩, inferInstance,
        (openObjectι_range B S hS W ⟨_, hopen⟩).symm, ?_⟩
      refine (locallyConstantSheafAb_map_eq_zero_iff.{u, v} B S hS A _ a).2 fun y => ?_
      rw [openObjectι_map]
      exact y.2
    have hle : (⟨_, hopen⟩ : ((SmallEtale.toScheme B S hS).obj W).Opens) ≤
        zeroOpen B S hS (locallyConstantSheafAb.{u, v} B S hS A) W a := le_sSup hmem
    exact hle hx

/-- **The support of a section of the constant abelian sheaf is its nonvanishing locus.** -/
public theorem supportSection_locallyConstantSheafAb (W : SmallEtale B S hS)
    (a : LocallyConstant ((SmallEtale.toScheme B S hS).obj W) A) :
    supportSection B S hS (locallyConstantSheafAb.{u, v} B S hS A) W a = {x | a x ≠ 0} := by
  show ((zeroOpen B S hS (locallyConstantSheafAb.{u, v} B S hS A) W a :
      ((SmallEtale.toScheme B S hS).obj W).Opens) :
    Set ((SmallEtale.toScheme B S hS).obj W))ᶜ = {x | a x ≠ 0}
  rw [zeroOpen_locallyConstantSheafAb.{u, v} B S hS A W a]
  rfl

end ConstantSheaf

/-! ### Sections of the constant sheaf supported on a finite support -/

section Sections

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- The group `H_E(Z)` of sections of the constant abelian sheaf on the small étale site of `X`
supported on a support `E` of `X_V` finite over `V`. -/
public abbrev integralTraceSections (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) :=
  supportedSections B X.obj X.property
    (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v})
    (baseChange B f V) E.1 (finiteSupport_isLocallyClosed B f V E)

/-- A section of the constant sheaf supported on a finite support vanishes off that support. -/
public theorem mem_preimage_of_supportedSections_apply_ne_zero
    (V : SmallEtale B Y.obj Y.property) (E : FiniteSupport B f V)
    (a : integralTraceSections.{u, v} B f V E)
    (x : (finiteSupportOpen B f V E).toScheme)
    (hx : asLocallyConstant.{u, v} B X.obj X.property TraceCoeff.{u, v}
      (finiteSupportOpenObject B f V E) a.val x ≠ 0) :
    x ∈ (finiteSupportOpen B f V E).ι.base ⁻¹' E.1 := by
  have heq := supportSection_locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}
    (finiteSupportOpenObject B f V E)
    (asLocallyConstant.{u, v} B X.obj X.property TraceCoeff.{u, v}
      (finiteSupportOpenObject B f V E) a.val)
  have hsub : supportSection B X.obj X.property
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v})
      (finiteSupportOpenObject B f V E) a.val ⊆
    (finiteSupportOpen B f V E).ι.base ⁻¹' E.1 := a.property
  exact hsub (heq.ge hx)

/-- The integer-valued function on the canonical open of a finite support underlying a section
of the constant sheaf supported on it. -/
public def integralTraceSectionFun (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) (a : integralTraceSections.{u, v} B f V E) :
    (finiteSupportOpen B f V E).toScheme → ℤ :=
  fun x => (asLocallyConstant.{u, v} B X.obj X.property TraceCoeff.{u, v}
    (finiteSupportOpenObject B f V E) a.val x).down

/-- The function underlying a supported section of the constant sheaf is the section itself,
read through `ULift.down`. -/
public theorem integralTraceSectionFun_apply (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) (a : integralTraceSections.{u, v} B f V E)
    (x : (finiteSupportOpen B f V E).toScheme) :
    integralTraceSectionFun.{u, v} B f V E a x =
      (asLocallyConstant.{u, v} B X.obj X.property TraceCoeff.{u, v}
        (finiteSupportOpenObject B f V E) a.val x).down := rfl

/-- The function of a supported section whose underlying section restricts along a morphism of
canonical opens is the function of the original section, read along that morphism. -/
private theorem integralTraceSectionFun_comp_of_val_eq {V V' : SmallEtale B Y.obj Y.property}
    {E : FiniteSupport B f V} {E' : FiniteSupport B f V'}
    (a : integralTraceSections.{u, v} B f V E) (a' : integralTraceSections.{u, v} B f V' E')
    (m : finiteSupportOpenObject B f V' E' ⟶ finiteSupportOpenObject B f V E)
    (h : a'.val = (locallyConstantSheafAb.{u, v} B X.obj X.property
      TraceCoeff.{u, v}).obj.map m.op a.val) (z : (finiteSupportOpen B f V' E').toScheme) :
    integralTraceSectionFun.{u, v} B f V' E' a' z =
      integralTraceSectionFun.{u, v} B f V E a
        (((SmallEtale.toScheme B X.obj X.property).map m).base z) := by
  rw [integralTraceSectionFun_apply, integralTraceSectionFun_apply, h]
  rfl

/-- The function underlying a supported section of the constant sheaf is locally constant. -/
public theorem isLocallyConstant_integralTraceSectionFun (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) (a : integralTraceSections.{u, v} B f V E) :
    IsLocallyConstant (integralTraceSectionFun.{u, v} B f V E a) :=
  (asLocallyConstant.{u, v} B X.obj X.property TraceCoeff.{u, v}
    (finiteSupportOpenObject B f V E) a.val).isLocallyConstant.comp ULift.down

/-- The function underlying a supported section of the constant sheaf vanishes off the
support. -/
public theorem integralTraceSectionFun_support (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) (a : integralTraceSections.{u, v} B f V E)
    (x : (finiteSupportOpen B f V E).toScheme)
    (hx : integralTraceSectionFun.{u, v} B f V E a x ≠ 0) :
    x ∈ (finiteSupportOpen B f V E).ι.base ⁻¹' E.1 := by
  refine mem_preimage_of_supportedSections_apply_ne_zero.{u, v} B f V E a x fun h0 => hx ?_
  rw [integralTraceSectionFun_apply.{u, v} B f V E a x]
  exact congrArg ULift.down h0

/-- The function underlying a supported section of the constant sheaf is additive in the
section. -/
public theorem integralTraceSectionFun_add (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) (a b : integralTraceSections.{u, v} B f V E) :
    integralTraceSectionFun.{u, v} B f V E (a + b) =
      fun x => integralTraceSectionFun.{u, v} B f V E a x +
        integralTraceSectionFun.{u, v} B f V E b x := rfl

end Sections

/-! ### The fibre integral of a supported section -/

section Generator

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  {w : X.obj → ℤ} (hw : IsWeighting (B.inclusion.map f) w)

/-- Two fibre integrals of equal sections agree. The section of a fibre integral is an implicit
argument determined by the proof that it is locally constant, so this is the congruence lemma
that proof has to be transported along. -/
public theorem fibreIntegral_congr_section {U Vs Xs : Scheme.{u}} (hh : U ⟶ Xs) (π : U ⟶ Vs)
    (ω : Xs → ℤ) {s₁ s₂ : U → ℤ} (h₁ : IsLocallyConstant s₁) (h₂ : IsLocallyConstant s₂)
    (hs : s₁ = s₂) : fibreIntegral hh π ω h₁ = fibreIntegral hh π ω h₂ := by
  subst hs
  rfl

/-- The fibre integral of a section of the constant sheaf supported on a finite support, as a
locally constant function on the étale test object. This is the value of the trace map on a
colimit generator of Stacks 0F6M. -/
public def integralTraceGenerator (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) (a : integralTraceSections.{u, v} B f V E) :
    LocallyConstant (B.inclusion.obj V.obj.left) TraceCoeff.{u, v} where
  toFun y := ULift.up (fibreIntegral (finiteSupportChartToSource B f V E)
    (finiteSupportChartProj B f V E) w
    (isLocallyConstant_integralTraceSectionFun.{u, v} B f V E a) y)
  isLocallyConstant :=
    (isLocallyConstant_fibreIntegral_finiteSupportChart B f V E hw
      (isLocallyConstant_integralTraceSectionFun.{u, v} B f V E a)
      (integralTraceSectionFun_support.{u, v} B f V E a)).comp ULift.up

/-- The value of the fibre integral of a supported section at a point of the test object. -/
public theorem integralTraceGenerator_apply (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) (a : integralTraceSections.{u, v} B f V E)
    (y : B.inclusion.obj V.obj.left) :
    integralTraceGenerator.{u, v} B f hw V E a y =
      ULift.up (fibreIntegral (finiteSupportChartToSource B f V E)
        (finiteSupportChartProj B f V E) w
        (isLocallyConstant_integralTraceSectionFun.{u, v} B f V E a) y) := rfl

/-- The fibre integral of a supported section is additive in the section. -/
public theorem integralTraceGenerator_add (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) (a b : integralTraceSections.{u, v} B f V E) :
    integralTraceGenerator.{u, v} B f hw V E (a + b) =
      integralTraceGenerator.{u, v} B f hw V E a +
        integralTraceGenerator.{u, v} B f hw V E b := by
  refine LocallyConstant.ext fun y => ?_
  have hadd : IsLocallyConstant (fun x => integralTraceSectionFun.{u, v} B f V E a x +
      integralTraceSectionFun.{u, v} B f V E b x) :=
    ((isLocallyConstant_integralTraceSectionFun.{u, v} B f V E a).prodMk
      (isLocallyConstant_integralTraceSectionFun.{u, v} B f V E b)).comp
        (fun p : ℤ × ℤ => p.1 + p.2)
  have h := fibreIntegral_add_finiteSupportChart B f V E w
    (isLocallyConstant_integralTraceSectionFun.{u, v} B f V E a)
    (isLocallyConstant_integralTraceSectionFun.{u, v} B f V E b) hadd
    (integralTraceSectionFun_support.{u, v} B f V E a)
    (integralTraceSectionFun_support.{u, v} B f V E b)
  have h2 := fibreIntegral_congr_section (finiteSupportChartToSource B f V E)
    (finiteSupportChartProj B f V E) w
    (isLocallyConstant_integralTraceSectionFun.{u, v} B f V E (a + b)) hadd
    (integralTraceSectionFun_add.{u, v} B f V E a b)
  exact congrArg ULift.up ((congrFun h2 y).trans (congrFun h y))

/-- The additive map out of the sections supported on a finite support given by the fibre
integral: the leg of the cocone defining the trace map at that support. -/
public def integralTraceStageHom (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) :
    AddCommGrpCat.of (integralTraceSections.{u, v} B f V E) ⟶
      (locallyConstantMapsAbSmallEtale.{u, v} B Y.obj Y.property TraceCoeff.{u, v}).obj (op V) :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk' (integralTraceGenerator.{u, v} B f hw V E)
    (integralTraceGenerator_add.{u, v} B f hw V E))

/-- The additive map out of a stage is the fibre integral of the section. -/
public theorem integralTraceStageHom_apply (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) (a : integralTraceSections.{u, v} B f V E) :
    (integralTraceStageHom.{u, v} B f hw V E).hom a =
      integralTraceGenerator.{u, v} B f hw V E a := rfl

end Generator

/-! ### Enlarging the support -/

section Shrink

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  {w : X.obj → ℤ} (hw : IsWeighting (B.inclusion.map f) w)

/-- **The fibre integral is unchanged when the support is enlarged.** Enlarging the support
shrinks the canonical open it is computed on, and the section vanishes off the smaller support,
which lies in both opens; so the weighted fibre sum computing the integral does not change. -/
public theorem fibreIntegral_shrink (V : SmallEtale B Y.obj Y.property)
    (E E' : FiniteSupport B f V)
    (hle : finiteSupportOpen B f V E' ≤ finiteSupportOpen B f V E) (hEE' : E.1 ⊆ E'.1)
    {s : (finiteSupportOpen B f V E).toScheme → ℤ} (hs : IsLocallyConstant s)
    (hsupp : ∀ x, s x ≠ 0 → x ∈ (finiteSupportOpen B f V E).ι.base ⁻¹' E.1)
    {s' : (finiteSupportOpen B f V E').toScheme → ℤ} (hs' : IsLocallyConstant s')
    (hss' : ∀ y, s' y = s ((Scheme.homOfLE _ hle).base y)) :
    fibreIntegral (finiteSupportChartToSource B f V E')
        (finiteSupportChartProj B f V E') w hs' =
      fibreIntegral (finiteSupportChartToSource B f V E)
        (finiteSupportChartProj B f V E) w hs := by
  have hι : Scheme.homOfLE _ hle ≫ (finiteSupportOpen B f V E).ι =
      (finiteSupportOpen B f V E').ι := Scheme.homOfLE_ι _ hle
  have hpt : ∀ y : (finiteSupportOpen B f V E').toScheme,
      (finiteSupportOpen B f V E).ι.base ((Scheme.homOfLE _ hle).base y) =
        (finiteSupportOpen B f V E').ι.base y := fun y => Scheme.homOfLE_apply hle y
  have hsrccomp : Scheme.homOfLE _ hle ≫ finiteSupportChartToSource B f V E =
      finiteSupportChartToSource B f V E' := (reassoc_of% hι) (baseChangeChartToSource B f V)
  have hprojcomp : Scheme.homOfLE _ hle ≫ finiteSupportChartProj B f V E =
      finiteSupportChartProj B f V E' := (reassoc_of% hι) (baseChangeChartProj B f V)
  have hsrcpt : ∀ y : (finiteSupportOpen B f V E').toScheme,
      finiteSupportChartToSource B f V E' y =
        finiteSupportChartToSource B f V E ((Scheme.homOfLE _ hle).base y) := by
    intro y
    rw [← hsrccomp]
    rfl
  have hsupp' : ∀ y, s' y ≠ 0 → y ∈ (finiteSupportOpen B f V E').ι.base ⁻¹' E'.1 := by
    intro y hy
    have hy' : s ((Scheme.homOfLE _ hle).base y) ≠ 0 := by
      rwa [← hss' y]
    show (finiteSupportOpen B f V E').ι.base y ∈ E'.1
    rw [← hpt y]
    exact hEE' (hsupp _ hy')
  have hrange : ∀ x : (finiteSupportOpen B f V E).toScheme,
      s x * w (finiteSupportChartToSource B f V E x) ≠ 0 →
        x ∈ Set.range (Scheme.homOfLE _ hle).base := by
    intro x hx
    have hs0 : s x ≠ 0 := fun h0 => hx (by rw [h0, zero_mul])
    have hmem : (finiteSupportOpen B f V E).ι.base x ∈
        (finiteSupportOpen B f V E' :
          Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V))) :=
      subset_supportOpen B X.obj X.property (baseChange B f V) E'.1
        (finiteSupport_isLocallyClosed B f V E') (hEE' (hsupp x hs0))
    exact ⟨⟨_, hmem⟩, Subtype.ext (Scheme.homOfLE_apply hle _)⟩
  have hshrink := separableDegreeWeightedFiberSum_comp_isOpenImmersion_of_support_subset
    (Scheme.homOfLE _ hle) (finiteSupportChartProj B f V E)
    (fun x => s x * w (finiteSupportChartToSource B f V E x)) hrange
  rw [hprojcomp] at hshrink
  rw [fibreIntegral_eq_separableDegreeWeightedFiberSum_finiteSupportChart B f V E' w hs' hsupp',
    fibreIntegral_eq_separableDegreeWeightedFiberSum_finiteSupportChart B f V E w hs hsupp,
    ← hshrink]
  congr 1
  funext y
  rw [hss' y]
  exact congrArg (fun z => s ((Scheme.homOfLE _ hle).base y) * w z) (hsrcpt y)

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The restriction of a supported section of the constant sheaf to the canonical open of a
larger support is the section read along the inclusion of the two opens. -/
public theorem integralTraceSectionFun_diagramMap (V : SmallEtale B Y.obj Y.property)
    {E E' : FiniteSupport B f V} (h : E ⟶ E')
    (a : integralTraceSections.{u, v} B f V E)
    (z : (finiteSupportOpen B f V E').toScheme) :
    integralTraceSectionFun.{u, v} B f V E'
        (((finiteSupportDiagram B f
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V).map h).hom a)
        z =
      integralTraceSectionFun.{u, v} B f V E a
        ((Scheme.homOfLE _ (supportOpen_antitone B X.obj X.property (baseChange B f V) E.1 E'.1
          (finiteSupport_isLocallyClosed B f V E) (finiteSupport_isLocallyClosed B f V E')
          (leOfHom h) (finiteSupport_closedWithin B f V E E' (leOfHom h)))).base z) := by
  have := integralTraceSectionFun_comp_of_val_eq.{u, v} B f a _
    (openObjectHomOfLE B X.obj X.property (baseChange B f V)
      (supportOpen_antitone B X.obj X.property (baseChange B f V) E.1 E'.1
        (finiteSupport_isLocallyClosed B f V E) (finiteSupport_isLocallyClosed B f V E')
        (leOfHom h) (finiteSupport_closedWithin B f V E E' (leOfHom h))))
    (supportedSectionsMap_apply B X.obj X.property
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v})
      (baseChange B f V) E.1 E'.1 (finiteSupport_isLocallyClosed B f V E)
      (finiteSupport_isLocallyClosed B f V E') (leOfHom h)
      (finiteSupport_closedWithin B f V E E' (leOfHom h)) a) z
  rwa [openObjectHomOfLE_map] at this

/-- **The cocone condition.** The fibre integral of a supported section does not change when the
support is enlarged. -/
public theorem integralTraceStageHom_compatible (V : SmallEtale B Y.obj Y.property)
    {E E' : FiniteSupport B f V} (h : E ⟶ E') :
    (finiteSupportDiagram B f
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V).map h ≫
        integralTraceStageHom.{u, v} B f hw V E' =
      integralTraceStageHom.{u, v} B f hw V E := by
  apply AddCommGrpCat.hom_ext
  ext a
  refine LocallyConstant.ext fun y => ?_
  have key := fibreIntegral_shrink (w := w) B f V E E'
    (supportOpen_antitone B X.obj X.property (baseChange B f V) E.1 E'.1
      (finiteSupport_isLocallyClosed B f V E) (finiteSupport_isLocallyClosed B f V E')
      (leOfHom h) (finiteSupport_closedWithin B f V E E' (leOfHom h)))
    (leOfHom h) (isLocallyConstant_integralTraceSectionFun.{u, v} B f V E a)
    (integralTraceSectionFun_support.{u, v} B f V E a)
    (isLocallyConstant_integralTraceSectionFun.{u, v} B f V E' _)
    (integralTraceSectionFun_diagramMap.{u, v} B f V h a)
  exact congrArg ULift.up (congrFun key y)

/-- The cocone on the diagram of supported sections whose leg at a finite support is the fibre
integral out of that stage. -/
public def integralTraceCocone (V : SmallEtale B Y.obj Y.property) :
    Cocone (finiteSupportDiagram B f
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V) where
  pt := (locallyConstantMapsAbSmallEtale.{u, v} B Y.obj Y.property TraceCoeff.{u, v}).obj (op V)
  ι :=
    { app := fun E => integralTraceStageHom.{u, v} B f hw V E
      naturality := by
        intro E E' h
        exact integralTraceStageHom_compatible.{u, v} B f hw V h }

end Shrink

/-! ### Base change of the test object -/

section BaseChange

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- **A cartesian square restricted to an open and its preimage is cartesian.** The one piece of
geometry in the naturality of the trace map: the canonical open of a support and the canonical
open of its inverse image form a cartesian square over the square of base changes. -/
public theorem isPullback_of_opens_preimage {Xv Xv' Vs Vs' : Scheme.{u}} {k : Xv' ⟶ Xv}
    {π : Xv ⟶ Vs} {π' : Xv' ⟶ Vs'} {g : Vs' ⟶ Vs} (sq : IsPullback k π' π g)
    (U : Xv.Opens) (U' : Xv'.Opens) (hU : (U' : Set Xv') = k.base ⁻¹' (U : Set Xv))
    (m : U'.toScheme ⟶ U.toScheme) (hm : m ≫ U.ι = U'.ι ≫ k) :
    IsPullback m (U'.ι ≫ π') (U.ι ≫ π) g := by
  obtain rfl : U' = k ⁻¹ᵁ U := TopologicalSpace.Opens.ext hU
  have hmeq : m = k ∣_ U := by
    rw [← cancel_mono U.ι, hm, morphismRestrict_ι]
  rw [hmeq]
  exact isPullback_morphismRestrict_comp sq U

/-- The base change of `X_V` along a morphism of the small étale site of `Y` is the fibre product
of `X_V` and `V'` over `V`. -/
public theorem isPullback_baseChangeChartProj_map {V V' : SmallEtale B Y.obj Y.property}
    (g : V' ⟶ V) :
    IsPullback ((SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map g))
      (baseChangeChartProj B f V') (baseChangeChartProj B f V)
      ((SmallEtale.toScheme B Y.obj Y.property).map g) :=
  (CategoryTheory.baseChange_square
    ((SmallEtale.inclusion B Y.obj Y.property).map g).left V.obj.hom V'.obj.hom f
    (Over.w ((SmallEtale.inclusion B Y.obj Y.property).map g))).map B.inclusion

/-- The base change morphism of the small étale site of `X` commutes with the structure maps to
`X`. -/
public theorem baseChangeChartToSource_comp {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V) :
    (SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map g) ≫
        baseChangeChartToSource B f V =
      baseChangeChartToSource B f V' :=
  SmallEtale.toScheme_map_comp B X.obj X.property ((smallEtaleBaseChange B f).map g)

/-- **The canonical open of an inverse-image support is the inverse image of the canonical
open.** The base change morphism is étale, hence open, so it commutes with closures of inverse
images, and the canonical open is the complement of `closure E \ E`. -/
public theorem finiteSupportOpen_preimage_eq {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V)
    (E : FiniteSupport B f V) (E' : FiniteSupport B f V')
    (hE' : E'.1 = ((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map g)).base ⁻¹' E.1) :
    ((finiteSupportOpen B f V' E' :
        ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V')).Opens) :
      Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V'))) =
      ((SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map g)).base ⁻¹'
        ((finiteSupportOpen B f V E :
            ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V)).Opens) :
          Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V))) := by
  have hopen : IsOpenMap ((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map g)).base :=
    ((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map g)).isOpenMap
  show (closure E'.1 \ E'.1)ᶜ =
    ((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map g)).base ⁻¹' (closure E.1 \ E.1)ᶜ
  rw [hE', Set.preimage_compl, Set.preimage_diff,
    hopen.preimage_closure_eq_closure_preimage
      ((SmallEtale.toScheme B X.obj X.property).map
        ((smallEtaleBaseChange B f).map g)).continuous E.1]

end BaseChange

/-! ### The morphism of presheaves, and its sheafification -/

section Presheaf

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  {w : X.obj → ℤ} (hw : IsWeighting (B.inclusion.map f) w)

/-- **The fibre integral is compatible with base change of the étale test object.** This is the
naturality of the trace map in the test object, and it is the base-change statement
`AlgebraicGeometry.fibreIntegral_comp_of_isPullback` applied to the cartesian square of the
canonical opens. -/
public theorem integralTraceGenerator_baseChange {V V' : SmallEtale B Y.obj Y.property}
    (g : V' ⟶ V) (E : FiniteSupport B f V) (a : integralTraceSections.{u, v} B f V E)
    (y : B.inclusion.obj V'.obj.left) :
    integralTraceGenerator.{u, v} B f hw V'
        (finiteSupportBaseChange B f
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E).support
        ((finiteSupportBaseChange B f
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E).sectionsMap
          a) y =
      integralTraceGenerator.{u, v} B f hw V E a
        (((SmallEtale.toScheme B Y.obj Y.property).map g).base y) := by
  obtain ⟨Z, i, hi, hZ, hrange⟩ :=
    exists_isClosedImmersion_isFinite_range_finiteSupportChart B f V E
  have hi' : IsClosedImmersion i := hi
  have hsq := isPullback_of_opens_preimage (isPullback_baseChangeChartProj_map B f g)
    (finiteSupportOpen B f V E)
    (finiteSupportOpen B f V' (finiteSupportBaseChange B f
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E).support)
    (finiteSupportOpen_preimage_eq B f g E _ (finiteSupportBaseChange B f
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E).support_eq)
    ((SmallEtale.toScheme B X.obj X.property).map (finiteSupportBaseChange B f
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E).openMap)
    (finiteSupportBaseChange B f
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E).openMap_commutes
  have hsrccomp : (SmallEtale.toScheme B X.obj X.property).map (finiteSupportBaseChange B f
        (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E).openMap ≫
      finiteSupportChartToSource B f V E =
      finiteSupportChartToSource B f V' (finiteSupportBaseChange B f
        (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E).support := by
    exact ((reassoc_of% (finiteSupportBaseChange B f
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E).openMap_commutes)
        (baseChangeChartToSource B f V)).trans
      (congrArg (_ ≫ ·) (baseChangeChartToSource_comp B f g))
  have hsec : ∀ z, integralTraceSectionFun.{u, v} B f V'
      (finiteSupportBaseChange B f
        (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E).support
      ((finiteSupportBaseChange B f
        (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E).sectionsMap a)
      z =
    (integralTraceSectionFun.{u, v} B f V E a ∘
      ⇑((SmallEtale.toScheme B X.obj X.property).map (finiteSupportBaseChange B f
        (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v})
          g E).openMap)) z :=
    integralTraceSectionFun_comp_of_val_eq.{u, v} B f a _ _
      ((finiteSupportBaseChange B f
        (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E).sectionsMap_apply
        a)
  have hs2 : IsLocallyConstant (integralTraceSectionFun.{u, v} B f V E a ∘
      ⇑((SmallEtale.toScheme B X.obj X.property).map (finiteSupportBaseChange B f
        (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E).openMap)) :=
    (isLocallyConstant_integralTraceSectionFun.{u, v} B f V E a).comp_continuous
      ((SmallEtale.toScheme B X.obj X.property).map (finiteSupportBaseChange B f
        (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v})
          g E).openMap).continuous
  have key := fibreIntegral_comp_of_isPullback (h := finiteSupportChartToSource B f V E) hsq w
    (isLocallyConstant_integralTraceSectionFun.{u, v} B f V E a) hs2 i hZ
    (fun x hx => hrange.ge (integralTraceSectionFun_support.{u, v} B f V E a x hx))
  rw [hsrccomp] at key
  have hfin := fibreIntegral_congr_section
    (finiteSupportChartToSource B f V' (finiteSupportBaseChange B f
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E).support)
    (finiteSupportChartProj B f V' (finiteSupportBaseChange B f
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E).support)
    w (isLocallyConstant_integralTraceSectionFun.{u, v} B f V'
      (finiteSupportBaseChange B f
        (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E).support
      ((finiteSupportBaseChange B f
        (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E).sectionsMap a))
    hs2 (funext hsec)
  exact congrArg ULift.up ((congrFun hfin y).trans (congrFun key.symm y))

/-- The value of the trace map of presheaves over one étale test object: the map out of the
colimit of Stacks 0F6M induced by the fibre integral on each stage. -/
public def integralTracePresheafApp (V : SmallEtale B Y.obj Y.property) :
    ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).1.obj
        (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v})).obj (op V) ⟶
      (locallyConstantMapsAbSmallEtale.{u, v} B Y.obj Y.property TraceCoeff.{u, v}).obj (op V) :=
  eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
      (fun _ => inferInstance)).2.obj_eq _ V) ≫
    colimit.desc (finiteSupportDiagram B f
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V)
      (integralTraceCocone.{u, v} B f hw V)

/-- The value of the trace map over one test object, spelled out as the identification of the
value of `f_{p!}Z` with the colimit followed by the map out of the colimit. -/
public theorem integralTracePresheafApp_eq (V : SmallEtale B Y.obj Y.property) :
    integralTracePresheafApp.{u, v} B f hw V =
      eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
          (fun _ => inferInstance)).2.obj_eq _ V) ≫
        colimit.desc (finiteSupportDiagram B f
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V)
          (integralTraceCocone.{u, v} B f hw V) := rfl

/-- **The value of the trace map over one test object on a colimit generator.** -/
public theorem integralTracePresheafApp_ι (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) :
    colimit.ι (finiteSupportDiagram B f
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V) E ≫
        eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
          (fun _ => inferInstance)).2.obj_eq _ V).symm ≫
        integralTracePresheafApp.{u, v} B f hw V =
      integralTraceStageHom.{u, v} B f hw V E :=
  colimit_ι_eqToHom_desc (finiteSupportDiagram B f
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V)
    ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).2.obj_eq _ V)
    (integralTraceCocone.{u, v} B f hw V) E

/-- **The fibre integral commutes with base change of the test object on a colimit generator.**
This is the content of the naturality of the trace map, with the colimit bookkeeping removed. -/
public theorem integralTraceStageHom_baseChange {V V' : SmallEtale B Y.obj Y.property}
    (g : V' ⟶ V) (E : FiniteSupport B f V) :
    AddCommGrpCat.ofHom (finiteSupportBaseChange B f
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E).sectionsMap ≫
        integralTraceStageHom.{u, v} B f hw V' (finiteSupportBaseChange B f
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E).support =
      integralTraceStageHom.{u, v} B f hw V E ≫
        (locallyConstantMapsAbSmallEtale.{u, v} B Y.obj Y.property TraceCoeff.{u, v}).map
          g.op := by
  apply AddCommGrpCat.hom_ext
  ext a
  exact LocallyConstant.ext fun y => integralTraceGenerator_baseChange.{u, v} B f hw g E a y

/-- **Naturality of the trace map in the étale test object.** On a colimit generator both sides
are the fibre integral of the restricted section, and those agree by the base-change invariance
of the fibre integral. -/
public theorem integralTracePresheafApp_naturality {V V' : SmallEtale B Y.obj Y.property}
    (g : V' ⟶ V) :
    ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).1.obj
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v})).map g.op ≫
        integralTracePresheafApp.{u, v} B f hw V' =
      integralTracePresheafApp.{u, v} B f hw V ≫
        (locallyConstantMapsAbSmallEtale.{u, v} B Y.obj Y.property TraceCoeff.{u, v}).map
          g.op := by
  apply (cancel_epi (eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
    (fun _ => inferInstance)).2.obj_eq
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V).symm)).1
  apply colimit.hom_ext
  intro E
  have hleft := colimit_ι_eqToHom_map_desc
    (finiteSupportDiagram B f
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V)
    (finiteSupportDiagram B f
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V')
    ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).2.obj_eq _ V)
    ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).2.obj_eq _ V')
    (((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).1.obj
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v})).map g.op)
    (integralTraceCocone.{u, v} B f hw V') E
    (finiteSupportBaseChange B f
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E).support
    (AddCommGrpCat.ofHom (finiteSupportBaseChange B f
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E).sectionsMap)
    ((finiteSupportPushforward.{u, max (u + 1) v} B f
      (fun _ => inferInstance)).2.map_restrict
        (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) g E)
  have hright := colimit_ι_eqToHom_desc_comp
    (finiteSupportDiagram B f
      (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V)
    ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).2.obj_eq _ V)
    (integralTraceCocone.{u, v} B f hw V) E
    ((locallyConstantMapsAbSmallEtale.{u, v} B Y.obj Y.property TraceCoeff.{u, v}).map g.op)
  exact hleft.trans ((integralTraceStageHom_baseChange.{u, v} B f hw g E).trans hright.symm)

/-- **The morphism of presheaves `f_{p!}Z ⟶ Z` of Stacks 0GKG.** Over an étale test object it is
the map out of the colimit of Stacks 0F6M induced by the fibre integral on each stage, and
naturality in the test object is the base-change invariance of the fibre integral. -/
public def integralTracePresheafMap :
    (finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).1.obj
        (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) ⟶
      (locallyConstantSheafAb.{u, v} B Y.obj Y.property TraceCoeff.{u, v}).obj where
  app V := integralTracePresheafApp.{u, v} B f hw V.unop
  naturality := by
    rintro ⟨V⟩ ⟨V'⟩ g
    exact integralTracePresheafApp_naturality.{u, v} B f hw g.unop

/-- **The value of the trace map of presheaves on a colimit generator.** The trace map applied to
the generator of a finite support `E` is the fibre integral out of the stage `H_E(Z)`. Every
statement about the trace map is proved from this. -/
public theorem integralTracePresheafMap_ι (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B f V) :
    colimit.ι (finiteSupportDiagram B f
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) V) E ≫
        eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
          (fun _ => inferInstance)).2.obj_eq _ V).symm ≫
        (integralTracePresheafMap.{u, v} B f hw).app (op V) =
      integralTraceStageHom.{u, v} B f hw V E :=
  integralTracePresheafApp_ι.{u, v} B f hw V E

/-- **The weighted trace map `Tr : f_!Z ⟶ Z` of Stacks 0GKG on the constant sheaf.** The
finite-support direct image `f_!Z` is the sheafification of `f_{p!}Z` and `Z` is a sheaf, so the
morphism of presheaves extends uniquely to a morphism of sheaves. -/
@[sga "4 IX 5.1" "partial"]
public def integralTrace :
    (fShriekFunctor.{u, v} B f).obj
        (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v}) ⟶
      locallyConstantSheafAb.{u, v} B Y.obj Y.property TraceCoeff.{u, v} :=
  ⟨sheafifyLift (SmallEtale.topology B Y.obj Y.property)
    (integralTracePresheafMap.{u, v} B f hw)
    (locallyConstantSheafAb.{u, v} B Y.obj Y.property TraceCoeff.{u, v}).property⟩

/-- The sheafified trace map restricts along the sheafification unit to the morphism of
presheaves it was built from. -/
public theorem toSheafify_integralTrace :
    toSheafify (SmallEtale.topology B Y.obj Y.property)
        ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).1.obj
          (locallyConstantSheafAb.{u, v} B X.obj X.property TraceCoeff.{u, v})) ≫
        (integralTrace.{u, v} B f hw).1 =
      integralTracePresheafMap.{u, v} B f hw :=
  toSheafify_sheafifyLift _ _ _

end Presheaf

end AlgebraicGeometry.SmallEtale

end
