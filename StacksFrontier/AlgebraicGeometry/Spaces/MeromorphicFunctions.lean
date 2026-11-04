module

public import Mathlib.Algebra.Category.Ring.Limits
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.MeromorphicPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.CategoryTheory.Sites.Modules.StructureSheafLocalization

/-!
# The sheaf of meromorphic functions on an algebraic space

Let `F` be an algebraic space over a scheme `S`.  A section of the structure sheaf of `F` over
an étale chart `U` is *regular* when it is a regular section of the structure sheaf of the
scheme underlying `U`, in the sense of Stacks 01WY.  Regularity is preserved by restriction
along a morphism of charts — the underlying morphism of schemes is étale, hence flat — and the
regular sections over a chart are closed under multiplication and contain `1`, so they form a
multiplicative subpresheaf `𝒮_F` of the structure sheaf.

The *sheaf of meromorphic functions* `𝒦_F` is the sheafification of the presheaf of sectionwise
localizations `U ↦ 𝒮_F(U)⁻¹ 𝒪_F(U)`, and a *meromorphic function* on `F` is a global section
of `𝒦_F`.

On an *affine* étale chart the regular sections are exactly the nonzerodivisors in the ring of
sections; in general regularity over a chart coincides with regularity in the sheaf-theoretic
sense on the slice étale site over that chart.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleScheme` is the scheme underlying an étale chart.
* `AlgebraicGeometry.Space.IsRegularSection` is regularity of a section of `𝒪_F` over a chart,
  and `AlgebraicGeometry.Space.regularSections` collects the regular sections over a chart into
  a multiplicative subset, `AlgebraicGeometry.Space.regularSectionsSubpresheaf` into the
  multiplicative subpresheaf `𝒮_F` of the structure sheaf.
* `AlgebraicGeometry.Space.meromorphicFunctionSheaf` is `𝒦_F`,
  `AlgebraicGeometry.Space.toMeromorphicFunctionSheaf` the canonical map `𝒪_F ⟶ 𝒦_F`, and
  `AlgebraicGeometry.Space.MeromorphicFunction` the ring of meromorphic functions on `F`.
* `AlgebraicGeometry.Space.IsRegularSectionOnSlice` is regularity of a section over a chart `U`
  on the slice étale site over `U`, expressed as a monomorphism of presheaves of modules.

## Main results

* `AlgebraicGeometry.Space.isRegularSection_map`: regularity of a section is preserved by
  restriction along a morphism of étale charts.
* `AlgebraicGeometry.Space.isRegularSection_iff_mem_nonZeroDivisors` is Stacks 0EN4: over an
  affine étale chart the regular sections are the nonzerodivisors.
* `AlgebraicGeometry.Space.isRegularSection_iff_isRegularSectionOnSlice` identifies regularity
  over a chart with regularity on the slice étale site over that chart.
* `AlgebraicGeometry.isRegularSectionOn_top_iff_mem_nonZeroDivisors`: on an affine scheme a
  global section of the structure sheaf is regular exactly when it is a nonzerodivisor.

## Implementation notes

The ringed site carrying the construction is the library's
`AlgebraicGeometry.Space.smallEtaleRingedSite`, and the sheafified sectionwise localization is
`AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.localizationPresheaf` of Stacks 0EMC,
so only the multiplicative subpresheaf of regular sections is built here.  Sheafification of
presheaves of commutative rings on the small étale site is available at the universe of the
schemes because the site is essentially small there
(`AlgebraicGeometry.Space.SmallEtale.instHasSheafify`); it is restated for the projections of
the ringed site, which instance search does not unfold.

Restriction of a regular section along a morphism of charts is reduced to the scheme-level
statement for a flat morphism, Stacks 02OU: the underlying morphism of schemes of a morphism of
étale charts is étale, hence flat.

The slice-site description is proved by comparing the two over the Zariski opens of the scheme
underlying the chart, every one of which is itself an étale chart over it
(`AlgebraicGeometry.Space.openChart`).  This is what makes the comparison hold for an arbitrary
chart, with affineness entering only through the scheme-level identification of regular global
sections with nonzerodivisors.

## References

* [Stacks Project, Tag 0EN3](https://stacks.math.columbia.edu/tag/0EN3)
* [Stacks Project, Tag 0EN4](https://stacks.math.columbia.edu/tag/0EN4)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry

/-- Multiplication by a ring element is injective exactly when it is a nonzerodivisor. -/
lemma isSMulRegular_iff_mem_nonZeroDivisors {R : Type*} [CommRing R] (a : R) :
    IsSMulRegular R a ↔ a ∈ R⁰ := by
  rw [mem_nonZeroDivisors_iff, isSMulRegular_iff_right_eq_zero_of_smul]
  refine ⟨fun h => ⟨fun x hx => h x (by rw [smul_eq_mul]; exact hx),
    fun x hx => h x (by rw [smul_eq_mul, mul_comm]; exact hx)⟩, fun h x hx => h.1 x ?_⟩
  rw [← smul_eq_mul]; exact hx

/-- A global section of the structure sheaf of a locally ringed space which is regular on the
whole space is a nonzerodivisor in the ring of global sections. -/
theorem mem_nonZeroDivisors_of_isRegularSectionOn_top (X : LocallyRingedSpace.{u})
    (s : X.presheaf.obj (op (⊤ : Opens X))) (hs : IsRegularSectionOn X ⊤ s) :
    s ∈ (X.presheaf.obj (op (⊤ : Opens X)))⁰ := by
  rw [← isSMulRegular_iff_mem_nonZeroDivisors]
  simpa using (Stacks.Meromorphic.isRegularSectionOn_iff_forall_le X ⊤ s).mp hs ⊤ le_rfl

/-- On an affine scheme a global section of the structure sheaf is regular exactly when it is a
nonzerodivisor in the ring of global sections. -/
theorem isRegularSectionOn_top_iff_mem_nonZeroDivisors (X : Scheme.{u}) [IsAffine X]
    (s : Γ(X, ⊤)) :
    IsRegularSectionOn X.toLocallyRingedSpace ⊤ s ↔ s ∈ Γ(X, ⊤)⁰ := by
  refine ⟨mem_nonZeroDivisors_of_isRegularSectionOn_top X.toLocallyRingedSpace s, fun hs => ?_⟩
  rw [Stacks.Meromorphic.isRegularSectionOn_iff_germ]
  intro x hx
  exact isSMulRegular_germ_of_isAffineOpen X (isAffineOpen_top X)
    ((isSMulRegular_iff_mem_nonZeroDivisors s).mpr hs) ⟨x, hx⟩

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The scheme underlying a small étale chart of `F`. -/
abbrev smallEtaleScheme (U : SmallEtale B S hS F) : Scheme.{u} :=
  (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)

/-! ### The multiplicative subpresheaf of regular sections -/

/-- A section of the structure sheaf of `F` over an étale chart `U` is *regular* when it is a
regular section of the structure sheaf of the scheme underlying `U`, in the sense of Stacks
01WY.  These are the sections denoted `𝒮_F(U)` in Stacks 0EN2. -/
abbrev IsRegularSection (U : SmallEtale B S hS F)
    (s : (structurePresheaf B S hS F).obj (op U)) : Prop :=
  IsRegularSectionOn (smallEtaleScheme B S hS F U).toLocallyRingedSpace ⊤ s

/-- The unit section is regular over every étale chart. -/
theorem isRegularSection_one (U : SmallEtale B S hS F) :
    IsRegularSection B S hS F U 1 := by
  refine (Stacks.Meromorphic.isRegularSectionOn_iff_germ _ ⊤ _).mpr fun x hx => ?_
  rw [show (smallEtaleScheme B S hS F U).presheaf.germ ⊤ x hx
      (1 : (structurePresheaf B S hS F).obj (op U)) = 1 from
    ((smallEtaleScheme B S hS F U).presheaf.germ ⊤ x hx).hom.map_one]
  exact IsSMulRegular.one _

/-- A product of regular sections over an étale chart is regular. -/
theorem isRegularSection_mul (U : SmallEtale B S hS F)
    (a b : (structurePresheaf B S hS F).obj (op U))
    (ha : IsRegularSection B S hS F U a) (hb : IsRegularSection B S hS F U b) :
    IsRegularSection B S hS F U (a * b) := by
  replace ha := (Stacks.Meromorphic.isRegularSectionOn_iff_germ _ ⊤ _).mp ha
  replace hb := (Stacks.Meromorphic.isRegularSectionOn_iff_germ _ ⊤ _).mp hb
  refine (Stacks.Meromorphic.isRegularSectionOn_iff_germ _ ⊤ _).mpr fun x hx => ?_
  rw [show (smallEtaleScheme B S hS F U).presheaf.germ ⊤ x hx
      (a * b : (structurePresheaf B S hS F).obj (op U)) =
      (smallEtaleScheme B S hS F U).presheaf.germ ⊤ x hx a *
        (smallEtaleScheme B S hS F U).presheaf.germ ⊤ x hx b from
    ((smallEtaleScheme B S hS F U).presheaf.germ ⊤ x hx).hom.map_mul a b]
  exact (ha x hx).mul (hb x hx)

/-- Restriction along a morphism of étale charts carries regular sections to regular sections:
the underlying morphism of schemes is étale, hence flat, and pullbacks of meromorphic functions
are defined along a flat morphism of schemes. -/
theorem isRegularSection_map {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (s : (structurePresheaf B S hS F).obj (op U)) (hs : IsRegularSection B S hS F U s) :
    IsRegularSection B S hS F V ((structurePresheaf B S hS F).map f.op s) := by
  have hEtale : Etale ((BigFppfOver.toScheme B S hS).map
    ((SmallEtale.toOver B S hS F).map f)) := etale_toScheme_toOver_map B S hS F f
  have : Flat ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map f)) :=
    (Etale.iff_flat_and_formallyUnramified.mp hEtale).1
  have hpull := pullbacksMeromorphicSections_of_flat
    ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map f)) ⊤ ⊤ (by simp) s hs
  have hmap : pullbackSection
      ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map f)).toLRSHom
        ⊤ ⊤ (by simp) s = (structurePresheaf B S hS F).map f.op s := by
    simp [pullbackSection, structurePresheaf, Scheme.Hom.toLRSHom, Scheme.Hom.appTop]
    rfl
  rw [← hmap]
  exact hpull

/-- The regular sections of the structure sheaf of `F` over an étale chart, as a multiplicative
subset of the ring of sections over that chart. -/
def regularSections (U : SmallEtale B S hS F) :
    Submonoid ((structurePresheaf B S hS F).obj (op U)) where
  carrier := {s | IsRegularSection B S hS F U s}
  one_mem' := isRegularSection_one B S hS F U
  mul_mem' ha hb := isRegularSection_mul B S hS F _ _ _ ha hb

/-- Membership in `AlgebraicGeometry.Space.regularSections` is regularity. -/
theorem mem_regularSections_iff (U : SmallEtale B S hS F)
    (s : (structurePresheaf B S hS F).obj (op U)) :
    s ∈ regularSections B S hS F U ↔ IsRegularSection B S hS F U s := Iff.rfl

/-- The subsheaf of sets `𝒮_F ⊆ 𝒪_F` of regular sections, as a multiplicative subpresheaf of
the structure sheaf of the small étale ringed site of `F`. -/
def regularSectionsSubpresheaf (hF : IsAlgebraicSpace B S hS F) :
    RingedSite.MultiplicativeSubpresheaf (smallEtaleRingedSite B S hS F hF) where
  obj U := regularSections B S hS F U.unop
  map f _ hs := isRegularSection_map B S hS F f.unop _ hs

/-! ### The sheaf of meromorphic functions -/

/-- Presheaves of commutative rings on the small étale ringed site of `F` admit sheafification,
in the form in which the sheafified localization of Stacks 0EMC consumes it.

The content is `AlgebraicGeometry.Space.SmallEtale.instHasSheafify`; this restates it for the
topology projection of `AlgebraicGeometry.Space.smallEtaleRingedSite`, which instance search
does not unfold. `AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify_addCommGrpCat` is
the same restatement for presheaves of abelian groups. -/
instance smallEtaleRingedSite_hasWeakSheafify_commRingCat (hF : IsAlgebraicSpace B S hS F) :
    HasWeakSheafify (smallEtaleRingedSite B S hS F hF).J CommRingCat.{u} := by
  change HasWeakSheafify (SmallEtale.topology B S hS F) CommRingCat.{u}
  infer_instance

/-- **Stacks 0EN3.** The *sheaf of meromorphic functions* `𝒦_F` on the algebraic space `F`: the
sheaf on the small étale site of `F` associated to the presheaf of sectionwise localizations
`U ↦ 𝒮_F(U)⁻¹ 𝒪_F(U)`. -/
@[stacks 0EN3 "the sheaf of meromorphic functions"]
noncomputable def meromorphicFunctionSheaf (hF : IsAlgebraicSpace B S hS F) :
    Sheaf (SmallEtale.topology B S hS F) CommRingCat.{u} :=
  (presheafToSheaf (SmallEtale.topology B S hS F) CommRingCat.{u}).obj
    (regularSectionsSubpresheaf B S hS F hF).localizationPresheaf

/-- The canonical map `𝒪_F ⟶ 𝒦_F` from regular functions to meromorphic functions. -/
noncomputable def toMeromorphicFunctionSheaf (hF : IsAlgebraicSpace B S hS F) :
    structureSheaf B S hS F hF ⟶ meromorphicFunctionSheaf B S hS F hF :=
  (regularSectionsSubpresheaf B S hS F hF).toLocalizationSheaf

/-- **Stacks 0EN3.** A *meromorphic function* on the algebraic space `F` is a global section of
its sheaf of meromorphic functions `𝒦_F`. -/
@[stacks 0EN3 "meromorphic functions"]
abbrev MeromorphicFunction (hF : IsAlgebraicSpace B S hS F) :=
  ((meromorphicFunctionSheaf B S hS F hF).obj ⋙ CategoryTheory.forget CommRingCat.{u}).sections

/-- The meromorphic functions on `F` form a commutative ring, with the operations computed on
the sections over each étale chart. -/
noncomputable instance meromorphicFunctionCommRing (hF : IsAlgebraicSpace B S hS F) :
    CommRing (MeromorphicFunction B S hS F hF) :=
  (RingCat.sectionsSubring ((meromorphicFunctionSheaf B S hS F hF).obj ⋙
    forget₂ CommRingCat.{u} RingCat.{u})).toCommRing

/-! ### Regular sections over a chart and over the slice étale site -/

/-- The presheaf of rings of sections of `F`, restricted to the slice étale site over a
chart. -/
abbrev structureRingPresheafOver (U : SmallEtale B S hS F) : (Over U)ᵒᵖ ⥤ RingCat.{u} :=
  (Over.forget U).op ⋙
    Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf (structurePresheaf B S hS F)

/-- A section of the structure sheaf of `F` over a chart `U`, read as a global section of the
unit module on the slice étale site over `U`. -/
noncomputable def structureSectionOver (U : SmallEtale B S hS F)
    (s : (structurePresheaf B S hS F).obj (op U)) :
    (PresheafOfModules.unit (structureRingPresheafOver B S hS F U)).sections :=
  PresheafOfModules.sectionsMk
    (fun V => (structurePresheaf B S hS F).map V.unop.hom.op s)
    (by
      intro V W f
      change (structurePresheaf B S hS F).map f.unop.left.op
          ((structurePresheaf B S hS F).map V.unop.hom.op s) =
        (structurePresheaf B S hS F).map W.unop.hom.op s
      rw [← Functor.map_comp_apply, ← op_comp, f.unop.w])

/-- A section of the structure sheaf of `F` over a chart `U` is *regular on the slice étale
site over `U`* when multiplication by it is a monomorphism of the unit module of the restricted
structure ring presheaf into itself.  This is regularity in the sense of Stacks 01WY, taken on
the slice étale site over `U` rather than on the scheme underlying `U`. -/
abbrev IsRegularSectionOnSlice (U : SmallEtale B S hS F)
    (s : (structurePresheaf B S hS F).obj (op U)) : Prop :=
  Mono ((PresheafOfModules.unit (structureRingPresheafOver B S hS F U)).unitHomEquiv.symm
    (structureSectionOver B S hS F U s))

/-- A section regular over a chart is regular on the slice étale site over that chart:
regularity is inherited by every restriction, and over each chart it says exactly that
multiplication by the restricted section is injective. -/
theorem isRegularSectionOnSlice_of_isRegularSection (U : SmallEtale B S hS F)
    (s : (structurePresheaf B S hS F).obj (op U)) (hs : IsRegularSection B S hS F U s) :
    IsRegularSectionOnSlice B S hS F U s := by
  apply PresheafOfModules.mono_of_injective
  intro V
  have hnd := mem_nonZeroDivisors_of_isRegularSectionOn_top _ _
    (isRegularSection_map B S hS F V.unop.hom s hs)
  change Function.Injective fun r => r * (structurePresheaf B S hS F).map V.unop.hom.op s
  intro x y hxy
  exact (mul_cancel_right_mem_nonZeroDivisors hnd).mp hxy

private lemma isSMulRegular_map_congr {X : Scheme.{u}} {U W W' : X.Opens} (e : W' = W)
    (h : W ≤ U) (h' : W' ≤ U) (s : Γ(X, U))
    (hr : IsSMulRegular Γ(X, W') (X.presheaf.map (homOfLE h').op s)) :
    IsSMulRegular Γ(X, W) (X.presheaf.map (homOfLE h).op s) := by
  subst e
  exact hr

/-- A section regular on the slice étale site over a chart is regular over that chart: every
Zariski open of the scheme underlying the chart is itself an étale chart over it, and
injectivity of multiplication there is exactly regularity of the restriction. -/
theorem isRegularSection_of_isRegularSectionOnSlice (U : SmallEtale B S hS F)
    (s : (structurePresheaf B S hS F).obj (op U)) (hs : IsRegularSectionOnSlice B S hS F U s) :
    IsRegularSection B S hS F U s := by
  have : Mono ((PresheafOfModules.unit (structureRingPresheafOver B S hS F U)).unitHomEquiv.symm
    (structureSectionOver B S hS F U s)) := hs
  have key : ∀ W : (smallEtaleScheme B S hS F U).Opens,
      IsSMulRegular Γ(smallEtaleScheme B S hS F U, W)
        ((smallEtaleScheme B S hS F U).presheaf.map (homOfLE (le_top (a := W))).op s) := by
    intro W
    have hinj := PresheafOfModules.injective_of_mono
      ((PresheafOfModules.unit (structureRingPresheafOver B S hS F U)).unitHomEquiv.symm
        (structureSectionOver B S hS F U s))
      (op (Over.mk (openChartInclusion B S hS F U W)))
    have hval : (structurePresheaf B S hS F).map (openChartInclusion B S hS F U W).op s =
        (smallEtaleScheme B S hS F U).presheaf.map
          (homOfLE (le_top (a := W.ι ''ᵁ (⊤ : W.toScheme.Opens)))).op s :=
      congrArg (fun g : smallEtaleScheme B S hS F (openChart B S hS F U W) ⟶
        smallEtaleScheme B S hS F U => (Scheme.Γ.map g.op) s)
        (toScheme_map_toOver_map_openChartInclusion B S hS F U W)
    have hnd : (structurePresheaf B S hS F).map (openChartInclusion B S hS F U W).op s ∈
        ((structurePresheaf B S hS F).obj (op (openChart B S hS F U W)))⁰ := by
      rw [mem_nonZeroDivisors_iff_right]
      intro x hx
      refine hinj ?_
      change x * (structurePresheaf B S hS F).map (openChartInclusion B S hS F U W).op s =
        (0 : (structurePresheaf B S hS F).obj (op (openChart B S hS F U W))) *
          (structurePresheaf B S hS F).map (openChartInclusion B S hS F U W).op s
      rw [hx, zero_mul]
    have hreg := (isSMulRegular_iff_mem_nonZeroDivisors _).mpr hnd
    rw [hval] at hreg
    exact isSMulRegular_map_congr W.ι_image_top le_top le_top s hreg
  exact (Stacks.Meromorphic.isRegularSectionOn_iff_forall_le _ ⊤ _).mpr fun W _ => key W

/-- Regularity of a section over an étale chart is the same as its regularity on the slice
étale site over that chart. -/
theorem isRegularSection_iff_isRegularSectionOnSlice (U : SmallEtale B S hS F)
    (s : (structurePresheaf B S hS F).obj (op U)) :
    IsRegularSection B S hS F U s ↔ IsRegularSectionOnSlice B S hS F U s :=
  ⟨isRegularSectionOnSlice_of_isRegularSection B S hS F U s,
    isRegularSection_of_isRegularSectionOnSlice B S hS F U s⟩

/-- **Stacks 0EN4.** Over an affine étale chart `U` of the algebraic space `F` the regular
sections of `𝒪_F` are exactly the nonzerodivisors of the ring of sections `𝒪_F(U)`. -/
@[stacks 0EN4]
theorem isRegularSection_iff_mem_nonZeroDivisors (U : SmallEtale B S hS F)
    (hU : IsAffine (smallEtaleScheme B S hS F U))
    (s : (structurePresheaf B S hS F).obj (op U)) :
    IsRegularSection B S hS F U s ↔ s ∈ ((structurePresheaf B S hS F).obj (op U))⁰ :=
  have := hU
  isRegularSectionOn_top_iff_mem_nonZeroDivisors (smallEtaleScheme B S hS F U) s

/-- Over an affine étale chart, regularity on the slice étale site is being a nonzerodivisor in
the ring of sections. -/
theorem isRegularSectionOnSlice_iff_mem_nonZeroDivisors (U : SmallEtale B S hS F)
    (hU : IsAffine (smallEtaleScheme B S hS F U))
    (s : (structurePresheaf B S hS F).obj (op U)) :
    IsRegularSectionOnSlice B S hS F U s ↔ s ∈ ((structurePresheaf B S hS F).obj (op U))⁰ :=
  (isRegularSection_iff_isRegularSectionOnSlice B S hS F U s).symm.trans
    (isRegularSection_iff_mem_nonZeroDivisors B S hS F U hU s)

end Space

end AlgebraicGeometry

end
