module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleBoundedBelow
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.BaseScalarTriangle
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.DerivedPushforwardDegreeZero
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.PuncturedPreimageSection
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.SpecialFibreSections
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.DegreeZeroSections
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.RestrictionAndConnectingMorphism

/-!
# `Rf_*𝒪_X` as an object of `D(A)`, and the vanishing of `Hom(κ[-1], Rf_*𝒪_X)`

Let `A` be a commutative ring and `f : X ⟶ Spec(A)` a scheme over `A`. The property
`AlgebraicGeometry.IsDerivedPushforwardStructureSheaf` of
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/Vanishing/PuncturedBaseCohomology.lean` pins
down an object of `D(A)` as `Rf_*𝒪_X`: no cohomology in negative degrees, and `Hⁿ(X, 𝒪_X)` as an
`A`-module in degree `n ≥ 0`. This file exhibits an object with that property, namely the
unbounded derived `A`-linear global sections `RΓ(X, 𝒪_X)` of
`StacksFrontier/AlgebraicGeometry/DerivedGlobalSections.lean` applied to the structure sheaf placed
in degree zero; and then proves [Stacks, Tag 0AXC] at that object, in the vanishing situation of
[Stacks, Tag 0AX8] with `X` normal: every morphism `κ[-1] ⟶ RΓ(X, 𝒪_X)` in `D(A)` is zero. The
source also assumes `A` Nagata; the proof here does not need it.

## Main definitions

* `AlgebraicGeometry.derivedGlobalSectionsStructureSheaf`: `RΓ(X, 𝒪_X)`, an object of `D(A)`.

## Main results

* `AlgebraicGeometry.isDerivedPushforwardStructureSheaf_derivedGlobalSectionsStructureSheaf`:
  it is `Rf_*𝒪_X` in the sense of `IsDerivedPushforwardStructureSheaf`.
* `AlgebraicGeometry.VanishingSituation.exists_preimage_of_res_preimagePuncturedSpectrum_eq_zero`:
  a global section of `𝒪_X/a𝒪_X` restricting to zero on `f⁻¹(U)` is the image of a global
  function of `X`. The source obtains this from [Stacks, Tag 0AXB]; here it comes from
  `AlgebraicGeometry.VanishingSituation.eq_zero_of_res_preimagePuncturedSpectrum_eq_zero`.
* `AlgebraicGeometry.VanishingSituation.hom_residueFieldShift_derivedGlobalSections_eq_zero`:
  [Stacks, Tag 0AXC].

## The proof, and how it differs from the source's

The source factors a morphism `α : κ[-1] ⟶ Rf_*𝒪_X` through the adjunction `Rf_* ⊣ Lf^*`, the
cohomology sheaves of `Lf^*κ[-1]` and the Ext spectral sequence of [Stacks, Tag 07AA], arriving
at an extension `0 → 𝒪_X → ℰ → 𝒪_{X_s} → 0`, and then lifts the unit section of `𝒪_{X_s}` and
corrects it by the element of `A` that `𝔪 → A` is multiplication by. The route taken here is
shorter and uses no spectral sequence.

Fix a nonzero `a ∈ 𝔪`. Multiplication by `a` on `𝒪_X` is injective, so
`0 → 𝒪_X → 𝒪_X → 𝒪_X/a𝒪_X → 0` is short exact, and `A`-linear derived global sections carry it
to a distinguished triangle in `D(A)` whose first morphism is `a • 𝟙`
(`AlgebraicGeometry.derivedGlobalSectionsSmulTriangle` and its two companions). A morphism out
of `κ` is annihilated by `a`, so `α` is killed by that first morphism, and
`CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₁` factors it through
`RΓ(X, 𝒪_X/a𝒪_X)`.

That factorisation is read off in degree zero. Both `RΓ(X, 𝒪_X)` and `RΓ(X, 𝒪_X/a𝒪_X)` are
`≥ 0` with degree-zero cohomology the global sections, by
`AlgebraicGeometry.isGE_zero_derivedGlobalSectionsSingle` and
`AlgebraicGeometry.derivedGlobalSectionsSingleHomologyZeroIso`, and `κ` placed in degree zero is
`≤ 0`; so `DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE` turns a morphism
`κ ⟶ RΓ(X, 𝒪_X/a𝒪_X)` into an `A`-linear map `κ ⟶ Γ(X, 𝒪_X/a𝒪_X)`, and conversely builds a
morphism `A ⟶ RΓ(X, 𝒪_X)` out of an `A`-linear map `A ⟶ Γ(X, 𝒪_X)`. Naturality of the
degree-zero identification in the sheaf,
`AlgebraicGeometry.derivedGlobalSectionsSingleHomologyZeroIso_hom_naturality`, is what makes the
two readings compatible with the second morphism of the triangle.

The section `s ∈ Γ(X, 𝒪_X/a𝒪_X)` so produced is the image of `1`, hence annihilated by `𝔪`,
hence restricts to zero on `f⁻¹(U)` by
`AlgebraicGeometry.res_preimage_eq_zero_of_maximalIdeal_smul_eq_zero`, so it is zero by
`AlgebraicGeometry.VanishingSituation.eq_zero_of_res_preimagePuncturedSpectrum_eq_zero` of
`Vanishing/SpecialFibreSections.lean` (no section of `𝒪_X/a𝒪_X` is supported in the special
fibre), and in particular it is the image of a global function of `X`. The source reaches this
point through [Stacks, Tag 0AXB] instead: the connecting class of `s` in `H¹(X, 𝒪_X)` dies on
`f⁻¹(U)`, so it vanishes, and the long exact sequence lifts `s`. That route is still recorded
here as `exists_class_of_res_preimagePuncturedSpectrum_eq_zero` and
`extensionClassOfDerivedHom_derivedGlobalSectionsStructureSheaf`, but the theorem does not use
it, and so it needs neither [Stacks, Tag 0AXB] nor the Nagata condition that tag requires. Lifting
that function back into `D(A)` factors the morphism out of `A` through `RΓ(X, 𝒪_X)`, which two
consecutive morphisms of a distinguished triangle annihilate.

What is left is the algebra, and it is already proved:
`AlgebraicGeometry.VanishingSituation.hom_residueFieldShift_eq_zero_of_comp_mkQ_eq_zero` of
`Vanishing/DerivedPushforwardDegreeZero.lean`, resting on `Hom_A(𝔪, A) = A`, turns the vanishing
of the composite `A[-1] ⟶ κ[-1] ⟶ RΓ(X, 𝒪_X)` into the vanishing of `α` itself.

## Implementation notes

Both halves of `IsDerivedPushforwardStructureSheaf` come from the two statements about a right
derived functor on the unbounded derived category applied to an object placed in degree zero: the
cohomology in degree `n ≥ 0` is Mathlib's classical `Rⁿ`, by
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`, and there is no cohomology
in negative degrees, by `Stacks.DerivedFunctor.isZero_homologyFunctor_obj_derived_single`. Their
common hypothesis, the existence of K-injective resolutions of complexes of `𝒪_X`-modules, is
`AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective`.

`AlgebraicGeometry.secsOver` and `AlgebraicGeometry.globalSectionsOver` are the same functor at
the two spellings `SheafOfModules X.ringCatSheaf` and `X.Modules` of its source, so the two
readings of `Rⁿ` agree definitionally and no comparison is interposed.

*One chosen resolution throughout.* The connecting morphism of the long exact sequence depends on
a resolution of the short exact sequence by a short exact sequence of injective resolutions, a
`Stacks.Cohomology.RightDerivedDelta.Horseshoe`, and nothing in the library identifies the
connecting morphisms of two different resolutions. So one resolution, the one
`Stacks.Cohomology.RightDerivedDelta.horseshoe` returns, is used for both facts needed about the
connecting morphism: exactness of the long sequence
(`Stacks.Cohomology.RightDerivedDelta.Horseshoe.exact_composableArrows₅`) and compatibility with
restriction to an open (`Stacks.Cohomology.Restriction.Hrestrict_delta_eq_zero`). Both are stated
for an arbitrary additive functor into an abelian category, and both are used at `secF R ⊤`, the
abelian-group-valued sections functor whose right derived functors are `Hgroup` — so no
comparison with the `A`-module-valued cohomology is needed, and the only crossing is at the level
of elements, where `Γ(X, ℱ)` as an `A`-module and `Γ(X, ℱ)` as an abelian group have the same
underlying type. The identification `H⁰(U, ℱ) ≅ Γ(U, ℱ)` and its naturality in both the sheaf and
the open are `HzeroIso`, `Hzero_map` and `Hzero_Hrestrict` of
`StacksFrontier/Topology/Sheaves/Cohomology/Locality/DegreeZeroSections.lean`; left exactness of
`secF R U`, which is their side condition, is `Stacks.SectionsExact.preservesFiniteLimits_secF`.

*The spelling of the sheaf of rings.* The cohomology of `Vanishing/PuncturedBaseCohomology.lean`
is stated with `VanishingSituation.structureRingSheaf` while the sheaves and sections here are
written at `X.ringCatSheaf`. The two are equal by `rfl`, and the instances on their categories of
modules are the same term, so the crossing is made by passing a term; a rewrite cannot do it, its
motive being elaborated at reducible transparency.

## References

* [Stacks Project, Tag 0AXC](https://stacks.math.columbia.edu/tag/0AXC)
* [Stacks Project, Tag 0AXB](https://stacks.math.columbia.edu/tag/0AXB)
* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 0AXK](https://stacks.math.columbia.edu/tag/0AXK)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard Scheme.commRingRingCatSheafObj

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **`RΓ(X, 𝒪_X)` as an object of `D(A)`.** The unbounded derived functor of `A`-linear global
sections, applied to the structure sheaf placed in cohomological degree zero. -/
def derivedGlobalSectionsStructureSheaf : DerivedCategory (ModuleCat.{u} A) :=
  (derivedGlobalSectionsOver f).obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))

/-- **`RΓ(X, 𝒪_X)` is `Rf_*𝒪_X`.** It has no cohomology in negative degrees, and its cohomology
in degree `n ≥ 0` is `Hⁿ(X, 𝒪_X)` as an `A`-module. -/
theorem isDerivedPushforwardStructureSheaf_derivedGlobalSectionsStructureSheaf :
    IsDerivedPushforwardStructureSheaf X f (derivedGlobalSectionsStructureSheaf f) where
  isZero_homology_neg n hn :=
    Stacks.DerivedFunctor.isZero_homologyFunctor_obj_derived_single (globalSectionsOver f)
      (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f)
      (Scheme.Modules.exists_quasiIso_isKInjective X) _ n hn
  nonempty_homology_iso n :=
    ⟨(Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived (globalSectionsOver f)
      (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f)
      (Scheme.Modules.exists_quasiIso_isKInjective X) n).app
        (SheafOfModules.unit X.ringCatSheaf)⟩

/-! ### Two lemmas about a triangle whose first morphism is a scalar -/

/-- **A morphism into the first vertex of a triangle whose first morphism is a scalar, shifted,
with the obstruction to lifting carried along.** Let `T` be a distinguished triangle whose first
morphism is `a • c`, let `P` be an object annihilated by `a`, and suppose every morphism
`β : P ⟶ T.obj₃` comes with an element `ξ` of some `Ξ` satisfying `p` whose vanishing makes `β`
lift along `T.mor₂` after precomposition with `q : Q ⟶ P`. Then every morphism
`P⟦-1⟧ ⟶ T.obj₁` comes with such an element whose vanishing kills it after precomposition with
the shift of `q`.

Shifting the morphism by one with the adjunction of the shift puts it, since `a` annihilates
`P`, in the image of precomposition with `T.mor₃`; that single `β` names the element, and once
the element vanishes the lift turns the composite into two consecutive morphisms of the
triangle.

The obstruction is threaded through as an abstract `Ξ` with a predicate `p` because the only
thing used of it is that it has a zero: at the point of use it is a class in `H¹(X, 𝒪_X)` and
`p` says that the class dies over the punctured spectrum. -/
private theorem exists_class_comp_shift_eq_zero_of_mor₁_eq_smul {R : Type*} [CommRing R]
    {C : Type*} [Category C] [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear R]
    [Pretriangulated C] (T : Triangle C) (hT : T ∈ distTriang C) {P Q : C} (q : Q ⟶ P) (a : R)
    (c : T.obj₁ ⟶ T.obj₂) (hmor : T.mor₁ = a • c) (hP : a • 𝟙 P = 0)
    {Ξ : Type*} [Zero Ξ] (p : Ξ → Prop)
    (hlift : ∀ β : P ⟶ T.obj₃, ∃ ξ : Ξ, p ξ ∧
      (ξ = 0 → ∃ γ : Q ⟶ T.obj₂, γ ≫ T.mor₂ = q ≫ β))
    (α : P⟦(-1 : ℤ)⟧ ⟶ T.obj₁) :
    ∃ ξ : Ξ, p ξ ∧ (ξ = 0 → q⟦(-1 : ℤ)⟧' ≫ α = 0) := by
  have key : ∀ α' : P ⟶ T.obj₁⟦(1 : ℤ)⟧, ∃ ξ : Ξ, p ξ ∧ (ξ = 0 → q ≫ α' = 0) := by
    intro α'
    have ha : a • α' = 0 := by
      rw [← Category.id_comp α', ← Linear.smul_comp, hP, zero_comp]
    have hz : α' ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 := by
      rw [hmor, Functor.map_smul, Linear.comp_smul, ← Linear.smul_comp, ha, zero_comp]
    obtain ⟨β, rfl⟩ := T.coyoneda_exact₁ hT α' hz
    obtain ⟨ξ, hp, himp⟩ := hlift β
    refine ⟨ξ, hp, fun hξ => ?_⟩
    obtain ⟨γ, hγ⟩ := himp hξ
    rw [← Category.assoc, ← hγ, Category.assoc, comp_distTriang_mor_zero₂₃ T hT, comp_zero]
  let adj := (shiftEquiv' C (-1 : ℤ) 1 (by norm_num)).toAdjunction
  obtain ⟨ξ, hp, himp⟩ := key (adj.homEquiv P T.obj₁ α)
  refine ⟨ξ, hp, fun hξ => (adj.homEquiv Q T.obj₁).injective ?_⟩
  exact ((adj.homEquiv_naturality_left q α).trans (himp hξ)).trans
    (show adj.homEquiv Q T.obj₁ 0 = 0 by
      rw [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]).symm

/-- **The residue field placed in degree zero is annihilated by the maximal ideal**, in the
derived category: the single functor is `A`-linear, and `𝔪` annihilates `κ = A/𝔪`. -/
private theorem smul_id_singleFunctor_residueField_eq_zero {A : Type u} [CommRing A]
    [IsLocalRing A] (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) :
    a • 𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A))) = 0 := by
  have h : a • 𝟙 (ModuleCat.of A (IsLocalRing.ResidueField A)) = 0 := by
    ext x
    show a • x = 0
    rw [Algebra.smul_def, show algebraMap A (IsLocalRing.ResidueField A) a = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul]
  rw [← CategoryTheory.Functor.map_id (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0),
    ← Functor.map_smul, h, Functor.map_zero]

namespace VanishingSituation

/-! ### A section that dies over the punctured spectrum comes from the base -/

/-- **The class in `H¹(X, 𝒪_X)` attached to a global section of `𝒪_X/a𝒪_X` that dies over
`f⁻¹(U)`:** it dies over `f⁻¹(U)` too, and as soon as it vanishes the section is the image of a
global function of `X`.

This is the construction, and it uses neither normality of `X`, nor the Nagata condition, nor
[Stacks, Tag 0AXB] — the vanishing of the class is left to the consumer, which is exactly how the
source arranges the argument. The class is the connecting class of the section for one chosen
resolution of `0 → 𝒪_X → 𝒪_X → 𝒪_X/a𝒪_X → 0` by a short exact sequence of injective
resolutions, and the two facts about that one connecting morphism
`H⁰(X, 𝒪_X/a𝒪_X) ⟶ H¹(X, 𝒪_X)` are read off it: compatibility with restriction to an open gives
the first conclusion, and exactness of the long sequence gives the second. -/
theorem exists_class_of_res_preimagePuncturedSpectrum_eq_zero (V : VanishingSituation.{u})
    {a : V.A}
    (hmono : Mono (baseSmulModules V.X V.f a (SheafOfModules.unit V.X.ringCatSheaf)))
    (s : ToType ((zeroSchemeStructureSheaf V.X V.f a).val.obj (op (⊤ : V.X.Opens))))
    (hs : Stacks.SheafOfModules.res (zeroSchemeStructureSheaf V.X V.f a)
      (homOfLE (show V.preimagePuncturedSpectrum ≤ (⊤ : V.X.Opens) from le_top)) s = 0) :
    ∃ ξ : Hgroup V.structureRingSheaf (⊤ : V.X.Opens) 1
        (SheafOfModules.unit V.structureRingSheaf),
      V.firstCohomologyRestriction ξ = V.firstCohomologyRestriction 0 ∧
      (ξ = 0 →
        ∃ t : ToType ((SheafOfModules.unit V.X.ringCatSheaf).val.obj (op (⊤ : V.X.Opens))),
          (toZeroSchemeStructureSheaf V.X V.f a).val.app (op (⊤ : V.X.Opens)) t = s) := by
  have hS : (ShortComplex.cokernelSequence (baseSmulModules V.X V.f a
      (SheafOfModules.unit V.X.ringCatSheaf))).ShortExact :=
    baseSmulUnit_shortExact (Over.mk V.f) a hmono
  obtain ⟨s₀, hs₀⟩ := (bijective_Hzero V.X.ringCatSheaf (⊤ : V.X.Opens)
    (zeroSchemeStructureSheaf V.X V.f a)).2 s
  -- the class of `s` in `H⁰(X, 𝒪_X/a𝒪_X)` dies on `f⁻¹(U)`
  have hres : Hrestrict V.X.ringCatSheaf
      (show V.preimagePuncturedSpectrum ≤ (⊤ : V.X.Opens) from le_top) 0
      (zeroSchemeStructureSheaf V.X V.f a) s₀ = 0 := by
    refine (bijective_Hzero V.X.ringCatSheaf V.preimagePuncturedSpectrum
      (zeroSchemeStructureSheaf V.X V.f a)).1 ?_
    rw [Hzero_Hrestrict, hs₀, map_zero]
    exact hs
  -- so its connecting class dies on `f⁻¹(U)`
  have hdelta₀ : Hrestrict V.X.ringCatSheaf
      (show V.preimagePuncturedSpectrum ≤ (⊤ : V.X.Opens) from le_top) 1
      (SheafOfModules.unit V.X.ringCatSheaf)
      ((Stacks.Cohomology.RightDerivedDelta.horseshoe hS).delta
        (secF V.X.ringCatSheaf (⊤ : V.X.Opens)) 0 s₀) = 0 :=
    Stacks.Cohomology.Restriction.Hrestrict_delta_eq_zero V.X.ringCatSheaf
      (Stacks.Cohomology.RightDerivedDelta.horseshoe hS) _ 0 s₀ hres
  refine ⟨(Stacks.Cohomology.RightDerivedDelta.horseshoe hS).delta
      (secF V.X.ringCatSheaf (⊤ : V.X.Opens)) 0 s₀,
    hdelta₀.trans (map_zero (ConcreteCategory.hom V.firstCohomologyRestriction)).symm,
    fun hdelta => ?_⟩
  -- exactness of the long sequence puts the class in the image of `H⁰(X, 𝒪_X)`
  have hker : ∀ x : (Hgroup V.X.ringCatSheaf (⊤ : V.X.Opens) 0
          (zeroSchemeStructureSheaf V.X V.f a) : Type u),
      (Stacks.Cohomology.RightDerivedDelta.horseshoe hS).delta
          (secF V.X.ringCatSheaf (⊤ : V.X.Opens)) 0 x = 0 →
      ∃ t₀ : (Hgroup V.X.ringCatSheaf (⊤ : V.X.Opens) 0
          (SheafOfModules.unit V.X.ringCatSheaf) : Type u),
        (Hfunctor V.X.ringCatSheaf (⊤ : V.X.Opens) 0).map
          (toZeroSchemeStructureSheaf V.X V.f a) t₀ = x :=
    (ShortComplex.ab_exact_iff _).1
      (((Stacks.Cohomology.RightDerivedDelta.horseshoe hS).exact_composableArrows₅
        (secF V.X.ringCatSheaf (⊤ : V.X.Opens)) 0).exact 1)
  obtain ⟨t₀, ht₀⟩ := hker s₀ hdelta
  refine ⟨ConcreteCategory.hom ((HzeroIso V.X.ringCatSheaf (⊤ : V.X.Opens)).hom.app
    (SheafOfModules.unit V.X.ringCatSheaf)) t₀, ?_⟩
  have h := Hzero_map V.X.ringCatSheaf (⊤ : V.X.Opens)
    (toZeroSchemeStructureSheaf V.X V.f a) t₀
  rw [ht₀, hs₀] at h
  exact h.symm

/-- **A global section of `𝒪_X/a𝒪_X` whose restriction to `f⁻¹(U)` vanishes is the image of a
global function of `X`**, for `X` normal and `a ≠ 0`: it is zero, by
`VanishingSituation.eq_zero_of_res_preimagePuncturedSpectrum_eq_zero`. The source obtains this
step from [Stacks, Tag 0AXB], through the connecting class that
`exists_class_of_res_preimagePuncturedSpectrum_eq_zero` attaches to the section; here it is
proved directly, without the Nagata condition. -/
theorem exists_preimage_of_res_preimagePuncturedSpectrum_eq_zero (V : VanishingSituation.{u})
    [IsNormal V.X] {a : V.A} (ha : a ≠ 0)
    (s : ToType ((zeroSchemeStructureSheaf V.X V.f a).val.obj (op (⊤ : V.X.Opens))))
    (hs : Stacks.SheafOfModules.res (zeroSchemeStructureSheaf V.X V.f a)
      (homOfLE (show V.preimagePuncturedSpectrum ≤ (⊤ : V.X.Opens) from le_top)) s = 0) :
    ∃ t : ToType ((SheafOfModules.unit V.X.ringCatSheaf).val.obj (op (⊤ : V.X.Opens))),
      (toZeroSchemeStructureSheaf V.X V.f a).val.app (op (⊤ : V.X.Opens)) t = s :=
  ⟨0, by rw [map_zero, V.eq_zero_of_res_preimagePuncturedSpectrum_eq_zero a ha s hs]⟩

/-! ### The lift of a morphism out of the residue field -/

/-- The image of `1` under an `A`-linear map out of the residue field is annihilated by `𝔪`. -/
private theorem smul_image_one_eq_zero (V : VanishingSituation.{u}) {a : V.A}
    (b : V.residueFieldModule ⟶ (secsOver V.f).obj (zeroSchemeStructureSheaf V.X V.f a)) :
    ∀ r ∈ IsLocalRing.maximalIdeal V.A,
      baseSection V.X V.f r • (show ToType ((zeroSchemeStructureSheaf V.X V.f a).val.obj
        (op (⊤ : V.X.Opens))) from b (1 : IsLocalRing.ResidueField V.A)) = 0 := by
  intro r hr
  have h := b.hom.map_smul r (1 : IsLocalRing.ResidueField V.A)
  have hr0 : r • (1 : IsLocalRing.ResidueField V.A) = 0 := by
    rw [Algebra.smul_def, mul_one, show
      algebraMap V.A (IsLocalRing.ResidueField V.A) r = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr hr]
  rw [hr0, map_zero] at h
  exact h.symm

/-- An `A`-linear map `κ ⟶ Γ(X, 𝒪_X/a𝒪_X)` restricted along `A ⟶ κ` factors through
`Γ(X, 𝒪_X)` as soon as the image of `1` is the image of a global function. -/
private theorem exists_comp_secsOver_eq_of_preimage (V : VanishingSituation.{u}) {a : V.A}
    (b : V.residueFieldModule ⟶ (secsOver V.f).obj (zeroSchemeStructureSheaf V.X V.f a))
    (t : ToType ((SheafOfModules.unit V.X.ringCatSheaf).val.obj (op (⊤ : V.X.Opens))))
    (ht : (toZeroSchemeStructureSheaf V.X V.f a).val.app (op (⊤ : V.X.Opens)) t =
      b (1 : IsLocalRing.ResidueField V.A)) :
    ∃ c : ModuleCat.of V.A V.A ⟶ (secsOver V.f).obj (SheafOfModules.unit V.X.ringCatSheaf),
      c ≫ (secsOver V.f).map (toZeroSchemeStructureSheaf V.X V.f a) =
        ModuleCat.ofHom (IsLocalRing.maximalIdeal V.A).mkQ ≫ b := by
  refine ⟨ConcreteCategory.ofHom (C := ModuleCat.{u} V.A)
    (LinearMap.toSpanSingleton V.A
      (ToType ((secsOver V.f).obj (SheafOfModules.unit V.X.ringCatSheaf)))
      (show ToType ((secsOver V.f).obj (SheafOfModules.unit V.X.ringCatSheaf)) from t)),
    ModuleCat.hom_ext (LinearMap.ext_ring ?_)⟩
  show (toZeroSchemeStructureSheaf V.X V.f a).val.app (op (⊤ : V.X.Opens))
      ((1 : V.A) • (show ToType ((secsOver V.f).obj
        (SheafOfModules.unit V.X.ringCatSheaf)) from t)) = b (1 : IsLocalRing.ResidueField V.A)
  rwa [one_smul]

/-- **A morphism `κ ⟶ Γ(X, 𝒪_X/a𝒪_X)` of `A`-modules, restricted along `A ⟶ κ`, factors through
`Γ(X, 𝒪_X)`**, for `X` normal and `a ≠ 0`. The image of `1` is annihilated by `𝔪`, so it dies
over the punctured spectrum, so it is the image of a global function by
`exists_preimage_of_res_preimagePuncturedSpectrum_eq_zero`. -/
private theorem exists_comp_secsOver_eq_of_hom_residueField (V : VanishingSituation.{u})
    [IsNormal V.X] {a : V.A} (ha : a ≠ 0)
    (b : V.residueFieldModule ⟶ (secsOver V.f).obj (zeroSchemeStructureSheaf V.X V.f a)) :
    ∃ c : ModuleCat.of V.A V.A ⟶ (secsOver V.f).obj (SheafOfModules.unit V.X.ringCatSheaf),
      c ≫ (secsOver V.f).map (toZeroSchemeStructureSheaf V.X V.f a) =
        ModuleCat.ofHom (IsLocalRing.maximalIdeal V.A).mkQ ≫ b := by
  obtain ⟨t, ht⟩ := V.exists_preimage_of_res_preimagePuncturedSpectrum_eq_zero ha _
    (res_preimage_eq_zero_of_maximalIdeal_smul_eq_zero V.f
      (zeroSchemeStructureSheaf V.X V.f a) _ (smul_image_one_eq_zero V b)
      V.puncturedSpectrumOpen (fun hx => hx rfl))
  exact exists_comp_secsOver_eq_of_preimage V b t ht

/-- **A morphism `κ ⟶ Γ(X, 𝒪_X/a𝒪_X)` of `A`-modules names a class in `H¹(X, 𝒪_X)` that dies
over `f⁻¹(U)`, and as soon as that class vanishes the morphism is the restriction along `A ⟶ κ`
of one through `Γ(X, 𝒪_X)`.** The image of `1` is annihilated by `𝔪`, hence dies over the
punctured spectrum, so
`exists_class_of_res_preimagePuncturedSpectrum_eq_zero` attaches the class to it; once the class
vanishes the image of `1` is the image of a global function of `X`, and multiplication by that
function is the map `A ⟶ Γ(X, 𝒪_X)` wanted.

Neither normality of `X` nor the Nagata condition is used, the vanishing of the class being left
to the consumer. -/
private theorem exists_class_comp_secsOver_eq_of_hom_residueField (V : VanishingSituation.{u})
    {a : V.A}
    (hmono : Mono (baseSmulModules V.X V.f a (SheafOfModules.unit V.X.ringCatSheaf)))
    (b : V.residueFieldModule ⟶ (secsOver V.f).obj (zeroSchemeStructureSheaf V.X V.f a)) :
    ∃ ξ : Hgroup V.structureRingSheaf (⊤ : V.X.Opens) 1
        (SheafOfModules.unit V.structureRingSheaf),
      V.firstCohomologyRestriction ξ = V.firstCohomologyRestriction 0 ∧
      (ξ = 0 →
        ∃ c : ModuleCat.of V.A V.A ⟶ (secsOver V.f).obj (SheafOfModules.unit V.X.ringCatSheaf),
          c ≫ (secsOver V.f).map (toZeroSchemeStructureSheaf V.X V.f a) =
            ModuleCat.ofHom (IsLocalRing.maximalIdeal V.A).mkQ ≫ b) := by
  obtain ⟨ξ, hξ, himp⟩ := V.exists_class_of_res_preimagePuncturedSpectrum_eq_zero hmono _
    (res_preimage_eq_zero_of_maximalIdeal_smul_eq_zero V.f
      (zeroSchemeStructureSheaf V.X V.f a) _ (smul_image_one_eq_zero V b)
      V.puncturedSpectrumOpen (fun hx => hx rfl))
  refine ⟨ξ, hξ, fun h0 => ?_⟩
  obtain ⟨t, ht⟩ := himp h0
  exact exists_comp_secsOver_eq_of_preimage V b t ht

/-- **A morphism `κ ⟶ RΓ(X, ℱ)` in `D(A)` names an obstruction whose vanishing makes it lift
through `RΓ(X, 𝒢)` along a morphism `𝒢 ⟶ ℱ` of sheaves of modules, after restriction along
`A ⟶ κ`, as soon as the corresponding `A`-linear map of global sections names one that does.**
Both `RΓ(X, ℱ)` and `RΓ(X, 𝒢)` are `≥ 0` with degree-zero cohomology the global sections, and
`κ` placed in degree zero is `≤ 0`, so taking `H⁰` is a bijection on morphisms out of it in both
cases; naturality of the degree-zero identification in the sheaf matches the two bijections along
the morphism, and the obstruction is the one the degree-zero map names.

As in `exists_class_comp_shift_eq_zero_of_mor₁_eq_smul` the obstruction is an abstract `Ξ` with a
predicate `p`; at the point of use it is a class in `H¹(X, 𝒪_X)` that dies over `f⁻¹(U)`. -/
private theorem exists_class_comp_eq_of_hom_singleResidueField (V : VanishingSituation.{u})
    {M₂ M₃ : V.X.Modules} (π : M₂ ⟶ M₃)
    (mkq : ModuleCat.of V.A V.A ⟶ V.residueFieldModule)
    {Ξ : Type*} [Zero Ξ] (p : Ξ → Prop)
    (hπ : ∀ b : V.residueFieldModule ⟶ (globalSectionsOver V.f).obj M₃,
      ∃ ξ : Ξ, p ξ ∧ (ξ = 0 →
        ∃ c : ModuleCat.of V.A V.A ⟶ (globalSectionsOver V.f).obj M₂,
          c ≫ (globalSectionsOver V.f).map π = mkq ≫ b))
    (β : (DerivedCategory.singleFunctor (ModuleCat.{u} V.A) 0).obj V.residueFieldModule ⟶
      (derivedGlobalSectionsOver V.f).obj
        ((DerivedCategory.singleFunctor V.X.Modules 0).obj M₃)) :
    ∃ ξ : Ξ, p ξ ∧ (ξ = 0 →
      ∃ γ : (DerivedCategory.singleFunctor (ModuleCat.{u} V.A) 0).obj (ModuleCat.of V.A V.A) ⟶
          (derivedGlobalSectionsOver V.f).obj
            ((DerivedCategory.singleFunctor V.X.Modules 0).obj M₂),
        γ ≫ (derivedGlobalSectionsOver V.f).map
            ((DerivedCategory.singleFunctor V.X.Modules 0).map π) =
          (DerivedCategory.singleFunctor (ModuleCat.{u} V.A) 0).map mkq ≫ β) := by
  let Hf := DerivedCategory.homologyFunctor (ModuleCat.{u} V.A) 0
  let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} V.A) 0
  let e₃ := derivedGlobalSectionsSingleHomologyZeroIso V.f M₃
  let e₂ := derivedGlobalSectionsSingleHomologyZeroIso V.f M₂
  let b : V.residueFieldModule ⟶ (globalSectionsOver V.f).obj M₃ :=
    ε.inv.app V.residueFieldModule ≫ Hf.map β ≫ e₃.hom
  have hb : ε.hom.app V.residueFieldModule ≫ b = Hf.map β ≫ e₃.hom := by
    dsimp only [b]
    rw [Iso.hom_inv_id_app_assoc]
  obtain ⟨ξ, hp, himp⟩ := hπ b
  refine ⟨ξ, hp, fun hξ => ?_⟩
  obtain ⟨c, hc⟩ := himp hξ
  have hnat : Hf.map ((derivedGlobalSectionsOver V.f).map
        ((DerivedCategory.singleFunctor V.X.Modules 0).map π)) ≫ e₃.hom =
      e₂.hom ≫ (globalSectionsOver V.f).map π :=
    derivedGlobalSectionsSingleHomologyZeroIso_hom_naturality V.f π
  have hεnat : Hf.map ((DerivedCategory.singleFunctor (ModuleCat.{u} V.A) 0).map mkq) ≫
      ε.hom.app V.residueFieldModule = ε.hom.app (ModuleCat.of V.A V.A) ≫ mkq :=
    ε.hom.naturality mkq
  have hge₂ : ((derivedGlobalSectionsOver V.f).obj
      ((DerivedCategory.singleFunctor V.X.Modules 0).obj M₂)).IsGE 0 :=
    isGE_zero_derivedGlobalSectionsSingle V.f M₂
  have hge₃ : ((derivedGlobalSectionsOver V.f).obj
      ((DerivedCategory.singleFunctor V.X.Modules 0).obj M₃)).IsGE 0 :=
    isGE_zero_derivedGlobalSectionsSingle V.f M₃
  obtain ⟨γ, hγ⟩ := (DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE
    ((DerivedCategory.singleFunctor (ModuleCat.{u} V.A) 0).obj (ModuleCat.of V.A V.A))
    ((derivedGlobalSectionsOver V.f).obj
      ((DerivedCategory.singleFunctor V.X.Modules 0).obj M₂)) 0).surjective
    (ε.hom.app (ModuleCat.of V.A V.A) ≫ c ≫ e₂.inv)
  change Hf.map γ = ε.hom.app (ModuleCat.of V.A V.A) ≫ c ≫ e₂.inv at hγ
  refine ⟨γ, ?_⟩
  have hleft : Hf.map (γ ≫ (derivedGlobalSectionsOver V.f).map
        ((DerivedCategory.singleFunctor V.X.Modules 0).map π)) ≫ e₃.hom =
      ε.hom.app (ModuleCat.of V.A V.A) ≫ c ≫ (globalSectionsOver V.f).map π := by
    rw [Functor.map_comp, hγ]
    simp only [Category.assoc]
    rw [hnat, Iso.inv_hom_id_assoc]
  have hright : Hf.map ((DerivedCategory.singleFunctor (ModuleCat.{u} V.A) 0).map mkq ≫ β) ≫
      e₃.hom = ε.hom.app (ModuleCat.of V.A V.A) ≫ mkq ≫ b := by
    rw [Functor.map_comp]
    simp only [Category.assoc]
    rw [← hb, ← Category.assoc, hεnat, Category.assoc]
  refine (DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE
    ((DerivedCategory.singleFunctor (ModuleCat.{u} V.A) 0).obj (ModuleCat.of V.A V.A))
    ((derivedGlobalSectionsOver V.f).obj
      ((DerivedCategory.singleFunctor V.X.Modules 0).obj M₃)) 0).injective ?_
  rw [← cancel_mono e₃.hom, hleft, hright, hc]

/-- **A morphism `α : κ[-1] ⟶ RΓ(X, 𝒪_X)` is zero as soon as an obstruction attached to it
vanishes**, for an obstruction-valued lifting property of the `A`-linear maps
`κ ⟶ Γ(X, 𝒪_X/a𝒪_X)` along `A ⟶ κ`, at some nonzero `a ∈ 𝔪` with `a • 𝟙 : 𝒪_X ⟶ 𝒪_X` mono.
This chains the triangle of `0 → 𝒪_X → 𝒪_X → 𝒪_X/a𝒪_X → 0`, the degree-zero reading of
morphisms out of `κ`, and `Hom_A(𝔪, A) = A`. -/
private theorem exists_obstruction_of_hom_residueFieldShift (V : VanishingSituation.{u})
    {Ξ : Type*} [Zero Ξ] (p : Ξ → Prop)
    (h : ∀ a : V.A, a ∈ IsLocalRing.maximalIdeal V.A → a ≠ 0 →
      Mono (baseSmulModules V.X V.f a (SheafOfModules.unit V.X.ringCatSheaf)) →
      ∀ b : V.residueFieldModule ⟶ (secsOver V.f).obj (zeroSchemeStructureSheaf V.X V.f a),
        ∃ ξ : Ξ, p ξ ∧ (ξ = 0 →
          ∃ c : ModuleCat.of V.A V.A ⟶ (secsOver V.f).obj (SheafOfModules.unit V.X.ringCatSheaf),
            c ≫ (secsOver V.f).map (toZeroSchemeStructureSheaf V.X V.f a) =
              ModuleCat.ofHom (IsLocalRing.maximalIdeal V.A).mkQ ≫ b))
    (α : V.residueFieldShift ⟶ derivedGlobalSectionsStructureSheaf V.f) :
    ∃ ξ : Ξ, p ξ ∧ (ξ = 0 → α = 0) := by
  have hd : 1 < ringKrullDim V.A := by rw [V.dimension_two]; norm_num
  obtain ⟨a, ham, ha⟩ := (Submodule.ne_bot_iff _).mp
    (Stacks.NormalLocalDomain.maximalIdeal_ne_bot_of_one_lt_ringKrullDim hd)
  have hmono : Mono (baseSmulModules V.X V.f a (SheafOfModules.unit V.X.ringCatSheaf)) :=
    mono_baseSmulModules_unit V.X V.f a
      (baseSection_ne_zero_of_isModification V.X V.f V.modification ha)
  obtain ⟨ξ, hξ, himp⟩ := exists_class_comp_shift_eq_zero_of_mor₁_eq_smul
    (derivedGlobalSectionsSmulTriangle (Over.mk V.f) a hmono)
    (derivedGlobalSectionsSmulTriangle_distinguished (Over.mk V.f) a hmono) _ a _
    (derivedGlobalSectionsSmulTriangle_mor₁ (Over.mk V.f) a hmono)
    (smul_id_singleFunctor_residueField_eq_zero a ham) p
    (fun β => V.exists_class_comp_eq_of_hom_singleResidueField
      (shortComplexBridge (Over.mk V.f) (ShortComplex.cokernelSequence
        (baseSmulModules V.X V.f a (SheafOfModules.unit V.X.ringCatSheaf)))).g
      (ModuleCat.ofHom (IsLocalRing.maximalIdeal V.A).mkQ) p (h a ham ha hmono) β) α
  exact ⟨ξ, hξ, fun h0 => V.hom_residueFieldShift_eq_zero_of_comp_mkQ_eq_zero
    (isDerivedPushforwardStructureSheaf_derivedGlobalSectionsStructureSheaf V.f) α (himp h0)⟩

/-! ### The construction of the source's proof -/

/-- **The construction in the proof of [Stacks, Tag 0AXC], carried out at `RΓ(X, 𝒪_X)`.** Every
morphism `α : κ[-1] ⟶ RΓ(X, 𝒪_X)` in `D(A)` has attached to it a class `ξ ∈ H¹(X, 𝒪_X)` whose
restriction to `f⁻¹(U)` agrees with that of the zero class and whose vanishing forces `α = 0`;
that is, `VanishingSituation.ExtensionClassOfDerivedHom` holds at `RΓ(X, 𝒪_X)`.

Nothing is assumed beyond Situation [Stacks, Tag 0AX8] — not normality of `X`, not the Nagata
condition, and in particular not [Stacks, Tag 0AXB]. That is the division of labour of the
source, whose construction produces a class split over `f⁻¹(U)` and then calls on injectivity of
restriction to make it vanish.

For a nonzero `a ∈ 𝔪` the class is the connecting class, for one chosen resolution of
`0 → 𝒪_X → 𝒪_X → 𝒪_X/a𝒪_X → 0`, of the global section of `𝒪_X/a𝒪_X` that `α` names in degree
zero. `exists_class_of_res_preimagePuncturedSpectrum_eq_zero` both shows that the class dies over
`f⁻¹(U)` and, once it vanishes, lifts the section to a global function of `X`;
`exists_class_comp_shift_eq_zero_of_mor₁_eq_smul` carries that lift back to the vanishing of the
restriction of `α` along `A[-1] ⟶ κ[-1]`, which `Hom_A(𝔪, A) = A` upgrades to `α = 0`.

The class is not the extension of [Stacks, Tag 0B3A] that the source attaches to `α` through the
adjunction `Rf_* ⊣ Lf^*` and the Ext spectral sequence of [Stacks, Tag 07AA]; it is the class of
the shorter route, which needs neither. What the two share is exactly what
`ExtensionClassOfDerivedHom` asks of a class. -/
theorem extensionClassOfDerivedHom_derivedGlobalSectionsStructureSheaf
    (V : VanishingSituation.{u}) :
    V.ExtensionClassOfDerivedHom (derivedGlobalSectionsStructureSheaf V.f) := by
  intro α
  exact V.exists_obstruction_of_hom_residueFieldShift
    (fun ζ => V.firstCohomologyRestriction ζ = V.firstCohomologyRestriction 0)
    (fun _ _ _ hmono b => V.exists_class_comp_secsOver_eq_of_hom_residueField hmono b) α

/-! ### Tag 0AXC -/

/-- **Stacks Project, Tag 0AXC.** In Situation [Stacks, Tag 0AX8] with `X` normal, every
morphism `κ[-1] ⟶ RΓ(X, 𝒪_X)` in `D(A)` is zero; that is, the group `Hom_{D(A)}(κ[-1], Rf_*𝒪_X)`
vanishes, the pushforward being read as the derived global sections `RΓ(X, 𝒪_X)`, which
`isDerivedPushforwardStructureSheaf_derivedGlobalSectionsStructureSheaf` identifies with
`Rf_*𝒪_X` by its cohomology. The source also assumes `A` Nagata; that is not needed here.

For a nonzero `a ∈ 𝔪` the triangle of `0 → 𝒪_X → 𝒪_X → 𝒪_X/a𝒪_X → 0` has `a • 𝟙` as its first
morphism, so `α` factors through `RΓ(X, 𝒪_X/a𝒪_X)`. In degree zero the factorisation is a global
section of `𝒪_X/a𝒪_X` annihilated by `𝔪`. Such a section dies over the punctured spectrum, so it
is zero by `eq_zero_of_res_preimagePuncturedSpectrum_eq_zero`, and in particular it is the image
of a global function of `X`. Two consecutive morphisms of the triangle then kill the restriction
of `α` along `A[-1] ⟶ κ[-1]`, and `Hom_A(𝔪, A) = A` kills `α`.

The source reaches the same lift through [Stacks, Tag 0AXB], whose proof needs the Nagata
condition to make a normalization finite. Here it comes from the vanishing of sections of
`𝒪_X/a𝒪_X` supported in the special fibre, which is proved directly by Lipman's argument from
[Stacks, Tag 0AX9], algebraic Hartogs and the fact that a proper integral curve has no nonconstant
functions. -/
@[stacks 0AXC "the vanishing of Hom_{D(A)}(kappa[-1], Rf_*O_X), the pushforward being the \
derived global sections RGamma(X, O_X), which \
isDerivedPushforwardStructureSheaf_derivedGlobalSectionsStructureSheaf identifies with Rf_*O_X \
by its cohomology H^n(X, O_X); stated for X normal without the Nagata hypothesis on A, which \
is not needed. For a nonzero a in the maximal ideal the triangle of \
0 -> O_X -> O_X -> O_X/aO_X -> 0 has first morphism a times the identity, so a morphism out of \
kappa[-1] factors through RGamma(X, O_X/aO_X); in degree zero that is a global section of \
O_X/aO_X annihilated by the maximal ideal, hence supported in the special fibre, hence zero by \
eq_zero_of_res_preimagePuncturedSpectrum_eq_zero (Lipman's argument from Tag 0AX9, used in \
place of Tag 0AXB), and Hom_A(m, A) = A over a Noetherian normal local domain of dimension at \
least two kills the morphism"]
theorem hom_residueFieldShift_derivedGlobalSections_eq_zero (V : VanishingSituation.{u})
    [IsNormal V.X]
    (α : V.residueFieldShift ⟶ derivedGlobalSectionsStructureSheaf V.f) : α = 0 := by
  obtain ⟨_, -, h0⟩ := V.exists_obstruction_of_hom_residueFieldShift (Ξ := PUnit.{1})
    (fun _ => True)
    (fun _ _ ha _ b => ⟨0, trivial, fun _ => V.exists_comp_secsOver_eq_of_hom_residueField ha b⟩) α
  exact h0 (Subsingleton.elim _ _)

end VanishingSituation

end AlgebraicGeometry

end
