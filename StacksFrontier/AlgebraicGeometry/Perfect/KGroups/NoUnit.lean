module

public import StacksFrontier.RingTheory.Length.FiniteLengthSerre
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.Perfect.KGroups.Ring
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.PerfectBoundedCoherent
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Groupoids.CoherentColimit
public import StacksFrontier.CategoryTheory.Triangulated.KGroup.Basic
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.CanonicalTruncation
public import StacksCore.Tactic.StacksAttribute

/-!
# The `K`-group of perfect complexes with support has no unit in general

Let `R` be a Noetherian domain of Krull dimension at most one, `f` a nonzero nonunit of `R`,
`X = Spec R` and `Z ⊂ X` a closed subscheme with underlying closed subset `V(f)`. Then the
multiplication on `K₀(D_{Z, perf}(𝒪_X))` given by the derived tensor product
(`AlgebraicGeometry.exists_supportedPerfect_nonUnitalCommRing`) has no unit. For `R = ℤ` and
`f = 2` this is the assertion of [Stacks, Tag 0FDN] that `K₀(D_{Z, perf}(𝒪_X))` in general
does not have a unit.

## Main results

* `AlgebraicGeometry.SupportedPerfectNoUnit.cls_supportedPerfectTensorObj_koszulSupported`:
  the class of `A ⊗^𝐋 (R ⧸ (f))^~` vanishes for every `A` in `D_{Z, perf}(𝒪_X)`.
* `AlgebraicGeometry.SupportedPerfectNoUnit.cls_koszulSupported_ne_zero`: the class of
  `(R ⧸ (f))^~` placed in degree zero is nonzero.
* `AlgebraicGeometry.SupportedPerfectNoUnit.not_exists_unit`: no unit, for `Spec R` and `V(f)`.
* `AlgebraicGeometry.exists_supportedPerfect_not_exists_unit` ([stacks 0FDN]): a scheme and a
  closed subscheme for which the multiplication exists and has no unit.

## Implementation notes

The class `[(R ⧸ (f))^~]` kills every class: the derived tensor product with a fixed object `A`
of `D_{Z, perf}(𝒪_X)` is exact, and carries the distinguished triangle
`𝒪_X --f--> 𝒪_X --> (R ⧸ (f))^~ --> 𝒪_X[1]` to a distinguished triangle all of whose vertices
lie in `D_{Z, perf}(𝒪_X)`, because `D_{Z, perf}(𝒪_X)` is closed under tensoring with perfect
objects; so `[A ⊗ (R ⧸ (f))^~] = [A ⊗ 𝒪_X] - [A ⊗ 𝒪_X] = 0`. A unit `e` would then give
`[(R ⧸ (f))^~] = e · [(R ⧸ (f))^~] = 0`.

That `[(R ⧸ (f))^~]` is nonzero is detected by lengths. Fix a point `x` of `V(f)`. For `E` in
`D_{Z, perf}(𝒪_X)` the stalks at `x` of the cohomology sheaves of `E` are finite modules over
`𝒪_{X,x}` which vanish at the generic point, hence are torsion, hence of finite length, `𝒪_{X,x}`
being a Noetherian domain of dimension at most one. Taking stalks of cohomology is therefore a
homological functor to the Serre class of modules of finite length, and by [Stacks, Tag 0FCR]
the alternating sum of lengths is a homomorphism `K₀(D_{Z, perf}(𝒪_X)) → ℤ`. It takes the value
`length (R ⧸ (f))_x > 0` on `[(R ⧸ (f))^~]`.

## References

* [Stacks Project, Tag 0FDN](https://stacks.math.columbia.edu/tag/0FDN)
* [Stacks Project, Tag 0FCR](https://stacks.math.columbia.edu/tag/0FCR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry StrictlyPerfect

universe u

namespace AlgebraicGeometry.SupportedPerfectNoUnit

attribute [local instance 10000] HasDerivedCategory.standard

variable {R : CommRingCat.{u}}

/-- The closed immersion `Spec(R ⧸ (f)) ⟶ Spec R`. -/
abbrev zeroLocusImmersion (f : R) :
    Spec (CommRingCat.of (R ⧸ Ideal.span {f})) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))

/-- `Spec(R ⧸ (f)) ⟶ Spec R` is a closed immersion. -/
instance isClosedImmersion_zeroLocusImmersion (f : R) : IsClosedImmersion (zeroLocusImmersion f) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The closed subset underlying `Spec(R ⧸ (f)) ⟶ Spec R` is `V(f)`. -/
theorem range_zeroLocusImmersion (f : R) :
    Set.range (zeroLocusImmersion f).base = PrimeSpectrum.zeroLocus {f} := by
  have h : Set.range (zeroLocusImmersion f).base = PrimeSpectrum.zeroLocus
      (RingHom.ker (Ideal.Quotient.mk (Ideal.span {f}))) :=
    range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective
  rw [h, Ideal.mk_ker, PrimeSpectrum.zeroLocus_span]

/-- `R ⧸ (f)`, as an `R`-module. -/
abbrev quotientModule (f : R) : ModuleCat.{u} R :=
  ModuleCat.of R (R ⧸ Ideal.span {f})

/-- `R`, as a module over itself. -/
abbrev selfModule (R : CommRingCat.{u}) : ModuleCat.{u} R :=
  ModuleCat.of R R

/-- The short complex `R --f--> R --> R ⧸ (f)`. -/
abbrev koszulShortComplex (f : R) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (X₁ := selfModule R) (X₂ := selfModule R) (X₃ := quotientModule f)
    (ModuleCat.ofHom (LinearMap.mulLeft R f))
    (ModuleCat.ofHom (Ideal.span {f}).mkQ)
    (ModuleCat.hom_ext (LinearMap.ext fun r => (Submodule.Quotient.mk_eq_zero _).2
      (Ideal.mul_mem_right r _ (Ideal.subset_span rfl))))

/-- `0 → R --f--> R --> R ⧸ (f) → 0` is exact when `f` is a non-zero element of a domain. -/
theorem koszulShortComplex_shortExact [IsDomain R] {f : R} (hf : f ≠ 0) :
    (koszulShortComplex f).ShortExact := by
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · rw [LinearMap.exact_iff]
    ext r
    simp only [ModuleCat.hom_ofHom, LinearMap.mem_ker, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, LinearMap.mem_range, LinearMap.mulLeft_apply,
      Ideal.mem_span_singleton']
    exact ⟨fun ⟨a, ha⟩ => ⟨a, by rw [← ha, mul_comm]⟩, fun ⟨a, ha⟩ => ⟨a, by rw [← ha, mul_comm]⟩⟩
  · exact mul_right_injective₀ hf
  · exact Submodule.mkQ_surjective _

/-- The stalk of `M^~` at `x` vanishes exactly when every element of `M` is killed by an element
not in the prime of `x`. -/
theorem subsingleton_stalk_tilde_iff (M : ModuleCat.{u} R) (x : PrimeSpectrum R) :
    Subsingleton ((tilde M).presheaf.stalk x) ↔
      ∀ m : M, ∃ r ∈ x.asIdeal.primeCompl, r • m = 0 :=
  IsLocalizedModule.subsingleton_iff x.asIdeal.primeCompl (tilde.toStalk M x).hom

/-- The stalk of `(R ⧸ (f))^~` at a point `y` vanishes exactly when `f` does not vanish at
`y`. -/
theorem subsingleton_stalk_tilde_quotientModule_iff (f : R) (y : PrimeSpectrum R) :
    Subsingleton ((tilde (quotientModule f)).presheaf.stalk y) ↔ f ∉ y.asIdeal := by
  rw [subsingleton_stalk_tilde_iff]
  constructor
  · intro h hf
    obtain ⟨r, hr, hr'⟩ := h (Submodule.Quotient.mk 1)
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one, Submodule.Quotient.mk_eq_zero] at hr'
    exact hr ((Ideal.span_singleton_le_iff_mem _).2 hf hr')
  · intro hf m
    refine ⟨f, hf, ?_⟩
    obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective _ m
    exact (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mul_mem_right r _ (Ideal.subset_span rfl))

/-- The stalk of `(R ⧸ (f))^~` at a point `y` is nontrivial exactly when `f` vanishes at `y`. -/
private theorem nontrivial_stalk_tilde_quotientModule_iff (f : R) (y : PrimeSpectrum R) :
    Nontrivial ((tilde (quotientModule f)).presheaf.stalk y) ↔ f ∈ y.asIdeal := by
  rw [← not_subsingleton_iff_nontrivial, subsingleton_stalk_tilde_quotientModule_iff, not_not]

section Stalks

variable [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]

/-- The local rings of `Spec R` have Krull dimension at most one when `R` has. -/
instance krullDimLE_one_stalk (x : Spec R) : Ring.KrullDimLE 1 ((Spec R).presheaf.stalk x) := by
  have hU := isAffineOpen_top (Spec R)
  letI := ((Spec R).presheaf.germ ⊤ x trivial).hom.toAlgebra
  haveI := hU.isLocalization_stalk ⟨x, trivial⟩
  rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height
    (hU.primeIdealOf ⟨x, trivial⟩).asIdeal]
  refine (Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top').trans ?_
  rw [ringKrullDim_eq_of_ringEquiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv]
  exact Ring.krullDimLE_iff.1 inferInstance

/-- **A coherent module on `Spec R` vanishing at one point has stalks of finite length.** A
section over `Spec R` vanishing at a point `y` is killed by a nonzero function, by
quasi-coherence; every element of the stalk at `x` is the germ of such a section up to a unit,
so it is killed by a nonzero element of the local ring at `x`, which is a Noetherian domain of
dimension at most one. -/
theorem isFiniteLength_stalk (F : (Spec R).Modules) [F.IsCoherent] (y : Spec R)
    (hy : Subsingleton (F.presheaf.stalk y)) (x : Spec R) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule F x
    IsFiniteLength ((Spec R).presheaf.stalk x) (F.presheaf.stalk x) := by
  let := Stacks.ModuleStalkSpecialization.stalkModule F x
  have : Module.Finite ((Spec R).presheaf.stalk x) (F.presheaf.stalk x) :=
    Scheme.Modules.finite_stalk_of_isCoherent F x
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  refine isFiniteLength_of_forall_exists_smul_eq_zero fun m => ?_
  have hU := isAffineOpen_top (Spec R)
  obtain ⟨t, c, hc, hct⟩ :=
    Stacks.ModuleStalkSpecialization.exists_germ_smul_eq_germ F hU (x := x) trivial m
  obtain ⟨d, hd, hdt⟩ := Stacks.ModuleStalkSpecialization.exists_smul_eq_of_germ_eq F hU
    (x := y) trivial t 0 (Subsingleton.elim _ _)
  have ne_zero {S : Type u} [Semiring S] {P : Ideal S} {s : S} (hs : s ∉ P) : s ≠ 0 :=
    fun h => hs (h ▸ P.zero_mem)
  refine ⟨(Spec R).presheaf.germ ⊤ x trivial (d * c), mem_nonZeroDivisors_of_ne_zero fun h => ?_,
    ?_⟩
  · exact mul_ne_zero (ne_zero hd) (ne_zero hc)
      (germ_injective_of_isIntegral (Spec R) (U := ⊤) x trivial (h.trans (map_zero _).symm))
  · rw [map_mul, mul_smul, hct]
    refine (Stacks.ModuleStalkSpecialization.germ_smul F (U := ⊤) (x := x) trivial d t).symm.trans
      ?_
    rw [hdt, smul_zero, map_zero]

end Stalks

/-! ### The length of the stalk of the cohomology -/

section Length

variable [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  {Z : Scheme.{u}} (i : Z ⟶ Spec R) [IsClosedImmersion i]

/-- The stalk functor at `x`, on the category `OXMod` in which `D(𝒪_X)` is formed. -/
def stalkFunctor (x : Spec R) :
    OXMod.{u, u} (Spec R).toRingedSpace ⥤ ModuleCat.{u} ((Spec R).presheaf.stalk x) :=
  Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec R) x

/-- The stalk functor at `x` preserves finite limits. -/
instance (x : Spec R) : PreservesFiniteLimits (stalkFunctor x) :=
  AlgebraicGeometry.modulesStalkFunctor_preservesFiniteLimits x

/-- The stalk functor at `x` preserves finite colimits. -/
instance (x : Spec R) : PreservesFiniteColimits (stalkFunctor x) :=
  have := AlgebraicGeometry.modulesStalkFunctor_preservesColimits x
  inferInstanceAs (PreservesFiniteColimits (Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec R) x))

/-- The stalk functor at `x` is additive. -/
instance (x : Spec R) : (stalkFunctor x).Additive :=
  AlgebraicGeometry.modulesStalkFunctor_additive x

/-- Degree-zero cohomology followed by the stalk at `x`, from `D(𝒪_X)` to modules over the local
ring at `x`. -/
abbrev stalkHomology (x : Spec R) :
    DerivedCategory (OXMod.{u, u} (Spec R).toRingedSpace) ⥤
      ModuleCat.{u} ((Spec R).presheaf.stalk x) :=
  DerivedCategory.homologyFunctor (OXMod.{u, u} (Spec R).toRingedSpace) 0 ⋙ stalkFunctor x

/-- The `n`-th cohomology sheaf of an object of `D(𝒪_X)`, read as an `𝒪_X`-module of the
scheme. -/
abbrev cohomologyModule (K : DerivedCategory (OXMod.{u, u} (Spec R).toRingedSpace)) (n : ℤ) :
    (Spec R).Modules :=
  (DerivedCategory.homologyFunctor (OXMod.{u, u} (Spec R).toRingedSpace) n).obj K

variable {y : Spec R} (hy : y ∉ Set.range i.base) (x : Spec R)

include hy

/-- The cohomology sheaves of an object of `D_{Z, perf}(𝒪_X)` vanish at a point off `Z`. -/
theorem subsingleton_stalk_cohomologyModule (E : supportedPerfectDerivedCategory i) (n : ℤ) :
    Subsingleton ((cohomologyModule E.obj n).presheaf.stalk y) := by
  rw [← not_nontrivial_iff_subsingleton]
  exact fun h => hy (E.property.2 n ((SheafOfModules.mem_supp_iff_nontrivial_stalk _ y).2 h))

/-- The stalks of the cohomology sheaves of an object of `D_{Z, perf}(𝒪_X)` have finite length,
when `Z` misses a point. -/
theorem isFiniteLength_stalkHomology (E : supportedPerfectDerivedCategory i) :
    ModuleCat.isFiniteLength _ ((stalkHomology x).obj E.obj) := by
  have : (cohomologyModule E.obj 0).IsCoherent :=
    Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_homology (Spec R) E.obj E.property.1 0
  exact isFiniteLength_stalk (cohomologyModule E.obj 0) y
    (subsingleton_stalk_cohomologyModule i hy E 0) x

/-- The stalk at `x` of degree-zero cohomology, as a functor from `D_{Z, perf}(𝒪_X)` to modules
of finite length over the local ring at `x`. -/
def supportedStalkHomology :
    supportedPerfectDerivedCategory i ⥤
      (ModuleCat.isFiniteLength ((Spec R).presheaf.stalk x)).FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ stalkHomology x)
    fun E => isFiniteLength_stalkHomology i hy x E

/-- The stalk of degree-zero cohomology on `D_{Z, perf}(𝒪_X)` preserves zero morphisms. -/
instance : (supportedStalkHomology i hy x).PreservesZeroMorphisms where
  map_zero E₁ E₂ := (ModuleCat.isFiniteLength _).ι.map_injective
    ((ObjectProperty.ι _ ⋙ stalkHomology x).map_zero E₁ E₂ :)

/-- **The stalk of degree-zero cohomology is a homological functor on `D_{Z, perf}(𝒪_X)`.** -/
instance : (supportedStalkHomology i hy x).IsHomological where
  exact T hT := by
    have := (ModuleCat.isFiniteLength
      ((Spec R).presheaf.stalk x)).preservesFiniteLimits_ι_of_isWeakSerreClass
    have := (ModuleCat.isFiniteLength
      ((Spec R).presheaf.stalk x)).preservesFiniteColimits_ι_of_isWeakSerreClass
    rw [← ShortComplex.exact_map_iff_of_faithful _ (ModuleCat.isFiniteLength _).ι]
    exact (Functor.map_distinguished_exact (ObjectProperty.ι _ ⋙
      DerivedCategory.homologyFunctor (OXMod.{u, u} (Spec R).toRingedSpace) 0) T hT).map
        (stalkFunctor x)

omit hy in
/-- Degree-zero cohomology of a shift is the shifted cohomology. -/
def homologyShiftIso (E : supportedPerfectDerivedCategory i) (n : ℤ) :
    (DerivedCategory.homologyFunctor (OXMod.{u, u} (Spec R).toRingedSpace) 0).obj
        ((shiftFunctor (supportedPerfectDerivedCategory i) n).obj E).obj ≅
      cohomologyModule E.obj n :=
  (DerivedCategory.homologyFunctor (OXMod.{u, u} (Spec R).toRingedSpace) 0).mapIso
    ((Functor.commShiftIso (ObjectProperty.ι _) n).app E) ≪≫
  ((DerivedCategory.homologyFunctor (OXMod.{u, u} (Spec R).toRingedSpace) 0).shiftIso n 0 n
    (add_zero n)).app E.obj

/-- The stalk of degree-zero cohomology of `E[n]` vanishes when the `n`-th cohomology sheaf of `E`
does. -/
theorem isZero_supportedStalkHomology (E : supportedPerfectDerivedCategory i) (n : ℤ)
    (hn : IsZero (cohomologyModule E.obj n)) :
    IsZero ((supportedStalkHomology i hy x).obj
      ((shiftFunctor (supportedPerfectDerivedCategory i) n).obj E)) :=
  IsZero.of_full_of_faithful_of_isZero (ModuleCat.isFiniteLength _).ι _
    ((stalkFunctor x).map_isZero
      (IsZero.of_iso hn (homologyShiftIso i E n)))

/-- Only finitely many cohomology sheaves of a perfect complex on `Spec R` are nonzero. -/
theorem finite_nonzero_supportedStalkHomology (E : supportedPerfectDerivedCategory i) :
    {n : ℤ | ¬ IsZero ((supportedStalkHomology i hy x).obj
      ((shiftFunctor (supportedPerfectDerivedCategory i) n).obj E))}.Finite := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, -⟩ :=
    Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect (Spec R)
      E.obj E.property.1
  refine (Set.finite_Icc a b).subset fun n hn => ?_
  by_contra hmem
  simp only [Set.mem_Icc, not_and_or, not_le] at hmem
  refine hn (isZero_supportedStalkHomology i hy x E n ?_)
  rcases hmem with h | h
  exacts [ha n h, hb n h]

end Length

/-! ### The Koszul complex of `f` -/

section Koszul

/-- The cohomology of an object placed in degree zero vanishes in every other degree. -/
theorem isZero_homology_singleFunctor_obj {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (A : C) {n : ℤ} (hn : n ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor C n).obj
      ((DerivedCategory.singleFunctor C 0).obj A)) := by
  refine IsZero.of_iso ?_
    ((DerivedCategory.homologyFunctorFactors C n).app ((CochainComplex.singleFunctor C 0).obj A))
  rcases lt_or_gt_of_ne hn with h | h
  · exact CochainComplex.isZero_of_isGE _ 0 n h
  · exact CochainComplex.isZero_of_isLE _ 0 n h

variable (R) in
/-- `𝒪_X = R^~` placed in degree zero. -/
abbrev structureObj : DerivedCategory (OXMod.{u, u} (Spec R).toRingedSpace) :=
  (DerivedCategory.singleFunctor (OXMod.{u, u} (Spec R).toRingedSpace) 0).obj
    (tilde (selfModule R))

/-- `(R ⧸ (f))^~` placed in degree zero. -/
abbrev koszulObj (f : R) : DerivedCategory (OXMod.{u, u} (Spec R).toRingedSpace) :=
  (DerivedCategory.singleFunctor (OXMod.{u, u} (Spec R).toRingedSpace) 0).obj
    (tilde (quotientModule f))

/-- `𝒪_X` placed in degree zero is perfect. -/
theorem isPerfect_structureObj : RingedSpace.IsPerfect.{u, u + 1} (structureObj R) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
    ((DerivedCategory.singleFunctorIsoCompQ (OXMod.{u, u} (Spec R).toRingedSpace) 0).app
      (tilde (selfModule R))).symm
    (Stacks.Cohomology.PerfectCanonicalTruncation.isPerfect_of_isStrictlyPerfect_of_isZero_X
      ((CochainComplex.singleFunctor (OXMod.{u, u} (Spec R).toRingedSpace) 0).obj
        (tilde (selfModule R)))
      (StrictlyPerfect.isStrictlyPerfect_single
        (StrictlyPerfect.isDirectSummandOfFiniteFree_structureModule (Spec R).toRingedSpace) 0)
      0 fun _ hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega))

variable [IsDomain R] {f : R} (hf : f ≠ 0)

include hf in
/-- `0 → 𝒪_X --f--> 𝒪_X --> (R ⧸ (f))^~ → 0` is exact. -/
theorem tilde_koszulShortComplex_shortExact :
    ((koszulShortComplex f).map (tilde.functor R)).ShortExact :=
  (koszulShortComplex_shortExact hf).map_of_exact (tilde.functor R)

include hf in
/-- The distinguished triangle `𝒪_X --f--> 𝒪_X --> (R ⧸ (f))^~ --> 𝒪_X[1]`. -/
theorem koszulTriangle_distinguished :
    Triangle.mk
      ((DerivedCategory.singleFunctor (OXMod.{u, u} (Spec R).toRingedSpace) 0).map
        ((koszulShortComplex f).map (tilde.functor R)).f)
      ((DerivedCategory.singleFunctor (OXMod.{u, u} (Spec R).toRingedSpace) 0).map
        ((koszulShortComplex f).map (tilde.functor R)).g)
      (tilde_koszulShortComplex_shortExact hf).singleδ ∈
        distTriang (DerivedCategory (OXMod.{u, u} (Spec R).toRingedSpace)) :=
  (tilde_koszulShortComplex_shortExact hf).singleTriangle_distinguished

include hf in
/-- `(R ⧸ (f))^~` placed in degree zero is perfect: it is the cone of `f` on `𝒪_X`. -/
theorem isPerfect_koszulObj : RingedSpace.IsPerfect.{u, u + 1} (koszulObj f) := by
  have := Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect.{u, u + 1}
    (Spec R).toRingedSpace
  exact ObjectProperty.ext_of_isTriangulatedClosed₃
    (Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := (Spec R).toRingedSpace)) _
    (koszulTriangle_distinguished hf) isPerfect_structureObj isPerfect_structureObj

variable {Z : Scheme.{u}} (i : Z ⟶ Spec R) [IsClosedImmersion i]
  (hi : Set.range i.base = PrimeSpectrum.zeroLocus {f})

include hf hi in
/-- `(R ⧸ (f))^~` placed in degree zero is a perfect object with cohomology supported on
`V(f)`. -/
theorem supportedPerfectProperty_koszulObj : supportedPerfectProperty i (koszulObj f) := by
  refine ⟨isPerfect_koszulObj hf, fun n => ?_⟩
  by_cases hn : n = 0
  · subst hn
    refine (SheafOfModules.supp_eq_of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (OXMod.{u, u} (Spec R).toRingedSpace) 0).app (tilde (quotientModule f)))).subset.trans ?_
    rw [hi]
    intro z hz
    exact (PrimeSpectrum.mem_zeroLocus (x := (z : PrimeSpectrum R)) {f}).2
      (Set.singleton_subset_iff.2 ((nontrivial_stalk_tilde_quotientModule_iff f z).1
        ((SheafOfModules.mem_supp_iff_nontrivial_stalk _ z).1 hz)))
  · exact (SheafOfModules.supp_eq_empty_of_isZero
      (isZero_homology_singleFunctor_obj _ hn)).subset.trans (Set.empty_subset _)

/-- `(R ⧸ (f))^~` placed in degree zero, as an object of `D_{Z, perf}(𝒪_X)` for `Z` with
underlying closed subset `V(f)`. -/
def koszulSupported : supportedPerfectDerivedCategory i :=
  ⟨koszulObj f, supportedPerfectProperty_koszulObj hf i hi⟩

open Stacks.DerivedTensor.RingedSite in
/-- **Tensoring with the Koszul object kills classes.** For `A` in `D_{Z, perf}(𝒪_X)`, the
derived tensor product with `A` is exact, so it carries the Koszul triangle
`𝒪_X --f--> 𝒪_X --> (R ⧸ (f))^~ --> 𝒪_X[1]` to a distinguished triangle
`A ⊗ 𝒪_X --> A ⊗ 𝒪_X --> A ⊗ (R ⧸ (f))^~ --> ` whose vertices lie in `D_{Z, perf}(𝒪_X)`; hence
`[A ⊗ 𝒪_X] = [A ⊗ 𝒪_X] + [A ⊗ (R ⧸ (f))^~]` in `K₀`. -/
theorem cls_supportedPerfectTensorObj_koszulSupported
    (A : supportedPerfectDerivedCategory i) :
    K0.cls (supportedPerfectTensorObj i A (koszulSupported hf i hi)) = 0 := by
  let T := (RingedSpace.derivedTensorStructure (Spec R).toRingedSpace
    (canonicalDerivedTensorProduct (Spec R).toRingedSpace.sheaf)).toNonUnitalTensorStructure
  let := T.commShiftRight A.obj
  have := T.isTriangulatedRight A.obj
  have := isTriangulated_supportedPerfect i
  have hT := (T.tensor.obj A.obj).map_distinguished _ (koszulTriangle_distinguished hf)
  have hprop {B} (hB : RingedSpace.IsPerfect.{u, u + 1} B) :
      supportedPerfectProperty i ((T.tensor.obj A.obj).obj B) :=
    supportedPerfect_canonicalDerivedTensorProduct _ _ _ A.property hB
  have h := K0.cls_eq_add_of_distinguished_of_prop (supportedPerfectProperty i)
    (hprop isPerfect_structureObj) (hprop isPerfect_structureObj)
    (hprop (isPerfect_koszulObj hf)) _ _ _ hT
  exact (left_eq_add.1 h :)

end Koszul

/-! ### The class of the Koszul object is nonzero -/

section NonZero

variable [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] {f : R} (hf : f ≠ 0)
  {Z : Scheme.{u}} (i : Z ⟶ Spec R) [IsClosedImmersion i]
  (hi : Set.range i.base = PrimeSpectrum.zeroLocus {f})

/-- The generic point of `Spec R`. -/
abbrev genericPt : Spec R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)

include hf hi in
/-- The generic point of `Spec R` does not lie in `V(f)` for `f ≠ 0`. -/
theorem genericPt_notMem_range : genericPt ∉ Set.range i.base := by
  rw [hi]
  intro h
  exact hf ((PrimeSpectrum.mem_zeroLocus (x := (genericPt : PrimeSpectrum R)) {f}).1 h rfl)

include hf hi in
/-- **The class of `(R ⧸ (f))^~[0]` in `K₀(D_{Z, perf}(𝒪_X))` is nonzero** when `f` vanishes at
some point `x`. The alternating sum of the lengths of the stalks at `x` of the cohomology
sheaves is additive on distinguished triangles, by Tag 0FCR, and takes the value
`length (R ⧸ (f))_x > 0` on `(R ⧸ (f))^~[0]`. -/
theorem cls_koszulSupported_ne_zero (x : Spec R) (hx : f ∈ (x : PrimeSpectrum R).asIdeal) :
    K0.cls (koszulSupported hf i hi) ≠ 0 := by
  intro h
  have hy := genericPt_notMem_range hf i hi
  obtain ⟨φ, hφ⟩ := K0_homomorphism_of_homological _ _
    (supportedStalkHomology i hy x) inferInstance
    (finite_nonzero_supportedStalkHomology i hy x)
  let H := supportedStalkHomology i hy x
  let E := koszulSupported hf i hi
  let M := H.obj ((shiftFunctor (supportedPerfectDerivedCategory i) (0 : ℤ)).obj E)
  have hterm (n : ℤ) (hn : n ≠ 0) : ((-1 : ℤ) ^ n.natAbs) • KZero.mk _ (H.obj
      ((shiftFunctor (supportedPerfectDerivedCategory i) n).obj E)) = 0 :=
    (congrArg (fun z => ((-1 : ℤ) ^ n.natAbs) • z) (KZero.mk_eq_zero_of_isZero
      (isZero_supportedStalkHomology _ hy x _ n (isZero_homology_singleFunctor_obj _ hn)))).trans
      (smul_zero _)
  have hE : eulerClass _ _ H E = KZero.mk _ M :=
    (finsum_eq_single _ 0 hterm).trans
      ((congrArg (fun k : ℤ => k • KZero.mk _ M)
        (by norm_num : (-1 : ℤ) ^ (0 : ℤ).natAbs = 1)).trans
        (one_smul ℤ _))
  have hval : ((Module.length ((Spec R).presheaf.stalk x) M.obj).toNat : ℤ) = 0 :=
    (ModuleCat.finiteLengthHom_mk _ M).symm.trans
      ((congrArg (ModuleCat.finiteLengthHom _) ((hφ E).trans hE)).symm.trans
        ((congrArg (fun a => ModuleCat.finiteLengthHom _ (φ a)) h).trans
          ((congrArg (ModuleCat.finiteLengthHom _) (map_zero φ)).trans (map_zero _))))
  have e : M.obj ≅ (stalkFunctor x).obj (tilde (quotientModule f)) :=
    (stalkFunctor x).mapIso (homologyShiftIso _ (koszulSupported hf i hi) 0 ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (OXMod.{u, u} (Spec R).toRingedSpace) 0).app (tilde (quotientModule f)))
  have : Nontrivial ((stalkFunctor x).obj (tilde (quotientModule f))) :=
    (nontrivial_stalk_tilde_quotientModule_iff f x).2 hx
  have hM : Nontrivial M.obj := e.toLinearEquiv.surjective.nontrivial
  have hpos : 0 < Module.length ((Spec R).presheaf.stalk x) M.obj := Module.length_pos_iff.2 hM
  have hfin := Module.length_ne_top_iff.2 M.property
  rcases ENat.toNat_eq_zero.1 (Nat.cast_eq_zero.1 hval) with h0 | h0
  · exact hpos.ne' h0
  · exact hfin h0

end NonZero

/-! ### No unit -/

/-- A multiplication whose underlying additive group is a given one distributes over the
addition of that group. -/
theorem add_mul_of_toAddCommGroup_eq {K : Type*} (r : NonUnitalCommRing K)
    (inst : AddCommGroup K) (hr : r.toAddCommGroup = inst) (a b c : K) :
    r.mul (@HAdd.hAdd K K K
      (@instHAdd K inst.toAddCommMonoid.toAddCommSemigroup.toAddCommMagma.toAdd) a b) c =
      @HAdd.hAdd K K K (@instHAdd K inst.toAddCommMonoid.toAddCommSemigroup.toAddCommMagma.toAdd)
        (r.mul a c) (r.mul b c) := by
  subst hr
  exact add_mul a b c

/-- A map on `K₀` additive in its first variable vanishes as soon as it vanishes on classes of
objects. -/
theorem mul_left_eq_zero_of_cls {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (mul : K0 C → K0 C → K0 C) (hadd : ∀ a b c, mul (a + b) c = mul a c + mul b c)
    (c : K0 C) (h : ∀ A : C, mul (K0.cls A) c = 0) (a : K0 C) : mul a c = 0 :=
  DFunLike.congr_fun (K0.hom_ext (f := AddMonoidHom.mk' (fun a => mul a c) fun a b => hadd a b c)
    (g := 0) h) a

section NoUnit

variable [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  {Z : Scheme.{u}} (i : Z ⟶ Spec R) [IsClosedImmersion i]

/-- **`K₀(D_{Z, perf}(𝒪_X))` has no unit, for `X = Spec R` and `Z = V(f)`**, where `R` is a
Noetherian domain of dimension at most one and `f` is a nonzero nonunit of `R`. This holds for
every multiplication on `K₀(D_{Z, perf}(𝒪_X))` which is distributive over its addition and sends
the classes of two objects to the class of their derived tensor product; Tag 0FDN's is one,
`AlgebraicGeometry.exists_supportedPerfect_nonUnitalCommRing`.

The class `[(R ⧸ (f))^~]` is nonzero, but its product with every class is zero: tensoring with
the triangle `𝒪_X --f--> 𝒪_X --> (R ⧸ (f))^~` gives `[A ⊗ (R ⧸ (f))^~] = [A ⊗ 𝒪_X] - [A ⊗ 𝒪_X]`.
A unit `e` would give `[(R ⧸ (f))^~] = e · [(R ⧸ (f))^~] = 0`. -/
theorem not_exists_unit {f : R} (hf : f ≠ 0) (hfu : ¬ IsUnit f)
    (hi : Set.range i.base = PrimeSpectrum.zeroLocus {f})
    (r : NonUnitalCommRing (K0 (supportedPerfectDerivedCategory i)))
    (hr : r.toAddCommGroup =
      (inferInstance : AddCommGroup (K0 (supportedPerfectDerivedCategory i))))
    (hmul : ∀ K L : supportedPerfectDerivedCategory i,
      r.mul (K0.cls K) (K0.cls L) = K0.cls (supportedPerfectTensorObj i K L)) :
    ¬ ∃ e, ∀ a, r.mul e a = a := by
  rintro ⟨e, he⟩
  obtain ⟨m, hm, hfm⟩ := Ideal.exists_le_maximal (Ideal.span {f})
    (fun h => hfu (Ideal.span_singleton_eq_top.1 h))
  let x : Spec R := (⟨m, hm.isPrime⟩ : PrimeSpectrum R)
  let c := K0.cls (koszulSupported hf i hi)
  have hc := mul_left_eq_zero_of_cls r.mul
    (fun a b d => @add_mul_of_toAddCommGroup_eq _ r _ hr a b d) c
    (fun A => (hmul A _).trans (cls_supportedPerfectTensorObj_koszulSupported hf i hi A))
  exact cls_koszulSupported_ne_zero hf i hi x (hfm (Ideal.subset_span rfl))
    ((he c).symm.trans (hc e))

end NoUnit

end AlgebraicGeometry.SupportedPerfectNoUnit

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

open SupportedPerfectNoUnit

/-- `ULift ℤ` has Krull dimension at most one. -/
theorem krullDimLE_one_uliftInt : Ring.KrullDimLE 1 (ULift.{u} ℤ) := by
  rw [Ring.krullDimLE_iff, ringKrullDim_eq_of_ringEquiv ULift.ringEquiv]
  exact Ring.krullDimLE_iff.1 inferInstance

/-- `2 ≠ 0` in `ULift ℤ`. -/
theorem two_ne_zero_uliftInt : (2 : ULift.{u} ℤ) ≠ 0 := fun h =>
  absurd (congrArg ULift.down h) (by decide)

/-- `2` is not a unit of `ULift ℤ`. -/
theorem not_isUnit_two_uliftInt : ¬ IsUnit (2 : ULift.{u} ℤ) := fun h =>
  absurd (h.map ULift.ringEquiv.toRingHom) (by decide)

/-- **In general `K₀(D_{Z, perf}(𝒪_X))` has no unit.** There are a scheme `X` and a closed
subscheme `Z` for which `K₀(D_{Z, perf}(𝒪_X))` carries a multiplication — a non-unital
commutative ring structure on its additive group whose product of two classes is the class of
the derived tensor product — and no multiplication of that kind has a unit. Here `X = Spec ℤ` and
`Z = Spec(ℤ/2)`; the general statement is
`AlgebraicGeometry.SupportedPerfectNoUnit.not_exists_unit`, for `V(f)` in the spectrum of any
Noetherian domain of dimension at most one and any nonzero nonunit `f`. -/
@[stacks 0FDN "in general `K_0(D_{Z, perf}(O_X))` has no unit: for `X = Spec ℤ` and \
`Z = Spec(ℤ/2)` the multiplication given by the derived tensor product exists, and no \
multiplication on `K_0(D_{Z, perf}(O_X))` distributive over its addition and computing the \
derived tensor product on classes has a unit"]
theorem exists_supportedPerfect_not_exists_unit :
    ∃ (X Z : Scheme.{u}) (i : Z ⟶ X) (_ : IsClosedImmersion i),
      (∃ r : NonUnitalCommRing (K0 (supportedPerfectDerivedCategory i)),
        r.toAddCommGroup = (inferInstance : AddCommGroup (K0 (supportedPerfectDerivedCategory i))) ∧
          ∀ K L : supportedPerfectDerivedCategory i,
            r.mul (K0.cls K) (K0.cls L) = K0.cls (supportedPerfectTensorObj i K L)) ∧
      ∀ r : NonUnitalCommRing (K0 (supportedPerfectDerivedCategory i)),
        r.toAddCommGroup = (inferInstance : AddCommGroup (K0 (supportedPerfectDerivedCategory i))) →
          (∀ K L : supportedPerfectDerivedCategory i,
            r.mul (K0.cls K) (K0.cls L) = K0.cls (supportedPerfectTensorObj i K L)) →
          ¬ ∃ e, ∀ a, r.mul e a = a :=
  have := isClosedImmersion_zeroLocusImmersion (R := CommRingCat.of (ULift.{u} ℤ)) 2
  have : IsDomain (ULift.{u} ℤ) := ULift.ringEquiv.toMulEquiv.isDomain
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have := krullDimLE_one_uliftInt.{u}
  ⟨_, _, zeroLocusImmersion (R := CommRingCat.of (ULift.{u} ℤ)) 2, inferInstance,
    exists_supportedPerfect_nonUnitalCommRing _,
    fun r hr hmul => not_exists_unit _ two_ne_zero_uliftInt not_isUnit_two_uliftInt
      (range_zeroLocusImmersion _) r hr hmul⟩

end AlgebraicGeometry
