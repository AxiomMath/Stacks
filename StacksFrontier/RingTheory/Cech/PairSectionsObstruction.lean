module

public import StacksFrontier.RingTheory.Cech.PairEvaluationInjectives
public import StacksFrontier.RingTheory.Cech.PairInjectiveResolution

/-!
# No resolution of the structure presheaf of pairs has good sections

Step 3 of the proof of [Stacks, Tag 099D] chooses an injective resolution `𝒪 ⟶ 𝒥•` of the
structure presheaf on the chaotically topologized category of presented pairs and then asserts
that `𝒥•(U)` is a resolution of `A` *by injective `A`-modules* at every object `U = (A, I)`,
which is what makes `ℱ•(U) = ⋃ₙ 𝒥•[ℐⁿ](U)` compute `RΓ_I(A)`. That assertion is refuted in
`StacksFrontier/RingTheory/Cech/PairEvaluationInjectives.lean`: evaluation at a pair does not
preserve injective objects.

The obvious repairs weaken the demand on `𝒥•` from "injective pair-modules" to "good sections",
which is all the rest of Step 3 uses. This file shows that **both repairs fail**: there is no
complex of pair-modules quasi-isomorphic to `𝒪[0]` whose sections at every pair are degreewise
injective, and none whose sections at every pair form a K-injective complex.

## The obstruction

Everything follows from one morphism and one divisibility argument. The pairs `(ℤ, 0)` and
`(ℤ/2, 0)` — `Stacks.PairSite.intPair` and `Stacks.PairSite.twoPair` — are joined by a unique
morphism `Stacks.PairSite.intToTwo`, and `2` is a nonzerodivisor of `ℤ` which dies in `ℤ/2`. An
injective module over the first ring is therefore divisible by `2`, and every additive map from
it to a module over the second ring vanishes. So the restriction map of a degreewise injective
complex of sections at `(ℤ, 0)` is zero, while a K-injective complex of sections at `(ℤ, 0)`
receives a map from an injective resolution of `ℤ[0]` — whose terms are divisible by `2` —
through which the augmentation factors up to homotopy. In both cases the augmentation cycle `1`
becomes a boundary at `(ℤ/2, 0)`, and a cycle of a resolution of `𝒪` is a boundary only if the
ring is zero: `ℤ/2` is not.

## Main results

* `CochainComplex.isZero_of_quasiIsoAt_single_of_eq_comp_d` — a quasi-isomorphism out of a
  complex concentrated in degree `j` whose degree-`j` component factors through a differential
  arriving in degree `j` forces that object to be zero.
* `CochainComplex.subsingleton_of_quasiIsoAt_single_self_of_boundary` — its module form: if the
  image of `1` under a resolution of `R[0]` is a boundary, the ring `R` is zero.
* `Stacks.PairSite.not_nonempty_homotopy_unitSections_comp_sectionsMap` — **the obstruction.**
  The augmentation of the sections at `(ℤ, 0)` of a resolution of `𝒪[0]`, followed by the
  restriction to `(ℤ/2, 0)`, is never null-homotopic.
* `Stacks.PairSite.not_forall_injective_value` — **the first repair fails** at every pair `P`
  admitting a morphism to a nonzero pair whose ring map kills a nonzerodivisor of `P.ring`: the
  sections there of a complex of pair-modules quasi-isomorphic to `𝒪[0]` are not injective
  modules in every degree. The witness `(ℤ, 0) ⟶ (ℤ/2, 0)` gives
  `Stacks.PairSite.not_forall_injective_value_intPair`, and its existential form is
  `Stacks.PairSite.not_exists_resolution_injective_value`.
* `Stacks.PairSite.not_isKInjective_sectionsComplex` — **the second repair fails** under the same
  hypotheses: the complex of sections at `P` is not K-injective. Likewise
  `Stacks.PairSite.not_isKInjective_sectionsComplex_intPair` and
  `Stacks.PairSite.not_exists_resolution_isKInjective_sections`.

## Implementation notes

The two refutations share `Stacks.PairSite.not_nonempty_homotopy_unitSections_comp_sectionsMap`,
whose proof reads the degree-zero component of a homotopy to zero as an element bounding the
augmentation cycle at `(ℤ/2, 0)`. The first repair produces the homotopy from an equality — the
restriction map is literally zero — and the second from
`CochainComplex.IsKInjective.exists_factorization_of_quasiIso` ([Stacks, Tag 013P]) applied to
an injective resolution of `ℤ[0]` over the ring of `(ℤ, 0)`.

No `@[stacks 099D]` attribute is attached: as with
`StacksFrontier/RingTheory/Cech/FunctorialCechFamilyObstruction.lean` and
`StacksFrontier/RingTheory/Cech/PairEvaluationInjectives.lean`, these are statements about what the
proof of the tag cannot be formalized by, not parts of the tag's statement.

## References

* [The Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [The Stacks Project, Tag 013P](https://stacks.math.columbia.edu/tag/013P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CochainComplex

/-- **A resolution of an object placed in one degree has nothing but zero in the image of a
differential.** If `ι` is a quasi-isomorphism in degree `j` from the complex with `M` in degree
`j` and the degree-`j` component of `ι` factors through a differential arriving in degree `j`,
then `M` is a zero object: the homology of the target in degree `j` is at the same time an
isomorphic image of `M` and killed by `ι`. -/
theorem isZero_of_quasiIsoAt_single_of_eq_comp_d {C : Type*} [Category C] [Abelian C] {M : C}
    {Y : CochainComplex C ℤ} {i j : ℤ}
    (ι : (HomologicalComplex.single C (ComplexShape.up ℤ) j).obj M ⟶ Y) [QuasiIsoAt ι j]
    (g : M ⟶ Y.X i)
    (hg : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) j M).inv ≫ ι.f j =
      g ≫ Y.d i j) : IsZero M := by
  have hcyc : (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) j M).inv ≫
      HomologicalComplex.cyclesMap ι j = g ≫ Y.toCycles i j := by
    rw [← cancel_mono (Y.iCycles j), Category.assoc, Category.assoc,
      HomologicalComplex.cyclesMap_i, HomologicalComplex.toCycles_i,
      HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc, hg]
  have h0 : HomologicalComplex.homologyMap ι j = 0 := by
    rw [← cancel_epi
        (((HomologicalComplex.single C (ComplexShape.up ℤ) j).obj M).homologyπ j),
      HomologicalComplex.homologyπ_naturality, comp_zero,
      ← cancel_epi (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) j M).inv,
      ← Category.assoc, hcyc, Category.assoc,
      HomologicalComplex.toCycles_comp_homologyπ, comp_zero, comp_zero]
  have hid : 𝟙 (((HomologicalComplex.single C (ComplexShape.up ℤ) j).obj M).homology j) = 0 := by
    rw [← cancel_mono (HomologicalComplex.homologyMap ι j)]
    simp [h0]
  exact IsZero.of_iso ((IsZero.iff_id_eq_zero _).2 hid)
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) j M).symm

/-- **The module form of the obstruction.** If the image of `1` under a quasi-isomorphism from
`R[0]` to a complex of `R`-modules is a boundary, the ring `R` is the zero ring. -/
theorem subsingleton_of_quasiIsoAt_single_self_of_boundary {R : Type u} [CommRing R]
    {Y : CochainComplex (ModuleCat.{u} R) ℤ} {i : ℤ}
    (ι : (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of R R) ⟶ Y) [QuasiIsoAt ι 0] (y : Y.X i)
    (hy : (ι.f 0) ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).inv (1 : R)) = (Y.d i 0) y) :
    Subsingleton R := by
  have key : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).inv ≫ ι.f 0 =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R (Y.X i) y) ≫ Y.d i 0 := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    have hx : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (ModuleCat.of R R)).inv x =
        x • (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (ModuleCat.of R R)).inv (1 : R) := by
      rw [← map_smul]
      congr 1
      simp
    calc ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (ModuleCat.of R R)).inv ≫ ι.f 0) x
        = (ι.f 0) (x • (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (ModuleCat.of R R)).inv (1 : R)) := by rw [ModuleCat.comp_apply, hx]
      _ = x • (Y.d i 0) y := by rw [map_smul, hy]
      _ = (Y.d i 0) (x • y) := (map_smul _ _ _).symm
      _ = (ModuleCat.ofHom (LinearMap.toSpanSingleton R (Y.X i) y) ≫ Y.d i 0) x := by
          rw [ModuleCat.comp_apply]
          rfl
  exact ModuleCat.isZero_iff_subsingleton.1
    (isZero_of_quasiIsoAt_single_of_eq_comp_d ι _ key)

end CochainComplex

namespace Stacks.PairSite

/-! ### Injective modules are divisible by a nonzerodivisor -/

/-- **An injective module is divisible by a nonzerodivisor of the ring**: multiplication by a
nonzerodivisor `a` is a monomorphism `R ⟶ R`, so a map `R ⟶ M` hitting `m` extends along it,
and the value of the extension at `1` is an `a`-th part of `m`. -/
theorem exists_smul_eq_of_injective {R : Type u} [CommRing R] {M : ModuleCat.{u} R}
    (hM : Injective M) {a : R} (ha : a ∈ nonZeroDivisors R) (m : M) :
    ∃ m' : M, a • m' = m := by
  have := hM
  have hmono : Mono (ModuleCat.ofHom (LinearMap.toSpanSingleton R R a)) := by
    rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    have hxy' : x * a = y * a := by
      simpa only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, smul_eq_mul] using hxy
    have h0 : (x - y) * a = 0 := by rw [sub_mul, hxy', sub_self]
    have hz := (mem_nonZeroDivisors_iff.1 ha).2 (x - y) h0
    rwa [sub_eq_zero] at hz
  obtain ⟨T, hT⟩ : ∃ T : ModuleCat.of R R ⟶ M,
      ModuleCat.ofHom (LinearMap.toSpanSingleton R R a) ≫ T =
        ModuleCat.ofHom (LinearMap.toSpanSingleton R M m) :=
    ⟨Injective.factorThru _ _, Injective.comp_factorThru _ _⟩
  have h1 := DFunLike.congr_fun (ModuleCat.hom_ext_iff.1 hT) (1 : R)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul, one_smul] at h1
  exact ⟨T (1 : R), (map_smul _ _ _).symm.trans (by rwa [smul_eq_mul, mul_one])⟩

/-- **`2` dies in the ring of `(ℤ/2, 0)`.** -/
theorem intToTwo_two : intToTwo.{u}.toRingHom (2 : (intPair.{u}).ring) = 0 := by
  rw [show (2 : (intPair.{u}).ring) =
    Ideal.Quotient.mk (⊥ : Ideal (presentationRing.{u} 0)) 2 from (map_ofNat _ 2).symm]
  show Ideal.Quotient.mk (Ideal.span {(2 : presentationRing.{u} 0)}) 2 = 0
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

/-- **A map out of an injective module to the sections at `P` dies on restriction along a
morphism of pairs killing a nonzerodivisor.** The source is divisible by that nonzerodivisor,
and the underlying ring map sends it to zero. -/
theorem comp_restriction_eq_zero_of_injective {M : PairModule.{u}} {P Q : Pair.{u}} (f : P ⟶ Q)
    {a : P.ring} (ha : a ∈ nonZeroDivisors P.ring) (ha0 : f.toRingHom a = 0)
    {N : ModuleCat.{u} P.ring} (hN : Injective N) (t : N ⟶ M.value P) :
    t ≫ M.restriction f = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun n => ?_)
  obtain ⟨n', hn'⟩ := exists_smul_eq_of_injective hN ha n
  have hsmul : M.restriction f (t n) = a • M.restriction f (t n') := by
    rw [← hn', map_smul, map_smul]
  rw [ModuleCat.comp_apply, hsmul, ModuleCat.restrictScalars.smul_def, ha0, zero_smul]
  rfl

/-! ### The augmentation of the sections of a resolution -/

/-- **The sections at a pair of a morphism of complexes of pair-modules.** This is
`StrictReplacement.sectionsFunctor` on morphisms, with the ring of the pair spelled as `P.ring`
rather than as the value of the structure presheaf of rings; the two are definitionally equal,
but only the former lets a tactic match the category. -/
abbrev sectionsOfMap {K L : CochainComplex PairModule.{u} ℤ} (α : K ⟶ L) (P : Pair.{u}) :
    sectionsComplex K P ⟶ sectionsComplex L P :=
  (StrictReplacement.sectionsFunctor structureRings.{u} P.ix).map α

/-- **The sections of a resolution `𝒪[0] ⟶ 𝒥•` at a pair**, read as a map out of the complex
with the pair's ring in degree zero. In degree zero it is the augmentation `A₀ ⟶ 𝒥⁰(A₀, I₀)`
whose value at `1` is the cycle that represents `1` in cohomology. -/
abbrev unitSections {J : CochainComplex PairModule.{u} ℤ} (ι : structureSingle.{u} ⟶ J)
    (P : Pair.{u}) :
    (HomologicalComplex.single (ModuleCat.{u} P.ring) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of P.ring P.ring) ⟶ sectionsComplex J P :=
  (sectionsStructureSingleIso P).inv ≫ sectionsOfMap ι P

/-- In degree zero, `unitSections ι P` sends `x : P.ring` to the value at `x` of the component
of `ι` at the pair `P`. -/
theorem unitSections_f_zero_apply {J : CochainComplex PairModule.{u} ℤ}
    (ι : structureSingle.{u} ⟶ J) (P : Pair.{u}) (x : P.ring) :
    (unitSections ι P).f 0 ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of P.ring P.ring)).inv x) =
      PresheafOfModules.Hom.app (ι.f 0) P.ix x :=
  rfl

/-- Evaluation at a pair is exact, so it carries a quasi-isomorphism of complexes of pair-modules
to a quasi-isomorphism of complexes of sections. -/
instance quasiIso_unitSections {J : CochainComplex PairModule.{u} ℤ}
    (ι : structureSingle.{u} ⟶ J) [QuasiIso ι] (P : Pair.{u}) :
    QuasiIso (unitSections ι P) := by
  have : (PresheafOfModules.evaluation.{u} structureRings.{u} P.ix).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have hmap : QuasiIso (sectionsOfMap ι P) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology ι
      (PresheafOfModules.evaluation.{u} structureRings.{u} P.ix)
  exact quasiIso_comp _ _

/-! ### The obstruction -/

/-- **The obstruction.** Let `𝒪[0] ⟶ 𝒥•` be any quasi-isomorphism of complexes of pair-modules
and let `f : P ⟶ Q` be a morphism of pairs with `Q` not the zero ring. Then the augmentation of
the sections of `𝒥•` at `P`, followed by the restriction map along `f`, is not null-homotopic.

A null-homotopy exhibits the image of `1` at `Q` as a boundary, and then
`CochainComplex.subsingleton_of_quasiIsoAt_single_self_of_boundary` makes the ring of `Q` the
zero ring. -/
theorem not_nonempty_homotopy_unitSections_comp_sectionsMap
    {J : CochainComplex PairModule.{u} ℤ} (ι : structureSingle.{u} ⟶ J) [QuasiIso ι]
    {P Q : Pair.{u}} (f : P ⟶ Q) [Nontrivial Q.ring] :
    ¬ Nonempty (Homotopy (unitSections ι P ≫ sectionsMap J f) 0) := by
  rintro ⟨h⟩
  have hcomm := h.comm 0
  rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel 0 1 by simp),
    prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)] at hcomm
  simp only [HomologicalComplex.single_obj_d, zero_comp, zero_add, HomologicalComplex.zero_f,
    add_zero] at hcomm
  -- the element produced by the homotopy, bounding the augmentation cycle at `Q`
  have happ := DFunLike.congr_fun (ModuleCat.hom_ext_iff.1 hcomm)
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (ModuleCat.of P.ring P.ring)).inv (1 : P.ring))
  have hnat := PairModule.naturality_apply (ι.f 0) f (1 : P.ring)
  have h1 : (structureSingle.{u}.X 0).restriction f (1 : P.ring) = (1 : Q.ring) :=
    map_one f.toRingHom
  rw [h1] at hnat
  refine (not_subsingleton Q.ring)
    (CochainComplex.subsingleton_of_quasiIsoAt_single_self_of_boundary (unitSections ι Q)
      (h.hom 0 (-1) ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of P.ring P.ring)).inv (1 : P.ring)))
      ?_)
  rw [unitSections_f_zero_apply, hnat]
  exact happ

/-! ### The two repairs fail at every pair admitting a morphism killing a nonzerodivisor -/

/-- If the augmentation at `P` is homotopic to a map factoring through a complex of injective
modules, restricting along a morphism `f` killing a nonzerodivisor makes it null-homotopic, which
the obstruction forbids. -/
private theorem false_of_homotopy_comp_of_injective {J : CochainComplex PairModule.{u} ℤ}
    (ι : structureSingle.{u} ⟶ J) [QuasiIso ι] {P Q : Pair.{u}} (f : P ⟶ Q) [Nontrivial Q.ring]
    {a : P.ring} (ha : a ∈ nonZeroDivisors P.ring) (ha0 : f.toRingHom a = 0)
    {K : CochainComplex (ModuleCat.{u} P.ring) ℤ} (hK : ∀ n, Injective (K.X n))
    (γ : (HomologicalComplex.single (ModuleCat.{u} P.ring) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of P.ring P.ring) ⟶ K) (β : K ⟶ sectionsComplex J P)
    (h : Homotopy (unitSections ι P) (γ ≫ β)) : False := by
  have hzero : β ≫ sectionsMap J f = 0 := by
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    rw [HomologicalComplex.comp_f, sectionsMap_f, HomologicalComplex.zero_f]
    exact comp_restriction_eq_zero_of_injective f ha ha0 (hK n) (β.f n)
  exact not_nonempty_homotopy_unitSections_comp_sectionsMap ι f
    ⟨(h.compRight (sectionsMap J f)).trans
      (Homotopy.ofEq (by rw [Category.assoc, hzero, comp_zero]))⟩

/-- **The sections of a resolution of `𝒪[0]` at `P` are not degreewise injective**, as soon as
`P` admits a morphism to a nonzero pair whose ring map kills a nonzerodivisor of `P.ring`. This
is the weakening of the refuted step of [Stacks, Tag 099D] that asks only for the *sections* of
`𝒥•` to be injective modules, rather than for `𝒥•` itself to consist of injective pair-modules;
it is unavailable too.

Injective modules over `P.ring` are divisible by the nonzerodivisor, so the restriction map
along `f` is zero in every degree, and the augmentation cycle becomes a boundary at `Q`. -/
theorem not_forall_injective_value {J : CochainComplex PairModule.{u} ℤ}
    (ι : structureSingle.{u} ⟶ J) [QuasiIso ι] {P Q : Pair.{u}} (f : P ⟶ Q) [Nontrivial Q.ring]
    {a : P.ring} (ha : a ∈ nonZeroDivisors P.ring) (ha0 : f.toRingHom a = 0) :
    ¬ ∀ n : ℤ, Injective ((J.X n).value P) := by
  intro hinj
  exact false_of_homotopy_comp_of_injective ι f ha ha0 hinj (unitSections ι P) (𝟙 _)
    (Homotopy.ofEq (by rw [Category.comp_id]))

/-- **The sections of a resolution of `𝒪[0]` at `P` are not a K-injective complex**, as soon as
`P` admits a morphism to a nonzero pair whose ring map kills a nonzerodivisor of `P.ring`. This
is the weakest form of the refuted step of [Stacks, Tag 099D] that still lets `ℱ•(U)` compute
`RΓ_I(A)`: the sections are not asked to be degreewise injective, only to be K-injective as a
complex. It is unavailable as well.

The proof factors the augmentation at `P` through an injective resolution of `P.ring[0]` — which
K-injectivity of the sections permits, by [Stacks, Tag 013P] — and the terms of that resolution
are divisible by the nonzerodivisor, so the restriction map along `f` kills the factorization. -/
theorem not_isKInjective_sectionsComplex {J : CochainComplex PairModule.{u} ℤ}
    (ι : structureSingle.{u} ⟶ J) [QuasiIso ι] {P Q : Pair.{u}} (f : P ⟶ Q) [Nontrivial Q.ring]
    {a : P.ring} (ha : a ∈ nonZeroDivisors P.ring) (ha0 : f.toRingHom a = 0) :
    ¬ (sectionsComplex J P).IsKInjective := by
  intro hKI
  have := hKI
  obtain ⟨Res, -, -⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE (0 : ℤ)
    ((HomologicalComplex.single (ModuleCat.{u} P.ring) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of P.ring P.ring))
  obtain ⟨β, ⟨hβ⟩⟩ := (CochainComplex.IsKInjective.exists_factorization_of_quasiIso Res.ι
    (unitSections ι P)).1
  exact false_of_homotopy_comp_of_injective ι f ha ha0 Res.injective Res.ι β hβ.symm

/-- **The sections at `(ℤ, 0)` of a resolution of `𝒪[0]` are not degreewise injective**: the
witness is the reduction `(ℤ, 0) ⟶ (ℤ/2, 0)`, `2` being a nonzerodivisor of `ℤ` which dies in
`ℤ/2`. -/
theorem not_forall_injective_value_intPair {J : CochainComplex PairModule.{u} ℤ}
    (ι : structureSingle.{u} ⟶ J) [QuasiIso ι] :
    ¬ ∀ n : ℤ, Injective ((J.X n).value intPair.{u}) :=
  not_forall_injective_value ι intToTwo.{u} two_mem_nonZeroDivisors_intPair.{u} intToTwo_two.{u}

/-- **The sections at `(ℤ, 0)` of a resolution of `𝒪[0]` are not a K-injective complex**, by the
same witness. -/
theorem not_isKInjective_sectionsComplex_intPair {J : CochainComplex PairModule.{u} ℤ}
    (ι : structureSingle.{u} ⟶ J) [QuasiIso ι] :
    ¬ (sectionsComplex J intPair.{u}).IsKInjective :=
  not_isKInjective_sectionsComplex ι intToTwo.{u} two_mem_nonZeroDivisors_intPair.{u}
    intToTwo_two.{u}

/-- **A resolution of `𝒪[0]` by pair-modules with injective modules of sections does not
exist**, the first repair of the refuted step of [Stacks, Tag 099D] in the form in which it
would have been used. -/
theorem not_exists_resolution_injective_value :
    ¬ ∃ (J : CochainComplex PairModule.{u} ℤ) (ι : structureSingle.{u} ⟶ J), QuasiIso ι ∧
      ∀ (P : Pair.{u}) (n : ℤ), Injective ((J.X n).value P) := by
  rintro ⟨J, ι, hι, hinj⟩
  have := hι
  exact not_forall_injective_value_intPair ι (hinj intPair.{u})

/-- **A resolution of `𝒪[0]` by pair-modules with K-injective complexes of sections does not
exist**, the second repair of the refuted step of [Stacks, Tag 099D] in the form in which it
would have been used. -/
theorem not_exists_resolution_isKInjective_sections :
    ¬ ∃ (J : CochainComplex PairModule.{u} ℤ) (ι : structureSingle.{u} ⟶ J), QuasiIso ι ∧
      ∀ P : Pair.{u}, (sectionsComplex J P).IsKInjective := by
  rintro ⟨J, ι, hι, hKI⟩
  have := hι
  exact not_isKInjective_sectionsComplex_intPair ι (hKI intPair.{u})

end Stacks.PairSite

end
