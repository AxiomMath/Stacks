module

public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.ContractionCocycle
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulStrictPerfection
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexCohomologyProduct

/-!
# The coordinate contractions as degree-one classes of the self-Ext algebra

Let `(X, O♯)` be a ringed space, let `φ : (O♯)ʳ ⟶ O♯` be a morphism of sheaves of modules and
let `K` be a Koszul chain complex of `φ`. Read as a cochain complex, `K` is a strictly perfect
complex, and the cohomology sheaves of its internal endomorphism complex `SheafHom^•(K, K)`
carry the composition product of
`Stacks.SheafOfModules.homologyGradedAlgebra`; when `K` resolves the quotient `O♯/I` these
cohomology sheaves are the self-Ext sheaves of the quotient.

A contraction `δⱼ` by a coordinate functional anticommutes with the differential of `K`, so the
family of its components is a degree-one **cocycle** of `SheafHom^•(K, K)` and defines a global
section of `H¹(SheafHom(K, K))`. This file constructs those classes and proves the two
identities among their products that the Koszul relations give:

`[δⱼ] [δₖ] + [δₖ] [δⱼ] = 0` and `[δⱼ] [δⱼ] = 0`.

Both hold **at the level of cocycles**, before passing to cohomology: contraction by two
coordinate functionals anticommutes and the square of a single contraction vanishes, each as an
identity of morphisms of sheaves of modules. The consequence drawn here is that an arbitrary
`O♯`-linear combination of the classes `[δⱼ]` has square zero: the diagonal terms die by the
second identity and the off-diagonal ones cancel in pairs by the first. Over a general base this
is strictly stronger than what graded commutativity of the product gives, which is only that
twice the square vanishes.

## Main definitions

* `Stacks.RegularSequence.KoszulChainData.contractionCochain` and `contractionSection`: the
  family of components of `δⱼ`, as a degree-one cochain of the restriction of `K` to the site
  over an open set and as a local section of the degree-one term of `SheafHom^•(K, K)`.
* `Stacks.RegularSequence.KoszulChainData.contractionCycle`: **`δⱼ` as a global cocycle** of
  `SheafHom^•(K, K)`, in the form of a morphism from the unit sheaf of modules into the
  degree-one cycles.
* `Stacks.RegularSequence.KoszulChainData.contractionClassOn` and `contractionClass`: **the
  cohomology class of `δⱼ`**, as a local section of `H¹(SheafHom(K, K))` over an open set and as
  a global section.

## Main results

* `Stacks.RegularSequence.KoszulChainData.d_contractionSection`: **`δⱼ` is a cocycle**, which is
  its anticommutation with the differential of `K`.
* `Stacks.RegularSequence.KoszulChainData.compositionSection_contraction_self` and
  `compositionSection_contraction_add_swap`: **the two Koszul identities at the level of
  cocycles**, `δⱼ δⱼ = 0` and `δⱼ δₖ + δₖ δⱼ = 0`.
* `Stacks.RegularSequence.KoszulChainData.homologyMul_contractionClass_self` and
  `homologyMul_contractionClass_add_swap`: the same two identities for the composition product
  on cohomology.
* `Stacks.RegularSequence.KoszulChainData.homologyMul_contraction_combination`: **an
  `O♯`-linear combination of the classes `[δⱼ]` has square zero.**

## Implementation notes

**Where the cochain lives.** A degree-`n` local section of an internal Hom complex over `U` is,
by the characterisation `AlgebraicGeometry.RingedSite.SheafHomComplex.sectionsEquiv`, a
degree-`n` cochain from the restriction of the source to the site over `U` to the restriction of
the target. The components of `δⱼ` are morphisms of sheaves of modules on the whole space, so
the cochain is their restriction to the slice, and restriction to a slice is an additive functor
preserving composition; the cocycle identity and both product identities are therefore the
corresponding identities of the unrestricted morphisms with that functor applied, with no sign
and no transport. The degrees are the ones of the cochain complex reading of `K`, in which the
degree-`n` term is the exterior power of degree `-n`.

**Why the classes are produced as morphisms out of the unit sheaf.** A global section of a sheaf
of modules is the same thing as a morphism from the unit sheaf of modules, and in that form the
cycle is produced by the morphism-level `HomologicalComplex.liftCycles` rather than sectionwise;
this is the device `Stacks.SheafOfModules.oneCycle` uses for the unit of the algebra, and it is
what makes the class available over every open set at once.

**How the double sum cancels.** The square of a combination `Σⱼ aⱼ [δⱼ]` expands, by bilinearity
of the product, into a sum over pairs of indices of `aⱼ aₖ [δⱼ][δₖ]`. Transposition is an
involution of the index pairs which fixes exactly the diagonal; the diagonal terms vanish by the
squaring identity and a transposed pair cancels by the anticommutation identity, because the
ring of sections is commutative. This is `Finset.sum_ninvolution` at `Prod.swap`.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry HomologicalComplex CochainComplex.HomComplex
open Stacks.ChainComplex Stacks.SheafOfModules

universe u

namespace Stacks.RegularSequence.KoszulChainData

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {r : ℕ}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Rc r)}
  {φ : koszulFreeSheaf Rc r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Rc)}
  (K : KoszulChainData.{u, u, u} A φ)

/-- The internal Hom complex of the Koszul cochain complex into itself. -/
noncomputable abbrev endHom :
    RingedSite.SheafHomComplex (ringedSite Rc) (cochain Rc K) (cochain Rc K) :=
  RingedSite.sheafHomComplex (ringedSite Rc) (cochain Rc K) (cochain Rc K)

/-- **The degree-one cochain of the contraction `δⱼ`**, over an open set `U`: in each pair of
adjacent degrees it is the component of `δⱼ` there, restricted to the site over `U`. The
degree-`n` term of the cochain complex reading of the Koszul complex is its exterior power of
degree `-n`, so the component from degree `p` to degree `p + 1` is the contraction from exterior
degree `-p` to exterior degree `-p - 1`. -/
noncomputable def contractionCochain (j : ULift.{u} (Fin r)) (U : Opens ↥X) :
    Cochain (RingedSite.restrictComplex (ringedSite Rc) (cochain Rc K) U)
      (RingedSite.restrictComplex (ringedSite Rc) (cochain Rc K) U) 1 :=
  Cochain.mk fun p q hpq =>
    SheafOfModules.Hom.over (K.coordKoszulD j (show -q + 1 = -p by omega)) U

/-- **The contraction `δⱼ` as a degree-one local section of `SheafHom^•(K, K)`** over an open
set, namely the section naming its cochain. -/
noncomputable def contractionSection (j : ULift.{u} (Fin r)) (U : Opens ↥X) :
    ((endComplex Rc (cochain Rc K)).X 1).val.obj (op U) :=
  ((endHom Rc K).sectionsEquiv U 1).symm (contractionCochain Rc K j U)

/-- The cochain named by the contraction section is the contraction cochain. -/
theorem sectionsEquiv_contractionSection (j : ULift.{u} (Fin r)) (U : Opens ↥X) :
    (endHom Rc K).sectionsEquiv U 1 (contractionSection Rc K j U) =
      contractionCochain Rc K j U :=
  ((endHom Rc K).sectionsEquiv U 1).apply_symm_apply _

/-- **Evaluating the contraction section returns the contraction of the section it is applied
to.** This is the only description of the section a computation needs. -/
theorem applyHomSectionOver_contractionSection (j : ULift.{u} (Fin r)) (U V : Opens ↥X)
    (i : V ⟶ U) (p q : ℤ) (hpq : p + 1 = q)
    (x : ((cochain Rc K).X p).val.obj (op V)) :
    RingedSite.applyHomSectionOver (ringedSite Rc) (endHom Rc K) U V i 1 p q hpq
        (contractionSection Rc K j U) x =
      (K.coordKoszulD j (show -q + 1 = -p by omega)).val.app (op V) x := by
  show (((endHom Rc K).sectionsEquiv U 1 (contractionSection Rc K j U)).v p q hpq).val.app
      (op (Over.mk i)) x = _
  rw [sectionsEquiv_contractionSection]
  rfl

/-- **The contraction section is compatible with restriction**, so the sections over all the open
sets assemble into a global section of the degree-one term of `SheafHom^•(K, K)`. Its components
are morphisms of sheaves of modules on the whole space, so evaluating it over an object of a
slice site does not depend on which slice the section is taken in. -/
theorem contractionSection_restrict (j : ULift.{u} (Fin r)) {U V : Opens ↥X} (g : V ⟶ U) :
    ((endComplex Rc (cochain Rc K)).X 1).val.map g.op (contractionSection Rc K j U) =
      contractionSection Rc K j V := by
  refine RingedSite.homSection_ext (ringedSite Rc) (endHom Rc K) V 1 ?_
  intro p q hpq W i x
  exact (RingedSite.applyHomSectionOver_restrict_comp (ringedSite Rc) (endHom Rc K)
    U V W g i 1 p q hpq (contractionSection Rc K j U) x).symm.trans
      ((applyHomSectionOver_contractionSection Rc K j U W (i ≫ g) p q hpq x).trans
        (applyHomSectionOver_contractionSection Rc K j V W i p q hpq x).symm)

/-- **The contraction section is a cocycle.** The differential of an internal Hom complex is the
Hom-complex differential, whose value on a degree-one cochain is the sum of its two composites
with the differential of the complex; that sum vanishes because `δⱼ` anticommutes with the
differential of the Koszul complex. -/
theorem d_contractionSection (j : ULift.{u} (Fin r)) (U : Opens ↥X) :
    ((endComplex Rc (cochain Rc K)).d 1 2).val.app (op U) (contractionSection Rc K j U) = 0 := by
  refine ((endHom Rc K).sectionsEquiv U 2).injective ?_
  rw [(endHom Rc K).sectionsEquiv_d U 1 2 (contractionSection Rc K j U),
    sectionsEquiv_contractionSection, map_zero]
  refine Cochain.ext _ _ fun p q hpq => ?_
  obtain rfl : q = p + 2 := by omega
  rw [δ_v 1 2 rfl _ p (p + 2) (by omega) (p + 1) (p + 1) (by omega) rfl, Cochain.zero_v]
  have h2 : (2 : ℤ).negOnePow = 1 := by decide
  have key : K.coordKoszulD j (show -(p + 1) + 1 = -p by omega)
        ≫ K.chain.d (-(p + 1)) (-(p + 2))
      + K.chain.d (-p) (-(p + 1)) ≫ K.coordKoszulD j (show -(p + 2) + 1 = -(p + 1) by omega)
      = 0 := by
    rw [K.coordKoszulD_comp_chain_d_comm j (show -(p + 1) + 1 = -p by omega)
      (show -(p + 2) + 1 = -(p + 1) by omega), neg_add_cancel]
  simp only [h2, one_smul]
  exact congrArg
    (fun z => (SheafOfModules.overFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U).map z) key

/-- **The contraction `δⱼ` as a global section of the degree-one term of `SheafHom^•(K, K)`**,
assembled from its sections over all the open sets. -/
noncomputable def contractionSections (j : ULift.{u} (Fin r)) :
    ((endComplex Rc (cochain Rc K)).X 1).sections :=
  PresheafOfModules.sectionsMk (fun U => contractionSection Rc K j U.unop)
    (fun {_ _} f => contractionSection_restrict Rc K j f.unop)

/-- **The contraction `δⱼ` as a morphism from the unit sheaf of modules into the degree-one term
of `SheafHom^•(K, K)`.** A global section of a sheaf of modules is the same thing as such a
morphism; passing to the morphism is what lets the cycle below be produced by the morphism-level
`HomologicalComplex.liftCycles` rather than sectionwise. -/
noncomputable def contractionMor (j : ULift.{u} (Fin r)) :
    SheafOfModules.unit ((Tensor.ringSheaf (ringedSite Rc).O)) ⟶
      (endComplex Rc (cochain Rc K)).X 1 :=
  ((endComplex Rc (cochain Rc K)).X 1).unitHomEquiv.symm (contractionSections Rc K j)

/-- The morphism of the contraction takes the unit section to the contraction section. -/
theorem contractionMor_val_app_one (j : ULift.{u} (Fin r)) (U : (Opens ↥X)ᵒᵖ) :
    (contractionMor Rc K j).val.app U (1 : ((Tensor.ringSheaf (ringedSite Rc).O)).obj.obj U) =
      contractionSection Rc K j U.unop :=
  congrFun (congrArg Subtype.val
    (((endComplex Rc (cochain Rc K)).X 1).unitHomEquiv.apply_symm_apply
      (contractionSections Rc K j))) U

/-- **The morphism of the contraction is killed by the differential**, which is the cocycle
identity read on the unit section. -/
theorem contractionMor_comp_d (j : ULift.{u} (Fin r)) :
    contractionMor Rc K j ≫ (endComplex Rc (cochain Rc K)).d 1 2 = 0 := by
  refine ((endComplex Rc (cochain Rc K)).X 2).unitHomEquiv.injective ?_
  refine PresheafOfModules.sections_ext _ _ fun U => ?_
  show ((endComplex Rc (cochain Rc K)).d 1 2).val.app U
    ((contractionMor Rc K j).val.app U (1 : ((Tensor.ringSheaf (ringedSite Rc).O)).obj.obj U)) = _
  rw [contractionMor_val_app_one, d_contractionSection]
  rfl

/-- **The contraction `δⱼ` as a global degree-one cocycle of `SheafHom^•(K, K)`**: the morphism
of the contraction, lifted through the inclusion of the degree-one cycles. -/
noncomputable def contractionCycle (j : ULift.{u} (Fin r)) :
    SheafOfModules.unit ((Tensor.ringSheaf (ringedSite Rc).O)) ⟶
      (endComplex Rc (cochain Rc K)).cycles 1 :=
  (endComplex Rc (cochain Rc K)).liftCycles (contractionMor Rc K j) 2 (by simp)
    (contractionMor_comp_d Rc K j)

/-- The cycle of the contraction is, inside the complex, the contraction section. -/
theorem iCycles_contractionCycle (j : ULift.{u} (Fin r)) (U : (Opens ↥X)ᵒᵖ) :
    (((endComplex Rc (cochain Rc K)).iCycles 1).val.app U)
        ((contractionCycle Rc K j).val.app U
          (1 : ((Tensor.ringSheaf (ringedSite Rc).O)).obj.obj U)) =
      contractionSection Rc K j U.unop :=
  (congrArg (fun z => (SheafOfModules.Hom.val z).app U
      (1 : ((Tensor.ringSheaf (ringedSite Rc).O)).obj.obj U))
    ((endComplex Rc (cochain Rc K)).liftCycles_i (contractionMor Rc K j) 2 (by simp)
      (contractionMor_comp_d Rc K j))).trans (contractionMor_val_app_one Rc K j U)

/-- **The cohomology class of the contraction `δⱼ`**, as a local section of
`H¹(SheafHom(K, K))` over an open set. For a Koszul complex resolving `O♯/I` this is a local
section of the first self-Ext sheaf of the quotient. -/
noncomputable def contractionClassOn (j : ULift.{u} (Fin r)) (U : (Opens ↥X)ᵒᵖ) :
    ((endComplex Rc (cochain Rc K)).homology 1).val.obj U :=
  (((endComplex Rc (cochain Rc K)).homologyπ 1).val.app U)
    ((contractionCycle Rc K j).val.app U (1 : ((Tensor.ringSheaf (ringedSite Rc).O)).obj.obj U))

/-- **The cohomology class of the contraction `δⱼ` as a global section of
`H¹(SheafHom(K, K))`.** -/
noncomputable def contractionClass (j : ULift.{u} (Fin r)) :
    ((endComplex Rc (cochain Rc K)).homology 1).sections :=
  ((endComplex Rc (cochain Rc K)).homology 1).unitHomEquiv
    (contractionCycle Rc K j ≫ (endComplex Rc (cochain Rc K)).homologyπ 1)

/-- The global class of the contraction is its class over each open set. -/
theorem contractionClass_val (j : ULift.{u} (Fin r)) (U : (Opens ↥X)ᵒᵖ) :
    (contractionClass Rc K j).val U = contractionClassOn Rc K j U :=
  rfl

/-- The components of the composite of two contraction sections are the composites of the
components. -/
private theorem sectionsEquiv_compositionSection_contraction_v (j k : ULift.{u} (Fin r))
    (U : Opens ↥X) (p : ℤ) :
    (((endHom Rc K).sectionsEquiv U 2) (RingedSite.compositionSection (ringedSite Rc) U 1 1 2 rfl
        (contractionSection Rc K j U) (contractionSection Rc K k U))).v p (p + 2) rfl =
      (SheafOfModules.overFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U).map
        (K.coordKoszulD k (show -(p + 1) + 1 = -p by omega) ≫
          K.coordKoszulD j (show -(p + 2) + 1 = -(p + 1) by omega)) := by
  refine (congrArg (fun z => z.v p (p + 2) rfl) (RingedSite.compositionSection_cochain
    (ringedSite Rc) U 1 1 2 rfl (contractionSection Rc K j U)
      (contractionSection Rc K k U))).trans ?_
  refine (congrArg₂ (fun left right =>
    (Cochain.comp left right (show (1 : ℤ) + 1 = 2 by omega)).v p (p + 2) rfl)
    (sectionsEquiv_contractionSection Rc K k U)
    (sectionsEquiv_contractionSection Rc K j U)).trans ?_
  rw [Cochain.comp_v _ _ (show (1 : ℤ) + 1 = 2 by omega) p (p + 1) (p + 2) rfl (by omega)]
  rfl

/-- **The composite of the contraction section with itself vanishes**, before passing to
cohomology: the square of a single coordinate contraction is zero. -/
theorem compositionSection_contraction_self (j : ULift.{u} (Fin r)) (U : Opens ↥X) :
    RingedSite.compositionSection (ringedSite Rc) U 1 1 2 rfl
        (contractionSection Rc K j U) (contractionSection Rc K j U) = 0 := by
  refine ((endHom Rc K).sectionsEquiv U 2).injective ?_
  refine Eq.trans ?_ (map_zero _).symm
  refine Cochain.ext _ _ fun p q hpq => ?_
  obtain rfl : q = p + 2 := by omega
  rw [Cochain.zero_v]
  refine (sectionsEquiv_compositionSection_contraction_v Rc K j j U p).trans ?_
  exact congrArg (fun z => (SheafOfModules.overFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U).map z)
    (K.coordKoszulD_comp_coordKoszulD_self j (show -(p + 1) + 1 = -p by omega)
      (show -(p + 2) + 1 = -(p + 1) by omega))

/-- **The two composites of the contraction sections of two coordinate functionals cancel**,
before passing to cohomology: contraction by two coordinate functionals anticommutes. -/
theorem compositionSection_contraction_add_swap (j k : ULift.{u} (Fin r)) (U : Opens ↥X) :
    RingedSite.compositionSection (ringedSite Rc) U 1 1 2 rfl
        (contractionSection Rc K j U) (contractionSection Rc K k U) +
      RingedSite.compositionSection (ringedSite Rc) U 1 1 2 rfl
        (contractionSection Rc K k U) (contractionSection Rc K j U) = 0 := by
  refine ((endHom Rc K).sectionsEquiv U 2).injective ?_
  refine (map_add _ _ _).trans (Eq.trans ?_ (map_zero _).symm)
  refine Cochain.ext _ _ fun p q hpq => ?_
  obtain rfl : q = p + 2 := by omega
  have key : K.coordKoszulD k (show -(p + 1) + 1 = -p by omega)
        ≫ K.coordKoszulD j (show -(p + 2) + 1 = -(p + 1) by omega)
      + K.coordKoszulD j (show -(p + 1) + 1 = -p by omega)
        ≫ K.coordKoszulD k (show -(p + 2) + 1 = -(p + 1) by omega) = 0 := by
    rw [K.coordKoszulD_comp_coordKoszulD_comm j k (show -(p + 1) + 1 = -p by omega)
      (show -(p + 2) + 1 = -(p + 1) by omega), neg_add_cancel]
  rw [Cochain.add_v, Cochain.zero_v]
  refine (congrArg₂ (fun left right => left + right)
    (sectionsEquiv_compositionSection_contraction_v Rc K j k U p)
    (sectionsEquiv_compositionSection_contraction_v Rc K k j U p)).trans ?_
  exact congrArg (fun z => (SheafOfModules.overFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O) U).map z) key

attribute [local instance] RingedSite.ringSheafSectionsCommRing

/-- The product of the classes of two contractions is the class of a cycle whose underlying
section is the composite of the two contraction sections. -/
private theorem exists_cycle_homologyMul_contractionClassOn (j k : ULift.{u} (Fin r))
    (W : Opens ↥X) :
    ∃ c : ((endComplex Rc (cochain Rc K)).cycles (1 + 1)).val.obj (op W),
      (homologyMul Rc (cochain Rc K) (cochain Rc K) (cochain Rc K) 1 1).app (op W)
          (contractionClassOn Rc K j (op W)) (contractionClassOn Rc K k (op W)) =
        ((endComplex Rc (cochain Rc K)).homologyπ (1 + 1)).val.app (op W) c ∧
      (((endComplex Rc (cochain Rc K)).iCycles (1 + 1)).val.app (op W)) c =
        RingedSite.compositionSection (ringedSite Rc) W 1 1 2 rfl
          (contractionSection Rc K j W) (contractionSection Rc K k W) :=
  ⟨_, homologyMul_app_homologyπ Rc (cochain Rc K) (cochain Rc K) (cochain Rc K) 1 1 W _ _,
    (iCycles_cycleComposition_pureSection Rc (cochain Rc K) (cochain Rc K) (cochain Rc K)
      1 1 W _ _).trans (congrArg₂ (RingedSite.compositionSection (ringedSite Rc) W 1 1 2 rfl)
        (iCycles_contractionCycle Rc K j (op W)) (iCycles_contractionCycle Rc K k (op W)))⟩

/-- **The square of the class of a contraction is zero** for the composition product on the
cohomology of `SheafHom^•(K, K)`. The product of two classes of cocycles is the class of their
cycle-level composite, and that composite is zero. -/
theorem homologyMul_contractionClass_self (j : ULift.{u} (Fin r)) (W : Opens ↥X) :
    (homologyMul Rc (cochain Rc K) (cochain Rc K) (cochain Rc K) 1 1).app (op W)
        (contractionClassOn Rc K j (op W)) (contractionClassOn Rc K j (op W)) = 0 := by
  obtain ⟨c, hc, hic⟩ := exists_cycle_homologyMul_contractionClassOn Rc K j j W
  obtain rfl : c = 0 := injective_app_of_mono ((endComplex Rc (cochain Rc K)).iCycles (1 + 1))
    (op W) (hic.trans ((compositionSection_contraction_self Rc K j W).trans (map_zero _).symm))
  rw [hc, map_zero]

/-- **The classes of two contractions anticommute** for the composition product on the cohomology
of `SheafHom^•(K, K)`. -/
theorem homologyMul_contractionClass_add_swap (j k : ULift.{u} (Fin r)) (W : Opens ↥X) :
    (homologyMul Rc (cochain Rc K) (cochain Rc K) (cochain Rc K) 1 1).app (op W)
        (contractionClassOn Rc K j (op W)) (contractionClassOn Rc K k (op W)) +
      (homologyMul Rc (cochain Rc K) (cochain Rc K) (cochain Rc K) 1 1).app (op W)
        (contractionClassOn Rc K k (op W)) (contractionClassOn Rc K j (op W)) = 0 := by
  obtain ⟨c, hc, hic⟩ := exists_cycle_homologyMul_contractionClassOn Rc K j k W
  obtain ⟨d, hd, hid⟩ := exists_cycle_homologyMul_contractionClassOn Rc K k j W
  have hcd : c + d = 0 := injective_app_of_mono ((endComplex Rc (cochain Rc K)).iCycles (1 + 1))
    (op W) ((map_add _ _ _).trans ((congrArg₂ (· + ·) hic hid).trans
      ((compositionSection_contraction_add_swap Rc K j k W).trans (map_zero _).symm)))
  rw [hc, hd, ← map_add, hcd, map_zero]

/-- **The square of a combination of classes expands into a double sum over pairs of indices**,
by bilinearity of the composition product. -/
theorem homologyMul_sum_expand (W : Opens ↥X)
    (a : ULift.{u} (Fin r) → ((Tensor.ringSheaf (ringedSite Rc).O)).obj.obj (op W))
    (x : ULift.{u} (Fin r) → ((endComplex Rc (cochain Rc K)).homology 1).val.obj (op W)) :
    (homologyMul Rc (cochain Rc K) (cochain Rc K) (cochain Rc K) 1 1).app (op W)
        (∑ j, a j • x j) (∑ j, a j • x j)
      = ∑ jk : ULift.{u} (Fin r) × ULift.{u} (Fin r), (a jk.1 * a jk.2) •
          (homologyMul Rc (cochain Rc K) (cochain Rc K) (cochain Rc K) 1 1).app (op W)
            (x jk.1) (x jk.2) := by
  classical
  have hout : ∀ t : ((endComplex Rc (cochain Rc K)).homology 1).val.obj (op W),
      (homologyMul Rc (cochain Rc K) (cochain Rc K) (cochain Rc K) 1 1).app (op W)
          (∑ j, a j • x j) t
        = ∑ j, a j •
            (homologyMul Rc (cochain Rc K) (cochain Rc K) (cochain Rc K) 1 1).app (op W)
              (x j) t := fun t => by
    rw [DFunLike.congr_fun (map_sum
      ((homologyMul Rc (cochain Rc K) (cochain Rc K) (cochain Rc K) 1 1).app (op W))
      (fun j => a j • x j) Finset.univ) t, AddMonoidHom.finsetSum_apply]
    exact Finset.sum_congr rfl fun j _ =>
      (homologyMul Rc (cochain Rc K) (cochain Rc K) (cochain Rc K) 1 1).map_smul_left _ _ _ _
  refine (hout _).trans ?_
  refine Eq.trans ?_ (Fintype.sum_prod_type _).symm
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(homologyMul Rc (cochain Rc K) (cochain Rc K) (cochain Rc K) 1 1).map_smul_right,
    smul_smul]

/-- **An `O♯`-linear combination of the classes of the coordinate contractions has square zero.**
The square expands into a sum over pairs of indices; transposition of a pair is an involution
fixing exactly the diagonal, the diagonal terms vanish because the square of a single class is
zero, and a transposed pair cancels because two classes anticommute and the ring of sections is
commutative.

This is the Koszul-specific input to the exterior-algebra description of the self-Ext algebra of
`O♯/I`: over a general base, graded commutativity of the composition product gives only that
twice the square of a degree-one class vanishes, which is not enough. -/
theorem homologyMul_contraction_combination (W : Opens ↥X)
    (a : ULift.{u} (Fin r) → ((Tensor.ringSheaf (ringedSite Rc).O)).obj.obj (op W)) :
    (homologyMul Rc (cochain Rc K) (cochain Rc K) (cochain Rc K) 1 1).app (op W)
        (∑ j, a j • contractionClassOn Rc K j (op W))
        (∑ j, a j • contractionClassOn Rc K j (op W)) = 0 := by
  classical
  rw [homologyMul_sum_expand]
  refine Finset.sum_ninvolution Prod.swap ?_ ?_ (fun _ => Finset.mem_univ _)
    (fun _ => Prod.swap_swap _)
  · rintro ⟨j, k⟩
    rw [Prod.fst_swap, Prod.snd_swap, mul_comm (a k) (a j), ← smul_add,
      homologyMul_contractionClass_add_swap, smul_zero]
  · rintro ⟨j, k⟩ h he
    obtain rfl : k = j := congrArg Prod.fst he
    exact h (by rw [homologyMul_contractionClass_self, smul_zero])

end Stacks.RegularSequence.KoszulChainData

end
