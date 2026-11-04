module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerGenericDevissage
public import StacksFrontier.AlgebraicGeometry.ConormalSheaf.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The group of `k`-cycles is the Grothendieck group of the `k`-th dimension layer

Let `(S, δ)` be a base situation with a dimension function — `S` locally Noetherian and
universally catenary with a dimension function `δ` — let `X` be a scheme **locally of finite
type** over `S`, and let `k ∈ ℤ`. Tag 02S9 asserts that the two homomorphisms

`Z_k(X) ⟶ K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` and `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) ⟶ Z_k(X)`

are mutually inverse isomorphisms. That is proved here, at exactly those hypotheses: `X` is
locally Noetherian, being locally of finite type over a locally Noetherian base, but it is not
quasi-compact, so it is not a Noetherian scheme and the dévissage filtration of Stacks 01YF is
unavailable.

One composite is the identity for formal reasons, which is
`Stacks.Chow.dimensionLayerCycleHom_comp_cycleDimensionLayerHom`. The other needs that for a
coherent module `F` of support dimension at most `k` the class of `F` in the layer is the class of
the locally finite direct sum `⨁_ξ 𝒪_{Z_ξ}^{⊕ m_ξ}` attached to the cycle `[F]_k = ∑ m_ξ [Z_ξ]`,
and that is `Stacks.Chow.dimensionLayerClassIsStructureSheafSum` below. Its proof is the source's:
filter `F` by the powers of the ideal sheaf `J` of the reduced induced structure on `supp F`, so
that the class of `F` is the class of the direct sum of the graded pieces
(`Stacks.Chow.of_eq_natCoproduct_adicGraded`), and apply the dévissage of
`Stacks.Chow.dimensionLayerClassMemRange_of_stalkKilled` to that direct sum — whose stalk at a
point of delta-dimension `k` of `supp F` is annihilated by the maximal ideal there, each graded
piece being annihilated by `J` and the local ring of `supp F` at such a point being a field.

## Main definitions

* `Stacks.Chow.cycleGroupAddEquivDimensionLayer` — **Stacks 02S9**: the group of `k`-cycles and
  the Grothendieck group of the dimension layer, identified by the two maps of the lemma.

## Main results

* `Stacks.Chow.ker_stalkMap_eq_maximalIdeal_of_isField` — the kernel of the stalk map of a closed
  immersion is the whole maximal ideal, at a point where the local ring of the closed subscheme is
  a field.
* `Stacks.Chow.stalkKilledByMaximalIdeal_of_smul_section_eq_zero` — **an annihilation of sections
  by an ideal sheaf becomes an annihilation of germs**: at such a point, a module whose sections
  over small affine opens are killed by the sections of the ideal sheaf has its stalk killed by
  the maximal ideal.
* `Stacks.Chow.smul_section_natCoproduct_eq_zero` and
  `Stacks.Chow.stalkKilledByMaximalIdeal_natCoproduct` — the same for a direct sum `⨁_{p ≥ 0} A p`
  of such modules, at a point where all but finitely many summands vanish.
* `Stacks.Chow.dimensionLayerClassIsStructureSheafSum` — **the remaining step of Tag 02S9 over a
  scheme merely locally of finite type over the base.**
* `Stacks.Chow.cycleDimensionLayerHom_dimensionLayerCycle_eq_of`,
  `Stacks.Chow.cycleDimensionLayerHom_comp_dimensionLayerCycleHom_eq_id` — the second inverse
  identity of Tag 02S9.
* `Stacks.Chow.cycleDimensionLayerHom_dimensionLayerCycleHom_mutuallyInverse` — **Tag 02S9**: the
  two maps, given by their formulas, are mutually inverse.

## Implementation notes

**Why the annihilation of the direct sum is read on sections and not on stalks.** The stalk at a
point of a direct sum of sheaves of modules is the direct sum of the stalks, but it is a direct
sum over the stalk of the *ring* sheaf read in `RingCat`, while the hypothesis of Stacks 01YE is
an annihilation by the maximal ideal of the stalk read in `CommRingCat`; the two rings are
canonically isomorphic and not interchangeable. `Stacks.Chow.smul_section_natCoproduct_eq_zero`
avoids them both: the splitting `Stacks.Chow.natCoproduct.shiftSplitting` is an identity of
morphisms of `𝒪_X`-modules, so it can be read on sections over a single open set, where scalars
are honest sections of `𝒪_X`, and the induction on the number of surviving summands terminates
because the supports of the terms of the ideal-adic filtration form a locally finite family.

**The neighbourhood is a parameter.** `stalkKilledByMaximalIdeal_of_smul_section_eq_zero` asks for
the annihilation only on the affine opens inside a given neighbourhood `V₀` of the point, because
that is what local finiteness supplies: the exponent beyond which the filtration dies depends on
`V₀`.

## References

* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 02QW](https://stacks.math.columbia.edu/tag/02QW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RegularIdealSheaf (definingIdealOfHom
  definingIdealOfHom_subschemeι_obj)
open Stacks.AlgebraicGeometry.CoherentDevissage
  (exists_definingIdealOfHom_section_germ_eq_of_stalkMap_eq_zero)
open Stacks.AlgebraicGeometry.IdealPowerSmul
open Stacks.AlgebraicGeometry.IrreducibleDevissage (idealPowStep isCoherent_cokernel'
  smul_top_cokernel_idealPowStep_of_isLocallyNoetherian)

universe u

namespace Stacks.Chow

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### The maximal ideal as the kernel of a stalk map -/

/-- **The kernel of the stalk map of a closed immersion is the whole maximal ideal at a point
where the local ring of the closed subscheme is a field.** The stalk map is surjective, so its
kernel is the preimage of a maximal ideal, hence maximal, hence *the* maximal ideal of the local
ring upstairs. -/
theorem ker_stalkMap_eq_maximalIdeal_of_isField {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (η : Z) (hη : IsField (Z.presheaf.stalk η)) :
    RingHom.ker (i.stalkMap η).hom = IsLocalRing.maximalIdeal (X.presheaf.stalk (i η)) := by
  have hbot : (⊥ : Ideal (Z.presheaf.stalk η)).IsMaximal := by
    rw [← IsLocalRing.isField_iff_maximalIdeal_eq.mp hη]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have hkerMax : (RingHom.ker (i.stalkMap η).hom).IsMaximal := by
    rw [RingHom.ker_eq_comap_bot]
    exact Ideal.comap_isMaximal_of_surjective _ (i.stalkMap_surjective η) (K := ⊥) (H := hbot)
  exact IsLocalRing.eq_maximalIdeal hkerMax

/-- A point of a reduced scheme with no proper generalization has a field for its local ring: it
is the generic point of the irreducible component it lies in. -/
@[ega "IV 20.1.3.1" "partial", sga "3 VIA 2.5.4" "partial"]
theorem isField_stalk_of_forall_specializes_eq [IsReduced X] (x : X)
    (h : ∀ y : X, y ⤳ x → y = x) : IsField (X.presheaf.stalk x) := by
  refine AlgebraicGeometry.isField_stalk_of_closure_mem_irreducibleComponents X x ?_
  let Z : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  rw [← h (genericPoints.ofComponent Z)
    ((genericPoints.isGenericPoint_ofComponent Z).specializes mem_irreducibleComponent)]
  exact (genericPoints.ofComponent Z).2

/-- The local ring of the reduced induced structure on a closed set `Z` is a field at a point
lying over the generic point of an irreducible component of `Z`. -/
private theorem isField_stalk_closedIdeal_of_isGenericPoint (Z : Closeds X) {C : Set (Z : Set X)}
    (hC : C ∈ irreducibleComponents (Z : Set X)) (η : (closedIdeal Z).subscheme)
    (hη : IsGenericPoint ((closedIdeal Z).subschemeι η) (Subtype.val '' C)) :
    IsField ((closedIdeal Z).subscheme.presheaf.stalk η) := by
  have : IsReduced (closedIdeal Z).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal Z
  have hsupp : ((closedIdeal Z).support : Set X) = Z :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  have hrange : Set.range (closedIdeal Z).subschemeι.base = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι, hsupp]
  refine isField_stalk_of_forall_specializes_eq η fun y hy =>
    (IsClosedImmersion.isClosedEmbedding (closedIdeal Z).subschemeι).injective ?_
  exact eq_of_specializes_of_isGenericPoint_component hC hη (hrange ▸ ⟨y, rfl⟩)
    (hy.map (closedIdeal Z).subschemeι.base.hom.2)

/-! ### From an annihilation of sections to an annihilation of germs -/

/-- **An annihilation of sections by an ideal sheaf becomes an annihilation of germs.** Let
`I` be a quasi-coherent sheaf of ideals whose closed subscheme has a *field* for its local ring at
a point `η`, write `ξ` for the image of `η`, and let `M` be an `𝒪_X`-module whose sections over
every small enough affine open around `ξ` are killed by the sections of `I` there. Then the stalk
of `M` at `ξ` is annihilated by the maximal ideal of `𝒪_{X, ξ}`.

The maximal ideal is the kernel of the stalk map of the closed immersion
(`Stacks.Chow.ker_stalkMap_eq_maximalIdeal_of_isField`), so every element of it is the germ of a
section of the defining ideal sheaf, by
`exists_definingIdealOfHom_section_germ_eq_of_stalkMap_eq_zero`, and on an affine open those
sections are the sections of `I`. -/
theorem stalkKilledByMaximalIdeal_of_smul_section_eq_zero (I : X.IdealSheafData)
    (η : I.subscheme) (hη : IsField (I.subscheme.presheaf.stalk η)) (M : X.Modules)
    (V₀ : X.Opens) (hV₀ : I.subschemeι η ∈ V₀)
    (hM : ∀ V : X.affineOpens, V.1 ≤ V₀ → ∀ r ∈ I.ideal V, ∀ t : Γ(M, V.1), r • t = 0) :
    Stacks.ClosedImmersion.StalkKilledByMaximalIdeal M (I.subschemeι η) := by
  let : Module (X.presheaf.stalk (I.subschemeι η))
      (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf (I.subschemeι η)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) M.val (I.subschemeι η)
  intro a ha s
  have ha0 : (I.subschemeι.stalkMap η).hom a = 0 := by
    rwa [← RingHom.mem_ker, ker_stalkMap_eq_maximalIdeal_of_isField I.subschemeι η hη]
  obtain ⟨U, hxU, r, hrJ, hr⟩ :=
    exists_definingIdealOfHom_section_germ_eq_of_stalkMap_eq_zero I.subschemeι η a ha0
  obtain ⟨W, hxW, t, ht⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf s
  obtain ⟨V, hVaff, hxV, hVle⟩ :=
    exists_isAffineOpen_mem_and_subset (U := U ⊓ W ⊓ V₀) ⟨⟨hxU, hxW⟩, hV₀⟩
  have hVU : V ≤ U := hVle.trans (inf_le_left.trans inf_le_left)
  have hVW : V ≤ W := hVle.trans (inf_le_left.trans inf_le_right)
  have hVV₀ : V ≤ V₀ := hVle.trans inf_le_right
  set rV : Γ(X, V) := X.presheaf.map (homOfLE hVU).op r
  set tV : Γ(M, V) := M.val.presheaf.map (homOfLE hVW).op t
  have hrVI : rV ∈ I.ideal ⟨V, hVaff⟩ := by
    rw [← definingIdealOfHom_subschemeι_obj I ⟨V, hVaff⟩]
    exact (definingIdealOfHom I.subschemeι).toSubmodule.map (homOfLE hVU).op hrJ
  have hra : (ConcreteCategory.hom (X.presheaf.germ V (I.subschemeι η) hxV)) rV = a :=
    (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) (I.subschemeι η) hxV r).trans hr
  have hts : (ConcreteCategory.hom
      (TopCat.Presheaf.germ M.val.presheaf V (I.subschemeι η) hxV)) tV = s :=
    (TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE hVW) (I.subschemeι η) hxV t).trans ht
  calc a • s
      = (ConcreteCategory.hom
          (TopCat.Presheaf.germ M.val.presheaf V (I.subschemeι η) hxV)) (rV • tV) := by
        rw [← hra, ← hts]
        exact (PresheafOfModules.germ_smul (R := X.presheaf) M.val
          (I.subschemeι η) V hxV rV tV).symm
    _ = 0 := by
        rw [hM ⟨V, hVaff⟩ hVV₀ rV hrVI tV]
        exact map_zero _

/-! ### Sections of a locally finite direct sum -/

/-- A section over an open set on which the support of a module is empty is zero: all its germs
vanish, the stalks there being trivial. -/
theorem section_eq_zero_of_forall_notMem_supp (M : X.Modules) (V : X.Opens)
    (hV : ∀ y ∈ V, y ∉ SheafOfModules.supp M) (u : Γ(M, V)) : u = 0 := by
  refine TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) V u 0
    fun y hy => ?_
  have h0 : ∀ c : ↑((TopCat.Sheaf.presheaf
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)).stalk y), c = 0 := fun c => by
    by_contra hc
    exact hV y hy ⟨c, hc⟩
  exact (h0 _).trans (h0 _).symm

/-- **A section of the structure sheaf that kills the sections of every summand over `V` kills the
sections over `V` of the direct sum**, provided all but the first `n` summands have empty support
inside `V`.

The induction is on `n`, through the splitting
`Stacks.Chow.natCoproduct.shiftSplitting` of `⨁_{p ≥ 0} A p` into its zeroth summand and the
summands of positive index: a section over `V` is the sum of its image from the shift and its
image from the zeroth summand, and multiplication by a section of the structure sheaf commutes
with both maps. The base case is the one where the whole direct sum has empty support inside `V`,
so its sections over `V` vanish. -/
theorem smul_section_natCoproduct_eq_zero (V : X.Opens) (r : Γ(X, V)) :
    ∀ (n : ℕ) (A : ℕ → X.Modules), (∀ p, ∀ u : Γ(A p, V), r • u = 0) →
      (∀ p, n ≤ p → ∀ y ∈ V, y ∉ SheafOfModules.supp (A p)) →
      ∀ u : Γ(natCoproduct A, V), r • u = 0 := by
  intro n
  induction n with
  | zero =>
    intro A _ hsupp u
    have hz : u = 0 :=
      section_eq_zero_of_forall_notMem_supp (natCoproduct A) V
        (fun y hy hmem => (supp_natCoproduct_subset A).trans
          (Set.iUnion_subset fun p _ hp hyV => hsupp p p.zero_le _ hyV hp) hmem hy) u
    rw [hz, smul_zero]
  | succ n IH =>
    intro A hA hsupp u
    have hid : natCoproduct.retr A ≫ natCoproduct.shift A
        + natCoproduct.proj A ≫ natCoproduct.ι A 0 = 𝟙 (natCoproduct A) :=
      (natCoproduct.shiftSplitting A).id
    have hu : u = (natCoproduct.shift A).app V ((natCoproduct.retr A).app V u)
        + (natCoproduct.ι A 0).app V ((natCoproduct.proj A).app V u) := by
      simpa using (congrArg
        (fun ψ : natCoproduct A ⟶ natCoproduct A => Scheme.Modules.Hom.app ψ V u) hid).symm
    have htail : r • (natCoproduct.retr A).app V u = 0 :=
      IH (fun p => A (p + 1)) (fun p => hA (p + 1))
        (fun p hp y hy => hsupp (p + 1) (by omega) y hy) _
    rw [hu, smul_add, ← Scheme.Modules.Hom.app_smul (natCoproduct.shift A),
      ← Scheme.Modules.Hom.app_smul (natCoproduct.ι A 0), htail, hA 0 _]
    simp

/-- **The stalk of a locally finite direct sum of modules annihilated by an ideal sheaf is killed
by the maximal ideal** at a point where the closed subscheme of that ideal has a field for its
local ring and where all but finitely many summands vanish. -/
theorem stalkKilledByMaximalIdeal_natCoproduct (I : X.IdealSheafData) (η : I.subscheme)
    (hη : IsField (I.subscheme.presheaf.stalk η)) (A : ℕ → X.Modules)
    (hA : ∀ (p : ℕ) (V : X.affineOpens),
      I.ideal V • (⊤ : Submodule Γ(X, V.1) Γ(A p, V.1)) = ⊥)
    (V₀ : X.Opens) (hV₀ : I.subschemeι η ∈ V₀) (n : ℕ)
    (hn : ∀ p, n ≤ p → ∀ y ∈ V₀, y ∉ SheafOfModules.supp (A p)) :
    Stacks.ClosedImmersion.StalkKilledByMaximalIdeal (natCoproduct A) (I.subschemeι η) := by
  refine stalkKilledByMaximalIdeal_of_smul_section_eq_zero I η hη _ V₀ hV₀ ?_
  intro V hVV₀ r hrI t
  refine smul_section_natCoproduct_eq_zero V.1 r n A (fun p u => ?_)
    (fun p hp y hy => hn p hp y (hVV₀ hy)) t
  have hmem := Submodule.smul_mem_smul hrI (Submodule.mem_top (x := u))
  rw [hA p V] at hmem
  exact (Submodule.mem_bot _).mp hmem

/-! ### The remaining step of Tag 02S9 at the hypotheses of the source -/

/-- The support of a graded piece of the ideal-adic filtration lies in the support of the
corresponding term of the filtration. -/
private theorem supp_cokernel_idealPowStep_subset (J : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] (p : ℕ) :
    SheafOfModules.supp (cokernel (idealPowStep J F p)) ⊆
      SheafOfModules.supp (idealPowSmulModule J p F) :=
  @supp_subset_of_epi X _ _ (cokernel.π (idealPowStep J F p))
    (shortExact_mk_cokernel (idealPowStep J F p)).epi_g

/-- **All but finitely many graded pieces of the ideal-adic filtration miss a neighbourhood of a
given point**, the supports of the terms of the filtration forming a locally finite family. -/
private theorem exists_forall_notMem_supp_cokernel_idealPowStep [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsCoherent] (Z : Closeds X)
    (hZ : SheafOfModules.supp F ⊆ (Z : Set X)) (ξ : X) :
    ∃ V₀ : X.Opens, ξ ∈ V₀ ∧ ∃ n : ℕ, ∀ p, n ≤ p → ∀ y ∈ V₀,
      y ∉ SheafOfModules.supp (cokernel (idealPowStep (closedIdeal Z) F p)) := by
  obtain ⟨t, ht, hfin⟩ := locallyFinite_supp_idealPowSmul F Z hZ ξ
  obtain ⟨V₀, hV₀t, hV₀open, hξV₀⟩ := mem_nhds_iff.mp ht
  have hfinN : {p : ℕ |
      (SheafOfModules.supp (idealPowSmulModule (closedIdeal Z) p F) ∩ t).Nonempty}.Finite :=
    Set.Finite.preimage (f := ULift.up.{u}) (fun _ _ _ _ h => ULift.up_injective h) hfin
  obtain ⟨n, hn⟩ := hfinN.bddAbove
  refine ⟨⟨V₀, hV₀open⟩, hξV₀, n + 1, fun p hp y hy hmem => ?_⟩
  have hple : p ≤ n :=
    hn ⟨y, supp_cokernel_idealPowStep_subset (closedIdeal Z) F p hmem, hV₀t hy⟩
  omega

variable (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)

/-- **The generic structure of a coherent module in a dimension layer, over a scheme merely
locally of finite type over the base.** The class in `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` of a coherent
`𝒪_X`-module `F` whose support has delta-dimension at most `k` is the class of the locally finite
direct sum `⨁_ξ 𝒪_{Z_ξ}^{⊕ m_ξ}` of the structure sheaves of the integral closed subschemes of
`[F]_k = ∑ m_ξ [Z_ξ]`.

No Noetherian hypothesis is used. Writing `J` for the ideal sheaf of the reduced induced
structure on `supp F`, the class of `F` is the class of the direct sum of the graded pieces of
the ideal-adic filtration `F ⊇ J·F ⊇ J²·F ⊇ ⋯`
(`Stacks.Chow.of_eq_natCoproduct_adicGraded`); each graded piece has its sections over an affine
open annihilated by `J` there
(`AlgebraicGeometry.IrreducibleDevissage.smul_top_cokernel_idealPowStep_of_isLocallyNoetherian`),
and at a point
`ξ` of delta-dimension `k` of `supp F` the local ring of `supp F` is a field, `ξ` being the
generic point of an irreducible component of a reduced scheme, so the germs of `J` at `ξ` fill
the maximal ideal of `𝒪_{X, ξ}` and the direct sum has its stalk there killed by that maximal
ideal (`Stacks.Chow.stalkKilledByMaximalIdeal_natCoproduct`). The dévissage of
`Stacks.Chow.dimensionLayerClassMemRange_of_stalkKilled` then puts the class in the image of the
map from cycles, and membership in that image is already the identity wanted. -/
theorem dimensionLayerClassIsStructureSheafSum :
    DimensionLayerClassIsStructureSheafSum C f k := by
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine dimensionLayerClassIsStructureSheafSum_of_forall_mem_range C f k fun G => ?_
  have hcF : _root_.SheafOfModules.IsCoherent G.obj.obj :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent G.obj.property
  have hftF : G.obj.obj.IsFiniteType := isFiniteType_of_isCoherent G.obj.obj
  have hqF : G.obj.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent G.obj.obj
  have hdimF : ∀ x ∈ SheafOfModules.supp G.obj.obj,
      relativeDimension C.dimensionFunction f x ≤ k :=
    relativeDimension_le_of_mem_supp_dimLE C f k G
  have hFk : schemeDeltaDimension C ((reducedSupport G.obj.obj).subschemeι ≫ f) ≤ (k : EInt) :=
    (schemeDeltaDimension_reducedSupport_le_iff C f G.obj.obj k).2 hdimF
  set Z : Closeds X :=
    ⟨SheafOfModules.supp G.obj.obj, SheafOfModules.isClosed_supp G.obj.obj⟩
  have hZ : SheafOfModules.supp G.obj.obj ⊆ (Z : Set X) := subset_rfl
  set J : X.IdealSheafData := closedIdeal Z
  have hJsupp : (J.support : Set X) = SheafOfModules.supp G.obj.obj :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  set B : ℕ → X.Modules := fun p => cokernel (idealPowStep J G.obj.obj p)
  -- coherence and supports of the ideal-adic filtration and of its graded pieces
  have hcB : ∀ p, (B p).IsCoherent := fun p => isCoherent_cokernel' _
    (isCoherent_idealPowSmul J _ G.obj.obj) (isCoherent_idealPowSmul J _ G.obj.obj)
  have hsuppA : ∀ p, SheafOfModules.supp (idealPowSmulModule J p G.obj.obj) ⊆
      SheafOfModules.supp G.obj.obj := fun p =>
    @supp_subset_of_mono X _ _ (idealPowSmulHom J p G.obj.obj)
      (inferInstanceAs (Mono (idealPowSmul J p G.obj.obj).ι))
  have hsuppB := supp_cokernel_idealPowStep_subset J G.obj.obj
  have hLFB : LocallyFinite fun p : ULift.{u} ℕ ↦ SheafOfModules.supp (B p.down) :=
    (locallyFinite_supp_idealPowSmul G.obj.obj Z hZ).subset fun p => hsuppB p.down
  have hcS : _root_.SheafOfModules.IsCoherent (natCoproduct B) :=
    isCoherent_natCoproduct B hcB hLFB
  have hsuppS : SheafOfModules.supp (natCoproduct B) ⊆ SheafOfModules.supp G.obj.obj :=
    (supp_natCoproduct_subset B).trans (Set.iUnion_subset fun p => (hsuppB p).trans (hsuppA p))
  have hdimS : ∀ x ∈ SheafOfModules.supp (natCoproduct B),
      relativeDimension C.dimensionFunction f x ≤ k := fun x hx => hdimF x (hsuppS hx)
  -- the class of `F` is the class of the direct sum of the graded pieces
  rw [of_eq_natCoproduct_adicGraded C f k G.obj.obj Z hZ G
    (dimLEObj C f k (natCoproduct B) hcS hdimS) rfl rfl]
  refine dimensionLayerClassMemRange_of_stalkKilled C f k (natCoproduct B) hcS hdimS ?_
  intro ξ hξ
  -- `ξ` lies in the support of `F` and has delta-dimension `k`
  obtain ⟨Comp, hComp⟩ := isGenericPoint_component_supp_of_relativeDimension_eq C f G.obj.obj k
    ξ hFk (hsuppS hξ.1) hξ.2
  -- the point of the reduced support above `ξ`
  obtain ⟨η, hηξ⟩ : ξ ∈ Set.range J.subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι, hJsupp]
    exact hsuppS hξ.1
  -- all but finitely many graded pieces miss a neighbourhood of `ξ`
  obtain ⟨V₀, hξV₀, n, hn⟩ := exists_forall_notMem_supp_cokernel_idealPowStep G.obj.obj Z hZ ξ
  -- the local ring of the reduced support at that point is a field
  exact hηξ ▸ stalkKilledByMaximalIdeal_natCoproduct J η
    (isField_stalk_closedIdeal_of_isGenericPoint Z Comp.2 η (hηξ ▸ hComp)) B
    (fun p V => smul_top_cokernel_idealPowStep_of_isLocallyNoetherian J G.obj.obj p V)
    V₀ (hηξ ▸ hξV₀) n hn

/-! ### The two mutually inverse isomorphisms -/

/-- The class of a coherent `𝒪_X`-module `F` of support dimension at most `k` in
`K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` is the image of its cycle `[F]_k` under the map
`Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))`, for `X` merely locally of finite type over the base. -/
theorem cycleDimensionLayerHom_dimensionLayerCycle_eq_of (F : CoherentModulesDimLE C f k) :
    cycleDimensionLayerHom C f k (dimensionLayerCycle C f k F) =
      GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj F) :=
  cycleDimensionLayerHom_dimensionLayerCycle_of_classIsStructureSheafSum C f k
    (dimensionLayerClassIsStructureSheafSum C f k) F

/-- The composite `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) → Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` of the
two maps of Tag 02S9 is the identity, for `X` merely locally of finite type over the base. -/
theorem cycleDimensionLayerHom_comp_dimensionLayerCycleHom_eq_id :
    (cycleDimensionLayerHom C f k).comp (dimensionLayerCycleHom C f k) = AddMonoidHom.id _ :=
  cycleDimensionLayerHom_comp_dimensionLayerCycleHom_of_classIsStructureSheafSum C f k
    (dimensionLayerClassIsStructureSheafSum C f k)

/-- **Stacks 02S9.** Let `X` be locally of finite type over `(S, δ)`. The maps
`Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))`,
`∑ n_Z[Z] ↦ [⨁_{n_Z > 0} 𝒪_Z^{⊕n_Z}] - [⨁_{n_Z < 0} 𝒪_Z^{⊕-n_Z}]`, and
`K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) → Z_k(X)`, `F ↦ [F]_k`, are mutually inverse isomorphisms.

The first two conjuncts are the formulas defining the two maps (the direct sums are the locally
finite direct sums of `Stacks.Chow.cycleStructureSheafDimLE`), the last two the two composites
being the identity. -/
@[stacks 02S9 "the two maps, given by their formulas, are mutually inverse isomorphisms"]
theorem cycleDimensionLayerHom_dimensionLayerCycleHom_mutuallyInverse :
    (∀ c : CycleGroup C f k, cycleDimensionLayerHom C f k c =
      GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj
          (cycleStructureSheafDimLE C f k (cyclePositivePart C f k c))) -
        GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj
          (cycleStructureSheafDimLE C f k (cycleNegativePart C f k c)))) ∧
    (∀ F : CoherentModulesDimLE C f k, dimensionLayerCycleHom C f k
        (GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj F)) =
      dimensionLayerCycle C f k F) ∧
    (dimensionLayerCycleHom C f k).comp (cycleDimensionLayerHom C f k) = AddMonoidHom.id _ ∧
    (cycleDimensionLayerHom C f k).comp (dimensionLayerCycleHom C f k) = AddMonoidHom.id _ :=
  ⟨cycleDimensionLayerHom_apply C f k, dimensionLayerCycleHom_of C f k,
    dimensionLayerCycleHom_comp_cycleDimensionLayerHom C f k,
    cycleDimensionLayerHom_comp_dimensionLayerCycleHom_eq_id C f k⟩

/-- **Stacks 02S9**, as an isomorphism: the group of `k`-cycles on `X` and the Grothendieck group
of the dimension layer `Coh_{≤k}(X)/Coh_{≤k-1}(X)`, identified by the two mutually inverse maps
`∑ n_Z[Z] ↦ [⨁_{n_Z > 0} 𝒪_Z^{⊕n_Z}] - [⨁_{n_Z < 0} 𝒪_Z^{⊕-n_Z}]` and `F ↦ [F]_k`. -/
@[stacks 02S9 "`Z_k(X) ≃ K₀(Coh_{≤k}/Coh_{≤k-1})` by the two maps of the lemma"]
def cycleGroupAddEquivDimensionLayer :
    CycleGroup C f k ≃+ GrothendieckGroup (coherentDimensionQuotient C f (k - 1) k) where
  toFun := cycleDimensionLayerHom C f k
  invFun := dimensionLayerCycleHom C f k
  left_inv := dimensionLayerCycleHom_cycleDimensionLayerHom C f k
  right_inv :=
    DFunLike.congr_fun (cycleDimensionLayerHom_comp_dimensionLayerCycleHom_eq_id C f k)
  map_add' := map_add _

/-- The isomorphism of Tag 02S9 is the map `∑ n_Z[Z] ↦ [⨁ 𝒪_Z^{⊕n_Z}] - [⨁ 𝒪_Z^{⊕-n_Z}]`. -/
@[simp]
theorem cycleGroupAddEquivDimensionLayer_apply (c : CycleGroup C f k) :
    cycleGroupAddEquivDimensionLayer C f k c = cycleDimensionLayerHom C f k c :=
  rfl

/-- The inverse of the isomorphism of Tag 02S9 is the map `F ↦ [F]_k`. -/
@[simp]
theorem cycleGroupAddEquivDimensionLayer_symm_apply
    (x : GrothendieckGroup (coherentDimensionQuotient C f (k - 1) k)) :
    (cycleGroupAddEquivDimensionLayer C f k).symm x = dimensionLayerCycleHom C f k x :=
  rfl

end Stacks.Chow

end
