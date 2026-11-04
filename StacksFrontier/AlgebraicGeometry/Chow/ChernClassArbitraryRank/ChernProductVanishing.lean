module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.ExcisionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.BoundedComplexChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ChernCommutation
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectTwist
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalChernWhitney
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.WhitneyInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.Frame
public import StacksFrontier.AlgebraicGeometry.Divisors.ClosedSubschemeDimensionDrop
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.AlgebraicGeometry.Modules.FreeSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniPullbackTrivialization

/-!
# Products of Chern classes vanish above the dimension

Let `Y` be a scheme locally of finite type over the base of chapter 42 whose underlying space is
Noetherian of dimension `< m`, and let `ℰ` be a finite locally free `𝒪_Y`-module of constant rank
`r`. Then every product `c_{i_1}(ℰ) ⋯ c_{i_m}(ℰ)` of `m` Chern classes of positive degree vanishes
in the ring `∏_{p ≥ 0} A^p(Y)` of total classes.

The proof is an induction on `m`. A finite locally free module is free on a neighbourhood of each
of the finitely many generic points of `Y`; shrinking these neighbourhoods so that each meets only
its own irreducible component, their union `U` is a dense open on which `ℰ` restricts to a
module whose total Chern class is `1`, being free on each of the pairwise disjoint pieces. The
complement `Y'` of `U` contains no generic point, so `dim Y' < m - 1`, and by induction the
product of the first `m - 1` classes restricts to zero on `Y'`; the last class restricts to zero
on `U`. A product of classes vanishing on complementary pieces vanishes
(`Stacks.Chow.TotalChowClass.mul_eq_zero_of_res_eq_zero`).

## Main results

* `Stacks.Chow.totalChern_eq_one_of_iso_free` — a free module has total Chern class `1`.
* `Stacks.Chow.exists_opens_res_totalChern_eq_one` — the dense open `U` above.
* `Stacks.Chow.list_prod_homComponent_totalChern_eq_zero` — the vanishing of products of `m`
  Chern classes of positive degree when `dim Y < m`.

## References

* [Stacks Project, Tag 0ESX](https://stacks.math.columbia.edu/tag/0ESX)
* [Stacks Project, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The total Chern class of a free module -/

section Free

variable (C : ChowSituation.{u})

/-- The free module `𝒪_Y^{⊕ I}` is finite locally free of rank `r` when `I` has `r` elements. -/
theorem isFiniteLocallyFreeOfRank_free {Y : Scheme.{u}} (I : Type u) (r : ℕ) (e : I ≃ Fin r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.free Y I) r :=
  SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv I r e

/-- **The total Chern class of `𝒪_Y` is `1`** (Stacks 02SP): on every test scheme the pullback of
`𝒪_Y` is `𝒪_T`, whose Chern class cap products are trivial. -/
theorem totalChern_free_punit {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] :
    haveI := isFiniteLocallyFreeOfRank_free (Y := Y) PUnit.{u + 1} 1 punitEquivFinOne
    totalChern C sY (Scheme.Modules.free Y PUnit.{u + 1}) 1 = 1 := by
  have := isFiniteLocallyFreeOfRank_free (Y := Y) PUnit.{u + 1} 1 punitEquivFinOne
  refine TotalChowClass.ext_op fun g _ ↦ ?_
  rw [op_totalChern, TotalChowClass.op_one]
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank
    (Scheme.Modules.free Y PUnit.{u + 1}) 1 g
  have e₀ : Scheme.Modules.free Y PUnit.{u + 1} ≅ SheafOfModules.unit Y.ringCatSheaf :=
    coproductUniqueIso (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit Y.ringCatSheaf)
  exact GenuineChern.chernFamily_eq_one_of_iso_unit C (g ≫ sY) _
    ((Scheme.Modules.pullback g).mapIso e₀ ≪≫ asIso (Stacks.Divisors.unitComparison g))

/-- `ULift (Fin (r + 1))` is `ULift (Fin r) ⊕ PUnit`. -/
def uliftFinSuccEquiv (r : ℕ) : ULift.{u} (Fin (r + 1)) ≃ ULift.{u} (Fin r) ⊕ PUnit.{u + 1} :=
  Equiv.ulift.trans ((finSuccEquiv' (Fin.last r)).trans
    ((Equiv.optionEquivSumPUnit (Fin r)).trans (Equiv.sumCongr Equiv.ulift.symm (Equiv.refl _))))

/-- **The free module of rank `r + 1` is the direct sum of the free module of rank `r` and
`𝒪_Y`.** -/
def freeSuccIsoBiprod (Y : Scheme.{u}) (r : ℕ) :
    Scheme.Modules.free Y (ULift.{u} (Fin (r + 1))) ≅
      Scheme.Modules.free Y (ULift.{u} (Fin r)) ⊞ Scheme.Modules.free Y PUnit.{u + 1} :=
  have e₁ : Scheme.Modules.free Y (ULift.{u} (Fin (r + 1))) ≅
      Scheme.Modules.free Y (ULift.{u} (Fin r) ⊕ PUnit.{u + 1}) :=
    SheafOfModules.freeFunctor.mapIso (uliftFinSuccEquiv r).toIso
  have e₂ : Scheme.Modules.free Y (ULift.{u} (Fin r) ⊕ PUnit.{u + 1}) ≅
      Scheme.Modules.free Y (ULift.{u} (Fin r)) ⨿ Scheme.Modules.free Y PUnit.{u + 1} :=
    (SheafOfModules.freeSumIso _ _).symm
  e₁ ≪≫ e₂ ≪≫ (biprod.isoCoprod _ _).symm

/-- **A free module of rank `r` has total Chern class `1`**: by the Whitney sum formula of
Stacks 02UI it is the product of `r` copies of the total Chern class of `𝒪_Y`. -/
theorem totalChern_eq_one_of_iso_free (r : ℕ) :
    ∀ {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (M : Y.Modules)
      [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r]
      (_ : M ≅ Scheme.Modules.free Y (ULift.{u} (Fin r))), totalChern C sY M r = 1 := by
  induction r with
  | zero => exact fun sY _ M _ _ ↦ totalChern_of_rank_zero C sY M
  | succ r ih =>
    intro Y sY _ M _ e
    have hF := isFiniteLocallyFreeOfRank_free (Y := Y) (ULift.{u} (Fin r)) r Equiv.ulift
    have hO := isFiniteLocallyFreeOfRank_free (Y := Y) PUnit.{u + 1} 1 punitEquivFinOne
    have := GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact
      (ShortComplex.mk (biprod.inl : Scheme.Modules.free Y (ULift.{u} (Fin r)) ⟶ _)
        (biprod.snd : _ ⟶ Scheme.Modules.free Y PUnit.{u + 1}) (by simp))
      (ShortComplex.Splitting.ofHasBinaryBiproduct _ _).shortExact r 1 ‹_› ‹_›
    rw [totalChern_congr C sY (e ≪≫ freeSuccIsoBiprod Y r) rfl, totalChern_biprod C sY _ _ r 1,
      ih sY _ (Iso.refl _), totalChern_free_punit, one_mul]

end Free

/-! ### A dense open on which the total Chern class is trivial -/

section DenseOpen

variable {Y : Scheme.{u}}

/-- A generic point lies in the closure of no other generic point. -/
theorem notMem_closure_of_mem_genericPoints {η η' : Y} (hη : η ∈ genericPoints Y)
    (hη' : η' ∈ genericPoints Y) (hne : η' ≠ η) : η ∉ closure {η'} := by
  intro hmem
  have hsub : closure {η} ⊆ closure {η'} :=
    closure_minimal (Set.singleton_subset_iff.2 hmem) isClosed_closure
  have heq : closure {η} = closure {η'} := hη.eq_of_le hη'.1 hsub
  exact hne (congrArg Subtype.val (genericPoints.component_injective (α := Y)
    (a₁ := ⟨η', hη'⟩) (a₂ := ⟨η, hη⟩) (Subtype.ext heq.symm)))

/-- Every point lies in the closure of a generic point. -/
theorem exists_mem_genericPoints_mem_closure (x : Y) :
    ∃ η ∈ genericPoints Y, x ∈ closure {η} := by
  let c : irreducibleComponents Y :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  refine ⟨(genericPoints.ofComponent c).1, (genericPoints.ofComponent c).2, ?_⟩
  rw [(genericPoints.isGenericPoint_ofComponent c).def]
  exact mem_irreducibleComponent

/-- Shrinking opens around the generic points of a Noetherian scheme to pairwise disjoint ones. -/
private theorem exists_disjoint_opens_mem_genericPoints [NoetherianSpace Y]
    (V : genericPoints Y → Y.Opens) (hV : ∀ η, η.1 ∈ V η) :
    ∃ W : genericPoints Y → Y.Opens, (∀ η, ∀ x ∈ W η, x ∈ V η) ∧ (∀ η, η.1 ∈ W η) ∧
      ∀ η η', η ≠ η' → Disjoint (W η) (W η') := by
  have hGfin : Finite (genericPoints Y) :=
    (genericPoints.finite NoetherianSpace.finite_irreducibleComponents).to_subtype
  let W : genericPoints Y → Y.Opens := fun η ↦ V η ⊓
    ⟨⋂ η' : {η' : genericPoints Y // η' ≠ η}, (closure {η'.1.1})ᶜ,
      isOpen_iInter_of_finite fun _ ↦ isClosed_closure.isOpen_compl⟩
  have hmemW : ∀ (η : genericPoints Y) (x : Y), x ∈ W η ↔
      x ∈ V η ∧ ∀ η' : genericPoints Y, η' ≠ η → x ∉ closure {η'.1} := fun η x ↦ by
    show x ∈ (V η : Set Y) ∩ ⋂ η' : {η' : genericPoints Y // η' ≠ η}, (closure {η'.1.1})ᶜ ↔ _
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff, SetLike.mem_coe,
      Subtype.forall]
  have hWη : ∀ (η : genericPoints Y) (x : Y), x ∈ W η →
      ∀ η' : genericPoints Y, x ∈ closure {η'.1} → η' = η :=
    fun η x hx η' hx' ↦ by_contra fun hne ↦ ((hmemW η x).1 hx).2 η' hne hx'
  refine ⟨W, fun η x hx ↦ ((hmemW η x).1 hx).1, fun η ↦ (hmemW η η.1).2 ⟨hV η, fun η' hne ↦
    notMem_closure_of_mem_genericPoints η.2 η'.2 (fun h ↦ hne (Subtype.ext h))⟩,
    fun η η' hne ↦ disjoint_iff_inf_le.2 fun x hx ↦ ?_⟩
  obtain ⟨ζ, hζ, hxζ⟩ := exists_mem_genericPoints_mem_closure x
  exact absurd ((hWη η x hx.1 ⟨ζ, hζ⟩ hxζ).symm.trans (hWη η' x hx.2 ⟨ζ, hζ⟩ hxζ)) hne

variable (C : ChowSituation.{u}) (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (E : Y.Modules)
  (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]

/-- The total Chern class of `ℰ` restricts to `1` on any open on which `ℰ` is free. -/
theorem res_totalChern_eq_one_of_restrict_iso (V : Y.Opens)
    (e : E.restrict V.ι ≅ Scheme.Modules.free V (ULift.{u} (Fin r))) :
    TotalChowClass.res V.ι rfl (totalChern C sY E r) = 1 := by
  have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank E r V.ι
  rw [TotalChowClass.res_totalChern]
  exact totalChern_eq_one_of_iso_free C r (V.ι ≫ sY) _
    (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app E).symm ≪≫ e)

variable [NoetherianSpace Y]

/-- **A dense open on which `ℰ` has trivial Chern classes.** There is an open `U ⊆ Y` containing
every generic point of `Y` such that the total Chern class of `ℰ` restricts to `1` on `U`. -/
theorem exists_opens_res_totalChern_eq_one :
    ∃ U : Y.Opens, (∀ x ∈ genericPoints Y, x ∈ U) ∧
      TotalChowClass.res U.ι rfl (totalChern C sY E r) = 1 := by
  classical
  -- a neighbourhood of each generic point on which `ℰ` is free
  have hV : ∀ η : genericPoints Y, ∃ V : Y.Opens, η.1 ∈ V ∧
      Nonempty (E.restrict V.ι ≅ Scheme.Modules.free V (ULift.{u} (Fin r))) := fun η ↦ by
    obtain ⟨V, -, hx, -, he⟩ :=
      Stacks.Chow.SectionZeroScheme.exists_frame E r (W := ⊤) (x := η.1) trivial
    exact ⟨V, hx, he⟩
  choose V hηV hVe using hV
  -- shrink it to meet no other component
  obtain ⟨W, hWV, hηW, hdisj⟩ := exists_disjoint_opens_mem_genericPoints V hηV
  set U : Y.Opens := ⨆ η, W η
  refine ⟨U, fun x hx ↦ Opens.mem_iSup.2 ⟨⟨x, hx⟩, hηW ⟨x, hx⟩⟩, ?_⟩
  -- the pieces of `U`
  let P : genericPoints Y → U.toScheme.Opens := fun η ↦ U.ι ⁻¹ᵁ W η
  have hP : IsClopenDecomposition P := by
    refine ⟨fun η η' hne ↦ ?_, ?_⟩
    · exact disjoint_iff_inf_le.2 fun x hx ↦ (hdisj η η' hne).le_bot ⟨hx.1, hx.2⟩
    · refine eq_top_iff.2 fun x _ ↦ ?_
      obtain ⟨η, hη⟩ := Opens.mem_iSup.1 x.2
      exact Opens.mem_iSup.2 ⟨η, hη⟩
  refine TotalChowClass.eq_of_res_eq hP fun η ↦ ?_
  rw [map_one, TotalChowClass.res_res]
  have hle : Set.range ((P η).ι ≫ U.ι) ⊆ Set.range (V η).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hWV η _ (by exact x.2)
  set h := IsOpenImmersion.lift (V η).ι ((P η).ι ≫ U.ι) hle
  have hh : h ≫ (V η).ι = (P η).ι ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
  have : LocallyOfFiniteType h := by
    have : LocallyOfFiniteType (h ≫ (V η).ι) := hh ▸ inferInstance
    exact locallyOfFiniteType_of_comp h (V η).ι
  rw [TotalChowClass.res_congr hh.symm _ (by rw [← Category.assoc, hh, Category.assoc]),
    ← TotalChowClass.res_res (V η).ι rfl h (by rw [← Category.assoc, hh, Category.assoc]),
    res_totalChern_eq_one_of_restrict_iso C sY E r (V η) (hVe η).some, map_one]

end DenseOpen

/-! ### The vanishing -/

section Vanishing

/-- An inequality of dimensions: `a + 1 ≤ b < m + 1` gives `a < m` in `WithBot ℕ∞`. -/
theorem withBot_lt_of_add_one_le_of_lt {a b : WithBot ℕ∞} {m : ℕ} (h1 : a + 1 ≤ b)
    (h2 : b < ((m + 1 : ℕ) : WithBot ℕ∞)) : a < (m : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot =>
      rw [← WithBot.coe_one, ← WithBot.coe_add] at h1
      exact absurd h1 (WithBot.not_coe_le_bot _)
    | coe b =>
      rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe] at h1
      have h2' : b < (m : ℕ∞) + 1 := WithBot.coe_lt_coe.1 (h2.trans_eq (by norm_cast))
      exact (WithBot.coe_lt_coe.2 ((ENat.add_lt_add_iff_right ENat.one_ne_top).1
        (h1.trans_lt h2'))).trans_eq (by norm_cast)

/-- A space of dimension `< 0` is empty. -/
theorem isEmpty_of_topologicalKrullDim_lt_zero {T : Type*} [TopologicalSpace T]
    (h : topologicalKrullDim T < ((0 : ℕ) : WithBot ℕ∞)) : IsEmpty T := by
  refine ⟨fun x ↦ ?_⟩
  have : Nonempty (IrreducibleCloseds T) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim T := Order.krullDim_nonneg
  have h' : topologicalKrullDim T < 0 := by simpa using h
  exact absurd h' (not_lt.2 h0)

variable (C : ChowSituation.{u})

/-- **Products of Chern classes vanish above the dimension.** If the underlying space of `Y` is
Noetherian of dimension `< m` and `ℰ` is finite locally free of constant rank `r`, every product
`c_{i_1}(ℰ) ⋯ c_{i_m}(ℰ)` of `m` Chern classes of positive degree vanishes in the ring of total
classes of `Y`. -/
theorem list_prod_homComponent_totalChern_eq_zero (m : ℕ) :
    ∀ {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [NoetherianSpace Y]
      (_ : topologicalKrullDim Y < (m : WithBot ℕ∞)) (E : Y.Modules) (r : ℕ)
      [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
      (f : Fin m → ℕ+),
      (List.ofFn fun j ↦ TotalChowClass.homComponent (f j : ℕ) (totalChern C sY E r)).prod =
        0 := by
  induction m with
  | zero =>
    intro Y sY _ _ hdim E r _ f
    have := isEmpty_of_topologicalKrullDim_lt_zero hdim
    have := TotalChowClass.subsingleton_of_isEmpty (C := C) sY
    exact Subsingleton.elim _ _
  | succ m ih =>
    intro Y sY _ _ hdim E r _ f
    obtain ⟨U, hgen, hU⟩ := exists_opens_res_totalChern_eq_one C sY E r
    -- the closed complement of `U`
    set Z : Closeds Y := ⟨(U : Set Y)ᶜ, U.isOpen.isClosed_compl⟩
    set I := Scheme.IdealSheafData.vanishingIdeal Z
    set ι := I.subschemeι
    have hrange : Set.range ι.base = (U : Set Y)ᶜ := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    have : NoetherianSpace I.subscheme :=
      (IsClosedImmersion.isClosedEmbedding ι).isInducing.noetherianSpace
    have hdim' : topologicalKrullDim I.subscheme < (m : WithBot ℕ∞) := by
      refine withBot_lt_of_add_one_le_of_lt
        (Stacks.Divisors.topologicalKrullDim_add_one_le_of_forall_genericPoints_notMem ι
          fun x hx hxr ↦ ?_) hdim
      rw [hrange] at hxr
      exact hxr (hgen x hx)
    have : LocallyOfFiniteType (ι ≫ sY) := inferInstance
    have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback ι E r
    have hIH := ih (ι ≫ sY) hdim' ((Scheme.Modules.pullback ι).obj E) r
      fun j ↦ f j.castSucc
    rw [List.ofFn_succ', List.prod_concat]
    refine TotalChowClass.mul_eq_zero_of_res_eq_zero C sY ι U hrange ?_ ?_
    · rw [map_list_prod, List.map_ofFn]
      refine Eq.trans ?_ hIH
      congr 1
      refine List.ofFn_inj.2 (funext fun j ↦ ?_)
      show TotalChowClass.res ι rfl (TotalChowClass.homComponent _ _) = _
      have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank E r ι
      rw [TotalChowClass.res_homComponent, TotalChowClass.res_totalChern]
    · rw [TotalChowClass.res_homComponent, hU, TotalChowClass.homComponent_one,
        ite_eq_right (f (Fin.last m)).ne_zero]

end Vanishing

end Stacks.Chow

end
