module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.GlobalStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StratumPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.SmallEtaleStability
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.OpenRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Generic local constancy of a constructible sheaf

On an irreducible reduced quasi-compact quasi-separated scheme `W`, a constructible sheaf of sets
on the small étale site of Tag 021B is finite locally constant on an open
subscheme containing the generic point.

The stratum of a global constructible stratification (Tag 095E) that contains the generic point is
locally closed and dense, hence open; the stratum maps onto that open by an immersion, which is a
surjective closed immersion onto a reduced scheme and so an isomorphism, and the restriction of the
sheaf to the open is the restriction to the stratum transported along that isomorphism.

## Main results

* `AlgebraicGeometry.exists_isOpenImmersion_isFiniteLocallyConstant_of_irreducible`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- A locally closed subset containing the generic point of an irreducible space is open. -/
theorem isOpen_of_isLocallyClosed_of_genericPoint_mem {α : Type*} [TopologicalSpace α]
    [IrreducibleSpace α] [QuasiSober α] {s : Set α} (hs : IsLocallyClosed s)
    (hη : genericPoint α ∈ s) : IsOpen s := by
  have hcl : closure s = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec α).def]
    exact closure_mono (Set.singleton_subset_iff.mpr hη)
  have h := coborder_inter_closure (s := s)
  rw [hcl, Set.inter_univ] at h
  rw [← h]
  exact hs.isOpen_coborder

/-- A surjective immersion into a reduced scheme is an isomorphism. -/
theorem isIso_of_isImmersion_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f]
    [IsReduced Y] (hf : Function.Surjective f.base) : IsIso f := by
  have : Surjective f := ⟨hf⟩
  have : IsClosedImmersion f :=
    IsClosedImmersion.of_isPreimmersion f (by rw [Set.range_eq_univ.mpr hf]; exact isClosed_univ)
  exact isIso_of_isClosedImmersion_of_surjective f

/-- Every point of the base lies on some stratum of a global stratification. -/
private theorem exists_mem_range_inclusion {W : B.Scheme} (s : ConstructibleStratification B W ⊤)
    (η : W.obj) : ∃ i, η ∈ Set.range (B.inclusion.map (s.inclusion i)).base := by
  have : η ∈ ((⊤ : W.obj.Opens) : Set W.obj) := trivial
  rw [s.covers] at this
  exact Set.mem_iUnion.mp this

/-- An immersion `g` that factors through an open `U` as `l ≫ U.ι` and covers `U` makes `l` an
isomorphism. -/
private theorem isIso_of_comp_opensι_eq_of_subset_range {X Y : Scheme.{u}} [IsReduced Y]
    (U : Y.Opens) (g : X ⟶ Y) [IsImmersion g] (l : X ⟶ (U : Scheme.{u})) (hl : l ≫ U.ι = g)
    (h : ∀ x ∈ U, x ∈ Set.range g.base) : IsIso l := by
  have : IsImmersion (l ≫ U.ι) := by rw [hl]; infer_instance
  have : IsImmersion l := IsImmersion.of_comp l U.ι
  refine isIso_of_isImmersion_of_surjective l ?_
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := h x hx
  refine ⟨y, U.ι.isOpenEmbedding.injective ?_⟩
  change (l ≫ U.ι).base y = _
  rw [hl]
  rfl

/-- Finite local constancy of a pullback passes to a pullback along any factorization through a
morphism along which the pullback is finite locally constant. -/
private theorem isFiniteLocallyConstant_pullback_of_eq_comp {W P O : B.Scheme} (p : P ⟶ W)
    (lB : O ⟶ P) (o : O ⟶ W) (hfac : o = lB ≫ p)
    (F : Sheaf (SmallEtale.topology B W.obj W.property) (Type (u + 1)))
    (h : Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B P.obj P.property)
      (((smallEtaleBaseChange B p).sheafPullback (Type (u + 1))
        (SmallEtale.topology B W.obj W.property)
        (SmallEtale.topology B P.obj P.property)).obj F)) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B O.obj O.property)
      (((smallEtaleBaseChange B o).sheafPullback (Type (u + 1))
        (SmallEtale.topology B W.obj W.property)
        (SmallEtale.topology B O.obj O.property)).obj F) := by
  have h' := isFiniteLocallyConstant_smallEtaleSheafPullback' B (Type (u + 1)) lB _ (hH := h)
  have e := (smallEtaleSheafPullbackCompIso B O P W lB p (Type (u + 1))).app F
  rw [← hfac] at e
  exact Stacks.ConstantSheaf.isFiniteLocallyConstant_congr _ e (hF := h')

/-- **Generic local constancy.** On an irreducible reduced quasi-compact quasi-separated scheme
of a big étale site, a constructible sheaf is finite locally constant on an open subscheme
containing the generic point. -/
theorem exists_isOpenImmersion_isFiniteLocallyConstant_of_irreducible (W : B.Scheme)
    [IrreducibleSpace W.obj] [IsReduced W.obj] [CompactSpace W.obj] [QuasiSeparatedSpace W.obj]
    (F : Sheaf (SmallEtale.topology B W.obj W.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B W F) :
    ∃ (O : B.Scheme) (o : O ⟶ W), IsOpenImmersion (B.inclusion.map o) ∧
      genericPoint W.obj ∈ Set.range (B.inclusion.map o) ∧
      Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B O.obj O.property)
        (((smallEtaleBaseChange B o).sheafPullback (Type (u + 1))
          (SmallEtale.topology B W.obj W.property)
          (SmallEtale.topology B O.obj O.property)).obj F) := by
  have : IrreducibleSpace (B.inclusion.obj W) := ‹IrreducibleSpace W.obj›
  obtain ⟨s, hs⟩ := (isConstructibleFiniteSheaf_iff_exists_stratification B W F).mp hF
  obtain ⟨i, hi⟩ := exists_mem_range_inclusion B s (genericPoint W.obj)
  set ι := B.inclusion.map (s.inclusion i)
  have := s.isImmersion i
  have hopen : IsOpen (Set.range ι.base) :=
    isOpen_of_isLocallyClosed_of_genericPoint_mem ι.isLocallyClosed_range hi
  let U : W.obj.Opens := ⟨Set.range ι.base, hopen⟩
  have hU : B.Contains (U : Scheme.{u}) := BigEtaleOver.contains_opens B W.property U
  let O : B.Scheme := B.obj (U : Scheme.{u}) hU
  let o : O ⟶ W := ObjectProperty.homMk U.ι
  have hrange : Set.range ι.base ⊆ Set.range U.ι.base := U.range_ι.ge
  let l : (s.piece i).obj ⟶ (U : Scheme.{u}) := IsOpenImmersion.lift U.ι ι hrange
  have hl : l ≫ U.ι = ι := IsOpenImmersion.lift_fac U.ι ι hrange
  have : IsIso l := isIso_of_comp_opensι_eq_of_subset_range U ι l hl fun x hx => hx
  let lB : s.piece i ⟶ O := ObjectProperty.homMk l
  have : IsIso lB := by
    refine ⟨⟨ObjectProperty.homMk (inv l), ?_, ?_⟩⟩ <;>
      exact B.inclusion.map_injective (by simp [lB])
  have hfac : s.inclusion i = lB ≫ o := B.inclusion.map_injective (by
    simp only [Functor.map_comp]
    exact hl.symm)
  refine ⟨O, o, inferInstanceAs (IsOpenImmersion U.ι), ?_, ?_⟩
  · exact U.range_ι.ge hi
  · refine isFiniteLocallyConstant_pullback_of_eq_comp B (s.inclusion i) (inv lB) o ?_ F (hs i)
    rw [hfac, IsIso.inv_hom_id_assoc]

/-- In a Noetherian space, the points outside every irreducible component other than the closure
of a generic point `η` form an open set containing `η` and contained in the closure of `η`. -/
theorem exists_isOpen_mem_subset_closure_of_mem_irreducibleComponents {α : Type*}
    [TopologicalSpace α] [NoetherianSpace α] {η : α} (hη : closure {η} ∈ irreducibleComponents α) :
    ∃ V : Set α, IsOpen V ∧ η ∈ V ∧ V ⊆ closure {η} := by
  classical
  set K : Set α := ⋃₀ (irreducibleComponents α \ {closure {η}})
  have hK : IsClosed K :=
    ((NoetherianSpace.finite_irreducibleComponents).subset Set.sdiff_subset).isClosed_sUnion
      fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  refine ⟨Kᶜ, hK.isOpen_compl, ?_, ?_⟩
  · rintro ⟨C, ⟨hC, hCne⟩, hηC⟩
    have hle : closure {η} ⊆ C :=
      (isClosed_of_mem_irreducibleComponents C hC).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hηC)
    exact hCne (Set.Subset.antisymm (hη.2 hC.1 hle) hle)
  · intro x hx
    obtain ⟨C, hC, hxC⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible {x} isIrreducible_singleton
    by_cases hCη : C = closure {η}
    · exact hCη ▸ hxC rfl
    · exact (hx ⟨C, ⟨hC, hCη⟩, hxC rfl⟩).elim

/-- **Generic local constancy at a generic point.** On a reduced Noetherian scheme of a big étale
site, a constructible sheaf of sets is finite locally constant on an open subscheme containing a
given generic point `η` of an irreducible component and contained in the closure of `η`. -/
@[sga "4 IX 2.4" "(v)"]
theorem exists_opens_isFiniteLocallyConstant_of_mem_irreducibleComponents (W : B.Scheme)
    [IsReduced W.obj] [CompactSpace W.obj] [QuasiSeparatedSpace W.obj] [NoetherianSpace W.obj]
    (F : Sheaf (SmallEtale.topology B W.obj W.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B W F) {η : W.obj}
    (hη : closure {η} ∈ irreducibleComponents W.obj) (N : Set W.obj) (hN : IsOpen N)
    (hηN : η ∈ N) :
    ∃ (O : B.Scheme) (o : O ⟶ W), IsOpenImmersion (B.inclusion.map o) ∧
      η ∈ Set.range (B.inclusion.map o) ∧ Set.range (B.inclusion.map o) ⊆ closure {η} ∧
      Set.range (B.inclusion.map o) ⊆ N ∧
      Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B O.obj O.property)
        (((smallEtaleBaseChange B o).sheafPullback (Type (u + 1))
          (SmallEtale.topology B W.obj W.property)
          (SmallEtale.topology B O.obj O.property)).obj F) := by
  obtain ⟨s, hs⟩ := (isConstructibleFiniteSheaf_iff_exists_stratification B W F).mp hF
  obtain ⟨i, hi⟩ := exists_mem_range_inclusion B s η
  set ι := B.inclusion.map (s.inclusion i)
  have := s.isImmersion i
  obtain ⟨V, hV, hηV, hVsub⟩ := exists_isOpen_mem_subset_closure_of_mem_irreducibleComponents hη
  obtain ⟨O, Cl, hO, hCl, hOCl⟩ := ι.isLocallyClosed_range
  have hηCl : η ∈ Cl := (hOCl ▸ hi).2
  have hclCl : closure {η} ⊆ Cl := hCl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hηCl)
  let U : W.obj.Opens := ⟨O ∩ V ∩ N, (hO.inter hV).inter hN⟩
  have hUrange : (U : Set W.obj) ⊆ Set.range ι.base := fun x hx => by
    rw [hOCl]; exact ⟨hx.1.1, hclCl (hVsub hx.1.2)⟩
  have hηU : η ∈ U := ⟨⟨(hOCl ▸ hi).1, hηV⟩, hηN⟩
  have hU : B.Contains (U : Scheme.{u}) := BigEtaleOver.contains_opens B W.property U
  -- the restriction of the stratum over `U` is an isomorphism onto `U`
  let ι' : (ι ⁻¹ᵁ U : Scheme.{u}) ⟶ (U : Scheme.{u}) := ι ∣_ U
  have hι' : ι' ≫ U.ι = (ι ⁻¹ᵁ U).ι ≫ ι := morphismRestrict_ι ι U
  have : IsIso ι' := isIso_of_comp_opensι_eq_of_subset_range U _ ι' hι' fun x hx => by
    obtain ⟨y, rfl⟩ := hUrange hx
    exact ⟨⟨y, hx⟩, rfl⟩
  let l : (U : Scheme.{u}) ⟶ (s.piece i).obj := inv ι' ≫ (ι ⁻¹ᵁ U).ι
  have hl : l ≫ ι = U.ι := by
    simp only [l, Category.assoc, ← hι', IsIso.inv_hom_id_assoc]
  let O' : B.Scheme := B.obj (U : Scheme.{u}) hU
  let o : O' ⟶ W := ObjectProperty.homMk U.ι
  let lB : O' ⟶ s.piece i := ObjectProperty.homMk l
  have hfac : o = lB ≫ s.inclusion i := B.inclusion.map_injective (by
    simp only [Functor.map_comp]
    exact hl.symm)
  refine ⟨O', o, inferInstanceAs (IsOpenImmersion U.ι), ?_, ?_, ?_, ?_⟩
  · exact U.range_ι.ge hηU
  · exact fun x hx => hVsub (U.range_ι.le hx).1.2
  · exact fun x hx => (U.range_ι.le hx).2
  exact isFiniteLocallyConstant_pullback_of_eq_comp B (s.inclusion i) lB o hfac F (hs i)

end AlgebraicGeometry

end
