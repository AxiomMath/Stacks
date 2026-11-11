module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFreeOfCoversTop
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RankDecomposition
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FittingKernel

/-!
# Extensions of finite locally free sheaves of modules on a ringed space

Let `(X, O_X)` be a ringed space and `0 → E' → E → E'' → 0` a short exact sequence of sheaves of
`O_X`-modules with `E'` and `E''` finite locally free. Near every point the epimorphism
`E → E''` splits, because the finitely many basis sections of `E''` over a trivialising open lift
to `E` over a smaller neighbourhood; there `E ≅ E' ⊕ E''` is free on the disjoint union of the
two bases. Hence `E` is finite locally free, and when the stalks of `O_X` are nonzero its rank is
the sum of the ranks of `E'` and `E''`.

## Main results

* `Stacks.SheafOfModules.exists_free_over_of_shortExact`: near every point the three terms are
  free, on bases `I'`, `I' ⊕ I''` and `I''`.
* `Stacks.SheafOfModules.isFiniteLocallyFree_of_shortExact`: the middle term is finite locally
  free.
* `Stacks.SheafOfModules.finiteLocallyFreeRank_eq_card_of_iso`: the rank at a point of an open
  over which the module is free on `I` is the cardinality of `I`.
* `Stacks.SheafOfModules.finiteLocallyFreeRank_X₂_of_shortExact`: the rank of the middle term is
  the sum of the ranks of the outer terms.

## References

* [Stacks Project, Tag 0B37](https://stacks.math.columbia.edu/tag/0B37)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.SheafOfModules

section Splitting

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- Finitely many sections of the target of an epimorphism of sheaves of modules on a ringed
space lift over one common open neighbourhood of any point of the open they live on. -/
theorem exists_le_lift_sections {M N : _root_.SheafOfModules.{u} R} (f : M ⟶ N) [Epi f]
    {ι : Type u} [Finite ι] (W : Opens X) (t : ι → N.val.obj (op W)) (x : X) (hx : x ∈ W) :
    ∃ (V : Opens X) (hVW : V ≤ W), x ∈ V ∧ ∃ s : ι → M.val.obj (op V),
      ∀ i, f.val.app (op V) (s i) = N.val.map (homOfLE hVW).op (t i) := by
  classical
  have hloc : ∀ i : ι, ∃ (V : Opens X) (hVW : V ≤ W), x ∈ V ∧ ∃ s : M.val.obj (op V),
      f.val.app (op V) s = N.val.map (homOfLE hVW).op (t i) := fun i => by
    obtain ⟨S, hS, hlift⟩ := Stacks.SheafOfModules.EpiMono.exists_covering_of_epi f (t i)
    obtain ⟨V, g, hg, hxV⟩ := (Opens.mem_grothendieckTopology _).1 hS x hx
    obtain ⟨s, hs⟩ := hlift g hg
    exact ⟨V, leOfHom g, hxV, s, hs⟩
  choose V hVW hxV s hs using hloc
  have hZV (i : ι) : W ⊓ ⨅ j, V j ≤ V i := inf_le_right.trans (iInf_le _ i)
  refine ⟨W ⊓ ⨅ j, V j, inf_le_left, ⟨hx, ?_⟩,
    fun i => M.val.map (homOfLE (hZV i)).op (s i), fun i => ?_⟩
  · show x ∈ ((⨅ j, V j : Opens X) : Set X)
    rw [Opens.coe_iInf, Set.mem_iInter]
    exact hxV
  · refine Eq.trans (PresheafOfModules.naturality_apply f.val (homOfLE (hZV i)).op (s i)) ?_
    rw [hs i]
    exact (N.val.map_comp_apply (homOfLE (hVW i)).op (homOfLE (hZV i)).op (t i)).symm

/-- **An epimorphism onto a sheaf of modules which is finite free over an open splits over a
neighbourhood, inside that open, of each of its points.** -/
theorem exists_isSplitEpi_over {M N : _root_.SheafOfModules.{u} R} (f : M ⟶ N) [Epi f]
    {W : Opens X} {ι : Type u} [Finite ι]
    (e : _root_.SheafOfModules.free ι ⟶ N.over W) [IsIso e] (x : X) (hx : x ∈ W) :
    ∃ (V : Opens X), V ≤ W ∧ x ∈ V ∧ IsSplitEpi (f.over V) := by
  obtain ⟨V, hVW, hxV, m, hm⟩ := exists_le_lift_sections f W
    (fun j => ((N.over W).freeHomEquiv e j).val (op (Over.mk (𝟙 W)))) x hx
  exact ⟨V, hVW, hxV, AlgebraicGeometry.isSplitEpi_over_of_lift f (homOfLE hVW) e m hm⟩

/-- A member of a finite free presentation of a finite locally free sheaf of modules through a
given point. -/
theorem exists_free_iso_over (M : _root_.SheafOfModules.{u} R)
    [hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] (x : X) :
    ∃ (W : Opens X) (_ : x ∈ W) (I : Type u) (_ : Finite I),
      Nonempty (_root_.SheafOfModules.free.{u} I ≅ M.over W) := by
  obtain ⟨q, hq, hfin⟩ := hM.exists_isFiniteLocallyFreeData
  have hxcover : x ∈ ⨆ k, q.X k := by
    rw [(Opens.coversTop_iff X q.X).mp q.coversTop]; trivial
  rw [Opens.mem_iSup] at hxcover
  obtain ⟨k, hk⟩ := hxcover
  have : IsIso (q.generators k).π := hq.isIso k
  exact ⟨q.X k, hk, (q.generators k).I, (hfin.isFiniteType k).finite,
    ⟨asIso (q.generators k).π⟩⟩

/-- **Near every point, the three terms of a short exact sequence of sheaves of modules with
finite locally free outer terms are free**, on finite bases `I'`, `I' ⊕ I''` and `I''`. -/
theorem exists_free_over_of_shortExact (S : ShortComplex (_root_.SheafOfModules.{u} R))
    (hS : S.ShortExact)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃] (x : X) :
    ∃ (V : Opens X) (_ : x ∈ V) (I₁ I₃ : Type u) (_ : Finite I₁) (_ : Finite I₃),
      Nonempty (_root_.SheafOfModules.free.{u} I₁ ≅ S.X₁.over V) ∧
      Nonempty (_root_.SheafOfModules.free.{u} I₃ ≅ S.X₃.over V) ∧
      Nonempty (_root_.SheafOfModules.free.{u} (I₁ ⊕ I₃) ≅ S.X₂.over V) := by
  have := hS.epi_g
  obtain ⟨W₁, hx₁, I₁, hI₁, ⟨e₁⟩⟩ := exists_free_iso_over S.X₁ x
  obtain ⟨W₃, hx₃, I₃, hI₃, ⟨e₃⟩⟩ := exists_free_iso_over S.X₃ x
  let e₃W := freeIsoOverMap S.X₃ (homOfLE (inf_le_right : W₁ ⊓ W₃ ≤ W₃)) I₃ e₃
  obtain ⟨V, hVW, hxV, hsplit⟩ := exists_isSplitEpi_over S.g e₃W.hom x ⟨hx₁, hx₃⟩
  let e₁V := freeIsoOverMap S.X₁ (homOfLE (hVW.trans inf_le_left)) I₁ e₁
  let e₃V := freeIsoOverMap S.X₃ (homOfLE (hVW.trans inf_le_right)) I₃ e₃
  let G := _root_.SheafOfModules.overFunctor R V
  have : PreservesFiniteLimits G :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits V
  have : PreservesFiniteColimits G :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits V
  have hS' : (S.map G).ShortExact := hS.map_of_exact G
  have : IsSplitEpi (G.map S.g) := hsplit
  let σ := ShortComplex.Splitting.ofExactOfSection (S.map G) hS'.exact (section_ (G.map S.g))
    (IsSplitEpi.id _) hS'.mono_f
  refine ⟨V, hxV, I₁, I₃, hI₁, hI₃, ⟨e₁V⟩, ⟨e₃V⟩, ⟨?_⟩⟩
  exact (_root_.SheafOfModules.freeSumIso (R := R.over V) I₁ I₃).symm ≪≫
    (biprod.isoCoprod _ _).symm ≪≫ biprod.mapIso e₁V e₃V ≪≫ σ.isoBinaryBiproduct.symm

/-- **An extension of finite locally free sheaves of modules on a ringed space is finite locally
free.** -/
theorem isFiniteLocallyFree_of_shortExact (S : ShortComplex (_root_.SheafOfModules.{u} R))
    (hS : S.ShortExact)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₂ := by
  choose V hxV I₁ I₃ hI₁ hI₃ _ _ e using exists_free_over_of_shortExact S hS
  refine AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_coversTop
    ((Opens.coversTop_iff X V).mpr ?_) S.X₂ fun x => ⟨I₁ x ⊕ I₃ x, inferInstance, e x⟩
  exact eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, hxV x⟩

end Splitting

section Rank

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  (F : _root_.SheafOfModules.{u} (LocallyFreeRank.toRingSheaf X O))
  (hO : LocallyFreeRank.StalksNontrivial X O)

/-- The trivialisation, in the sense of [Stacks, Tag 01C9], given by a presentation of the
restriction of a sheaf of modules to an open as a free sheaf of modules. -/
noncomputable def trivializationOfIso {V : Opens X} (I : Type u)
    (e : _root_.SheafOfModules.free.{u} I ≅ F.over V) :
    LocallyFreeRank.Trivialization X (LocallyFreeRank.toRingSheaf X O) F V :=
  ⟨I, (_root_.SheafOfModules.mapFreeIso (V.sheafOfModulesEquivOver
      (LocallyFreeRank.toRingSheaf X O)).functor I
      (V.sheafOfModulesEquivOverUnit (LocallyFreeRank.toRingSheaf X O)) ≪≫
    (V.sheafOfModulesEquivOver (LocallyFreeRank.toRingSheaf X O)).functor.mapIso e ≪≫
      LocallyFreeRank.restrictModIsoOver X V (LocallyFreeRank.toRingSheaf X O) F).symm⟩

/-- The index type of `trivializationOfIso` is the basis of the presentation. -/
@[simp]
theorem trivializationOfIso_ι {V : Opens X} (I : Type u)
    (e : _root_.SheafOfModules.free.{u} I ≅ F.over V) : (trivializationOfIso F I e).ι = I :=
  rfl

/-- **The rank at a point of an open over which a finite locally free sheaf of modules is free on
`I` is the cardinality of `I`.** -/
theorem finiteLocallyFreeRank_eq_card_of_iso
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] {V : Opens X}
    (I : Type u) (e : _root_.SheafOfModules.free.{u} I ≅ F.over V) (x : X) (hx : x ∈ V) :
    finiteLocallyFreeRank F hO x = Nat.card I := by
  have h := LocallyFreeRank.trivialization_rank_eq_locallyFreeRank F hO x V hx
    (trivializationOfIso F I e)
  change Cardinal.toNat (LocallyFreeRank.locallyFreeRank F hO x) = _
  rw [← h]
  rfl

/-- **The rank is additive in a short exact sequence of finite locally free sheaves of
modules**: the rank of the middle term is the sum of the ranks of the outer terms. -/
theorem finiteLocallyFreeRank_X₂_of_shortExact
    (S : ShortComplex (_root_.SheafOfModules.{u} (LocallyFreeRank.toRingSheaf X O)))
    (hS : S.ShortExact)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₂]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃] (x : X) :
    finiteLocallyFreeRank S.X₂ hO x =
      finiteLocallyFreeRank S.X₁ hO x + finiteLocallyFreeRank S.X₃ hO x := by
  obtain ⟨V, hxV, I₁, I₃, hI₁, hI₃, ⟨e₁⟩, ⟨e₃⟩, ⟨e₂⟩⟩ := exists_free_over_of_shortExact S hS x
  rw [finiteLocallyFreeRank_eq_card_of_iso S.X₁ hO I₁ e₁ x hxV,
    finiteLocallyFreeRank_eq_card_of_iso S.X₂ hO (I₁ ⊕ I₃) e₂ x hxV,
    finiteLocallyFreeRank_eq_card_of_iso S.X₃ hO I₃ e₃ x hxV, Nat.card_sum]

end Rank

end Stacks.SheafOfModules

end
