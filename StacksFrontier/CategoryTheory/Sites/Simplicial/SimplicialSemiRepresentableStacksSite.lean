module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.FiniteSiteCoverings
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCechComplex
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialSemiRepresentableSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationComponents

/-!
# Lower shriek along the augmentation of `C/K`, for an arbitrary site

Let `C` be a site in the sense of the Stacks project: a category with a class of coverings
satisfying the isomorphism, composition and base change axioms, where the base change axiom asks
for the fibre products of a covering with an *arbitrary* morphism, and nothing more. Let `K` be a
simplicial object of `SR(C)`. This file builds the simplicial family of sites `n ↦ C/K_n` with
its augmentation towards `C` for such a site, and proves Stacks 09WM for it:

1. `a^{-1} : Sh(C) ⥤ Sh((C/K)_total)` has a left adjoint `a^{Sh}_!`;
2. `a^{-1} : Ab(C) ⥤ Ab((C/K)_total)` has a left adjoint `a_!`;
3. `a^{-1}ℱ` is in simplicial degree `n` the sheaf `a_n^{-1}ℱ`;
4. for an abelian sheaf `𝒢` on the total site, `a_*𝒢` is the equalizer of the two maps
   `a_{0,*}𝒢_0 ⟶ a_{1,*}𝒢_1`.

## The hypothesis on the site

The site is given by its Grothendieck topology `J`. The covering families of `C/K_n` and of `C`
which the simplicial-site situation needs are the *stable* ones: the covering families of `J`
along whose members every fibre product exists
(`CategoryTheory.GrothendieckTopology.stableCoverings`). They always satisfy the site axioms, with
no assumption on `C`. The only hypothesis is `CategoryTheory.GrothendieckTopology.IsStacksSite J`:
they generate `J`. By `CategoryTheory.GrothendieckTopology.isStacksSite_iff` this holds exactly
when `J` is the topology of some class of coverings satisfying the site axioms, that is when
`(C, J)` is a site in the sense of Stacks 00VH; so it is the source's "let `C` be a site".

The companion module `SimplicialSemiRepresentableLowerShriek` proves the same four statements
under `[J.toCoverage.HasPullbacks]`. Since the maximal presieve of an object is a covering family
of `J`, that hypothesis forces `C` to have *all* fibre products, which the source does not
assume; it implies `IsStacksSite J`
(`CategoryTheory.GrothendieckTopology.isStacksSite_of_hasPullbacks`), so the results here
generalize those.

The covering families of `C/K_n` are the families whose image in `C` is a stable covering family
of `J` (`CategoryTheory.SemiRepresentable.stableComponentCoverings`), which are the coverings of
the localization `C/U` of Stacks 00XZ for the site structure given by the stable families. The
transition functors are cocontinuous and have property P of Stacks 09W7 for them, which is
Stacks 0D85 for these coverings; the fibre products this needs are those of covering families
with arbitrary morphisms, and nothing else.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.stableSheafLowerShriekAdjunction`: part (1).
* `CategoryTheory.SimplicialSemiRepresentable.stableAbelianLowerShriekAdjunction`: part (2).
* `CategoryTheory.SimplicialSemiRepresentable.stableInverseImageComponentIso`: part (3).
* `CategoryTheory.SimplicialSemiRepresentable.stableAbelianPushforwardFork` and
  `CategoryTheory.SimplicialSemiRepresentable.stableAbelianPushforwardForkIsLimit`: part (4).

## Implementation notes

The identifications of the morphisms of topoi of Stacks 0D70 with those of the localization
functors `j_n` and `j_total` (Stacks 0D8B) are proved here again for this simplicial site, by
the same arguments as in `SimplicialSemiRepresentableSite`, because the declarations there are
stated for the simplicial site built from all covering families of `J`; the two remaining clauses
of Stacks 0D8B, that the functor of the augmentation is `j_0` and that the direct image of `a` is
that of `j_total` on the nose, are in `SimplicialSemiRepresentableStacksAugmentation`. The
conventions on
universes are those of that file: `C` is small and everything lives in one universe `u`.

## References

* [Stacks Project, Tag 09WM](https://stacks.math.columbia.edu/tag/09WM)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 00VH](https://stacks.math.columbia.edu/tag/00VH)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory

/-! ### Fibre products along composites and base changes -/

section Pullbacks

variable {C : Type u} [SmallCategory C]

/-- If all fibre products along `v` and along `u` exist, so do all fibre products along
`v ≫ u`: paste the two pullback squares. -/
theorem hasPullback_comp_of_forall {X Y Z : C} {v : X ⟶ Y} {w : Y ⟶ Z}
    (hv : ∀ {W : C} (k : W ⟶ Y), HasPullback v k) (hw : ∀ {W : C} (k : W ⟶ Z), HasPullback w k)
    {W : C} (h : W ⟶ Z) : HasPullback (v ≫ w) h := by
  have := hw h
  have := hv (pullback.fst w h)
  exact (IsPullback.paste_vert (IsPullback.of_hasPullback v (pullback.fst w h))
    (IsPullback.of_hasPullback w h)).hasPullback

/-- The base change of a morphism along which all fibre products exist again has this property:
a fibre product along the base change is a fibre product along the original morphism. -/
theorem hasPullback_of_isPullback_of_forall {P X U V : C} {π₁ : P ⟶ X} {π₂ : P ⟶ V}
    {f : X ⟶ U} {g : V ⟶ U} (sq : IsPullback π₁ π₂ f g)
    (hf : ∀ {W : C} (k : W ⟶ U), HasPullback f k) {W : C} (h : W ⟶ V) :
    HasPullback π₂ h := by
  have := hf (h ≫ g)
  let l : pullback f (h ≫ g) ⟶ P := sq.lift (pullback.fst f (h ≫ g))
    (pullback.snd f (h ≫ g) ≫ h) (by rw [pullback.condition, Category.assoc])
  have outer : IsPullback (l ≫ π₁) (pullback.snd f (h ≫ g)) f (h ≫ g) := by
    rw [sq.lift_fst]
    exact IsPullback.of_hasPullback f (h ≫ g)
  have top : IsPullback l (pullback.snd f (h ≫ g)) π₂ h :=
    IsPullback.of_right outer (sq.lift_snd _ _ _) sq
  exact top.hasPullback

end Pullbacks

/-! ### The stable covering families of a Grothendieck topology -/

namespace GrothendieckTopology

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- The *stable* covering families of a Grothendieck topology: the families generating a
covering sieve along whose members every fibre product exists. These are the largest class of
covering families of `J` satisfying the base change axiom of a site. -/
def stableCoverings : Covering.{u, u, u} C → Prop := fun 𝒰 =>
  𝒰.2.presieve₀ ∈ J.toCoverage 𝒰.1 ∧
    ∀ (i : 𝒰.2.I₀) {W : C} (h : W ⟶ 𝒰.1), HasPullback (𝒰.2.f i) h

/-- A family of base changes of a stable covering family is a stable covering family. -/
theorem stableCoverings_of_isPullback {𝒰 : Covering.{u, u, u} C} (h𝒰 : J.stableCoverings 𝒰)
    {V : C} (g : V ⟶ 𝒰.1) (P : 𝒰.2.I₀ → C) (π₁ : ∀ i, P i ⟶ 𝒰.2.X i) (π₂ : ∀ i, P i ⟶ V)
    (sq : ∀ i, IsPullback (π₁ i) (π₂ i) (𝒰.2.f i) g) :
    J.stableCoverings ⟨V, ⟨𝒰.2.I₀, P, π₂⟩⟩ := by
  refine ⟨?_, fun i W h => hasPullback_of_isPullback_of_forall (sq i) (h𝒰.2 i) h⟩
  change _ ∈ J.toPrecoverage V
  exact Precoverage.IsStableUnderBaseChange.mem_coverings_of_isPullback
    (J := J.toPrecoverage) 𝒰.2.f h𝒰.1 g _ _ fun i => (sq i).flip

/-- The stable covering families of a Grothendieck topology satisfy the isomorphism, composition
and base change axioms of a site, with no assumption on the category. -/
theorem isSite_stableCoverings : IsSite J.stableCoverings := by
  refine ⟨?_, ?_, ?_⟩
  · intro U V f hf
    refine ⟨?_, fun _ W h => hasPullback_of_left_iso f h⟩
    change _ ∈ J.toPrecoverage U
    rw [PreZeroHypercover.presieve₀_singleton]
    exact Precoverage.HasIsos.mem_coverings_of_isIso (J := J.toPrecoverage) f
  · intro 𝒰 h𝒰 𝒱 h𝒱 h
    refine ⟨?_, ?_⟩
    · have hmove : ∀ {A B : C} (e : A = B) {ι : Type u} (X : ι → C) (f : ∀ j, X j ⟶ A),
          Presieve.ofArrows X f ∈ J.toPrecoverage A →
            Presieve.ofArrows X (fun j => f j ≫ eqToHom e) ∈ J.toPrecoverage B := by
        intro A B e ι X f hf
        subst e
        simpa using hf
      change _ ∈ J.toPrecoverage 𝒰.1
      exact Precoverage.IsStableUnderComposition.comp_mem_coverings
        (J := J.toPrecoverage) 𝒰.2.f h𝒰.1 (fun i j => (𝒱 i).2.f j ≫ eqToHom (h i))
        fun i => hmove (h i) _ _ (h𝒱 i).1
    · rintro ⟨i, j⟩ W k
      exact hasPullback_comp_of_forall
        (hasPullback_comp_of_forall (fun k' => (h𝒱 i).2 j k') fun k' =>
          hasPullback_of_left_iso (eqToHom (h i)) k')
        (fun k' => h𝒰.2 i k') k
  · intro 𝒰 h𝒰 V g
    have := fun i => h𝒰.2 i g
    exact ⟨fun i => Limits.pullback (𝒰.2.f i) g, fun i => Limits.pullback.fst _ _,
      fun i => Limits.pullback.snd _ _,
      fun i => IsPullback.of_hasPullback _ _,
      J.stableCoverings_of_isPullback h𝒰 g _ _ _ fun i => IsPullback.of_hasPullback _ _⟩

/-- The topology generated by the stable covering families of `J` is contained in `J`. -/
theorem topologyOfCoverings_stableCoverings_le : topologyOfCoverings J.stableCoverings ≤ J := by
  change Precoverage.toGrothendieck _ ≤ J
  refine Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr fun U R hR => ?_
  obtain ⟨E, hE, rfl⟩ := hR
  rw [GrothendieckTopology.mem_toPrecoverage_iff]
  exact hE.1

/-- `J` is *the topology of a site*: it is generated by its stable covering families, those
along whose members every fibre product exists. By
`CategoryTheory.GrothendieckTopology.isStacksSite_iff` this says exactly that `J` is the
topology of a class of covering families satisfying the axioms of a site in the sense of Stacks
00VH, whose base change axiom asks only for fibre products of coverings with arbitrary
morphisms. -/
class IsStacksSite : Prop where
  topologyOfCoverings_stableCoverings : topologyOfCoverings J.stableCoverings = J

/-- The topology of a class of covering families satisfying the site axioms is the topology of a
site: every such covering family is stable, by the base change axiom. -/
theorem isStacksSite_of_isSite (Cov : Covering.{u, u, u} C → Prop) (hCov : IsSite Cov)
    (hJ : topologyOfCoverings Cov = J) : J.IsStacksSite := by
  refine ⟨le_antisymm J.topologyOfCoverings_stableCoverings_le (le_trans (le_of_eq hJ.symm) ?_)⟩
  change Precoverage.toGrothendieck _ ≤ _
  refine Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr fun U R hR => ?_
  obtain ⟨E, hE, rfl⟩ := hR
  rw [GrothendieckTopology.mem_toPrecoverage_iff]
  refine Precoverage.generate_mem_toGrothendieck ⟨E, ⟨?_, fun i W h => ?_⟩, rfl⟩
  · rw [GrothendieckTopology.mem_toCoverage_iff]
    have h : Sieve.generate E.presieve₀ ∈ topologyOfCoverings Cov U :=
      Precoverage.generate_mem_toGrothendieck ⟨E, hE, rfl⟩
    rwa [hJ] at h
  · obtain ⟨P, π₁, π₂, sq, -⟩ := hCov.2.2 ⟨U, E⟩ hE W h
    exact (sq i).hasPullback

/-- `J` is the topology of a site exactly when it is the topology of some class of covering
families satisfying the site axioms. -/
theorem isStacksSite_iff :
    J.IsStacksSite ↔
      ∃ Cov : Covering.{u, u, u} C → Prop, IsSite Cov ∧ topologyOfCoverings Cov = J :=
  ⟨fun h => ⟨J.stableCoverings, J.isSite_stableCoverings, h.1⟩,
    fun ⟨Cov, hCov, hJ⟩ => J.isStacksSite_of_isSite Cov hCov hJ⟩

/-- When every covering family of `J` has all its fibre products, which forces the category to
have all fibre products, `J` is the topology of a site. -/
instance isStacksSite_of_hasPullbacks [J.toCoverage.HasPullbacks] : J.IsStacksSite :=
  J.isStacksSite_of_isSite _ J.isSite_coverings J.topologyOfCoverings_coverings

end GrothendieckTopology

/-! ### The stable covering families of `C/K` -/

namespace SemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- The covering families of `C/K`: the families whose image under the localization functor
`C/K ⥤ C` is a stable covering family of `J`. -/
def stableComponentCoverings (K : FormalCoproduct.{u} C) :
    Covering.{u, u, u} (ComponentOver K) → Prop := fun 𝒰 =>
  J.stableCoverings ⟨(componentOverForget K).obj 𝒰.1, 𝒰.2.map (componentOverForget K)⟩

variable {J}

/-- The inclusion of a component of `C/K`. -/
local notation "ιₒ[" K' "]" =>
  CategoryTheory.Sigma.incl (C := fun j : FormalCoproduct.I K' => Over (FormalCoproduct.obj K' j))

/-- A cospan of `C/K` whose image in `C` has a fibre product has a fibre product, preserved by
the localization functor. -/
theorem exists_isPullback_componentOverForget {K : FormalCoproduct.{u} C}
    {A B Z : ComponentOver K} (e : A ⟶ Z) (g : B ⟶ Z)
    (hpb : HasPullback ((componentOverForget K).map e) ((componentOverForget K).map g)) :
    ∃ (P : ComponentOver K) (π₁ : P ⟶ A) (π₂ : P ⟶ B), IsPullback π₁ π₂ e g ∧
      IsPullback ((componentOverForget K).map π₁) ((componentOverForget K).map π₂)
        ((componentOverForget K).map e) ((componentOverForget K).map g) := by
  obtain ⟨i, A⟩ := A
  obtain ⟨i', B⟩ := B
  obtain ⟨j, Z⟩ := Z
  obtain ⟨e⟩ := e
  obtain ⟨g⟩ := g
  change HasPullback e.left g.left at hpb
  have : HasPullback e g := Over.hasPullback_of_left e g
  refine ⟨⟨_, pullback e g⟩, (ιₒ[K] _).map (pullback.fst e g),
    (ιₒ[K] _).map (pullback.snd e g),
    CategoryTheory.Sigma.isPullback_incl_map (D := fun j : K.I => Over (K.obj j))
      (IsPullback.of_hasPullback e g), ?_⟩
  exact (IsPullback.of_hasPullback e g).map (Over.forget _)

/-- The image of a family of `C/K` generates a covering sieve of `J` only if the family generates
a covering sieve of the componentwise topology. -/
theorem generate_mem_componentwiseTopology {K : FormalCoproduct.{u} C} {U : ComponentOver K}
    (E : PreZeroHypercover.{u} U)
    (hE : Sieve.generate (E.map (componentOverForget K)).presieve₀ ∈
      J ((componentOverForget K).obj U)) :
    Sieve.generate E.presieve₀ ∈ componentwiseTopology J K U := by
  obtain ⟨i, X⟩ := U
  rw [mem_componentwiseTopology_iff, GrothendieckTopology.mem_over_iff]
  change Sieve.generate (E.map (componentOverForget K)).presieve₀ ∈ J X.left at hE
  refine J.superset_covering ((Sieve.generate_le_iff _ _).mpr ?_) hE
  rintro _ _ ⟨a⟩
  refine (Sieve.overEquiv_iff _ _).mpr ?_
  -- an arrow of `C/K` into the component `i` comes from the component `i`
  have key : ∀ {A : ComponentOver K} (e : A ⟶ ⟨i, X⟩),
      ∃ m : (⟨i, Over.mk ((componentOverForget K).map e ≫ X.hom)⟩ : ComponentOver K) ⟶ A,
        m ≫ e = (ιₒ[K] i).map (Over.homMk ((componentOverForget K).map e) :
          Over.mk ((componentOverForget K).map e ≫ X.hom) ⟶ X) := by
    rintro ⟨i', A⟩ ⟨e⟩
    exact ⟨(ιₒ[K] i).map (Over.homMk (𝟙 A.left) (by simp [Over.w e]) :
        Over.mk (e.left ≫ X.hom) ⟶ A),
      by
        change _ ≫ (ιₒ[K] i).map e = _
        exact ((ιₒ[K] i).map_comp _ _).symm.trans
          (congrArg (ιₒ[K] i).map (Over.OverMorphism.ext (Category.id_comp _)))⟩
  obtain ⟨m, hm⟩ := key (E.f a)
  exact ⟨_, m, E.f a, Presieve.ofArrows.mk a, hm⟩

/-- The covering families of `C/K` satisfy the axioms of a site, with no assumption on `C`. -/
theorem isSite_stableComponentCoverings (K : FormalCoproduct.{u} C) :
    IsSite (stableComponentCoverings J K) := by
  refine ⟨?_, ?_, ?_⟩
  · intro U V f hf
    exact (J.isSite_stableCoverings).1 ((componentOverForget K).map f)
  · intro 𝒰 h𝒰 𝒱 h𝒱 h
    refine ⟨?_, ?_⟩
    · have hmove : ∀ {A B : C} (e : A = B) {ι : Type u} (X : ι → C) (f : ∀ j, X j ⟶ A),
          Presieve.ofArrows X f ∈ J.toPrecoverage A →
            Presieve.ofArrows X (fun j => f j ≫ eqToHom e) ∈ J.toPrecoverage B := by
        intro A B e ι X f hf
        subst e
        simpa using hf
      have hc := Precoverage.IsStableUnderComposition.comp_mem_coverings
        (J := J.toPrecoverage) (fun i => (componentOverForget K).map (𝒰.2.f i)) h𝒰.1
        (fun i j => (componentOverForget K).map ((𝒱 i).2.f j) ≫
          eqToHom (congrArg (componentOverForget K).obj (h i)))
        fun i => hmove _ _ _ (h𝒱 i).1
      change _ ∈ J.toPrecoverage _
      convert hc using 2
      funext p
      simp [PreZeroHypercover.map, PreZeroHypercover.bind, PreZeroHypercover.pushforward,
        eqToHom_map]
    · rintro ⟨i, j⟩ W k
      change HasPullback ((componentOverForget K).map
        (((𝒱 i).2.f j ≫ eqToHom (h i)) ≫ 𝒰.2.f i)) k
      rw [Functor.map_comp, Functor.map_comp, eqToHom_map]
      exact hasPullback_comp_of_forall
        (hasPullback_comp_of_forall (fun k' => (h𝒱 i).2 j k') fun k' =>
          hasPullback_of_left_iso
            (eqToHom (congrArg (componentOverForget K).obj (h i))) k')
        (fun k' => h𝒰.2 i k') k
  · intro 𝒰 h𝒰 V g
    choose P π₁ π₂ hsq hsqC using fun i =>
      exists_isPullback_componentOverForget (𝒰.2.f i) g
        (h𝒰.2 i ((componentOverForget K).map g))
    exact ⟨P, π₁, π₂, hsq, J.stableCoverings_of_isPullback h𝒰 ((componentOverForget K).map g)
      (fun i => (componentOverForget K).obj (P i)) (fun i => (componentOverForget K).map (π₁ i))
      (fun i => (componentOverForget K).map (π₂ i)) hsqC⟩

/-- Every covering family of `C/K` generates a covering sieve of the componentwise topology. -/
theorem generate_mem_of_stableComponentCoverings {K : FormalCoproduct.{u} C}
    {𝒰 : Covering.{u, u, u} (ComponentOver K)} (h𝒰 : stableComponentCoverings J K 𝒰) :
    Sieve.generate 𝒰.2.presieve₀ ∈ componentwiseTopology J K 𝒰.1 :=
  generate_mem_componentwiseTopology 𝒰.2 h𝒰.1

variable (J) in
/-- On the topology of a site, the covering families of `C/K` generate the componentwise
localized topology. -/
theorem topologyOfCoverings_stableComponentCoverings [J.IsStacksSite]
    (K : FormalCoproduct.{u} C) :
    topologyOfCoverings (stableComponentCoverings J K) = componentwiseTopology J K := by
  apply le_antisymm
  · change Precoverage.toGrothendieck _ ≤ _
    refine Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr fun U R hR => ?_
    obtain ⟨E, hE, rfl⟩ := hR
    rw [GrothendieckTopology.mem_toPrecoverage_iff]
    exact generate_mem_of_stableComponentCoverings hE
  · rintro ⟨i, X⟩ S hS
    rw [mem_componentwiseTopology_iff, GrothendieckTopology.mem_over_iff] at hS
    have hS' : Sieve.overEquiv X (S.functorPullback
        (CategoryTheory.Sigma.incl (C := fun i : K.I => Over (K.obj i)) i)) ∈
          topologyOfCoverings J.stableCoverings X.left := by
      rw [GrothendieckTopology.IsStacksSite.topologyOfCoverings_stableCoverings]
      exact hS
    obtain ⟨E₀, hE₀, hle⟩ := exists_covering_le_of_isSite J.stableCoverings
      J.isSite_stableCoverings ({ coverings := fun U ↦
        { R | ∃ E : PreZeroHypercover.{u} U, J.stableCoverings ⟨U, E⟩ ∧ E.presieve₀ = R } })
      (fun X R => ⟨fun ⟨E, h₁, h₂⟩ => ⟨E, h₂.symm, h₁⟩, fun ⟨E, h₂, h₁⟩ => ⟨E, h₁, h₂.symm⟩⟩)
      _ hS'
    let E : PreZeroHypercover.{u} (⟨i, X⟩ : ComponentOver K) :=
      ⟨E₀.I₀, fun a => ⟨i, Over.mk (E₀.f a ≫ X.hom)⟩,
        fun a => (ιₒ[K] _).map (Over.homMk (E₀.f a))⟩
    have hE : stableComponentCoverings J K ⟨⟨i, X⟩, E⟩ := hE₀
    refine GrothendieckTopology.superset_covering _ ((Sieve.generate_le_iff _ _).mpr ?_)
      (Precoverage.generate_mem_toGrothendieck ⟨E, hE, rfl⟩)
    rintro _ _ ⟨a⟩
    exact (Sieve.overEquiv_iff _ _).mp (hle _ _ (Presieve.ofArrows.mk a))

/-- A cospan of `C/L` formed by an arrow and a map out of a relocalized object, whose image in
`C` has a fibre product, has a representable fibre product in the sense of Stacks 09W7 along the
relocalization functor `C/K ⥤ C/L`, whose image in `C` is that fibre product. -/
theorem exists_isRepresentablePullback_componentOverMap {K L : FormalCoproduct.{u} C}
    (f : K ⟶ L) {i : K.I} {X : Over (K.obj i)} {A Z : ComponentOver L} (e : A ⟶ Z)
    (g : (componentOverMap f).obj ⟨i, X⟩ ⟶ Z)
    (hpb : HasPullback ((componentOverForget L).map e) ((componentOverForget L).map g)) :
    ∃ (P₀ : Over (K.obj i)) (p₁ : (⟨i, P₀⟩ : ComponentOver K) ⟶ ⟨i, X⟩)
      (p₂ : (componentOverMap f).obj ⟨i, P₀⟩ ⟶ A),
      Functor.IsRepresentablePullback (componentOverMap f) g e ⟨i, P₀⟩ p₁ p₂ ∧
        IsPullback ((componentOverForget L).map p₂) ((componentOverForget K).map p₁)
          ((componentOverForget L).map e) ((componentOverForget L).map g) := by
  obtain ⟨k, A⟩ := A
  obtain ⟨k', Z⟩ := Z
  obtain ⟨e⟩ := e
  obtain ⟨g⟩ := g
  change HasPullback e.left g.left at hpb
  let P₀ : Over (K.obj i) := Over.mk (pullback.snd e.left g.left ≫ X.hom)
  let p₁₀ : P₀ ⟶ X := Over.homMk (pullback.snd e.left g.left)
  let p₂₀ : (Over.map (f.φ i)).obj P₀ ⟶ A := Over.homMk (pullback.fst e.left g.left) (by
    have hg := Over.w g
    simp only [Over.map_obj_left, Over.map_obj_hom] at hg
    simp only [P₀, Over.map_obj_hom, Over.mk_hom, Category.assoc]
    rw [← Over.w e, pullback.condition_assoc, hg])
  refine ⟨P₀, (ιₒ[K] _).map p₁₀, (ιₒ[L] _).map p₂₀, ⟨?_, ?_⟩,
    IsPullback.of_hasPullback e.left g.left⟩
  · exact congrArg (ιₒ[L] _).map (by ext; simp [p₁₀, p₂₀, pullback.condition])
  · rintro ⟨k₁, T⟩ ⟨a⟩ b hab
    obtain ⟨b₀, rfl⟩ : ∃ b₀, b = (ιₒ[L] (f.f i)).map b₀ :=
      ⟨(ιₒ[L] (f.f i)).preimage b,
        (Functor.map_preimage (ιₒ[L] (f.f i)) b).symm⟩
    have hab₀ : ((Over.map (f.φ i)).map a ≫ g).left = (b₀ ≫ e).left :=
      congrArg CommaMorphism.left (Sigma.SigmaHom.mk.inj (C := fun j : L.I => Over (L.obj j)) hab)
    simp only [Over.comp_left, Over.map_map_left] at hab₀
    let l₀ : T ⟶ P₀ := Over.homMk (pullback.lift b₀.left a.left hab₀.symm) (by
      change pullback.lift b₀.left a.left hab₀.symm ≫ pullback.snd e.left g.left ≫ X.hom = T.hom
      rw [pullback.lift_snd_assoc]
      exact Over.w a)
    refine ⟨(ιₒ[K] _).map l₀, ⟨congrArg (ιₒ[K] _).map
      (Over.OverMorphism.ext (pullback.lift_snd _ _ _)),
      congrArg (ιₒ[L] _).map (Over.OverMorphism.ext (pullback.lift_fst _ _ _))⟩, ?_⟩
    rintro l ⟨h₁, h₂⟩
    obtain ⟨m, rfl⟩ : ∃ m, l = (ιₒ[K] i).map m :=
      ⟨(ιₒ[K] i).preimage l,
        (Functor.map_preimage (ιₒ[K] i) l).symm⟩
    have h₁' : m.left ≫ pullback.snd e.left g.left = a.left :=
      congrArg CommaMorphism.left (Sigma.SigmaHom.mk.inj (C := fun j : K.I => Over (K.obj j)) h₁)
    have h₂' : m.left ≫ pullback.fst e.left g.left = b₀.left :=
      congrArg CommaMorphism.left (Sigma.SigmaHom.mk.inj (C := fun j : L.I => Over (L.obj j)) h₂)
    refine congrArg (ιₒ[K] _).map (Over.OverMorphism.ext ?_)
    exact pullback.hom_ext (h₂'.trans (pullback.lift_fst _ _ _).symm)
      (h₁'.trans (pullback.lift_snd _ _ _).symm)

/-- **Stacks 0D85, for the covering families of `C/K`.** The componentwise relocalization functor
`C/K ⥤ C/L` has property P of Stacks 09W7: covering families admit representable pullbacks, and
those pullbacks cover. -/
theorem hasCoverPullbacks_stableComponentCoverings {K L : FormalCoproduct.{u} C} (f : K ⟶ L) :
    Functor.HasCoverPullbacks (componentOverMap f) (stableComponentCoverings J K)
      (stableComponentCoverings J L) := by
  rintro 𝒱 h𝒱 ⟨i, X⟩ g
  choose P₀ p₁ p₂ hrep hsq using fun a =>
    exists_isRepresentablePullback_componentOverMap f (𝒱.2.f a) g
      (h𝒱.2 a ((componentOverForget L).map g))
  exact ⟨fun a => ⟨i, P₀ a⟩, p₁, p₂, hrep,
    J.stableCoverings_of_isPullback h𝒱 ((componentOverForget L).map g) (fun a => (P₀ a).left)
      (fun a => (componentOverForget L).map (p₂ a))
      (fun a => (componentOverForget K).map (p₁ a)) hsq⟩

end SemiRepresentable

/-! ### The simplicial site `n ↦ C/K_n` of a site -/

namespace SimplicialSemiRepresentable

open SemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.IsStacksSite]

/-- The covering families of `C/K_n` generate the componentwise localized topology. -/
theorem topologyOfCoverings_stableSliceCoverings (n : SimplexCategoryᵒᵖ) :
    topologyOfCoverings (stableComponentCoverings J (K.obj n)) =
      componentwiseTopology J (K.obj n) :=
  topologyOfCoverings_stableComponentCoverings J (K.obj n)

/-- The simplicial family of sites `n ↦ C/K_n` attached to a simplicial object `K` of `SR(C)`
over a site `(C, J)`, in case (B), with the covering families of
`CategoryTheory.SemiRepresentable.stableComponentCoverings`: the transition functors are
cocontinuous and have property P of Stacks 09W7, both by Stacks 0D85. -/
def stableSimplicialSite : CocontinuousSimplicialSite.{u} where
  underlying := slices K
  coverage n := stableComponentCoverings J (K.obj n)
  isSite n := isSite_stableComponentCoverings (K.obj n)
  isCocontinuous {m n} φ := by
    change (componentOverMap (K.map φ)).IsCocontinuous
      (topologyOfCoverings (stableComponentCoverings J (K.obj m)))
      (topologyOfCoverings (stableComponentCoverings J (K.obj n)))
    rw [topologyOfCoverings_stableSliceCoverings, topologyOfCoverings_stableSliceCoverings]
    exact LocalizationSites.relocalizationFunctor_isCocontinuous (transitionSites J K φ)
  hasCoverPullbacks {_ _} φ := hasCoverPullbacks_stableComponentCoverings (K.map φ)

/-- The simplicial family of sites `n ↦ C/K_n` over a site, read as a simplicial-site
situation. -/
def stableSituation : SimplicialSiteSituation.{u} := ⟨Sum.inr (stableSimplicialSite J K)⟩

/-- The topology of the component site in degree `n` is the componentwise localized topology of
`C/K_n`. -/
theorem stableComponentTopology_eq (n : SimplexCategory) :
    (stableSituation J K).componentTopology n = componentwiseTopology J (K.obj (op n)) :=
  topologyOfCoverings_stableSliceCoverings J K (op n)

/-- The localization functor `j_n : C/K_n ⥤ C` is continuous, by Stacks 0D85. -/
instance stable_sliceForget_isContinuous (n : SimplexCategory) :
    (sliceForget K (op n)).IsContinuous ((stableSituation J K).componentTopology n) J := by
  rw [stableComponentTopology_eq]
  exact LocalizationSites.localizationFunctor_isContinuous
    (⟨K.obj (op n), K.obj (op n), 𝟙 _⟩ : LocalizationSites.{u} C J)

/-- The localization functor `j_n : C/K_n ⥤ C` is cocontinuous, by Stacks 0D85. -/
instance stable_sliceForget_isCocontinuous (n : SimplexCategory) :
    (sliceForget K (op n)).IsCocontinuous ((stableSituation J K).componentTopology n) J := by
  rw [stableComponentTopology_eq]
  exact LocalizationSites.localizationFunctor_isCocontinuous
    (⟨K.obj (op n), K.obj (op n), 𝟙 _⟩ : LocalizationSites.{u} C J)

/-- The localization functor `j_0 : C/K_0 ⥤ C` defines an augmentation of the simplicial site
`n ↦ C/K_n` towards `(C, J)`, as in case (B) of Stacks 0D6Z, as in Stacks 0D8B, for an arbitrary
site. -/
@[stacks 0D8B "j_0 defines an augmentation a_0 : Sh(C/K_0) to Sh(C), case (B) of 0D6Z"]
def stableAugmentation : (stableSimplicialSite J K).Augmentation (Cat.of C) J where
  functor := sliceForget K (op (SimplexCategory.mk 0))
  isCocontinuous := stable_sliceForget_isCocontinuous J K (SimplexCategory.mk 0)
  compatibility _ φ ψ :=
    (slicesMap_comp_sliceForget K φ.op).trans (slicesMap_comp_sliceForget K ψ.op).symm

/-- The augmentation of the simplicial-site situation attached to `K`. -/
def stableSituationAugmentation :
    SimplicialSiteSituation.Augmentation (stableSituation J K) (Cat.of C) J :=
  stableAugmentation J K

/-- The functor out of the total category attached to the augmentation `j_0` is the localization
functor `j_total` of the total site. -/
theorem stableTotalAugmentationFunctor_eq :
    CocontinuousSimplicialSite.Augmentation.totalAugmentationFunctor (stableAugmentation J K) =
      totalForget K := by
  have h : CocontinuousSimplicialSite.Augmentation.totalAugmentationFibre
      (stableAugmentation J K) = sliceForget K :=
    funext fun c => slicesMap_comp_sliceForget K (CocontinuousSimplicialSite.degreeZeroVertexOp c)
  rw [CocontinuousSimplicialSite.Augmentation.totalAugmentationFunctor, totalForget]
  exact Grothendieck.functorFromOfEq_congr _ _ _ _ _ _ _ _ h

/-- The localization functor `j_total` of the total site is cocontinuous. -/
instance stable_totalForget_isCocontinuous :
    (totalForget K).IsCocontinuous ((stableSituation J K).totalTopology) J := by
  rw [← stableTotalAugmentationFunctor_eq J K]
  exact CocontinuousSimplicialSite.Augmentation.totalAugmentationFunctor_isCocontinuous
    (stableAugmentation J K)

/-- The localization functor `j_total` of the total site is continuous: the total topology is
generated by the covering families of the individual simplicial degrees, and the restriction of
`j_total` to a degree is `j_c`, which is continuous. -/
instance stable_totalForget_isContinuous :
    (totalForget K).IsContinuous ((stableSituation J K).totalTopology) J := by
  constructor
  intro G
  refine isSheaf_topologyOfCoverings
    (SimplicialCoverings.total_isSite (slices K) (stableSimplicialSite J K).coverage
      (stableSimplicialSite J K).isSite (stableSimplicialSite J K).isCocontinuous
      (stableSimplicialSite J K).hasCoverPullbacks) _ ?_
  intro X E hE
  obtain ⟨E', hE', hEeq⟩ : ∃ E'' : PreZeroHypercover.{u} X.fiber,
      stableComponentCoverings J (K.obj X.base) ⟨X.fiber, E''⟩ ∧
        E = E''.map (Grothendieck.ι (slices K) X.base) := hE
  subst hEeq
  refine Presieve.isSheafFor_presieve₀_map (Grothendieck.ι (slices K) X.base) _ E' ?_
  have hre : (Grothendieck.ι (slices K) X.base).op ⋙ (totalForget K).op ⋙ G.obj =
      (sliceForget K X.base).op ⋙ G.obj :=
    congrArg (fun F : ((slices K).obj X.base : Cat.{u, u}) ⥤ C => F.op ⋙ G.obj)
      (ι_comp_totalForget K X.base)
  rw [hre]
  have h2 : Sieve.generate E'.presieve₀ ∈ componentwiseTopology J (K.obj X.base) X.fiber :=
    generate_mem_componentwiseTopology (K := K.obj X.base) E' hE'.1
  exact (Presieve.isSheafFor_iff_generate _).mpr
    ((sliceForget_isContinuous_componentwise J K X.base).op_comp_isSheaf_of_types G _ h2)

/-- The morphism of topoi `Sh(C/K_n) ⟶ Sh(C)` of the continuous and cocontinuous localization
functor `j_n`: its inverse image is restriction along `j_n`. -/
def stableLocalizationMorphism (n : SimplexCategory) :
    MorphismOfTopoi (Sheaf ((stableSituation J K).componentTopology n) (Type u))
      (Sheaf J (Type u)) where
  pushforward := (sliceForget K (op n)).sheafPushforwardCocontinuous (Type u)
    ((stableSituation J K).componentTopology n) J
  inverseImage := (sliceForget K (op n)).sheafPushforwardContinuous (Type u)
    ((stableSituation J K).componentTopology n) J
  adj := (sliceForget K (op n)).sheafAdjunctionCocontinuous (Type u)
    ((stableSituation J K).componentTopology n) J
  preservesFiniteLimits :=
    Functor.preservesFiniteLimits_sheafPushforwardContinuous _ _ (sliceForget K (op n)) (Type u)

/-- The morphism of topoi `Sh((C/K)_total) ⟶ Sh(C)` of the continuous and cocontinuous
localization functor `j_total`: its inverse image is restriction along `j_total`. -/
def stableTotalLocalizationMorphism :
    MorphismOfTopoi (Sheaf ((stableSituation J K).totalTopology) (Type u)) (Sheaf J (Type u)) where
  pushforward := (totalForget K).sheafPushforwardCocontinuous (Type u)
    ((stableSituation J K).totalTopology) J
  inverseImage := (totalForget K).sheafPushforwardContinuous (Type u)
    ((stableSituation J K).totalTopology) J
  adj := (totalForget K).sheafAdjunctionCocontinuous (Type u)
    ((stableSituation J K).totalTopology) J
  preservesFiniteLimits :=
    Functor.preservesFiniteLimits_sheafPushforwardContinuous _ _ (totalForget K) (Type u)

/-- The morphism of topoi `a_n : Sh(C/K_n) ⟶ Sh(C)` which Stacks 0D70 attaches to the
augmentation `j_0` is the morphism of topoi of the localization functor `j_n`: their direct
images agree canonically, as in Stacks 0D8B, for an arbitrary site. -/
@[stacks 0D8B "a_n is the morphism of topoi of j_n: direct images"]
def stableComponentPushforwardIso (n : SimplexCategory) :
    (SimplicialSiteSituation.Augmentation.componentAugmentation (stableSituation J K) (Cat.of C)
        J (stableSituationAugmentation J K) n).pushforward ≅
      (stableLocalizationMorphism J K n).pushforward := by
  have h1 : (componentOverMap (K.map (SimplexCategory.const (SimplexCategory.mk 0) n 0).op
      )).IsCocontinuous ((stableSituation J K).componentTopology n)
      ((stableSituation J K).componentTopology (SimplexCategory.mk 0)) :=
    (stableSimplicialSite J K).isCocontinuous _
  have h2 : (sliceForget K (op (SimplexCategory.mk 0))).IsCocontinuous
      ((stableSituation J K).componentTopology (SimplexCategory.mk 0)) J :=
    stable_sliceForget_isCocontinuous J K (SimplexCategory.mk 0)
  have h3 : (componentOverMap (K.map (SimplexCategory.const (SimplexCategory.mk 0) n 0).op) ⋙
      sliceForget K (op (SimplexCategory.mk 0))).IsCocontinuous
      ((stableSituation J K).componentTopology n) J :=
    @CategoryTheory.isCocontinuous_comp _ _ _ _ _ _ _ _
      ((stableSituation J K).componentTopology n)
      ((stableSituation J K).componentTopology (SimplexCategory.mk 0)) J h1 h2
  have h4 : (sliceForget K (op n)).IsCocontinuous ((stableSituation J K).componentTopology n) J :=
    stable_sliceForget_isCocontinuous J K n
  exact (@sheafPushforwardCocontinuousCompIso _ _ _ _ _ _
        ((stableSituation J K).componentTopology n)
        ((stableSituation J K).componentTopology (SimplexCategory.mk 0)) J
        (componentOverMap (K.map (SimplexCategory.const (SimplexCategory.mk 0) n 0).op))
        (sliceForget K (op (SimplexCategory.mk 0))) h1 h2).symm ≪≫
      @SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} _ _ _ _
        ((stableSituation J K).componentTopology n) J _ _ h3 h4
        (slicesMap_comp_sliceForget K (SimplexCategory.const (SimplexCategory.mk 0) n 0).op)

/-- **Stacks 0D8B.** The same identification in inverse images, obtained from uniqueness of left
adjoints. -/
@[stacks 0D8B "a_n is the morphism of topoi of j_n: inverse images"]
def stableComponentInverseImageIso (n : SimplexCategory) :
    (SimplicialSiteSituation.Augmentation.componentAugmentation (stableSituation J K) (Cat.of C)
        J (stableSituationAugmentation J K) n).inverseImage ≅
      (stableLocalizationMorphism J K n).inverseImage :=
  Adjunction.leftAdjointUniq
    (SimplicialSiteSituation.Augmentation.componentAugmentation (stableSituation J K) (Cat.of C)
      J (stableSituationAugmentation J K) n).adj
    ((stableLocalizationMorphism J K n).adj.ofNatIsoRight
      (stableComponentPushforwardIso J K n).symm)

/-- The morphism of topoi `a : Sh((C/K)_total) ⟶ Sh(C)` which Stacks 0D70 attaches to the
augmentation `j_0` has the direct image of the morphism of topoi of `j_total`, up to the
canonical isomorphism coming from the equality of the two functors. -/
def stableTotalPushforwardIso :
    (CocontinuousSimplicialSite.Augmentation.totalMorphismOfTopoi
        (stableAugmentation J K)).pushforward ≅
      (stableTotalLocalizationMorphism J K).pushforward := by
  have h1 : (CocontinuousSimplicialSite.Augmentation.totalAugmentationFunctor
      (stableAugmentation J K)).IsCocontinuous ((stableSituation J K).totalTopology) J :=
    CocontinuousSimplicialSite.Augmentation.totalAugmentationFunctor_isCocontinuous
      (stableAugmentation J K)
  exact @SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} _ _ _ _
    ((stableSituation J K).totalTopology) J _ _ h1 (stable_totalForget_isCocontinuous J K)
    (stableTotalAugmentationFunctor_eq J K)

/-- **Stacks 0D8B.** The same identification in inverse images, obtained from uniqueness of left
adjoints. -/
@[stacks 0D8B "a is the morphism of topoi of j_total: inverse images"]
def stableTotalInverseImageIso :
    (CocontinuousSimplicialSite.Augmentation.totalMorphismOfTopoi
        (stableAugmentation J K)).inverseImage ≅
      (stableTotalLocalizationMorphism J K).inverseImage :=
  Adjunction.leftAdjointUniq
    (CocontinuousSimplicialSite.Augmentation.totalMorphismOfTopoi (stableAugmentation J K)).adj
    ((stableTotalLocalizationMorphism J K).adj.ofNatIsoRight (stableTotalPushforwardIso J K).symm)

/-! ### The lower shriek on sheaves of sets -/

/-- The extension by zero `a^{Sh}_! : Sh((C/K)_total) ⥤ Sh(C)` along the augmentation: the sheaf
pullback along the localization functor `j_total` of the total site. -/
def stableSheafLowerShriek :
    Sheaf ((stableSituation J K).totalTopology) (Type u) ⥤ Sheaf J (Type u) :=
  Functor.sheafPullbackConstruction.sheafPullback (totalForget K) (Type u)
    ((stableSituation J K).totalTopology) J

/-- **Stacks 09WM, part (1).** Let `(C, J)` be a site and `K` a simplicial object of `SR(C)`.
The functor `a^{Sh}_! : Sh((C/K)_total) ⥤ Sh(C)` is left adjoint to the inverse image
`a^{-1} : Sh(C) ⥤ Sh((C/K)_total)` of the augmentation.

The inverse image of the augmentation is restriction along `j_total`, because `j_total` is
cocontinuous as well as continuous, and restriction along a continuous functor has a left
adjoint. -/
@[stacks 09WM "part (1): the left adjoint on sheaves of sets"]
def stableSheafLowerShriekAdjunction :
    stableSheafLowerShriek J K ⊣
      (CocontinuousSimplicialSite.Augmentation.totalMorphismOfTopoi
        (stableAugmentation J K)).inverseImage :=
  ((totalForget K).sheafAdjunctionLowerShriek (Type u)
    ((stableSituation J K).totalTopology) J).ofNatIsoRight (stableTotalInverseImageIso J K).symm

/-! ### The lower shriek on abelian sheaves -/

/-- The extension by zero `a_! : Ab((C/K)_total) ⥤ Ab(C)` along the augmentation: the sheaf
pullback of abelian sheaves along the localization functor `j_total` of the total site. -/
def stableAbelianLowerShriek :
    Sheaf ((stableSituation J K).totalTopology) AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
  Functor.sheafPullbackConstruction.sheafPullback (totalForget K) AddCommGrpCat.{u}
    ((stableSituation J K).totalTopology) J

/-- **Stacks 09WM, part (2).** Let `(C, J)` be a site and `K` a simplicial object of `SR(C)`.
The functor `a_! : Ab((C/K)_total) ⥤ Ab(C)` is left adjoint to the inverse image
`a^{-1} : Ab(C) ⥤ Ab((C/K)_total)` of the augmentation, which on abelian sheaves as on sheaves
of sets is restriction along the continuous and cocontinuous functor `j_total` (Stacks 00XR). -/
@[stacks 09WM "part (2): the left adjoint on abelian sheaves"]
def stableAbelianLowerShriekAdjunction :
    stableAbelianLowerShriek J K ⊣
      (totalForget K).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((stableSituation J K).totalTopology) J :=
  (totalForget K).sheafAdjunctionLowerShriek AddCommGrpCat.{u}
    ((stableSituation J K).totalTopology) J

/-! ### The inverse image in a simplicial degree -/

/-- **Stacks 09WM, part (3).** Let `(C, J)` be a site and `K` a simplicial object of `SR(C)`.
The inverse image of the augmentation followed by restriction to the simplicial degree `n` is
the inverse image `a_n^{-1}` of the augmentation of that degree, which is restriction along the
localization functor `j_n : C/K_n ⥤ C`. So `a^{-1}ℱ` is in degree `n` the sheaf `a_n^{-1}ℱ`. -/
@[stacks 09WM "part (3): the inverse image in each simplicial degree"]
def stableInverseImageComponentIso (n : SimplexCategory) :
    (CocontinuousSimplicialSite.Augmentation.totalMorphismOfTopoi
          (stableAugmentation J K)).inverseImage ⋙ (stableSituation J K).restrict n ≅
      (stableLocalizationMorphism J K n).inverseImage :=
  Functor.isoWhiskerLeft _
      (SimplicialSiteSituation.componentInverseImageIsoPushforward (stableSituation J K) n).symm ≪≫
    CocontinuousSimplicialSite.Augmentation.componentInclusionCompInverseImageIso
      (stableAugmentation J K) n ≪≫
    stableComponentInverseImageIso J K n

/-! ### The abelian direct image as an equalizer -/

variable (G : Sheaf ((stableSituation J K).totalTopology) AddCommGrpCat.{u})

/-- The cosimplicial abelian sheaf `n ↦ a_{n,*}𝒢_n` on `(C, J)` attached to an abelian sheaf `𝒢`
on the total site. -/
def stableAbelianComponentDiagram : CosimplicialObject (Sheaf J AddCommGrpCat.{u}) :=
  SimplicialSiteSituation.Augmentation.abelianCechDiagram (stableSituation J K) (Cat.of C) J
    (stableSituationAugmentation J K) G

/-- The term of `n ↦ a_{n,*}𝒢_n` in simplicial degree `n`. -/
theorem stableAbelianComponentDiagram_obj (n : SimplexCategory) :
    (stableAbelianComponentDiagram J K G).obj n =
      (SimplicialSiteSituation.Augmentation.abelianComponentPushforward (stableSituation J K)
        (Cat.of C) J (stableSituationAugmentation J K) n).obj G := rfl

/-- The cone over `n ↦ a_{n,*}𝒢_n` with vertex the direct image `a_*𝒢`. -/
def stableAbelianPushforwardCone : Cone (stableAbelianComponentDiagram J K G) :=
  SimplicialSiteSituation.Augmentation.abelianCechCone (stableSituation J K) (Cat.of C) J
    (stableSituationAugmentation J K) G

/-- **Stacks 09WM, part (4).** Let `(C, J)` be a site and `K` a simplicial object of `SR(C)`.
The fork of the direct image `a_*𝒢` of an abelian sheaf on the total site over the two maps
`a_{0,*}𝒢_0 ⟶ a_{1,*}𝒢_1` attached to the two vertices of the one-simplex, which are the two
cofaces of the cosimplicial sheaf `n ↦ a_{n,*}𝒢_n`. Its map is the canonical projection of
`a_*𝒢` onto `a_{0,*}𝒢_0`. -/
@[stacks 09WM "part (4): the direct image is the equalizer of the two vertex maps"]
def stableAbelianPushforwardFork :
    Fork ((stableAbelianComponentDiagram J K G).map
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0))
      ((stableAbelianComponentDiagram J K G).map
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1)) :=
  Fork.ofι
    (show (SimplicialSiteSituation.Augmentation.abelianTotalPushforward (stableSituation J K)
        (Cat.of C) J (stableSituationAugmentation J K)).obj G ⟶ _ from
      (stableAbelianPushforwardCone J K G).π.app (SimplexCategory.mk 0))
    (CosimplicialObject.cone_condition _ _)

/-- The vertex of that fork is the direct image `a_*𝒢` of Stacks 0D70. -/
theorem stableAbelianPushforwardFork_pt :
    (stableAbelianPushforwardFork J K G).pt =
      (SimplicialSiteSituation.Augmentation.abelianTotalPushforward (stableSituation J K)
        (Cat.of C) J (stableSituationAugmentation J K)).obj G := rfl

/-- **Stacks 09WM, part (4).** That fork is a limit: the direct image `a_*𝒢` is the equalizer of
the two maps `a_{0,*}𝒢_0 ⟶ a_{1,*}𝒢_1`. -/
@[stacks 09WM "part (4): the equalizer is a limit"]
def stableAbelianPushforwardForkIsLimit :
    IsLimit (stableAbelianPushforwardFork J K G) :=
  CosimplicialObject.isLimitForkOfIsLimit _ _
    (SimplicialSiteSituation.Augmentation.abelianCechCone_isLimit (stableSituation J K)
      (Cat.of C) J (stableSituationAugmentation J K) G)

end SimplicialSemiRepresentable

end CategoryTheory

end
