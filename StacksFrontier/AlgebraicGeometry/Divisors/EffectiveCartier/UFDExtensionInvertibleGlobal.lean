module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtensionInvertible
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.Modules.GluedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.ZariskiModuleChartComparison

/-!
# Extending an invertible module across a factorial locus: the Noetherian case

Let `X` be a Noetherian scheme and `U ⊆ X` an open subscheme such that the local ring
`𝒪_{X, x}` is a unique factorization domain at every point `x` outside `U`. Then every invertible
`𝒪_U`-module is the restriction of an invertible `𝒪_X`-module. This is
[Stacks, Tag 0BD9](https://stacks.math.columbia.edu/tag/0BD9) with `X` Noetherian in place of
locally Noetherian; see "What is and is not proved" below.

## The argument

The source extends `ℒ` over one affine chart at a time and assembles the chart extensions with
Zorn's lemma, after a reduction to the case in which `U` is schematically dense. With `X`
quasi-compact the assembly is instead a **Noetherian induction** on the open `U`: the opens of a
Noetherian space satisfy the ascending chain condition, so one may induct on `U` with the
inductive hypothesis available at every strictly larger open.

The induction, `Stacks.UFDExtensionGlobal.exists_isInvertible_restrict_iso`, is run on sheaves of
`𝒪_X`-modules rather than on sheaves on the open subschemes: the statement proved is that a sheaf
of `𝒪_X`-modules whose restriction to `U` is invertible agrees on `U` with a globally invertible
one. That is no loss, because `ℒ` on `U` is the restriction of its own pushforward
(`AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso`), and it keeps every object in a
single category, so no transport along an isomorphism of schemes is needed.

One step of the induction, for `U ≠ ⊤`:

* pick `x ∉ U` and an affine open `W ∋ x`;
* `W` is Noetherian affine and `W ∖ (U ⊓ W)` consists of points outside `U`, so the affine-chart
  step `AlgebraicGeometry.exists_isInvertible_pullback_iso_of_isAffine_of_uniqueFactorization` —
  which is where Tag 0BD8 and the unique factorization hypothesis are used — extends the
  restriction of `N` to `U ⊓ W` to an invertible module `M` on `W`;
* `N` on `U` and the pushforward of `M` on `W` are isomorphic over `U ⊓ W`, so they glue:
  `Stacks.UFDExtensionGlobal.exists_restrict_iso_two` produces a sheaf of `𝒪_X`-modules `G`
  restricting to `N` on `U` and to `M` on `W`;
* `G` is invertible on `U ⊔ W`, because invertibility is local on the base
  (`Stacks.UFDExtensionGlobal.isInvertible_restrict_sup`), and `U ⊔ W` is strictly larger than
  `U` since it contains `x`. The inductive hypothesis applied to `U ⊔ W` and `G` finishes.

In the base case `U = ⊤` the module `N` is itself invertible, again because invertibility is
local on the base.

## The two-chart glueing

The glueing is the two-chart case of Tag 00AM: a `Stacks.SheafOfModules.OModuleGlueData`
indexed by `ULift Bool`, whose comparison isomorphism across the two charts is the sections
equivalence `AlgebraicGeometry.localAppEquiv` of the given isomorphism of the restrictions to
`U₀ ⊓ U₁`, and the identity on the diagonal. The restriction law and the cocycle condition reduce
case by case to the naturality (`AlgebraicGeometry.localAppFun_naturality`) and the functoriality
(`AlgebraicGeometry.localAppFun_comp`) of that sections equivalence, together with the two
round-trip identities of a linear equivalence. The comparison of the glued sheaf with the two
given ones is `Stacks.SheafOfModules.OModuleGlueData.ofModulesRestrictIso`.

## Invertibility is local on the base

`Stacks.UFDExtensionGlobal.isInvertible_of_isInvertible_restrict` is the statement that a sheaf
of modules on a scheme whose restriction to each member of an open cover is invertible is
invertible. It is proved through the rank-one characterization of invertibility
(`Stacks.ModuleDescent.isInvertible_iff_isFiniteLocallyFreeOfRank_one`), since finite local
freeness of a fixed rank *is* local on the base
(`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top`).

## Main results

* `AlgebraicGeometry.exists_isInvertible_pullback_iso_of_uniqueFactorization`: the conclusion of
  Tag 0BD9 for a Noetherian scheme; untagged, because Noetherianness is not a hypothesis of the
  tag.
* `Stacks.UFDExtensionGlobal.exists_isInvertible_restrict_iso`: the Noetherian induction behind
  it, stated for a sheaf of `𝒪_X`-modules invertible on `U`.
* `Stacks.UFDExtensionGlobal.exists_restrict_iso_two`: the two-chart glueing of sheaves of
  modules.
* `Stacks.UFDExtensionGlobal.isInvertible_of_isInvertible_restrict`,
  `Stacks.UFDExtensionGlobal.isInvertible_restrict_sup`: invertibility is local on the base.

## What is and is not proved

Tag 0BD9 is stated for `X` *locally* Noetherian. What is proved here is the Noetherian case, that
is, with the extra hypothesis `[AlgebraicGeometry.IsNoetherian X]` — locally Noetherian together
with quasi-compactness. Quasi-compactness is used only to make the complement of `U` satisfy a
descending chain condition, i.e. to replace the source's Zorn-lemma assembly of the chart
extensions by the Noetherian induction above; in particular the source's reduction to a
schematically dense `U` is not needed and does not appear. The tag itself, on the source's own
hypotheses, is `AlgebraicGeometry.exists_isInvertible_pullback_iso_of_isLocallyNoetherian`.

## References

* [Stacks Project, Tag 0BD9](https://stacks.math.columbia.edu/tag/0BD9)
* [Stacks Project, Tag 0BD8](https://stacks.math.columbia.edu/tag/0BD8)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.UFDExtensionGlobal

/-- Invertibility of a sheaf of modules on a scheme is finite local freeness of rank one, in the
pointwise form of that predicate. -/
theorem isInvertible_iff_isFiniteLocallyFreeOfRank_one {X : Scheme.{u}} (M : X.Modules) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M ↔
      Scheme.Modules.IsFiniteLocallyFreeOfRank M 1 :=
  (Stacks.ModuleDescent.isInvertible_iff_isFiniteLocallyFreeOfRank_one X M).trans
    (Scheme.Modules.isFiniteLocallyFreeOfRank_iff M 1).symm

/-- Invertibility depends only on the isomorphism class of a sheaf of modules. -/
theorem isInvertible_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (h : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N :=
  (isInvertible_iff_isFiniteLocallyFreeOfRank_one N).2
    (Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso e
      ((isInvertible_iff_isFiniteLocallyFreeOfRank_one M).1 h))

/-- The restriction of an invertible module along an open immersion is invertible. -/
theorem isInvertible_restrict {X Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g] (M : Y.Modules)
    (h : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (M.restrict g) :=
  (isInvertible_iff_isFiniteLocallyFreeOfRank_one _).2
    (Scheme.Modules.IsFiniteLocallyFreeOfRank.restrict g
      ((isInvertible_iff_isFiniteLocallyFreeOfRank_one M).1 h))

/-- **Restriction along a factored open immersion.** If an open immersion `f'` factors as
`φ ≫ f` through an open immersion `f`, then restricting along `f'` is restricting along `f` and
then along `φ`. -/
noncomputable def restrictCongrComp {X Z Z' : Scheme.{u}} {f : Z ⟶ X} [IsOpenImmersion f]
    {f' : Z' ⟶ X} [IsOpenImmersion f'] {φ : Z' ⟶ Z} [IsOpenImmersion φ] (hφ : φ ≫ f = f')
    (M : X.Modules) : M.restrict f' ≅ (M.restrict f).restrict φ :=
  ((Scheme.Modules.restrictFunctorCongr hφ).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorComp φ f).app M

/-- An isomorphism of the restrictions along `f`, transported to a factor `φ ≫ f = f'`. -/
noncomputable def restrictIsoCongr {X Z Z' : Scheme.{u}} {f : Z ⟶ X} [IsOpenImmersion f]
    {f' : Z' ⟶ X} [IsOpenImmersion f'] {φ : Z' ⟶ Z} [IsOpenImmersion φ] (hφ : φ ≫ f = f')
    {M N : X.Modules} (e : M.restrict f ≅ N.restrict f) : M.restrict f' ≅ N.restrict f' :=
  restrictCongrComp hφ M ≪≫ (Scheme.Modules.restrictFunctor φ).mapIso e ≪≫
    (restrictCongrComp hφ N).symm

/-- Two open immersions with the same open range have the same range as sets. -/
theorem range_eq_of_opensRange_eq {X Z Z' : Scheme.{u}} {f : Z ⟶ X} [IsOpenImmersion f]
    {f' : Z' ⟶ X} [IsOpenImmersion f'] (h : f'.opensRange = f.opensRange) :
    Set.range f'.base = Set.range f.base :=
  congrArg (fun S : X.Opens => (S : Set X)) h

/-- **Invertibility is local on the base.** A sheaf of modules whose restriction to every member
of an open cover of the scheme is invertible is itself invertible. -/
theorem isInvertible_of_isInvertible_restrict {X : Scheme.{u}} (M : X.Modules) {ι : Type*}
    (U : ι → X.Opens) (hU : iSup U = ⊤)
    (h : ∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible (U i).toScheme.sheaf.obj
      (U i).toScheme.ringCatSheaf.property (M.restrict (U i).ι)) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
  (isInvertible_iff_isFiniteLocallyFreeOfRank_one M).2
    (Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top U hU fun i =>
      (isInvertible_iff_isFiniteLocallyFreeOfRank_one _).1 (h i))

section TwoChart

variable {X : Scheme.{u}}

/-- The two opens of a two-chart glueing datum, indexed by `Bool`. -/
def twoOpens (U₀ U₁ : X.Opens) (i : ULift.{u} Bool) : X.Opens := cond i.down U₁ U₀

/-- The two sheaves of modules of a two-chart glueing datum, indexed by `Bool`. -/
def twoMods (N₀ N₁ : X.Modules) (i : ULift.{u} Bool) : X.Modules := cond i.down N₁ N₀

variable {U₀ U₁ : X.Opens} {N₀ N₁ : X.Modules}
  (ψ : N₀.restrict (U₀ ⊓ U₁ : X.Opens).ι ≅ N₁.restrict (U₀ ⊓ U₁ : X.Opens).ι)

/-- The comparison isomorphisms of the two-chart glueing datum: the identity on the diagonal, and
the sections equivalence of `ψ` across. -/
noncomputable def twoTrans (i j : ULift.{u} Bool) {V : X.Opens}
    (hi : V ≤ twoOpens U₀ U₁ i) (hj : V ≤ twoOpens U₀ U₁ j) :
    (twoMods N₀ N₁ i).val.obj (op V) ≃ₗ[ToType (X.ringCatSheaf.obj.obj (op V))]
      (twoMods N₀ N₁ j).val.obj (op V) :=
  match i, j, hi, hj with
  | ⟨false⟩, ⟨false⟩, _, _ => LinearEquiv.refl _ _
  | ⟨true⟩, ⟨true⟩, _, _ => LinearEquiv.refl _ _
  | ⟨false⟩, ⟨true⟩, hi, hj => localAppEquiv ψ V (le_inf hi hj)
  | ⟨true⟩, ⟨false⟩, hi, hj => (localAppEquiv ψ V (le_inf hj hi)).symm

/-- The comparison isomorphisms of the two-chart datum commute with the restriction maps. -/
theorem twoTrans_map (i j : ULift.{u} Bool) {V W : X.Opens} (hi : V ≤ twoOpens U₀ U₁ i)
    (hj : V ≤ twoOpens U₀ U₁ j) (hWV : W ≤ V)
    (s : ToType ((twoMods N₀ N₁ i).val.obj (op V))) :
    twoTrans ψ i j (hWV.trans hi) (hWV.trans hj)
        ((twoMods N₀ N₁ i).val.map (homOfLE hWV).op s)
      = (twoMods N₀ N₁ j).val.map (homOfLE hWV).op (twoTrans ψ i j hi hj s) := by
  obtain ⟨i⟩ := i; obtain ⟨j⟩ := j
  cases i <;> cases j
  · rfl
  · exact (localAppFun_naturality ψ.hom (le_inf hi hj) (le_inf (hWV.trans hi) (hWV.trans hj))
      (homOfLE hWV) s).symm
  · refine (localAppEquiv ψ W (le_inf (hWV.trans hj) (hWV.trans hi))).symm_apply_eq.2 ?_
    refine Eq.symm ?_
    refine (localAppFun_naturality ψ.hom (le_inf hj hi)
      (le_inf (hWV.trans hj) (hWV.trans hi)) (homOfLE hWV) _).symm.trans ?_
    exact congrArg (N₁.val.map (homOfLE hWV).op)
      ((localAppEquiv ψ V (le_inf hj hi)).apply_symm_apply s)
  · rfl

/-- The comparison isomorphisms of the two-chart datum satisfy the cocycle condition. -/
theorem twoTrans_trans (i j k : ULift.{u} Bool) {V : X.Opens} (hi : V ≤ twoOpens U₀ U₁ i)
    (hj : V ≤ twoOpens U₀ U₁ j) (hk : V ≤ twoOpens U₀ U₁ k)
    (s : ToType ((twoMods N₀ N₁ i).val.obj (op V))) :
    twoTrans ψ j k hj hk (twoTrans ψ i j hi hj s) = twoTrans ψ i k hi hk s := by
  obtain ⟨i⟩ := i; obtain ⟨j⟩ := j; obtain ⟨k⟩ := k
  cases i <;> cases j <;> cases k
  · rfl
  · rfl
  · exact (localAppEquiv ψ V (le_inf hi hj)).symm_apply_apply s
  · rfl
  · rfl
  · exact (localAppEquiv ψ V (le_inf hj hk)).apply_symm_apply s
  · rfl
  · rfl

/-- **Two sheaves of modules compared over the intersection of their charts glue.** Given two
opens `U₀`, `U₁` of a scheme `X`, two sheaves of `𝒪_X`-modules `N₀`, `N₁`, and an isomorphism of
their restrictions to `U₀ ⊓ U₁`, there is a sheaf of `𝒪_X`-modules restricting on `U₀` to `N₀`
and on `U₁` to `N₁`.

This is the two-chart case of [Stacks, Tag 00AM]. -/
theorem exists_restrict_iso_two
    (ψ' : N₀.restrict (U₀ ⊓ U₁ : X.Opens).ι ≅ N₁.restrict (U₀ ⊓ U₁ : X.Opens).ι) :
    ∃ G : X.Modules, Nonempty (G.restrict U₀.ι ≅ N₀.restrict U₀.ι) ∧
      Nonempty (G.restrict U₁.ι ≅ N₁.restrict U₁.ι) := by
  have r := fun b : Bool => Stacks.SheafOfModules.OModuleGlueData.ofModulesRestrictIso
    (U := twoOpens U₀ U₁) (twoMods N₀ N₁) (twoTrans ψ') (twoTrans_map ψ') (twoTrans_trans ψ')
    ⟨b⟩
  exact ⟨_, ⟨r false⟩, ⟨r true⟩⟩

/-- Invertibility of the restriction along an open immersion passes to any open immersion
factoring through it. -/
theorem isInvertible_restrict_of_fac {X Z Z' : Scheme.{u}} {f : Z ⟶ X} [IsOpenImmersion f]
    {f' : Z' ⟶ X} [IsOpenImmersion f'] {φ : Z' ⟶ Z} [IsOpenImmersion φ] (hφ : φ ≫ f = f')
    (M : X.Modules)
    (h : AlgebraicGeometry.SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property
      (M.restrict f)) :
    AlgebraicGeometry.SheafOfModules.IsInvertible Z'.sheaf.obj Z'.ringCatSheaf.property
      (M.restrict f') :=
  isInvertible_of_iso (restrictCongrComp hφ M).symm (isInvertible_restrict φ _ h)

/-- Invertibility of a restriction depends only on the range of the open immersion. -/
theorem isInvertible_restrict_of_range_eq {X Z Z' : Scheme.{u}} (f : Z ⟶ X) [IsOpenImmersion f]
    (f' : Z' ⟶ X) [IsOpenImmersion f'] (h : Set.range f'.base = Set.range f.base)
    (M : X.Modules)
    (hf : AlgebraicGeometry.SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property
      (M.restrict f)) :
    AlgebraicGeometry.SheafOfModules.IsInvertible Z'.sheaf.obj Z'.ringCatSheaf.property
      (M.restrict f') :=
  isInvertible_restrict_of_fac (IsOpenImmersion.isoOfRangeEq_hom_fac f' f h) M hf

/-- **Invertibility of a restriction propagates to the union of two opens.** If a sheaf of
modules restricts to an invertible sheaf on each of two opens, it restricts to an invertible
sheaf on their union. -/
theorem isInvertible_restrict_sup {X : Scheme.{u}} (M : X.Modules) (U W : X.Opens)
    (hU : AlgebraicGeometry.SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property (M.restrict U.ι))
    (hW : AlgebraicGeometry.SheafOfModules.IsInvertible W.toScheme.sheaf.obj
      W.toScheme.ringCatSheaf.property (M.restrict W.ι)) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (U ⊔ W : X.Opens).toScheme.sheaf.obj
      (U ⊔ W : X.Opens).toScheme.ringCatSheaf.property (M.restrict (U ⊔ W : X.Opens).ι) := by
  refine isInvertible_of_isInvertible_restrict _
    (fun b : Bool => cond b ((U ⊔ W : X.Opens).ι ⁻¹ᵁ W) ((U ⊔ W : X.Opens).ι ⁻¹ᵁ U)) ?_ ?_
  · refine eq_top_iff.mpr fun y _ => ?_
    rw [TopologicalSpace.Opens.mem_iSup]
    rcases y.2 with h | h
    exacts [⟨false, h⟩, ⟨true, h⟩]
  · have key : ∀ V : X.Opens, V ≤ U ⊔ W →
        AlgebraicGeometry.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
          V.toScheme.ringCatSheaf.property (M.restrict V.ι) →
        AlgebraicGeometry.SheafOfModules.IsInvertible ((U ⊔ W : X.Opens).ι ⁻¹ᵁ V).toScheme.sheaf.obj
          ((U ⊔ W : X.Opens).ι ⁻¹ᵁ V).toScheme.ringCatSheaf.property
          ((M.restrict (U ⊔ W : X.Opens).ι).restrict
            ((U ⊔ W : X.Opens).ι ⁻¹ᵁ V).ι) := fun V hV hVinv =>
      isInvertible_restrict_of_range_eq (X.homOfLE hV) _
        (range_eq_of_opensRange_eq (by simp)) _
        (isInvertible_of_iso (restrictCongrComp (X.homOfLE_ι hV) M) hVinv)
    intro b
    cases b
    exacts [key U le_sup_left hU, key W le_sup_right hW]

end TwoChart

section Induction

variable {X : Scheme.{u}}

/-- **The Noetherian induction behind [Stacks, Tag 0BD9].** Let `X` be a Noetherian scheme, let
`U ⊆ X` be an open whose complementary points have unique factorization local rings, and let `N`
be a sheaf of `𝒪_X`-modules whose restriction to `U` is invertible. Then there is an invertible
sheaf of `𝒪_X`-modules whose restriction to `U` is isomorphic to that of `N`. -/
theorem exists_isInvertible_restrict_iso [IsNoetherian X] (U : X.Opens) (N : X.Modules)
    (hUFD : ∀ x : X, x ∉ U → UniqueFactorizationMonoid (X.presheaf.stalk x))
    (hN : AlgebraicGeometry.SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property (N.restrict U.ι)) :
    ∃ N' : X.Modules,
      AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N' ∧
        Nonempty (N.restrict U.ι ≅ N'.restrict U.ι) := by
  revert N hUFD hN
  refine WellFoundedGT.induction (α := X.Opens)
    (motive := fun V => ∀ N : X.Modules,
      (∀ x : X, x ∉ V → UniqueFactorizationMonoid (X.presheaf.stalk x)) →
      AlgebraicGeometry.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
        V.toScheme.ringCatSheaf.property (N.restrict V.ι) →
      ∃ N' : X.Modules,
        AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N' ∧
          Nonempty (N.restrict V.ι ≅ N'.restrict V.ι)) U ?_
  clear U
  intro U ih N hUFD hN
  by_cases hUtop : U = ⊤
  · exact ⟨N, isInvertible_of_isInvertible_restrict N (fun _ : Unit => U) (by simp [hUtop])
      fun _ => hN, ⟨Iso.refl _⟩⟩
  obtain ⟨x, hx⟩ : ∃ x : X, x ∉ U := by
    by_contra! hc
    exact hUtop (eq_top_iff.mpr fun y _ => hc y)
  obtain ⟨W, hWaff, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by trivial)
  have : IsAffine W.toScheme := hWaff
  have : CompactSpace W.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (W : Set X))
  have : IsNoetherian W.toScheme :=
    (isNoetherian_iff W.toScheme).2 ⟨inferInstance, inferInstance⟩
  have hrange : Set.range ((W.ι ⁻¹ᵁ U).ι ≫ W.ι).base = Set.range (U ⊓ W : X.Opens).ι.base := by
    rw [Scheme.Opens.range_ι]
    simp [Set.range_comp, Set.image_preimage_eq_inter_range]
  have hfac : (IsOpenImmersion.isoOfRangeEq ((W.ι ⁻¹ᵁ U).ι ≫ W.ι) (U ⊓ W : X.Opens).ι
      hrange).hom ≫ (U ⊓ W : X.Opens).ι = (W.ι ⁻¹ᵁ U).ι ≫ W.ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange
  have hfac' : (IsOpenImmersion.isoOfRangeEq ((W.ι ⁻¹ᵁ U).ι ≫ W.ι) (U ⊓ W : X.Opens).ι
      hrange).inv ≫ ((W.ι ⁻¹ᵁ U).ι ≫ W.ι) = (U ⊓ W : X.Opens).ι :=
    IsOpenImmersion.isoOfRangeEq_inv_fac _ _ hrange
  have hL : AlgebraicGeometry.SheafOfModules.IsInvertible (W.ι ⁻¹ᵁ U).toScheme.sheaf.obj
      (W.ι ⁻¹ᵁ U).toScheme.ringCatSheaf.property (N.restrict ((W.ι ⁻¹ᵁ U).ι ≫ W.ι)) :=
    isInvertible_restrict_of_fac hfac N
      (isInvertible_restrict_of_fac (X.homOfLE_ι (inf_le_left : (U ⊓ W : X.Opens) ≤ U)) N hN)
  have hUFDW : ∀ y : W.toScheme, y ∉ W.ι ⁻¹ᵁ U →
      UniqueFactorizationMonoid (W.toScheme.presheaf.stalk y) := fun y hy =>
    (W.stalkIso y).commRingCatIsoToRingEquiv.toMulEquiv.symm.uniqueFactorizationMonoid
      (hUFD _ hy)
  obtain ⟨M, hM, ⟨eM⟩⟩ :=
    exists_isInvertible_pullback_iso_of_isAffine_of_uniqueFactorization (W := W.toScheme)
      (W.ι ⁻¹ᵁ U) (N.restrict ((W.ι ⁻¹ᵁ U).ι ≫ W.ι)) hUFDW
  have e₁ : N.restrict ((W.ι ⁻¹ᵁ U).ι ≫ W.ι) ≅
      ((Scheme.Modules.pushforward W.ι).obj M).restrict ((W.ι ⁻¹ᵁ U).ι ≫ W.ι) :=
    eM ≪≫ ((Scheme.Modules.restrictFunctorIsoPullback (W.ι ⁻¹ᵁ U).ι).app M).symm ≪≫
      (Scheme.Modules.restrictFunctor (W.ι ⁻¹ᵁ U).ι).mapIso
        ((Scheme.Modules.restrictFunctorAdjCounitIso W.ι).app M).symm ≪≫
      ((Scheme.Modules.restrictFunctorComp (W.ι ⁻¹ᵁ U).ι W.ι).app
        ((Scheme.Modules.pushforward W.ι).obj M)).symm
  obtain ⟨G, ⟨gU⟩, ⟨gW⟩⟩ :=
    exists_restrict_iso_two (U₀ := U) (U₁ := W) (N₀ := N)
      (N₁ := (Scheme.Modules.pushforward W.ι).obj M) (restrictIsoCongr hfac' e₁)
  have hGU : AlgebraicGeometry.SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property (G.restrict U.ι) := isInvertible_of_iso gU.symm hN
  have hGW : AlgebraicGeometry.SheafOfModules.IsInvertible W.toScheme.sheaf.obj
      W.toScheme.ringCatSheaf.property (G.restrict W.ι) :=
    isInvertible_of_iso gW.symm
      (isInvertible_of_iso ((Scheme.Modules.restrictFunctorAdjCounitIso W.ι).app M).symm hM)
  have hle : U ≤ U ⊔ W := le_sup_left
  have hlt : U ⊔ W > U := lt_of_le_of_ne hle fun h =>
    hx ((le_sup_right : W ≤ U ⊔ W).trans h.symm.le hxW)
  obtain ⟨N', hN', ⟨eN'⟩⟩ := ih (U ⊔ W) hlt G
    (fun y hy => hUFD y fun hyU => hy (Or.inl hyU))
    (isInvertible_restrict_sup G U W hGU hGW)
  exact ⟨N', hN', ⟨gU.symm ≪≫ restrictCongrComp (X.homOfLE_ι hle) G ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE hle)).mapIso eN' ≪≫
    (restrictCongrComp (X.homOfLE_ι hle) N').symm⟩⟩

end Induction

end Stacks.UFDExtensionGlobal

namespace AlgebraicGeometry

/-- **The Noetherian case of [Stacks, Tag 0BD9].** Let `X` be a Noetherian scheme, let `U ⊆ X`
be an open subscheme, and let `L` be an invertible `𝒪_U`-module. If the local ring `𝒪_{X, x}` is
a unique factorization domain at every point `x` outside `U`, then `L` is the restriction of an
invertible `𝒪_X`-module.

The source states this for `X` locally Noetherian, which is
`AlgebraicGeometry.exists_isInvertible_pullback_iso_of_isLocallyNoetherian`. -/
theorem exists_isInvertible_pullback_iso_of_uniqueFactorization {X : Scheme.{u}} [IsNoetherian X]
    (U : X.Opens) (L : U.toScheme.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property L]
    (hUFD : ∀ x : X, x ∉ U → UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    ∃ L' : X.Modules,
      AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L' ∧
        Nonempty (L ≅ (Scheme.Modules.pullback U.ι).obj L') := by
  have c : ((Scheme.Modules.pushforward U.ι).obj L).restrict U.ι ≅ L :=
    (Scheme.Modules.restrictFunctorAdjCounitIso U.ι).app L
  obtain ⟨L', hL', ⟨e⟩⟩ := Stacks.UFDExtensionGlobal.exists_isInvertible_restrict_iso U
    ((Scheme.Modules.pushforward U.ι).obj L) hUFD
    (Stacks.UFDExtensionGlobal.isInvertible_of_iso c.symm ‹_›)
  exact ⟨L', hL', ⟨c.symm ≪≫ e ≪≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).app L'⟩⟩

end AlgebraicGeometry

end
