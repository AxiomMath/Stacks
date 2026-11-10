module

public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformAdmissibleOpen
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformProblem.FreeOnSurjectiveOpen
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Basic
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Quasicoherent

/-!
# The standing situation of Stacks 0811 and its two reductions

[Stacks, Tag 0811] starts from a quasi-compact quasi-separated base `S`, an affine, flat morphism
`f : X ⟶ S` of finite presentation with geometrically integral fibres, a quasi-coherent
`𝒪_X`-module `F` of finite type which is of finite presentation over a quasi-compact open
`U ⊆ S`, and which is flat over `S` at every generic point of a fibre over a point of `U`. The
goal is a `U`-admissible blowup after which the strict transform is finite locally free on an open
surjecting onto the blowup.

This file bundles that data as `AlgebraicGeometry.FlatteningSituation`, turns it into the
strict-transform problem of [Stacks, Tag 080Y] for the property
`AlgebraicGeometry.FreeOnSurjectiveOpen`, and shows that the data is carried by the two operations
the reductions of that remark perform: restriction to an open of the base, and the strict
transform along a `U`-admissible blowup.

## Main definitions

* `AlgebraicGeometry.FlatteningSituation`: the data above.
* `AlgebraicGeometry.FlatteningSituation.problem`: it as a strict-transform problem.
* `AlgebraicGeometry.FlatteningSituation.restrict` and
  `AlgebraicGeometry.FlatteningSituation.transform`: the two operations, together with
  `AlgebraicGeometry.FlatteningSituation.problem_restrict` and
  `AlgebraicGeometry.FlatteningSituation.problem_transform` identifying them with the
  corresponding operations on the problem.

## Main results

* `AlgebraicGeometry.fibre_subset_closure_of_pullback`: a point of a base change which is generic
  in its fibre lies over a point which is generic in its fibre.
* `AlgebraicGeometry.isFinitePresentation_restrict_of_le`: finite presentation over an open is
  inherited by a pullback over any open mapping into it.
* `AlgebraicGeometry.FlatteningSituation.exists_freeAtPointOfRank_of_isFlatOverAt`: hypotheses
  (1)–(4) of the source give freeness of some finite rank near every generic point of a fibre
  over `U`, which is the form in which the flatness hypothesis (4) is used.

## Implementation notes

**Why freeness rather than flatness is carried.** The source's hypothesis (4) is flatness of `F`
over `S` at the generic points of the fibres over `U`. Together with (1) and (3) — finite
presentation of the morphism and of `F` over `U` — [Stacks, Tag 080Q] upgrades it, at those
points, to freeness of finite rank on a neighbourhood. That stronger form is what the reductions
carry, because it transports along the strict transform with no extra work:
`AlgebraicGeometry.freeAtPointOfRank_strictTransformSheaf` is exactly the needed statement, and
the rank is unchanged, which is what makes the decomposition by rank survive the reductions.

**Over the distinguished open nothing happens.** The exceptional ideal of a `U`-admissible blowup
is supported over the complement of `U`, so above the inverse image of `U` the quotient map
defining the strict transform is invertible
(`Stacks.StrictTransform.isIso_restrictFunctor_map_π` together with
`AlgebraicGeometry.Scheme.Modules.isIso_restrictFunctor_map_of_le`). That is what carries
hypothesis (3). No statement about the blowup being an isomorphism over `U` is needed.

**The strict transform of the total space.** Since `f` is flat, the strict transform of `X` is the
whole base change ([Stacks, Tag 080F] part (1)), so the defining ideal is `⊥` and its closed
immersion is an isomorphism. Every property of the transformed morphism is read off the base
change through that isomorphism.

## References

* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
* [Stacks Project, Tag 080Q](https://stacks.math.columbia.edu/tag/080Q)
* [Stacks Project, Tag 080F](https://stacks.math.columbia.edu/tag/080F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Two lemmas about base changes -/

/-- The two projections of a pullback have the same image in the base, on underlying points. -/
private theorem base_fst_eq_base_snd {X S T : Scheme.{u}} (f : X ⟶ S) (b : T ⟶ S)
    (z : ↑(Limits.pullback f b)) :
    f.base ((pullback.fst f b).base z) = b.base ((pullback.snd f b).base z) := by
  change (pullback.fst f b ≫ f).base z = (pullback.snd f b ≫ b).base z
  rw [pullback.condition]

/-- **A point of a base change which is generic in its fibre lies over a point which is generic in
its fibre.** For `f : X ⟶ S` and `b : T ⟶ S`, if the fibre of `pr_T` through `z` is contained in
the closure of `z`, then the fibre of `f` through `pr_X z` is contained in the closure of
`pr_X z`: a point of that fibre, paired with `pr_T z`, is realized by a point of the base change,
which therefore lies in the closure of `z`. -/
theorem fibre_subset_closure_of_pullback {X S T : Scheme.{u}} (f : X ⟶ S) (b : T ⟶ S)
    (z : ↥(Limits.pullback f b))
    (hz : (pullback.snd f b).base ⁻¹' {(pullback.snd f b).base z} ⊆ closure {z}) :
    f.base ⁻¹' {f.base ((pullback.fst f b).base z)} ⊆
      closure {(pullback.fst f b).base z} := by
  intro x' hx'
  have hx'eq : f.base x' = b.base ((pullback.snd f b).base z) := by
    rw [show f.base x' = f.base ((pullback.fst f b).base z) from hx', base_fst_eq_base_snd]
  obtain ⟨w, hw₁, hw₂⟩ :=
    Scheme.Pullback.exists_preimage_pullback x' ((pullback.snd f b).base z) hx'eq
  have hspec : z ⤳ w := specializes_iff_mem_closure.mpr (hz hw₂)
  have hspec2 := hspec.map (pullback.fst f b).continuous
  rw [hw₁] at hspec2
  exact specializes_iff_mem_closure.mp hspec2

/-- **Along a base change by an open immersion, generic points of fibres correspond.** This is
the converse of `AlgebraicGeometry.fibre_subset_closure_of_pullback` for `b` an open immersion:
the first projection is then an open immersion too, hence inducing, so it reflects
specializations. -/
theorem fibre_subset_closure_pullback_of_isOpenImmersion {X S T : Scheme.{u}} (f : X ⟶ S)
    (b : T ⟶ S) [IsOpenImmersion b] (z : ↑(Limits.pullback f b))
    (hz : f.base ⁻¹' {f.base ((pullback.fst f b).base z)} ⊆
      closure {(pullback.fst f b).base z}) :
    (pullback.snd f b).base ⁻¹' {(pullback.snd f b).base z} ⊆ closure {z} := by
  intro w hw
  have hfw : f.base ((pullback.fst f b).base w) = f.base ((pullback.fst f b).base z) := by
    rw [base_fst_eq_base_snd, base_fst_eq_base_snd,
      show (pullback.snd f b).base w = (pullback.snd f b).base z from hw]
  have hspec : (pullback.fst f b).base z ⤳ (pullback.fst f b).base w :=
    specializes_iff_mem_closure.mpr (hz hfw)
  exact specializes_iff_mem_closure.mp
    ((pullback.fst f b).isOpenEmbedding.isEmbedding.isInducing.specializes_iff.mp hspec)

/-- **Finite presentation over an open is inherited by a pullback over any open mapping into
it.** If `F` is of finite presentation over `A ⊆ X` and `B ⊆ Y` maps into `A` under `q : Y ⟶ X`,
then the pullback of `F` along `q` is of finite presentation over `B`. -/
theorem isFinitePresentation_restrict_of_le {X Y : Scheme.{u}} (q : Y ⟶ X) (F : X.Modules)
    (A : X.Opens) (hA : (F.restrict A.ι).IsFinitePresentation) (B : Y.Opens)
    (hB : B ≤ q ⁻¹ᵁ A) :
    (((Scheme.Modules.pullback q).obj F).restrict B.ι).IsFinitePresentation := by
  have hrange : Set.range (B.ι ≫ q).base ⊆ Set.range A.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨v, rfl⟩
    exact hB v.2
  set m : B.toScheme ⟶ A.toScheme := IsOpenImmersion.lift A.ι (B.ι ≫ q) hrange with hm
  have hmfac : m ≫ A.ι = B.ι ≫ q := IsOpenImmersion.lift_fac _ _ hrange
  have _ : (F.restrict A.ι).IsFinitePresentation := hA
  have hpull : ((Scheme.Modules.pullback m).obj (F.restrict A.ι)).IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback m (F.restrict A.ι)
  refine (SheafOfModules.isFinitePresentation.{u, u, u} _).prop_of_iso ?_ hpull
  refine (Scheme.Modules.pullback m).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback A.ι).app F) ≪≫ ?_
  refine ((Scheme.Modules.pullbackComp m A.ι).app F) ≪≫ ?_
  refine (Scheme.Modules.pullbackCongr hmfac).app F ≪≫ ?_
  exact ((Scheme.Modules.pullbackComp B.ι q).app F).symm ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback B.ι).app
      ((Scheme.Modules.pullback q).obj F)).symm

/-! ### The standing situation -/

/-- **The standing data of [Stacks, Tag 0811].** A quasi-compact and quasi-separated base, an
affine flat morphism of finite presentation with geometrically integral fibres, a quasi-coherent
module of finite type on its source which is of finite presentation over a quasi-compact open `U`
of the base, and which is finite locally free of some finite rank near every generic point of a
fibre over a point of `U`.

The last field is the source's hypothesis (4) in the strengthened form
`AlgebraicGeometry.FlatteningSituation.exists_freeAtPointOfRank_of_isFlatOverAt` derives from it:
flatness over the base at such a point, together with (1) and (3), *is* finite local freeness
there, by [Stacks, Tag 080Q]. -/
structure FlatteningSituation where
  /-- The base scheme. -/
  S : Scheme.{u}
  [compactSpace : CompactSpace S]
  [quasiSeparatedSpace : QuasiSeparatedSpace S]
  /-- The total space. -/
  X : Scheme.{u}
  /-- The structure morphism. -/
  f : X ⟶ S
  [isAffineHom : IsAffineHom f]
  [flat : Flat f]
  [geometricallyIntegral : GeometricallyIntegral f]
  /-- The structure morphism is of finite presentation. -/
  finitePresentation : AlgebraicGeometry.FinitePresentation f
  /-- The module to be flattened. -/
  F : X.Modules
  [quasicoherent : F.IsQuasicoherent]
  [finiteType : F.IsFiniteType]
  /-- The distinguished open of the base. -/
  U : S.Opens
  /-- The distinguished open is quasi-compact. -/
  compact_U : IsCompact (U : Set S)
  /-- Hypothesis (3): the module is of finite presentation over the distinguished open. -/
  finitePresentation_restrict : (F.restrict (f ⁻¹ᵁ U).ι).IsFinitePresentation
  /-- Hypothesis (4), strengthened: near every generic point of a fibre over the distinguished
  open the module is finite locally free of some finite rank. -/
  free_at_generic : ∀ x : X, f.base x ∈ U → f.base ⁻¹' {f.base x} ⊆ closure {x} →
    ∃ r : ℕ, FreeAtPointOfRank F x r

attribute [instance] FlatteningSituation.compactSpace FlatteningSituation.quasiSeparatedSpace
  FlatteningSituation.isAffineHom FlatteningSituation.flat
  FlatteningSituation.geometricallyIntegral FlatteningSituation.quasicoherent
  FlatteningSituation.finiteType

namespace FlatteningSituation

variable (D : FlatteningSituation.{u})

/-- **The strict-transform problem of [Stacks, Tag 080Y] attached to the situation**, for the
property `AlgebraicGeometry.FreeOnSurjectiveOpen`. -/
def problem : StrictTransformProblem.{u} where
  S := D.S
  X := D.X
  f := D.f
  F := D.F
  U := D.U
  compact_U := D.compact_U
  P := fun g G ↦ FreeOnSurjectiveOpen g G
  invariant_under_iso := freeOnSurjectiveOpen_iff_of_iso
  stable := by
    intro Y T _ _ g G _ p _ I _ _ hP
    exact freeOnSurjectiveOpen_strictTransform g G I hP

/-- The situation is **solvable** when its strict-transform problem is: some `U`-admissible centre
makes the strict transform finite locally free on an open surjecting onto the blowup. -/
def IsSolvable : Prop := D.problem.IsSolvable

/-! ### Restriction to an open of the base -/

/-- **A generic point of a fibre over the inverse image of the distinguished open, in the base
change over an open of the base, lies over such a point of the original situation.** -/
theorem mem_and_fibre_subset_closure_pullback (W : D.S.Opens)
    (z : ↑(Limits.pullback D.f W.ι))
    (hz : (pullback.snd D.f W.ι).base z ∈ (W.ι ⁻¹ᵁ D.U : W.toScheme.Opens))
    (hgen : (pullback.snd D.f W.ι).base ⁻¹' {(pullback.snd D.f W.ι).base z} ⊆ closure {z}) :
    D.f.base ((pullback.fst D.f W.ι).base z) ∈ D.U ∧
      D.f.base ⁻¹' {D.f.base ((pullback.fst D.f W.ι).base z)} ⊆
        closure {(pullback.fst D.f W.ι).base z} ∧
      D.f.base ((pullback.fst D.f W.ι).base z) =
        W.ι.base ((pullback.snd D.f W.ι).base z) := by
  have heq := base_fst_eq_base_snd D.f W.ι z
  exact ⟨by rw [heq]; exact hz, fibre_subset_closure_of_pullback D.f W.ι z hgen, heq⟩

/-- **The situation restricted to a quasi-compact open of the base.** Every hypothesis is stable
under this base change; finite presentation of the module over the distinguished open passes by
`AlgebraicGeometry.isFinitePresentation_restrict_of_le` and freeness at the generic points of the
fibres by `AlgebraicGeometry.fibre_subset_closure_of_pullback`. -/
def restrict (W : D.S.Opens) (hW : IsCompact (W : Set D.S)) : FlatteningSituation.{u} where
  S := W.toScheme
  compactSpace := isCompact_iff_compactSpace.mp hW
  quasiSeparatedSpace := W.ι.isOpenEmbedding.quasiSeparatedSpace
  X := Limits.pullback D.f W.ι
  f := pullback.snd D.f W.ι
  isAffineHom := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback D.f W.ι) D.isAffineHom
  geometricallyIntegral := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback D.f W.ι) D.geometricallyIntegral
  finitePresentation :=
    ⟨locallyOfFinitePresentation_isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback D.f W.ι)
        D.finitePresentation.locallyOfFinitePresentation,
      quasiCompact_isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback D.f W.ι) D.finitePresentation.quasiCompact,
      quasiSeparated_isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback D.f W.ι) D.finitePresentation.quasiSeparated⟩
  F := (Scheme.Modules.pullback (pullback.fst D.f W.ι)).obj D.F
  finiteType := SheafOfModules.pullback_isFiniteType
    (pullback.fst D.f W.ι).toLRSHom.toShHom D.F
  U := W.ι ⁻¹ᵁ D.U
  compact_U := by
    let : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
    rw [W.ι.isEmbedding.isCompact_iff]
    change IsCompact (W.ι.base '' (W.ι.base ⁻¹' (D.U : Set D.S)))
    rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
    simpa [Set.inter_comm] using IsCompact.inter_of_isOpen hW D.compact_U W.2 D.U.2
  finitePresentation_restrict := by
    refine isFinitePresentation_restrict_of_le (pullback.fst D.f W.ι) D.F (D.f ⁻¹ᵁ D.U)
      D.finitePresentation_restrict _ fun z hz ↦ ?_
    change D.f.base ((pullback.fst D.f W.ι).base z) ∈ D.U
    have heq : D.f.base ((pullback.fst D.f W.ι).base z) =
        W.ι.base ((pullback.snd D.f W.ι).base z) := by
      change (pullback.fst D.f W.ι ≫ D.f).base z = (pullback.snd D.f W.ι ≫ W.ι).base z
      rw [pullback.condition]
    rw [heq]
    exact hz
  free_at_generic := fun z hz hgen ↦ by
    obtain ⟨h1, h2, -⟩ := D.mem_and_fibre_subset_closure_pullback W z hz hgen
    obtain ⟨r, hr⟩ := D.free_at_generic _ h1 h2
    exact ⟨r, freeAtPointOfRank_pullback (pullback.fst D.f W.ι) D.F z r hr⟩

/-- Solvability of the restricted situation is solvability of the restricted problem: the two
carry the same base, morphism, module, distinguished open and property. -/
theorem isSolvable_restrict (W : D.S.Opens) (hW : IsCompact (W : Set D.S))
    (h : (D.restrict W hW).IsSolvable) : (D.problem.restrict W hW).IsSolvable := h

/-- **A constant rank at the generic points of the fibres over the distinguished open survives
restriction**, with the same value. -/
theorem freeAtPointOfRank_restrict (W : D.S.Opens) (hW : IsCompact (W : Set D.S)) (r : ℕ)
    (hr : ∀ x : D.X, D.f.base x ∈ D.U → D.f.base ⁻¹' {D.f.base x} ⊆ closure {x} →
      FreeAtPointOfRank D.F x r) :
    ∀ z : (D.restrict W hW).X, (D.restrict W hW).f.base z ∈ (D.restrict W hW).U →
      (D.restrict W hW).f.base ⁻¹' {(D.restrict W hW).f.base z} ⊆ closure {z} →
        FreeAtPointOfRank (D.restrict W hW).F z r := by
  intro z hz hgen
  obtain ⟨h1, h2, -⟩ := D.mem_and_fibre_subset_closure_pullback W z hz hgen
  exact freeAtPointOfRank_pullback (pullback.fst D.f W.ι) D.F z r (hr _ h1 h2)

/-! ### The strict transform along an admissible blowup -/

variable (C : D.S.IdealSheafData)

/-- **The strict transform of the total space is the whole base change.** The structure morphism
is flat, so the ideal cutting out the strict transform is zero and its closed immersion is
invertible. This is [Stacks, Tag 080F] part (1). -/
theorem isIso_strictTransform_subschemeι :
    IsIso (Stacks.StrictTransform.ideal D.f (blowUpToBase C)
      (exceptionalIdeal C)).subschemeι := by
  rw [strictTransformIdeal_eq_bot_of_flat_at_exceptional D.f C fun x _ ↦ Flat.stalkMap D.f x]
  infer_instance

/-- The projection of the base change along the blowup is of finite presentation. -/
theorem finitePresentation_pullback_snd :
    AlgebraicGeometry.FinitePresentation (pullback.snd D.f (blowUpToBase C)) :=
  ⟨locallyOfFinitePresentation_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback D.f (blowUpToBase C))
      D.finitePresentation.locallyOfFinitePresentation,
    quasiCompact_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback D.f (blowUpToBase C)) D.finitePresentation.quasiCompact,
    quasiSeparated_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback D.f (blowUpToBase C)) D.finitePresentation.quasiSeparated⟩

/-- Above the inverse image of the distinguished open the exceptional divisor is empty: its
support is the inverse image of the support of the centre, which avoids the distinguished open. -/
theorem mem_exceptionalComplement_of_mem_preimage
    (hCU : Disjoint (D.U : Set D.S) (C.support : Set D.S)) (y : blowUp C)
    (hy : y ∈ (blowUpToBase C ⁻¹ᵁ D.U : (blowUp C).Opens)) :
    y ∈ ((exceptionalIdeal C).support.compl : (blowUp C).Opens) := by
  change y ∉ ((exceptionalIdeal C).support : Set (blowUp C))
  intro hmem
  have h1 : (blowUpToBase C).base y ∈ (C.support : Set D.S) := by
    change y ∈ ((C.comap (blowUpToBase C)).support : Set (blowUp C)) at hmem
    rw [Scheme.IdealSheafData.support_comap] at hmem
    exact hmem
  exact Set.disjoint_left.mp hCU hy h1

/-- **A generic point of a fibre over the inverse image of the distinguished open, on the strict
transform, lies over such a point of the original situation**, and freeness of any fixed rank
there is carried to it. The strict transform of the total space being the whole base change, the
point is transported by the inverse of that isomorphism, and the freeness by
`AlgebraicGeometry.freeAtPointOfRank_strictTransformSheaf`. -/
theorem exists_point_of_strictTransform (C : D.S.IdealSheafData)
    (z' : ↑(Stacks.StrictTransform.scheme D.f (blowUpToBase C) (exceptionalIdeal C)))
    (hz' : (strictTransformToBlowUp D.f C).base z' ∈
      (blowUpToBase C ⁻¹ᵁ D.U : (blowUp C).Opens))
    (hgen : (strictTransformToBlowUp D.f C).base ⁻¹'
      {(strictTransformToBlowUp D.f C).base z'} ⊆ closure {z'}) :
    ∃ x : D.X, D.f.base x ∈ D.U ∧ D.f.base ⁻¹' {D.f.base x} ⊆ closure {x} ∧
      D.f.base x = (blowUpToBase C).base ((strictTransformToBlowUp D.f C).base z') ∧
      ∀ r : ℕ, FreeAtPointOfRank D.F x r →
        FreeAtPointOfRank (strictTransformBlowUpModule D.f C D.F) z' r := by
  have := D.isIso_strictTransform_subschemeι C
  set s := (Stacks.StrictTransform.ideal D.f (blowUpToBase C)
    (exceptionalIdeal C)).subschemeι with hs
  have hsinv : ∀ w : ↑(Stacks.StrictTransform.baseChange D.f (blowUpToBase C)),
      s.base ((inv s).base w) = w := fun w ↦ by
    change (inv s ≫ s).base w = w
    rw [IsIso.inv_hom_id]
    rfl
  -- The corresponding point of the ambient base change is generic in its fibre.
  have hgen2 : (pullback.snd D.f (blowUpToBase C)).base ⁻¹'
      {(pullback.snd D.f (blowUpToBase C)).base (s.base z')} ⊆ closure {s.base z'} := by
    intro w hw
    have hmem : (strictTransformToBlowUp D.f C).base ((inv s).base w) =
        (strictTransformToBlowUp D.f C).base z' := by
      change (pullback.snd D.f (blowUpToBase C)).base (s.base ((inv s).base w)) =
        (pullback.snd D.f (blowUpToBase C)).base (s.base z')
      rw [hsinv]
      exact hw
    have hspec : z' ⤳ (inv s).base w := specializes_iff_mem_closure.mpr (hgen hmem)
    have hspec2 := hspec.map s.continuous
    rw [hsinv] at hspec2
    exact specializes_iff_mem_closure.mp hspec2
  -- Its image in `X` is generic in its fibre and lies over the distinguished open.
  have hcond := base_fst_eq_base_snd D.f (blowUpToBase C) (s.base z')
  refine ⟨(pullback.fst D.f (blowUpToBase C)).base (s.base z'), by rw [hcond]; exact hz',
    fibre_subset_closure_of_pullback D.f (blowUpToBase C) (s.base z') hgen2, hcond,
    fun r hr ↦ ?_⟩
  exact freeAtPointOfRank_pullback s
    (Stacks.StrictTransform.sheaf D.f (blowUpToBase C) (exceptionalIdeal C) D.F) z' r
    (freeAtPointOfRank_strictTransformSheaf D.f C D.F (s.base z') r hr)

/-- **The situation transformed by a `U`-admissible blowup.** The source's hypotheses (1) and (2)
are carried along the base change through the isomorphism of
`AlgebraicGeometry.FlatteningSituation.isIso_strictTransform_subschemeι`, hypothesis (3) because
above the inverse image of `U` the strict transform is the pullback, and the strengthened
hypothesis (4) by `AlgebraicGeometry.freeAtPointOfRank_strictTransformSheaf`. -/
def transform (hC : FinitePresentation C.subschemeι)
    (hCU : Disjoint (D.U : Set D.S) (C.support : Set D.S)) : FlatteningSituation.{u} where
  S := blowUp C
  compactSpace :=
    have : IsProper (blowUpToBase C) :=
      isProper_blowUpToBase_of_fg C ((finitePresentation_subschemeι_iff_isFiniteType C).mp hC)
    QuasiCompact.compactSpace_of_compactSpace (blowUpToBase C)
  quasiSeparatedSpace :=
    have : IsProper (blowUpToBase C) :=
      isProper_blowUpToBase_of_fg C ((finitePresentation_subschemeι_iff_isFiniteType C).mp hC)
    quasiSeparatedSpace_of_quasiSeparated (blowUpToBase C)
  X := Stacks.StrictTransform.scheme D.f (blowUpToBase C) (exceptionalIdeal C)
  f := strictTransformToBlowUp D.f C
  isAffineHom := by
    have := D.isIso_strictTransform_subschemeι C
    have : IsAffineHom (pullback.snd D.f (blowUpToBase C)) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback D.f (blowUpToBase C)) D.isAffineHom
    exact inferInstance
  flat := by
    have := D.isIso_strictTransform_subschemeι C
    exact inferInstance
  geometricallyIntegral := by
    have := D.isIso_strictTransform_subschemeι C
    have : GeometricallyIntegral (pullback.snd D.f (blowUpToBase C)) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback D.f (blowUpToBase C)) D.geometricallyIntegral
    have : MorphismProperty.RespectsIso (@GeometricallyIntegral) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    change GeometricallyIntegral ((Stacks.StrictTransform.ideal D.f (blowUpToBase C)
      (exceptionalIdeal C)).subschemeι ≫ pullback.snd D.f (blowUpToBase C))
    rw [MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIntegral)]
    infer_instance
  finitePresentation := by
    have := D.isIso_strictTransform_subschemeι C
    obtain ⟨h1, h2, h3⟩ := D.finitePresentation_pullback_snd C
    have := h1
    have := h2
    have := h3
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  F := strictTransformBlowUpModule D.f C D.F
  finiteType := by
    have : (Stacks.StrictTransform.sheaf D.f (blowUpToBase C)
        (exceptionalIdeal C) D.F).IsFiniteType :=
      isFiniteType_strictTransformSheaf D.f C D.F
    exact SheafOfModules.pullback_isFiniteType _ _
  U := blowUpToBase C ⁻¹ᵁ D.U
  compact_U :=
    have : IsProper (blowUpToBase C) :=
      isProper_blowUpToBase_of_fg C ((finitePresentation_subschemeι_iff_isFiniteType C).mp hC)
    QuasiCompact.isCompact_preimage (f := blowUpToBase C) _ D.U.2 D.compact_U
  finitePresentation_restrict := by
    have := D.isIso_strictTransform_subschemeι C
    set Ω₀ : (Stacks.StrictTransform.baseChange D.f (blowUpToBase C)).Opens :=
      pullback.snd D.f (blowUpToBase C) ⁻¹ᵁ (blowUpToBase C ⁻¹ᵁ D.U) with hΩ₀
    have hcond : ∀ z : ↥(Stacks.StrictTransform.baseChange D.f (blowUpToBase C)),
        D.f.base ((pullback.fst D.f (blowUpToBase C)).base z) =
          (blowUpToBase C).base ((pullback.snd D.f (blowUpToBase C)).base z) := fun z ↦ by
      change (pullback.fst D.f (blowUpToBase C) ≫ D.f).base z =
        (pullback.snd D.f (blowUpToBase C) ≫ blowUpToBase C).base z
      rw [pullback.condition]
    have hle : Ω₀ ≤ Stacks.StrictTransform.exceptionalComplement D.f (blowUpToBase C)
        (exceptionalIdeal C) := fun z hz ↦
      D.mem_exceptionalComplement_of_mem_preimage C hCU _ hz
    have hisoV := Stacks.StrictTransform.isIso_restrictFunctor_map_π D.f (blowUpToBase C)
      (exceptionalIdeal C) D.F
    have hisoU : IsIso ((Scheme.Modules.restrictFunctor Ω₀.ι).map
        (Stacks.StrictTransform.π D.f (blowUpToBase C) (exceptionalIdeal C) D.F)) :=
      @Scheme.Modules.isIso_restrictFunctor_map_of_le _ Ω₀ _ hle _ _
        (Stacks.StrictTransform.π D.f (blowUpToBase C) (exceptionalIdeal C) D.F) hisoV
    have := hisoU
    have hpre : (((Scheme.Modules.pullback
        (pullback.fst D.f (blowUpToBase C))).obj D.F).restrict Ω₀.ι).IsFinitePresentation := by
      refine isFinitePresentation_restrict_of_le (pullback.fst D.f (blowUpToBase C)) D.F
        (D.f ⁻¹ᵁ D.U) D.finitePresentation_restrict Ω₀ fun z hz ↦ ?_
      change D.f.base ((pullback.fst D.f (blowUpToBase C)).base z) ∈ D.U
      rw [hcond]
      exact hz
    have hsheaf : ((Stacks.StrictTransform.sheaf D.f (blowUpToBase C) (exceptionalIdeal C)
        D.F).restrict Ω₀.ι).IsFinitePresentation :=
      (SheafOfModules.isFinitePresentation.{u, u, u} _).prop_of_iso
        (@asIso _ _ _ _ _ hisoU) hpre
    exact isFinitePresentation_restrict_of_le _ _ Ω₀ hsheaf _ fun w hw ↦ hw
  free_at_generic := fun z' hz' hgen ↦ by
    obtain ⟨x, h1, h2, -, h3⟩ := D.exists_point_of_strictTransform C z' hz' hgen
    obtain ⟨r, hr⟩ := D.free_at_generic x h1 h2
    exact ⟨r, h3 r hr⟩

/-- Solvability of the transformed situation is solvability of the transformed problem. -/
theorem isSolvable_transform (hC : FinitePresentation C.subschemeι)
    (hCU : Disjoint (D.U : Set D.S) (C.support : Set D.S))
    (h : (D.transform C hC hCU).IsSolvable) : (D.problem.transform C hC).IsSolvable := h

/-- **A constant rank at the generic points of the fibres over the distinguished open survives
the strict transform**, with the same value. -/
theorem freeAtPointOfRank_transform (hC : FinitePresentation C.subschemeι)
    (hCU : Disjoint (D.U : Set D.S) (C.support : Set D.S)) (r : ℕ)
    (hr : ∀ x : D.X, D.f.base x ∈ D.U → D.f.base ⁻¹' {D.f.base x} ⊆ closure {x} →
      FreeAtPointOfRank D.F x r) :
    ∀ z : (D.transform C hC hCU).X,
      (D.transform C hC hCU).f.base z ∈ (D.transform C hC hCU).U →
        (D.transform C hC hCU).f.base ⁻¹' {(D.transform C hC hCU).f.base z} ⊆ closure {z} →
          FreeAtPointOfRank (D.transform C hC hCU).F z r := by
  intro z hz hgen
  obtain ⟨x, h1, h2, -, h3⟩ := D.exists_point_of_strictTransform C z hz hgen
  exact h3 r (hr x h1 h2)

end FlatteningSituation

end AlgebraicGeometry

end
