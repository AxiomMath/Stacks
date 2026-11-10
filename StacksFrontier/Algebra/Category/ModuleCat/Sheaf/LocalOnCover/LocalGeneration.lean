module

public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
import StacksCore.Tactic.StacksAttribute

/-!
# Local generation by sections is local on a covering family

Stacks 03DN asserts that each of the local conditions of Stacks 03DL may be tested on the
members of any family covering the final object.  This file proves the two clauses about
generation by global sections: local generation by sections, Stacks 03DL(3), and local
generation by a fixed number `r` of sections, Stacks 03DL(4).  For each, the condition on a
ringed site is shown equivalent to the condition on the localized ringed sites of a covering
family, and to the existence of the global generating families themselves on a covering family.

The two clauses have one proof.  Generating sections of `M.over U` restrict along any arrow
`f : V ⟶ U` to generating sections of `M.over V` with the *same index type*
(`generatingSectionsOverMap`), because restriction between slice sites preserves colimits and
matches up the two structure sheaves; that one construction gives both descent steps at once,
and keeping the index type is exactly what makes the clause about `r` sections follow from the
clause about sections.  In the other direction the generating sections handed to us live on
iterated slice sites, and are moved to the slice over the base object by the comparison
`sliceEquiv` of those two sites.

## Main results

* `Stacks.SheafOfModules.isLocallyGeneratedBySectionsOnSite_iff_exists_cover_locallyGenerated`
  and
  `Stacks.SheafOfModules.isLocallyGeneratedBySectionsOnSite_iff_exists_cover_generatingSections`:
  conditions (a) ↔ (b) and (a) ↔ (c) of Stacks 03DN for local generation by sections.
* `Stacks.SheafOfModules.isLocallyGeneratedByOnSite_iff_exists_cover_isLocallyGeneratedBy` and
  `Stacks.SheafOfModules.isLocallyGeneratedByOnSite_iff_exists_cover_generators`: the same two
  equivalences for local generation by `r` sections.
* `Stacks.SheafOfModules.generatingSectionsOverMap`: restriction of a family of generating
  sections along an arrow of the site, with unchanged index type.
* `Stacks.SheafOfModules.isLocallyGeneratedBySectionsOnSite_of_coversTop` and
  `Stacks.SheafOfModules.isLocallyGeneratedByOnSite_of_coversTop`: global generation on the
  members of a family covering the final object gives the corresponding local condition
  everywhere.

## Implementation notes

The predicates are `SheafOfModules.IsLocallyGeneratedBySectionsOnSite` and
`SheafOfModules.IsLocallyGeneratedByOnSite`, which are Stacks 03DL(3) and 03DL(4), and the
localized ringed site is `AlgebraicGeometry.RingedSite.over`, which is Stacks 04IX; no notion is
introduced here.  Both predicates carry the sheafification hypotheses of Mathlib's
`SheafOfModules.GeneratingSections`, which the statements below therefore also carry; they are
hypotheses of that existing construction, not finiteness conditions.

Restriction of generating sections is Mathlib's `SheafOfModules.GeneratingSections.map`, whose
colimit-preservation hypothesis on restriction between slice sites is
`Stacks.SheafOfModules.overMap_preservesColimits`.  That hypothesis is the whole reason this
file is not formal: Mathlib knows `SheafOfModules.overMap` to be a left adjoint only when the
site has pullbacks.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Stacks.SheafOfModules

universe u v w

section Restriction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Generating global sections of the restriction of `M` to `U` restrict, along an arrow
`f : V ⟶ U`, to generating global sections of the restriction of `M` to `V`.  The index type is
unchanged. -/
noncomputable def generatingSectionsOverMap (M : SheafOfModules.{w} R) {V U : C} (f : V ⟶ U)
    (σ : (M.over U).GeneratingSections) : (M.over V).GeneratingSections := by
  have : HasSheafify (J.over V) AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  have : PreservesColimitsOfSize.{w, w} (SheafOfModules.overMap.{w} R f) :=
    overMap_preservesColimits R f
  exact SheafOfModules.GeneratingSections.equivOfIso
    ((SheafOfModules.overFunctorMap R f).app M)
    (σ.map (SheafOfModules.overMap R f) (SheafOfModules.overMapUnitIso f).symm)

@[simp]
theorem generatingSectionsOverMap_I (M : SheafOfModules.{w} R) {V U : C} (f : V ⟶ U)
    (σ : (M.over U).GeneratingSections) : (generatingSectionsOverMap M f σ).I = σ.I := rfl

/-- **Local generation by sections descends from a covering family.** If a family of objects
covers the terminal object and the restriction of `M` to each member is generated by global
sections, then `M` is locally generated by sections. -/
theorem isLocallyGeneratedBySectionsOnSite_of_coversTop (M : SheafOfModules.{w} R)
    {I : Type*} (U : I → C) (hU : J.CoversTop U)
    (hM : ∀ i, Nonempty ((M.over (U i)).GeneratingSections)) :
    SheafOfModules.IsLocallyGeneratedBySectionsOnSite M := by
  intro W
  obtain ⟨K, V, g, hg⟩ := (Sieve.ofObjects U W).exists_eq_ofArrows
  refine ⟨K, fun k => Over.mk (g k),
    coversTop_over_of_ofArrows_mem J W V g (by rw [← hg]; exact hU W), ?_⟩
  intro k
  have hmem : (Sieve.ofObjects U W) (g k) := by
    rw [hg, Sieve.mem_ofArrows_iff]
    exact ⟨k, 𝟙 _, by simp⟩
  obtain ⟨i, ⟨f⟩⟩ := (Sieve.mem_ofObjects_iff U (g k)).mp hmem
  obtain ⟨σ⟩ := hM i
  exact ⟨generatingSectionsOverMap M f σ⟩

/-- **Local generation by `r` sections descends from a covering family.** -/
theorem isLocallyGeneratedByOnSite_of_coversTop (M : SheafOfModules.{w} R) (r : ℕ)
    {I : Type*} (U : I → C) (hU : J.CoversTop U)
    (hM : ∀ i, ∃ σ : (M.over (U i)).GeneratingSections, Nonempty (σ.I ≃ Fin r)) :
    SheafOfModules.IsLocallyGeneratedByOnSite M r := by
  intro W
  refine ⟨⟨Sieve.ofObjects U W, hU W⟩, ?_⟩
  intro V f hf
  obtain ⟨i, ⟨g⟩⟩ := (Sieve.mem_ofObjects_iff U f).mp hf
  obtain ⟨σ, hr⟩ := hM i
  exact ⟨generatingSectionsOverMap M g σ, hr⟩

variable [∀ (U : C) (V : Over U), HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
  [∀ (U : C) (V : Over U), ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Generating sections of `M` read on an iterated slice site, transported to the slice site
over the base object.  The index type is unchanged. -/
noncomputable def generatingSectionsOfIteratedSlice (M : SheafOfModules.{w} R) (U : C)
    (V : Over U) (G : ((M.over U).over V).GeneratingSections) :
    (M.over V.left).GeneratingSections := by
  have : HasSheafify (J.over V.left) AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let e := sliceEquiv R U V
  have : e.inverse.IsLeftAdjoint := inferInstance
  have : PreservesColimitsOfSize.{w, w} e.inverse :=
    (Adjunction.ofIsLeftAdjoint e.inverse).leftAdjoint_preservesColimits
  refine SheafOfModules.GeneratingSections.equivOfIso
    (e.inverse.mapIso (sliceEquivObjIso M U V).symm ≪≫ (e.unitIso.app (M.over V.left)).symm)
    (G.map e.inverse ?_)
  exact e.unitIso.app _ ≪≫ e.inverse.mapIso (sliceEquivUnitIso R U V)

@[simp]
theorem generatingSectionsOfIteratedSlice_I (M : SheafOfModules.{w} R) (U : C) (V : Over U)
    (G : ((M.over U).over V).GeneratingSections) :
    (generatingSectionsOfIteratedSlice M U V G).I = G.I := rfl

/-- Generating sections of the restriction of `M` to the base object of `V`, transported to the
iterated slice site over `V`.  The index type is unchanged. -/
noncomputable def generatingSectionsOfIteratedSliceSymm (M : SheafOfModules.{w} R) (U : C)
    (V : Over U) (G : (M.over V.left).GeneratingSections) :
    ((M.over U).over V).GeneratingSections := by
  have : HasSheafify ((J.over U).over V) AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let e := sliceEquiv R U V
  have : e.functor.IsLeftAdjoint := inferInstance
  have : PreservesColimitsOfSize.{w, w} e.functor :=
    (Adjunction.ofIsLeftAdjoint e.functor).leftAdjoint_preservesColimits
  exact SheafOfModules.GeneratingSections.equivOfIso (sliceEquivObjIso M U V)
    (G.map e.functor (sliceEquivUnitIso R U V).symm)

@[simp]
theorem generatingSectionsOfIteratedSliceSymm_I (M : SheafOfModules.{w} R) (U : C) (V : Over U)
    (G : (M.over V.left).GeneratingSections) :
    (generatingSectionsOfIteratedSliceSymm M U V G).I = G.I := rfl

end Restriction

/-- A family covering the terminal object of the slice site over `V.left`, read in the iterated
slice site over `V`, covers the terminal object there. -/
private theorem coversTop_iteratedSlice {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {U : C} (V : Over U) {I : Type*} (Z : I → Over V.left)
    (hZ : (J.over V.left).CoversTop Z) :
    ((J.over U).over V).CoversTop (fun i => V.iteratedSliceBackward.obj (Z i)) := by
  intro T
  let W : I → Over V := fun i => V.iteratedSliceBackward.obj (Z i)
  let T' : Over V.left := Over.mk T.hom.left
  have hT := hZ T'
  rw [GrothendieckTopology.mem_over_iff] at hT
  rw [GrothendieckTopology.mem_over_iff]
  rw [GrothendieckTopology.mem_over_iff]
  have hs : Sieve.overEquiv T.left (Sieve.overEquiv T (Sieve.ofObjects W T)) =
      Sieve.overEquiv T' (Sieve.ofObjects Z T') := by
    ext A f
    dsimp [T', Over.iteratedSliceForward]
    rw [Sieve.overEquiv_iff, Sieve.overEquiv_iff, Sieve.overEquiv_iff]
    simp only [Sieve.ofObjects]
    let A₀ : Over U := Over.mk (f ≫ T.left.hom)
    let a : A₀ ⟶ T.left := Over.homMk f (by simp [A₀])
    let N : Over V := Over.mk (a ≫ T.hom)
    let A' : Over V.left := V.iteratedSliceForward.obj N
    constructor
    · rintro ⟨i, ⟨g⟩⟩
      change N ⟶ W i at g
      refine ⟨i, ⟨?_⟩⟩
      simpa [A', T', W, N, a, A₀, Over.iteratedSliceForward,
        Over.iteratedSliceBackward, Category.assoc] using
        (V.iteratedSliceForward.map g ≫ (V.iteratedSliceEquiv.counitIso.app (Z i)).hom)
    · rintro ⟨i, ⟨g⟩⟩
      change A' ⟶ Z i at g
      refine ⟨i, ⟨?_⟩⟩
      simpa [A', W, N, a, A₀, Over.iteratedSliceForward,
        Over.iteratedSliceBackward, Category.assoc] using
        (V.iteratedSliceEquiv.unitIso.hom.app N ≫
          V.iteratedSliceBackward.map
            (g ≫ (V.iteratedSliceEquiv.counitIso.app (Z i)).inv) ≫
          V.iteratedSliceEquiv.unitIso.inv.app (W i))
  rw [hs]
  exact hT

/-- The family of all objects of the site covers the terminal object. -/
private theorem coversTop_id {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    J.CoversTop (fun U : C => U) := fun U =>
  J.covering_of_eq_top (by
    ext Y f
    exact ⟨fun _ => trivial, fun _ => ⟨Y, ⟨𝟙 Y⟩⟩⟩)

/-- Local generation by sections packaged as local generators data: the covering families of all
the objects of the site assemble into one family covering the terminal object. -/
private noncomputable def localGeneratorsDataOfLocallyGenerated
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (M : SheafOfModules.{w} R) (h : SheafOfModules.IsLocallyGeneratedBySectionsOnSite M) :
    M.LocalGeneratorsData.{u} := by
  classical
  choose I V hV hgen using h
  let D : M.LocalGeneratorsData.{max u v} :=
    { I := Σ U : C, I U
      X := fun j => (V j.1 j.2).left
      coversTop := (coversTop_id J).over (fun U => hV U)
      generators j := Classical.choice (hgen j.1 j.2) }
  exact D.shrink

section RingedSite

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 03DN, local generation by sections.** A sheaf of modules on a ringed site is locally
generated by sections if and only if its restriction to each member of some covering family of
the final object is locally generated by sections on the corresponding localized ringed site. -/
@[stacks 03DN "locally_generated"]
theorem isLocallyGeneratedBySectionsOnSite_iff_exists_cover_locallyGenerated
    [∀ (U : X.C) (V : Over U), HasWeakSheafify ((X.J.over U).over V) AddCommGrpCat.{w}]
    [∀ (U : X.C) (V : Over U), ((X.J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}] :
    SheafOfModules.IsLocallyGeneratedBySectionsOnSite F ↔
      ∃ (I : Type u) (U : I → X.C), X.J.CoversTop U ∧
        ∀ i : I, SheafOfModules.IsLocallyGeneratedBySectionsOnSite
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (U i)) (F.over (U i)) := by
  constructor
  · intro h
    refine ⟨X.C, fun U => U, coversTop_id X.J, ?_⟩
    · intro U V
      obtain ⟨I, Z, hZ, hgen⟩ := h V.left
      refine ⟨I, fun i => V.iteratedSliceBackward.obj (Z i),
        coversTop_iteratedSlice X.J V Z hZ, fun i => ⟨?_⟩⟩
      exact generatingSectionsOfIteratedSliceSymm F U
        ((V.iteratedSliceBackward.obj (Z i)).left) (Classical.choice (hgen i))
  · rintro ⟨I, U, hU, hF⟩
    let D : ∀ i, (F.over (U i)).LocalGeneratorsData.{max u v} := fun i =>
      localGeneratorsDataOfLocallyGenerated (F.over (U i)) (hF i)
    let Dall : F.LocalGeneratorsData.{max u v} :=
      { I := Σ i, (D i).I
        X := fun ij => ((D ij.1).X ij.2).left
        coversTop := hU.over (fun i => (D i).coversTop)
        generators ij :=
          generatingSectionsOfIteratedSlice F (U ij.1) ((D ij.1).X ij.2)
            ((D ij.1).generators ij.2) }
    exact isLocallyGeneratedBySectionsOnSite_of_coversTop F Dall.X Dall.coversTop
      (fun i => ⟨Dall.generators i⟩)

/-- **Stacks 03DN, local generation by sections.** A sheaf of modules on a ringed site is locally
generated by sections if and only if its restriction to each member of some covering family of
the final object is generated by global sections. -/
@[stacks 03DN "locally_generated"]
theorem isLocallyGeneratedBySectionsOnSite_iff_exists_cover_generatingSections :
    SheafOfModules.IsLocallyGeneratedBySectionsOnSite F ↔
      ∃ (I : Type u) (U : I → X.C), X.J.CoversTop U ∧
        ∀ i : I, Nonempty ((F.over (U i)).GeneratingSections) := by
  constructor
  · intro h
    let D := localGeneratorsDataOfLocallyGenerated F h
    exact ⟨D.I, D.X, D.coversTop, fun i => ⟨D.generators i⟩⟩
  · rintro ⟨I, U, hU, hF⟩
    exact isLocallyGeneratedBySectionsOnSite_of_coversTop F U hU hF

variable (r : ℕ)

/-- **Stacks 03DN, local generation by `r` sections.** A sheaf of modules on a ringed site is
locally generated by `r` sections if and only if its restriction to each member of some covering
family of the final object is, on the corresponding localized ringed site. -/
@[stacks 03DN "locally_generated_r"]
theorem isLocallyGeneratedByOnSite_iff_exists_cover_isLocallyGeneratedBy
    [∀ (U : X.C) (V : Over U), HasWeakSheafify ((X.J.over U).over V) AddCommGrpCat.{w}]
    [∀ (U : X.C) (V : Over U), ((X.J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}] :
    SheafOfModules.IsLocallyGeneratedByOnSite F r ↔
      ∃ (I : Type u) (U : I → X.C), X.J.CoversTop U ∧
        ∀ i : I, SheafOfModules.IsLocallyGeneratedByOnSite
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (U i)) (F.over (U i)) r := by
  constructor
  · intro hF
    classical
    refine ⟨X.C, fun U => U, coversTop_id X.J, ?_⟩
    intro U A
    obtain ⟨S, hS⟩ := hF A.left
    refine ⟨⟨(Sieve.overEquiv A).symm S, ?_⟩, ?_⟩
    · rw [GrothendieckTopology.mem_over_iff]
      simpa only [OrderIso.apply_symm_apply] using S.2
    · intro B f hf
      obtain ⟨σ, hσ⟩ := hS B.left f.left ((Sieve.overEquiv_symm_iff S f).mp hf)
      exact ⟨generatingSectionsOfIteratedSliceSymm F U B σ, hσ⟩
  · rintro ⟨I, U, hU, hF⟩
    classical
    let top (i : I) : Over (U i) := Over.mk (𝟙 (U i))
    have htop (i : I) : IsTerminal (top i) := by
      simpa [top] using (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (U i))))
    let S (i : I) : (X.J.over (U i)).Cover (top i) := Classical.choose (hF i (top i))
    have hSG (i : I) (V : Over (U i)) (f : V ⟶ top i) (hf : S i f) :
        ∃ σ : ((F.over (U i)).over V).GeneratingSections, Nonempty (σ.I ≃ Fin r) :=
      Classical.choose_spec (hF i (top i)) V f hf
    let I' : ∀ i : I, Type (max u v) := fun i =>
      {V : Over (U i) // S i (Over.homMk V.hom (by simp [top]))}
    let V : (i : I) → I' i → Over (U i) := fun i j => j.1
    have hV : ∀ i : I, (X.J.over (U i)).CoversTop (V i) := by
      intro i
      rw [GrothendieckTopology.coversTop_iff_of_isTerminal
        (X.J.over (U i)) (top i) (htop i)]
      apply (X.J.over (U i)).superset_covering ?_ (S i).2
      intro Z f hf
      rw [Sieve.mem_ofObjects_iff]
      refine ⟨⟨Z, ?_⟩, ⟨𝟙 Z⟩⟩
      have hEq : f = Over.homMk Z.hom (by simp [top]) := (htop i).hom_ext _ _
      simpa [hEq, I', V] using hf
    refine isLocallyGeneratedByOnSite_of_coversTop F r
      (fun j : Σ i, I' i => (V j.1 j.2).left) (hU.over hV) ?_
    intro j
    obtain ⟨σ, hσ⟩ := hSG j.1 (V j.1 j.2)
      (Over.homMk (V j.1 j.2).hom (by simp [top])) j.2.2
    exact ⟨generatingSectionsOfIteratedSlice F (U j.1) (V j.1 j.2) σ, hσ⟩

/-- **Stacks 03DN, local generation by `r` sections.** A sheaf of modules on a ringed site is
locally generated by `r` sections if and only if its restriction to each member of some covering
family of the final object is generated by `r` global sections. -/
@[stacks 03DN "locally_generated_r"]
theorem isLocallyGeneratedByOnSite_iff_exists_cover_generators :
    SheafOfModules.IsLocallyGeneratedByOnSite F r ↔
      ∃ (I : Type u) (U : I → X.C), X.J.CoversTop U ∧
        ∀ i : I, ∃ σ : (F.over (U i)).GeneratingSections, Nonempty (σ.I ≃ Fin r) := by
  constructor
  · intro hF
    classical
    let S : ∀ U : X.C, X.J.Cover U := fun U => Classical.choose (hF U)
    have hS : ∀ (U : X.C) (V : X.C) (f : V ⟶ U), S U f →
        ∃ σ : (F.over V).GeneratingSections, Nonempty (σ.I ≃ Fin r) :=
      fun U => Classical.choose_spec (hF U)
    refine ⟨{V : X.C // ∃ (U : X.C) (f : V ⟶ U), S U f}, fun i => i.1, ?_, ?_⟩
    · intro W
      apply X.J.superset_covering ?_ (S W).2
      intro V f hf
      exact ⟨⟨V, ⟨W, ⟨f, hf⟩⟩⟩, ⟨𝟙 V⟩⟩
    · intro i
      obtain ⟨U₀, f, hf⟩ := i.2
      exact hS U₀ i.1 f hf
  · rintro ⟨I, U, hU, hgen⟩
    exact isLocallyGeneratedByOnSite_of_coversTop F r U hU hgen

end RingedSite

end Stacks.SheafOfModules

end
