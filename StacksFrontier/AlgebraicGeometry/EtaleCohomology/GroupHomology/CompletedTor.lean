module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.HomologyLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.TorChangeOfRings

/-!
# Homology with finite coefficients is completed `Tor`

Let `G` be a profinite group, `Λ` a finite ring and `M` a finite `Λ`-module with a continuous
action of `G`. Item (1) of the notes on homology of [Stacks, Section 03VI] identifies
`H_i(G, M)` with `Tor_i^{Λ[[G]]}(M, Λ)`, `Λ[[G]]` the limit of the group algebras of the finite
quotients of `G`. With the abstract `Tor` over the ring `Λ[[G]]` this fails
(`Stacks.GroupHomology.exists_forall_eval_mem_and_not_mem_augmentationIdealSq`, for
`G = (ℤ/p)^ℕ` in degree one); the correct statement uses the completed `Tor`:

`H_i(G, M) ≅ lim_U Tor_i^{Λ[G/U]}(M, Λ)`,

the limit over the open normal subgroups `U` of `G` acting trivially on `M`
(`Stacks.GroupHomology.homologyIsoLimitTor`). This file proves it, for the homology
`H_i(G, M) = Hⁱ(G, M^∨)^∨` of `Stacks.ContinuousCohomology.restrictedHomologyDelta`, in every
degree `i`, by combining two results:

* `H_i(G, M) = lim_U H_i(G/U, M)` along the coinflation maps
  (`Stacks.ContinuousCohomology.homologyIsoLimit`), the dual of the continuity of cohomology
  `Hⁱ(G, M^∨) = colim_U Hⁱ(G/U, M^∨)`;
* for the finite group `Q = G/U`, `H_i(Q, -) ≅ Tor_i^{Λ[Q]}(-, Λ)` as homological δ-functors
  (`Stacks.GroupHomology.homologyTorIso`), both being universal with the coinvariants in degree
  zero.

Here `Tor_i^{Λ[Q]}(M, Λ)` is `Stacks.GroupHomology.torDelta`: the left derived functors of the
coinvariants `N ↦ Λ ⊗_{Λ[[Q]]} N` of `Λ[[Q]]`-modules
(`Stacks.GroupHomology.finiteTypeGroupHomology`),
which for the finite discrete group `Q` is the group algebra `Λ[Q]`
(`Stacks.GroupHomology.eq_sum_const_mul_of`). This is the source's own `Tor_i^{Λ[[-]]}(M, Λ)`,
applied to the finite quotients instead of to `G`.

The transition map `Tor_i^{Λ[G/V]}(M, Λ) → Tor_i^{Λ[G/U]}(M, Λ)` for `V ≤ U` is the
change-of-rings map along `Λ[G/V] → Λ[G/U]` (`Stacks.GroupHomology.torChangeOfRings`, the morphism
of homological δ-functors `Tor_•^{Λ[G/V]}(res -, Λ) ⟶ Tor_•^{Λ[G/U]}(-, Λ)` which is the
projection of coinvariants in degree zero; `Stacks.GroupHomology.torDiagram_map`). Through
`H_i(G/V, -) ≅ Tor_i^{Λ[G/V]}(-, Λ)` and `H_i(G/U, -) ≅ Tor_i^{Λ[G/U]}(-, Λ)` it is the coinflation
map `H_i(G/V, M) → H_i(G/U, M)`, the dual of inflation along `G/V → G/U`
(`Stacks.GroupHomology.torDiagram_map_eq`): coinflation is a morphism of δ-functors with the same
degree-zero part (`Stacks.GroupHomology.coinflation_comp_homologyTorIso`), and `Tor_•^{Λ[G/U]}` is
universal.

The identification is natural in `M`: for `f : M ⟶ M'` it carries `H_i(G, f)` to the map of limits
induced by `Tor_i^{Λ[G/U]}(f, Λ)` over the open normal subgroups acting trivially on both, a cofinal
index set for both diagrams (`Stacks.GroupHomology.homologyIsoLimitTor_naturality`).

## Main definitions

* `Stacks.GroupHomology.torDiagram`: `U ↦ Tor_i^{Λ[G/U]}(M, Λ)`, along the change-of-rings maps.
* `Stacks.GroupHomology.limitTorMap`: the map of limits induced by `f : M ⟶ M'`.

## Main results

* `Stacks.GroupHomology.homologyIsoLimitTor`: `H_i(G, M) ≅ lim_U Tor_i^{Λ[G/U]}(M, Λ)`.
* `Stacks.GroupHomology.torDiagram_map_eq`: the change-of-rings maps are the coinflation maps.
* `Stacks.GroupHomology.homologyIsoLimitTor_naturality`: naturality in `M`.

## References

* [Stacks Project, Section 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.ContinuousCohomology
  Stacks.CategoryHomology

universe w

namespace Stacks.GroupHomology

variable (Λ : Type) [Ring Λ] [Finite Λ] {G : Type w} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  (M : FiniteTypeContinuousModule.{0, w, w} Λ G)

/-- `H_i(G/U, M) ≅ Tor_i^{Λ[G/U]}(M, Λ)` at the finite quotient `G/U`. -/
def homologyTorIsoAt (i : ℕ) (U : TrivialSubgroup Λ M) :
    (homologyDiagram M i).obj U ≅
      ((torDelta Λ (G ⧸ (U.1 : Subgroup G))).functor i).obj (descendU U) :=
  (Stacks.CategoryHomology.HomologicalDeltaFunctor.isoApp
    (homologyTorIso Λ (G ⧸ (U.1 : Subgroup G))) i).app (descendU U)

/-- `M` over `G ⧸ V` is the restriction of `M` over `G ⧸ U`, for `V ≤ U`: the identity of `M`. -/
def descendTransition {U V : TrivialSubgroup Λ M} (h : V ≤ U) :
    descendU V ⟶
      (finiteTypeContinuousModuleRes.{0, w, w} Λ (quotientMap (show V.1 ≤ U.1 from h))).obj
        (descendU U) :=
  resPreimage Λ (quotientMk V.1) (quotientMk_surjective V.1) (𝟙 M)

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- The dual of `descendTransition` is `dualTransition`. -/
theorem resDualHom_comp_dual_map_descendTransition {U V : TrivialSubgroup Λ M} (h : V ≤ U) :
    resDualHom (quotientMap (show V.1 ≤ U.1 from h)) (descendU U) ≫
        (finiteTypeContinuousModuleDual.{0, w, w} Λ (G ⧸ (V.1 : Subgroup G))).map
          (descendTransition Λ M h).op =
      dualTransition h :=
  finiteTypeContinuousModule_hom_ext fun _ ↦ rfl

omit [TotallyDisconnectedSpace G] in
/-- **The transition maps of the homology diagram are coinflation**: the map
`H_i(G/V, M) ⟶ H_i(G/U, M)` is the coinflation δ-morphism `H_i(G/V, res M) ⟶ H_i(G/U, M)` at `M`,
after `M = res M` (`Stacks.GroupHomology.descendTransition`). -/
theorem homologyDiagram_map_eq (i : ℕ) {V U : TrivialSubgroup Λ M} (f : V ⟶ U) :
    (homologyDiagram M i).map f =
      ((restrictedHomologyDelta Λ (ContinuousMonoidHom.id (G ⧸ (V.1 : Subgroup G)))).functor i).map
          (descendTransition Λ M (leOfHom f)) ≫
        ((coinflation Λ (quotientMap (show V.1 ≤ U.1 from leOfHom f))).app i).app (descendU U) := by
  let E := (cohomologyDelta Λᵐᵒᵖ (G ⧸ (V.1 : Subgroup G))).functor i
  have h : coinflationDual Λ (quotientMap (show V.1 ≤ U.1 from leOfHom f)) i (descendU U) ≫
      E.map ((finiteTypeContinuousModuleDual.{0, w, w} Λ (G ⧸ (V.1 : Subgroup G))).map
        (descendTransition Λ M (leOfHom f)).op) =
      𝟙 _ ≫ (cohomologyDiagram M i).map f.op :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((E.map_comp _ _).symm.trans
      (congrArg E.map (resDualHom_comp_dual_map_descendTransition Λ M (leOfHom f))))).trans
        (Category.id_comp _).symm)
  exact ((HomologicalDeltaFunctor.map_op_comp_map_op_eq
    (CharacterModule.moduleCatDualOfMulOppositeFunctor Λ) _ _ _ (𝟙 _) h).trans
    ((congrArg (_ ≫ ·) ((CharacterModule.moduleCatDualOfMulOppositeFunctor Λ).map_id _)).trans
      (Category.comp_id _))).symm

/-- Moving a commutative square past two more arrows, in any category. -/
private theorem comp_comp_comp_of_comp_eq {C : Type*} [Category C] {X Y Y' Z W T : C}
    {a : X ⟶ Y} {b : Y ⟶ Z} {c : Z ⟶ W} {d : W ⟶ T} {e : X ⟶ Y'} {k : Y' ⟶ Z}
    (h : e ≫ k = a ≫ b) : a ≫ (b ≫ c) ≫ d = e ≫ k ≫ c ≫ d := by
  simp only [← Category.assoc, h]

omit [TotallyDisconnectedSpace G] in
/-- **The coinflation maps, read on `Tor`, are the change-of-rings maps**: through
`H_i(G/V, -) ≅ Tor_i^{Λ[G/V]}(-, Λ)` and `H_i(G/U, -) ≅ Tor_i^{Λ[G/U]}(-, Λ)`, the coinflation
`H_i(G/V, M) ⟶ H_i(G/U, M)` is the change-of-rings map
`Tor_i^{Λ[G/V]}(M, Λ) ⟶ Tor_i^{Λ[G/U]}(M, Λ)` along `Λ[G/V] → Λ[G/U]`. -/
theorem homologyTorIsoAt_inv_comp_map_comp_hom (i : ℕ) {V U : TrivialSubgroup Λ M}
    (f : V ⟶ U) :
    (homologyTorIsoAt Λ M i V).inv ≫ (homologyDiagram M i).map f ≫
        (homologyTorIsoAt Λ M i U).hom =
      ((torDelta Λ (G ⧸ (V.1 : Subgroup G))).functor i).map (descendTransition Λ M (leOfHom f)) ≫
        ((torChangeOfRings Λ (quotientMap (show V.1 ≤ U.1 from leOfHom f))).app i).app
          (descendU U) := by
  rw [homologyDiagram_map_eq, torChangeOfRings_app_app]
  exact comp_comp_comp_of_comp_eq
    (((homologyTorIso Λ (G ⧸ (V.1 : Subgroup G))).inv.app i).naturality
      (descendTransition Λ M (leOfHom f)))

/-- **The completed `Tor` diagram** `U ↦ Tor_i^{Λ[G/U]}(M, Λ)`, `U` running over the open normal
subgroups acting trivially on `M`, with the change-of-rings maps
`Tor_i^{Λ[G/V]}(M, Λ) ⟶ Tor_i^{Λ[G/U]}(M, Λ)` along `Λ[G/V] → Λ[G/U]` as transition maps
(`Stacks.GroupHomology.torChangeOfRings`). -/
def torDiagram (i : ℕ) : TrivialSubgroup Λ M ⥤ ModuleCat.{w} Λ where
  obj U := ((torDelta Λ (G ⧸ (U.1 : Subgroup G))).functor i).obj (descendU U)
  map {V U} f :=
    ((torDelta Λ (G ⧸ (V.1 : Subgroup G))).functor i).map (descendTransition Λ M (leOfHom f)) ≫
      ((torChangeOfRings Λ (quotientMap (show V.1 ≤ U.1 from leOfHom f))).app i).app (descendU U)
  map_id U := (homologyTorIsoAt_inv_comp_map_comp_hom Λ M i (𝟙 U)).symm.trans (by
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id])
  map_comp f g := (homologyTorIsoAt_inv_comp_map_comp_hom Λ M i (f ≫ g)).symm.trans
    (Eq.trans (by simp only [CategoryTheory.Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc])
      (congrArg₂ (· ≫ ·) (homologyTorIsoAt_inv_comp_map_comp_hom Λ M i f)
        (homologyTorIsoAt_inv_comp_map_comp_hom Λ M i g)))

omit [TotallyDisconnectedSpace G] in
/-- The transition maps of the completed `Tor` diagram are the change-of-rings maps. -/
theorem torDiagram_map (i : ℕ) {V U : TrivialSubgroup Λ M} (f : V ⟶ U) :
    (torDiagram Λ M i).map f =
      ((torDelta Λ (G ⧸ (V.1 : Subgroup G))).functor i).map (descendTransition Λ M (leOfHom f)) ≫
        ((torChangeOfRings Λ (quotientMap (show V.1 ≤ U.1 from leOfHom f))).app i).app
          (descendU U) :=
  rfl

omit [TotallyDisconnectedSpace G] in
/-- **The transition maps of the completed `Tor` diagram are coinflation**, read through
`H_i(G/U, -) ≅ Tor_i^{Λ[G/U]}(-, Λ)`. -/
theorem torDiagram_map_eq (i : ℕ) {V U : TrivialSubgroup Λ M} (f : V ⟶ U) :
    (torDiagram Λ M i).map f =
      (homologyTorIsoAt Λ M i V).inv ≫ (homologyDiagram M i).map f ≫
        (homologyTorIsoAt Λ M i U).hom :=
  (homologyTorIsoAt_inv_comp_map_comp_hom Λ M i f).symm

/-- The homology diagram is the completed `Tor` diagram. -/
def homologyDiagramIsoTorDiagram (i : ℕ) : homologyDiagram M i ≅ torDiagram Λ M i :=
  NatIso.ofComponents (homologyTorIsoAt Λ M i) fun f ↦
    (Iso.hom_inv_id_assoc (homologyTorIsoAt Λ M i _) _).symm.trans
      (congrArg (_ ≫ ·) (torDiagram_map_eq Λ M i f).symm)

/-- **Stacks Project, Section 03VI, notes on homology (1), corrected.** For a profinite group
`G`, a finite ring `Λ` and a finite `Λ`-module `M` with continuous `G`-action,
`H_i(G, M) ≅ lim_U Tor_i^{Λ[G/U]}(M, Λ)` in every degree `i`, the limit over the open normal
subgroups `U` acting trivially on `M` along the change-of-rings maps. Here
`H_i(G, M) = Hⁱ(G, M^∨)^∨`. -/
@[stacks 03VI "Notes on Homology (1), with Tor over Λ[[G]] read as completed Tor: \
  H_i(G, M) = lim_U Tor_i^{Λ[G/U]}(M, Λ) for finite M over a finite ring Λ"]
def homologyIsoLimitTor (i : ℕ) :
    ((restrictedHomologyDelta Λ (ContinuousMonoidHom.id G)).functor i).obj M ≅
      limit (torDiagram Λ M i) :=
  homologyIsoLimit M i ≪≫ HasLimit.isoOfNatIso (homologyDiagramIsoTorDiagram Λ M i)

/-- The component of `H_i(G, M) ≅ lim_U Tor_i^{Λ[G/U]}(M, Λ)` at `U` is coinflation
`H_i(G, M) ⟶ H_i(G/U, M)` followed by `H_i(G/U, M) ≅ Tor_i^{Λ[G/U]}(M, Λ)`. -/
theorem homologyIsoLimitTor_hom_π (i : ℕ) (U : TrivialSubgroup Λ M) :
    (homologyIsoLimitTor Λ M i).hom ≫ limit.π (torDiagram Λ M i) U =
      (homologyCone M i).π.app U ≫ (homologyTorIsoAt Λ M i U).hom := by
  rw [homologyIsoLimitTor, Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π,
    homologyIsoLimit, ← Category.assoc]
  exact congrArg (· ≫ _) (IsLimit.conePointUniqueUpToIso_hom_comp _ _ U)

section Naturality

variable {Λ} {M M' : FiniteTypeContinuousModule.{0, w, w} Λ G}

variable (M M') in
/-- **The open normal subgroups of `G` acting trivially on both `M` and `M'`**, ordered by
inclusion: a common index set for the completed `Tor` diagrams of `M` and `M'`. -/
abbrev TrivialSubgroupPair : Type w :=
  {U : OpenNormalSubgroup G // ActsTrivially Λ U M ∧ ActsTrivially Λ U M'}

/-- Two open normal subgroups acting trivially on `M` and `M'` intersect in one. -/
instance : SemilatticeInf (TrivialSubgroupPair M M') :=
  Subtype.semilatticeInf fun {U V} hU _ ↦
    ⟨fun g hg ↦ hU.1 g ((inf_le_left : U ⊓ V ≤ U) hg),
      fun g hg ↦ hU.2 g ((inf_le_left : U ⊓ V ≤ U) hg)⟩

/-- Some open normal subgroup acts trivially on both `M` and `M'`. -/
instance : Nonempty (TrivialSubgroupPair M M') :=
  let ⟨U, hU⟩ := exists_actsTrivially Λ M
  let ⟨U', hU'⟩ := exists_actsTrivially Λ M'
  ⟨⟨U ⊓ U', hU.mono Λ inf_le_left, hU'.mono Λ inf_le_right⟩⟩

variable (M M') in
/-- The inclusion of the common index set into the index set of `M`. -/
def pairFst : TrivialSubgroupPair M M' ⥤ TrivialSubgroup Λ M :=
  Monotone.functor (f := fun U ↦ ⟨U.1, U.2.1⟩) fun _ _ h ↦ h

variable (M M') in
/-- The inclusion of the common index set into the index set of `M'`. -/
def pairSnd : TrivialSubgroupPair M M' ⥤ TrivialSubgroup Λ M' :=
  Monotone.functor (f := fun U ↦ ⟨U.1, U.2.2⟩) fun _ _ h ↦ h

/-- The inclusion into the index set of `M` is full. -/
instance : (pairFst M M').Full := ⟨fun f ↦ ⟨homOfLE (leOfHom f), rfl⟩⟩

/-- The inclusion into the index set of `M` is faithful. -/
instance : (pairFst M M').Faithful := ⟨fun _ ↦ Subsingleton.elim _ _⟩

/-- The inclusion into the index set of `M'` is full. -/
instance : (pairSnd M M').Full := ⟨fun f ↦ ⟨homOfLE (leOfHom f), rfl⟩⟩

/-- The inclusion into the index set of `M'` is faithful. -/
instance : (pairSnd M M').Faithful := ⟨fun _ ↦ Subsingleton.elim _ _⟩

/-- **The common index set is cofinal in the index set of `M`**: every `U` acting trivially on
`M` contains `U ⊓ U'` with `U'` acting trivially on `M'`. -/
instance : (pairFst M M').Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ fun U ↦
    let ⟨U', hU'⟩ := exists_actsTrivially Λ M'
    ⟨⟨U.1 ⊓ U', U.2.mono Λ inf_le_left, hU'.mono Λ inf_le_right⟩,
      ⟨homOfLE (show U.1 ⊓ U' ≤ U.1 from inf_le_left)⟩⟩

/-- **The common index set is cofinal in the index set of `M'`.** -/
instance : (pairSnd M M').Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ fun U' ↦
    let ⟨U, hU⟩ := exists_actsTrivially Λ M
    ⟨⟨U ⊓ U'.1, hU.mono Λ inf_le_left, U'.2.mono Λ inf_le_right⟩,
      ⟨homOfLE (show U ⊓ U'.1 ≤ U'.1 from inf_le_right)⟩⟩

variable (f : M ⟶ M')

/-- The morphism `f : M ⟶ M'` over the finite quotient `G ⧸ U`. -/
def descendMap (U : TrivialSubgroupPair M M') :
    descendU ((pairFst M M').obj U) ⟶ descendU ((pairSnd M M').obj U) :=
  resPreimage Λ (quotientMk U.1) (quotientMk_surjective U.1) f

/-- **The morphism of completed `Tor` diagrams induced by `f : M ⟶ M'`**, on the common index set:
`Tor_i^{Λ[G/U]}(f, Λ)`. -/
def torDiagramMap (i : ℕ) :
    pairFst M M' ⋙ torDiagram Λ M i ⟶ pairSnd M M' ⋙ torDiagram Λ M' i where
  app U := ((torDelta Λ (G ⧸ (U.1 : Subgroup G))).functor i).map (descendMap f U)
  naturality {V U} g := by
    have hc := ((torChangeOfRings Λ (quotientMap (show V.1 ≤ U.1 from leOfHom g))).app i).naturality
      (descendMap f U)
    have ht : descendTransition Λ M (leOfHom ((pairFst M M').map g)) ≫
        (finiteTypeContinuousModuleRes.{0, w, w} Λ
          (quotientMap (show V.1 ≤ U.1 from leOfHom g))).map (descendMap f U) =
        descendMap f V ≫ descendTransition Λ M' (leOfHom ((pairSnd M M').map g)) :=
      finiteTypeContinuousModule_hom_ext fun _ ↦ rfl
    let T := (torDelta Λ (G ⧸ (V.1 : Subgroup G))).functor i
    calc (T.map (descendTransition Λ M (leOfHom ((pairFst M M').map g))) ≫
          ((torChangeOfRings Λ (quotientMap (show V.1 ≤ U.1 from leOfHom g))).app i).app
            (descendU ((pairFst M M').obj U))) ≫
          ((torDelta Λ (G ⧸ (U.1 : Subgroup G))).functor i).map (descendMap f U)
        = T.map (descendTransition Λ M (leOfHom ((pairFst M M').map g))) ≫
          T.map ((finiteTypeContinuousModuleRes.{0, w, w} Λ
            (quotientMap (show V.1 ≤ U.1 from leOfHom g))).map (descendMap f U)) ≫
          ((torChangeOfRings Λ (quotientMap (show V.1 ≤ U.1 from leOfHom g))).app i).app
            (descendU ((pairSnd M M').obj U)) :=
          (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hc.symm)
      _ = T.map (descendMap f V) ≫
          T.map (descendTransition Λ M' (leOfHom ((pairSnd M M').map g))) ≫
          ((torChangeOfRings Λ (quotientMap (show V.1 ≤ U.1 from leOfHom g))).app i).app
            (descendU ((pairSnd M M').obj U)) :=
          (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ((T.map_comp _ _).symm.trans
            ((congrArg T.map ht).trans (T.map_comp _ _)))).trans (Category.assoc _ _ _))
      _ = _ := rfl

/-- **The map of completed `Tor` limits induced by `f : M ⟶ M'`**: restrict both limits to the
open normal subgroups acting trivially on `M` and `M'` (a cofinal index set for both, so the
restriction of each limit is an isomorphism) and apply `Tor_i^{Λ[G/U]}(f, Λ)` there. -/
def limitTorMap (i : ℕ) : limit (torDiagram Λ M i) ⟶ limit (torDiagram Λ M' i) :=
  limit.pre (torDiagram Λ M i) (pairFst M M') ≫ limMap (torDiagramMap f i) ≫
    inv (limit.pre (torDiagram Λ M' i) (pairSnd M M'))

omit [TotallyDisconnectedSpace G] in
/-- Coinflation `H_i(G, -) ⟶ H_i(G/U, -)` is natural. -/
theorem homologyCone_π_naturality (i : ℕ) (U : TrivialSubgroupPair M M') :
    ((restrictedHomologyDelta Λ (ContinuousMonoidHom.id G)).functor i).map f ≫
        (homologyCone M' i).π.app ((pairSnd M M').obj U) =
      (homologyCone M i).π.app ((pairFst M M').obj U) ≫
        ((restrictedHomologyDelta Λ
          (ContinuousMonoidHom.id (G ⧸ (U.1 : Subgroup G)))).functor i).map (descendMap f U) :=
  HomologicalDeltaFunctor.map_op_comp_map_op_eq
    (CharacterModule.moduleCatDualOfMulOppositeFunctor Λ) _ _ _ _
    (((inflation Λᵐᵒᵖ (quotientMk U.1)).app i).naturality
      ((finiteTypeContinuousModuleDual.{0, w, w} Λ (G ⧸ (U.1 : Subgroup G))).map
        (descendMap f U).op)).symm

/-- The diagram chase behind `homologyIsoLimitTor_naturality_pre`, in any category. -/
private theorem naturality_chase {C : Type*} [Category C]
    {A A' L L' P P' T T' H H' : C} {Hf : A ⟶ A'} {h' : A' ⟶ L'} {pre' : L' ⟶ P'} {π' : P' ⟶ T'}
    {πL' : L' ⟶ T'} {c' : A' ⟶ H'} {k' : H' ⟶ T'} {c : A ⟶ H} {Hd : H ⟶ H'} {k : H ⟶ T}
    {Td : T ⟶ T'} {h : A ⟶ L} {πL : L ⟶ T} {pre : L ⟶ P} {πP : P ⟶ T} {lm : P ⟶ P'}
    (e₅ : pre' ≫ π' = πL') (e₁ : h' ≫ πL' = c' ≫ k') (e₃ : Hf ≫ c' = c ≫ Hd)
    (e₄ : Hd ≫ k' = k ≫ Td) (e₂ : h ≫ πL = c ≫ k) (e₆ : pre ≫ πP = πL)
    (e₇ : lm ≫ π' = πP ≫ Td) :
    ((Hf ≫ h') ≫ pre') ≫ π' = ((h ≫ pre) ≫ lm) ≫ π' := by
  simp only [Category.assoc, e₅, e₁, reassoc_of% e₃, e₄, e₇, reassoc_of% e₆, reassoc_of% e₂]

/-- Moving an isomorphism to the other side, in any category. -/
private theorem eq_comp_comp_inv {C : Type*} [Category C] {X Y Z W L P : C} {a : X ⟶ Y}
    {b : Y ⟶ Z} {p : Z ⟶ W} [IsIso p] {h : X ⟶ L} {q : L ⟶ P} {l : P ⟶ W}
    (e : (a ≫ b) ≫ p = (h ≫ q) ≫ l) : a ≫ b = h ≫ q ≫ l ≫ inv p := by
  rw [← Category.assoc, ← Category.assoc, ← e]
  simp

/-- **Naturality of `H_i(G, M) ≅ lim_U Tor_i^{Λ[G/U]}(M, Λ)` in `M`, on the common index set**:
for `f : M ⟶ M'`, restricted to the open normal subgroups acting trivially on both `M` and `M'`,
it carries `H_i(G, f)` to the map induced by `Tor_i^{Λ[G/U]}(f, Λ)`. -/
theorem homologyIsoLimitTor_naturality_pre (i : ℕ) :
    (((restrictedHomologyDelta Λ (ContinuousMonoidHom.id G)).functor i).map f ≫
        (homologyIsoLimitTor Λ M' i).hom) ≫ limit.pre (torDiagram Λ M' i) (pairSnd M M') =
      ((homologyIsoLimitTor Λ M i).hom ≫ limit.pre (torDiagram Λ M i) (pairFst M M')) ≫
        limMap (torDiagramMap f i) := by
  apply limit.hom_ext
  intro U
  exact naturality_chase (limit.pre_π (torDiagram Λ M' i) (pairSnd M M') U)
    (homologyIsoLimitTor_hom_π Λ M' i ((pairSnd M M').obj U)) (homologyCone_π_naturality f i U)
    (((homologyTorIso Λ (G ⧸ (U.1 : Subgroup G))).hom.app i).naturality (descendMap f U))
    (homologyIsoLimitTor_hom_π Λ M i ((pairFst M M').obj U))
    (limit.pre_π (torDiagram Λ M i) (pairFst M M') U) (limMap_π (torDiagramMap f i) U)

/-- **`H_i(G, M) ≅ lim_U Tor_i^{Λ[G/U]}(M, Λ)` is natural in `M`**: for `f : M ⟶ M'` it carries
`H_i(G, f)` to the map of limits induced by `Tor_i^{Λ[G/U]}(f, Λ)`
(`Stacks.GroupHomology.limitTorMap`). -/
theorem homologyIsoLimitTor_naturality (i : ℕ) :
    ((restrictedHomologyDelta Λ (ContinuousMonoidHom.id G)).functor i).map f ≫
        (homologyIsoLimitTor Λ M' i).hom =
      (homologyIsoLimitTor Λ M i).hom ≫ limitTorMap f i :=
  eq_comp_comp_inv (homologyIsoLimitTor_naturality_pre f i)

end Naturality

end Stacks.GroupHomology

end
