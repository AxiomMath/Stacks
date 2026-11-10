module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SiteUpColimit
public import Mathlib.CategoryTheory.Sites.CoverPreserving

/-!
# `u_p` transports the local equational criterion for flatness

Let `u : D ⥤ C` be a functor for which the index categories `I^u_U = CostructuredArrow u.op U`
of Stacks 00VC are filtered (`CategoryTheory.Functor.RepresentablyFlat`, which Stacks 00X3
produces from "`D` has finite limits and `u` preserves them"), let `O` be a presheaf of rings on
`D` and let `G` be a presheaf of `O`-modules.  `Stacks.ModuleUp` gives the colimit formula
`(u_p G)(U) = colim_{(V, φ) ∈ I^u_U} G(V)` together with the germ maps and the germ formula for
the scalar action.  This file draws from them the two consequences the proof of Stacks 05VD
("the pullback of a flat module is flat") consumes.

The first is purely about the filtered colimit:

`Stacks.ModuleUp.exists_index_relation_eq_zero`: given finitely many sections
`aᵢ ∈ (u_p O)(U)` and `sᵢ ∈ (u_p G)(U)` with `∑ᵢ aᵢ • sᵢ = 0`, there is a *single* index
`(V, φ) ∈ I^u_U` and sections `a'ᵢ ∈ O(V)`, `s'ᵢ ∈ G(V)` whose germs are the `aᵢ` and `sᵢ`
**and for which the relation already holds in `G(V)`**.

This is the step the source performs in the words "Hence we may assume there is a pair
`(V, φ) ∈ Ob(I^u_U)` … and elements `s''ₐ ∈ F(V)` and `f''ₐ ∈ O(V)` … such that
`∑ f''ₐ s''ₐ = 0` in `F(V)`".  Three facts of `Stacks.ModuleUp` enter: joint surjectivity of
the germ maps (used `2n` times and fused by filteredness), the germ formula for the scalar
action, and the vanishing criterion `abGerm_eq_zero_iff`.

The second is the transport itself:

`Stacks.ModuleUp.hasLocalRelationFactorizations_up`: if every single relation among sections
of `G` admits, on a covering sieve, a factorisation of the sections through a finite free module
by a matrix annihilating the relation, then the same holds for `u_p G` over `u_p O` — provided
`u` carries covering sieves to covering sieves.

That hypothesis and that conclusion are the presheaf-level form of parts (2) of Stacks 08FC,
whose sheaf-level form is `Stacks.SheafOfModules.HasLocalSingleRelationFactorizations`
(`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRelations`); the passage from the presheaf
form to the sheaf form is
`Stacks.ModuleUp.hasLocalRelationFactorizations_sheafify`
(`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifyRelationCriterion`).  See the
implementation notes for why the statement here is at the presheaf level.

## Main definitions

* `Stacks.ModuleUp.sectionRestrict`: the restriction map of a presheaf of modules, **at the
  result type `G.obj Y`**.  This is `(Stacks.ModuleUp.underlyingAb O G).map f`
  (`sectionRestrict_eq`, by `rfl`); see the implementation notes for why the spelling has to be
  pinned by a `def`.
* `Stacks.ModuleUp.LocallyFactorsRelation` and
  `Stacks.ModuleUp.HasLocalRelationFactorizations`: the local factorisation property of a
  single relation, and its universally quantified form, for a presheaf of modules over a
  presheaf of rings on a site.

## Main results

* `Stacks.ModuleUp.exists_index_relation_eq_zero`: **a relation among finitely many sections of
  `u_p G` descends to a single index of `I^u_U`.**
* `Stacks.ModuleUp.hasLocalRelationFactorizations_up`: **`u_p` transports the local equational
  criterion**, for a cover-preserving `u`.
* the germ calculus these rest on: `Stacks.ModuleUp.germ_jointly_surjective_family` (joint
  surjectivity of the germ maps for a *finite family*), `Stacks.ModuleUp.ringGerm_map` and
  `Stacks.ModuleUp.abGerm_map` (germs are unchanged along a morphism of `I^u_U`),
  `Stacks.ModuleUp.upRing_map_ringGerm` and `Stacks.ModuleUp.upAb_map_abGerm` (naturality of
  the germ maps in `U`).

## Implementation notes

**Why the statement is at the presheaf level.** The sheaf-level criterion of Stacks 08FC is
available in both directions
(`Stacks.SheafOfModules.isFlat_iff_hasLocalSingleRelationFactorizations`), so deducing
"`f^{-1}F` is flat over `f^{-1}O`" from `hasLocalRelationFactorizations_up` needs only that
`f^{-1}` of a sheaf of modules *is* the sheafification of `u_p`, plus the local
surjectivity/injectivity of the sheafification unit.  **Both halves are now available**, in
separate modules, which is why the transport is still stated here against `u_p` itself: this
file needs none of the sheafification hypotheses that either half carries.

* The local surjectivity/injectivity half is
  `Stacks.ModuleUp.hasLocalRelationFactorizations_sheafify`
  (`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifyRelationCriterion`), built from
  `CategoryTheory.Presheaf.imageSieve_mem`, `CategoryTheory.Presheaf.localPreimage` and
  `CategoryTheory.Presheaf.equalizerSieve_mem`.
* The identification half is `Stacks.ModuleUp.upModuleSheafPullbackIso`
  (`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteUpSheafification`, `:248`).  An earlier
  version of this note called it unavailable because
  `Stacks.ModuleUp.pullbackIsoUpModuleFunctor` takes the adjunction
  `upModuleFunctor u O ⊣ PresheafOfModules.pushforward (ringUnit u O)` as a hypothesis.  **That
  adjunction is proved**: `Stacks.ModuleUp.upModuleAdjunction`
  (`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SiteUpColimitAdjunction`, `:516`), with the
  hypothesis discharged in `Stacks.ModuleUp.pullbackIsoUpModuleFunctorOfColimit` (`:538`).

**Pinning the spelling of a restriction map.** `PresheafOfModules.map f` has codomain
`(ModuleCat.restrictScalars (O.map f).hom).obj (G.obj Y)`.  That is the same type as
`G.obj Y`, but it is not a spelling at which the `Module (O.obj Y)` instance is found, so a `•`
or a `∑` written against it does not elaborate — the failure is an application type mismatch
between two displayed types one of which is a `restrictScalars` of the other.  A type ascription
`(e : G.obj Y)` does not fix this; a `def` with a declared result type does, which is
`sectionRestrict`, with `sectionRestrict_eq` keeping the two from becoming two notions.  This is
the discipline of `StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SiteUpColimit`, applied to a
fifth boundary.

**`CoverPreserving` rather than continuity.** `hasLocalRelationFactorizations_up` takes
`CategoryTheory.CoverPreserving K J u` as a hypothesis rather than
`CategoryTheory.Functor.IsContinuous u K J`.  That is strictly weaker — continuity gives it by
`CategoryTheory.CoverPreserving.of_isContinuous` — and it avoids the universe constraint
`IsContinuous` carries through `Sheaf K (Type max u₁ v₁ u₂ v₂)`.  It is also all the proof uses:
the covering of `U` is the pullback along `φ : U ⟶ u V` of the image of a covering of `V`.

## References

* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
* [Stacks Project, Tag 00VC](https://stacks.math.columbia.edu/tag/00VC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ModuleUp

universe w

attribute [local instance] FinallySmall.preservesColimitsOfShape_of_isFiltered

/-! ### Restriction maps of a presheaf of modules, at a pinned result type -/

section SectionRestrict

variable {D : Type w} [SmallCategory D] (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O)

/-- The restriction map of `G` along `f : X ⟶ Y` in `Dᵒᵖ`, at the result type `G.obj Y`.

This is `(underlyingAb O G).map f` (see `sectionRestrict_eq`). The `def` exists for its declared
result type; see the implementation notes of the module. -/
noncomputable def sectionRestrict {X Y : Dᵒᵖ} (f : X ⟶ Y) (m : G.obj X) : G.obj Y :=
  (underlyingAb O G).map f m

/-- `sectionRestrict O G f m` is the image of `m` under `(underlyingAb O G).map f`. -/
theorem sectionRestrict_eq {X Y : Dᵒᵖ} (f : X ⟶ Y) (m : G.obj X) :
    sectionRestrict O G f m = (underlyingAb O G).map f m := rfl

/-- Restriction is semilinear: `(a • m)|_Y = a|_Y • m|_Y`. -/
theorem sectionRestrict_smul {X Y : Dᵒᵖ} (f : X ⟶ Y) (a : O.obj X) (m : G.obj X) :
    sectionRestrict O G f (a • m) = O.map f a • sectionRestrict O G f m :=
  G.map_smul f a m

/-- Restriction is additive on finite sums. -/
theorem sectionRestrict_sum {X Y : Dᵒᵖ} (f : X ⟶ Y) {n : ℕ} (m : Fin n → G.obj X) :
    sectionRestrict O G f (∑ i : Fin n, m i) = ∑ i : Fin n, sectionRestrict O G f (m i) :=
  map_sum ((underlyingAb O G).map f).hom _ _

end SectionRestrict

variable {C D : Type w} [SmallCategory C] [SmallCategory D] (u : D ⥤ C) [RepresentablyFlat u]

/-! ### Germ calculus: functoriality in the index and in the object -/

section Germ

variable (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O)

/-- **Germs are unchanged along a morphism of the index category.**  For `h : c ⟶ c'` in
`I^u_U`, the germ at `c'` of the restriction of `a` equals the germ of `a` at `c`. -/
lemma ringGerm_map {U : Cᵒᵖ} {c c' : CostructuredArrow u.op U} (h : c ⟶ c')
    (a : O.obj c.left) :
    ringGerm u O c' ((O.map h.left) a) = ringGerm u O c a := by
  have hw : (pbRdiag u O U).map h.op.op ≫ colimit.ι (pbRdiag u O U) (idx u c')
      = colimit.ι (pbRdiag u O U) (idx u c) := colimit.w (pbRdiag u O U) h.op.op
  have h2 : colimit.ι (pbRdiag u O U) (idx u c') (((pbRdiag u O U).map h.op.op) a)
      = colimit.ι (pbRdiag u O U) (idx u c) a := by rw [← hw]; rfl
  change (pbRingIso u O U).hom (colimit.ι (pbRdiag u O U) (idx u c') ((O.map h.left) a)) = _
  rw [show ((O.map h.left) a) = ((pbRdiag u O U).map h.op.op) a from rfl, h2]
  rfl

omit [RepresentablyFlat u] in
/-- The module analogue of `ringGerm_map`. -/
lemma abGerm_map {U : Cᵒᵖ} {c c' : CostructuredArrow u.op U} (h : c ⟶ c')
    (m : G.obj c.left) :
    abGerm u O G c' (sectionRestrict O G h.left m) = abGerm u O G c m := by
  have hw : (pbMmod u O G U).presheaf.map h.op.op ≫
      colimit.ι (pbMmod u O G U).presheaf (idx u c')
      = colimit.ι (pbMmod u O G U).presheaf (idx u c) :=
    colimit.w (pbMmod u O G U).presheaf h.op.op
  have h2 : colimit.ι (pbMmod u O G U).presheaf (idx u c')
        (((pbMmod u O G U).presheaf.map h.op.op) m)
      = colimit.ι (pbMmod u O G U).presheaf (idx u c) m := by rw [← hw]; rfl
  change (pbAbIso u O G U).hom
    (colimit.ι (pbMmod u O G U).presheaf (idx u c') (sectionRestrict O G h.left m)) = _
  rw [show (sectionRestrict O G h.left m)
      = ((pbMmod u O G U).presheaf.map h.op.op) m from rfl, h2]
  rfl

/-- **Naturality of the germ maps in `U`.**  Restricting the germ of `a : O(V)` at
`(V, φ) ∈ I^u_U` along `i : U ⟶ U'` gives the germ of the same `a` at the reindexed object
`(V, φ ≫ i) ∈ I^u_{U'}`. -/
theorem upRing_map_ringGerm {U U' : Cᵒᵖ} (i : U ⟶ U') (c : CostructuredArrow u.op U)
    (a : O.obj c.left) :
    (upRing u O).map i (ringGerm u O c a)
      = ringGerm u O ((CostructuredArrow.map i).obj c) a := by
  have h1 : (upRing u O).map i (ringGerm u O c a)
      = (pbRingIso u O U').hom (pbRingReindex u O i (colimit.ι (pbRdiag u O U) (idx u c) a)) :=
    pbRingIso_naturality u O i (colimit.ι (pbRdiag u O U) (idx u c) a)
  rw [h1, pbRingReindex_ι u O i (idx u c) a]
  rfl

omit [RepresentablyFlat u] in
/-- The module analogue of `upRing_map_ringGerm`. -/
theorem upAb_map_abGerm {U U' : Cᵒᵖ} (i : U ⟶ U') (c : CostructuredArrow u.op U)
    (m : G.obj c.left) :
    (upAb u (underlyingAb O G)).map i (abGerm u O G c m)
      = abGerm u O G ((CostructuredArrow.map i).obj c) m := by
  have h1 : (upAb u (underlyingAb O G)).map i (abGerm u O G c m)
      = (pbAbIso u O G U').hom
          (pbAbReindex u O G i (colimit.ι (pbMmod u O G U).presheaf (idx u c) m)) :=
    pbAbIso_naturality u O G i (colimit.ι (pbMmod u O G U).presheaf (idx u c) m)
  rw [h1, pbAbReindex_ι u O G i (idx u c) m]
  rfl

/-- **Joint surjectivity of the germ maps for a finite family.**  Finitely many sections of
`u_p O` and finitely many sections of `u_p G` over the same object `U` are all germs at a
*single* index `(V, φ) ∈ I^u_U`.

This is `germ_jointly_surjective₂` iterated and fused by the filteredness of `I^u_U`, which is
what lets the proof of Stacks 05VD replace the `2n` sections `fₐ`, `sₐ` by sections over one
`V`. -/
theorem germ_jointly_surjective_family {U : Cᵒᵖ} (n : ℕ)
    (r : Fin n → (upRing u O).obj U) (m : Fin n → (upAb u (underlyingAb O G)).obj U) :
    ∃ (c : CostructuredArrow u.op U) (a : Fin n → O.obj c.left) (s : Fin n → G.obj c.left),
      (∀ i, ringGerm u O c (a i) = r i) ∧ (∀ i, abGerm u O G c (s i) = m i) := by
  induction n with
  | zero =>
      obtain ⟨c⟩ := IsFiltered.nonempty (C := CostructuredArrow u.op U)
      exact ⟨c, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
      obtain ⟨c₀, a₀, s₀, ha₀, hs₀⟩ := ih (fun i => r i.succ) (fun i => m i.succ)
      obtain ⟨c₁, a₁, s₁, ha₁, hs₁⟩ := germ_jointly_surjective₂ u O G (r 0) (m 0)
      refine ⟨IsFiltered.max c₀ c₁,
        Fin.cases (O.map (IsFiltered.rightToMax c₀ c₁).left a₁)
          (fun i => O.map (IsFiltered.leftToMax c₀ c₁).left (a₀ i)),
        Fin.cases (sectionRestrict O G (IsFiltered.rightToMax c₀ c₁).left s₁)
          (fun i => sectionRestrict O G (IsFiltered.leftToMax c₀ c₁).left (s₀ i)), ?_, ?_⟩
      · refine Fin.cases ?_ ?_
        · exact (ringGerm_map u O (IsFiltered.rightToMax c₀ c₁) a₁).trans ha₁
        · exact fun j => (ringGerm_map u O (IsFiltered.leftToMax c₀ c₁) (a₀ j)).trans (ha₀ j)
      · refine Fin.cases ?_ ?_
        · exact (abGerm_map u O G (IsFiltered.rightToMax c₀ c₁) s₁).trans hs₁
        · exact fun j => (abGerm_map u O G (IsFiltered.leftToMax c₀ c₁) (s₀ j)).trans (hs₀ j)

/-- The germ of a sum of scalar multiples is the sum of the products of the germs. -/
private theorem abGerm_sum_smul {U : Cᵒᵖ} (c : CostructuredArrow u.op U) {n : ℕ}
    (a : Fin n → O.obj c.left) (s : Fin n → G.obj c.left) :
    letI := upModule u O G U
    abGerm u O G c (∑ i : Fin n, a i • s i)
      = ∑ i : Fin n, ringGerm u O c (a i) • abGerm u O G c (s i) :=
  (map_sum (abGerm u O G c).hom _ _).trans
    (Finset.sum_congr rfl fun i _ => germ_smul u O G c (a i) (s i))

/-- **A relation among finitely many sections of `u_p G` descends to a single index.**

Given `aᵢ ∈ (u_p O)(U)` and `sᵢ ∈ (u_p G)(U)` with `∑ᵢ aᵢ • sᵢ = 0`, there is an index
`(V, φ) ∈ I^u_U` and sections `a'ᵢ ∈ O(V)`, `s'ᵢ ∈ G(V)` with germs `aᵢ` and `sᵢ` for which the
relation holds **already in `G(V)`**.

This is the paragraph of the proof of Stacks 05VD beginning "Then after another replacement of
`U` by the members of a covering we may assume that `∑ f'ₐ s'ₐ` is zero in `u_p F(U)`": joint
surjectivity puts the `2n` sections at one index, the germ formula turns the relation into the
vanishing of the germ of `∑ a'ᵢ • s'ᵢ`, and `abGerm_eq_zero_iff` moves past the one further
index at which that section is killed. -/
theorem exists_index_relation_eq_zero {U : Cᵒᵖ} (n : ℕ)
    (r : Fin n → (upRing u O).obj U) (m : Fin n → (upAb u (underlyingAb O G)).obj U)
    (hrel : letI := upModule u O G U; ∑ i : Fin n, r i • m i = 0) :
    ∃ (c : CostructuredArrow u.op U) (a : Fin n → O.obj c.left) (s : Fin n → G.obj c.left),
      (∀ i, ringGerm u O c (a i) = r i) ∧ (∀ i, abGerm u O G c (s i) = m i) ∧
        ∑ i : Fin n, a i • s i = 0 := by
  obtain ⟨c₀, a₀, s₀, ha₀, hs₀⟩ := germ_jointly_surjective_family u O G n r m
  let _ := upModule u O G U
  have hsum : abGerm u O G c₀ (∑ i : Fin n, a₀ i • s₀ i) = 0 := by
    rw [abGerm_sum_smul]
    simpa only [ha₀, hs₀] using hrel
  obtain ⟨c, h, hz⟩ := (abGerm_eq_zero_iff u O G c₀ (∑ i : Fin n, a₀ i • s₀ i)).1 hsum
  refine ⟨c, fun i => O.map h.left (a₀ i), fun i => sectionRestrict O G h.left (s₀ i),
    fun i => (ringGerm_map u O h (a₀ i)).trans (ha₀ i),
    fun i => (abGerm_map u O G h (s₀ i)).trans (hs₀ i), ?_⟩
  have e3 : sectionRestrict O G h.left (∑ i : Fin n, a₀ i • s₀ i)
      = ∑ i : Fin n, O.map h.left (a₀ i) • sectionRestrict O G h.left (s₀ i) := by
    rw [sectionRestrict_sum]
    exact Finset.sum_congr rfl fun i _ => sectionRestrict_smul O G h.left (a₀ i) (s₀ i)
  rw [← e3]
  exact hz

end Germ

/-! ### The local equational criterion and its transport along `u_p` -/

section Transport

/-- `LocallyFactorsRelation K O G V a s` says that the relation recorded by
`a : Fin n → O(V)` among the sections `s : Fin n → G(V)` admits, locally on `V`, a factorisation
of `s` through a finite free module annihilating `a`: there is a covering sieve `T` of `V` such
that every `g : V' ⟶ V` in `T` admits sections `t : Fin l → G(V')` and a matrix
`B : Fin l → Fin n → O(V')` with `s i |_{V'} = ∑ₖ B k i • t k` and `B · a|_{V'} = 0`.

This is the conclusion of part (2) of Stacks 08FC, for a presheaf of modules rather than a
sheaf; the sheaf-level form is `Stacks.SheafOfModules.LocallyFactorsRelations` at `m = 1`. -/
def LocallyFactorsRelation {D : Type w} [SmallCategory D] (K : GrothendieckTopology D)
    (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O) (V : D) {n : ℕ}
    (a : Fin n → O.obj (op V)) (s : Fin n → G.obj (op V)) : Prop :=
  ∃ T : Sieve V, T ∈ K V ∧
    ∀ ⦃V' : D⦄ (g : V' ⟶ V), T g →
      ∃ (l : ℕ) (t : Fin l → G.obj (op V')) (B : Fin l → Fin n → O.obj (op V')),
        (∀ i, sectionRestrict O G g.op (s i) = ∑ k : Fin l, B k i • t k) ∧
        (∀ k, ∑ i : Fin n, B k i * O.map g.op (a i) = 0)

/-- Every single relation among sections of `G` admits a local finite-free factorisation of the
sections annihilating that relation.  This is part (2) of Stacks 08FC for a presheaf of
modules. -/
def HasLocalRelationFactorizations {D : Type w} [SmallCategory D] (K : GrothendieckTopology D)
    (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O) : Prop :=
  ∀ (V : D) (n : ℕ) (a : Fin n → O.obj (op V)) (s : Fin n → G.obj (op V)),
    (∑ i : Fin n, a i • s i = 0) → LocallyFactorsRelation K O G V a s

variable {K : GrothendieckTopology D} {J : GrothendieckTopology C}
  (O : Dᵒᵖ ⥤ RingCat.{w}) (G : PresheafOfModules.{w} O)

/-- **`u_p` transports the local equational criterion.**

If every single relation among sections of `G` factors locally through a finite free module by a
matrix annihilating it, and if `u` carries covering sieves of `K` to covering sieves of `J`,
then the same holds for `u_p G` over `u_p O`.

This is the final paragraph of the proof of Stacks 05VD, with the sheafification steps removed:
a relation among sections of `u_p G` over `U` is pushed to a single index `(V, φ) ∈ I^u_U` by
`exists_index_relation_eq_zero`, the hypothesis is applied over `V`, and the resulting covering
`{Vᵢ → V}` is pulled back along `φ` to the covering `Uᵢ = U ×_{φ, u V} u(Vᵢ)` of `U` — which is
a covering because the image of a covering is a covering and covering sieves are stable under
pullback.  The factorisation transports because `ringGerm` is a ring map, `abGerm` is additive,
and the two commute with the scalar action (`germ_smul`) and with restriction
(`upAb_map_abGerm`, `abGerm_map`). -/
theorem hasLocalRelationFactorizations_up (hcp : CoverPreserving K J u)
    (hG : HasLocalRelationFactorizations K O G) :
    HasLocalRelationFactorizations J (upRing u O)
      ((upModuleFunctor u O).obj G) := by
  intro U n a s hrel
  obtain ⟨c, a', s', ha', hs', hzero⟩ := exists_index_relation_eq_zero u O G n a s hrel
  obtain ⟨T, hT, hfac⟩ := hG c.left.unop n a' s' hzero
  refine ⟨(T.functorPushforward u).pullback c.hom.unop,
    J.pullback_stable _ (hcp.cover_preserve hT), ?_⟩
  rintro U' g ⟨Z, g', ψ, hg', hψ⟩
  obtain ⟨l, t, B, hB1, hB2⟩ := hfac g' hg'
  -- The index of `I^u_{U'}` at which everything is a germ, and the morphism of `I^u_{U'}`
  -- from the reindexed `c` to it.
  let c' : CostructuredArrow u.op (op U') := CostructuredArrow.mk (Y := op Z) ψ.op
  let hmk : (CostructuredArrow.map g.op).obj c ⟶ c' :=
    CostructuredArrow.homMk g'.op (Quiver.Hom.unop_inj hψ.symm)
  have hleft : hmk.left = g'.op := rfl
  refine ⟨l, fun k => abGerm u O G c' (t k), fun k i => ringGerm u O c' (B k i), ?_, ?_⟩
  · intro i
    have hrestrict : sectionRestrict (upRing u O) ((upModuleFunctor u O).obj G) g.op (s i)
        = abGerm u O G c' (sectionRestrict O G g'.op (s' i)) := by
      rw [← hs' i]
      rw [show sectionRestrict (upRing u O) ((upModuleFunctor u O).obj G) g.op
            (abGerm u O G c (s' i))
          = (upAb u (underlyingAb O G)).map g.op (abGerm u O G c (s' i)) from rfl,
        upAb_map_abGerm u O G g.op c (s' i)]
      exact (hleft ▸ (abGerm_map u O G hmk (s' i))).symm
    rw [hrestrict, hB1 i]
    exact abGerm_sum_smul u O G c' (fun k => B k i) t
  · intro k
    have hcol : ∀ i, (upRing u O).map g.op (a i) = ringGerm u O c' (O.map g'.op (a' i)) := by
      intro i
      rw [← ha' i, upRing_map_ringGerm u O g.op c (a' i)]
      exact (hleft ▸ (ringGerm_map u O hmk (a' i))).symm
    calc ∑ i : Fin n, ringGerm u O c' (B k i) * (upRing u O).map g.op (a i)
        = ∑ i : Fin n, ringGerm u O c' (B k i * O.map g'.op (a' i)) :=
          Finset.sum_congr rfl fun i _ => by
            rw [hcol i, map_mul (ringGerm u O c').hom]
      _ = ringGerm u O c' (∑ i : Fin n, B k i * O.map g'.op (a' i)) :=
          (map_sum (ringGerm u O c').hom _ _).symm
      _ = 0 := by rw [hB2 k, map_zero]

end Transport

end Stacks.ModuleUp

end
