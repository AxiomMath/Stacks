module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackColimit

/-!
# The sections of a pullback along an equivalence of sites are a base change

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSectionsBaseChange` describes the sections
of
`PresheafOfModules.pullback` as a base change for a change of rings along the **identity** functor
of the site, and says that for a general functor of sites `F : C ⥤ D` there is "no candidate of the
simple shape `R'(V) ⊗_{R(V)} M(V)` to compare the sections with", because the sections are then a
filtered colimit of base changes rather than one base change.  This file supplies the missing
middle case: when `F` is **fully faithful** and the object `U` of the target is isomorphic to one
of the form `F(V₀)` — in particular whenever `F` is an *equivalence* — that colimit has a terminal
index, so it collapses to a single term and the sections are a base change after all.

The motivating case is the map of sites `TopologicalSpace.Opens.map f` for `f` a **homeomorphism**
of topological spaces, which is where the crystalline comparison map of [Stacks, Tag 07JN] lives:
the map of ambient schemes there is a closed immersion of thickenings, whose underlying continuous
map is a homeomorphism and not merely a closed map.  `TopologicalSpace.Opens.mapMapIso` turns a
`TopCat`-isomorphism into an equivalence of the open-set categories, which is exactly the
hypothesis the reduction needs.

## Main definitions

* `CategoryTheory.CostructuredArrow.isTerminalMkIso`: for a **fully faithful** functor `G`, a
  costructured arrow `G(V₀) ≅ U` which is an isomorphism is a *terminal* object of
  `CostructuredArrow G U`.  This is the whole reason the reduction works, and it is pure category
  theory: fullness gives the factorisation of an arbitrary `G(X) ⟶ U` through it, faithfulness
  makes that factorisation unique.
* `Stacks.PullbackEquivalence.indexIso`: hence the colimit of `Stacks.PullbackColimit.diagram`,
  whose index category is `CostructuredArrow F.op U`, is its single term at that terminal index.
* `Stacks.PullbackEquivalence.pullbackObjIsoBaseChange`: **the sections of
  `PresheafOfModules.pullback` over `U` are the base change `R(U) ⊗_{S(V₀)} N(V₀)`**, along the
  composite ring map `S(V₀) → R(F V₀) → R(U)`.
* `Stacks.PullbackEquivalence.objIsoBaseChangeOfIsIso`: for a comparison map out of the pullback
  which is an isomorphism, the sections of its target are that same base change.
* `Stacks.PullbackEquivalence.comparison`: the comparison map `(pullback α).obj N ⟶ Q` out of the
  pullback, i.e. the adjoint transpose of a morphism `ψ : N ⟶ (pushforward α).obj Q`.
* `Stacks.PullbackEquivalence.pullbackObjIsoBaseChangeOfEquivalence` and
  `opensPullbackObjIsoBaseChange`: the specialisations to an equivalence of sites and to
  `TopologicalSpace.Opens.map` of an isomorphism of topological spaces, the latter being the form
  the crystalline consumer wants.

## Main results

* `Stacks.PullbackEquivalence.exists_eq_tmul_one`: the ring-theoretic input.  Every element of a
  base change along a *surjection* is `1 ⊗ m` — not merely every pure tensor.
* `Stacks.PullbackEquivalence.exists_germ_eq`: every section of the colimit model over `U` is a
  single germ at the terminal index.
* `Stacks.PullbackEquivalence.exists_eq_map_unit`: **every section of the pullback over `U` is the
  restriction along `e` of a unit section.**  When the ring map `S(V₀) → R(F V₀)` is surjective,
  the sections of `(pullback α).obj N` over `U` are exactly the elements `(unit n)|_U` for `n` a
  section of `N` over `V₀`; no sums and no scalar multiples are needed.  This is the
  general-functor form of the collapse that
  `Stacks.NoncommChangeOfRings.Presheaf.exists_apply_eq_transpose_apply` proves for the identity
  functor.
* `Stacks.PullbackEquivalence.comparison_app_map_unit`: the comparison map, read on those sections,
  is `(unit n)|_U ↦ ψ(n)|_U`.  This is the computation rule that Mathlib's abstract left adjoint
  does not supply.
* `Stacks.PullbackEquivalence.surjective_app_of_surjective_comparison`: **a surjective comparison
  map forces the map it is the transpose of to be surjective**, over an object isomorphic to one in
  the image of `F` and over which the ring map is surjective.  Together with
  `surjective_comparison_app_of_surjective_app`, the converse, which needs no surjectivity of the
  ring map.

## What is and is not proved

The hypotheses, exactly.

* Everything below assumes `[F.Full]` and `[F.Faithful]` — fullness alone makes the index object
  *weakly* terminal, which is enough for the generation half that
  `PresheafOfModules.range_homEquivSymm_app_eq_generatedSubmodule` already provides, but not enough
  to collapse the colimit, which needs the factorisation to be unique.  `F` is *not* assumed
  essentially surjective: the isomorphism `e : F.op.obj V₀ ≅ U` is data, supplied at the one object
  `U` in question.  `Stacks.PullbackEquivalence.essImageIso` produces it at every object when `F`
  *is* an equivalence.
* `pullbackObjIsoBaseChange` assumes **nothing** about `α` or `N`: no surjectivity, no
  quasi-coherence, no flatness, no presentation of `N`.  As for the identity functor
  (`Stacks.NoncommChangeOfRings.Presheaf.pullbackObjIso`) this is because the isomorphism comes
  from uniqueness of left adjoints together with a terminal index object, not from a computation on
  sections.
* `exists_eq_map_unit` and `surjective_app_of_surjective_comparison` assume in addition that
  `(α.app V₀).hom : S(V₀) → R(F V₀)` is surjective.  That hypothesis is as necessary here as it is
  for the identity functor; the counterexample without it is the one recorded in the implementation
  notes of `PullbackSectionsBaseChange` (`R = ℤ`, `R' = ℚ`, `M = R`, `N = R'`).
* The standing hypotheses of `Stacks.PullbackColimit` are inherited: `C` and `D` are **small**
  categories in `Type u`, the presheaves of rings are valued in `CommRingCat.{u}`, and the
  presheaves of modules are `PresheafOfModules.{u}`.  Smallness is what Mathlib itself assumes for
  `PresheafOfModules.pullback` to exist; commutativity is forced by `ModuleCat.extendScalars`.

What is **not** proved:

* **No `@[stacks]` attribute is placed.**  Neither the description of the sections of a pullback
  nor the surjectivity transfer is tagged content of the source; both are auxiliaries used in the
  proof of [Stacks, Tag 07JN] and in the construction of the canonical connection of
  [Stacks, Tag 07J6].
* **The local (sheaf-theoretic) form of the surjectivity transfer.**
  `Stacks.NoncommChangeOfRings.Presheaf.isLocallySurjective_of_isLocallySurjective_transpose`
  upgrades the objectwise statement to a locally-surjective one for the identity functor, where
  both maps live on one site carrying one topology.  For a general `F` the comparison map and the
  map it transposes live on *different* sites, so transporting local surjectivity needs the
  equivalence to be continuous for the two topologies; that step is not taken here, and the
  statements below are objectwise.
* **Nothing is claimed for `SheafOfModules.pullback`.**  As in `PullbackSectionsBaseChange`, the
  pullback of *sheaves* of modules is the sheafification of the presheaf pullback, and inverting
  the sheafification unit of a base change is exactly where flatness or a presentation has to
  enter.
* **The transport of the crystalline comparison map into the `CommRingCat` spelling.**  Everything
  here needs presheaves of `CommRingCat`, because `ModuleCat.extendScalars` and hence
  `Stacks.PullbackColimit` do.  At the level of the site that is no obstacle:
  `Crystalline.GlobalCrystallineSituation.SmallSite.structurePresheaf` is the structure presheaf
  valued in `CommRingCat`, and `Crystalline.GlobalCrystallineSituation.SmallSite.crisRing` is
  definitionally its composite with `forget₂ CommRingCat RingCat`.  But the objects the comparison
  map is built from — `Crystalline.GlobalCrystallineSituation.Thickening.ringRestriction`,
  `moduleRestriction`, `restrictionFMap` and
  `Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.moduleComparison` — are
  all declared over the `RingCat`-valued `crisRing`, and are not restated over
  `structurePresheaf`.  Until they are, the statements below cannot be applied to
  `moduleComparison` without that transport, which is not performed here.

## Implementation notes

**Why the surjectivity transfer is proved through the unit and not through the generated
submodule.** `PresheafOfModules.generatedSubmodule`, and with it the general-functor generation
half `PresheafOfModules.range_homEquivSymm_app_eq_generatedSubmodule`, live in
`StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ComparisonSurjectivity`.  That module
declares
`PresheafOfModules.restrictₛₗ_comp_apply`, `restrictₛₗ_id_apply` and `map_id_apply`, and so does
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor`, which
`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackColimit` imports; the two modules
therefore **cannot both be imported** into one file.  Since the colimit model is what makes the
collapse available at all, the surjectivity statements here are derived from
`exists_eq_map_unit` — every section of the pullback is a restricted unit section — rather than
from the generated submodule.  The route through the unit is in any case the more informative one,
since it carries the computation rule `comparison_app_map_unit` with it.

**The germ at the terminal index, and the unit.**  `Stacks.PullbackColimit.unit` is the germ of
`1 ⊗ a` at the index `(V, 𝟙)` of the colimit over `F(V)`; the germ at the terminal index `(V₀, e)`
of the colimit over `U` is its restriction along `e`, which is `germ_eq_pullbackObjIso_hom`.
Transporting that from the model to Mathlib's abstract pullback is
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`: the comparison of two left adjoints of
one functor carries one unit to the other.  No computation inside `Adjunction.leftAdjointUniq` is
needed, and in particular `Stacks.PullbackColimit.homEquiv` is never unfolded.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct ChangeOfRings

universe v v₁ v₂ u₁ u₂ u

noncomputable section

namespace CategoryTheory.CostructuredArrow

/-- **For a fully faithful functor `G`, a costructured arrow which is an isomorphism is a terminal
object of `CostructuredArrow G U`.**  Every `T` maps to it by the preimage under `G` of
`T.hom ≫ e.inv`: fullness gives that morphism, faithfulness its uniqueness.

This is what makes the pullback of presheaves of modules along an equivalence of sites computable.
The index category of the colimit of `Stacks.PullbackColimit.diagram` is
`CostructuredArrow F.op U`, so a terminal object there collapses the colimit to a single one of its
terms. -/
def isTerminalMkIso {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {G : C ⥤ D}
    [G.Full] [G.Faithful] {V₀ : C} {U : D} (e : G.obj V₀ ≅ U) :
    IsTerminal (mk (S := G) e.hom) :=
  IsTerminal.ofUniqueHom (fun T => homMk (G.preimage (T.hom ≫ e.inv)) (by simp)) fun T m => by
    have h : G.map m.left = G.map (G.preimage (T.hom ≫ e.inv)) := by
      rw [Functor.map_preimage, ← w m]
      simp
    exact hom_ext _ _ (G.map_injective h)

end CategoryTheory.CostructuredArrow

namespace PresheafOfModules

/-! ### Restriction along an isomorphism of objects is bijective -/

section Restrict

variable {D : Type u₂} [Category.{v₂} D] {R : Dᵒᵖ ⥤ RingCat.{u}} (N : PresheafOfModules.{v} R)
  {U U' : Dᵒᵖ} (e : U ≅ U')

/-- Restricting along `e.hom` and then along `e.inv` is the identity. -/
theorem map_inv_map_hom (x : N.obj U) : N.map e.inv (N.map e.hom x) = x := by
  rw [← N.map_comp_apply, e.hom_inv_id, map_id_apply]

/-- Restricting along `e.inv` and then along `e.hom` is the identity. -/
theorem map_hom_map_inv (x : N.obj U') : N.map e.hom (N.map e.inv x) = x :=
  map_inv_map_hom N e.symm x

/-- **The restriction map of a presheaf of modules along an isomorphism of objects is bijective**,
with inverse the restriction along the inverse isomorphism. -/
theorem bijective_map_of_iso : Function.Bijective (N.map e.hom) :=
  Function.bijective_iff_has_inverse.2
    ⟨N.map e.inv, map_inv_map_hom N e, map_hom_map_inv N e⟩

end Restrict

end PresheafOfModules

namespace Stacks.PullbackEquivalence

open PresheafOfModules Stacks.PullbackModel Stacks.PullbackColimit

/-! ### Two elementary inputs -/

section Inputs

/-- A morphism of `ModuleCat` which is an isomorphism is injective on elements. -/
theorem injective_isoHom {B : Type u} [Ring B] {M M' : ModuleCat.{u} B} (i : M ≅ M') :
    Function.Injective i.hom :=
  (ConcreteCategory.bijective_of_isIso i.hom).1

variable {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B} {M : ModuleCat.{u} A}

/-- **Every element of a base change along a surjection is `1 ⊗ m`.**  Not merely every pure
tensor: the elements of that form are closed under addition, and a pure tensor `f a ⊗ m` is
`1 ⊗ (a • m)`, so the induction over the tensor product never leaves them.

This is the `ModuleCat.extendScalars` form of
`Stacks.NoncommChangeOfRings.objTmul_eq_of_surjective`, strengthened from pure tensors to all
elements as `Stacks.NoncommChangeOfRings.exists_apply_eq_desc_apply` does. -/
theorem exists_eq_tmul_one (hf : Function.Surjective f) (x : (ModuleCat.extendScalars f).obj M) :
    ∃ m : M, x = tmul f 1 m := by
  induction x using TensorProduct.inductionOn with
  | tmul b m =>
      obtain ⟨a, rfl⟩ := hf b
      exact ⟨a • m, (tmul_one_smul f a m).symm⟩
  | add x y hx hy =>
      obtain ⟨m, rfl⟩ := hx
      obtain ⟨m', rfl⟩ := hy
      exact ⟨m + m', (tmul_one_add f m m').symm⟩

end Inputs

/-! ### The colimit collapses at a terminal index -/

section Collapse

/-- The restriction map of a presheaf of commutative rings along an isomorphism of objects is
surjective, being an isomorphism of rings. -/
theorem surjective_map_hom {D : Type u₂} [Category.{v₂} D] (R : Dᵒᵖ ⥤ CommRingCat.{u})
    {U U' : Dᵒᵖ} (e : U ≅ U') : Function.Surjective (R.map e.hom).hom :=
  (ConcreteCategory.bijective_of_isIso (R.map e.hom)).2

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D) [F.Full] [F.Faithful]
  (R : Dᵒᵖ ⥤ CommRingCat.{u})
  (A : PresheafOfModules.{u} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
  {U : Dᵒᵖ} {V₀ : Cᵒᵖ} (e : F.op.obj V₀ ≅ U)

/-- **The colimit computing the pullback collapses to a single term.**  For a fully faithful
functor of sites the index category `CostructuredArrow F.op U` has `(V₀, e)` as a terminal object,
by `CategoryTheory.CostructuredArrow.isTerminalMkIso`, so the colimit of
`Stacks.PullbackColimit.diagram` over it is its value there. -/
def indexIso : colimit (diagram F R A U) ≅ diagramObj F R A (CostructuredArrow.mk e.hom) :=
  colimit.isoColimitCocone
    ⟨coconeOfDiagramTerminal (CostructuredArrow.isTerminalMkIso e) (diagram F R A U),
      colimitOfDiagramTerminal (CostructuredArrow.isTerminalMkIso e) (diagram F R A U)⟩

/-- The inverse of the collapse isomorphism is the inclusion of the terminal term into the
colimit. -/
theorem indexIso_inv_apply (x : diagramObj F R A (CostructuredArrow.mk e.hom)) :
    (indexIso F R A e).inv x = colimit.ι (diagram F R A U) (CostructuredArrow.mk e.hom) x :=
  rfl

omit [F.Full] [F.Faithful] in
/-- **The germ at the terminal index is a restriction of the germ at the identity index.**  The
index `(V₀, e)` of the colimit over `U` is the image of the index `(V₀, 𝟙)` of the colimit over
`F(V₀)` under restriction along `e`, so the germs correspond.

Stated for an abstract section `a`, because a germ whose argument is written as a pure tensor is
not type-correct at `implicit` transparency and so cannot be rewritten; see the implementation
notes of `Stacks.PullbackColimit`. -/
theorem germ_eq_obj_map_germ_id (a : A.obj V₀) :
    germ F R A (CostructuredArrow.mk e.hom) 1 a =
      (Stacks.PullbackColimit.obj F R A).map e.hom
        (germ F R A (CostructuredArrow.mk (𝟙 (F.op.obj V₀))) 1 a) := by
  rw [obj_map_germ, map_one]
  exact (germ_congr F R A (Category.id_comp e.hom) 1 a).symm

/-- **Every section of the colimit model over `U` is a single germ at the terminal index.**  The
colimit is its term at `(V₀, e)`, which is a base change along the ring isomorphism `R.map e.hom`,
and a base change along a surjection consists of the elements `1 ⊗ a`. -/
theorem exists_germ_eq (z : ↑(colimit (diagram F R A U))) :
    ∃ a : A.obj V₀, z = germ F R A (CostructuredArrow.mk e.hom) 1 a := by
  obtain ⟨a, ha⟩ := exists_eq_tmul_one (surjective_map_hom R e) ((indexIso F R A e).hom z)
  refine ⟨a, ?_⟩
  have h : (indexIso F R A e).inv ((indexIso F R A e).hom z) = z :=
    ConcreteCategory.congr_hom (indexIso F R A e).hom_inv_id z
  rw [← h, ha, indexIso_inv_apply]
  rfl

end Collapse

/-! ### The sections of the pullback are a base change -/

section BaseChange

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D) [F.Full] [F.Faithful]
  (R : Dᵒᵖ ⥤ CommRingCat.{u}) {S : Cᵒᵖ ⥤ CommRingCat.{u}} {U : Dᵒᵖ} {V₀ : Cᵒᵖ}
  (e : F.op.obj V₀ ≅ U) (α : S ⟶ F.op ⋙ R)
  (N : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))

/-- **The sections of `PresheafOfModules.pullback` over `U` are a base change of the sections.**
For a fully faithful functor of sites `F`, a morphism `α : S ⟶ F.op ⋙ R` of presheaves of
commutative rings and an object `U` isomorphic to `F(V₀)`, the sections of the pullback of `N` over
`U` are `R(U) ⊗_{S(V₀)} N(V₀)`, the base change along the composite `S(V₀) → R(F V₀) → R(U)`.

No hypothesis on `α` or on `N` is needed.  `Stacks.PullbackColimit.pullbackObjIso` identifies the
sections with a colimit of base changes, the colimit collapses to one term because the index
category has a terminal object, and `ModuleCat.extendScalarsComp` composes the two base changes
into one. -/
def pullbackObjIsoBaseChange :
    ((PresheafOfModules.pullback.{u} (toRingCatPullback α)).obj N).obj U ≅
      (ModuleCat.extendScalars ((R.map e.hom).hom.comp (α.app V₀).hom)).obj (N.obj V₀) :=
  Stacks.PullbackColimit.pullbackObjIso α N U ≪≫
    indexIso F R ((extendScalars α).obj N) e ≪≫
      ((ModuleCat.extendScalarsComp (α.app V₀).hom (R.map e.hom).hom).app (N.obj V₀)).symm

/-- **A module with a comparison isomorphism has its sections a base change.**  If the comparison
map `(pullback α).obj N ⟶ Q` out of the pullback is an isomorphism — the defining property of a
crystal, for instance — then the sections of `Q` over `U` are `R(U) ⊗_{S(V₀)} N(V₀)`. -/
def objIsoBaseChangeOfIsIso {Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (c : (PresheafOfModules.pullback.{u} (toRingCatPullback α)).obj N ⟶ Q) [IsIso c] :
    Q.obj U ≅ (ModuleCat.extendScalars ((R.map e.hom).hom.comp (α.app V₀).hom)).obj (N.obj V₀) :=
  ((PresheafOfModules.evaluation.{u} (R ⋙ forget₂ CommRingCat RingCat) U).mapIso
    (asIso c)).symm ≪≫ pullbackObjIsoBaseChange F R e α N

end BaseChange

/-! ### The unit and the comparison map -/

section Transpose

variable {C D : Type u} [SmallCategory C] [SmallCategory D] {F : C ⥤ D}
  {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}} (α : S ⟶ F.op ⋙ R)

/-- The unit of Mathlib's pullback-pushforward adjunction at `N`: the canonical map
`N ⟶ (pushforward α).obj ((pullback α).obj N)`, whose sections are the elements `1 ⊗ n`. -/
abbrev pullbackUnit (N : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) :
    N ⟶ (PresheafOfModules.pushforward.{u} (toRingCatPullback α)).obj
      ((PresheafOfModules.pullback.{u} (toRingCatPullback α)).obj N) :=
  (PresheafOfModules.pullbackPushforwardAdjunction.{u} (toRingCatPullback α)).unit.app N

/-- The comparison map out of the pullback: the adjoint transpose of
`ψ : N ⟶ (pushforward α).obj Q` through Mathlib's pullback-pushforward adjunction. -/
abbrev comparison {N : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}
    {Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (ψ : N ⟶ (PresheafOfModules.pushforward.{u} (toRingCatPullback α)).obj Q) :
    (PresheafOfModules.pullback.{u} (toRingCatPullback α)).obj N ⟶ Q :=
  ((PresheafOfModules.pullbackPushforwardAdjunction.{u} (toRingCatPullback α)).homEquiv N Q).symm ψ

end Transpose

/-! ### Every section of the pullback is a restricted unit section -/

section Unit

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D) [F.Full] [F.Faithful]
  (R : Dᵒᵖ ⥤ CommRingCat.{u}) {S : Cᵒᵖ ⥤ CommRingCat.{u}} {U : Dᵒᵖ} {V₀ : Cᵒᵖ}
  (e : F.op.obj V₀ ≅ U) (α : S ⟶ F.op ⋙ R)
  (N : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))

omit [F.Full] [F.Faithful] in
/-- **The germ at the terminal index is the image of a unit section.**  Under the identification of
the sections of the pullback over `U` with the colimit, the germ of `1 ⊗ (1 ⊗ n)` at `(V₀, e)` is
the restriction along `e` of the unit section at `n`.

The two steps are `Stacks.PullbackColimit.modelAdjunction_unit_app_apply`, which computes the unit
of the concrete model on sections, and
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`, which carries the unit of Mathlib's
adjunction to the unit of the model along the comparison of the two left adjoints. -/
theorem germ_eq_pullbackObjIso_hom (n : N.obj V₀) :
    germ F R ((extendScalars α).obj N) (CostructuredArrow.mk e.hom) 1 (tmul (α.app V₀).hom 1 n) =
      (Stacks.PullbackColimit.pullbackObjIso α N U).hom
        (((PresheafOfModules.pullback.{u} (toRingCatPullback α)).obj N).map e.hom
          (Hom.app (pullbackUnit α N) V₀ n)) := by
  have h2 : Hom.app ((modelAdjunction α).unit.app N) V₀ n =
      germ F R ((extendScalars α).obj N) (CostructuredArrow.mk (𝟙 (F.op.obj V₀))) 1
        (tmul (α.app V₀).hom 1 n) :=
    modelAdjunction_unit_app_apply α N V₀ n
  have h3 : Hom.app ((modelAdjunction α).unit.app N) V₀ n =
      Hom.app ((pullbackIso α).hom.app N) (F.op.obj V₀) (Hom.app (pullbackUnit α N) V₀ n) := by
    rw [← Adjunction.unit_leftAdjointUniq_hom_app
      (PresheafOfModules.pullbackPushforwardAdjunction.{u} (toRingCatPullback α))
      (modelAdjunction α) N]
    rfl
  refine (germ_eq_obj_map_germ_id F R ((extendScalars α).obj N) e _).trans ?_
  refine Eq.trans (congrArg
    (fun x => (Stacks.PullbackColimit.obj F R ((extendScalars α).obj N)).map e.hom x)
    (h2.symm.trans h3)) ?_
  exact (naturality_apply ((pullbackIso α).hom.app N) e.hom
    (Hom.app (pullbackUnit α N) V₀ n)).symm

/-- **Every section of the pullback over `U` is the restriction along `e` of a unit section.**
When the ring map `S(V₀) → R(F V₀)` is surjective and `U` is isomorphic to `F(V₀)`, the sections of
`(pullback α).obj N` over `U` are exactly the elements `(1 ⊗ n)|_U`: no sums and no scalar
multiples are needed, because the colimit is the single base change `R(U) ⊗_{S(V₀)} N(V₀)` and a
base change along a surjection consists of the elements `1 ⊗ n`.

This is the general-functor form of the collapse that
`Stacks.NoncommChangeOfRings.Presheaf.exists_apply_eq_transpose_apply` proves for the identity
functor, and the surjectivity of the ring map is needed for the same reason: the image of a unit is
only an `S(V₀)`-submodule, and it is an `R(U)`-submodule exactly when the scalars of the target are
already scalars of the source. -/
theorem exists_eq_map_unit (hα : Function.Surjective (α.app V₀).hom)
    (t : ((PresheafOfModules.pullback.{u} (toRingCatPullback α)).obj N).obj U) :
    ∃ n : N.obj V₀, t = ((PresheafOfModules.pullback.{u} (toRingCatPullback α)).obj N).map e.hom
      (Hom.app (pullbackUnit α N) V₀ n) := by
  obtain ⟨a, ha⟩ := exists_germ_eq F R ((extendScalars α).obj N) e
    ((Stacks.PullbackColimit.pullbackObjIso α N U).hom t)
  obtain ⟨n, rfl⟩ := exists_eq_tmul_one hα a
  exact ⟨n, injective_isoHom (Stacks.PullbackColimit.pullbackObjIso α N U)
    (ha.trans (germ_eq_pullbackObjIso_hom F R e α N n))⟩

end Unit

/-! ### Surjectivity of the comparison map forces surjectivity of its transpose -/

section Comparison

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D) [F.Full] [F.Faithful]
  (R : Dᵒᵖ ⥤ CommRingCat.{u}) {S : Cᵒᵖ ⥤ CommRingCat.{u}} {U : Dᵒᵖ} {V₀ : Cᵒᵖ}
  (e : F.op.obj V₀ ≅ U) (α : S ⟶ F.op ⋙ R)
  {N : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}
  {Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
  (ψ : N ⟶ (PresheafOfModules.pushforward.{u} (toRingCatPullback α)).obj Q)

omit [F.Full] [F.Faithful] in
/-- **The comparison map, read on the restricted unit sections**: it carries `(1 ⊗ n)|_U` to
`ψ(n)|_U`.  This is the computation rule that Mathlib's abstract left adjoint does not supply, and
both surjectivity statements below are consequences of it together with `exists_eq_map_unit`. -/
theorem comparison_app_map_unit (n : N.obj V₀) :
    Hom.app (comparison α ψ) U
        (((PresheafOfModules.pullback.{u} (toRingCatPullback α)).obj N).map e.hom
          (Hom.app (pullbackUnit α N) V₀ n)) =
      Q.map e.hom (Hom.app ψ V₀ n) := by
  have hψ : ψ = pullbackUnit α N ≫
      (PresheafOfModules.pushforward.{u} (toRingCatPullback α)).map (comparison α ψ) := by
    rw [← Adjunction.homEquiv_unit]
    exact (Equiv.apply_symm_apply _ ψ).symm
  have h2 : Hom.app ψ V₀ n =
      Hom.app (comparison α ψ) (F.op.obj V₀) (Hom.app (pullbackUnit α N) V₀ n) := by
    conv_lhs => rw [hψ]
    rfl
  rw [h2]
  exact naturality_apply (comparison α ψ) e.hom (Hom.app (pullbackUnit α N) V₀ n)

include e in
/-- **A surjective comparison map forces the map it is the transpose of to be surjective.**  If the
functor of sites is fully faithful, `U` is isomorphic to `F(V₀)`, the ring map `S(V₀) → R(F V₀)` is
surjective, and the comparison map `(pullback α).obj N ⟶ Q` is surjective on sections over `U`,
then `ψ` is surjective on sections over `V₀`.

This is the implication "surjectivity of `c_f` gives surjectivity of the `f`-map" of
[Stacks, Tag 07JN], for a functor of sites that need not be the identity — the case the crystalline
comparison map lives in, where the functor is `TopologicalSpace.Opens.map` of the underlying map of
a thickening, which is a homeomorphism. -/
theorem surjective_app_of_surjective_comparison (hα : Function.Surjective (α.app V₀).hom)
    (hc : Function.Surjective (Hom.app (comparison α ψ) U)) :
    Function.Surjective (Hom.app ψ V₀) := by
  intro q
  obtain ⟨t, ht⟩ := hc (Q.map e.hom q)
  obtain ⟨n, rfl⟩ := exists_eq_map_unit F R e α N hα t
  exact ⟨n, (bijective_map_of_iso Q e).1
    ((comparison_app_map_unit F R e α ψ n).symm.trans ht)⟩

omit [F.Full] [F.Faithful] in
include e in
/-- **Conversely, a surjective `ψ` has a surjective comparison map**, and this needs no hypothesis
on the ring map: the comparison map already hits `ψ(n)|_U` for every `n`, and every section of `Q`
over `U` is of that form once `ψ` is surjective over `V₀`, because restriction along the
isomorphism `e` is bijective. -/
theorem surjective_comparison_app_of_surjective_app (hψ : Function.Surjective (Hom.app ψ V₀)) :
    Function.Surjective (Hom.app (comparison α ψ) U) := by
  intro q
  obtain ⟨n, hn⟩ := hψ (Q.map e.inv q)
  refine ⟨((PresheafOfModules.pullback.{u} (toRingCatPullback α)).obj N).map e.hom
    (Hom.app (pullbackUnit α N) V₀ n), ?_⟩
  rw [comparison_app_map_unit F R e α ψ n, hn]
  exact map_hom_map_inv Q e q

end Comparison

/-! ### The case of an equivalence of sites, and of a homeomorphism of spaces -/

section Equivalence

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D) [F.IsEquivalence]

/-- For an equivalence of sites every object of the target is isomorphic to one in the image of the
functor: the isomorphism is the counit, read in the opposite categories. -/
def essImageIso (U : Dᵒᵖ) : F.op.obj (op (F.inv.obj U.unop)) ≅ U :=
  (F.asEquivalence.counitIso.app U.unop).symm.op

variable (R : Dᵒᵖ ⥤ CommRingCat.{u}) {S : Cᵒᵖ ⥤ CommRingCat.{u}} (α : S ⟶ F.op ⋙ R)
  (N : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))

/-- **The sections of a pullback along an equivalence of sites are a base change**, at every object
of the target: the case of `pullbackObjIsoBaseChange` in which `F` is an equivalence, so that `V₀`
may be taken to be `F⁻¹(U)` and `e` the counit. -/
def pullbackObjIsoBaseChangeOfEquivalence (U : Dᵒᵖ) :
    ((PresheafOfModules.pullback.{u} (toRingCatPullback α)).obj N).obj U ≅
      (ModuleCat.extendScalars
        ((R.map (essImageIso F U).hom).hom.comp (α.app (op (F.inv.obj U.unop))).hom)).obj
        (N.obj (op (F.inv.obj U.unop))) :=
  pullbackObjIsoBaseChange F R (essImageIso F U) α N

end Equivalence

section Topology

variable {X Y : TopCat.{u}} (H : X ≅ Y) (R : (Opens ↑X)ᵒᵖ ⥤ CommRingCat.{u})
  {S : (Opens ↑Y)ᵒᵖ ⥤ CommRingCat.{u}} (α : S ⟶ (Opens.map H.hom).op ⋙ R)
  (N : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))

/-- `TopologicalSpace.Opens.map` of an isomorphism of topological spaces is an equivalence of the
categories of open sets, by `TopologicalSpace.Opens.mapMapIso`. -/
theorem isEquivalence_opensMap : (Opens.map H.hom).IsEquivalence :=
  (Opens.mapMapIso H).isEquivalence_functor

/-- **Every open of `X` is the preimage of an open of `Y`**, for a homeomorphism `H : X ≅ Y`: the
isomorphism is the counit of `TopologicalSpace.Opens.mapMapIso`, read in the opposite categories.
Stated without reference to `Functor.inv`, so that it needs no `IsEquivalence` instance and can
appear in the statement below. -/
def opensEssImageIso (U : (Opens ↑X)ᵒᵖ) :
    (Opens.map H.hom).op.obj (op ((Opens.map H.inv).obj U.unop)) ≅ U :=
  ((Opens.mapMapIso H).counitIso.app U.unop).symm.op

/-- **The sections of a pullback along `TopologicalSpace.Opens.map` of a homeomorphism are a base
change**: over an open `W` of `X` they are `R(W) ⊗_{S(H⁻¹ W)} N(H⁻¹ W)`.

This is the form the crystalline comparison map of [Stacks, Tag 07JN] wants: the map of ambient
schemes there is a closed immersion of thickenings, whose underlying continuous map is a
homeomorphism, so that the functor of sites is an equivalence and not merely a continuous
functor. -/
def opensPullbackObjIsoBaseChange (U : (Opens ↑X)ᵒᵖ) :
    ((PresheafOfModules.pullback.{u} (toRingCatPullback α)).obj N).obj U ≅
      (ModuleCat.extendScalars
        ((R.map (opensEssImageIso H U).hom).hom.comp
          (α.app (op ((Opens.map H.inv).obj U.unop))).hom)).obj
        (N.obj (op ((Opens.map H.inv).obj U.unop))) :=
  letI : (Opens.map H.hom).IsEquivalence := isEquivalence_opensMap H
  pullbackObjIsoBaseChange (Opens.map H.hom) R (opensEssImageIso H U) α N

end Topology

end Stacks.PullbackEquivalence

end
