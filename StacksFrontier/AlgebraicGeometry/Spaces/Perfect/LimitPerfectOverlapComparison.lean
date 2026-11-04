module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectObjectsPerfectTarget

/-!
# The comparison isomorphism over the intersection, for the square step of Stacks 09RJ

In Situation 09RH — a directed inverse system `i ↦ X_i` of quasi-compact quasi-separated
algebraic spaces over a scheme `S` with affine transition morphisms, a chosen limit `X` and a
chosen index `0` — the essential surjectivity half of Stacks 09RJ is proved by the induction
principle of Stacks 08GP, and its elementary-distinguished-square step glues with Stacks 08HB.
Stacks 08HB asks for a **comparison isomorphism over the intersection** `P = U ×_W V`: the two
objects descended over `U` and over `V` must have isomorphic restrictions to `P`, and in the
source that isomorphism is produced by **full faithfulness**, Stacks 09RI, after advancing the
two stages carrying the descended objects to a common one.

This file proves that production step.  It is stated for Situation 09RH *at the intersection*:
read `D` below as the base change of Situation 09RH along `P ⟶ X_0`, so that the limit of `D` is
`P`, the stages of `D` are the `P_i`, and the two objects `E₀` and `K₀` of `D(𝒪_{P_0})` are the
two restrictions to the intersection of the objects descended over `U` and over `V`, advanced to
the common stage that is the chosen index of `D`.  The conclusion is the source's `c`: a stage
`k` and an isomorphism of the two objects *at that stage*, whose image in `D(𝒪_P)` is the
prescribed one.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.exists_stageIso_of_isHomColimit`: **an isomorphism
  over the limit descends to an isomorphism at a finite stage.**  If the hom-sets of `D(𝒪_X)`
  between the objects coming from the system are the filtered colimits of the hom-sets at the
  stages — which is the conclusion of Stacks 09RI,
  `AlgebraicGeometry.Space.DescentSituation.IsHomColimit` — then every isomorphism
  `Lf_0^*E₀ ≅ Lf_0^*K₀` is the image of an isomorphism `Lf_{k0}^*E₀ ≅ Lf_{k0}^*K₀` at some stage
  `k ≥ 0`.
* `AlgebraicGeometry.Space.DescentSituation.exists_stageIso_of_homProjection_eq`: the step of
  that argument which turns a morphism and a candidate inverse found at one stage into mutually
  inverse morphisms at a later stage.
* `AlgebraicGeometry.Space.DescentSituation.exists_stageIso_of_limitIso`: the same with the
  isomorphism presented as a pair of isomorphisms `Lf_0^*E₀ ≅ E` and `Lf_0^*K₀ ≅ E` with a
  common target, which is the form the square step has it in: `E` is the restriction to the
  intersection of the perfect object being descended, and the two isomorphisms are the ones
  recording that the objects over `U` and over `V` descend it.
* `AlgebraicGeometry.Space.DescentSituation.exists_stageIso_of_isPerfect`: **the comparison
  isomorphism `c`**, with the four hom-colimit hypotheses discharged from Stacks 09RI for
  perfect objects.
* `AlgebraicGeometry.Space.DescentSituation.exists_stageIso_of_isPerfect_of_le`: the same after
  **advancing two stages to a common one**: two stages `i` and `j` of the situation are given and
  the conclusion is at a stage beyond both.
* The bookkeeping that makes the descent work: the two maps of Stacks 09RI,
  `AlgebraicGeometry.Space.DescentSituation.homProjection` to the limit and
  `…homTransition` between stages, are **compatible with composition and with identities**
  (`…homProjection_comp`, `…homProjection_id`, `…homTransition_comp`, `…homTransition_id`).
  They are not functors — their source and target hom-sets depend on a *pair* of objects of
  `D(𝒪_{X₀})` — so these four identities are what replaces functoriality, and without them an
  inverse cannot be recognised at a stage.
* `CategoryTheory.Functor.conjugate_map_id` and `CategoryTheory.Functor.conjugate_map_comp`: the
  purely formal content of those four identities — conjugating `F.map` by isomorphisms at the
  source and at the target preserves identities and composition.

## The hypotheses carried, and why each is an input rather than part of the conclusion

*The `DerivedPullbackSystem` `sys`.*  This is the standing data of Stacks 09RI in this library:
the derived pullback functors along the maps of Situation 09RH together with the two canonical
comparisons of the factorisations `f_{ji} ∘ f_{i0} = f_{j0}` and `f_i ∘ f_{i0} = f_0`.  Every
statement of `StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHom.lean` carries it and
nothing is added to it here; in particular no coherence is assumed of its two comparisons, see
"Implementation notes".

*The derived tensor product `T` and the ring-level dictionaries.*  These are the hypotheses of
the library's Stacks 09RI for perfect objects,
`AlgebraicGeometry.Space.DescentSituation.isHomColimit_of_isPerfect`, passed through unchanged.
`T` is a `Stacks.SheafOfModules.DerivedTensorProduct` on the small étale ringed site of the
chosen stage; a dictionary is an `AlgebraicGeometry.Space.DescentSituation.RingModel`, the
affine ring-translation data that the proof of Stacks 09RI consumes, and "The carried
hypothesis" in the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHom.lean` says why it is an input of
the source's proof of Stacks 09RI rather than part of its conclusion.  When it is
discharged, every statement below loses `T`, the rings and the
dictionaries at once, because each of them enters only through
`…DescentSituation.isHomColimit_of_isPerfect`.

*There are **four** dictionaries, not one.*  Recognising an isomorphism at a stage needs full
faithfulness for four pairs of objects: `(E₀, K₀)` to descend the isomorphism, `(K₀, E₀)` to
descend its inverse, and `(E₀, E₀)` and `(K₀, K₀)` to see the two composites become identities
at a later stage.  Stacks 09RI is a statement about one *ordered pair* of objects and carries one
dictionary per pair, so four instances of it carry four.  Each dictionary is allowed its own ring
and its own derived-category universe: nothing forces them to agree and nothing below makes them
agree.  The dictionary-free form of the same argument is
`…exists_stageIso_of_isHomColimit`, which assumes only four instances of the *conclusion* of
Stacks 09RI and so carries no dictionary at all.

Nothing else is assumed.  In particular the comparison isomorphism being produced is nowhere
assumed, no `Prop` binder stands in for missing mathematics, and no clause of Stacks 09RJ, of
Stacks 09RI or of Stacks 08HB is assumed.

## What is not here

*The identification of the restriction of a derived pullback with the derived pullback of a
restriction.*  To read the two objects of `D(𝒪_{P_0})` below as the restrictions to the
intersection of objects over `U_0` and over `V_0`, and to read `E` as the restriction to `P` of
the perfect object being descended, one needs the compatibility of the composition comparison of
the derived-pullback pseudofunctor with
`AlgebraicGeometry.Space.edsDerivedRestrictCompOpen` and `…edsDerivedRestrictCompEtale`.  That
is recorded as missing in "What is not here" of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/MayerVietorisGluePerfect.lean` and it is not
supplied or assumed below: every statement here is about one descent situation and the objects of
the derived category of its chosen stage, with no elementary distinguished square mentioned.

*The base change of Situation 09RH along `P ⟶ X_0`.*  That is
`AlgebraicGeometry.Space.DescentSituation.baseChangeAlong` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/DescentSituationBaseChangeSpace.lean`; the
statements below take the situation at the intersection as given, as every statement of
Stacks 09RI does.

## Implementation notes

The two comparisons of an `AlgebraicGeometry.Space.DescentSituation.DerivedPullbackSystem` carry
no coherence axiom, so `AlgebraicGeometry.Space.DescentSituation.homTransition` is *not* known to
be functorial in the index: the composite of the transitions `k ≤ l` and `l ≤ n` need not be the
transition `k ≤ n`.  The argument below is therefore arranged never to compose two transitions
and compare the result with a single one.  It finds the morphism and its candidate inverse at a
common stage `k`, makes the first composite an identity at a stage `l ≥ k`, makes the *second*
composite an identity at a stage `m ≥ l` — reading the two images at `l` off the cocone identity
`Stacks.IsStagesColimit.ι_trans`, which needs no functoriality — and transports the first
identity from `l` to `m` by applying one transition map to it.

`CategoryTheory.Functor.conjugate_map_id` and `…conjugate_map_comp` are stated for an arbitrary
functor because on these concrete categories of modules the category instances that
`CategoryTheory.Functor.map_id` and `…map_comp` would need do not unify syntactically with the
ones the statements elaborate to, so neither `rw` nor `simp` reaches them in place; the same
obstruction, and the same remedy, is recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Perfect/LimitPerfectCategoryColimit.lean`, whose
`AlgebraicGeometry.DescentSituation.conj_id` and `…conj_comp` are the scheme-level counterparts
of these two and would be the ones to unify with if this file and that one ever share an import.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Lemma 75.9.3 (Tag 08GP)](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Lemma 75.10.8 (Tag 08HB)](https://stacks.math.columbia.edu/tag/08HB)
* [Stacks Project, Definition 36.11.1 (Tag 0F8I)](https://stacks.math.columbia.edu/tag/0F8I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w₁ w₂ w₃ w₄ v u

namespace CategoryTheory.Functor

variable {C E : Type*} [Category C] [Category E]

/-- **Conjugating `F.map` by isomorphisms preserves identities.**  For a functor `F` and an
isomorphism `e : F.obj X ≅ Y`, the morphism `e⁻¹ ∘ F(𝟙_X) ∘ e` is the identity of `Y`. -/
theorem conjugate_map_id (F : C ⥤ E) {X : C} {Y : E} (e : F.obj X ≅ Y) :
    e.inv ≫ F.map (𝟙 X) ≫ e.hom = 𝟙 Y := by
  rw [F.map_id, Category.id_comp, e.inv_hom_id]

/-- **Conjugating `F.map` by isomorphisms preserves composition.**  For a functor `F` and
isomorphisms `eX : F.obj X ≅ X'`, `eY : F.obj Y ≅ Y'` and `eZ : F.obj Z ≅ Z'`, the conjugate of
`F(g ∘ f)` is the composite of the conjugate of `F f` with the conjugate of `F g`; the two copies
of `eY` that appear in the middle cancel. -/
theorem conjugate_map_comp (F : C ⥤ E) {X Y Z : C} {X' Y' Z' : E} (eX : F.obj X ≅ X')
    (eY : F.obj Y ≅ Y') (eZ : F.obj Z ≅ Z') (f : X ⟶ Y) (g : Y ⟶ Z) :
    eX.inv ≫ F.map (f ≫ g) ≫ eZ.hom =
      (eX.inv ≫ F.map f ≫ eY.hom) ≫ eY.inv ≫ F.map g ≫ eZ.hom := by
  rw [F.map_comp]
  simp

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  [∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y), (modulePullback B S hS f).Additive]
  {D : DescentSituation B S hS hZ I} (sys : D.DerivedPullbackSystem)
  (E₀ K₀ G₀ : DerivedCategory
    (Modules.{u, u} B S hS (D.stage D.base).obj (D.stage D.base).property))

/-! ### The two maps of Stacks 09RI respect composition and identities -/

/-- **The map to the limit of Stacks 09RI sends an identity to an identity.**  That map is
`Lf_i^*` conjugated by the comparison `Lf_i^*Lf_{i0}^* ≅ Lf_0^*` at the source and at the
target, so it preserves identities. -/
theorem homProjection_id (i : D.Stages) :
    homProjection sys E₀ E₀ i (𝟙 _) = 𝟙 _ :=
  (sys.projPullback i).functor.conjugate_map_id ((sys.projComp i).app E₀)

/-- **The map to the limit of Stacks 09RI respects composition.**  The two copies of the
comparison `Lf_i^*Lf_{i0}^* ≅ Lf_0^*` at the middle object `K₀` cancel, so composing at a stage
and then mapping to the limit agrees with mapping each factor to the limit and composing
there. -/
theorem homProjection_comp (i : D.Stages) (g : stageObj sys E₀ i ⟶ stageObj sys K₀ i)
    (g' : stageObj sys K₀ i ⟶ stageObj sys G₀ i) :
    homProjection sys E₀ G₀ i (g ≫ g') =
      homProjection sys E₀ K₀ i g ≫ homProjection sys K₀ G₀ i g' :=
  (sys.projPullback i).functor.conjugate_map_comp ((sys.projComp i).app E₀)
    ((sys.projComp i).app K₀) ((sys.projComp i).app G₀) g g'

/-- **The transition map of Stacks 09RI sends an identity to an identity.** -/
theorem homTransition_id (i j : D.Stages) (h : i ≤ j) :
    homTransition sys E₀ E₀ i j h (𝟙 _) = 𝟙 _ :=
  (sys.transPullback i j h).functor.conjugate_map_id ((sys.transComp i j h).app E₀)

/-- **The transition map of Stacks 09RI respects composition.** -/
theorem homTransition_comp (i j : D.Stages) (h : i ≤ j)
    (g : stageObj sys E₀ i ⟶ stageObj sys K₀ i)
    (g' : stageObj sys K₀ i ⟶ stageObj sys G₀ i) :
    homTransition sys E₀ G₀ i j h (g ≫ g') =
      homTransition sys E₀ K₀ i j h g ≫ homTransition sys K₀ G₀ i j h g' :=
  (sys.transPullback i j h).functor.conjugate_map_comp ((sys.transComp i j h).app E₀)
    ((sys.transComp i j h).app K₀) ((sys.transComp i j h).app G₀) g g'

/-- **Transition maps carry a pair of mutually inverse morphisms to such a pair.** -/
private theorem homTransition_comp_eq_id (i j : D.Stages) (h : i ≤ j)
    {f : stageObj sys E₀ i ⟶ stageObj sys K₀ i} {g : stageObj sys K₀ i ⟶ stageObj sys E₀ i}
    (hfg : f ≫ g = 𝟙 _) :
    homTransition sys E₀ K₀ i j h f ≫ homTransition sys K₀ E₀ i j h g = 𝟙 _ := by
  rw [← homTransition_comp, hfg, homTransition_id]

/-! ### Descending an isomorphism to a finite stage -/

/-- **A morphism at a stage whose image at the limit is invertible, presented with a candidate
inverse at the same stage, becomes invertible at a later stage.**  Let `a : E_k ⟶ K_k` and
`b : K_k ⟶ E_k` be morphisms at a stage `k` whose images in `D(𝒪_X)` are `e` and `e⁻¹`.  Then `a`
and `b` become mutually inverse at some stage `m ≥ k`, and the resulting isomorphism still has
image `e`.

Both composites `b ∘ a` and `a ∘ b` have identity image at the limit, so faithfulness for the
pairs `(E₀, E₀)` and `(K₀, K₀)` makes each of them an identity at a late enough stage.  The two
stages this produces are unrelated, and the transition maps are not known to be functorial in the
index, so the second application is made at the stage the first one produced and the first
identity is carried forward to the second stage by a single transition map. -/
theorem exists_stageIso_of_homProjection_eq
    (hEK : IsHomColimit sys E₀ K₀) (hKE : IsHomColimit sys K₀ E₀)
    (hEE : IsHomColimit sys E₀ E₀) (hKK : IsHomColimit sys K₀ K₀)
    (e : limitObj sys E₀ ≅ limitObj sys K₀) (k : D.Stages)
    (a : stageObj sys E₀ k ⟶ stageObj sys K₀ k)
    (b : stageObj sys K₀ k ⟶ stageObj sys E₀ k)
    (ha : homProjection sys E₀ K₀ k a = e.hom)
    (hb : homProjection sys K₀ E₀ k b = e.inv) :
    ∃ (m : D.Stages) (c : stageObj sys E₀ m ≅ stageObj sys K₀ m),
      homProjection sys E₀ K₀ m c.hom = e.hom := by
  obtain ⟨l, hkl, hl⟩ := Stacks.IsStagesColimit.exists_trans_eq hEE k (a ≫ b) (𝟙 _) (by
    rw [homProjection_comp, homProjection_id, ha, hb, e.hom_inv_id])
  rw [homTransition_comp, homTransition_id] at hl
  obtain ⟨m, hlm, hm⟩ := Stacks.IsStagesColimit.exists_trans_eq hKK l
    (homTransition sys K₀ E₀ k l hkl b ≫ homTransition sys E₀ K₀ k l hkl a) (𝟙 _) (by
      rw [homProjection_comp, homProjection_id,
        Stacks.IsStagesColimit.ι_trans hKE k l hkl b, hb,
        Stacks.IsStagesColimit.ι_trans hEK k l hkl a, ha, e.inv_hom_id])
  rw [homTransition_comp, homTransition_id] at hm
  refine ⟨m, ⟨_, _, homTransition_comp_eq_id sys E₀ K₀ l m hlm hl, hm⟩, ?_⟩
  rw [Stacks.IsStagesColimit.ι_trans hEK l m hlm _,
    Stacks.IsStagesColimit.ι_trans hEK k l hkl a, ha]

/-- **An isomorphism over the limit descends to an isomorphism at a finite stage.**  In
Situation 09RH, let `E₀` and `K₀` be objects of `D(𝒪_{X₀})` whose systems of homomorphism groups
have the colimit property of Stacks 09RI in the four orders `(E₀, K₀)`, `(K₀, E₀)`, `(E₀, E₀)`
and `(K₀, K₀)`.  Then every isomorphism `e : Lf_0^*E₀ ≅ Lf_0^*K₀` of `D(𝒪_X)` is the image,
under the map of Stacks 09RI, of an isomorphism `Lf_{k0}^*E₀ ≅ Lf_{k0}^*K₀` at some stage
`k ≥ 0`.

This is the production of the source's comparison isomorphism `c` for the
elementary-distinguished-square step of Stacks 09RJ, read at the intersection: fullness delivers
`e` and `e⁻¹` at two stages, which are advanced to a common one before
`AlgebraicGeometry.Space.DescentSituation.exists_stageIso_of_homProjection_eq` makes them
mutually inverse. -/
theorem exists_stageIso_of_isHomColimit
    (hEK : IsHomColimit sys E₀ K₀) (hKE : IsHomColimit sys K₀ E₀)
    (hEE : IsHomColimit sys E₀ E₀) (hKK : IsHomColimit sys K₀ K₀)
    (e : limitObj sys E₀ ≅ limitObj sys K₀) :
    ∃ (k : D.Stages) (c : stageObj sys E₀ k ≅ stageObj sys K₀ k),
      homProjection sys E₀ K₀ k c.hom = e.hom := by
  obtain ⟨i, g, hg⟩ := Stacks.IsStagesColimit.exists_stage hEK e.hom
  obtain ⟨j, g', hg'⟩ := Stacks.IsStagesColimit.exists_stage hKE e.inv
  obtain ⟨k, hik, hjk⟩ := (isDirectedStages (D := D)).directed i j
  exact exists_stageIso_of_homProjection_eq sys E₀ K₀ hEK hKE hEE hKK e k
    (homTransition sys E₀ K₀ i k hik g) (homTransition sys K₀ E₀ j k hjk g')
    (by rw [Stacks.IsStagesColimit.ι_trans hEK i k hik g, hg])
    (by rw [Stacks.IsStagesColimit.ι_trans hKE j k hjk g', hg'])

/-- **The comparison isomorphism over the intersection, from two isomorphisms with a common
target.**  Let `E₀` and `K₀` be objects of `D(𝒪_{X₀})` satisfying the colimit property of
Stacks 09RI in the four orders, and let `α : Lf_0^*E₀ ≅ E` and `β : Lf_0^*K₀ ≅ E` be
isomorphisms with a common object `E` of `D(𝒪_X)`.  Then at some stage `k ≥ 0` there is an
isomorphism `Lf_{k0}^*E₀ ≅ Lf_{k0}^*K₀` whose image in `D(𝒪_X)` is `β⁻¹ ∘ α`.

This is the shape the elementary-distinguished-square step has its data in.  Reading `D` as
Situation 09RH base changed along the intersection `P ⟶ X_0`: `E` is the restriction to `P` of
the perfect object being descended, `α` and `β` record that the two objects descended over `U`
and over `V` restrict to it, and the conclusion is the comparison isomorphism `c` that
Stacks 08HB asks for, with the compatibility over `P` that makes the glued object compare with
the given one. -/
theorem exists_stageIso_of_limitIso
    (hEK : IsHomColimit sys E₀ K₀) (hKE : IsHomColimit sys K₀ E₀)
    (hEE : IsHomColimit sys E₀ E₀) (hKK : IsHomColimit sys K₀ K₀)
    (E : DerivedCategory
      (Modules.{u, u} B S hS D.limitSpace.obj D.limitSpace.property))
    (α : limitObj sys E₀ ≅ E) (β : limitObj sys K₀ ≅ E) :
    ∃ (k : D.Stages) (c : stageObj sys E₀ k ≅ stageObj sys K₀ k),
      homProjection sys E₀ K₀ k c.hom = α.hom ≫ β.inv :=
  exists_stageIso_of_isHomColimit sys E₀ K₀ hEK hKE hEE hKK (α ≪≫ β.symm)

/-! ### The comparison isomorphism for perfect objects -/

section Perfect

variable
  [∀ U : (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).C,
    HasSheafify ((smallEtaleRingedSite B S hS (D.stage D.base).obj
      (D.stage D.base).property).J.over U) AddCommGrpCat.{u}]
  [∀ U : (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).C,
    ((smallEtaleRingedSite B S hS (D.stage D.base).obj
      (D.stage D.base).property).J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).C,
    ((smallEtaleRingedSite B S hS (D.stage D.base).obj
      (D.stage D.base).property).J.over U).HasSheafCompose
        (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS (D.stage D.base).obj
      (D.stage D.base).property).O).obj M).Additive]
  [∀ (M N : CochainComplex
      (Modules.{u, u} B S hS (D.stage D.base).obj (D.stage D.base).property) ℤ),
    HomologicalComplex.HasMapBifunctor M N
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property).O)
      (ComplexShape.up ℤ)]
  (A₀ Bo₀ : PerfectDerivedCategory B S hS (D.stage D.base))
  (T : Stacks.SheafOfModules.DerivedTensorProduct
    (smallEtaleRingedSite B S hS (D.stage D.base).obj (D.stage D.base).property))
  (R₁ : Type u) [Ring R₁] [HasDerivedCategory.{w₁} (ModuleCat.{u} R₁)]
  (R₂ : Type u) [Ring R₂] [HasDerivedCategory.{w₂} (ModuleCat.{u} R₂)]
  (R₃ : Type u) [Ring R₃] [HasDerivedCategory.{w₃} (ModuleCat.{u} R₃)]
  (R₄ : Type u) [Ring R₄] [HasDerivedCategory.{w₄} (ModuleCat.{u} R₄)]

-- The derived tensor product is an input of Stacks 09RI and is used in the proofs below, but
-- does not appear in either statement, so it has to be included by hand.
include T

/-- **The comparison isomorphism `c` over the intersection, for the square step of
Stacks 09RJ.**  In Situation 09RH, let `A₀` and `Bo₀` be perfect objects of `D(𝒪_{X₀})` and let
`α : Lf_0^*A₀ ≅ E` and `β : Lf_0^*Bo₀ ≅ E` be isomorphisms with a common object `E` of
`D(𝒪_X)`.  Then there are a stage `k ≥ 0` and an isomorphism
`c : Lf_{k0}^*A₀ ≅ Lf_{k0}^*Bo₀` of `D(𝒪_{X_k})` whose image in `D(𝒪_X)` under the map of
Stacks 09RI is `β⁻¹ ∘ α`.

Read `D` as Situation 09RH base changed along the intersection `P = U ×_W V` of an elementary
distinguished square over `X_0`,
`AlgebraicGeometry.Space.DescentSituation.baseChangeAlong`: this is the comparison isomorphism
that the elementary-distinguished-square step of the essential surjectivity half of Stacks 09RJ
feeds to Stacks 08HB as the hypothesis `c` of
`AlgebraicGeometry.Space.exists_glued_isPerfect_object_and_hom`, together with the compatibility
over `P` that the same step needs in order to recognise the glued comparison as an isomorphism.

The hypotheses `T`, `R₁`-`R₄` and the four dictionaries are the hypotheses of the library's
Stacks 09RI for perfect objects,
`AlgebraicGeometry.Space.DescentSituation.isHomColimit_of_isPerfect`, one instance of it per
ordered pair of objects; see "The hypotheses carried, and why each is an input rather than part
of the conclusion" in this file's module documentation.  Nothing else is assumed, and in
particular the isomorphism being produced is not. -/
theorem exists_stageIso_of_isPerfect
    (mAB : RingModel sys A₀.obj Bo₀.obj R₁) (mBA : RingModel sys Bo₀.obj A₀.obj R₂)
    (mAA : RingModel sys A₀.obj A₀.obj R₃) (mBB : RingModel sys Bo₀.obj Bo₀.obj R₄)
    (E : DerivedCategory
      (Modules.{u, u} B S hS D.limitSpace.obj D.limitSpace.property))
    (α : limitObj sys A₀.obj ≅ E) (β : limitObj sys Bo₀.obj ≅ E) :
    ∃ (k : D.Stages) (c : stageObj sys A₀.obj k ≅ stageObj sys Bo₀.obj k),
      homProjection sys A₀.obj Bo₀.obj k c.hom = α.hom ≫ β.inv :=
  exists_stageIso_of_limitIso sys A₀.obj Bo₀.obj
    (isHomColimit_of_isPerfect sys A₀ Bo₀ T R₁ mAB)
    (isHomColimit_of_isPerfect sys Bo₀ A₀ T R₂ mBA)
    (isHomColimit_of_isPerfect sys A₀ A₀ T R₃ mAA)
    (isHomColimit_of_isPerfect sys Bo₀ Bo₀ T R₄ mBB) E α β

/-- **The comparison isomorphism over the intersection, at a stage beyond two prescribed
ones.**  Two stages `i` and `j` of Situation 09RH are given, and the conclusion is at a stage `k`
beyond both of them: the directedness of the stages produces a stage beyond `i` and `j`, and the
isomorphism produced by `AlgebraicGeometry.Space.DescentSituation.exists_stageIso_of_isPerfect`
is carried to a stage beyond that one by a transition map, which preserves its invertibility and
its image at the limit.

This is the form the elementary-distinguished-square step of Stacks 09RJ needs, its two
descended objects having been found at two unrelated stages: it is the source's "after
increasing `i` we may assume `i = j`". -/
theorem exists_stageIso_of_isPerfect_of_le (i j : D.Stages)
    (mAB : RingModel sys A₀.obj Bo₀.obj R₁) (mBA : RingModel sys Bo₀.obj A₀.obj R₂)
    (mAA : RingModel sys A₀.obj A₀.obj R₃) (mBB : RingModel sys Bo₀.obj Bo₀.obj R₄)
    (E : DerivedCategory
      (Modules.{u, u} B S hS D.limitSpace.obj D.limitSpace.property))
    (α : limitObj sys A₀.obj ≅ E) (β : limitObj sys Bo₀.obj ≅ E) :
    ∃ (k : D.Stages) (_ : i ≤ k) (_ : j ≤ k)
      (c : stageObj sys A₀.obj k ≅ stageObj sys Bo₀.obj k),
      homProjection sys A₀.obj Bo₀.obj k c.hom = α.hom ≫ β.inv := by
  obtain ⟨k, hik, hjk⟩ := (isDirectedStages (D := D)).directed i j
  obtain ⟨m, c, hc⟩ := exists_stageIso_of_isPerfect sys A₀ Bo₀ T R₁ R₂ R₃ R₄ mAB mBA mAA mBB E α β
  obtain ⟨n, hkn, hmn⟩ := (isDirectedStages (D := D)).directed k m
  refine ⟨n, hik.trans hkn, hjk.trans hkn, ⟨homTransition sys A₀.obj Bo₀.obj m n hmn c.hom,
    homTransition sys Bo₀.obj A₀.obj m n hmn c.inv,
    homTransition_comp_eq_id sys A₀.obj Bo₀.obj m n hmn c.hom_inv_id,
    homTransition_comp_eq_id sys Bo₀.obj A₀.obj m n hmn c.inv_hom_id⟩, ?_⟩
  rw [Stacks.IsStagesColimit.ι_trans
    (isHomColimit_of_isPerfect sys A₀ Bo₀ T R₁ mAB) m n hmn c.hom, hc]

end Perfect

end DescentSituation

end AlgebraicGeometry.Space

end
