module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
public import Mathlib.CategoryTheory.Subobject.HasCardinalLT
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import StacksFrontier.Homology.Injectives.SmallObject
public import StacksFrontier.Homology.Injectives.Module.BaerPushout
public import StacksFrontier.Homology.Injectives.Module.SmallWithRespectToInjections
import StacksCore.Tactic.StacksAttribute

/-!
# The Baer--Grothendieck injective embedding

Let `R` be a commutative ring. The functorial Baer construction `M ↦ BaerM R M` embeds every
module in a module in which every partial homomorphism from an ideal extends. Iterating it
through an ordinal `α` gives a functor `M ↦ M_α` together with a natural monomorphism
`M ⟶ M_α`, built from Mathlib's transfinite iteration of a successor structure, whose colimit
stages at limit ordinals are the ones the construction needs.

If the cofinality of `α` exceeds the number of ideals of `R`, the top stage `M_α` is injective.
The reason is that a homomorphism from an ideal `a` into `M_α` factors through an earlier stage:
the set of subobjects of `ModuleCat.of R a` has cardinality smaller than the cofinality of `α`,
so `a` is `α`-small with respect to the monomorphisms, and the transfinite stages form a
filtered colimit along `α` with monomorphic transition maps. One more Baer step extends the
factored homomorphism to `R`, which is Baer's criterion.

## Main definitions

* `Stacks.Injectives.baerFunctor`: the one-step Baer endofunctor on `R`-modules.
* `Stacks.Injectives.baerEmbedding`: its canonical natural map from the identity functor.
* `Stacks.Injectives.baerSucc`: the successor structure the iteration is taken of.
* `Stacks.Injectives.baerIterateFunctor`: the transfinite iterate `M ↦ M_α`.
* `Stacks.Injectives.baerIterateEmbedding`: the natural map `M ⟶ M_α`.

## Main results

* `Stacks.Injectives.baerIterate_injective_of_cofinality`: the iterate is injective under the
  cofinality bound.
* `Stacks.Injectives.mono_baerIterateEmbedding`: every component of the canonical natural map
  is a monomorphism.

## Implementation notes

The one-step construction and its functoriality are `BaerM`, `baerMMap` and `baerUMap` of
Tag 05NW; `IsSmallWithRespectTo` is the smallness notion of Tag 05NS. Monomorphy of the
transition maps of the iteration is proved by transfinite induction, the limit step using that
a filtered colimit in `ModuleCat R` preserves monomorphisms; the index category of a cofinal
subobject at a limit stage is only essentially small, so it is replaced by its small model
before the exactness of filtered colimits is invoked.

## References

* [Stacks Project, Tag 05NX](https://stacks.math.columbia.edu/tag/05NX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject Opposite MorphismProperty
open scoped Ordinal

universe u

namespace Stacks.Injectives

private theorem ideal_subobject_cardinal_lt (R : Type u) [CommRing R]
    (a : Ideal R) (α : Ordinal.{u}) (hα : Cardinal.mk (Ideal R) < α.cof) :
    HasCardinalLT (Subobject (ModuleCat.of R a)) α.cof := by
  have hinj : Function.Injective (fun S : Subobject (ModuleCat.of R a) =>
      Submodule.map a.subtype ((ModuleCat.subobjectModule (ModuleCat.of R a)) S)) :=
    fun S T h => (ModuleCat.subobjectModule (ModuleCat.of R a)).injective
      (Submodule.map_injective_of_injective Subtype.val_injective h)
  exact ((hasCardinalLT_iff_cardinal_mk_lt _ _).mpr hα).of_injective _ hinj

private theorem ordinal_limit_of_ideal_cofinality (R : Type u) [CommRing R]
    (α : Ordinal.{u}) (hα : Cardinal.mk (Ideal R) < α.cof) :
    Order.IsSuccLimit α :=
  Ordinal.one_lt_cof_iff.mp
    ((Cardinal.one_le_iff_ne_zero.mpr (Cardinal.mk_ne_zero (Ideal R))).trans_lt hα)

private theorem iic_top_isSuccLimit (α : Ordinal.{u}) (hα : Order.IsSuccLimit α) :
    Order.IsSuccLimit (⊤ : Set.Iic α) := by
  have h0 : (0 : Ordinal) < α := hα.bot_lt
  refine ⟨fun hmin => ?_, fun b hb => ?_⟩
  · exact not_lt_of_ge (hmin (show (⟨0, h0.le⟩ : Set.Iic α) ≤ ⊤ by simp)) h0
  · exact hα.isSuccPrelimit b.1 ⟨hb.1, fun c hbc hca => hb.2 (c := ⟨c, hca.le⟩) hbc hca⟩

/-- The one-step Baer construction, as an endofunctor of the category of
`R`-modules. -/
noncomputable def baerFunctor (R : Type u) [CommRing R] :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (BaerM R M)
  map f := ModuleCat.ofHom (baerMMap R f.hom)
  map_id _ := ModuleCat.hom_ext (baerMMap_id R)
  map_comp f g := ModuleCat.hom_ext (baerMMap_comp R f.hom g.hom)

/-- The canonical natural map from a module to its one-step Baer
construction. -/
noncomputable def baerEmbedding (R : Type u) [CommRing R] :
    𝟭 (ModuleCat.{u} R) ⟶ baerFunctor R where
  app M := ModuleCat.ofHom (baerUMap R M)
  naturality _ _ f := by
    ext
    exact LinearMap.congr_fun (baerMMap_natural R f.hom).symm _

/-- The successor structure whose transfinite stages are the iterated Baer
constructions. -/
noncomputable def baerSucc (R : Type u) [CommRing R] :
    SuccStruct (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
  SuccStruct.ofNatTrans (baerEmbedding R)

/-- The category of `R`-modules admits transfinite iterations indexed by `Set.Iic α`. -/
noncomputable instance moduleCatHasIterationOfShape (R : Type u) [CommRing R]
    (α : Ordinal.{u}) : HasIterationOfShape (Set.Iic α) (ModuleCat.{u} R) where

/-- The category of endofunctors of `R`-modules admits transfinite iterations indexed by
`Set.Iic α`. -/
noncomputable instance baerHasIterationOfShape (R : Type u) [CommRing R]
    (α : Ordinal.{u}) :
    HasIterationOfShape (Set.Iic α) (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
  instHasIterationOfShapeFunctor (Set.Iic α) (ModuleCat.{u} R) (ModuleCat.{u} R)

/-- `M_α`, functorially in `M`: the top stage of the transfinite iteration of
the Baer construction through the ordinal `α`. -/
@[stacks 05NX "the functorial transfinite construction"]
noncomputable def baerIterateFunctor (R : Type u) [CommRing R]
    (α : Ordinal.{u}) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  ((baerSucc R).iterationFunctor (Set.Iic α)).obj ⊤

/-- The canonical natural map `M ⟶ M_α`. -/
@[stacks 05NX "the natural map to the iterate"]
noncomputable def baerIterateEmbedding (R : Type u) [CommRing R]
    (α : Ordinal.{u}) : 𝟭 (ModuleCat.{u} R) ⟶ baerIterateFunctor R α :=
  ((baerSucc R).ιIterationFunctor (Set.Iic α)).app ⊤

private theorem baerSucc_toSucc_mono (R : Type u) [CommRing R]
    (G : ModuleCat.{u} R ⥤ ModuleCat.{u} R) : Mono ((baerSucc R).toSucc G) := by
  rw [NatTrans.mono_iff_mono_app]
  intro M
  change Mono ((baerEmbedding R).app (G.obj M))
  rw [ModuleCat.mono_iff_injective]
  change Function.Injective (baerUMap R (G.obj M))
  exact baer_uMap_injective R (G.obj M)

private theorem mono_ι_app_of_iio {R : Type u} [CommRing R] {α : Ordinal.{u}} {j : Set.Iic α}
    [IsFiltered (Set.Iio j)] (D : Set.Iio j ⥤ ModuleCat.{u} R)
    (hmaps : ∀ (k k' : Set.Iio j) (f : k ⟶ k'), Mono (D.map f)) {c : Cocone D}
    (hc : IsColimit c) (j₀ : Set.Iio j) : Mono (c.ι.app j₀) := by
  have : Small.{u} (Under j₀) :=
    small_of_injective (f := (Under.forget j₀).obj) (by
      intro x y hxy
      cases x with
      | mk f xr xh =>
        cases y with
        | mk g yr yh =>
          dsimp [Under.right] at hxy
          cases hxy
          obtain rfl : f = g := Subsingleton.elim _ _
          obtain rfl : xh = yh := Subsingleton.elim _ _
          rfl)
  have : LocallySmall.{u} (Under j₀) := ⟨fun X Y =>
    small_of_injective (f := fun _ : X ⟶ Y => PUnit.unit)
      fun _ _ _ => Under.UnderMorphism.ext (Subsingleton.elim _ _)⟩
  have : EssentiallySmall.{u} (Under j₀) := inferInstance
  let : HasColimitsOfSize.{u, u} (ModuleCat.{u} R) := inferInstance
  let : HasColimitsOfShape (Under j₀) (ModuleCat.{u} R) :=
    hasColimitsOfShape_of_essentiallySmall _ _
  have : IsFiltered (Under j₀) := inferInstance
  let e : Under j₀ ≌ SmallModel (Under j₀) := equivSmallModel.{u} (Under j₀)
  have : IsFiltered (SmallModel (Under j₀)) :=
    IsFiltered.of_equivalence e
  let : HasExactColimitsOfShape (SmallModel (Under j₀))
      (ModuleCat.{u} R) := inferInstance
  let : HasExactColimitsOfShape (Under j₀) (ModuleCat.{u} R) :=
    HasExactColimitsOfShape.of_domain_equivalence _ e.symm
  have : Functor.PreservesMonomorphisms
      (colim (J := Under j₀) (C := ModuleCat.{u} R)) := by
    infer_instance
  exact @IsColimit.mono_ι_app_of_isFiltered
    (ModuleCat.{u} R) inferInstance (Set.Iio j) inferInstance
    D hmaps c hc inferInstance j₀ inferInstance inferInstance

private theorem baerIterationMap_mono (R : Type u) [CommRing R]
    (α : Ordinal.{u}) :
    ∀ (j : Set.Iic α) (i : Set.Iic α) (hij : i ≤ j) (M : ModuleCat.{u} R),
      Mono ((((baerSucc R).iterationFunctor (Set.Iic α)).map (homOfLE hij)).app M) := by
  let F := (baerSucc R).iterationFunctor (Set.Iic α)
  have hid : ∀ j M, Mono ((F.map (𝟙 j)).app M) := fun j M => by
    simpa using (inferInstance : Mono (𝟙 ((F.obj j).obj M)))
  intro j
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
      intro i hij M
      obtain rfl := le_antisymm hij (hj hij)
      exact hid _ M
  | succ j hj ih =>
      intro i hij M
      by_cases hi : i ≤ j
      · have hmono₁ : Mono ((F.map (homOfLE hi)).app M) := ih i hi M
        have hmono₂ : Mono (F.map (homOfLE (Order.le_succ j))) := by
          have : Mono ((baerSucc R).toSucc (F.obj j)) := baerSucc_toSucc_mono R _
          rw [((baerSucc R).prop_iterationFunctor_map_succ j hj).fac]
          infer_instance
        have hcomp : F.map (homOfLE hij) =
            F.map (homOfLE hi) ≫ F.map (homOfLE (Order.le_succ j)) := by
          rw [← F.map_comp, homOfLE_comp]
        rw [hcomp, NatTrans.comp_app]
        infer_instance
      · obtain rfl := le_antisymm hij ((Order.succ_le_iff_of_not_isMax hj).2 (lt_of_not_ge hi))
        exact hid _ M
  | isSuccLimit j hj ih =>
      intro i hij M
      by_cases hEq : i = j
      · subst i
        exact hid _ M
      · have hij' : i < j := lt_of_le_of_ne hij hEq
        let E := (evaluation (ModuleCat.{u} R) (ModuleCat.{u} R)).obj M
        have : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
        have hmaps : ∀ (k k' : Set.Iio j) (f : k ⟶ k'),
            Mono (((Set.principalSegIio j).monotone.functor ⋙ F ⋙ E).map f) := by
          intro k k' f
          have hkk' : k.1 ≤ k'.1 := leOfHom f
          change Mono (((F.map (homOfLE hkk')).app M))
          exact ih k'.1 k'.2 k.1 hkk' M
        have hm := mono_ι_app_of_iio ((Set.principalSegIio j).monotone.functor ⋙ F ⋙ E) hmaps
          (isColimitOfPreserves E (F.isColimitOfIsWellOrderContinuous j hj)) ⟨i, hij'⟩
        change Mono ((F.map (homOfLE (le_of_lt hij'))).app M) at hm
        simpa [E] using hm

private def iioTopOrderIso (α : Ordinal.{u}) :
    Set.Iio (⊤ : Set.Iic α) ≃o Set.Iio α where
  toFun i := ⟨i.1.1, i.2⟩
  invFun i := ⟨⟨i.1, Set.mem_Iic.mpr i.2.le⟩, i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

private noncomputable def ordinalToIioTop (α : Ordinal.{u}) :
    α.ToType ≃o Set.Iio (⊤ : Set.Iic α) :=
  Ordinal.ToType.mk.symm.trans (iioTopOrderIso α).symm

/-- If the cofinality of `α` is larger than the cardinality of the set of ideals of `R`, then
every homomorphism from an ideal of `R` to `M_α` factors through an earlier stage of the
transfinite Baer iteration. -/
private theorem baerIterate_factor_through_stage
    (R : Type u) [CommRing R] (α : Ordinal.{u})
    (hα : Cardinal.mk (Ideal R) < α.cof) (M : ModuleCat.{u} R) (a : Ideal R)
    (f : ModuleCat.of R a ⟶ (baerIterateFunctor R α).obj M) :
    ∃ (i : α.ToType)
      (g : ModuleCat.of R a ⟶
        (((baerSucc R).iterationFunctor (Set.Iic α)).obj
          ((Set.principalSegIio (⊤ : Set.Iic α)).monotone.functor.obj
            (ordinalToIioTop α i))).obj M),
      g ≫ (((baerSucc R).iterationFunctor (Set.Iic α)).map
        (homOfLE (show ((Set.principalSegIio (⊤ : Set.Iic α)).monotone.functor.obj
          (ordinalToIioTop α i)) ≤ ⊤
          from le_top))).app M = f := by
  have hαlim : Order.IsSuccLimit α := ordinal_limit_of_ideal_cofinality R α hα
  let : Fact α.cof.IsRegular := ⟨Cardinal.isRegular_cof hαlim⟩
  let : IsCardinalFiltered α.ToType α.cof := Ordinal.isCardinalFiltered_toType_cof α
  let F := (baerSucc R).iterationFunctor (Set.Iic α)
  let S := (Set.principalSegIio (⊤ : Set.Iic α)).monotone.functor
  let E := (evaluation (ModuleCat.{u} R) (ModuleCat.{u} R)).obj M
  let eOrder := ordinalToIioTop α
  let e := eOrder.equivalence
  let D := (e.functor ⋙ (S ⋙ F)) ⋙ E
  change ModuleCat.of R a ⟶ (F.obj ⊤).obj M at f
  let H := coyoneda.obj (Opposite.op (ModuleCat.of R a))
  have hsmall : IsSmallWithRespectTo (ModuleCat.of R a)
      (MorphismProperty.monomorphisms (ModuleCat.{u} R)) α := fun B _ =>
    IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono B
      (ideal_subobject_cardinal_lt R a α hα)
  have hmaps : ∀ (i j : α.ToType) (f : i ⟶ j), Mono (D.map f) := by
    intro i j f
    change Mono ((F.map (S.map (homOfLE (eOrder.monotone (leOfHom f))))).app M)
    exact baerIterationMap_mono R α (S.obj (eOrder j)) (S.obj (eOrder i))
      (eOrder.monotone (leOfHom f)) M
  let cBase := (Set.principalSegIio (⊤ : Set.Iic α)).cocone F
  let cD := (E.mapCocone cBase).whisker e.functor
  have hcD : IsColimit cD := (isColimitOfPreserves E
    (F.isColimitOfIsWellOrderContinuous ⊤ (iic_top_isSuccLimit α hαlim))).whiskerEquivalence e
  let : PreservesColimit (e.functor ⋙ (S ⋙ F) ⋙ E) H := hsmall _ fun f => hmaps _ _ f
  have hcH : IsColimit (H.mapCocone cD) := isColimitOfPreserves H hcD
  obtain ⟨i, g, hg⟩ := Concrete.isColimit_exists_rep (D ⋙ H) hcH f
  have hι : cD.ι.app i =
      (F.map (homOfLE (show S.obj (eOrder i) ≤ ⊤ from le_top))).app M := by
    change E.map (cBase.ι.app (eOrder i)) = _
    dsimp [E, cBase]
  refine ⟨i, g, ?_⟩
  rw [← hι]
  exact hg

private theorem baerIterate_extend_of_not_isMax (R : Type u) [CommRing R] (α : Ordinal.{u})
    (M : ModuleCat.{u} R) (a : Ideal R) (k : Set.Iic α) (hk : ¬ IsMax k)
    (g : ModuleCat.of R a ⟶ (((baerSucc R).iterationFunctor (Set.Iic α)).obj k).obj M) :
    ∃ ψ : ModuleCat.of R R ⟶ (((baerSucc R).iterationFunctor (Set.Iic α)).obj ⊤).obj M,
      ModuleCat.ofHom a.subtype ≫ ψ =
        g ≫ (((baerSucc R).iterationFunctor (Set.Iic α)).map (homOfLE (le_top : k ≤ ⊤))).app M := by
  let F := (baerSucc R).iterationFunctor (Set.Iic α)
  let eSucc := (baerSucc R).iterationFunctorObjSuccIso k hk
  obtain ⟨ψ, hψ⟩ := baer_extension (R := R) (M := (F.obj k).obj M) a g.hom
  let ψCat : ModuleCat.of R R ⟶ ((baerSucc R).succ (F.obj k)).obj M := by
    change ModuleCat.of R R ⟶ ModuleCat.of R (BaerM R ((F.obj k).obj M))
    exact ModuleCat.ofHom ψ
  refine ⟨ψCat ≫ (eSucc.app M).inv ≫
    (F.map (homOfLE (show Order.succ k ≤ ⊤ from le_top))).app M, ?_⟩
  have hsuccMap : (F.map (homOfLE (show k ≤ Order.succ k from Order.le_succ k))).app M =
      ((baerSucc R).toSucc (F.obj k)).app M ≫ (eSucc.app M).inv := by
    simpa [eSucc] using congrArg (fun η => η.app M)
      ((baerSucc R).iterationFunctor_map_succ k hk)
  have hcomp : (F.map (homOfLE (le_top : k ≤ ⊤))).app M =
      (F.map (homOfLE (show k ≤ Order.succ k from Order.le_succ k))).app M ≫
        (F.map (homOfLE (show Order.succ k ≤ ⊤ from le_top))).app M := by
    rw [← NatTrans.comp_app, ← F.map_comp, homOfLE_comp]
  have hextSucc : ModuleCat.ofHom (a.subtype) ≫ ψCat =
      g ≫ ((baerSucc R).toSucc (F.obj k)).app M := by
    change ModuleCat.ofHom (a.subtype) ≫ ModuleCat.ofHom ψ =
      g ≫ ModuleCat.ofHom (baerUMap R ((F.obj k).obj M))
    exact ModuleCat.hom_ext hψ
  rw [hcomp, hsuccMap, reassoc_of% hextSucc]
  simp only [Category.assoc]

/-- If the cofinality of `α` exceeds the cardinality of the set of ideals of `R`, then the
top stage `M_α` of the transfinite Baer iteration is an injective `R`-module. -/
@[stacks 05NX "injectivity of the target"]
theorem baerIterate_injective_of_cofinality
    (R : Type u) [CommRing R] (α : Ordinal.{u})
    (hα : Cardinal.mk (Ideal R) < α.cof) (M : ModuleCat.{u} R) :
    Injective ((baerIterateFunctor R α).obj M) := by
  let F := (baerSucc R).iterationFunctor (Set.Iic α)
  change Injective ((F.obj ⊤).obj M)
  let T := (F.obj ⊤).obj M
  apply (Module.injective_iff_injective_object R (T : Type u)).mp
  apply Module.Baer.injective
  intro a φ
  obtain ⟨i, g, hfactor⟩ := baerIterate_factor_through_stage R α hα M a
    (ModuleCat.ofHom φ)
  let k := (Set.principalSegIio (⊤ : Set.Iic α)).monotone.functor.obj (ordinalToIioTop α i)
  let β := (Ordinal.ToType.mk.symm i).1
  have hβ : β + 1 < α :=
    (ordinal_limit_of_ideal_cofinality R α hα).succ_lt (Ordinal.ToType.mk.symm i).2
  have hkl : k < ⟨β + 1, hβ.le⟩ := by
    change β < β + 1
    exact Order.lt_succ β
  obtain ⟨ψ, hψ⟩ := baerIterate_extend_of_not_isMax R α M a k
    (fun hk => lt_irrefl k (hkl.trans_le (hk hkl.le))) g
  refine ⟨ψ.hom, fun x hx => ?_⟩
  have hfinal : ModuleCat.ofHom a.subtype ≫ ψ = ModuleCat.ofHom φ := hψ.trans hfactor
  simpa using congrArg (fun q : ModuleCat.of R a ⟶ T => q.hom ⟨x, hx⟩) hfinal

/-- The canonical natural map from a module to any transfinite Baer iterate is a monomorphism.
Together with `baerIterate_injective_of_cofinality`, its components give functorial injective
embeddings. -/
@[stacks 05NX "the natural embedding"]
theorem mono_baerIterateEmbedding
    (R : Type u) [CommRing R] (α : Ordinal.{u}) (M : ModuleCat.{u} R) :
    Mono ((baerIterateEmbedding R α).app M) := by
  let F := (baerSucc R).iterationFunctor (Set.Iic α)
  have : Mono ((F.map (homOfLE (show (⊥ : Set.Iic α) ≤ ⊤ from le_top))).app M) :=
    baerIterationMap_mono R α ⊤ ⊥ bot_le M
  change Mono (((baerSucc R).iterationFunctorObjBotIso (Set.Iic α)).inv.app M ≫
    (F.map (homOfLE (show (⊥ : Set.Iic α) ≤ ⊤ from le_top))).app M)
  infer_instance

end Stacks.Injectives
