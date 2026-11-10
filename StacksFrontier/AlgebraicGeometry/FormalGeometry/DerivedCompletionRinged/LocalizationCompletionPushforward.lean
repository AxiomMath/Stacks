module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.LocalizationDerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.LocalizationPushforwardComplete
import StacksCore.Tactic.StacksAttribute

/-!
# The second map of Tag 0A0F

Let `(𝒞, 𝒪)` be a ringed site, `ℐ ⊂ 𝒪` a sheaf of ideals of finite type, `U` an object of `𝒞` and
`j : (𝒞/U, 𝒪_U) ⟶ (𝒞, 𝒪)` the localization morphism. Besides the canonical map
`a : (K|_U)^∧ ⟶ K^∧|_U` of `LocalizationCompletionFiniteType.lean`, [Stacks, Tag 0A0F] builds a
second map: `Rj_*` carries objects derived complete along `ℐ|_U` to objects derived complete along
`ℐ` ([Stacks, Tag 099J]), so the adjunct `K ⟶ Rj_*((K|_U)^∧)` of the completion map of `K|_U`
factors uniquely through `K ⟶ K^∧`, giving `b : K^∧ ⟶ Rj_*((K|_U)^∧)`. The source omits the
"formal verification that the adjoint of `b` is the inverse of `a`"; it is
`derivedCompletion_restrict_secondMap` here.

## Main results

* `Stacks.Algebraization.ReflectiveAdjunction.a_comp_homEquiv_symm_eq_id` and
  `Stacks.Algebraization.ReflectiveAdjunction.homEquiv_symm_comp_a_eq_id`: the formal
  verification, for an adjunction `L ⊣ R` and reflections on both sides intertwined by `a`.
* `AlgebraicGeometry.RingedSite.derivedCompletion_restrict_secondMap`: **the second half of
  [Stacks, Tag 0A0F].**

## Implementation notes

The adjunction is `AlgebraicGeometry.RingedSite.overFunctorDerivedAdjunction` of
`LocalizationDerivedAdjunction.lean`, restriction to the slice on derived categories being left
adjoint to the derived direct image `Rj_*` of the localization morphism of ringed topoi, and
[Stacks, Tag 099J] for `j` is
`AlgebraicGeometry.RingedSite.localizationDerivedPushforward_isDerivedComplete` of
`LocalizationPushforwardComplete.lean`.

## References

* [Stacks Project, Tag 099J](https://stacks.math.columbia.edu/tag/099J)
* [Stacks Project, Tag 0A0F](https://stacks.math.columbia.edu/tag/0A0F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Algebraization.ReflectiveAdjunction

/-! The setting: an adjunction `L ⊣ R`, a functor `c` with a natural map `η : 𝟭 ⟶ c` on the
source, a functor `c'` with `η'` on the target whose values are objects `P'` out of which maps
are determined by their composite with `η'`, and maps `a M : c'(L M) ⟶ L(c M)` compatible with
`η'` and `L η`. -/

variable {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] {L : 𝒜 ⥤ ℬ} {R : ℬ ⥤ 𝒜} (adj : L ⊣ R)
  {c : 𝒜 ⥤ 𝒜} (η : 𝟭 𝒜 ⟶ c)
  {P' : ℬ → Prop} {c' : ℬ ⥤ ℬ} (η' : 𝟭 ℬ ⟶ c')
  (hc' : ∀ M, P' (c'.obj M))
  (uniq' : ∀ {M N : ℬ}, P' N → ∀ {g₁ g₂ : c'.obj M ⟶ N},
    η'.app M ≫ g₁ = η'.app M ≫ g₂ → g₁ = g₂)
  (a : ∀ M, c'.obj (L.obj M) ⟶ L.obj (c.obj M)) (haiso : ∀ M, IsIso (a M))
  (ha : ∀ M, η'.app (L.obj M) ≫ a M = L.map (η.app M))

include adj ha uniq' hc' in
/-- **The adjoint of the second map inverts `a`**: if `b : c M ⟶ R(c'(L M))` is compatible with
the units, then its adjunct `L(c M) ⟶ c'(L M)` is a left inverse of `a`. -/
theorem a_comp_homEquiv_symm_eq_id (M : 𝒜) (b : c.obj M ⟶ R.obj (c'.obj (L.obj M)))
    (hb : η.app M ≫ b = adj.unit.app M ≫ R.map (η'.app (L.obj M))) :
    a M ≫ (adj.homEquiv _ _).symm b = 𝟙 _ := by
  refine uniq' (hc' _) ?_
  rw [← Category.assoc, ha, ← adj.homEquiv_naturality_left_symm, hb, Category.comp_id]
  exact (Equiv.symm_apply_eq _).2 (adj.homEquiv_unit _ _ _).symm

include adj ha uniq' hc' haiso in
/-- **The adjoint of the second map is the inverse of `a`**, on the other side. -/
theorem homEquiv_symm_comp_a_eq_id (M : 𝒜) (b : c.obj M ⟶ R.obj (c'.obj (L.obj M)))
    (hb : η.app M ≫ b = adj.unit.app M ≫ R.map (η'.app (L.obj M))) :
    (adj.homEquiv _ _).symm b ≫ a M = 𝟙 _ := by
  have := haiso M
  rw [← cancel_epi (a M), ← Category.assoc,
    a_comp_homEquiv_symm_eq_id adj η η' hc' uniq' a ha M b hb, Category.id_comp,
    Category.comp_id]

end Stacks.Algebraization.ReflectiveAdjunction

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

/-- Every map into a derived-complete object factors through the completion map. -/
theorem exists_comp_derivedCompletionUnit_eq
    [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).IsRightAdjoint]
    {M N : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    (hN : IsDerivedComplete.{u, u, u, u} X I N) (f : M ⟶ N) :
    ∃ g : (derivedCompletion X I).obj M ⟶ N, (derivedCompletionUnit X I).app M ≫ g = f :=
  ⟨(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).map
      (((derivedCompletionAdjunction X I).homEquiv M ⟨N, hN⟩).symm f),
    ((derivedCompletionAdjunction X I).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)⟩

variable [I.toSheafOfModules.IsFiniteType] (U : X.C)

/-- **The second half of [Stacks, Tag 0A0F]: the map `b` and its adjoint.** Let `ℐ ⊂ 𝒪` be a
sheaf of ideals of finite type, `U` an object of `𝒞` and `j` the localization morphism.

* `Rj_*` carries objects derived complete along `ℐ|_U` to objects derived complete along `ℐ`
  ([Stacks, Tag 099J] for `j`);
* hence for every `K` there is a unique `b : K^∧ ⟶ Rj_*((K|_U)^∧)` whose composite with the
  completion map `K ⟶ K^∧` is the adjunct `K ⟶ Rj_*((K|_U)^∧)` of the completion map of `K|_U`,
  under the adjunction `(-)|_U ⊣ Rj_*` (`overFunctorDerivedAdjunction`);
* the adjoint `K^∧|_U ⟶ (K|_U)^∧` of `b` is the inverse of the canonical map
  `a = derivedCompletionRestrictComparison` of `derivedCompletion_restrict`. -/
@[stacks 0A0F "the Remark's second argument: `Rj_*` carries objects derived complete along
  `ℐ|_U` to objects derived complete along `ℐ`, so there is a unique map
  `b : K^∧ ⟶ Rj_*((K|_U)^∧)` compatible with the completion maps, and the adjoint of `b` under
  `(-)|_U ⊣ Rj_*` is the inverse of the map `a` of `derivedCompletion_restrict`"]
theorem derivedCompletion_restrict_secondMap :
    (∀ E : DerivedCategory
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))),
      IsDerivedComplete.{u, u, u, u} (X.over U) (overIdeal I U) E →
        IsDerivedComplete.{u, u, u, u} X I ((localizationDerivedPushforward X U).obj E)) ∧
    (∀ K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
      ∃! b : (derivedCompletion X I).obj K ⟶ (localizationDerivedPushforward X U).obj
          ((derivedCompletion (X.over U) (overIdeal I U)).obj
            ((SheafOfModules.overFunctor.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj K)),
        (derivedCompletionUnit X I).app K ≫ b =
          (overFunctorDerivedAdjunction X U).unit.app K ≫
            (localizationDerivedPushforward X U).map
              ((derivedCompletionUnit (X.over U) (overIdeal I U)).app
                ((SheafOfModules.overFunctor.{u}
                  ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj K))) ∧
    (∀ (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
      (b : (derivedCompletion X I).obj K ⟶ (localizationDerivedPushforward X U).obj
          ((derivedCompletion (X.over U) (overIdeal I U)).obj
            ((SheafOfModules.overFunctor.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj K))),
      (derivedCompletionUnit X I).app K ≫ b =
          (overFunctorDerivedAdjunction X U).unit.app K ≫
            (localizationDerivedPushforward X U).map
              ((derivedCompletionUnit (X.over U) (overIdeal I U)).app
                ((SheafOfModules.overFunctor.{u}
                  ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj K)) →
        ((overFunctorDerivedAdjunction X U).homEquiv _ _).symm b ≫
            (derivedCompletionRestrictComparison X I U (overIdeal I U) (fun _ _ hg ↦ hg)).app K =
          𝟙 _ ∧
        (derivedCompletionRestrictComparison X I U (overIdeal I U) (fun _ _ hg ↦ hg)).app K ≫
            ((overFunctorDerivedAdjunction X U).homEquiv _ _).symm b = 𝟙 _) := by
  have hc := fun K => localizationDerivedPushforward_isDerivedComplete X I U _
    (isDerivedComplete_derivedCompletion_obj (X.over U) (overIdeal I U) K)
  refine ⟨fun E hE => localizationDerivedPushforward_isDerivedComplete X I U _ hE,
    fun K => ?_, fun K b hb => ⟨?_, ?_⟩⟩
  · obtain ⟨b, hb⟩ := exists_comp_derivedCompletionUnit_eq X I (hc _) _
    exact ⟨b, hb, fun b' hb' => hom_ext_derivedCompletionUnit X I (hc _) (hb'.trans hb.symm)⟩
  · exact Stacks.Algebraization.ReflectiveAdjunction.homEquiv_symm_comp_a_eq_id
      (overFunctorDerivedAdjunction X U) (derivedCompletionUnit X I)
      (derivedCompletionUnit (X.over U) (overIdeal I U))
      (isDerivedComplete_derivedCompletion_obj (X.over U) (overIdeal I U))
      (fun hN _ _ h => hom_ext_derivedCompletionUnit (X.over U) (overIdeal I U) hN h)
      (fun K => (derivedCompletionRestrictComparison X I U (overIdeal I U)
        (fun _ _ hg ↦ hg)).app K)
      (isIso_derivedCompletionRestrictComparison_overIdeal_app X I U)
      (derivedCompletionUnit_comp_derivedCompletionRestrictComparison X I U (overIdeal I U)
        (fun _ _ hg ↦ hg)) K b hb
  · exact Stacks.Algebraization.ReflectiveAdjunction.a_comp_homEquiv_symm_eq_id
      (overFunctorDerivedAdjunction X U) (derivedCompletionUnit X I)
      (derivedCompletionUnit (X.over U) (overIdeal I U))
      (isDerivedComplete_derivedCompletion_obj (X.over U) (overIdeal I U))
      (fun hN _ _ h => hom_ext_derivedCompletionUnit (X.over U) (overIdeal I U) hN h)
      (fun K => (derivedCompletionRestrictComparison X I U (overIdeal I U)
        (fun _ _ hg ↦ hg)).app K)
      (derivedCompletionUnit_comp_derivedCompletionRestrictComparison X I U (overIdeal I U)
        (fun _ _ hg ↦ hg)) K b hb

end AlgebraicGeometry.RingedSite

end
