module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.MapAlongCorepresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteObjectCohomology

/-!
# Cohomology over objects along a cocontinuous functor, naturally in the object

Let `G : C ⥤ D` be a continuous functor of sites whose restriction functor `G^*` on abelian
sheaves is exact and preserves injective objects (for instance, `G` continuous and cocontinuous
and preserving fibre products and equalizers). For an abelian sheaf `M` on `D` the cohomology of
`M` over `G U` is the cohomology of `G^* M` over `U`:
`Hⁿ(G U, M) ≅ Hⁿ(U, G^* M)`. This file builds that identification *as an isomorphism of
presheaves on `C`*, i.e. compatibly with the restriction maps along morphisms `U' ⟶ U`.

`Stacks.Cohomology.BiggerSite.cohomologyPresheafFunctorIso` gives the same groups for each `U`
separately, through derived functors; its naturality in `U` is not available there. Here the
comparison is instead the map of `Ext`-groups induced by the exact functor `G^*`, followed by
precomposition with the canonical morphism from the free abelian sheaf on `U` to the restriction
of the free abelian sheaf on `G U`. Both operations are compatible with composition of `Ext`, and
restriction maps of cohomology presheaves are precompositions, so the naturality is formal.

## Main definitions

* `Stacks.Cohomology.BiggerSite.freeYonedaSheafMap`: the morphism of free abelian sheaves
  induced by a morphism of objects.
* `Stacks.Cohomology.BiggerSite.freeYonedaSheafUnit`: the canonical morphism
  `ℤ[U] ⟶ G^* ℤ[G U]`.
* `Stacks.Cohomology.BiggerSite.cohomologyPresheafRestrictionIso`: the isomorphism of cohomology
  presheaves `G.op ⋙ Hⁿ(-, M) ≅ Hⁿ(-, G^* M)`.

## References

* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w v u u'

namespace Stacks.Cohomology.BiggerSite

section FreeYoneda

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [HasSheafify J Ab.{v}]

/-- **The morphism of free abelian sheaves induced by a morphism of objects.** It is the
morphism along which the restriction maps of `CategoryTheory.Sheaf.cohomologyPresheaf` are
precompositions. -/
def freeYonedaSheafMap {U U' : C} (g : U' ⟶ U) : freeYonedaSheaf J U' ⟶ freeYonedaSheaf J U :=
  (presheafToSheaf J Ab.{v}).map (Functor.whiskerRight (yoneda.map g) AddCommGrpCat.free)

/-- **Precomposition with `freeYonedaSheafMap` is restriction of sections.** Under the
corepresentation `freeYonedaSheafHomEquiv`, precomposing with the morphism induced by
`g : U' ⟶ U` restricts a section over `U` to `U'`. -/
theorem freeYonedaSheafHomEquiv_freeYonedaSheafMap_comp {U U' : C} (g : U' ⟶ U)
    (F : Sheaf J Ab.{v}) (φ : freeYonedaSheaf J U ⟶ F) :
    freeYonedaSheafHomEquiv J U' F (freeYonedaSheafMap J g ≫ φ) =
      F.obj.map g.op (freeYonedaSheafHomEquiv J U F φ) := by
  have h₁ := (sheafificationAdjunction J Ab.{v}).homEquiv_naturality_left
    (Functor.whiskerRight (yoneda.map g) AddCommGrpCat.free) φ
  have h₂ := (Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj).homEquiv_naturality_left
    (yoneda.map g) ((sheafificationAdjunction J Ab.{v}).homEquiv _ F φ)
  refine (congrArg (fun x => yonedaEquiv
    ((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj).homEquiv _ _ x)) h₁).trans ?_
  refine (congrArg yonedaEquiv h₂).trans ?_
  exact (yonedaEquiv_naturality _ g).symm

end FreeYoneda

section Restriction

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D) [G.IsContinuous J K]
  [HasSheafify J Ab.{v}] [HasSheafify K Ab.{v}]

/-- **The canonical morphism `ℤ[U] ⟶ G^* ℤ[G U]`**: under the corepresentation of sections over
`U` it is the tautological section of the free abelian sheaf on `G U` over `G U`. -/
def freeYonedaSheafUnit (U : C) :
    freeYonedaSheaf J U ⟶
      (G.sheafPushforwardContinuous Ab.{v} J K).obj (freeYonedaSheaf K (G.obj U)) :=
  (freeYonedaSheafHomEquiv J U _).symm (freeYonedaSheafHomEquiv K (G.obj U) _ (𝟙 _))

/-- **`freeYonedaSheafUnit` corepresents the tautological section over `G U`.** -/
private theorem freeYonedaSheafHomEquiv_unit (U : C) :
    freeYonedaSheafHomEquiv J U _ (freeYonedaSheafUnit J K G U) =
      freeYonedaSheafHomEquiv K (G.obj U) _ (𝟙 _) :=
  Equiv.apply_symm_apply _ _

/-- **`freeYonedaSheafUnit` followed by `G^* f` corepresents the same section as `f`.** -/
theorem freeYonedaSheafHomEquiv_unit_comp (U : C) (M : Sheaf K Ab.{v})
    (f : freeYonedaSheaf K (G.obj U) ⟶ M) :
    freeYonedaSheafHomEquiv J U _
        (freeYonedaSheafUnit J K G U ≫ (G.sheafPushforwardContinuous Ab.{v} J K).map f) =
      freeYonedaSheafHomEquiv K (G.obj U) M f := by
  rw [freeYonedaSheafHomEquiv_comp, freeYonedaSheafHomEquiv_unit]
  exact (freeYonedaSheafHomEquiv_comp K (G.obj U) (𝟙 _) f).symm.trans
    (congrArg _ (Category.id_comp f))

/-- **Morphisms out of `ℤ[G U]` are morphisms out of `ℤ[U]` into the restriction**, through
`freeYonedaSheafUnit`: both are sections over `G U`. -/
theorem bijective_freeYonedaSheafUnit_comp (U : C) (M : Sheaf K Ab.{v}) :
    Function.Bijective (fun f : freeYonedaSheaf K (G.obj U) ⟶ M =>
      freeYonedaSheafUnit J K G U ≫ (G.sheafPushforwardContinuous Ab.{v} J K).map f) := by
  have h : (fun f : freeYonedaSheaf K (G.obj U) ⟶ M =>
      freeYonedaSheafUnit J K G U ≫ (G.sheafPushforwardContinuous Ab.{v} J K).map f) =
      (freeYonedaSheafHomEquiv J U _).symm ∘ freeYonedaSheafHomEquiv K (G.obj U) M := by
    funext f
    exact (Equiv.eq_symm_apply _).mpr (freeYonedaSheafHomEquiv_unit_comp J K G U M f)
  rw [h]
  exact (Equiv.bijective _).comp (Equiv.bijective _)

/-- **`freeYonedaSheafUnit` is natural in the object.** -/
theorem freeYonedaSheafUnit_naturality {U U' : C} (g : U' ⟶ U) :
    freeYonedaSheafUnit J K G U' ≫
        (G.sheafPushforwardContinuous Ab.{v} J K).map (freeYonedaSheafMap K (G.map g)) =
      freeYonedaSheafMap J g ≫ freeYonedaSheafUnit J K G U := by
  apply (freeYonedaSheafHomEquiv J U' _).injective
  rw [freeYonedaSheafHomEquiv_unit_comp, freeYonedaSheafHomEquiv_freeYonedaSheafMap_comp,
    freeYonedaSheafHomEquiv_unit]
  exact (congrArg _ (Category.comp_id _)).symm.trans
    (freeYonedaSheafHomEquiv_freeYonedaSheafMap_comp K (G.map g) _ (𝟙 _))

variable [HasExt.{w} (Sheaf J Ab.{v})] [HasExt.{w} (Sheaf K Ab.{v})]
  [EnoughInjectives (Sheaf K Ab.{v})]
  [PreservesFiniteLimits (G.sheafPushforwardContinuous Ab.{v} J K)]
  [PreservesFiniteColimits (G.sheafPushforwardContinuous Ab.{v} J K)]
  [(G.sheafPushforwardContinuous Ab.{v} J K).PreservesInjectiveObjects]

/-- **Cohomology over `G U` is cohomology over `U` of the restriction, naturally in `U`.** For an
abelian sheaf `M` on `D`, the presheaf `U ↦ Hⁿ(G U, M)` on `C` is isomorphic to the cohomology
presheaf of `G^* M`. The component at `U` applies the exact functor `G^*` to extension classes and
precomposes with `freeYonedaSheafUnit`. -/
def cohomologyPresheafRestrictionIso (M : Sheaf K Ab.{v}) (n : ℕ) :
    G.op ⋙ M.cohomologyPresheaf.{w} n ≅
      ((G.sheafPushforwardContinuous Ab.{v} J K).obj M).cohomologyPresheaf.{w} n :=
  have : HasLimitsOfShape (Discrete WalkingPair) (Dᵒᵖ ⥤ Ab.{v}) := inferInstance
  have : HasBinaryProducts (Sheaf K Ab.{v}) := inferInstance
  have : (G.sheafPushforwardContinuous Ab.{v} J K).Additive :=
    Functor.additive_of_preserves_binary_products _
  NatIso.ofComponents
    (fun U => (AddEquiv.ofBijective
      (ExtComparison.extMapAlong.{w, w} (G.sheafPushforwardContinuous Ab.{v} J K)
        (freeYonedaSheafUnit J K G U.unop) M n)
      (ExtComparison.extMapAlong_bijective _ _
        (bijective_freeYonedaSheafUnit_comp J K G U.unop) M n)).toAddCommGrpIso)
    (fun {U U'} g => by
      ext e
      exact ExtComparison.extMapAlong_mk₀_comp _ _ _ _ _
        (freeYonedaSheafUnit_naturality J K G g.unop) e)

end Restriction

end Stacks.Cohomology.BiggerSite

end
