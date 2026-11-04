module

public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.FilteredColimit
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.HomologicalPrecompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.CanonicalMapAsDeltaFunctorMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.ExplicitChainMapOnHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.FibreHomologyPresheaf

/-!
# The fibre homology presheaves form a homological δ-functor

Let `p : C ⥤ D` be a fibred category over the underlying site of a ringed site `(D, O_D)`, as in
Stacks 08P8, with small fibres. For an abelian presheaf `F` on `C` the presheaves

```
L_{n,p}(F) : V ↦ H_n(C_V, F|_{C_V})
```

of Stacks 08PI are functors of `F`, and this file equips that family with the structure of a
homological δ-functor: the connecting morphism of a short exact sequence of coefficient presheaves
is, at each `V`, the connecting morphism of the long exact sequence of the homology of the fibre
`C_V`. This is the first step of Stacks 08PJ.

For a functor `f : C' ⥤ C` of small categories and a transformation `τ : W ⟶ W' ⋙ f⁻¹` of exact
functors into abelian presheaves on `C'` resp. `C`, the canonical maps of Stacks 08PH
`categoryHomologyMap f (τ.app -)` commute with the connecting morphisms of both sides.

## Main definitions

* `Stacks.CategoryHomology.categoryHomologyδ`: the connecting morphism of the homology of a small
  category, with the projectivity hypothesis of Stacks 08PF discharged.
* `Stacks.Sites.FibredCategory.fiberRestriction`: restriction of abelian presheaves on the total
  category to the fibre at `V`, as an exact functor.
* `Stacks.Sites.FibredCategory.fiberCartesianRestrictionNatTrans`: restriction along the chosen
  cartesian lifts of `h : V' ⟶ V`, as a transformation of restriction functors.
* `Stacks.Sites.FibredCategory.fiberHomologyδ`: the connecting morphism of `L_{·,p}`, as a morphism
  of presheaves on the base.
* `Stacks.Sites.FibredCategory.fiberHomologyPresheafDeltaFunctor`: **the δ-functor of Stacks 08PJ,
  step one.** Its degree-`n` functor is `Stacks.Sites.FibredCategory.fiberHomologyPresheafFunctor`
  on the nose.
* `Stacks.Sites.FibredCategory.fiberHomologySheafDeltaFunctor`: the same with sheafified values.

## Main results

* `Stacks.CategoryHomology.categoryHomologyMap_id_eq_leftDerived_map`: the canonical map of Stacks
  08PH attached to the identity functor of `C` is the map the left derived functors of `colim`
  induce.
* `Stacks.CategoryHomology.categoryHomologyMap_comm_categoryHomologyδ`: a canonical map of Stacks
  08PH commutes with the connecting morphisms.
* `Stacks.CategoryHomology.HomologicalDeltaFunctor.postcomp`: postcomposition of a homological
  δ-functor with an exact additive functor.
* `Stacks.CategoryHomology.epi_of_epi_evaluation`: a pointwise epimorphism of diagrams in an
  abelian category is an epimorphism.
* `Stacks.Sites.FibredCategory.fiberHomologyδ_naturality` and
  `Stacks.Sites.FibredCategory.epi_fiberHomologyPresheafFunctor_map_g`: the connecting morphisms
  of `L_{·,p}` are natural in the short exact sequence, and `L_{0,p}` carries the second map of a
  short exact sequence to an epimorphism.

## Implementation notes

* The δ-functor is not built from a presheaf of chain complexes on the base: the chosen pullback
  functors are only pseudofunctorial, and the simplicial replacement depends on the indexing
  functor on the nose. The connecting morphisms are built fibre by fibre instead.
* Universes are written out at every call: instance search does not find
  `Stacks.CategoryHomology.presheafEnoughProjectives` at the universe `max w uD vD uC`, so the
  general results are stated over a universe parameter and instantiated at the fibres.
* In degree zero, identifying the spellings `(S.map W).X₂` and `W.obj S.X₂` unfolds the chosen
  projective resolutions and does not terminate; hence the form of `epi_categoryHomologyMap_id_map`
  and the use of `epi_of_epi_evaluation` rather than `CategoryTheory.NatTrans.epi_of_epi_app`.
* `CategoryTheory.Functor.Fiber` and `CategoryTheory.Functor.Fiber.fiberInclusion` are made locally
  `implicit_reducible`, and the δ-functor clauses are closed by `exact` rather than by rewriting,
  since the relevant spellings agree only up to definitional equality.

## References

* [Stacks Project, Tag 08PJ](https://stacks.math.columbia.edu/tag/08PJ)
* [Stacks Project, Tag 08PI](https://stacks.math.columbia.edu/tag/08PI)
* [Stacks Project, Tag 08PH](https://stacks.math.columbia.edu/tag/08PH)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category

namespace Stacks.CategoryHomology

universe u u' v uA vA uB vB uB' vB' uD vD uC w

/-! ### The canonical maps on homology commute with the connecting morphisms -/

section Aux

variable {C : Type u} {C' : Type u'} [SmallCategory C] [SmallCategory C']
  {A : Type uA} [Category.{vA} A] [Abelian A]
  [EnoughProjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v})]
  [EnoughProjectives (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v})]

/-- A canonical map on homology factors as the map induced by its coefficient morphism followed
by the canonical map with identity coefficients. -/
alias homologyMapAux_eq_leftDerived_map_comp := homologyMapAux_eq_comp

/-- **The canonical maps on homology commute with the connecting morphisms.** For exact functors
`W`, `W'` into abelian presheaves on `C'` and on `C` and a transformation `τ : W ⟶ W' ⋙ f⁻¹`, the
canonical maps of Stacks 08PH attached to `f` and to the components of `τ` form a morphism of the
long exact homology sequences of a short exact sequence. -/
theorem homologyMapAux_comm_leftDerivedδ (f : C' ⥤ C)
    (W : A ⥤ C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) [W.Additive]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (W' : A ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) [W'.Additive]
    [PreservesFiniteLimits W'] [PreservesFiniteColimits W']
    (τ : W ⟶ W' ⋙ presheafRestriction.{u, u', v} f)
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    homologyMapAux.{u, u', v} f (τ.app S.X₃) (n + 1) ≫
        (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).leftDerivedδ (hS.map_of_exact W') n =
      (colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).leftDerivedδ (hS.map_of_exact W) n ≫
        homologyMapAux.{u, u', v} f (τ.app S.X₁) n := by
  have h2 := (colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).leftDerivedδ_naturality
    (hS.map_of_exact W) ((hS.map_of_exact W').map_of_exact (presheafRestriction.{u, u', v} f))
    (ShortComplex.mapNatTrans S τ) n
  rw [ShortComplex.mapNatTrans_τ₁, ShortComplex.mapNatTrans_τ₃] at h2
  have h3 : (colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).leftDerivedδ
          ((hS.map_of_exact W').map_of_exact (presheafRestriction.{u, u', v} f)) n ≫
        homologyMapAux.{u, u', v} f (𝟙 (f.op ⋙ W'.obj S.X₁)) n =
      homologyMapAux.{u, u', v} f (𝟙 (f.op ⋙ W'.obj S.X₃)) (n + 1) ≫
        (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).leftDerivedδ (hS.map_of_exact W') n := by
    have h := (homologyMapAuxDeltaHom.{u, u', v} f).comm (hS.map_of_exact W') n
    rw [homologyMapAuxDeltaHom_app, homologyMapAuxDeltaHom_app] at h
    exact h
  rw [homologyMapAux_eq_leftDerived_map_comp f (τ.app S.X₃) (n + 1),
    homologyMapAux_eq_leftDerived_map_comp f (τ.app S.X₁) n, assoc, ← h3, ← assoc, h2, assoc]

end Aux

/-! ### The connecting morphism on the homology of a category -/

section Delta

variable {C : Type u} [SmallCategory C] {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})}

/-- **The connecting morphism of Stacks 08PF.** For a short exact sequence of abelian presheaves
on a small category `C`, the morphism `H_{n+1}(C, S.X₃) ⟶ H_n(C, S.X₁)` of the long exact
sequence of the left derived functors of `colim_{Cᵒᵖ}`. -/
def categoryHomologyδ (hS : S.ShortExact) (n : ℕ) :
    categoryHomology.{u, v} S.X₃ (n + 1) ⟶ categoryHomology.{u, v} S.X₁ n :=
  (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _).leftDerivedδ hS n

/-- **Stacks 08PH for the identity functor.** The canonical map on homology attached to the
identity functor of `C` and a morphism of coefficient presheaves is the map induced by the left
derived functors of `colim_{Cᵒᵖ}`. -/
theorem categoryHomologyMap_id_eq_leftDerived_map
    {F F' : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} (t : F' ⟶ F) (n : ℕ) :
    categoryHomologyMap.{u, u, v} (𝟭 C) (F := F) (F' := F') t n =
      ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _).leftDerived n).map t := by
  have := presheafEnoughProjectives.{u, max u v} C
  have hid : homologyMapAux.{u, u, v} (𝟭 C) (𝟙 ((𝟭 C).op ⋙ F)) n =
      𝟙 (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _).leftDerived n).obj ((𝟭 C).op ⋙ F)) :=
    homologyMapAux_id.{u, v} F n
  have h := homologyMapAux_eq_leftDerived_map_comp.{u, u, v} (𝟭 C) (F := F) (F' := F') t n
  rw [hid, comp_id] at h
  exact h

/-- The map on homology induced by the second map of a short exact sequence composes with the
connecting morphism to zero. -/
theorem categoryHomologyMap_id_comp_categoryHomologyδ (hS : S.ShortExact) (n : ℕ) :
    categoryHomologyMap.{u, u, v} (𝟭 C) (F := S.X₃) (F' := S.X₂) S.g (n + 1) ≫
        categoryHomologyδ.{u, v} hS n = 0 := by
  rw [categoryHomologyMap_id_eq_leftDerived_map]
  exact (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _).leftDerived_map_g_comp_δ hS n

/-- The connecting morphism composes with the map on homology induced by the first map of a short
exact sequence to zero. -/
theorem categoryHomologyδ_comp_categoryHomologyMap_id (hS : S.ShortExact) (n : ℕ) :
    categoryHomologyδ.{u, v} hS n ≫
        categoryHomologyMap.{u, u, v} (𝟭 C) (F := S.X₂) (F' := S.X₁) S.f n = 0 := by
  rw [categoryHomologyMap_id_eq_leftDerived_map]
  exact (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _).leftDerivedδ_comp_map_f hS n

/-- A short complex with the same morphisms as an exact one, up to equality, is exact. -/
private theorem exact_mk_of_eq_of_exact {D : Type*} [Category D] [Preadditive D]
    {S' : ShortComplex D} (h : S'.Exact) {f : S'.X₁ ⟶ S'.X₂} {g : S'.X₂ ⟶ S'.X₃}
    (hf : f = S'.f) (hg : g = S'.g) (hz : f ≫ g = 0) : (ShortComplex.mk f g hz).Exact := by
  refine ShortComplex.exact_of_iso ?_ h
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [hf]) (by simp [hg])

/-- The three-term sequence of homology groups in a fixed degree attached to a short exact
sequence of coefficient presheaves is exact. -/
theorem exact_categoryHomologyMap_id (hS : S.ShortExact) (n : ℕ)
    (hz : categoryHomologyMap.{u, u, v} (𝟭 C) (F := S.X₂) (F' := S.X₁) S.f n ≫
      categoryHomologyMap.{u, u, v} (𝟭 C) (F := S.X₃) (F' := S.X₂) S.g n = 0) :
    (ShortComplex.mk _ _ hz).Exact :=
  exact_mk_of_eq_of_exact
    ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _).leftDerived_exact hS n)
    (categoryHomologyMap_id_eq_leftDerived_map.{u, v} S.f n)
    (categoryHomologyMap_id_eq_leftDerived_map.{u, v} S.g n) hz

/-- Exactness of `H_{n+1}(C, S.X₂) ⟶ H_{n+1}(C, S.X₃) ⟶ H_n(C, S.X₁)`. -/
theorem exact_categoryHomologyδ₁ (hS : S.ShortExact) (n : ℕ)
    (hz : categoryHomologyMap.{u, u, v} (𝟭 C) (F := S.X₃) (F' := S.X₂) S.g (n + 1) ≫
      categoryHomologyδ.{u, v} hS n = 0) :
    (ShortComplex.mk _ _ hz).Exact :=
  exact_mk_of_eq_of_exact
    ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _).leftDerived_exact_δ₁ hS n)
    (categoryHomologyMap_id_eq_leftDerived_map.{u, v} S.g (n + 1)) rfl hz

/-- Exactness of `H_{n+1}(C, S.X₃) ⟶ H_n(C, S.X₁) ⟶ H_n(C, S.X₂)`. -/
theorem exact_categoryHomologyδ₂ (hS : S.ShortExact) (n : ℕ)
    (hz : categoryHomologyδ.{u, v} hS n ≫
      categoryHomologyMap.{u, u, v} (𝟭 C) (F := S.X₂) (F' := S.X₁) S.f n = 0) :
    (ShortComplex.mk _ _ hz).Exact :=
  exact_mk_of_eq_of_exact
    ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _).leftDerived_exact_δ₂ hS n)
    rfl (categoryHomologyMap_id_eq_leftDerived_map.{u, v} S.f n) hz

/-- The connecting morphism is natural in the short exact sequence. -/
theorem categoryHomologyδ_naturality {T : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ) :
    categoryHomologyMap.{u, u, v} (𝟭 C) (F := T.X₃) (F' := S.X₃) φ.τ₃ (n + 1) ≫
        categoryHomologyδ.{u, v} hT n =
      categoryHomologyδ.{u, v} hS n ≫
        categoryHomologyMap.{u, u, v} (𝟭 C) (F := T.X₁) (F' := S.X₁) φ.τ₁ n := by
  rw [categoryHomologyMap_id_eq_leftDerived_map, categoryHomologyMap_id_eq_leftDerived_map]
  exact (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _).leftDerivedδ_naturality hS hT φ n

end Delta

section Comm

/-- The canonical maps attached to the identity functor of `C` are additive in the coefficient
morphism, when the coefficients are the values of an additive functor. -/
theorem categoryHomologyMap_id_map_add.{u₁, v₁, uA₁, vA₁} {C : Type u₁} [SmallCategory C]
    {A : Type uA₁} [Category.{vA₁} A] [Preadditive A]
    (W : A ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}) [W.Additive] {X Y : A} (α β : X ⟶ Y) (n : ℕ) :
    categoryHomologyMap.{u₁, u₁, v₁} (𝟭 C) (F := W.obj Y) (F' := W.obj X) (W.map (α + β)) n =
      categoryHomologyMap.{u₁, u₁, v₁} (𝟭 C) (F := W.obj Y) (F' := W.obj X) (W.map α) n +
        categoryHomologyMap.{u₁, u₁, v₁} (𝟭 C) (F := W.obj Y) (F' := W.obj X) (W.map β) n := by
  rw [CategoryTheory.Functor.map_add, categoryHomologyMap_id_eq_leftDerived_map,
    categoryHomologyMap_id_eq_leftDerived_map, categoryHomologyMap_id_eq_leftDerived_map,
    CategoryTheory.Functor.map_add]

/-- **In degree zero the map on homology induced by the second map of a short exact sequence is
an epimorphism**, for coefficients the values of an exact additive functor. -/
theorem epi_categoryHomologyMap_id_map.{u₁, v₁, uA₁, vA₁} {C : Type u₁} [SmallCategory C]
    {A : Type uA₁} [Category.{vA₁} A] [Abelian A]
    (W : A ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}) [W.Additive]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    {S : ShortComplex A} (hS : S.ShortExact) :
    Epi (categoryHomologyMap.{u₁, u₁, v₁} (𝟭 C) (F := W.obj S.X₃) (F' := W.obj S.X₂)
      (W.map S.g) 0) := by
  rw [categoryHomologyMap_id_eq_leftDerived_map]
  exact (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁}) ⥤ _).epi_leftDerivedZero_map_g
    (hS.map_of_exact W)

/-- A morphism of diagrams in an abelian category which is an epimorphism at every index is an
epimorphism. Unlike `CategoryTheory.NatTrans.epi_of_epi_app` it needs no `HasPushouts` instance,
whose search over abelian presheaves does not terminate here. -/
lemma epi_of_epi_evaluation {I : Type uA} [Category.{vA} I] {B : Type uB} [Category.{vB} B]
    [Abelian B] {X Y : I ⥤ B} (α : X ⟶ Y) (h : ∀ i, Epi (α.app i)) : Epi α := by
  rw [← ShortComplex.exact_iff_epi (ShortComplex.mk α (0 : Y ⟶ Y) comp_zero) rfl]
  exact ShortComplex.exact_of_exact_evaluation _ fun i =>
    (ShortComplex.exact_iff_epi _ rfl).2 (h i)

/-- **A canonical map of Stacks 08PH commutes with the connecting morphisms.** For exact functors
`W`, `W'` into abelian presheaves on `C'` and on `C` and a transformation `τ : W ⟶ W' ⋙ f⁻¹`, the
canonical maps attached to `f` and to the components of `τ` commute with the connecting
morphisms. -/
theorem categoryHomologyMap_comm_categoryHomologyδ.{u₁, u₂, v₁, uA₁, vA₁} {C : Type u₁}
    {C' : Type u₂} [SmallCategory C] [SmallCategory C'] {A : Type uA₁} [Category.{vA₁} A]
    [Abelian A] (f : C' ⥤ C)
    (W : A ⥤ C'ᵒᵖ ⥤ AddCommGrpCat.{max u₁ u₂ v₁}) [W.Additive]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (W' : A ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ u₂ v₁}) [W'.Additive]
    [PreservesFiniteLimits W'] [PreservesFiniteColimits W']
    (τ : W ⟶ W' ⋙ presheafRestriction.{u₁, u₂, v₁} f)
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    categoryHomologyMap.{u₁, u₂, v₁} f (τ.app S.X₃) (n + 1) ≫
        categoryHomologyδ.{u₁, max u₂ v₁} (hS.map_of_exact W') n =
      categoryHomologyδ.{u₂, max u₁ v₁} (hS.map_of_exact W) n ≫
        categoryHomologyMap.{u₁, u₂, v₁} f (τ.app S.X₁) n := by
  have := presheafEnoughProjectives.{u₁, max u₂ v₁} C
  have := presheafEnoughProjectives.{u₂, max u₁ v₁} C'
  exact homologyMapAux_comm_leftDerivedδ.{u₁, u₂, v₁} f W W' τ hS n

end Comm

/-! ### Postcomposition of a homological δ-functor with an exact functor -/

namespace HomologicalDeltaFunctor

section Postcompose

variable {A : Type uA} [Category.{vA} A] [Abelian A] {B : Type uB} [Category.{vB} B] [Abelian B]
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] (E : B ⥤ B') [E.Additive]
  [PreservesFiniteLimits E] [PreservesFiniteColimits E]

/-- **Postcomposition of a homological δ-functor with an exact additive functor.** The degree-`n`
functor is `Hₙ ⋙ E` and the connecting morphism of a short exact sequence is the image under `E`
of the connecting morphism of `H`. -/
def postcomp (H : HomologicalDeltaFunctor A B) : HomologicalDeltaFunctor A B' where
  functor n := H.functor n ⋙ E
  additive n := have := H.additive n; inferInstance
  δ hS n := E.map (H.δ hS n)
  map_g_δ hS n := by
    rw [Functor.comp_map, ← E.map_comp, H.map_g_δ hS n, E.map_zero]
  δ_map_f hS n := by
    rw [Functor.comp_map, ← E.map_comp, H.δ_map_f hS n, E.map_zero]
  epi_map_g hS := by
    have := H.epi_map_g hS
    exact inferInstanceAs (Epi (E.map ((H.functor 0).map _)))
  exact_map hS n := (H.exact_map hS n).map E
  exact_δ₁ hS n := (H.exact_δ₁ hS n).map E
  exact_δ₂ hS n := (H.exact_δ₂ hS n).map E
  δ_naturality hS hT φ n := by
    rw [Functor.comp_map, Functor.comp_map, ← E.map_comp, ← E.map_comp,
      H.δ_naturality hS hT φ n]

/-- The degree-`n` functor of a postcomposition. Deliberately not a `simp` lemma: it rewrites a
whole functor. -/
lemma postcomp_functor (H : HomologicalDeltaFunctor A B) (n : ℕ) :
    (H.postcomp E).functor n = H.functor n ⋙ E :=
  rfl

/-- The connecting morphism of a postcomposition. Not a `simp` lemma, for the same reason. -/
lemma postcomp_δ (H : HomologicalDeltaFunctor A B) {S : ShortComplex A} (hS : S.ShortExact)
    (n : ℕ) :
    (H.postcomp E).δ hS n = E.map (H.δ hS n) :=
  rfl

end Postcompose

end HomologicalDeltaFunctor

end Stacks.CategoryHomology

namespace Stacks.Sites.FibredCategory

open Stacks.CategoryHomology

universe uD vD uC w

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

variable (s : FibredCategorySituation.{uD, vD, uC, uC, w})

/-- Restriction of abelian presheaves on the total category to the fibre at `V`, that is
precomposition with the inclusion of the fibre. -/
abbrev fiberRestriction (V : s.base.C) :
    (s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}) ⥤
      (s.p.Fiber V)ᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC} :=
  CategoryHomology.presheafRestriction.{uC, uC, max w uD vD uC}
    (Functor.Fiber.fiberInclusion (p := s.p) (S := V))

/-- Restriction of the coefficients along the chosen cartesian lifts of `h : V' ⟶ V`, as a
transformation from restriction to the fibre at `V` to restriction to the fibre at `V'` reindexed
along the chosen pullback functor. Its component at `F` is
`Stacks.Sites.FibredCategory.fiberCartesianRestriction`. -/
def fiberCartesianRestrictionNatTrans {V V' : s.base.C} (h : V' ⟶ V) :
    fiberRestriction s V ⟶
      fiberRestriction s V' ⋙ CategoryHomology.presheafRestriction.{uC, uC, max w uD vD uC}
        ((Functor.chosenPullbacks s.p).pullbackFunctor h) where
  app F := fiberCartesianRestriction s F h
  naturality F G α := by
    refine NatTrans.ext (funext fun x => ?_)
    change α.app (.op (Functor.Fiber.fiberInclusion.obj x.unop)) ≫
        G.map (.op ((Functor.chosenPullbacks s.p).map h x.unop)) =
      F.map (.op ((Functor.chosenPullbacks s.p).map h x.unop)) ≫
        α.app (.op (Functor.Fiber.fiberInclusion.obj
          ((Functor.chosenPullbacks s.p).obj h x.unop)))
    exact (α.naturality ((Functor.chosenPullbacks s.p).map h x.unop).op).symm

/-- **Stacks 08PI, the connecting morphism.** For a short exact sequence of abelian presheaves on
the total category, the morphism of presheaves on the base from `L_{n+1,p}(S.X₃)` to
`L_{n,p}(S.X₁)` whose component at `V` is the connecting morphism of the homology of the fibre at
`V`. -/
def fiberHomologyδ {S : ShortComplex (s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC})}
    (hS : S.ShortExact) (n : ℕ) :
    (fiberHomologyPresheafFunctor s (n + 1)).obj S.X₃ ⟶
      (fiberHomologyPresheafFunctor s n).obj S.X₁ where
  app V := CategoryHomology.categoryHomologyδ.{uC, max w uD vD uC}
    (hS.map_of_exact (fiberRestriction s V.unop)) n
  naturality V V' h :=
    CategoryHomology.categoryHomologyMap_comm_categoryHomologyδ.{uC, uC, max w uD vD uC}
      ((Functor.chosenPullbacks s.p).pullbackFunctor h.unop)
      (fiberRestriction s V.unop) (fiberRestriction s V'.unop)
      (fiberCartesianRestrictionNatTrans s h.unop) hS n

/-- The map of fibre homology presheaves induced by the second map of a short exact sequence of
coefficients is an epimorphism in degree zero. -/
lemma epi_fiberHomologyPresheafFunctor_map_g
    {S : ShortComplex (s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC})} (hS : S.ShortExact) :
    Epi ((fiberHomologyPresheafFunctor s 0).map S.g) := by
  refine CategoryHomology.epi_of_epi_evaluation _ fun V => ?_
  rw [fiberHomologyPresheafFunctor_map_app]
  exact CategoryHomology.epi_categoryHomologyMap_id_map.{uC, max w uD vD uC}
    (fiberRestriction s V.unop) hS

/-- The connecting morphisms of the fibre homology presheaves are natural in the short exact
sequence of coefficients. -/
lemma fiberHomologyδ_naturality
    {S T : ShortComplex (s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC})} (hS : S.ShortExact)
    (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ) :
    (fiberHomologyPresheafFunctor s (n + 1)).map φ.τ₃ ≫ fiberHomologyδ s hT n =
      fiberHomologyδ s hS n ≫ (fiberHomologyPresheafFunctor s n).map φ.τ₁ :=
  NatTrans.ext (funext fun V => by
    rw [NatTrans.comp_app, NatTrans.comp_app]
    exact CategoryHomology.categoryHomologyδ_naturality.{uC, max w uD vD uC}
      (hS.map_of_exact (fiberRestriction s V.unop))
      (hT.map_of_exact (fiberRestriction s V.unop))
      ((fiberRestriction s V.unop).mapShortComplex.map φ) n)

/-- **Stacks 08PJ, step one.** The fibre homology presheaves of Stacks 08PI, with the connecting
morphisms of the long exact sequences of the fibres, form a homological δ-functor from abelian
presheaves on the total category to abelian presheaves on the base. The degree-`n` functor is
`Stacks.Sites.FibredCategory.fiberHomologyPresheafFunctor` itself. -/
def fiberHomologyPresheafDeltaFunctor :
    CategoryHomology.HomologicalDeltaFunctor
      (s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC})
      (s.base.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}) where
  functor n := fiberHomologyPresheafFunctor s n
  additive n :=
    { map_add := fun {_F _G α β} => NatTrans.ext (funext fun V => by
        rw [NatTrans.app_add]
        exact CategoryHomology.categoryHomologyMap_id_map_add.{uC, max w uD vD uC}
          (fiberRestriction s V.unop) α β n) }
  δ hS n := fiberHomologyδ s hS n
  map_g_δ hS n := NatTrans.ext (funext fun V => by
    rw [NatTrans.comp_app, NatTrans.app_zero]
    exact CategoryHomology.categoryHomologyMap_id_comp_categoryHomologyδ.{uC, max w uD vD uC}
      (hS.map_of_exact (fiberRestriction s V.unop)) n)
  δ_map_f hS n := NatTrans.ext (funext fun V => by
    rw [NatTrans.comp_app, NatTrans.app_zero]
    exact CategoryHomology.categoryHomologyδ_comp_categoryHomologyMap_id.{uC, max w uD vD uC}
      (hS.map_of_exact (fiberRestriction s V.unop)) n)
  epi_map_g hS := epi_fiberHomologyPresheafFunctor_map_g s hS
  exact_map hS n := ShortComplex.exact_of_exact_evaluation _ fun V =>
    CategoryHomology.exact_categoryHomologyMap_id.{uC, max w uD vD uC}
      (hS.map_of_exact (fiberRestriction s V.unop)) n _
  exact_δ₁ hS n := ShortComplex.exact_of_exact_evaluation _ fun V =>
    CategoryHomology.exact_categoryHomologyδ₁.{uC, max w uD vD uC}
      (hS.map_of_exact (fiberRestriction s V.unop)) n _
  exact_δ₂ hS n := ShortComplex.exact_of_exact_evaluation _ fun V =>
    CategoryHomology.exact_categoryHomologyδ₂.{uC, max w uD vD uC}
      (hS.map_of_exact (fiberRestriction s V.unop)) n _
  δ_naturality hS hT φ n := fiberHomologyδ_naturality s hS hT φ n

/-- The degree-`n` functor of the δ-functor of fibre homology is the presheaf of fibre homology of
Stacks 08PI. Deliberately not a `simp` lemma: it rewrites a whole functor. -/
lemma fiberHomologyPresheafDeltaFunctor_functor (n : ℕ) :
    (fiberHomologyPresheafDeltaFunctor s).functor n = fiberHomologyPresheafFunctor s n :=
  rfl

/-- The connecting morphism of the δ-functor of fibre homology is, at `V`, the connecting
morphism of the homology of the fibre at `V`. -/
lemma fiberHomologyPresheafDeltaFunctor_δ_app
    {S : ShortComplex (s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC})} (hS : S.ShortExact) (n : ℕ)
    (V : s.base.Cᵒᵖ) :
    ((fiberHomologyPresheafDeltaFunctor s).δ hS n).app V =
      CategoryHomology.categoryHomologyδ.{uC, max w uD vD uC}
        (hS.map_of_exact (fiberRestriction s V.unop)) n :=
  rfl

/-- **Stacks 08PJ, step one, for the sheaves `L_n(F)`.** The sheaves of fibre homology, with the
connecting morphisms of the fibres, form a homological δ-functor into abelian sheaves on the
base. -/
def fiberHomologySheafDeltaFunctor [HasSheafify s.base.J AddCommGrpCat.{max w uD vD uC}] :
    CategoryHomology.HomologicalDeltaFunctor
      (s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC})
      (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC}) :=
  (fiberHomologyPresheafDeltaFunctor s).postcomp
    (presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC})

/-- The degree-`n` functor of the sheafified δ-functor is the presheaf of fibre homology followed
by sheafification, so its value at `F` is the sheaf `L_n(F)` of Stacks 08PI. Deliberately not a
`simp` lemma: it rewrites a whole functor. -/
lemma fiberHomologySheafDeltaFunctor_functor
    [HasSheafify s.base.J AddCommGrpCat.{max w uD vD uC}] (n : ℕ) :
    (fiberHomologySheafDeltaFunctor s).functor n =
      fiberHomologyPresheafFunctor s n ⋙
        presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC} :=
  rfl

/-- The value of the sheafified δ-functor at a coefficient presheaf is the sheaf `L_n(F)` of
Stacks 08PI. -/
lemma fiberHomologySheafDeltaFunctor_functor_obj
    [HasSheafify s.base.J AddCommGrpCat.{max w uD vD uC}] (n : ℕ)
    (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}) :
    ((fiberHomologySheafDeltaFunctor s).functor n).obj F = fiberHomologySheaf s F n :=
  rfl

end Stacks.Sites.FibredCategory

end
