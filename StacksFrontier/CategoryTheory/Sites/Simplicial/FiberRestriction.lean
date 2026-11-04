module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.RestrictTransition

/-!
# Fibrewise restriction of sheaves on the total site

In the simplicial-site situation of Stacks 09WE, a sheaf `F` on the total site restricts, in
every simplicial degree `n`, to a sheaf `F_n` on the component site, and the arrows of the
total category lying over a simplex map `φ : [m] ⟶ [n]` assemble into a transition map
`f_φ⁻¹ F_m ⟶ F_n`. This file constructs that data and pins it down by the restriction maps of
the original presheaf.

All names are in the namespace `CategoryTheory.SimplicialSiteSituation`.

## Main definitions

* `fiberRestriction`: restriction to a component followed by sheafification, which does not
  change the underlying presheaf.
* `fiberRestrictTransition`: the direct-image transition on fibre restrictions, transported from
  `restrictTransition`.
* `inverseImageFiberTransition`: the inverse-image transition on fibre restrictions.
* `IsRestrictionTransition`: the property of a transition that its adjoint is presheaf
  restriction along every arrow of the total category.
* `FiberRestrictionData`: the package consisting of the sheaf condition on raw restrictions, a
  transition, and the restriction equations characterizing it.

## Main results

* `fiberRestrictionData`: the fibre restrictions of a sheaf on the total site, together with
  their specified transitions.
* `inverseImageFiberTransition_restriction`: the adjoint of the transition is presheaf
  restriction along every arrow of the total category.
* `IsRestrictionTransition.ext`: those restriction equations determine the transition uniquely.

## Implementation notes

Two restriction functors appear. `restrict`, from
`StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentRestriction`, is precomposition with the
component inclusion, which lands in sheaves because that inclusion is continuous;
`fiberRestriction` sheafifies afterwards, which is the shape in which the inverse-image functor
of a cocontinuous functor is written. They are identified by `restrictIsoFiberRestriction`,
whose components are the sheafification units, and the transition is transported along that
identification.

The transition itself is the mate, under the adjunction specified in the morphism of topoi, of
the direct-image transition `restrictTransition` of
`StacksFrontier.CategoryTheory.Sites.Simplicial.RestrictTransition`, whose inverse-image mate
there, `fiberTransition`, is the same construction on `restrict` rather than on
`fiberRestriction`.

## References

* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pseudofunctor

universe u

namespace CategoryTheory

namespace SimplicialSiteSituation

/-- Because the component inclusion is continuous, the raw restriction of a sheaf on the total
site is already a sheaf for the component topology. -/
theorem restrict_isSheaf (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)
    (F : Sheaf S.totalTopology (Type u)) :
    Presheaf.IsSheaf (S.componentTopology n) ((S.inclusion n).op ⋙ F.obj) :=
  ((S.restrict n).obj F).property

section ContinuousArrows

attribute [local implicit_reducible] CategoryTheory.SimplicialSite.totalPseudofunctor
  CategoryTheory.Functor.toPseudofunctor' CategoryTheory.pseudofunctorOfIsLocallyDiscrete
  Quiver.Hom.toLoc CategoryTheory.Pseudofunctor.CoGrothendieck.ι

/-- The arrow `(φ, f)` of the total category in case (A). -/
def continuousTotalArrow (C : SimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) {U : C.underlying.obj n}
    {V : C.underlying.obj m} (f : U ⟶ (C.underlying.map φ).toFunctor.obj V) :
    (inclusion (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).obj U ⟶
      (inclusion (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) m).obj V :=
  ⟨φ.op, f⟩

end ContinuousArrows

section CocontinuousArrows

attribute [local implicit_reducible] CategoryTheory.Grothendieck.ι

/-- The arrow `(φ, f)` of the total category in case (B). -/
def cocontinuousTotalArrow (C : CocontinuousSimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) {U : C.underlying.obj (Opposite.op n)}
    {V : C.underlying.obj (Opposite.op m)}
    (f : (C.underlying.map φ.op).toFunctor.obj U ⟶ V) :
    (inclusion (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).obj U ⟶
      (inclusion (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) m).obj V :=
  ⟨φ.op, f⟩

end CocontinuousArrows

/-- Restriction to a simplicial degree, expressed by precomposition with the component
inclusion and sheafification. The latter does not change the underlying presheaf because
fibrewise coverings are coverings in the total site. -/
noncomputable def fiberRestriction (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) :
    Sheaf S.totalTopology (Type u) ⥤ Sheaf (S.componentTopology n) (Type u) :=
  sheafToPresheaf S.totalTopology (Type u) ⋙
    (Functor.whiskeringLeft _ _ _).obj (S.inclusion n).op ⋙
      presheafToSheaf (S.componentTopology n) (Type u)

/-- The sheafification unit from presheaf restriction to fibre restriction. -/
noncomputable def fiberRestrictionUnit (S : SimplicialSiteSituation.{u})
    (F : Sheaf S.totalTopology (Type u)) (n : SimplexCategory) :
    (S.inclusion n).op ⋙ F.obj ⟶ ((S.fiberRestriction n).obj F).obj :=
  toSheafify (S.componentTopology n) _

/-- Raw restriction and fibre restriction are identified by the sheafification units. -/
noncomputable def restrictIsoFiberRestriction (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) : S.restrict n ≅ S.fiberRestriction n :=
  NatIso.ofComponents
    (fun F => (fullyFaithfulSheafToPresheaf (S.componentTopology n) (Type u)).preimageIso
      (isoSheafify (S.componentTopology n) (S.restrict_isSheaf n F)))
    (fun _ => Sheaf.hom_ext (toSheafify_naturality _ _))

/-- The forward identification is the sheafification unit. -/
theorem restrictIsoFiberRestriction_hom_app_hom (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) (F : Sheaf S.totalTopology (Type u)) :
    ((S.restrictIsoFiberRestriction n).hom.app F).hom = S.fiberRestrictionUnit F n := rfl

/-- The backward identification is the inverse of the sheafification unit. -/
theorem restrictIsoFiberRestriction_inv_app_hom (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) (F : Sheaf S.totalTopology (Type u)) :
    ((S.restrictIsoFiberRestriction n).inv.app F).hom =
      (isoSheafify (S.componentTopology n) (S.restrict_isSheaf n F)).inv := rfl

/-- The direct-image transition on fibre restrictions, transported from `restrictTransition`
along the sheafification units. -/
noncomputable def fiberRestrictTransition (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    S.fiberRestriction m ⟶ S.fiberRestriction n ⋙ (S.transitionMorphism φ).pushforward :=
  (S.restrictIsoFiberRestriction m).inv ≫ S.restrictTransition φ ≫
    Functor.whiskerRight (S.restrictIsoFiberRestriction n).hom
      (S.transitionMorphism φ).pushforward

/-- The components of the transported direct-image transition. -/
theorem fiberRestrictTransition_app_hom (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) (F : Sheaf S.totalTopology (Type u)) :
    ((S.fiberRestrictTransition φ).app F).hom =
      ((S.restrictIsoFiberRestriction m).inv.app F).hom ≫
        ((S.restrictTransition φ).app F).hom ≫
          ((S.transitionMorphism φ).pushforward.map
            ((S.restrictIsoFiberRestriction n).hom.app F)).hom := rfl

/-- The natural transition between fibre restrictions of a sheaf on the total site: the mate,
under the adjunction specified in the morphism of topoi, of the direct-image transition.

This is the mate construction of `fiberTransition`, taken at `S.fiberRestriction` (restriction
followed by sheafification) instead of at `S.restrict` (restriction by precomposition). -/
noncomputable def inverseImageFiberTransition (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    S.fiberRestriction m ⋙ (S.transitionMorphism φ).inverseImage ⟶ S.fiberRestriction n where
  app F :=
    ((S.transitionMorphism φ).adj.homEquiv _ _).symm ((S.fiberRestrictTransition φ).app F)
  naturality F G α := by
    simpa only [Functor.comp_map] using
      (S.transitionMorphism φ).adj.homEquiv_naturality_right_square
        ((S.fiberRestriction m).map α)
        ((S.fiberRestrictTransition φ).app G)
        ((S.fiberRestrictTransition φ).app F)
        ((S.fiberRestriction n).map α)
        (by simpa only [Functor.comp_map] using (S.fiberRestrictTransition φ).naturality α)

/-- The adjoint of the inverse-image transition is the direct-image transition. -/
theorem inverseImageFiberTransition_adj (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) (F : Sheaf S.totalTopology (Type u)) :
    ((S.transitionMorphism φ).adj.homEquiv _ _) ((S.inverseImageFiberTransition φ).app F) =
      (S.fiberRestrictTransition φ).app F :=
  Equiv.apply_symm_apply _ _

/-- A transition is induced by presheaf restriction along every total-category arrow.

In case (A), take its mate under the specified topos adjunction and evaluate the resulting
direct-image map. In case (B), also take the mate under the right Kan extension adjunction to
evaluate on the source site. In both cases the resulting map must be the actual presheaf
restriction, transported through the specified sheafification units. -/
def IsRestrictionTransition (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    (τ : S.fiberRestriction m ⋙ (S.transitionMorphism φ).inverseImage ⟶
      S.fiberRestriction n) : Prop :=
  match S with
  | ⟨Sum.inl C⟩ =>
    ∀ (F : Sheaf (totalTopology ⟨Sum.inl C⟩) (Type u))
      (U : C.underlying.obj n) (V : C.underlying.obj m)
      (f : U ⟶ (C.underlying.map φ).toFunctor.obj V),
      (fiberRestrictionUnit ⟨Sum.inl C⟩ F m).app (Opposite.op V) ≫
        (((transitionMorphism ⟨Sum.inl C⟩ φ).adj.homEquiv
          _ _) (τ.app F)).hom.app (Opposite.op V) ≫
        ((fiberRestriction ⟨Sum.inl C⟩ n).obj F).obj.map f.op =
      F.obj.map (continuousTotalArrow C φ f).op ≫
        (fiberRestrictionUnit ⟨Sum.inl C⟩ F n).app (Opposite.op U)
  | ⟨Sum.inr C⟩ =>
    ∀ (F : Sheaf (totalTopology ⟨Sum.inr C⟩) (Type u))
      (U : C.underlying.obj (Opposite.op n)) (V : C.underlying.obj (Opposite.op m))
      (f : (C.underlying.map φ.op).toFunctor.obj U ⟶ V),
      (fiberRestrictionUnit ⟨Sum.inr C⟩ F m).app (Opposite.op V) ≫
        ((fiberRestriction ⟨Sum.inr C⟩ m).obj F).obj.map f.op ≫
        ((((C.underlying.map φ.op).toFunctor.op.ranAdjunction (Type u)).homEquiv _ _).symm
          ((((transitionMorphism ⟨Sum.inr C⟩ φ).adj.homEquiv
            _ _) (τ.app F)).hom)).app (Opposite.op U) =
      F.obj.map (cocontinuousTotalArrow C φ f).op ≫
        (fiberRestrictionUnit ⟨Sum.inr C⟩ F n).app (Opposite.op U)

/-- Fibre restrictions are sheaves, and their transitions are fixed by actual restriction along
arrows of the total site. The equations use only the site data and its specified adjunctions. -/
structure FiberRestrictionData (S : SimplicialSiteSituation.{u}) where
  /-- The raw presheaf restriction of a sheaf on the total site is a sheaf on the component. -/
  restriction_isSheaf (F : Sheaf S.totalTopology (Type u)) (n : SimplexCategory) :
    Presheaf.IsSheaf (S.componentTopology n) ((S.inclusion n).op ⋙ F.obj)
  /-- The transition on fibre restrictions. -/
  transition {m n : SimplexCategory} (φ : m ⟶ n) :
    S.fiberRestriction m ⋙ (S.transitionMorphism φ).inverseImage ⟶ S.fiberRestriction n
  /-- Its adjoint is the presheaf restriction map along every total-category arrow. -/
  transition_restriction {m n : SimplexCategory} (φ : m ⟶ n) :
    S.IsRestrictionTransition φ (transition φ)

/-- The sheafification unit cancels against the backward identification. -/
theorem fiberRestrictionUnit_comp_inv (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)
    (F : Sheaf S.totalTopology (Type u)) (X : (S.component n)ᵒᵖ) :
    (S.fiberRestrictionUnit F n).app X ≫
      ((S.restrictIsoFiberRestriction n).inv.app F).hom.app X = 𝟙 _ := by
  rw [restrictIsoFiberRestriction_inv_app_hom]
  exact (isoSheafify (S.componentTopology n) (S.restrict_isSheaf n F)).hom_inv_id_app X

/-- In case (A) the direct image is precomposition with the site functor, so the forward
identification is the sheafification unit of the target degree. -/
theorem pushforward_inl_restrictIso_hom_app (C : SimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    (F : Sheaf (totalTopology ⟨Sum.inl C⟩) (Type u)) (V : C.underlying.obj m) :
    ((transitionMorphism ⟨Sum.inl C⟩ φ).pushforward.map
        ((restrictIsoFiberRestriction ⟨Sum.inl C⟩ n).hom.app F)).hom.app (Opposite.op V) =
      (fiberRestrictionUnit (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) F n).app
        (Opposite.op ((C.underlying.map φ).toFunctor.obj V)) := rfl

/-- In case (B) the direct image is the right Kan extension along the site functor. -/
theorem pushforward_inr_restrictIso_hom (C : CocontinuousSimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    (F : Sheaf (totalTopology ⟨Sum.inr C⟩) (Type u)) :
    ((transitionMorphism ⟨Sum.inr C⟩ φ).pushforward.map
        ((restrictIsoFiberRestriction ⟨Sum.inr C⟩ n).hom.app F)).hom =
      (C.underlying.map φ.op).toFunctor.op.ran.map
        (fiberRestrictionUnit (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) F n) := rfl

/-- The shape of the case (A) restriction equation, in abstract morphisms: a cancelling pair,
a naturality square and an arrow identity. -/
private theorem restriction_equation_inl_aux {D : Type*} [Category D]
    {A B X Y Z T : D} {u : A ⟶ B} {i : B ⟶ A} {t : A ⟶ X} {v : X ⟶ Y} {r : Y ⟶ Z}
    {n₁ : X ⟶ T} {s : T ⟶ Z} {m₁ : A ⟶ T}
    (hui : u ≫ i = 𝟙 A) (hnat : n₁ ≫ s = v ≫ r) (harr : t ≫ n₁ = m₁) :
    u ≫ (i ≫ t ≫ v) ≫ r = m₁ ≫ s := by
  calc u ≫ (i ≫ t ≫ v) ≫ r = (u ≫ i) ≫ t ≫ v ≫ r := by simp
    _ = t ≫ v ≫ r := by rw [hui, Category.id_comp]
    _ = t ≫ n₁ ≫ s := by rw [hnat]
    _ = m₁ ≫ s := by rw [← Category.assoc, harr]

/-- The mate of a triple composite whose last factor is a direct image. -/
private theorem homEquiv_symm_triple {E₁ E₂ : Type*} [Category E₁] [Category E₂]
    {L : E₁ ⥤ E₂} {R : E₂ ⥤ E₁} (adj : L ⊣ R) {A B : E₁} {Y Y' : E₂}
    (a : A ⟶ B) (b : B ⟶ R.obj Y) (d : Y ⟶ Y') :
    (adj.homEquiv A Y').symm (a ≫ b ≫ R.map d) =
      L.map a ≫ (adj.homEquiv B Y).symm b ≫ d := by
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm]

/-- The shape of the case (B) restriction equation, in abstract morphisms. -/
private theorem restriction_equation_inr_aux {D : Type*} [Category D]
    {A B X E T Z : D} {p : A ⟶ B} {q : B ⟶ X} {i : X ⟶ E} {sb : E ⟶ T} {s : T ⟶ Z}
    {pm : A ⟶ E} {um : E ⟶ X} {m₁ : A ⟶ T}
    (hui : um ≫ i = 𝟙 E) (hnat : pm ≫ um = p ≫ q) (harr : pm ≫ sb = m₁) :
    p ≫ q ≫ i ≫ sb ≫ s = m₁ ≫ s := by
  calc p ≫ q ≫ i ≫ sb ≫ s = (p ≫ q) ≫ i ≫ sb ≫ s := by simp
    _ = (pm ≫ um) ≫ i ≫ sb ≫ s := by rw [hnat]
    _ = pm ≫ (um ≫ i) ≫ sb ≫ s := by simp
    _ = pm ≫ sb ≫ s := by rw [hui, Category.id_comp]
    _ = m₁ ≫ s := by rw [← Category.assoc, harr]

/-- Case (A) of the restriction equations for `inverseImageFiberTransition`. -/
theorem inverseImageFiberTransition_restriction_inl (C : SimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    IsRestrictionTransition ⟨Sum.inl C⟩ φ (inverseImageFiberTransition ⟨Sum.inl C⟩ φ) := by
  intro F U V f
  rw [inverseImageFiberTransition_adj, fiberRestrictTransition_app_hom]
  simp only [NatTrans.comp_app, pushforward_inl_restrictIso_hom_app]
  exact restriction_equation_inl_aux
    (fiberRestrictionUnit_comp_inv (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) m F (Opposite.op V))
    ((fiberRestrictionUnit (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) F n).naturality f.op)
    (restrictTransition_inl_arrow C φ F f)

/-- Case (B) of the restriction equations for `inverseImageFiberTransition`. -/
theorem inverseImageFiberTransition_restriction_inr (C : CocontinuousSimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    IsRestrictionTransition ⟨Sum.inr C⟩ φ (inverseImageFiberTransition ⟨Sum.inr C⟩ φ) := by
  intro F U V f
  rw [inverseImageFiberTransition_adj, fiberRestrictTransition_app_hom,
    pushforward_inr_restrictIso_hom]
  refine (congrArg (fun t =>
      (fiberRestrictionUnit (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) F m).app (Opposite.op V) ≫
        ((fiberRestriction (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) m).obj F).obj.map f.op ≫
          NatTrans.app t (Opposite.op U))
    (homEquiv_symm_triple ((C.underlying.map φ.op).toFunctor.op.ranAdjunction (Type u))
      (((restrictIsoFiberRestriction (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) m).inv.app
        F).hom)
      (((restrictTransition (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app F).hom)
      (fiberRestrictionUnit (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) F n))).trans ?_
  exact restriction_equation_inr_aux
    (fiberRestrictionUnit_comp_inv (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) m F
      (Opposite.op ((C.underlying.map φ.op).toFunctor.obj U)))
    ((fiberRestrictionUnit (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) F m).naturality f.op)
    (restrictTransition_inr_arrow C φ F f)

/-- **Stacks Project, Tag 09WF.** The fibre restrictions of a sheaf on the total site of a
simplicial site, together with their specified transitions. -/
@[stacks 09WF "fibre restrictions and their specified transitions"]
noncomputable def fiberRestrictionData (S : SimplicialSiteSituation.{u}) :
    FiberRestrictionData S where
  restriction_isSheaf F n := S.restrict_isSheaf n F
  transition φ := S.inverseImageFiberTransition φ
  transition_restriction {m n} φ := by
    rcases S with ⟨C | C⟩
    · exact inverseImageFiberTransition_restriction_inl C φ
    · exact inverseImageFiberTransition_restriction_inr C φ

/-- Every component of the sheafification unit of a fibre restriction is an isomorphism. -/
instance isIso_fiberRestrictionUnit_app (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)
    (F : Sheaf S.totalTopology (Type u)) (X : (S.component n)ᵒᵖ) :
    IsIso ((S.fiberRestrictionUnit F n).app X) := by
  change IsIso ((isoSheafify (S.componentTopology n) (S.restrict_isSheaf n F)).hom.app X)
  infer_instance

/-- The restriction equations determine the transition uniquely: it suffices to test them on
the identity arrows of the total category, where the sheafification unit is an epimorphism. -/
theorem IsRestrictionTransition.ext (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    (τ σ : S.fiberRestriction m ⋙ (S.transitionMorphism φ).inverseImage ⟶ S.fiberRestriction n)
    (hτ : S.IsRestrictionTransition φ τ) (hσ : S.IsRestrictionTransition φ σ) : τ = σ := by
  rcases S with ⟨C | C⟩
  · apply NatTrans.ext
    funext F
    apply ((transitionMorphism (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).adj.homEquiv
      _ _).injective
    apply (sheafToPresheaf _ _).map_injective
    apply NatTrans.ext
    funext V
    refine (cancel_epi
      ((fiberRestrictionUnit (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) F m).app V)).1 ?_
    have h := (hτ F ((C.underlying.map φ).toFunctor.obj V.unop) V.unop (𝟙 _)).trans
      (hσ F ((C.underlying.map φ).toFunctor.obj V.unop) V.unop (𝟙 _)).symm
    erw [Functor.map_id, Category.comp_id, Category.comp_id] at h
    exact h
  · apply NatTrans.ext
    funext F
    apply ((transitionMorphism (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).adj.homEquiv
      _ _).injective
    apply (sheafToPresheaf _ _).map_injective
    apply ((((C.underlying.map φ.op).toFunctor.op.ranAdjunction (Type u)).homEquiv
      _ _).symm).injective
    apply NatTrans.ext
    funext U
    refine (cancel_epi
      ((fiberRestrictionUnit (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) F m).app
        (Opposite.op ((C.underlying.map φ.op).toFunctor.obj U.unop)))).1 ?_
    have h := (hτ F U.unop ((C.underlying.map φ.op).toFunctor.obj U.unop) (𝟙 _)).trans
      (hσ F U.unop ((C.underlying.map φ.op).toFunctor.obj U.unop) (𝟙 _)).symm
    erw [Functor.map_id, Category.id_comp, Category.id_comp] at h
    exact h

/-- The adjoint of the fibre transition is the restriction of the original presheaf along every
arrow `(φ, f)` of the total category, in both cases of Situation 09WE. -/
theorem inverseImageFiberTransition_restriction (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    S.IsRestrictionTransition φ (S.inverseImageFiberTransition φ) :=
  (S.fiberRestrictionData).transition_restriction φ

end SimplicialSiteSituation

end CategoryTheory

end
