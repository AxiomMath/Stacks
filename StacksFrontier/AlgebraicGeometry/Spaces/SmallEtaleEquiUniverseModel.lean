module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSmallModel
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFilteredColimitsSections

/-!
# An equi-universe model of the small étale ringed site of an algebraic space

`AlgebraicGeometry.Space.smallEtaleRingedSite` is an
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`: its objects lie one universe above its morphisms.
The small étale site is essentially small at the universe of its schemes
(`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`), so it has a model whose objects and
morphisms both lie in `Type u`. This file builds that model as a ringed site, transports the
structure sheaf to it, and exhibits the `𝒪_X`-modules of `AlgebraicGeometry.Space.Modules` as
equivalent to the sheaves of modules on the model.

## Main definitions

* `AlgebraicGeometry.Space.SmallEtaleModel`, `AlgebraicGeometry.Space.smallEtaleModelTopology`
  and `AlgebraicGeometry.Space.smallEtaleModelRingedSite`: the small étale site of an algebraic
  space transported to a model in `Type u`, as an `AlgebraicGeometry.RingedSite.{u, u, u}`.

## Main results

* `Stacks.SheafOfModules.SiteTransport.isFinitePresentation_modulesEquivalence`: reindexing along
  an equivalence of sites preserves finite presentation.
* `Stacks.SheafOfModules.SiteTransport.preservesColimitsOfShape_coyoneda_of_equivalence`: an
  equivalence of categories carries preservation of colimits by `Hom(G, -)` from one side to the
  other, across the universe gap between the two hom types.
* `AlgebraicGeometry.Space.modulesEquivModelModules`: the `𝒪_X`-modules of an algebraic space
  are the sheaves of modules on the equi-universe model of its small étale ringed site.
* `AlgebraicGeometry.Space.preservesColimitsOfShape_coyoneda_of_model`: `Hom_X(G, -)` commutes
  with colimits of a given shape as soon as its transport to the model does.
* `AlgebraicGeometry.Space.preservesColimitsOfShape_coyoneda_of_isFinitePresentation_model`: if
  the transport of `G` to the model is of finite presentation and the model site satisfies the
  condition of Stacks 0GMR part (4), then `Hom_X(G, -)` commutes with filtered colimits.

## Implementation notes

On a site with objects in `Type u₁` and morphisms in `Type v₁`, the sections of the internal Hom
sheaf `Hom_O(F, G)` lie in `Type (max u₁ v₁ …)`, so internal Hom is an endofunctor of the
category of modules only at module universes at least `max u₁ v₁`. For the small étale site this
is `u + 1`, while the modules of `AlgebraicGeometry.Space.Modules.{u, u}` have sections in
`Type u`; on the model, `max u₁ v₁ = u`.

The underlying categories of the two sites have different hom universes, so an equivalence
between their module categories relates a `Type (u + 1)`-valued and a `Type u`-valued Hom
functor; `Stacks.SheafOfModules.SiteTransport.coyonedaUliftIsoOfEquivalence` inserts the lift.

The sheaf of rings of `AlgebraicGeometry.Space.smallEtaleModelRingedSite` is, by `rfl`, the
transport of the sheaf of rings of `AlgebraicGeometry.Space.smallEtaleRingedSite`
(`AlgebraicGeometry.Space.ringSheaf_smallEtaleModelRingedSite`).

## References

* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
* [Stacks Project, Tag 0GMZ](https://stacks.math.columbia.edu/tag/0GMZ)
* [Stacks Project, Tag 0GN0](https://stacks.math.columbia.edu/tag/0GN0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules.SiteTransport

section Transport

universe w m u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}

variable (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{w})

end Transport

/-! ### Finite presentation across an equivalence of sites -/

section FinitePresentation

universe w u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}

/-- Localizing an equivalence of sites at an object gives an equivalence of the localized
sites. -/
instance overPostTransport_isDenseSubsite (e : C' ≌ C) [e.inverse.IsDenseSubsite J J']
    (V : C') :
    (Over.post (X := V) e.functor).IsDenseSubsite (J'.over V) (J.over (e.functor.obj V)) where
  functorPushforward_mem_iff := by
    intro X T
    rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff,
      Sieve.overEquiv_functorPushforward_post]
    exact e.functor.functorPushforward_mem_iff J' J

variable {R : Sheaf J RingCat.{w}} {S : Sheaf J' RingCat.{w}}
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{w}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ X : C', HasSheafify (J'.over X) AddCommGrpCat.{w}]
  [∀ X : C', (J'.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Direct image along a continuous and cocontinuous left adjoint preserves finite
presentation. -/
theorem isFinitePresentation_pushforward (G : C' ⥤ C) [G.IsContinuous J' J]
    [G.IsCocontinuous J' J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{w} J' J).obj R)
    (η : (SheafOfModules.pushforward φ).obj (SheafOfModules.unit R) ≅ SheafOfModules.unit S)
    [G.IsLeftAdjoint] [IsIso φ] [HasPullbacks C] [HasPullbacks C']
    [∀ X : C', (Over.post (X := X) G).IsContinuous (J'.over X) (J.over _)]
    (M : SheafOfModules.{w} R) [M.IsFinitePresentation] :
    ((SheafOfModules.pushforward φ).obj M).IsFinitePresentation := by
  have h : ∀ (X : C') (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{w, w} <|
      SheafOfModules.pushforward.{w} (R := (R.over Y)) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{w} (J'.over X) J').map φ) := by
    intro X Y f
    have _ : (Over.post (X := X) G ⋙ Over.map f).IsContinuous (J'.over X) (J.over Y) :=
      Functor.isContinuous_comp _ _ _ (J.over _) _
    have _ : (Over.post (X := X) G ⋙ Over.map f).IsCocontinuous (J'.over X) (J.over Y) :=
      isCocontinuous_comp _ _ _ (J.over _)
    let a : S.over X ⟶ ((Over.post (X := X) G ⋙ Over.map f).sheafPushforwardContinuous
        RingCat.{w} (J'.over X) (J.over Y)).obj (R.over Y) :=
      ((Over.forget X).sheafPushforwardContinuous RingCat.{w} (J'.over X) J').map φ
    have _ : IsIso a := inferInstanceAs
      (IsIso (((Over.forget X).sheafPushforwardContinuous RingCat.{w} (J'.over X) J').map φ))
    have _ : (SheafOfModules.pushforward.{w} a).IsLeftAdjoint :=
      SheafOfModules.isLeftAdjoint_pushforward_of_isIso a
    infer_instance
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  have _ := hσ
  have _ : (σ.pushforward G φ η h).IsFinitePresentation := by
    refine ⟨fun i => ⟨⟨?_⟩, ⟨?_⟩⟩⟩
    · exact SheafOfModules.GeneratingSections.IsFiniteType.finite
        (σ := (σ.presentation i.2.1).generators)
    · exact SheafOfModules.GeneratingSections.IsFiniteType.finite
        (σ := (σ.presentation i.2.1).relations)
  exact ⟨(σ.pushforward G φ η h).shrink, inferInstance⟩

/-- The reindexing `Stacks.SheafOfModules.reindexEquivalence` of a module of finite
presentation along an equivalence of sites is again of finite presentation. -/
theorem isFinitePresentation_modulesEquivalence (J' : GrothendieckTopology C') (e : C' ≌ C)
    [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
    [e.inverse.IsDenseSubsite J J'] [HasPullbacks C] [HasPullbacks C']
    [∀ X : C', HasSheafify (J'.over X) AddCommGrpCat.{w}]
    [∀ X : C', (J'.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (M : SheafOfModules.{w} R) [M.IsFinitePresentation] :
    ((Stacks.SheafOfModules.reindexEquivalence.{w} (J' := J') e R).functor.obj
      M).IsFinitePresentation :=
  isFinitePresentation_pushforward e.functor
    (𝟙 (Stacks.SheafOfModules.reindexRing J' e R)) (Iso.refl _) M

end FinitePresentation

/-! ### Hom out of a fixed object across an equivalence -/

section Coyoneda

universe a b x y k

variable {A : Type x} [Category.{max a b} A] {D : Type y} [Category.{b} D]

/-- For an equivalence `E : A ≌ D` the functor `Hom_A(G, -)` is `E` followed by
`Hom_D(E G, -)` followed by the universe lift. -/
noncomputable def coyonedaUliftIsoOfEquivalence (E : A ≌ D) (G : A) :
    coyoneda.obj (Opposite.op G) ≅
      E.functor ⋙ coyoneda.obj (Opposite.op (E.functor.obj G)) ⋙ uliftFunctor.{a, b} :=
  NatIso.ofComponents
    (fun X => Equiv.toIso
      { toFun := fun f => ULift.up (E.functor.map f)
        invFun := fun f => E.functor.preimage f.down
        left_inv := fun f => E.functor.preimage_map f
        right_inv := fun f => ULift.ext (E.functor.map_preimage f.down) })
    (fun {X Y} g => by
      ext f
      exact ULift.ext (E.functor.map_comp f g))

/-- Preservation of colimits by `Hom(G, -)` transports across an equivalence. -/
theorem preservesColimitsOfShape_coyoneda_of_equivalence (E : A ≌ D) (G : A) (K : Type k)
    [Category.{k} K]
    [PreservesColimitsOfShape K (coyoneda.obj (Opposite.op (E.functor.obj G)))] :
    PreservesColimitsOfShape K (coyoneda.obj (Opposite.op G)) := by
  have _ : PreservesColimitsOfShape K E.functor :=
    (E.toAdjunction.leftAdjoint_preservesColimits).preservesColimitsOfShape
  have _ : PreservesColimitsOfShape K
      (E.functor ⋙ coyoneda.obj (Opposite.op (E.functor.obj G)) ⋙ uliftFunctor.{a, b}) :=
    inferInstance
  exact preservesColimitsOfShape_of_natIso (coyonedaUliftIsoOfEquivalence E G).symm

end Coyoneda

end Stacks.SheafOfModules.SiteTransport

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- A model of the small étale site of `F` whose objects lie in the universe `u` of the
schemes, where the small étale site itself has objects in `Type (u + 1)`. -/
abbrev SmallEtaleModel : Type u := SmallModel.{u} (SmallEtale B S hS F)

/-- The equivalence between the model and the small étale site of `F`. -/
noncomputable def smallEtaleModelEquivalence :
    SmallEtaleModel B S hS F ≌ SmallEtale B S hS F where
  functor := (equivSmallModel.{u} (SmallEtale B S hS F)).inverse
  inverse := (equivSmallModel.{u} (SmallEtale B S hS F)).functor
  unitIso := (equivSmallModel.{u} (SmallEtale B S hS F)).counitIso.symm
  counitIso := (equivSmallModel.{u} (SmallEtale B S hS F)).unitIso.symm
  functor_unitIso_comp _ := by simp

/-- The topology on the model induced from the small étale topology of `F`. -/
noncomputable abbrev smallEtaleModelTopology : GrothendieckTopology (SmallEtaleModel B S hS F) :=
  RingedTopos.smallModelTopology (SmallEtale.topology B S hS F)

/-- The functor of the model equivalence is continuous for the model topology and the small
étale topology. -/
instance smallEtaleModelEquivalence_functor_isContinuous :
    (smallEtaleModelEquivalence B S hS F).functor.IsContinuous
      (smallEtaleModelTopology B S hS F) (SmallEtale.topology B S hS F) :=
  inferInstanceAs ((equivSmallModel.{u} (SmallEtale B S hS F)).inverse.IsContinuous _ _)

/-- The inverse of the model equivalence is continuous for the small étale topology and the
model topology. -/
instance smallEtaleModelEquivalence_inverse_isContinuous :
    (smallEtaleModelEquivalence B S hS F).inverse.IsContinuous
      (SmallEtale.topology B S hS F) (smallEtaleModelTopology B S hS F) :=
  inferInstanceAs ((equivSmallModel.{u} (SmallEtale B S hS F)).functor.IsContinuous _ _)

/-- The continuity of the model equivalence, restated for the topology of
`AlgebraicGeometry.Space.smallEtaleRingedSite`. -/
instance smallEtaleRingedSite_functor_isContinuous (hF : IsAlgebraicSpace B S hS F) :
    (smallEtaleModelEquivalence B S hS F).functor.IsContinuous
      (smallEtaleModelTopology B S hS F) (smallEtaleRingedSite B S hS F hF).J := by
  change (smallEtaleModelEquivalence B S hS F).functor.IsContinuous
    (smallEtaleModelTopology B S hS F) (SmallEtale.topology B S hS F)
  infer_instance

/-- The continuity of the inverse of the model equivalence, restated for the topology of
`AlgebraicGeometry.Space.smallEtaleRingedSite`. -/
instance smallEtaleRingedSite_inverse_isContinuous (hF : IsAlgebraicSpace B S hS F) :
    (smallEtaleModelEquivalence B S hS F).inverse.IsContinuous
      (smallEtaleRingedSite B S hS F hF).J (smallEtaleModelTopology B S hS F) := by
  change (smallEtaleModelEquivalence B S hS F).inverse.IsContinuous
    (SmallEtale.topology B S hS F) (smallEtaleModelTopology B S hS F)
  infer_instance

/-- The inverse of the model equivalence exhibits the small étale site as a dense subsite of
its model. -/
instance smallEtaleModelEquivalence_inverse_isDenseSubsite :
    (smallEtaleModelEquivalence B S hS F).inverse.IsDenseSubsite
      (SmallEtale.topology B S hS F) (smallEtaleModelTopology B S hS F) :=
  inferInstanceAs ((equivSmallModel.{u} (SmallEtale B S hS F)).functor.IsDenseSubsite _ _)

/-- The equi-universe model of the small étale ringed site of the algebraic space `F`: the
model site with the direct image of the structure sheaf, an `AlgebraicGeometry.RingedSite` whose
objects, morphisms and sections all lie in `Type u`. -/
noncomputable def smallEtaleModelRingedSite (hF : IsAlgebraicSpace B S hS F) :
    RingedSite.{u, u, u} where
  C := SmallEtaleModel B S hS F
  J := smallEtaleModelTopology B S hS F
  O := RingedTopos.smallModelStructureSheaf (SmallEtale.topology B S hS F)
    (structureSheaf B S hS F hF)

/-- The continuity of the model equivalence, restated for the topology of
`AlgebraicGeometry.Space.smallEtaleModelRingedSite`. -/
instance smallEtaleModelRingedSite_functor_isContinuous (hF : IsAlgebraicSpace B S hS F) :
    (smallEtaleModelEquivalence B S hS F).functor.IsContinuous
      (smallEtaleModelRingedSite B S hS F hF).J (smallEtaleRingedSite B S hS F hF).J := by
  change (smallEtaleModelEquivalence B S hS F).functor.IsContinuous
    (smallEtaleModelTopology B S hS F) (SmallEtale.topology B S hS F)
  infer_instance

/-- The continuity of the inverse of the model equivalence, restated for the topology of
`AlgebraicGeometry.Space.smallEtaleModelRingedSite`. -/
instance smallEtaleModelRingedSite_inverse_isContinuous (hF : IsAlgebraicSpace B S hS F) :
    (smallEtaleModelEquivalence B S hS F).inverse.IsContinuous
      (smallEtaleRingedSite B S hS F hF).J (smallEtaleModelRingedSite B S hS F hF).J := by
  change (smallEtaleModelEquivalence B S hS F).inverse.IsContinuous
    (SmallEtale.topology B S hS F) (smallEtaleModelTopology B S hS F)
  infer_instance

/-- The sheaf of rings of the model is, on the nose, the transport of the sheaf of rings of the
small étale ringed site. -/
theorem ringSheaf_smallEtaleModelRingedSite (hF : IsAlgebraicSpace B S hS F) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS F hF).O) =
      Stacks.SheafOfModules.reindexRing
        (smallEtaleModelTopology B S hS F) (smallEtaleModelEquivalence B S hS F)
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) :=
  rfl

/-- The `𝒪_F`-modules of an algebraic space are equivalent to the sheaves of modules on the
equi-universe model of its small étale ringed site. -/
noncomputable def modulesEquivModelModules (hF : IsAlgebraicSpace B S hS F) :
    Modules.{u, u} B S hS F hF ≌
      SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS F hF).O) :=
  Stacks.SheafOfModules.reindexEquivalence (smallEtaleModelEquivalence B S hS F)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)

/-- `Hom_F(G, -)` commutes with colimits of a given shape as soon as its transport to the
equi-universe model does. -/
theorem preservesColimitsOfShape_coyoneda_of_model (hF : IsAlgebraicSpace B S hS F)
    (G : Modules.{u, u} B S hS F hF) (K : Type u) [Category.{u} K]
    [PreservesColimitsOfShape K
      (coyoneda.obj (Opposite.op ((modulesEquivModelModules B S hS F hF).functor.obj G)))] :
    PreservesColimitsOfShape K (coyoneda.obj (Opposite.op G)) :=
  Stacks.SheafOfModules.SiteTransport.preservesColimitsOfShape_coyoneda_of_equivalence.{u + 1, u,
    u + 1, u + 1, u} (modulesEquivModelModules B S hS F hF) G K

/-- If the transport of `G` to the equi-universe model is of finite presentation, and the model
site carries a set of sheaves as in Stacks 0GMR part (4), then `Hom_F(G, -)` commutes with
filtered colimits of `𝒪_F`-modules. -/
theorem preservesColimitsOfShape_coyoneda_of_isFinitePresentation_model
    (hF : IsAlgebraicSpace B S hS F) (G : Modules.{u, u} B S hS F hF)
    (hG : ((modulesEquivModelModules B S hS F hF).functor.obj G).IsFinitePresentation)
    (K : Type u) [Category.{u} K] [IsFiltered K]
    (hX : ∃ T : Set (Sheaf (smallEtaleModelRingedSite B S hS F hF).J (Type u)),
      (∀ H : Sheaf (smallEtaleModelRingedSite B S hS F hF).J (Type u),
          Sheaf.IsLocallySurjective (terminal.from H) →
            ∃ L ∈ T, Nonempty (L ⟶ H) ∧ Sheaf.IsLocallySurjective (terminal.from L)) ∧
        ∀ L ∈ T, Sheaf.IsQuasiCompact (L ⨯ L)) :
    PreservesColimitsOfShape K (coyoneda.obj (Opposite.op G)) :=
  have _ := hG
  have _ : PreservesColimitsOfShape K (coyoneda.obj
      (Opposite.op ((modulesEquivModelModules B S hS F hF).functor.obj G))) :=
    Stacks.SheafOfModules.InternalHom.coyoneda_preservesColimitsOfShape_of_isFinitePresentation
      (smallEtaleModelRingedSite B S hS F hF) _ K hX
  preservesColimitsOfShape_coyoneda_of_model B S hS F hF G K

end AlgebraicGeometry.Space

end
