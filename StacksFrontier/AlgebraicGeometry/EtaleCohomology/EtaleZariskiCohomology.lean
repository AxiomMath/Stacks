module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ZariskiRefinement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteSheafCohomology

/-!
# Étale and Zariski cohomology of a scheme with strictly henselian local rings

Let `S` be a scheme all of whose local rings are strictly henselian. Then étale cohomology of
an abelian sheaf on the small étale site of `S` agrees in every degree with Zariski cohomology
of its restriction to the open subschemes of `S`.

## Main definitions

* `AlgebraicGeometry.zariskiPushforward` — the direct image `ε_*` for the morphism of sites
  `ε : S_étale ⟶ S_Zariski`, as the sheaf pushforward along the continuous functor
  `AlgebraicGeometry.opensToEtale`.
* `AlgebraicGeometry.etaleZariskiCohomologyIso` — the comparison of the two cohomology functors
  at the common morphism universe of the two sheaf categories.
* `AlgebraicGeometry.etaleZariskiSheafHAddEquiv` — the comparison at an arbitrary `Ext` universe.

## Main results

* `AlgebraicGeometry.isTerminal_opensToEtale_top` — the whole scheme, read as an open subscheme,
  is a final object of the small étale site.
* `AlgebraicGeometry.zariskiPushforward_preservesFiniteColimits` — `ε_*` is right exact when all
  local rings of `S` are strictly henselian.
* `AlgebraicGeometry.zariskiPushforward_preservesInjectiveObjects` — `ε_*` preserves injective
  abelian sheaves, with no hypothesis on the local rings.

## References

* [Stacks Project, Tag 09AX](https://stacks.math.columbia.edu/tag/09AX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe w u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-! ### Finite limits of open subschemes inside the small étale site -/

/-- The intersection of two open subschemes, with its two inclusions, as a cone over any cospan
of open subschemes. -/
public def opensInfPullbackCone {U V W : S.Opens} (f : U ⟶ W) (g : V ⟶ W) : PullbackCone f g :=
  PullbackCone.mk (homOfLE inf_le_left : U ⊓ V ⟶ U)
    (homOfLE inf_le_right : U ⊓ V ⟶ V) (Subsingleton.elim _ _)

/-- The intersection of two open subschemes is their fibre product. -/
public def isLimitOpensInfPullbackCone {U V W : S.Opens} (f : U ⟶ W) (g : V ⟶ W) :
    IsLimit (opensInfPullbackCone f g) :=
  PullbackCone.IsLimit.mk _ (fun s => homOfLE (le_inf (s.fst).le (s.snd).le))
    (fun _ => Subsingleton.elim _ _) (fun _ => Subsingleton.elim _ _)
    (fun _ _ _ _ => Subsingleton.elim _ _)

/-- The intersection of two open subschemes is their fibre product in the small étale site. -/
public def isLimitMapOpensInfPullbackCone {U V W : S.Opens} (f : U ⟶ W) (g : V ⟶ W) :
    IsLimit ((opensToEtale S).mapCone (opensInfPullbackCone f g)) := by
  refine (PullbackCone.isLimitMapConeEquiv (opensInfPullbackCone f g) (opensToEtale S)).2 ?_
  refine PullbackCone.IsLimit.mk _ (fun s => homToOpensToEtale s.pt (U ⊓ V) ?_)
    (fun _ => Subsingleton.elim _ _) (fun _ => Subsingleton.elim _ _)
    (fun _ _ _ _ => Subsingleton.elim _ _)
  simpa only [Opens.coe_inf] using Set.subset_inter (range_subset_of_hom_opensToEtale s.fst)
    (range_subset_of_hom_opensToEtale s.snd)

/-- `AlgebraicGeometry.opensToEtale` preserves fibre products. -/
public instance opensToEtale_preservesLimitsOfShape_walkingCospan :
    PreservesLimitsOfShape WalkingCospan (opensToEtale S) where
  preservesLimit {K} := by
    have : PreservesLimit
        (cospan (K.map WalkingCospan.Hom.inl) (K.map WalkingCospan.Hom.inr))
        (opensToEtale S) :=
      preservesLimit_of_preserves_limit_cone (isLimitOpensInfPullbackCone _ _)
        (isLimitMapOpensInfPullbackCone _ _)
    exact preservesLimit_of_iso_diagram _ (diagramIsoCospan K).symm

/-- The identity of an open subscheme, as a fork of any parallel pair out of it. -/
public def opensIdFork {U V : S.Opens} (f g : U ⟶ V) : Fork f g :=
  Fork.ofι (𝟙 U) (Subsingleton.elim _ _)

/-- An open subscheme is the equalizer of any parallel pair out of it. -/
public def isLimitOpensIdFork {U V : S.Opens} (f g : U ⟶ V) : IsLimit (opensIdFork f g) :=
  Fork.IsLimit.mk _ (fun s => s.ι) (fun _ => Subsingleton.elim _ _)
    (fun _ _ _ => Subsingleton.elim _ _)

/-- The image under `AlgebraicGeometry.opensToEtale` of the identity fork of a parallel pair of
open subschemes is an equalizer in the small étale site. -/
public def isLimitMapOpensIdFork {U V : S.Opens} (f g : U ⟶ V) :
    IsLimit ((opensToEtale S).mapCone (opensIdFork f g)) := by
  refine (isLimitMapConeForkEquiv (opensToEtale S)
      (show (𝟙 U) ≫ f = (𝟙 U) ≫ g from Subsingleton.elim _ _)).symm
    (Fork.IsLimit.mk _ (fun s => s.ι) (fun s => ?_) (fun s m _ => ?_))
  all_goals exact @Subsingleton.elim _ (subsingleton_hom_opensToEtale _ U) _ _

/-- `AlgebraicGeometry.opensToEtale` preserves equalizers. -/
public instance opensToEtale_preservesLimitsOfShape_walkingParallelPair :
    PreservesLimitsOfShape WalkingParallelPair (opensToEtale S) where
  preservesLimit {K} := by
    have : PreservesLimit
        (parallelPair (K.map WalkingParallelPairHom.left) (K.map WalkingParallelPairHom.right))
        (opensToEtale S) :=
      preservesLimit_of_preserves_limit_cone (isLimitOpensIdFork _ _) (isLimitMapOpensIdFork _ _)
    exact preservesLimit_of_iso_diagram _ (diagramIsoParallelPair K).symm

/-- The whole scheme, read as an open subscheme, is a final object of the small étale site. -/
public def isTerminal_opensToEtale_top (S : Scheme.{u}) :
    IsTerminal ((opensToEtale S).obj ⊤) :=
  IsTerminal.ofUnique (h := fun W =>
    ⟨⟨homToOpensToEtale W ⊤ (by simp)⟩, fun _ => Subsingleton.elim _ _⟩)

/-! ### The direct image along `ε` and its exactness -/

variable (S)

/-- The direct image `ε_*` for the morphism of sites `ε : S_étale ⟶ S_Zariski`, as the sheaf
pushforward along the continuous functor `AlgebraicGeometry.opensToEtale`. -/
public abbrev zariskiPushforward :
    Sheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{u + 1} :=
  (opensToEtale S).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology S) (Scheme.smallEtaleTopology S)

/-- The direct image `ε_*` preserves finite colimits when every local ring of `S` is strictly
henselian. -/
public theorem zariskiPushforward_preservesFiniteColimits
    (hlocal : ∀ x : S, StrictlyHenselianLocalRing ↥(S.presheaf.stalk x))
    [HasSheafify (Opens.grothendieckTopology S) AddCommGrpCat.{u + 1}] :
    PreservesFiniteColimits (zariskiPushforward S) := by
  have := isCocontinuous_opensToEtale S hlocal
  exact Stacks.Cohomology.BiggerSite.preservesFiniteColimits_sheafPushforwardContinuous
    (Opens.grothendieckTopology S) (Scheme.smallEtaleTopology S) (opensToEtale S)
    AddCommGrpCat.{u + 1}

/-- The direct image `ε_*` preserves injective abelian sheaves. -/
public theorem zariskiPushforward_preservesInjectiveObjects
    [HasSheafify (Opens.grothendieckTopology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}] :
    (zariskiPushforward S).PreservesInjectiveObjects :=
  Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous
    (Opens.grothendieckTopology S) (Scheme.smallEtaleTopology S) (opensToEtale S)

/-! ### The comparison of cohomology -/

variable [HasSheafify (Opens.grothendieckTopology S) AddCommGrpCat.{u + 1}]
  [HasSheafify (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1})]
  [HasInjectiveResolutions (Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{u + 1})]
  [HasInjectiveResolutions (Sheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1})]

/-- For a scheme all of whose local rings are strictly henselian, étale cohomology in degree `p`
agrees with Zariski cohomology of the restriction to the open subschemes, naturally in the
abelian sheaf, with `Ext` groups in the morphism universe `u + 1` of the two sheaf categories. -/
public def etaleZariskiCohomologyIso
    (hlocal : ∀ x : S, StrictlyHenselianLocalRing ↥(S.presheaf.stalk x)) (p : ℕ) :
    zariskiPushforward S ⋙ Sheaf.functorH (Opens.grothendieckTopology S) p ≅
      Sheaf.functorH (Scheme.smallEtaleTopology S) p :=
  have : PreservesFiniteColimits (zariskiPushforward S) :=
    zariskiPushforward_preservesFiniteColimits S hlocal
  have : (zariskiPushforward S).PreservesInjectiveObjects :=
    zariskiPushforward_preservesInjectiveObjects S
  have : (zariskiPushforward S).IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (opensToEtale S)
      AddCommGrpCat.{u + 1} (Opens.grothendieckTopology S)
      (Scheme.smallEtaleTopology S)).isRightAdjoint
  have : (zariskiPushforward S).Additive := Functor.additive_of_preserves_binary_products _
  have : (Functor.sheafPullbackConstruction.sheafPullback (opensToEtale S)
      AddCommGrpCat.{u + 1} (Opens.grothendieckTopology S)
      (Scheme.smallEtaleTopology S)).Additive :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (opensToEtale S)
      AddCommGrpCat.{u + 1} (Opens.grothendieckTopology S)
      (Scheme.smallEtaleTopology S)).left_adjoint_additive
  (Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (opensToEtale S)
        AddCommGrpCat.{u + 1} (Opens.grothendieckTopology S) (Scheme.smallEtaleTopology S))
      ((Stacks.Cohomology.BiggerSite.constantSheafCompSheafPullbackIso
        (Opens.grothendieckTopology S) (Scheme.smallEtaleTopology S) (opensToEtale S)
        AddCommGrpCat.{u + 1} isTerminalTop (isTerminal_opensToEtale_top S) rfl).app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) p).symm

variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1})]

/-- Let `S` be a scheme all of whose local rings are strictly henselian. Then
for every abelian sheaf `F` on the small étale site of `S` and every degree `p`, étale cohomology
`H^p(S_étale, F)` agrees with Zariski cohomology `H^p(S_Zariski, ε_* F)` of its restriction to
the open subschemes of `S`. -/
@[stacks 09AX]
public def etaleZariskiSheafHAddEquiv
    (hlocal : ∀ x : S, StrictlyHenselianLocalRing ↥(S.presheaf.stalk x))
    (F : Sheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}) (p : ℕ) :
    Sheaf.H.{w, u + 1} F p ≃+ Sheaf.H.{w, u + 1} ((zariskiPushforward S).obj F) p :=
  (Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv.{w, u + 1}).trans
    ((((etaleZariskiCohomologyIso S hlocal p).symm.app F).addCommGroupIsoToAddEquiv).trans
      Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv.{u + 1, w})

end AlgebraicGeometry

end
