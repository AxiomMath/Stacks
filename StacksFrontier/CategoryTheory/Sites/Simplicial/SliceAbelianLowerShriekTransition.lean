module

public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointCompIsoTrans
public import StacksFrontier.CategoryTheory.Sites.PushforwardContinuousCalculus
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianSections
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSheafify
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceAbelianLowerShriek

/-!
# Extension by zero from a simplicial slice, along the simplicial structure

Let `(C, J)` be a site and `K` a simplicial object of `SR(C)`.
`CategoryTheory.SimplicialSemiRepresentable.componentLowerShriekCompAugmentationAbelianIso`
identifies, in each simplicial degree `p`, the composite `a_! g_{p!}` of the two extensions by
zero — from the component of degree `p` into the total site, then along the augmentation — with
the extension by zero `j_{p!}` along the localization functor `j_p : C/K_p ⥤ C`. This file proves
that the identification is compatible with the simplicial structure.

For a simplex map `φ : m ⟶ n` the transition functor `r_φ : C/K_n ⥤ C/K_m` is continuous, so it
too has an extension by zero `r_{φ!}` on abelian sheaves, and `r_φ ⋙ j_m = j_n` gives
`r_{φ!} j_{m!} ≅ j_{n!}`. The compatibility says that the square formed by that comparison, the
two degreewise identifications, and the comparison `r_{φ!} a_! g_{m!} ≅ a_! g_{n!}` of the two
composites through the total site, commutes.

This is the shriek counterpart of
`CategoryTheory.SimplicialSemiRepresentable.componentPushforwardIso_transitionPushforwardIso`,
which is the same compatibility for the direct images of Stacks 0D8B.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.componentTransitionFunctor`: the transition functor
  `r_φ`, spelled with source and target the components of the simplicial-site situation.
* `CategoryTheory.SimplicialSemiRepresentable.transitionAbelianLowerShriek` and
  `.transitionAbelianLowerShriekAdjunction`: the extension by zero `r_{φ!}` and its adjunction.
* `CategoryTheory.SimplicialSemiRepresentable.sliceAbelianLowerShriekCompIso`:
  `r_{φ!} j_{m!} ≅ j_{n!}`.
* `CategoryTheory.SimplicialSemiRepresentable.augmentationTransitionAbelianLowerShriekIso`:
  `r_{φ!} a_! g_{m!} ≅ a_! g_{n!}`, the shriek counterpart of
  `CategoryTheory.SimplicialSiteSituation.Augmentation.transitionPushforwardIso`.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.augmentationTransitionRestrictionIso_cocycle`: the
  cocycle on the *restrictions*.
* `CategoryTheory.SimplicialSemiRepresentable`
  `.componentLowerShriekCompAugmentationAbelianIso_transition`: **the compatibility.**

## References

* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
* [Stacks Project, Tag 09WM](https://stacks.math.columbia.edu/tag/09WM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory

universe w vA v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]
  {T : Type u₃} [Category.{v₃} T] {Z : Type u₄} [Category.{v₄} Z]

/-- The comparison `sheafPushforwardContinuousComp'` along `Iso.refl` is the canonical one. -/
private theorem sheafPushforwardContinuousComp'_refl {S U V : Type*} [Category S] [Category U]
    [Category V] (J : GrothendieckTopology S) (K : GrothendieckTopology U)
    (L : GrothendieckTopology V) (A : Type w) [Category.{vA} A] (g : S ⥤ U) (a : U ⥤ V)
    [g.IsContinuous J K] [a.IsContinuous K L] [(g ⋙ a).IsContinuous J L] :
    Functor.sheafPushforwardContinuousComp' (Iso.refl (g ⋙ a)) A J K L =
      Functor.sheafPushforwardContinuousComp g a A J K L :=
  Iso.ext (by rw [Functor.sheafPushforwardContinuousComp'_refl_hom]; rfl)

/-- **The cocycle for the comparisons of restriction functors.** Let `r`, `g`, `g'`, `a` be
continuous site functors with `g ⋙ a = jm`, `g' ⋙ a = jn` and `r ⋙ jm = jn`. Restricting along
`r` the comparison `a^{-1} g^{-1} ≅ jm^{-1}` and then comparing with `jn^{-1}` is the comparison
of the two triple composites followed by the comparison `a^{-1} g'^{-1} ≅ jn^{-1}`. -/
theorem Functor.sheafPushforwardContinuousComp'_eqToIso_cocycle
    (Jx : GrothendieckTopology X) (Jy : GrothendieckTopology Y)
    (Jt : GrothendieckTopology T) (Jz : GrothendieckTopology Z)
    (A : Type w) [Category.{vA} A]
    {r : X ⥤ Y} {g : Y ⥤ T} {g' : X ⥤ T} {a : T ⥤ Z} {jm : Y ⥤ Z} {jn : X ⥤ Z}
    [r.IsContinuous Jx Jy] [g.IsContinuous Jy Jt] [g'.IsContinuous Jx Jt]
    [a.IsContinuous Jt Jz] [jm.IsContinuous Jy Jz] [jn.IsContinuous Jx Jz]
    [(g ⋙ a).IsContinuous Jy Jz] [(g' ⋙ a).IsContinuous Jx Jz]
    (hm : g ⋙ a = jm) (hn : g' ⋙ a = jn) (hsl : r ⋙ jm = jn)
    (hτ : r ⋙ (g ⋙ a) = g' ⋙ a) :
    Functor.isoWhiskerRight (Functor.sheafPushforwardContinuousComp' (eqToIso hm) A Jy Jt Jz)
          (r.sheafPushforwardContinuous A Jx Jy) ≪≫
        Functor.sheafPushforwardContinuousComp' (eqToIso hsl) A Jx Jy Jz =
      (Functor.isoWhiskerRight (Functor.sheafPushforwardContinuousComp g a A Jy Jt Jz)
            (r.sheafPushforwardContinuous A Jx Jy) ≪≫
          Functor.sheafPushforwardContinuousComp' (eqToIso hτ) A Jx Jy Jz ≪≫
            (Functor.sheafPushforwardContinuousComp g' a A Jx Jt Jz).symm) ≪≫
        Functor.sheafPushforwardContinuousComp' (eqToIso hn) A Jx Jt Jz := by
  subst hm
  subst hn
  rw [eqToIso_refl, eqToIso_refl, sheafPushforwardContinuousComp'_refl,
    sheafPushforwardContinuousComp'_refl, Iso.trans_assoc, Iso.trans_assoc, Iso.symm_self_id,
    Iso.trans_refl]

end CategoryTheory

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]

/-! ### The transition functor and its extension by zero -/

/-- The transition functor `r_φ : C/K_n ⥤ C/K_m` of a simplex map `φ : m ⟶ n`, with source and
target spelled as the components of the simplicial-site situation of `K`. This is
`componentOverMap (K.map φ.op)`. -/
def componentTransitionFunctor {m n : SimplexCategory} (φ : m ⟶ n) :
    ((situation J K).component n : Cat.{u, u}) ⥤ ((situation J K).component m : Cat.{u, u}) :=
  componentOverMap (K.map φ.op)

/-- The transition functor of `φ` is `componentOverMap (K.map φ.op)`. -/
theorem componentTransitionFunctor_eq {m n : SimplexCategory} (φ : m ⟶ n) :
    componentTransitionFunctor J K φ = componentOverMap (K.map φ.op) := rfl

/-- **Stacks 0D85.** The transition functor of a simplex map is continuous for the component
topologies. -/
instance componentTransitionFunctor_isContinuous {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentTransitionFunctor J K φ).IsContinuous ((situation J K).componentTopology n)
      ((situation J K).componentTopology m) :=
  componentOverMap_isContinuous' J K φ

/-- Relocalizing along a simplex map and then localizing is localizing: `r_φ ⋙ j_m = j_n`. -/
theorem componentTransitionFunctor_comp_sliceForget {m n : SimplexCategory} (φ : m ⟶ n) :
    componentTransitionFunctor J K φ ⋙ sliceForget K (op m) = sliceForget K (op n) :=
  slicesMap_comp_sliceForget K φ.op

/-- The transition functor of a simplex map followed by the component inclusion of the target
degree and the localization functor of the total site is the component inclusion of the source
degree followed by that localization functor: both composites of site functors are `j_n`. -/
theorem componentTransitionFunctor_comp_componentFunctor_comp_totalForget
    {m n : SimplexCategory} (φ : m ⟶ n) :
    componentTransitionFunctor J K φ ⋙
        (SimplicialSiteSituation.componentFunctor (situation J K) m ⋙ totalForget K) =
      SimplicialSiteSituation.componentFunctor (situation J K) n ⋙ totalForget K :=
  (congrArg (fun F => componentTransitionFunctor J K φ ⋙ F)
        (componentFunctor_comp_totalForget J K m)).trans
    ((componentTransitionFunctor_comp_sliceForget J K φ).trans
      (componentFunctor_comp_totalForget J K n).symm)

/-- The extension by zero `r_{φ!} : Ab(C/K_n) ⥤ Ab(C/K_m)` along the transition functor
`r_φ : C/K_n ⥤ C/K_m` of a simplex map `φ : m ⟶ n`: the sheaf pullback of abelian sheaves along
`r_φ`, that is the left Kan extension along `r_φ` followed by sheafification. -/
def transitionAbelianLowerShriek {m n : SimplexCategory} (φ : m ⟶ n) :
    Sheaf ((situation J K).componentTopology n) AddCommGrpCat.{u} ⥤
      Sheaf ((situation J K).componentTopology m) AddCommGrpCat.{u} :=
  Functor.sheafPullbackConstruction.sheafPullback (componentTransitionFunctor J K φ)
    AddCommGrpCat.{u} ((situation J K).componentTopology n)
    ((situation J K).componentTopology m)

/-- The extension by zero `r_{φ!}` is left adjoint to the inverse image `r_φ^{-1}`, which is
restriction along `r_φ`. -/
def transitionAbelianLowerShriekAdjunction {m n : SimplexCategory} (φ : m ⟶ n) :
    transitionAbelianLowerShriek J K φ ⊣
      (componentTransitionFunctor J K φ).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology n) ((situation J K).componentTopology m) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentTransitionFunctor J K φ)
    AddCommGrpCat.{u} ((situation J K).componentTopology n)
    ((situation J K).componentTopology m)

/-! ### The comparisons of restrictions -/

/-- The comparison `j_m^{-1} r_φ^{-1} ≅ j_n^{-1}` of restrictions along the factorization
`r_φ ⋙ j_m = j_n` of the localization functor of degree `n`. -/
def sliceAbelianRestrictionCompIso {m n : SimplexCategory} (φ : m ⟶ n) :
    (sliceForget K (op m)).sheafPushforwardContinuous AddCommGrpCat.{u}
          ((situation J K).componentTopology m) J ⋙
        (componentTransitionFunctor J K φ).sheafPushforwardContinuous AddCommGrpCat.{u}
          ((situation J K).componentTopology n) ((situation J K).componentTopology m) ≅
      (sliceForget K (op n)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology n) J :=
  haveI := sliceForget_isContinuous_component J K m
  haveI := sliceForget_isContinuous_component J K n
  Functor.sheafPushforwardContinuousComp'
    (eqToIso (componentTransitionFunctor_comp_sliceForget J K φ)) AddCommGrpCat.{u}
    ((situation J K).componentTopology n) ((situation J K).componentTopology m) J

/-- The comparison `a^{-1} g_p^{-1} ≅ j_p^{-1}` of restrictions along the factorization
`g_p ⋙ j_total = j_p`. -/
def componentAugmentationRestrictionIso (p : SimplexCategory) :
    (totalForget K).sheafPushforwardContinuous AddCommGrpCat.{u}
          ((situation J K).totalTopology) J ⋙
        (SimplicialSiteSituation.componentFunctor (situation J K) p).sheafPushforwardContinuous
          AddCommGrpCat.{u} ((situation J K).componentTopology p)
          ((situation J K).totalTopology) ≅
      (sliceForget K (op p)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology p) J :=
  haveI := totalForget_isContinuous_totalCategory J K
  haveI := sliceForget_isContinuous_component J K p
  Functor.sheafPushforwardContinuousComp' (eqToIso (componentFunctor_comp_totalForget J K p))
    AddCommGrpCat.{u} ((situation J K).componentTopology p)
    ((situation J K).totalTopology) J

/-- `componentLowerShriekCompAugmentationAbelianIso` is the comparison of left adjoints which
uniqueness of a left adjoint builds from `componentAugmentationRestrictionIso`. -/
theorem componentLowerShriekCompAugmentationAbelianIso_eq (p : SimplexCategory) :
    componentLowerShriekCompAugmentationAbelianIso J K p =
      Adjunction.leftAdjointCompIso
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (SimplicialSiteSituation.componentFunctor (situation J K) p) AddCommGrpCat.{u}
          ((situation J K).componentTopology p) ((situation J K).totalTopology))
        (augmentationAbelianLowerShriekAdjunction J K)
        (sliceAbelianLowerShriekAdjunction J K p)
        (componentAugmentationRestrictionIso J K p) :=
  rfl

/-- Continuity of `g_p ⋙ j_total`, which is `j_p`. -/
theorem componentFunctor_comp_totalForget_isContinuous (p : SimplexCategory) :
    (SimplicialSiteSituation.componentFunctor (situation J K) p ⋙
      totalForget K).IsContinuous ((situation J K).componentTopology p) J :=
  (componentFunctor_comp_totalForget J K p) ▸ sliceForget_isContinuous_component J K p

/-- The comparison `a^{-1} g_m^{-1} r_φ^{-1} ≅ a^{-1} g_n^{-1}` of restrictions, along the
equality of site functors `r_φ ⋙ g_m ⋙ j_total = g_n ⋙ j_total`: both composites are `j_n`. -/
def augmentationTransitionRestrictionIso {m n : SimplexCategory} (φ : m ⟶ n) :
    ((totalForget K).sheafPushforwardContinuous AddCommGrpCat.{u}
            ((situation J K).totalTopology) J ⋙
          (SimplicialSiteSituation.componentFunctor (situation J K) m).sheafPushforwardContinuous
            AddCommGrpCat.{u} ((situation J K).componentTopology m)
            ((situation J K).totalTopology)) ⋙
        (componentTransitionFunctor J K φ).sheafPushforwardContinuous AddCommGrpCat.{u}
          ((situation J K).componentTopology n) ((situation J K).componentTopology m) ≅
      (totalForget K).sheafPushforwardContinuous AddCommGrpCat.{u}
          ((situation J K).totalTopology) J ⋙
        (SimplicialSiteSituation.componentFunctor (situation J K) n).sheafPushforwardContinuous
          AddCommGrpCat.{u} ((situation J K).componentTopology n)
          ((situation J K).totalTopology) :=
  haveI := totalForget_isContinuous_totalCategory J K
  haveI := componentFunctor_comp_totalForget_isContinuous J K m
  haveI := componentFunctor_comp_totalForget_isContinuous J K n
  Functor.isoWhiskerRight
      (Functor.sheafPushforwardContinuousComp
        (SimplicialSiteSituation.componentFunctor (situation J K) m) (totalForget K)
        AddCommGrpCat.{u} ((situation J K).componentTopology m)
        ((situation J K).totalTopology) J)
      ((componentTransitionFunctor J K φ).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology n) ((situation J K).componentTopology m)) ≪≫
    Functor.sheafPushforwardContinuousComp'
        (eqToIso (componentTransitionFunctor_comp_componentFunctor_comp_totalForget J K φ))
        AddCommGrpCat.{u} ((situation J K).componentTopology n)
        ((situation J K).componentTopology m) J ≪≫
      (Functor.sheafPushforwardContinuousComp
        (SimplicialSiteSituation.componentFunctor (situation J K) n) (totalForget K)
        AddCommGrpCat.{u} ((situation J K).componentTopology n)
        ((situation J K).totalTopology) J).symm

/-! ### The two comparisons of extensions by zero, and the compatibility -/

/-- **The extensions by zero along the localization functors compose.** The extension by zero
`r_{φ!}` of a simplex transition followed by the extension by zero `j_{m!}` of the target degree
is the extension by zero `j_{n!}` of the source degree, the three site functors satisfying
`r_φ ⋙ j_m = j_n`. -/
def sliceAbelianLowerShriekCompIso {m n : SimplexCategory} (φ : m ⟶ n) :
    transitionAbelianLowerShriek J K φ ⋙ sliceAbelianLowerShriek J K m ≅
      sliceAbelianLowerShriek J K n :=
  Adjunction.leftAdjointCompIso (transitionAbelianLowerShriekAdjunction J K φ)
    (sliceAbelianLowerShriekAdjunction J K m) (sliceAbelianLowerShriekAdjunction J K n)
    (sliceAbelianRestrictionCompIso J K φ)

/-- **The composites through the total site are compatible with the simplicial structure.** The
extension by zero `r_{φ!}` of a simplex transition followed by `a_! g_{m!}` is `a_! g_{n!}`. -/
def augmentationTransitionAbelianLowerShriekIso {m n : SimplexCategory} (φ : m ⟶ n) :
    transitionAbelianLowerShriek J K φ ⋙
        (SimplicialSiteSituation.componentLowerShriekAb (situation J K) m ⋙
          augmentationAbelianLowerShriek J K) ≅
      SimplicialSiteSituation.componentLowerShriekAb (situation J K) n ⋙
        augmentationAbelianLowerShriek J K :=
  Adjunction.leftAdjointCompIso (transitionAbelianLowerShriekAdjunction J K φ)
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (SimplicialSiteSituation.componentFunctor (situation J K) m) AddCommGrpCat.{u}
        ((situation J K).componentTopology m) ((situation J K).totalTopology)).comp
      (augmentationAbelianLowerShriekAdjunction J K))
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (SimplicialSiteSituation.componentFunctor (situation J K) n) AddCommGrpCat.{u}
        ((situation J K).componentTopology n) ((situation J K).totalTopology)).comp
      (augmentationAbelianLowerShriekAdjunction J K))
    (augmentationTransitionRestrictionIso J K φ)

/-- **The cocycle on the restrictions.** Restricting along `r_φ` the comparison of degree `m`
and then comparing with `j_n^{-1}` is comparing the two factorizations of `j_n` through the total
site and then using the comparison of degree `n`. -/
theorem augmentationTransitionRestrictionIso_cocycle {m n : SimplexCategory} (φ : m ⟶ n) :
    Functor.isoWhiskerRight (componentAugmentationRestrictionIso J K m)
          ((componentTransitionFunctor J K φ).sheafPushforwardContinuous AddCommGrpCat.{u}
            ((situation J K).componentTopology n) ((situation J K).componentTopology m)) ≪≫
        sliceAbelianRestrictionCompIso J K φ =
      augmentationTransitionRestrictionIso J K φ ≪≫
        componentAugmentationRestrictionIso J K n := by
  have := totalForget_isContinuous_totalCategory J K
  have := sliceForget_isContinuous_component J K m
  have := sliceForget_isContinuous_component J K n
  have := componentFunctor_comp_totalForget_isContinuous J K m
  have := componentFunctor_comp_totalForget_isContinuous J K n
  exact Functor.sheafPushforwardContinuousComp'_eqToIso_cocycle
    ((situation J K).componentTopology n) ((situation J K).componentTopology m)
    ((situation J K).totalTopology) J AddCommGrpCat.{u}
    (componentFunctor_comp_totalForget J K m) (componentFunctor_comp_totalForget J K n)
    (componentTransitionFunctor_comp_sliceForget J K φ)
    (componentTransitionFunctor_comp_componentFunctor_comp_totalForget J K φ)

/-- **The identification of `a_! g_{p!}` with `j_{p!}` is compatible with the simplicial
structure.** For a simplex map `φ : m ⟶ n`, extending by zero along `r_φ` the identification of
degree `m` and then composing the two extensions along the localization functors is the
comparison of the two composites through the total site followed by the identification of
degree `n`. -/
theorem componentLowerShriekCompAugmentationAbelianIso_transition
    {m n : SimplexCategory} (φ : m ⟶ n) :
    Functor.isoWhiskerLeft (transitionAbelianLowerShriek J K φ)
          (componentLowerShriekCompAugmentationAbelianIso J K m) ≪≫
        sliceAbelianLowerShriekCompIso J K φ =
      augmentationTransitionAbelianLowerShriekIso J K φ ≪≫
        componentLowerShriekCompAugmentationAbelianIso J K n := by
  rw [componentLowerShriekCompAugmentationAbelianIso_eq J K m,
    componentLowerShriekCompAugmentationAbelianIso_eq J K n]
  exact Stacks.CategoryTheory.leftAdjointCompIso_isoWhiskerLeft_trans
    (transitionAbelianLowerShriekAdjunction J K φ)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (SimplicialSiteSituation.componentFunctor (situation J K) m) AddCommGrpCat.{u}
      ((situation J K).componentTopology m) ((situation J K).totalTopology))
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (SimplicialSiteSituation.componentFunctor (situation J K) n) AddCommGrpCat.{u}
      ((situation J K).componentTopology n) ((situation J K).totalTopology))
    (augmentationAbelianLowerShriekAdjunction J K)
    (sliceAbelianLowerShriekAdjunction J K m) (sliceAbelianLowerShriekAdjunction J K n)
    (componentAugmentationRestrictionIso J K m) (sliceAbelianRestrictionCompIso J K φ)
    (augmentationTransitionRestrictionIso J K φ) (componentAugmentationRestrictionIso J K n)
    (augmentationTransitionRestrictionIso_cocycle J K φ)

end CategoryTheory.SimplicialSemiRepresentable

end
