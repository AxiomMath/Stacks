module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentPushforwardSections
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationPushforwardComparison
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentedMorphism
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalMorphismOfTopoi

/-!
# The square of total topoi of a morphism of augmented simplicial sites

Let `h` be a morphism between simplicial sites as in Stacks 0D95, let `a`, `a'` be augmentations
of its source and target towards sites `D`, `D'` as in Stacks 0D6Z, and let
`h_{-1} : Sh(D) → Sh(D')` be a morphism of topoi compatible with `h`, `a`, `a'` as in Stacks
0D98. Then the square formed by the morphism of total topoi `h_total` of Stacks 0D96, the total
augmentations `a`, `a'` of Stacks 0D70 and `h_{-1}` commutes. Both cases of the situation are
treated.

## Main results

* `CategoryTheory.SimplicialSite.Morphism.totalComponentSiteFunctor_comp_totalFunctor`: in case
  (A), the functors from the augmentation sites into the total categories attached to a simplicial
  degree commute with the functor between the total categories and the functor between the
  augmentation sites.
* `CategoryTheory.SimplicialSite.Morphism.totalAugmentationPushforwardIso`: the square in case
  (A).
* `CategoryTheory.SimplicialSiteMorphism.totalAugmentationPushforwardIso`: **Stacks 0D99**, the
  square in both cases.

## Implementation notes

The source writes an equality of morphisms of topoi. Since composition of the associated sheaf
functors is only canonical up to isomorphism, the square is expressed, as for Tags 0D96 and 0D98,
by a natural isomorphism of direct-image functors.

The total augmentation is the morphism of topoi of Stacks 0D70 that is uniform in the two cases:
its direct image is the limit over the simplex category of the direct images along the
augmentations of the degrees of the restrictions to the degrees.

In case (A) every functor involved is a direct image along a continuous site functor, that is,
a restriction of sections. In simplicial degree `n` the two composites around the square are
restriction along two functors from `D'` into the total category of `C`, and these are equal: the
degreewise functor `h_n` commutes with the component inclusions and with the vertex functors, and
in degree zero the compatibility of `h_{-1}` is the hypothesis of Stacks 0D98. This is the
reduction of the source to the degreewise squares, and the degree-zero square. The resulting
identifications are compatible with the cosimplicial structure, because on sections that structure
is restriction along the cartesian arrows of the total category (Stacks 0D70, compatibility (3)),
which the functor between the total categories preserves. Taking limits, and using that the
direct image along `h_{-1}` preserves them, gives the square.

In case (B) the square is the one of the cocontinuous total functors,
`CategoryTheory.CocontinuousSimplicialSite.Morphism.totalAugmentationPushforwardIso`, transported
along the identification of the two constructions of the total augmentation,
`CategoryTheory.CocontinuousSimplicialSite.Augmentation.totalPushforwardIso`.

## References

* [Stacks Project, Tag 0D99](https://stacks.math.columbia.edu/tag/0D99)
* [Stacks Project, Tag 0D98](https://stacks.math.columbia.edu/tag/0D98)
* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite

universe u

namespace CategoryTheory

namespace SimplicialSite.Morphism

attribute [local implicit_reducible] CategoryTheory.SimplicialSite.totalPseudofunctor
  CategoryTheory.Functor.toPseudofunctor' CategoryTheory.pseudofunctorOfIsLocallyDiscrete
  Quiver.Hom.toLoc

variable {C C' : SimplicialSite.{u}} {D D' : Cat.{u, u}} {K : GrothendieckTopology D}
  {K' : GrothendieckTopology D'}

open SimplicialSiteSituation.Augmentation in
/-- In case (A), the functor from the augmentation site of the target into the total category of
the target attached to a simplicial degree, followed by the functor between the total categories,
is the functor between the augmentation sites followed by the functor attached to that degree for
the source, as soon as the two agree in degree zero. -/
theorem totalComponentSiteFunctor_comp_totalFunctor (h : SimplicialSite.Morphism C C')
    (a : C.ContinuousAugmentation D K) (a' : C'.ContinuousAugmentation D' K') (v : D' ⥤ D)
    (hv : v ⋙ a.functor = a'.functor ⋙ (h.hom.app (SimplexCategory.mk 0)).toFunctor)
    (n : SimplexCategory) :
    a'.totalComponentSiteFunctor n ⋙ h.totalFunctor = v ⋙ a.totalComponentSiteFunctor n := by
  let c := SimplexCategory.const (SimplexCategory.mk 0) n 0
  have hnat : (C'.underlying.map c).toFunctor ⋙ (h.hom.app n).toFunctor =
      (h.hom.app (SimplexCategory.mk 0)).toFunctor ⋙ (C.underlying.map c).toFunctor :=
    congrArg Cat.Hom.toFunctor (h.hom.naturality c)
  have hι := h.ι_comp_totalFunctor (op n)
  change ((a'.functor ⋙ (C'.underlying.map c).toFunctor) ⋙
      CoGrothendieck.ι C'.totalPseudofunctor (op n)) ⋙ h.totalFunctor =
    v ⋙ ((a.functor ⋙ (C.underlying.map c).toFunctor) ⋙
      CoGrothendieck.ι C.totalPseudofunctor (op n))
  rw [Functor.assoc, hι]
  change a'.functor ⋙ (C'.underlying.map c).toFunctor ⋙ (h.hom.app n).toFunctor ⋙
      CoGrothendieck.ι C.totalPseudofunctor (op n) = _
  rw [← Functor.assoc (C'.underlying.map c).toFunctor, hnat, Functor.assoc,
    ← Functor.assoc a'.functor, ← hv]
  rfl

open SimplicialSiteSituation.Augmentation in
/-- In case (A), the direct image along the functor between the total categories followed by the
direct image along the augmentation of a simplicial degree of the target is the direct image along
the augmentation of that degree of the source followed by the direct image along the functor
between the augmentation sites. -/
def componentAugmentationPushforwardSquareIso (h : SimplicialSite.Morphism C C')
    (a : C.ContinuousAugmentation D K) (a' : C'.ContinuousAugmentation D' K') (v : D' ⥤ D)
    (hv' : v.IsMorphismOfSites K' K)
    (hv : v ⋙ a.functor = a'.functor ⋙ (h.hom.app (SimplexCategory.mk 0)).toFunctor)
    (n : SimplexCategory) :
    h.totalMorphism.pushforward ⋙ (cosimplicialPushforward C'.situation D' K' a').obj n ≅
      (cosimplicialPushforward C.situation D K a).obj n ⋙ hv'.morphismOfTopoi.pushforward :=
  letI : v.IsContinuous K' K := hv'.isContinuous
  letI : (a'.totalComponentSiteFunctor n ⋙ h.totalFunctor).IsContinuous K' C.totalTopology :=
    Functor.isContinuous_comp _ _ K' C'.totalTopology C.totalTopology
  letI : (v ⋙ a.totalComponentSiteFunctor n).IsContinuous K' C.totalTopology :=
    Functor.isContinuous_comp _ _ K' K C.totalTopology
  Functor.sheafPushforwardContinuousIso
    (eqToIso (h.totalComponentSiteFunctor_comp_totalFunctor a a' v hv n)) (Type u) K'
    C.totalTopology

open SimplicialSiteSituation.Augmentation in
/-- In case (A), the degreewise identifications `componentAugmentationPushforwardSquareIso` are
compatible with the cosimplicial structure of the direct images along the augmentations of the
degrees. -/
theorem componentAugmentationPushforwardSquareIso_naturality (h : SimplicialSite.Morphism C C')
    (a : C.ContinuousAugmentation D K) (a' : C'.ContinuousAugmentation D' K') (v : D' ⥤ D)
    (hv' : v.IsMorphismOfSites K' K)
    (hv : v ⋙ a.functor = a'.functor ⋙ (h.hom.app (SimplexCategory.mk 0)).toFunctor)
    {m n : SimplexCategory} (φ : m ⟶ n) (F : Sheaf C.totalTopology (Type u)) :
    ((cosimplicialPushforward C'.situation D' K' a').map φ).app
          (h.totalMorphism.pushforward.obj F) ≫
        (h.componentAugmentationPushforwardSquareIso a a' v hv' hv n).hom.app F =
      (h.componentAugmentationPushforwardSquareIso a a' v hv' hv m).hom.app F ≫
        hv'.morphismOfTopoi.pushforward.map
          (((cosimplicialPushforward C.situation D K a).map φ).app F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext X
  have e₁ := a'.componentPushforwardTransition_app_hom_app φ (h.totalMorphism.pushforward.obj F)
    (unop X)
  have e₂ := a.componentPushforwardTransition_app_hom_app φ F (v.obj (unop X))
  have E := h.totalComponentSiteFunctor_comp_totalFunctor a a' v hv
  have e : ∀ k : SimplexCategory, (a.componentSiteFunctor k).obj (v.obj (unop X)) =
      (h.hom.app k).toFunctor.obj ((a'.componentSiteFunctor k).obj (unop X)) := fun k =>
    (congrArg (C.underlying.map (SimplexCategory.const (SimplexCategory.mk 0) k 0)).toFunctor.obj
      (Functor.congr_obj hv (unop X))).trans
      (h.app_obj_map (SimplexCategory.const (SimplexCategory.mk 0) k 0)
        (a'.functor.obj (unop X))).symm
  have hκ : ∀ k : SimplexCategory, (eqToIso (E k)).inv.app (unop X) =
      (CoGrothendieck.ι C.totalPseudofunctor (op k)).map (eqToHom (e k)) :=
    fun k => by
      simp only [eqToIso.inv, eqToHom_app, eqToHom_map]
      rfl
  have hpush : ∀ {P Q : (CoGrothendieck C'.totalPseudofunctor)ᵒᵖ} (f : P ⟶ Q),
      (h.totalMorphism.pushforward.obj F).obj.map f = F.obj.map (h.totalFunctor.map f.unop).op :=
    fun _ => rfl
  let Q' := (a'.componentSiteFunctor m).obj (unop X)
  have h₂ : h.totalFunctor.map
      ((SimplicialSiteSituation.continuousInclusionTransition C' φ).app Q') =
      (CoGrothendieck.ι C.totalPseudofunctor (op n)).map (eqToHom (h.app_obj_map φ Q')) ≫
        (SimplicialSiteSituation.continuousInclusionTransition C φ).app
          ((h.hom.app m).toFunctor.obj Q') := by
    refine Eq.trans ?_ (CoGrothendieck.ι_map_comp_ιNatTrans_app C.totalPseudofunctor φ.op
      (eqToHom (h.app_obj_map φ Q'))).symm
    refine CoGrothendieck.Hom.ext _ _ rfl ?_
    refine (congrArg (· ≫ eqToHom _) ((h.hom.app n).toFunctor.map_id _)).trans ?_
    exact (Category.id_comp _).trans (eqToHom_trans (h.app_obj_map φ Q') _).symm
  change ((componentPushforwardTransition C'.situation D' K' a' φ).app
      (h.totalMorphism.pushforward.obj F)).hom.app (op (unop X)) ≫
      F.obj.map (((eqToIso (E n)).inv.app (unop X)).op) =
    F.obj.map (((eqToIso (E m)).inv.app (unop X)).op) ≫
      ((componentPushforwardTransition C.situation D K a φ).app F).hom.app (op (v.obj (unop X)))
  rw [e₁, e₂, hpush]
  refine ((F.obj.map_comp _ _).symm.trans ?_).trans (F.obj.map_comp _ _)
  refine congrArg F.obj.map (op_comp.symm.trans (Eq.trans (congrArg Quiver.Hom.op ?_) op_comp))
  refine (congrArg₂ (· ≫ ·) (hκ n) rfl).trans (Eq.trans ?_ (congrArg₂ (· ≫ ·) rfl (hκ m)).symm)
  let A := (a.componentSiteFunctor m).obj (v.obj (unop X))
  have key : (CoGrothendieck.ι C.totalPseudofunctor (op n)).map (eqToHom (e n)) ≫
      (CoGrothendieck.ι C.totalPseudofunctor (op n)).map ((h.hom.app n).toFunctor.map
          (eqToHom (Functor.congr_obj (a'.componentSiteFunctor_comp_eq φ) (unop X)).symm)) ≫
        (CoGrothendieck.ι C.totalPseudofunctor (op n)).map (eqToHom (h.app_obj_map φ Q')) ≫
          (SimplicialSiteSituation.continuousInclusionTransition C φ).app
            ((h.hom.app m).toFunctor.obj Q') =
      ((CoGrothendieck.ι C.totalPseudofunctor (op n)).map
          (eqToHom (Functor.congr_obj (a.componentSiteFunctor_comp_eq φ) (v.obj (unop X))).symm) ≫
        (SimplicialSiteSituation.continuousInclusionTransition C φ).app A) ≫
        (CoGrothendieck.ι C.totalPseudofunctor (op m)).map (eqToHom (e m)) := by
    have hnat := (SimplicialSiteSituation.continuousInclusionTransition C φ).naturality
      (eqToHom (e m))
    simp only [Functor.comp_map] at hnat
    rw [Category.assoc, ← hnat]
    simp only [← Category.assoc, ← Functor.map_comp]
    congr 2
    simp [eqToHom_map]
  rw [Quiver.Hom.unop_op, Functor.map_comp, h.ι_map_totalFunctor, h₂]
  exact key

open SimplicialSiteSituation.Augmentation in
/-- In case (A), the square formed by the morphism of total topoi of a morphism between simplicial
sites, the total augmentations of the source and the target, and the morphism of the augmentation
topoi given by a morphism of sites compatible with the two augmentations in degree zero commutes,
as witnessed by a natural isomorphism of direct-image functors. -/
def totalAugmentationPushforwardIso (h : SimplicialSite.Morphism C C')
    (a : C.ContinuousAugmentation D K) (a' : C'.ContinuousAugmentation D' K') (v : D' ⥤ D)
    (hv' : v.IsMorphismOfSites K' K)
    (hv : v ⋙ a.functor = a'.functor ⋙ (h.hom.app (SimplexCategory.mk 0)).toFunctor) :
    h.totalMorphism.pushforward ⋙ (totalMorphismOfTopoi C'.situation D' K' a').pushforward ≅
      (totalMorphismOfTopoi C.situation D K a).pushforward ⋙ hv'.morphismOfTopoi.pushforward :=
  haveI : PreservesLimitsOfShape SimplexCategory hv'.morphismOfTopoi.pushforward :=
    hv'.morphismOfTopoi.adj.rightAdjoint_preservesLimits.preservesLimitsOfShape
  let Θ : h.totalMorphism.pushforward ⋙ (cosimplicialPushforward C'.situation D' K' a').flip ≅
      (cosimplicialPushforward C.situation D K a).flip ⋙
        (Functor.whiskeringRight SimplexCategory _ _).obj hv'.morphismOfTopoi.pushforward :=
    NatIso.ofComponents
      (fun F => NatIso.ofComponents
        (fun n => (h.componentAugmentationPushforwardSquareIso a a' v hv' hv n).app F)
        (fun φ => h.componentAugmentationPushforwardSquareIso_naturality a a' v hv' hv φ F))
      (fun α => NatTrans.ext (funext fun n =>
        (h.componentAugmentationPushforwardSquareIso a a' v hv' hv n).hom.naturality α))
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight Θ lim ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (preservesLimitNatIso hv'.morphismOfTopoi.pushforward).symm ≪≫
    (Functor.associator _ _ _).symm

end SimplicialSite.Morphism

namespace SimplicialSiteMorphism

/-- **Stacks 0D99.** Let `h` be a morphism between simplicial sites (Stacks 0D95), in either case
of Stacks 09WE, let `a`, `a'` be augmentations of its source and target towards sites `D`, `D'`
(Stacks 0D6Z), and let `g : Sh(D) → Sh(D')` be a morphism of topoi compatible with `h`, `a`, `a'`
(Stacks 0D98). Then the square formed by the morphism of total topoi `h_total` (Stacks 0D96), the
morphisms of topoi `a : Sh(C_total) → Sh(D)` and `a' : Sh(C'_total) → Sh(D')` of the total
augmentations (Stacks 0D70) and `g` commutes: `a' ∘ h_total = g ∘ a`, as witnessed by a natural
isomorphism of direct-image functors. -/
@[stacks 0D99]
def totalAugmentationPushforwardIso {S S' : SimplicialSiteSituation.{u}}
    {D D' : Cat.{u, u}} {K : GrothendieckTopology D} {K' : GrothendieckTopology D'}
    (h : SimplicialSiteMorphism S S')
    (a : SimplicialSiteSituation.Augmentation S D K)
    (a' : SimplicialSiteSituation.Augmentation S' D' K')
    (g : MorphismOfTopoi (Sheaf K (Type u)) (Sheaf K' (Type u)))
    (hg : h.CompatibleWithAugmentations a a' g) :
    h.totalMorphism.pushforward ⋙
        (SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi S' D' K' a').pushforward ≅
      (SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi S D K a).pushforward ⋙
        g.pushforward := by
  cases h with
  | @ofMorphismOfSites C C' hm =>
      change ∃ (v : D' ⥤ D) (hv : v.IsMorphismOfSites K' K),
        (g = hv.morphismOfTopoi) ∧
          (v ⋙ a.functor = a'.functor ⋙ (hm.hom.app (SimplexCategory.mk 0)).toFunctor) at hg
      let v := Classical.choose hg
      let hv := Classical.choose (Classical.choose_spec hg)
      have ⟨hg_eq, hcomp⟩ := Classical.choose_spec (Classical.choose_spec hg)
      rw [hg_eq]
      exact hm.totalAugmentationPushforwardIso a a' v hv hcomp
  | @ofCocontinuous C C' hm =>
      exact Functor.isoWhiskerLeft hm.totalMorphism.pushforward
          (CocontinuousSimplicialSite.Augmentation.totalPushforwardIso a') ≪≫
        hm.totalAugmentationPushforwardIso a a' g hg ≪≫
        Functor.isoWhiskerRight
          (CocontinuousSimplicialSite.Augmentation.totalPushforwardIso a).symm g.pushforward

end SimplicialSiteMorphism

end CategoryTheory

end
