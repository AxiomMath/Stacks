module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedBaseChangePlusPastingHorizontal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Refinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionModuleBaseChange
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqPasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FrobeniusRestrictionCoherence
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IntegralModuleBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pasting identities for extension by zero and the base change maps of étale sheaves of modules

The identities between underived natural transformations of sheaves of `Λ`-modules on small
étale sites that the compatibility of the base change maps for `Rf_!` with composition
([Stacks, Tag 0F7L]) reduces to.

## Main results

* `Stacks.EtaleCohomology.etaleModuleInverseImageExtensionByZeroIso_pasteH`: the isomorphisms
  `pY_! ∘ hU⁻¹ ≅ h⁻¹ ∘ j_!` paste horizontally.
* `Stacks.EtaleCohomology.etaleModuleRefinementComparison_baseChange`: the comparison
  `θ : k_! ⟶ g_* j_!` is compatible with base change.
* `Stacks.EtaleCohomology.ExtensionByZeroPasting.map_extensionByZeroToDirectImage_comp_baseChange`:
  the inclusion `ε_j : j_! ⟶ j_*` is compatible with base change along a cartesian square.

## Implementation notes

Every isomorphism and map in sight is either a comparison of left adjoints obtained by
uniqueness, a mate, or a restriction of sections along a morphism of small étale sites. The
formal parts are proved once, over abstract functors, in
`StacksFrontier/CategoryTheory/Adjunction/LeftAdjointUniqPasting.lean`; what remains here are
identities of comparisons of right adjoints, which are checked on sections, where they become
identities of morphisms into iterated fibre products, determined by their first projections.
The auxiliary lemmas live in the namespace `Stacks.EtaleCohomology.ExtensionByZeroPasting`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open Stacks.Cohomology.DerivedBaseChangePlus

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type r) [Ring Λ]

namespace ExtensionByZeroPasting

section SiteLemmas

variable {X Y U YU : Scheme.{u}} {h : Y ⟶ X} {j : U ⟶ X} [Etale j] {hU : YU ⟶ U} {pY : YU ⟶ Y}

/-- The comparison `V ×_X Y ≅ V ×_U YU` of
`AlgebraicGeometry.Scheme.Etale.smallEtaleComposeBaseChangeIsoOfIsPullback` commutes with the
first projections to `V`. -/
@[reassoc]
lemma smallEtaleComposeBaseChangeIsoOfIsPullback_hom_app_left_fst (upper : IsPullback hU pY j h)
    (V : U.Etale) :
    haveI := etale_of_isPullback_snd upper
    ((smallEtaleComposeBaseChangeIsoOfIsPullback upper).hom.app V).left ≫
      pullback.fst V.hom hU = pullback.fst (V.hom ≫ j) h := by
  have := etale_of_isPullback_snd upper
  have h1 : ((smallEtaleComposeBaseChangeIsoOfIsPullback upper).hom.app V).left =
      ((overPullbackBaseChangeIso pY hU h j upper.flip).hom.app ((Etale.forget U).obj V)).left := by
    change ((Etale.forget Y).map _).left = _
    rw [smallEtaleComposeBaseChangeIsoOfIsPullback, Functor.fullyFaithfulCancelRight_hom_app,
      Functor.map_preimage]
    rfl
  rw [h1]
  simp only [overPullbackBaseChangeIso, NatIso.ofComponents_hom_app, Over.isoMk_hom_left]
  exact IsPullback.isoIsPullback_hom_fst _ _ _ _

omit [Etale j] in
/-- A morphism into `V ×_U YU`, regarded as étale over `Y` through the cartesian square, is
determined by its first component. -/
lemma compose_baseChange_hom_ext (upper : IsPullback hU pY j h) [Etale pY] {V : U.Etale}
    {A : Y.Etale}
    {p q : A ⟶ (smallEtaleCompose pY).obj ((smallEtaleBaseChange hU).obj V)}
    (hpq : p.left ≫ pullback.fst V.hom hU = q.left ≫ pullback.fst V.hom hU) : p = q := by
  refine MorphismProperty.Over.Hom.ext (pullback.hom_ext hpq (upper.hom_ext ?_ ?_))
  · have hc := pullback.condition (f := V.hom) (g := hU)
    exact (Category.assoc _ _ _).trans ((congrArg (fun z => p.left ≫ z) hc.symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (fun z => z ≫ V.hom) hpq).trans
        ((Category.assoc _ _ _).trans ((congrArg (fun z => q.left ≫ z) hc).trans
          (Category.assoc _ _ _).symm)))))
  · exact (MorphismProperty.Over.w p).trans (MorphismProperty.Over.w q).symm

/-- `Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_inv_fst`, followed by a morphism. -/
lemma smallEtaleBaseChangeComp'_inv_fst_assoc {W X Y : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (fg : W ⟶ Y) (hfg : fg = f ≫ g) (U : Y.Etale) {Z : Scheme.{u}} (k : U.left ⟶ Z) :
    ((smallEtaleBaseChangeComp' f g fg hfg).inv.app U).left ≫ pullback.fst U.hom fg ≫ k =
      pullback.fst ((smallEtaleBaseChange g).obj U).hom f ≫ pullback.fst U.hom g ≫ k :=
  (Category.assoc _ _ _).symm.trans ((eq_whisker (smallEtaleBaseChangeComp'_inv_fst f g fg hfg U)
    k).trans (Category.assoc _ _ _))

/-- `Stacks.EtaleCohomology.smallEtaleBaseChange_map_left_fst`, followed by a morphism. -/
lemma smallEtaleBaseChange_map_left_fst_assoc {W X : Scheme.{u}} (f : W ⟶ X) {U V : X.Etale}
    (p : U ⟶ V) {Z : Scheme.{u}} (k : V.left ⟶ Z) :
    ((smallEtaleBaseChange f).map p).left ≫ pullback.fst V.hom f ≫ k =
      pullback.fst U.hom f ≫ p.left ≫ k :=
  (Category.assoc _ _ _).symm.trans ((eq_whisker (smallEtaleBaseChange_map_left_fst f p) k).trans
    (Category.assoc _ _ _))

/-- On sections, `Stacks.EtaleCohomology.etaleRestrictionPushforwardIsoOfIsPullback` is
restriction along the comparison of the two composites of site functors. -/
lemma etaleRestrictionPushforwardIsoOfIsPullback_hom_app_hom_app (A : Type*) [Category A]
    (upper : IsPullback hU pY j h)
    (M : Sheaf Y.smallEtaleTopology A) (V : U.Etaleᵒᵖ) :
    ((etaleRestrictionPushforwardIsoOfIsPullback A upper).hom.app M).hom.app V =
      M.obj.map ((smallEtaleComposeBaseChangeIsoOfIsPullback upper).hom.app V.unop).op := by
  simp only [Functor.comp_obj, etaleRestrictionPushforwardIsoOfIsPullback, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app, Iso.symm_inv,
    Functor.sheafPushforwardContinuousComp_inv_app_hom_app]
  exact Category.comp_id _

/-- On sections, the inverse of the composition isomorphism of direct images is restriction
along the inverse of the base change comparison. -/
lemma etaleModuleDirectImageComp_inv_app_hom_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (F : EtaleModules.{u, r} Λ X) (U : (Z.Etale)ᵒᵖ) :
    ((etaleModuleDirectImageComp.{u, r} Λ f g fg hfg).inv.app F).hom.app U =
      F.obj.map ((smallEtaleBaseChangeComp' f g fg hfg).inv.app U.unop).op := by
  simp only [Functor.comp_obj, etaleModuleDirectImageComp, smallEtalePushforwardComp',
    Functor.sheafPushforwardContinuousComp'_inv_app_hom_app, Iso.symm_hom]
  rfl

end SiteLemmas

section MateForm

/-- The composition isomorphism of inverse images, read along a named composite, is conjugate
to the composition isomorphism of direct images. -/
alias conjugateEquiv_eqToHom_comp_etaleModuleInverseImageCompIso_hom :=
  Stacks.EtaleCohomology.conjugateEquiv_eqToHom_comp_etaleModuleInverseImageCompIso_hom

variable {Z Z' X X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X' ⟶ X) (g' : Z' ⟶ Z)
  (w : i' ≫ g = g' ≫ i)

/-- **The base change map is the mate, along the horizontal adjunctions, of the comparison of
the two composite direct images around the square.** -/
alias etaleModuleBaseChange_eq_mateEquiv_symm :=
  Stacks.EtaleCohomology.etaleModuleBaseChange_eq_mateEquiv_symm

/-- **The unit formula for the base change map**: `β : g^{-1} i_* ⟶ i'_* g'^{-1}` followed
through the unit of `g^{-1} ⊣ g_*` is `i_*` of the unit of `g'^{-1} ⊣ g'_*` followed by the
comparison `i_* g'_* ≅ g_* i'_*`. -/
lemma unit_comp_map_etaleModuleBaseChange (F : EtaleModules.{u, r} Λ Z) :
    (etaleModuleInverseImageAdj.{u, r} Λ g).unit.app ((etaleModuleDirectImage.{u, r} Λ i).obj F) ≫
        (etaleModuleDirectImage.{u, r} Λ g).map ((etaleModuleBaseChange Λ i i' g g' w).app F) =
      (etaleModuleDirectImage.{u, r} Λ i).map
          ((etaleModuleInverseImageAdj.{u, r} Λ g').unit.app F) ≫
        ((etaleModuleDirectImageComp.{u, r} Λ g' i (i' ≫ g) w).hom ≫
          (etaleModuleDirectImageComp.{u, r} Λ i' g (i' ≫ g) rfl).inv).app
            ((etaleModuleInverseImage.{u, r} Λ g').obj F) := by
  rw [etaleModuleBaseChange_eq_mateEquiv_symm]
  exact (unit_mateEquiv_symm (etaleModuleInverseImageAdj.{u, r} Λ g')
    (etaleModuleInverseImageAdj.{u, r} Λ g) _ F).symm

end MateForm

section EpsilonBaseChange

/-- The inverse comparison `V ×_U YU ≅ V ×_X Y` commutes with the first projections to `V`. -/
lemma smallEtaleComposeBaseChangeIsoOfIsPullback_inv_app_left_fst {X Y U YU : Scheme.{u}}
    {h : Y ⟶ X} {j : U ⟶ X} [Etale j] {hU : YU ⟶ U} {pY : YU ⟶ Y} (upper : IsPullback hU pY j h)
    (V : U.Etale) :
    haveI := etale_of_isPullback_snd upper
    ((smallEtaleComposeBaseChangeIsoOfIsPullback upper).inv.app V).left ≫
      pullback.fst (V.hom ≫ j) h = pullback.fst V.hom hU := by
  have := etale_of_isPullback_snd upper
  have hi := congrArg (fun z : (smallEtaleBaseChange hU ⋙ smallEtaleCompose pY).obj V ⟶
      (smallEtaleBaseChange hU ⋙ smallEtaleCompose pY).obj V => z.left)
    ((smallEtaleComposeBaseChangeIsoOfIsPullback upper).inv_hom_id_app V)
  rw [← smallEtaleComposeBaseChangeIsoOfIsPullback_hom_app_left_fst upper V]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun z => z ≫ _) hi).trans
    (Category.id_comp _))

/-- The unit `V ⟶ V ×_X U` of composition against base change along `j` is a section of the
first projection. -/
@[reassoc]
lemma smallEtaleComposeBaseChangeAdj_unit_app_left_fst {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (V : U.Etale) :
    ((smallEtaleComposeBaseChangeAdj j).unit.app V).left ≫ pullback.fst (V.hom ≫ j) j = 𝟙 _ := by
  simp only [smallEtaleComposeBaseChangeAdj]
  exact pullback.lift_fst _ _ _

/-- On sections, the counit of restriction against direct image along an étale `j` is
restriction along the unit of composition against base change. -/
lemma etaleModuleRestrictionDirectImageAdj_counit_app_hom_app {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j] (G : EtaleModules.{u, r} Λ U) (V : U.Etaleᵒᵖ) :
    ((etaleModuleRestrictionDirectImageAdj.{u, r} Λ j).counit.app G).hom.app V =
      G.obj.map ((smallEtaleComposeBaseChangeAdj j).unit.app V.unop).op := by
  rfl

/-- On sections, the inverse of
`Stacks.EtaleCohomology.etaleRestrictionPushforwardIsoOfIsPullback` is restriction along the
inverse comparison of the two composites of site functors. -/
lemma etaleRestrictionPushforwardIsoOfIsPullback_inv_app_hom_app {X Y U YU : Scheme.{u}}
    {h : Y ⟶ X} {j : U ⟶ X} [Etale j] {hU : YU ⟶ U} {pY : YU ⟶ Y} (A : Type*) [Category A]
    (upper : IsPullback hU pY j h)
    (M : Sheaf Y.smallEtaleTopology A) (V : U.Etaleᵒᵖ) :
    ((etaleRestrictionPushforwardIsoOfIsPullback A upper).inv.app M).hom.app V =
      M.obj.map ((smallEtaleComposeBaseChangeIsoOfIsPullback upper).inv.app V.unop).op := by
  simp only [Functor.comp_obj, etaleRestrictionPushforwardIsoOfIsPullback, Iso.trans_inv,
    Iso.symm_inv, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousComp_hom_app_hom_app,
    Functor.sheafPushforwardContinuousComp'_inv_app_hom_app, Iso.symm_hom]
  exact Category.id_comp _

/-- The underlying morphism of schemes of a fourfold composite in the small étale site. -/
lemma comp_comp_comp_left {Y : Scheme.{u}} {A B C D E : Y.Etale} (a : A ⟶ B) (b : B ⟶ C)
    (c : C ⟶ D) (d : D ⟶ E) : (a ≫ b ≫ c ≫ d).left = a.left ≫ b.left ≫ c.left ≫ d.left :=
  rfl

/-- A morphism into a threefold iterated base change is determined by its composite with the
projections to the original object. -/
lemma smallEtaleBaseChange_baseChange_baseChange_hom_ext {W X Y Z : Scheme.{u}} (f : W ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) {A : W.Etale} {U : Z.Etale}
    {p q : A ⟶ (smallEtaleBaseChange f).obj
      ((smallEtaleBaseChange g).obj ((smallEtaleBaseChange h).obj U))}
    (hpq : p.left ≫ pullback.fst ((smallEtaleBaseChange g).obj
          ((smallEtaleBaseChange h).obj U)).hom f ≫
        pullback.fst ((smallEtaleBaseChange h).obj U).hom g ≫ pullback.fst U.hom h =
      q.left ≫ pullback.fst ((smallEtaleBaseChange g).obj
          ((smallEtaleBaseChange h).obj U)).hom f ≫
        pullback.fst ((smallEtaleBaseChange h).obj U).hom g ≫ pullback.fst U.hom h) :
    p = q := by
  exact smallEtaleBaseChange_hom_ext₃ f g h hpq

/-- The underlying morphism of schemes of a fivefold composite in the small étale site,
followed by a morphism of schemes. -/
lemma comp_comp_comp_comp_left_assoc {Y : Scheme.{u}} {A B C D E F : Y.Etale} {T : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (d : D ⟶ E) (e : E ⟶ F) (k : F.left ⟶ T) :
    (a ≫ b ≫ c ≫ d ≫ e).left ≫ k = a.left ≫ b.left ≫ c.left ≫ d.left ≫ e.left ≫ k := by
  change (a.left ≫ b.left ≫ c.left ≫ d.left ≫ e.left) ≫ k = _
  simp only [Category.assoc]

/-- The underlying morphism of schemes of a threefold composite in the small étale site,
followed by a morphism of schemes. -/
lemma comp_comp_left_assoc {Y : Scheme.{u}} {A B C D : Y.Etale} {T : Scheme.{u}} (a : A ⟶ B)
    (b : B ⟶ C) (c : C ⟶ D) (k : D.left ⟶ T) :
    (a ≫ b ≫ c).left ≫ k = a.left ≫ b.left ≫ c.left ≫ k := by
  change (a.left ≫ b.left ≫ c.left) ≫ k = _
  simp only [Category.assoc]

/-- `Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_fst_fst`, followed by a morphism. -/
lemma smallEtaleBaseChangeComp'_fst_fst_assoc {W X Y : Scheme.{u}} (f : W ⟶ X)
    (g : X ⟶ Y) (fg : W ⟶ Y) (hfg : fg = f ≫ g) (U : Y.Etale) {Z : Scheme.{u}} (k : U.left ⟶ Z) :
    ((smallEtaleBaseChangeComp' f g fg hfg).hom.app U).left ≫
        pullback.fst ((smallEtaleBaseChange g).obj U).hom f ≫ pullback.fst U.hom g ≫ k =
      pullback.fst U.hom fg ≫ k :=
  (whisker_eq _ (Category.assoc _ _ _).symm).trans ((Category.assoc _ _ _).symm.trans
    (eq_whisker (smallEtaleBaseChangeComp'_fst_fst f g fg hfg U) k))

variable {X X' Xb Xb' : Scheme.{u}} {g' : X' ⟶ X} {j : X ⟶ Xb} {j' : X' ⟶ Xb'} {φ : Xb' ⟶ Xb}
  [Etale j] [Etale j']

/-- The identity of morphisms of small étale sites behind
`Stacks.EtaleCohomology.ExtensionByZeroPasting.restriction_map_directImageComp_comp_counit`. -/
lemma smallEtale_unit_comp_baseChange_eq (hc : IsPullback g' j' j φ) (V : X.Etale) :
    (smallEtaleComposeBaseChangeAdj j').unit.app ((smallEtaleBaseChange g').obj V) ≫
      (smallEtaleBaseChange j').map ((smallEtaleComposeBaseChangeIsoOfIsPullback hc).inv.app V) ≫
      (smallEtaleBaseChangeComp' j' φ (j' ≫ φ) rfl).inv.app ((smallEtaleCompose j).obj V) ≫
      (smallEtaleBaseChangeComp' g' j (j' ≫ φ) hc.w.symm).hom.app ((smallEtaleCompose j).obj V) =
    (smallEtaleBaseChange g').map ((smallEtaleComposeBaseChangeAdj j).unit.app V) := by
  refine smallEtaleBaseChange_hom_ext₂ g' j ?_
  refine (congrArg (fun z => z ≫ _) (comp_comp_comp_left _ _ _ _)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => _ ≫ z) (Category.assoc _ _ _)).trans ?_
  refine (congrArg (fun z => _ ≫ _ ≫ z) (Category.assoc _ _ _)).trans ?_
  refine (congrArg (fun z => _ ≫ _ ≫ _ ≫ z) (smallEtaleBaseChangeComp'_fst_fst g' j (j' ≫ φ)
    hc.w.symm ((smallEtaleCompose j).obj V))).trans ?_
  refine (congrArg (fun z => _ ≫ _ ≫ z)
    (smallEtaleBaseChangeComp'_inv_fst j' φ (j' ≫ φ) rfl
      ((smallEtaleCompose j).obj V))).trans ?_
  refine (congrArg (fun z => _ ≫ z) (smallEtaleBaseChange_map_left_fst_assoc j'
    ((smallEtaleComposeBaseChangeIsoOfIsPullback hc).inv.app V)
    (pullback.fst (V.hom ≫ j) φ))).trans ?_
  refine (congrArg (fun z => _ ≫ _ ≫ z)
    (smallEtaleComposeBaseChangeIsoOfIsPullback_inv_app_left_fst hc V)).trans ?_
  refine (smallEtaleComposeBaseChangeAdj_unit_app_left_fst_assoc j'
    ((smallEtaleBaseChange g').obj V) _).trans ?_
  refine (Eq.trans (smallEtaleBaseChange_map_left_fst_assoc g'
    ((smallEtaleComposeBaseChangeAdj j).unit.app V)
    (pullback.fst (V.hom ≫ j) j)) ?_).symm
  exact (congrArg (fun z => _ ≫ z) (smallEtaleComposeBaseChangeAdj_unit_app_left_fst j V)).trans
    (Category.comp_id _)

/-- For a cartesian square with `j`, `j'` étale, the comparison `g'_* j_* ⟶ j'_* φ_*` of
direct images, restricted to `X`, followed by the identification of restriction with direct
image around the square and by `g'_*` of the counit of `j'^{-1} ⊣ j'_*`, is the counit of
`j^{-1} ⊣ j_*`. -/
lemma restriction_map_directImageComp_comp_counit (hc : IsPullback g' j' j φ)
    (G : EtaleModules.{u, r} Λ X') :
    (etaleModuleRestriction.{u, r} Λ j).map
        (((etaleModuleDirectImageComp.{u, r} Λ g' j (j' ≫ φ) hc.w.symm).hom ≫
          (etaleModuleDirectImageComp.{u, r} Λ j' φ (j' ≫ φ) rfl).inv).app G) ≫
      (etaleRestrictionPushforwardIsoOfIsPullback (ModuleCat.{max (u + 1) r} Λ) hc).inv.app
        ((etaleModuleDirectImage.{u, r} Λ j').obj G) ≫
      (etaleModuleDirectImage.{u, r} Λ g').map
        ((etaleModuleRestrictionDirectImageAdj.{u, r} Λ j').counit.app G) =
    (etaleModuleRestrictionDirectImageAdj.{u, r} Λ j).counit.app
      ((etaleModuleDirectImage.{u, r} Λ g').obj G) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    etaleRestrictionPushforwardIsoOfIsPullback_inv_app_hom_app,
    etaleModuleRestrictionDirectImageAdj_counit_app_hom_app]
  have key := congrArg (fun z => G.obj.map (Quiver.Hom.op z))
    (smallEtale_unit_comp_baseChange_eq hc V.unop)
  simp only [op_comp, Functor.map_comp, Category.assoc] at key
  exact key

end EpsilonBaseChange

section Epsilon

/-- The inclusion `ε_j : j_! ⟶ j_*` is transposed, under `j_! ⊣ j^{-1} ⊣ j_*`, to the
identity. -/
lemma unit_comp_map_extensionByZeroToDirectImage_comp_counit {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (F : EtaleModules.{u, r} Λ U) :
    (etaleModuleExtensionByZeroAdj.{u, r} Λ j).unit.app F ≫
        (etaleModuleRestriction.{u, r} Λ j).map
          ((etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j).app F) ≫
        (etaleModuleRestrictionDirectImageAdj.{u, r} Λ j).counit.app F = 𝟙 F := by
  rw [etaleModuleExtensionByZeroToDirectImage_app]
  exact Stacks.CategoryTheory.LeftAdjointUniqPasting.unit_comp_map_comp_counit _ _ F

variable {X X' Xb Xb' : Scheme.{u}} {g' : X' ⟶ X} {j : X ⟶ Xb} {j' : X' ⟶ Xb'} {φ : Xb' ⟶ Xb}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- **The inclusion of extension by zero into direct image commutes with base change**: for a
cartesian square with `j`, `j'` open immersions, `φ^{-1} ε_j` followed by the base change map
`φ^{-1} j_* ⟶ j'_* g'^{-1}` is the isomorphism `φ^{-1} j_! ≅ j'_! g'^{-1}` of [Stacks, Tag 03S6]
followed by `ε_{j'}`. -/
@[sga "4 XVII 5.1.2" "Existence clause"]
theorem map_extensionByZeroToDirectImage_comp_baseChange (hc : IsPullback g' j' j φ)
    (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleInverseImage.{u, r} Λ φ).map
        ((etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j).app F) ≫
      (etaleModuleBaseChange Λ j j' φ g' hc.w.symm).app F =
    (etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ hc).inv.app F ≫
      (etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j').app
        ((etaleModuleInverseImage.{u, r} Λ g').obj F) :=
  Stacks.CategoryTheory.LeftAdjointUniqPasting.map_comp_baseChange_eq
    (etaleModuleExtensionByZeroAdj.{u, r} Λ j) (etaleModuleRestrictionDirectImageAdj.{u, r} Λ j)
    (etaleModuleExtensionByZeroAdj.{u, r} Λ j')
    (etaleModuleRestrictionDirectImageAdj.{u, r} Λ j')
    (etaleModuleInverseImageAdj.{u, r} Λ φ) (etaleModuleInverseImageAdj.{u, r} Λ g')
    (etaleRestrictionPushforwardIsoOfIsPullback (ModuleCat.{max (u + 1) r} Λ) hc).symm
    (etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j)
    (etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j')
    (unit_comp_map_extensionByZeroToDirectImage_comp_counit Λ j)
    (unit_comp_map_extensionByZeroToDirectImage_comp_counit Λ j') _ _
    (unit_comp_map_etaleModuleBaseChange Λ j j' φ g' hc.w.symm)
    (restriction_map_directImageComp_comp_counit Λ hc) F

end Epsilon

end ExtensionByZeroPasting

section ExtensionByZero

variable {X X' X'' Xb Xb' Xb'' : Scheme.{u}} {g₁' : X' ⟶ X} {g₂' : X'' ⟶ X'} {j : X ⟶ Xb}
  {j' : X' ⟶ Xb'} {j'' : X'' ⟶ Xb''} {φ₁ : Xb' ⟶ Xb} {φ₂ : Xb'' ⟶ Xb'} [Etale j] [Etale j']
  [Etale j''] (hc₁ : IsPullback g₁' j' j φ₁) (hc₂ : IsPullback g₂' j'' j' φ₂)

namespace ExtensionByZeroPasting

/-- The comparison of site functors of the horizontally pasted square is the pasting of the
comparisons of the two squares. -/
lemma smallEtaleComposeBaseChangeIsoOfIsPullback_pasteHoriz (V : X.Etale) :
    (smallEtaleBaseChangeComp' φ₂ φ₁ (φ₂ ≫ φ₁) rfl).hom.app ((smallEtaleCompose j).obj V) ≫
      (smallEtaleBaseChange φ₂).map ((smallEtaleComposeBaseChangeIsoOfIsPullback hc₁).hom.app V) ≫
      (smallEtaleComposeBaseChangeIsoOfIsPullback hc₂).hom.app
        ((smallEtaleBaseChange g₁').obj V) ≫
      (smallEtaleCompose j'').map ((smallEtaleBaseChangeComp' g₂' g₁' (g₂' ≫ g₁') rfl).inv.app V) =
    (smallEtaleComposeBaseChangeIsoOfIsPullback (hc₂.paste_horiz hc₁)).hom.app V := by
  refine compose_baseChange_hom_ext (hc₂.paste_horiz hc₁) ?_
  refine Eq.trans ?_
    (smallEtaleComposeBaseChangeIsoOfIsPullback_hom_app_left_fst (hc₂.paste_horiz hc₁) V).symm
  refine (congrArg (fun z => _ ≫ _ ≫ _ ≫ z)
    (smallEtaleBaseChangeComp'_inv_fst g₂' g₁' (g₂' ≫ g₁') rfl V)).trans ?_
  refine (congrArg (fun z => _ ≫ _ ≫ z)
    (smallEtaleComposeBaseChangeIsoOfIsPullback_hom_app_left_fst_assoc hc₂
      ((smallEtaleBaseChange g₁').obj V) (pullback.fst V.hom g₁'))).trans ?_
  refine (congrArg (fun z => _ ≫ z) (smallEtaleBaseChange_map_left_fst_assoc φ₂
    ((smallEtaleComposeBaseChangeIsoOfIsPullback hc₁).hom.app V)
    (pullback.fst V.hom g₁'))).trans ?_
  refine (congrArg (fun z => _ ≫ _ ≫ z)
    (smallEtaleComposeBaseChangeIsoOfIsPullback_hom_app_left_fst hc₁ V)).trans ?_
  exact smallEtaleBaseChangeComp'_fst_fst φ₂ φ₁ (φ₂ ≫ φ₁) rfl ((smallEtaleCompose j).obj V)

/-- The identification `(h_* G)|_U = h_{U,*}(G|_{YU})` for the horizontally pasted square is the
pasting of the identifications for the two squares, read through the composition isomorphisms
of direct images. -/
lemma etaleRestrictionPushforwardIsoOfIsPullback_pasteHoriz :
    (etaleRestrictionPushforwardIsoOfIsPullback (ModuleCat.{max (u + 1) r} Λ)
        (hc₂.paste_horiz hc₁)).hom =
      Functor.whiskerLeft (etaleModuleRestriction.{u, r} Λ j'')
          (etaleModuleDirectImageComp.{u, r} Λ g₂' g₁' (g₂' ≫ g₁') rfl).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (etaleRestrictionPushforwardIsoOfIsPullback
          (ModuleCat.{max (u + 1) r} Λ) hc₂).hom (etaleModuleDirectImage.{u, r} Λ g₁') ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (etaleModuleDirectImage.{u, r} Λ φ₂)
          (etaleRestrictionPushforwardIsoOfIsPullback (ModuleCat.{max (u + 1) r} Λ) hc₁).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (etaleModuleDirectImageComp.{u, r} Λ φ₂ φ₁ (φ₂ ≫ φ₁) rfl).hom
          (etaleModuleRestriction.{u, r} Λ j) := by
  refine NatTrans.ext (funext fun M => Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_)))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    ObjectProperty.FullSubcategory.comp_hom, Category.id_comp,
    etaleRestrictionPushforwardIsoOfIsPullback_hom_app_hom_app,
    etaleModuleDirectImageComp_inv_app_hom_app]
  have key := congrArg (fun z => M.obj.map (Quiver.Hom.op z))
    (smallEtaleComposeBaseChangeIsoOfIsPullback_pasteHoriz hc₁ hc₂ V.unop)
  simp only [op_comp, Functor.map_comp, Category.assoc] at key
  exact key.symm

end ExtensionByZeroPasting

/-- **The isomorphisms `pY_! ∘ hU⁻¹ ≅ h⁻¹ ∘ j_!` of [Stacks, Tag 03S6] paste horizontally**,
read through the composition isomorphisms of inverse images. -/
theorem etaleModuleInverseImageExtensionByZeroIso_pasteH :
    pasteH (etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ hc₁).inv
        (etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ hc₂).inv
        (etaleModuleInverseImageCompIso.{u, r} Λ φ₂ φ₁).symm
        (etaleModuleInverseImageCompIso.{u, r} Λ g₂' g₁').symm =
      (etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ (hc₂.paste_horiz hc₁)).inv :=
  Stacks.CategoryTheory.LeftAdjointUniqPasting.pasteH_leftAdjointUniq_inv
    (etaleModuleExtensionByZeroAdj.{u, r} Λ j) (etaleModuleExtensionByZeroAdj.{u, r} Λ j')
    (etaleModuleExtensionByZeroAdj.{u, r} Λ j'')
    (etaleModuleInverseImageAdj.{u, r} Λ φ₁) (etaleModuleInverseImageAdj.{u, r} Λ φ₂)
    (etaleModuleInverseImageAdj.{u, r} Λ (φ₂ ≫ φ₁))
    (etaleModuleInverseImageAdj.{u, r} Λ g₁') (etaleModuleInverseImageAdj.{u, r} Λ g₂')
    (etaleModuleInverseImageAdj.{u, r} Λ (g₂' ≫ g₁')) _ _ _ _ _
    (etaleModuleDirectImageComp.{u, r} Λ φ₂ φ₁ (φ₂ ≫ φ₁) rfl)
    (etaleModuleDirectImageComp.{u, r} Λ g₂' g₁' (g₂' ≫ g₁') rfl)
    ((Stacks.CategoryTheory.LeftAdjointUniqPasting.conjugateEquiv_leftAdjointUniq_hom
      _ _ _).trans rfl)
    ((Stacks.CategoryTheory.LeftAdjointUniqPasting.conjugateEquiv_leftAdjointUniq_inv
      _ _ _).trans rfl)
    (ExtensionByZeroPasting.etaleRestrictionPushforwardIsoOfIsPullback_pasteHoriz Λ hc₁ hc₂)

end ExtensionByZero

section Refinement

variable {X X' Xb₁ Xb₂ Xb₁' Xb₂' : Scheme.{u}} {g' : X' ⟶ X} {j₁ : X ⟶ Xb₁} {j₂ : X ⟶ Xb₂}
  {j₁' : X' ⟶ Xb₁'} {j₂' : X' ⟶ Xb₂'} {p : Xb₁ ⟶ Xb₂} {p' : Xb₁' ⟶ Xb₂'}
  [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j₁'] [IsOpenImmersion j₂']
  [IsSeparated p] [IsSeparated p'] (hjk : j₁ ≫ p = j₂) (hjk' : j₁' ≫ p' = j₂')
  {φ₁ : Xb₁' ⟶ Xb₁} {φ₂ : Xb₂' ⟶ Xb₂} (hc₁ : IsPullback g' j₁' j₁ φ₁)
  (hc₂ : IsPullback g' j₂' j₂ φ₂) (wp : p' ≫ φ₂ = φ₁ ≫ p)

namespace ExtensionByZeroPasting

omit [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j₁'] [IsOpenImmersion j₂']
  [IsSeparated p] [IsSeparated p'] in
/-- The identity of morphisms of small étale sites behind
`Stacks.EtaleCohomology.ExtensionByZeroPasting.etaleModuleDirectImageComp_paste`. -/
lemma smallEtaleBaseChangeComp'_paste (U : Xb₂.Etale) :
    (smallEtaleBaseChangeComp' j₁' p' j₂' hjk'.symm).hom.app ((smallEtaleBaseChange φ₂).obj U) ≫
      (smallEtaleBaseChange j₁').map ((smallEtaleBaseChangeComp' p' φ₂ (p' ≫ φ₂) rfl).inv.app U) ≫
      (smallEtaleBaseChange j₁').map ((smallEtaleBaseChangeComp' φ₁ p (p' ≫ φ₂) wp).hom.app U) ≫
      (smallEtaleBaseChangeComp' j₁' φ₁ (j₁' ≫ φ₁) rfl).inv.app ((smallEtaleBaseChange p).obj U) ≫
      (smallEtaleBaseChangeComp' g' j₁ (j₁' ≫ φ₁) hc₁.w.symm).hom.app
        ((smallEtaleBaseChange p).obj U) =
    (smallEtaleBaseChangeComp' j₂' φ₂ (j₂' ≫ φ₂) rfl).inv.app U ≫
      (smallEtaleBaseChangeComp' g' j₂ (j₂' ≫ φ₂) hc₂.w.symm).hom.app U ≫
      (smallEtaleBaseChange g').map ((smallEtaleBaseChangeComp' j₁ p j₂ hjk.symm).hom.app U) := by
  refine smallEtaleBaseChange_baseChange_baseChange_hom_ext g' j₁ p ?_
  refine (comp_comp_comp_comp_left_assoc _ _ _ _ _ _).trans ?_
  refine (congrArg (fun z => _ ≫ _ ≫ _ ≫ _ ≫ z)
    (smallEtaleBaseChangeComp'_fst_fst_assoc g' j₁ (j₁' ≫ φ₁) hc₁.w.symm
    ((smallEtaleBaseChange p).obj U) (pullback.fst U.hom p))).trans ?_
  refine (congrArg (fun z => _ ≫ _ ≫ _ ≫ z)
    (smallEtaleBaseChangeComp'_inv_fst_assoc j₁' φ₁ (j₁' ≫ φ₁) rfl
    ((smallEtaleBaseChange p).obj U) (pullback.fst U.hom p))).trans ?_
  refine (congrArg (fun z => _ ≫ _ ≫ _ ≫ z) (Category.assoc _ _ _)).trans ?_
  have h4a := smallEtaleBaseChange_map_left_fst_assoc j₁'
    ((smallEtaleBaseChangeComp' φ₁ p (p' ≫ φ₂) wp).hom.app U)
    (pullback.fst ((smallEtaleBaseChange p).obj U).hom φ₁ ≫ pullback.fst U.hom p)
  dsimp only [Functor.comp_obj] at h4a ⊢
  refine (congrArg (fun z => _ ≫ _ ≫ z) h4a).trans ?_
  refine (congrArg (fun z => _ ≫ _ ≫ _ ≫ z)
    (smallEtaleBaseChangeComp'_fst_fst φ₁ p (p' ≫ φ₂) wp U)).trans ?_
  have h4b := smallEtaleBaseChange_map_left_fst_assoc j₁'
    ((smallEtaleBaseChangeComp' p' φ₂ (p' ≫ φ₂) rfl).inv.app U)
    (pullback.fst U.hom (p' ≫ φ₂))
  dsimp only [Functor.comp_obj] at h4b
  refine (congrArg (fun z => _ ≫ z) h4b).trans ?_
  refine (congrArg (fun z => _ ≫ _ ≫ z)
    (smallEtaleBaseChangeComp'_inv_fst p' φ₂ (p' ≫ φ₂) rfl U)).trans ?_
  refine (smallEtaleBaseChangeComp'_fst_fst_assoc j₁' p' j₂' hjk'.symm
    ((smallEtaleBaseChange φ₂).obj U)
    (pullback.fst U.hom φ₂)).trans ?_
  refine Eq.symm ((comp_comp_left_assoc _ _ _ _).trans ?_)
  have h4c := smallEtaleBaseChange_map_left_fst_assoc g'
    ((smallEtaleBaseChangeComp' j₁ p j₂ hjk.symm).hom.app U)
    (pullback.fst ((smallEtaleBaseChange p).obj U).hom j₁ ≫ pullback.fst U.hom p)
  dsimp only [Functor.comp_obj] at h4c ⊢
  refine (congrArg (fun z => _ ≫ _ ≫ z) h4c).trans ?_
  refine (congrArg (fun z => _ ≫ _ ≫ _ ≫ z)
    (smallEtaleBaseChangeComp'_fst_fst j₁ p j₂ hjk.symm U)).trans ?_
  refine (congrArg (fun z => _ ≫ z)
    (smallEtaleBaseChangeComp'_fst_fst g' j₂ (j₂' ≫ φ₂) hc₂.w.symm U)).trans ?_
  exact smallEtaleBaseChangeComp'_inv_fst j₂' φ₂ (j₂' ≫ φ₂) rfl U

omit [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j₁'] [IsOpenImmersion j₂']
  [IsSeparated p] [IsSeparated p'] in
/-- The comparisons of composite direct images around the two faces of the cube through `p`
and `p'` paste vertically to the comparison around the face through `j₂` and `j₂'`. -/
lemma etaleModuleDirectImageComp_paste (F : EtaleModules.{u, r} Λ X') :
    (etaleModuleDirectImage.{u, r} Λ p).map
        (((etaleModuleDirectImageComp.{u, r} Λ g' j₁ (j₁' ≫ φ₁) hc₁.w.symm).hom ≫
          (etaleModuleDirectImageComp.{u, r} Λ j₁' φ₁ (j₁' ≫ φ₁) rfl).inv).app F) ≫
      ((etaleModuleDirectImageComp.{u, r} Λ φ₁ p (p' ≫ φ₂) wp).hom ≫
          (etaleModuleDirectImageComp.{u, r} Λ p' φ₂ (p' ≫ φ₂) rfl).inv).app
        ((etaleModuleDirectImage.{u, r} Λ j₁').obj F) ≫
      (etaleModuleDirectImage.{u, r} Λ φ₂).map
        ((etaleModuleDirectImageComp.{u, r} Λ j₁' p' j₂' hjk'.symm).hom.app F) =
    (etaleModuleDirectImageComp.{u, r} Λ j₁ p j₂ hjk.symm).hom.app
        ((etaleModuleDirectImage.{u, r} Λ g').obj F) ≫
      ((etaleModuleDirectImageComp.{u, r} Λ g' j₂ (j₂' ≫ φ₂) hc₂.w.symm).hom ≫
          (etaleModuleDirectImageComp.{u, r} Λ j₂' φ₂ (j₂' ≫ φ₂) rfl).inv).app F := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    etaleModuleDirectImageComp_inv_app_hom_app, etaleModuleDirectImageComp_hom_app_hom_app]
  have key := congrArg (fun z => F.obj.map (Quiver.Hom.op z))
    (smallEtaleBaseChangeComp'_paste hjk hjk' hc₁ hc₂ wp U.unop)
  simp only [op_comp, Functor.map_comp, Category.assoc] at key
  exact key

omit [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j₁'] [IsOpenImmersion j₂']
  [IsSeparated p] [IsSeparated p'] in
/-- **Vertical pasting of base change maps along `j₂ = j₁ ≫ p`**: the base change map of `j₂`
is the pasting of those of `j₁` and of `p`, read through the composition isomorphisms of direct
images. -/
lemma etaleModuleBaseChange_pasteV_refinement (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleInverseImage.{u, r} Λ φ₂).map
        ((etaleModuleDirectImageComp.{u, r} Λ j₁ p j₂ hjk.symm).hom.app F) ≫
      (etaleModuleBaseChange Λ j₂ j₂' φ₂ g' hc₂.w.symm).app F =
    (etaleModuleBaseChange Λ p p' φ₂ φ₁ wp).app ((etaleModuleDirectImage.{u, r} Λ j₁).obj F) ≫
      (etaleModuleDirectImage.{u, r} Λ p').map
        ((etaleModuleBaseChange Λ j₁ j₁' φ₁ g' hc₁.w.symm).app F) ≫
      (etaleModuleDirectImageComp.{u, r} Λ j₁' p' j₂' hjk'.symm).hom.app
        ((etaleModuleInverseImage.{u, r} Λ g').obj F) := by
  rw [etaleModuleBaseChange_eq_mateEquiv_symm Λ j₂ j₂' φ₂ g' hc₂.w.symm,
    etaleModuleBaseChange_eq_mateEquiv_symm Λ p p' φ₂ φ₁ wp,
    etaleModuleBaseChange_eq_mateEquiv_symm Λ j₁ j₁' φ₁ g' hc₁.w.symm]
  exact CategoryTheory.mateEquiv_symm_paste_app (etaleModuleInverseImageAdj.{u, r} Λ g')
    (etaleModuleInverseImageAdj.{u, r} Λ φ₁) (etaleModuleInverseImageAdj.{u, r} Λ φ₂)
    (etaleModuleDirectImageComp.{u, r} Λ j₁ p j₂ hjk.symm)
    (etaleModuleDirectImageComp.{u, r} Λ j₁' p' j₂' hjk'.symm) _ _ _
    (etaleModuleDirectImageComp_paste Λ hjk hjk' hc₁ hc₂ wp) F

end ExtensionByZeroPasting

/-- **The comparison `θ : k_! ⟶ g_* j_!` of [Stacks, Tag 0F7G] is compatible with base
change**: for a cube whose two faces through the open immersions are cartesian, the base change
of `θ_p` is `θ_{p'}`, read through the isomorphisms of [Stacks, Tag 03S6] and the base change
map of `p`. -/
theorem etaleModuleRefinementComparison_baseChange :
    Functor.whiskerRight (etaleModuleRefinementComparison Λ hjk)
        (etaleModuleInverseImage.{u, r} Λ φ₂) ≫
      pasteV (etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ hc₁).inv
        (etaleModuleBaseChange Λ p p' φ₂ φ₁ wp) =
    (etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ hc₂).inv ≫
      Functor.whiskerLeft (etaleModuleInverseImage.{u, r} Λ g')
        (etaleModuleRefinementComparison Λ hjk') := by
  refine NatTrans.ext (funext fun F => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, pasteV,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  have hA₁ : (etaleModuleDirectImage.{u, r} Λ p').map
        ((etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ hc₁).inv.app F) ≫
      (etaleModuleDirectImage.{u, r} Λ p').map
        ((etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j₁').app
          ((etaleModuleInverseImage.{u, r} Λ g').obj F)) =
      (etaleModuleDirectImage.{u, r} Λ p').map ((etaleModuleInverseImage.{u, r} Λ φ₁).map
        ((etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j₁).app F)) ≫
      (etaleModuleDirectImage.{u, r} Λ p').map
        ((etaleModuleBaseChange Λ j₁ j₁' φ₁ g' hc₁.w.symm).app F) := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      ExtensionByZeroPasting.map_extensionByZeroToDirectImage_comp_baseChange Λ hc₁ F]
  have hθ : (etaleModuleInverseImage.{u, r} Λ φ₂).map
        ((etaleModuleRefinementComparison Λ hjk).app F) ≫
      (etaleModuleInverseImage.{u, r} Λ φ₂).map ((etaleModuleDirectImage.{u, r} Λ p).map
        ((etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j₁).app F)) =
      (etaleModuleInverseImage.{u, r} Λ φ₂).map
        ((etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j₂).app F) ≫
      (etaleModuleInverseImage.{u, r} Λ φ₂).map
        ((etaleModuleDirectImageComp.{u, r} Λ j₁ p j₂ hjk.symm).inv.app F) := by
    rw [← Functor.map_comp, ← Functor.map_comp, etaleModuleRefinementComparison_comp_map]
  have hm : (etaleModuleInverseImage.{u, r} Λ φ₂).map
        ((etaleModuleDirectImageComp.{u, r} Λ j₁ p j₂ hjk.symm).inv.app F) ≫
      (etaleModuleInverseImage.{u, r} Λ φ₂).map
        ((etaleModuleDirectImageComp.{u, r} Λ j₁ p j₂ hjk.symm).hom.app F) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  exact Stacks.CategoryTheory.LeftAdjointUniqPasting.comp_eq_of_hom_ext _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ (fun x y h => etaleModuleRefinement_hom_ext Λ hjk' h)
    ((etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ hc₂).hom_inv_id_app F)
    ((etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ hc₂).inv_hom_id_app F)
    (etaleModuleRefinementComparison_comp_map Λ hjk' _) hA₁
    ((etaleModuleBaseChange Λ p p' φ₂ φ₁ wp).naturality
      ((etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j₁).app F)).symm
    hθ (ExtensionByZeroPasting.etaleModuleBaseChange_pasteV_refinement Λ hjk hjk' hc₁ hc₂ wp F) hm
    ((etaleModuleDirectImageComp.{u, r} Λ j₁' p' j₂' hjk'.symm).hom_inv_id_app _)
    (ExtensionByZeroPasting.map_extensionByZeroToDirectImage_comp_baseChange Λ hc₂ F)

end Refinement

end Stacks.EtaleCohomology
