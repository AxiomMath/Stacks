module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedSectionsCocycleAssembly
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedSmallEtaleIsoComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtalePullbackFinalSections
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleSectionsModule

/-!
# The factor-four square of Stacks 076T, reduced to one base-change compatibility

`AlgebraicGeometry.Stack.LiftedSectionsFactorFourSquareStandIn` is the composition law for
factors 2, 3 and 4 of the identification of sections `AlgebraicGeometry.Stack.liftedSectionsIso`
of **Stacks 076T**, read on sections over the final object of the small étale site.  This file
reduces that square to a single compatibility *on sections over the final object* between the
base-change identification `AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso`
of **Stacks 03LC (1)** and `Stacks.Sites.quasiCoherentPresheafBaseChangeIso` of **Stacks 03DS**,
`AlgebraicGeometry.Stack.AssociatedModuleBaseChangeFinalSectionsCompat`, which is assumed and not
proved here.

## Implementation notes

The reduction uses:

* `AlgebraicGeometry.Stack.liftedSmallEtaleIso_hom_comp_sheafInv` turns each factor of the
  identification into the underlying morphism of presheaves of a morphism of *sheaves* of
  modules, read backwards;
* `AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv_comp` is the composition law for factors 2,
  3 and 4 at the level of sheaves of modules, and
  `AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv_eq` peels factor 4 off it;
* `AlgebraicGeometry.Stack.smallEtaleFinalPullbackUnit_comp_sheafifiedFactor` reads factors 3
  and 4 on sections over the final object, which the Stacks 06WC pullback of presheaves of
  modules being a left adjoint would otherwise forbid;
* `AlgebraicGeometry.SmallEtale.associatedModulePresheafIso_hom_naturality_module` crosses the
  vertical at the associated-module stage, whose two spellings are
  `AlgebraicGeometry.Scheme.Modules.pullbackFactoredComp` applied to the morphisms of schemes
  below and `Stacks.Sites.pullbackCompSectionsIsoOfEq` on global sections; that those two agree
  is `Stacks.Sites.pullbackCompSectionsIsoOfEq_hom`.

Unwinding `AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso`, the
compatibility asks for the mate of **Stacks 03LC (1)** — which
`AlgebraicGeometry.SmallEtale.conjugateEquiv_associatedModuleBaseChangeIso_inv` pins, as
`AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso`, over the *opens* of the base — to be
read through the **Stacks 070S** identification
`AlgebraicGeometry.SmallEtale.associatedModulePresheafIso` of the sections of `𝓖^a` with the
presheaf of Stacks 03DS.

## Main definitions

* `AlgebraicGeometry.Stack.AssociatedModuleBaseChangeFinalSectionsCompat`: the compatibility of
  the two base changes on sections over the final object.

## Main results

* `Stacks.Sites.pullbackCompSectionsIsoOfEq_hom`: the composition isomorphism of the pullback
  pseudofunctor on global sections is the global sections of
  `AlgebraicGeometry.Scheme.Modules.pullbackFactoredComp`.
* `AlgebraicGeometry.Stack.liftedSectionsFactorFourSquare_of_compat`: the factor-four square
  follows from that compatibility.

## References

* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.Sites

variable {U W W' : Scheme.{u}} (𝓕 : U.Modules) (g : W ⟶ U) (k : W' ⟶ W) (g' : W' ⟶ U)

/-- **`Stacks.Sites.pullbackCompSectionsIsoOfEq` is the global sections of
`AlgebraicGeometry.Scheme.Modules.pullbackFactoredComp`.**  Both are built by substituting the
factorisation `g' = k ≫ g` into the composition isomorphism of the pullback pseudofunctor, one
on global sections over an object of `Sch/W'` and one on the pullback functors themselves, so the
two agree after the substitution. -/
theorem pullbackCompSectionsIsoOfEq_hom (hg' : g' = k ≫ g) (A : Over W') :
    (pullbackCompSectionsIsoOfEq 𝓕 g k g' hg' A).hom =
      ((Scheme.Modules.pullback A.hom).map
        ((Scheme.Modules.pullbackFactoredComp k g g' hg'.symm).hom.app 𝓕)).app ⊤ := by
  subst hg'
  change ((Scheme.Modules.pullback A.hom).map
      ((Scheme.Modules.pullbackComp k g).hom.app 𝓕 ≫
        ((Scheme.Modules.pullbackCongr (rfl : k ≫ g = k ≫ g)).app 𝓕).inv)).app ⊤ = _
  rw [show ((Scheme.Modules.pullbackCongr (rfl : k ≫ g = k ≫ g)).app 𝓕).inv = 𝟙 _ from rfl,
    Category.comp_id]
  rfl

end Stacks.Sites

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **The compatibility on sections between the two base changes.**
For an arrow `ψ : z' ⟶ z` of `𝒳` lying over a morphism of schemes `k : W' ⟶ W` and a
quasi-coherent `𝒪_W`-module `𝓖`, the base-change identification `(k^*𝓖)^a ≅ ε_ψ^*(𝓖^a)` of
**Stacks 03LC (1)**, read on sections over the final object of the small étale site of `W'`
through `AlgebraicGeometry.Stack.smallEtaleFinalPullbackUnit` and the sheafification unit and
then through the **Stacks 070S** identification of those sections with the sections of the
presheaf of **Stacks 03DS**, is the base-change identification of **Stacks 03DS** itself:
restriction along the arrow `n` of `Sch/W` below `ψ` followed by
`Stacks.Sites.quasiCoherentPresheafBaseChangeIso`.

This is a hypothesis, not a proved statement. -/
def AssociatedModuleBaseChangeFinalSectionsCompat : Prop :=
  ∀ {z' z : 𝒳} (ψ : z' ⟶ z) (𝓖 : (p.obj z).left.1.Modules) (h𝓖 : 𝓖.IsQuasicoherent)
    (n : (Over.map (B.inclusion.map (p.map ψ).left)).obj
        ((SmallEtale.toOver E (p.obj z').left.1 (contains_base B E h S hS p z')).obj
          (smallEtaleFinal B E h S hS p z')) ⟶
      (SmallEtale.toOver E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
        (smallEtaleFinal B E h S hS p z))
    (_hn : n.left = B.inclusion.map (p.map ψ).left),
    letI := h𝓖
    smallEtaleFinalPullbackUnit B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) ψ
          ((SmallEtale.associatedModule E (p.obj z).left.1
            (contains_base B E h S hS p z)).obj 𝓖).val ≫
        ((PresheafOfModules.toPresheaf _).map
          ((PresheafOfModules.sheafificationAdjunction
                (𝟙 (SmallEtale.structureSheaf E (p.obj z').left.1
                  (contains_base B E h S hS p z')).obj)).unit.app
              ((PresheafOfModules.pullback.{u}
                (smallEtaleStructureComparison B E h S hS p hp ψ (etaleTopology B)
                  (etaleTopology_le_topology B))).obj
                ((SmallEtale.associatedModule E (p.obj z).left.1
                  (contains_base B E h S hS p z)).obj 𝓖).val))).app
          (op (smallEtaleFinal B E h S hS p z')) ≫
        ((PresheafOfModules.toPresheaf _).map
          ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).map
            (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
              (etaleTopology_le_topology B) ψ 𝓖).hom)).app
          (op (smallEtaleFinal B E h S hS p z')) ≫
        (SmallEtale.associatedModulePresheafIso E (p.obj z').left.1
            (contains_base B E h S hS p z')
            ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓖)).hom.app
          (op (smallEtaleFinal B E h S hS p z')) =
      (SmallEtale.associatedModulePresheafIso E (p.obj z).left.1
            (contains_base B E h S hS p z) 𝓖).hom.app
          (op (smallEtaleFinal B E h S hS p z)) ≫
        (quasiCoherentPresheafFunctor (p.obj z).left.1 𝓖).map n.op ≫
        (Stacks.Sites.quasiCoherentPresheafBaseChangeIso 𝓖
            (Over.mk (B.inclusion.map (p.map ψ).left))).hom.app
          (op ((SmallEtale.toOver E (p.obj z').left.1
            (contains_base B E h S hS p z')).obj
            (smallEtaleFinal B E h S hS p z')))

/-- A left inverse of the forward map of an isomorphism is a right inverse. -/
private theorem right_inv_of_left_inv {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) (s : Y ⟶ X)
    (hs : e.hom ≫ s = 𝟙 X) : s ≫ e.hom = 𝟙 Y :=
  e.comp_hom_eq_id.2 (e.hom_comp_eq_id.1 hs)

/-- The category algebra of the factor-four square, with every object and arrow abstract. -/
private theorem factor_four_algebra {C : Type*} [Category C]
    {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ O₁₁ O₁₂ O₁₃ : C}
    (sinv : O₁ ⟶ O₂) (fzh : O₂ ⟶ O₃) (fψ : O₃ ⟶ O₄) (fzi' : O₄ ⟶ O₅)
    (lam' : O₅ ⟶ O₆) (ap' : O₆ ⟶ O₇)
    (uu : O₁ ⟶ O₈) (eta : O₈ ⟶ O₉) (bc : O₉ ⟶ O₁₀) (pf : O₁₀ ⟶ O₆) (si' : O₆ ⟶ O₅)
    (apQ : O₁₀ ⟶ O₁₁) (pfs : O₁₁ ⟶ O₇) (apB : O₁ ⟶ O₁₂) (nmap : O₁₂ ⟶ O₁₃) (qcbc : O₁₃ ⟶ O₁₁)
    (hfinal : uu ≫ eta ≫ bc ≫ pf ≫ si' = sinv ≫ fzh ≫ fψ ≫ fzi')
    (hsi : si' ≫ lam' = 𝟙 O₆)
    (hnat : pf ≫ ap' = apQ ≫ pfs)
    (hcompat : uu ≫ eta ≫ bc ≫ apQ = apB ≫ nmap ≫ qcbc) :
    sinv ≫ fzh ≫ fψ ≫ fzi' ≫ lam' ≫ ap' = apB ≫ nmap ≫ qcbc ≫ pfs := by
  have e1 : uu ≫ eta ≫ bc ≫ pf ≫ si' ≫ lam' ≫ ap' =
      sinv ≫ fzh ≫ fψ ≫ fzi' ≫ lam' ≫ ap' := by
    simpa only [Category.assoc] using congrArg (fun t => t ≫ lam' ≫ ap') hfinal
  rw [← e1, ← Category.assoc si' lam' ap', hsi, Category.id_comp, hnat]
  simpa only [Category.assoc] using congrArg (fun t => t ≫ pfs) hcompat

/-- The prefix split: stripping the invertible head of the identification. -/
private theorem split_prefix {C : Type*} [Category C] {O₁ O₂ O₃ O₄ O₅ : C}
    (fzh : O₂ ⟶ O₁) (fzi : O₁ ⟶ O₂) (lh : O₂ ⟶ O₃) (li : O₃ ⟶ O₂)
    (t : O₁ ⟶ O₄) (ap : O₃ ⟶ O₅) (rest : O₅ ⟶ O₄)
    (hfz : fzi ≫ fzh = 𝟙 O₁) (hl : lh ≫ li = 𝟙 O₂)
    (key : li ≫ fzh ≫ t = ap ≫ rest) :
    t = (fzi ≫ lh ≫ ap) ≫ rest := by
  rw [Category.assoc, Category.assoc, ← key, ← Category.assoc lh li, hl, Category.id_comp,
    ← Category.assoc, hfz, Category.id_comp]

/-- **The factor-four square of Stacks 076T, over the compatibility of the two base changes on
sections.**  `AlgebraicGeometry.Stack.LiftedSectionsFactorFourSquareStandIn` — and hence, by
`AlgebraicGeometry.Stack.liftedSectionsCocycle_of_factorFourSquare`, the cocycle condition
`AlgebraicGeometry.Stack.LiftedSectionsCocycle` — follows from
`AlgebraicGeometry.Stack.AssociatedModuleBaseChangeFinalSectionsCompat` alone. -/
theorem liftedSectionsFactorFourSquare_of_compat
    (hc : AssociatedModuleBaseChangeFinalSectionsCompat B E h S hS p hp) :
    LiftedSectionsFactorFourSquareStandIn B E h S hS p hp := by
  intro F hlqcF x 𝓕 h𝓕 hMx eU z' z ψ φ hkg hiso hiso' n
  let := h𝓕
  have hn : n.left = B.inclusion.map (p.map ψ).left :=
    (Category.comp_id _).symm.trans ((Over.w n).trans (Category.id_comp _))
  have hMz : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z).left.1
      (contains_base B E h S hS p z))
      (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf := (hlqcF.2 z).choose
  have hMz' : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z').left.1
      (contains_base B E h S hS p z'))
      (restrictModuleToSmallEtale B E h S hS p hp z' (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf := (hlqcF.2 z').choose
  rw [Stacks.Sites.pullbackCompSectionsIsoOfEq_hom]
  unfold liftedSectionsUpper
  -- `h3`: the composition law for factors 2, 3, 4 at sheaf level, with factor 4 peeled off
  have h3 : (PresheafOfModules.sheafification
            (𝟙 (SmallEtale.structureSheaf E (p.obj z').left.1
              (contains_base B E h S hS p z')).obj)).map
            ((PresheafOfModules.pullback.{u}
              (smallEtaleStructureComparison B E h S hS p hp ψ (etaleTopology B)
                (etaleTopology_le_topology B))).map
              ((SheafOfModules.forget _).map
                (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom))) ≫
          sheafifiedRestrictComparison B E h S hS p hp F ψ hMz' =
        (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B) ψ
            ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).hom ≫
          (SmallEtale.associatedModule E (p.obj z').left.1
              (contains_base B E h S hS p z')).map
            ((Scheme.Modules.pullbackFactoredComp (B.inclusion.map (p.map ψ).left)
              (B.inclusion.map (p.map φ).left) (B.inclusion.map (p.map (ψ ≫ φ)).left)
              (belowSchemeHom_comp B S hS p ψ φ)).hom.app 𝓕) ≫
          liftedSmallEtaleSheafInv B E h S hS p hp F (ψ ≫ φ) 𝓕 hMx hMz' eU.hom := by
    rw [← liftedSmallEtaleSheafInv_comp B E h S hS p hp F ψ φ 𝓕 hMx hMz hMz' eU.hom,
      liftedSmallEtaleSheafInv_eq B E h S hS p hp F ψ
        ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕) hMz hMz'
        (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom),
      Iso.hom_inv_id_assoc]
    rfl
  -- `e1`: factors 3 and 4 read on sections at the final object
  have e1 := smallEtaleFinalPullbackUnit_comp_sheafifiedFactor B E h S hS p hp ψ F hMz'
    ((SmallEtale.associatedModule E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
      ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)).val
    ((SheafOfModules.forget _).map
      (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom))
  erw [h3] at e1
  simp only [Functor.map_comp, NatTrans.comp_app] at e1
  -- `hA`: factors 2, 3, 4 are inverse to the identification, at `ψ ≫ φ`
  have hA := NatTrans.congr_app (liftedSmallEtaleIso_hom_comp_sheafInv B E h S hS p hp F hlqcF
    (ψ ≫ φ) 𝓕 h𝓕 hMx hMz' eU hiso') (op (smallEtaleFinal B E h S hS p z'))
  simp only [NatTrans.id_app] at hA
  have hsi := right_inv_of_left_inv
    ((liftedSmallEtaleIso B E h S hS p hp F hlqcF (ψ ≫ φ) 𝓕 h𝓕 hMx eU hiso').app
      (op (smallEtaleFinal B E h S hS p z'))) _ hA
  -- `hnat`: naturality of the Stacks 070S identification in the module
  have : SheafOfModules.IsQuasicoherent
      ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left) ⋙
        Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj 𝓕) :=
    inferInstanceAs (SheafOfModules.IsQuasicoherent
      ((Scheme.Modules.pullback (B.inclusion.map (p.map ψ).left)).obj
        ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕)))
  have hnat := SmallEtale.associatedModulePresheafIso_hom_naturality_module E
    (p.obj z').left.1 (contains_base B E h S hS p z')
    ((Scheme.Modules.pullbackFactoredComp (B.inclusion.map (p.map ψ).left)
      (B.inclusion.map (p.map φ).left) (B.inclusion.map (p.map (ψ ≫ φ)).left)
      (belowSchemeHom_comp B S hS p ψ φ)).hom.app 𝓕)
    (op (smallEtaleFinal B E h S hS p z'))
  have hl := NatTrans.congr_app (liftedSmallEtaleIso_hom_comp_sheafInv B E h S hS p hp F hlqcF
    φ 𝓕 h𝓕 hMx hMz eU hiso) (op (smallEtaleFinal B E h S hS p z))
  simp only [NatTrans.id_app] at hl
  refine split_prefix
    (restrictModuleToSmallEtaleFinalIso B E h S hS p hp z (etaleTopology B)
      (etaleTopology_le_topology B) F).hom _ _
    (((PresheafOfModules.toPresheaf _).map
      ((SheafOfModules.forget _).map
        (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom))).app
      (op (smallEtaleFinal B E h S hS p z)))
    _ _ _ (Iso.inv_hom_id _) hl ?_
  exact factor_four_algebra _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e1 hsi hnat
    (hc ψ ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕) inferInstance n hn)

end AlgebraicGeometry.Stack

end
