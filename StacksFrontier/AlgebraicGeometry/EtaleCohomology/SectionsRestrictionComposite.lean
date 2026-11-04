module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackCompIsoComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SectionsTransitivityOverBase

/-!
# Restricting sections in two steps, with named composites

Restriction of a section of an abelian étale sheaf over an étale object `W` along a morphism
`r : Y ⟶ W` (`Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb`), followed by restriction of
global sections along `g : Y' ⟶ Y`
(`Stacks.EtaleCohomology.smallEtaleGlobalSectionsRestrictionAb`), is restriction along `g ≫ r`,
once the inverse images are identified by the composition isomorphisms. This file records that in
the form in which the restriction maps of the system of base changes of [Stacks, Tag 03Q6] are
written: every composite is carried as a named morphism, and the identifications are
`Stacks.EtaleCohomology.smallEtalePullbackAbCompIso'`.

## Main results

* `Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_comp_base'` — transitivity with a named
  composite.
* `Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_restriction_comp` — the two-step
  restriction through an intermediate scheme `X_U`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- `Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_comp_base` with the composite
`q = c ≫ p` and the morphism `r' = c ≫ r` named. -/
theorem smallEtaleSectionsPullbackAb_comp_base' {Z T T' : Scheme.{u}} (p : T ⟶ Z) (c : T' ⟶ T)
    (W : Z.Etale) (r : T ⟶ W.left) (hr : r ≫ W.hom = p) (q : T' ⟶ Z) (hq : q = c ≫ p)
    (r' : T' ⟶ W.left) (hr' : r' = c ≫ r) (hr'' : r' ≫ W.hom = q)
    (F : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) :
    (smallEtaleSectionsPullbackAb q W r' hr'').app F =
      (smallEtaleSectionsPullbackAb p W r hr).app F ≫
        (smallEtaleGlobalSectionsRestrictionAb c).app ((smallEtalePullbackAb p).obj F) ≫
          (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1}).map
            ((smallEtalePullbackAbCompIso' c p q hq).hom.app F) := by
  subst hq hr'
  have h := congrArg (fun φ => NatTrans.app φ F)
    (smallEtaleSectionsPullbackAb_comp_base p c W r hr hr'')
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Category.id_comp] at h
  rw [h, smallEtalePullbackAbCompIso_eq]

variable {X XU Y Y' : Scheme.{u}} (k : XU ⟶ X) (h : Y ⟶ XU) (g : Y' ⟶ Y) (a : Y ⟶ X)
  (ha : a = h ≫ k) (m : Y' ⟶ XU) (hm : m = g ≫ h) (q : Y' ⟶ X) (hq₁ : q = m ≫ k)
  (hq₂ : q = g ≫ a) (W : X.Etale) (r : Y ⟶ W.left) (hr : r ≫ W.hom = a) (r' : Y' ⟶ W.left)
  (hr' : r' = g ≫ r) (hr'' : r' ≫ W.hom = q)

include hq₂ in
/-- The pentagon for the composition isomorphisms, read at a sheaf, with the inner identification
inverted. -/
theorem smallEtalePullbackAbCompIso'_pentagon_app (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    (smallEtalePullbackAb g).map ((smallEtalePullbackAbCompIso' h k a ha).inv.app F) ≫
        (smallEtalePullbackAbCompIso' g h m hm).hom.app ((smallEtalePullbackAb k).obj F) ≫
          (smallEtalePullbackAbCompIso' m k q hq₁).hom.app F =
      (smallEtalePullbackAbCompIso' g a q hq₂).hom.app F := by
  have hpent := congrArg
    (fun e : smallEtalePullbackAb k ⋙ smallEtalePullbackAb h ⋙ smallEtalePullbackAb g ≅
      smallEtalePullbackAb q => e.hom.app F)
    (smallEtalePullbackAbCompIso'_assoc k h g a ha m hm q hq₁ hq₂)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.id_comp] at hpent
  refine (congrArg (_ ≫ ·) hpent).trans ?_
  rw [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]

include hq₂ hr' in
/-- **Two-step restriction through an intermediate scheme.** Restricting a section of `F` over `W`
to `Γ(Y, a⁻¹F)` along `r`, rewriting `a⁻¹F = h⁻¹k⁻¹F`, restricting along `g`, and rewriting
`g⁻¹h⁻¹k⁻¹F = m⁻¹k⁻¹F = q⁻¹F`, is restricting along `r' = g ≫ r`. -/
theorem smallEtaleSectionsPullbackAb_restriction_comp
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    (smallEtaleSectionsPullbackAb a W r hr).app F ≫
        (Sheaf.Γ (smallEtaleTopology Y) Ab.{u + 1}).map
          ((smallEtalePullbackAbCompIso' h k a ha).inv.app F) ≫
        (smallEtaleGlobalSectionsRestrictionAb g).app
          ((smallEtalePullbackAb h).obj ((smallEtalePullbackAb k).obj F)) ≫
        (Sheaf.Γ (smallEtaleTopology Y') Ab.{u + 1}).map
          ((smallEtalePullbackAbCompIso' g h m hm).hom.app ((smallEtalePullbackAb k).obj F)) ≫
        (Sheaf.Γ (smallEtaleTopology Y') Ab.{u + 1}).map
          ((smallEtalePullbackAbCompIso' m k q hq₁).hom.app F) =
      (smallEtaleSectionsPullbackAb q W r' hr'').app F := by
  rw [smallEtaleSectionsPullbackAb_comp_base' a g W r hr q hq₂ r' hr' hr'' F]
  refine congrArg ((smallEtaleSectionsPullbackAb a W r hr).app F ≫ ·) ?_
  let Γ' := Sheaf.Γ (smallEtaleTopology Y') Ab.{u + 1}
  have hnat := (smallEtaleGlobalSectionsRestrictionAb g).naturality
    ((smallEtalePullbackAbCompIso' h k a ha).inv.app F)
  have hp := congrArg Γ'.map (smallEtalePullbackAbCompIso'_pentagon_app k h g a ha m hm q hq₁ hq₂ F)
  simp only [Functor.map_comp] at hp
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hnat).trans ?_)
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  exact hp

end Stacks.EtaleCohomology

end
