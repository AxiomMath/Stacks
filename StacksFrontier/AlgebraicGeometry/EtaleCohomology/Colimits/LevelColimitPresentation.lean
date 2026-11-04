module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LevelLimitTransport

/-!
# The inverse image to the limit presents the colimit of the levels

For the system `levelSystem E d 𝓜` of inverse images `π_i⁻¹ 𝓜` restricted to the levels of the site
system of Stacks 0EYL, the restriction of `p⁻¹ 𝓜` to the raised site of the limit, with the legs
`levelLeg`, presents `colim_i u_i⁻¹ F_i` (`isColimitPresentation_levelLeg`): the legs are
compatible and their transposes are isomorphisms, and the index is cofiltered.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.EtaleCohomology.TransitionBaseChange

universe v u

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory.Sites.InverseSystem
  InverseSystemOfFiniteSites Stacks.WeakSites.ExtColimit Stacks.WeakSites.ColimitSiteCohomology

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : Iᵒᵖ ⥤ Scheme.{max u v}} {c : Cone D}
  {B : AlgebraicGeometry.BigEtaleSite.{max u v}}
  {hD : ∀ i, B.Contains (D.obj i)} {hX : B.Contains c.pt}
  (E : AffineEtaleSiteColimit D c B hD hX) (d : Cocone D)
  (p : c.pt ⟶ d.pt) (hp : ∀ i : E.system.I, p = coneProj E i ≫ stageProj E d i)
  [hcont : ∀ i : E.system.I, (levelEtale E i).IsContinuous (E.system.J i) (stageTopology E i)]
  [hcontL : ∀ i : E.system.I, (levelToLimit E i).IsContinuous (E.system.J i)
    (limitPrecoverageRaised (c := c) (hX := hX)).toGrothendieck]
  [hequiv : ∀ i : E.system.I, (levelMathlibRestrict E i).IsEquivalence]
  [hequivL : (limitMathlibRestrict (c := c) (hX := hX)).IsEquivalence]

attribute [local instance] isContinuous_levelMathlib isContinuous_transition
  isContinuous_limitSmallMathlib

include E in
/-- The index category of the site system is nonempty. -/
theorem nonempty_system_I : Nonempty E.system.I :=
  ⟨E.indexEquiv.inverse.obj (Opposite.op (Classical.arbitrary I))⟩

include E in
/-- Any two indices of the site system have a common lower bound. -/
theorem system_I_cofiltered (j j' : E.system.I) :
    ∃ m : E.system.I, Nonempty (m ⟶ j) ∧ Nonempty (m ⟶ j') := by
  obtain ⟨k, hk, hk'⟩ := directed_of (· ≤ ·) (Opposite.unop (E.indexEquiv.functor.obj j))
    (Opposite.unop (E.indexEquiv.functor.obj j'))
  exact ⟨E.indexEquiv.inverse.obj (Opposite.op k),
    ⟨E.indexEquiv.inverse.map (homOfLE hk).op ≫ E.indexEquiv.unitInv.app j⟩,
    ⟨E.indexEquiv.inverse.map (homOfLE hk').op ≫ E.indexEquiv.unitInv.app j'⟩⟩

/-- **The inverse image to the limit presents the colimit of the levels.** -/
theorem isColimitPresentation_levelLeg (𝓜 : Sheaf (smallEtaleTopology d.pt) Ab.{max u v + 1}) :
    IsColimitPresentation.{v, v, max u v + 1, max u v + 1} E.system (levelToLimit E)
      (levelToLimit_transition E) (limitPrecoverageRaised (c := c) (hX := hX))
      (levelSystem E d 𝓜)
      ((limitMathlibRestrict (c := c) (hX := hX)).obj ((smallEtalePullbackAb p).obj 𝓜))
      (fun j => (levelLeg E d p hp 𝓜 j).hom) := by
  have := nonempty_system_I E
  have hcomp : IsCompatible.{v, v, max v (max u v + 1), max u v + 1} E.system (levelToLimit E)
      (levelToLimit_transition E) (levelSystem E d 𝓜)
      ((limitMathlibRestrict (c := c) (hX := hX)).obj ((smallEtalePullbackAb p).obj 𝓜)).obj
      (fun j => (levelLeg E d p hp 𝓜 j).hom) :=
    @levelLeg_isCompatible _ _ _ _ _ _ _ _ _ E d p hp _ _ 𝓜
  exact isColimitPresentation_of_isIso_systemLeg.{v, v, max u v + 1} (system_I_cofiltered E) _
    hcomp (isIso_legTranspose E d p hp 𝓜)

end Stacks.EtaleCohomology.TransitionBaseChange

end
