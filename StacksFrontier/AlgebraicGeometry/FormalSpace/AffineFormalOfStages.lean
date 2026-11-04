module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedSurjective

/-!
# Affine formal algebraic spaces from directed systems of affine stages

Let `S` be a scheme of a big fppf site and let `G : Λ ⥤ FppfSheaf` be a directed system of fppf
sheaves each isomorphic to the sheaf represented by an affine object of the site, with
representable thickenings as transition morphisms. Then the colimit of `G`, if it satisfies the
set-theoretic condition of Stacks 0AIS, is an affine formal algebraic space (Stacks 0AI7): the
system is isomorphic to one coming from a directed system of affine objects of the site whose
transition morphisms are thickenings of schemes.

## Main results

* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_of_isColimit_of_isAffine_stages`

## Implementation notes

The sheafified Yoneda embedding of the site is fully faithful, so the system of represented
sheaves lifts to a system of affine objects of the site, one transition morphism at a time. That
the lifted transition morphisms are thickenings is read off the relative thickening property of
the given ones at the identity points of their targets, where the represented base change is the
lifted morphism itself.

## References

* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A directed colimit of affine stages along representable thickenings is an affine formal
algebraic space.** Let `G : Λ ⥤ FppfSheaf` be a nonempty directed system whose terms are
isomorphic to sheaves represented by affine objects of the site and whose transition morphisms
are representable thickenings. Then the vertex of a colimit cocone of `G` which satisfies the
set-theoretic condition of Stacks 0AIS is an affine formal algebraic space. -/
theorem isAffineFormalAlgebraicSpace_of_isColimit_of_isAffine_stages
    (Λ : Type (u + 1)) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (G : Λ ⥤ FppfSheaf B S hS)
    (hG : ∀ μ, ∃ T : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
      Nonempty (G.obj μ ≅ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T))
    (hthick : ∀ ⦃μ ν : Λ⦄ (g : μ ⟶ ν),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (G.map g).hom)
    (c : Cocone G) (hc : IsColimit c) (hset : SatisfiesSetTheoreticCondition B S hS c.pt) :
    IsAffineFormalAlgebraicSpace B S hS c.pt := by
  classical
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let ι := BigAffineFppf.inclusion B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let F' := ι ⋙ F
  let hF' : F'.FullyFaithful :=
    (ObjectProperty.fullyFaithfulι _).comp (Sheaf.fullyFaithfulSheafifiedYoneda J)
  choose T hTaff hTe using hG
  let T' : Λ → BigAffineFppf B S hS := fun μ ↦ ⟨T μ, hTaff μ⟩
  let e : ∀ μ, G.obj μ ≅ F'.obj (T' μ) := fun μ ↦ (hTe μ).some
  -- the lifted system of affine objects of the site
  let D : Λ ⥤ BigAffineFppf B S hS :=
    { obj := T'
      map := fun {μ ν} g ↦ hF'.preimage ((e μ).inv ≫ G.map g ≫ (e ν).hom)
      map_id := fun μ ↦ hF'.map_injective (by simp)
      map_comp := fun {μ ν ρ} g g' ↦ hF'.map_injective (by simp) }
  have hDmap : ∀ {μ ν : Λ} (g : μ ⟶ ν), F'.map (D.map g) = (e μ).inv ≫ G.map g ≫ (e ν).hom :=
    fun g ↦ hF'.map_preimage _
  let α : D ⋙ F' ≅ G := NatIso.ofComponents (fun μ ↦ (e μ).symm) fun {μ ν} g ↦ by
    show F'.map (D.map g) ≫ (e ν).inv = (e μ).inv ≫ G.map g
    rw [hDmap]
    simp
  -- the lifted transition morphisms are thickenings
  have hDthick : ∀ ⦃μ ν : Λ⦄ (g : μ ⟶ ν),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map g)) := by
    intro μ ν g
    let ε := sheafifiedYonedaCompForgetIso B S hS
    have hsq : IsPullback ((ε.app (T μ)).inv ≫ (e μ).inv.hom)
        ((uliftYoneda.{u + 1}).map (ι.map (D.map g))) (G.map g).hom
        ((ε.app (T ν)).inv ≫ (e ν).inv.hom) := by
      refine IsPullback.of_horiz_isIso ⟨?_⟩
      have hF : (F.map (ι.map (D.map g))).hom ≫ (e ν).inv.hom =
          (e μ).inv.hom ≫ (G.map g).hom := by
        simpa [F'] using congrArg (fun φ ↦ φ.hom) (congrArg (· ≫ (e ν).inv) (hDmap g))
      calc ((ε.app (T μ)).inv ≫ (e μ).inv.hom) ≫ (G.map g).hom
          = (ε.app (T μ)).inv ≫ (F.map (ι.map (D.map g))).hom ≫ (e ν).inv.hom := by
            rw [hF, Category.assoc]
        _ = _ := by
            rw [← Category.assoc, ← Category.assoc]
            congr 1
            exact (ε.inv.naturality (ι.map (D.map g))).symm
    exact (hthick g).property _ _ _ hsq
  exact ⟨hset, Λ, inferInstance, inferInstance, inferInstance, D, hDthick,
    ⟨(colimit.isoColimitCocone ⟨c, hc⟩).symm.trans (HasColimit.isoOfNatIso α).symm⟩⟩

end AlgebraicGeometry.FormalSpace
