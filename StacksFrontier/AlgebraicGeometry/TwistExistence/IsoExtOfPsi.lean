module

public import StacksFrontier.AlgebraicGeometry.TwistExistence.Glue

/-!
# An isomorphism onto the twists is determined by the homogeneous-section maps

In Situation 01NN let `D` be a set of twist data of Stacks 01NR on the relative Proj of `A`, so
that `D.algebra` is `⨁_{n ∈ ℤ} 𝒪(n)` and `D.ψ` its homogeneous-section maps.  Let `G` be any
sheaf of `ℤ`-graded algebras on the relative Proj carrying maps `ψ_G n : A_n ⟶ π_* G_n`.  This
file proves that **an isomorphism `G ≅ D.algebra` carrying `ψ_G` to `D.ψ` is unique**.

## Main results

* `Stacks.AlgebraicGeometry.TwistExistence.iso_ext_of_psi`: two isomorphisms onto the twists of
  a twist datum which carry a given family of homogeneous-section maps to `D.ψ` are equal.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.TwistExistence

universe u

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-- **An isomorphism onto the twists is determined by the homogeneous-section maps.**  For a set
of twist data `D` of Stacks 01NR, a sheaf of graded algebras `G` on the relative Proj and maps
`ψ_G n : A_n ⟶ π_* G_n`, two isomorphisms `e e' : G ≅ D.algebra` both carrying `ψ_G` to `D.ψ` in
every degree `n ≥ 0` are equal. -/
theorem iso_ext_of_psi (D : TwistData A) {G : SchemeGradedAlgebra (relativeProj A).scheme}
    (ψG : ∀ n : ℕ, A.piece (n : ℤ) ⟶
      (Scheme.Modules.pushforward (relativeProj A).toBase).obj (G.piece (n : ℤ)))
    {e e' : G ≅ D.algebra}
    (he : ∀ n : ℕ, ψG n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
      (e.hom.app (n : ℤ)) = D.ψ n)
    (he' : ∀ n : ℕ, ψG n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
      (e'.hom.app (n : ℤ)) = D.ψ n) :
    e = e' := by
  obtain ⟨x, -, huniq⟩ := isUniqueTwistData A D D
  let push := Scheme.Modules.pushforward (relativeProj A).toBase
  have hinv : ∀ n : ℕ, D.ψ n ≫ push.map (e'.inv.app (n : ℤ)) = ψG n := by
    intro n
    calc D.ψ n ≫ push.map (e'.inv.app (n : ℤ))
        = ψG n ≫ push.map (e'.hom.app (n : ℤ)) ≫ push.map (e'.inv.app (n : ℤ)) := by
          rw [← he' n, Category.assoc]
      _ = ψG n ≫ push.map (e'.hom.app (n : ℤ) ≫ e'.inv.app (n : ℤ)) :=
          congrArg (ψG n ≫ ·) (push.map_comp _ _).symm
      _ = ψG n ≫ push.map (𝟙 _) := congrArg (fun k => ψG n ≫ push.map k)
          (congrArg (fun k => SheafOfModules.GradedAlgebra.Hom.app k (n : ℤ)) e'.hom_inv_id)
      _ = ψG n := (congrArg (ψG n ≫ ·) (push.map_id _)).trans (Category.comp_id _)
  have hrefl : Iso.refl D.algebra = x := huniq (Iso.refl _) fun n =>
    (congrArg (D.ψ n ≫ ·) (push.map_id _)).trans (Category.comp_id _)
  have hcomp : e'.symm ≪≫ e = x := huniq (e'.symm ≪≫ e) fun n =>
    calc D.ψ n ≫ push.map (e'.inv.app (n : ℤ) ≫ e.hom.app (n : ℤ))
        = D.ψ n ≫ push.map (e'.inv.app (n : ℤ)) ≫ push.map (e.hom.app (n : ℤ)) :=
          congrArg (D.ψ n ≫ ·) (push.map_comp _ _)
      _ = D.ψ n := by rw [← Category.assoc, hinv n, he n]
  ext1
  have := congrArg Iso.hom (hcomp.trans hrefl.symm)
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.refl_hom] at this
  rw [← Category.id_comp e.hom, ← e'.hom_inv_id, Category.assoc, this, Category.comp_id]

end Stacks.AlgebraicGeometry.TwistExistence

end
