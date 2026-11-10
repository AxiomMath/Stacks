module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Coproducts of cokernels, and maps out of a coproduct

Two facts about an arbitrary category, used wherever a quasi-coherence argument compares a
coproduct of presentations with a presentation of a coproduct. Neither mentions a site, a ringed
site or a sheaf of modules, so both live here rather than being restated in each development
that needs them.

## Main results

* `CategoryTheory.Limits.coproductCokernel`: a coproduct of copies of a cokernel is the cokernel
  of the coproduct.
* `CategoryTheory.Limits.cofanHomEquiv`: a map out of a coproduct is a family of maps out of its
  summands.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

/-- A coproduct of copies of a cokernel is the cokernel of the coproduct. -/
noncomputable def coproductCokernel
    {D : Type*} [Category D] [HasZeroMorphisms D]
    {A B M : D} {a : A ⟶ B} {b : B ⟶ M} {hab : a ≫ b = 0}
    (h : IsColimit (CokernelCofork.ofπ b hab))
    (I : Type*) [HasCoproduct (fun _ : I => A)]
    [HasCoproduct (fun _ : I => B)] [HasCoproduct (fun _ : I => M)] :
    IsColimit (CokernelCofork.ofπ (Limits.Sigma.map (fun _ : I => b))
      (show Limits.Sigma.map (fun _ : I => a) ≫ Limits.Sigma.map (fun _ : I => b) = 0 by
        apply Sigma.hom_ext; intro i
        simp only [Sigma.ι_map_assoc, Sigma.ι_map, comp_zero]
        rw [← Category.assoc, hab, zero_comp])) := by
  refine CokernelCofork.IsColimit.ofπ _ _ (fun s hs =>
    Sigma.desc (fun i => (CokernelCofork.IsColimit.desc' h (Sigma.ι (fun _ : I => B) i ≫ s)
      (by simpa using congrArg (fun f => Sigma.ι (fun _ : I => A) i ≫ f) hs)).1)) ?_ ?_
  · intro Z s hs
    ext i
    simpa using (CokernelCofork.IsColimit.desc' h (Sigma.ι (fun _ : I => B) i ≫ s) _).2
  · intro Z s hs m hm
    ext i
    apply Cofork.IsColimit.hom_ext h
    simp only [Sigma.ι_comp_desc, CokernelCofork.π_ofπ]
    change b ≫ _ = b ≫ (CokernelCofork.IsColimit.desc' h _ _).1
    exact (show b ≫ Sigma.ι (fun _ : I => M) i ≫ m =
        Sigma.ι (fun _ : I => B) i ≫ s by
      simpa using congrArg (fun f => Sigma.ι (fun _ : I => B) i ≫ f) hm).trans
        (CokernelCofork.IsColimit.desc' h _ _).2.symm


/-- A map out of a coproduct is a family of maps out of its summands. -/
noncomputable def cofanHomEquiv
    {D : Type*} [Category D] {I : Type*} {A M N : D}
    (ι : I → (A ⟶ M)) (h : IsColimit (Cofan.mk M ι)) :
    (M ⟶ N) ≃ (I → (A ⟶ N)) where
  toFun f i := ι i ≫ f
  invFun f := Cofan.IsColimit.desc h f
  left_inv f := Cofan.IsColimit.hom_ext h _ _ (fun i => Cofan.IsColimit.fac h _ i)
  right_inv f := by funext i; exact Cofan.IsColimit.fac h f i

end CategoryTheory.Limits

end
