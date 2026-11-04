module

public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateNaturality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackTensorComp

/-!
# Two comparisons of left adjoints of a composite

Let `Lf ⊣ Rf`, `Lg ⊣ Rg` and `Lfg ⊣ Rfg` be adjunctions, and let the right adjoints be given in two
presentations, related by isomorphisms `ef : Rf ≅ Rf'`, `eg : Rg ≅ Rg'` and `efg : Rfg ≅ Rfg'`.
A comparison `c : Rf ⋙ Rg ≅ Rfg` of right adjoints in the first presentation and a comparison
`c' : Rf' ⋙ Rg' ≅ Rfg'` in the second each induce, by uniqueness of left adjoints, a comparison
`Lg ⋙ Lf ≅ Lfg` of left adjoints.  If `c` and `c'` correspond under the isomorphisms of
presentations, the two comparisons of left adjoints are the same.

## Main results

* `CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_comp_eq_symm`: the two comparisons of
  left adjoints agree as soon as the two comparisons of right adjoints correspond.

## Implementation notes

The statement is phrased with the second comparison of left adjoints read backwards, in the
shape in which `Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso` is defined; the proof
compares the conjugates of the two sides.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

/-- **Two presentations of the right adjoints give the same comparison of left adjoints.**  Let
`ef`, `eg`, `efg` identify two presentations of the right adjoints of three adjunctions, and let
`c` and `c'` compare the composite right adjoint with the third one in each presentation.  If `c`
and `c'` correspond under `ef`, `eg` and `efg`, then the comparison `Lg ⋙ Lf ≅ Lfg` of left
adjoints induced by `c'` is the inverse of the comparison induced by `c`. -/
theorem leftAdjointUniq_ofNatIsoRight_comp_eq_symm
    {CX CY CZ : Type*} [Category CX] [Category CY] [Category CZ]
    {Lf : CY ⥤ CX} {Lg : CZ ⥤ CY} {Lfg : CZ ⥤ CX}
    {Rf Rf' : CX ⥤ CY} {Rg Rg' : CY ⥤ CZ} {Rfg Rfg' : CX ⥤ CZ}
    (af : Lf ⊣ Rf) (ag : Lg ⊣ Rg) (afg : Lfg ⊣ Rfg)
    (ef : Rf ≅ Rf') (eg : Rg ≅ Rg') (efg : Rfg ≅ Rfg')
    (c : Rf ⋙ Rg ≅ Rfg) (c' : Rf' ⋙ Rg' ≅ Rfg')
    (hc : ∀ M, (Rg.map (ef.hom.app M) ≫ eg.hom.app (Rf'.obj M)) ≫ c'.hom.app M =
      c.hom.app M ≫ efg.hom.app M) :
    Adjunction.leftAdjointUniq
        (((ag.ofNatIsoRight eg).comp (af.ofNatIsoRight ef)).ofNatIsoRight c')
        (afg.ofNatIsoRight efg) =
      (Adjunction.leftAdjointUniq (afg.ofNatIsoRight c.symm) (ag.comp af)).symm := by
  refine Iso.ext ((conjugateEquiv (afg.ofNatIsoRight efg)
    ((ag.ofNatIsoRight eg).comp (af.ofNatIsoRight ef))).injective ?_)
  rw [Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom,
    Adjunction.comp_ofNatIsoRight, Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight]
  have hconj : conjugateEquiv afg (ag.comp af)
      (Adjunction.leftAdjointUniq (afg.ofNatIsoRight c.symm) (ag.comp af)).symm.hom = c.inv := by
    have h := conjugateEquiv_comm (ag.comp af) afg
      (α := (Adjunction.leftAdjointUniq (afg.ofNatIsoRight c.symm) (ag.comp af)).hom)
      (β := (Adjunction.leftAdjointUniq (afg.ofNatIsoRight c.symm) (ag.comp af)).inv)
      (Iso.inv_hom_id _)
    rw [Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom] at h
    simp only [Iso.symm_inv] at h
    rw [Iso.symm_hom]
    exact (Iso.hom_comp_eq_id c).mp h
  rw [hconj]
  ext M
  simp only [NatTrans.comp_app, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← cancel_mono (c'.hom.app M)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← Category.assoc (Rg.map (ef.hom.app M)), hc M]
  simp

end CategoryTheory.Adjunction

end
