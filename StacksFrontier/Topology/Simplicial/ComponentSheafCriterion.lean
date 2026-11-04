module

public import StacksFrontier.Topology.Simplicial.Sheaves

/-!
# A presheaf on the site of a simplicial space is a sheaf when its components are

Let `X` be a simplicial topological space and `P` a presheaf on its total site, with values in
any category. If for every simplicial degree `n` the restriction of `P` to the opens of `X n` is
a sheaf, then `P` is a sheaf on the total site. The coverings of the total site are the open
coverings inside one degree, so this is the expected statement; it is proved here through the
description of sheaves on the total site as systems of degreewise sheaves (Stacks 09VM): the
components of `P` with the restriction maps of `P` over the simplex maps form such a system, and
the presheaf reconstructed from it is `P`.

## Main results

* `Stacks.Topology.Simplicial.isSheaf_of_isSheaf_componentPresheaf`: a presheaf on the site of a
  simplicial space whose components are sheaves is a sheaf.

## References

* [Stacks Project, Tag 09VM](https://stacks.math.columbia.edu/tag/09VM)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u v w

namespace Stacks.Topology.Simplicial

variable {X : SimplicialObject TopCat.{u}} {A : Type w} [Category.{v} A]

/-- The system of degreewise sheaves of a presheaf on the site of a simplicial space whose
components are sheaves: its components, with the restriction maps over the simplex maps. -/
noncomputable def componentSystemOfIsSheaf (P : (SimplicialOpen X)ᵒᵖ ⥤ A)
    (h : ∀ n, Presheaf.IsSheaf (Opens.grothendieckTopology (X.obj n)) (componentPresheaf P n)) :
    SimplicialSheafSystem X A where
  component n := ⟨componentPresheaf P n, h n⟩
  transition φ := SimplicialSheafSystem.transitionMap P φ
  transition_id n V := SimplicialSheafSystem.transitionMap_id_app P n V
  transition_comp φ ψ V := SimplicialSheafSystem.transitionMap_comp_app P φ ψ V

/-- The presheaf reconstructed from the system of degreewise sheaves of a presheaf is that
presheaf. -/
noncomputable def reconstructedComponentSystemIso (P : (SimplicialOpen X)ᵒᵖ ⥤ A)
    (h : ∀ n, Presheaf.IsSheaf (Opens.grothendieckTopology (X.obj n)) (componentPresheaf P n)) :
    (sheafEquivalenceSimplicialSheafSystem X A).toPresheaf.obj (componentSystemOfIsSheaf P h) ≅
      P := by
  let E := sheafEquivalenceSimplicialSheafSystem X A
  let S := componentSystemOfIsSheaf P h
  let R := E.toPresheaf.obj S
  refine NatIso.ofComponents
    (fun U => ((E.componentIso U.unop.degree).app S).app (op U.unop.toOpens)) ?_
  intro U V f
  let φ := f.unop.base
  let pre : Opens (X.obj V.unop.degree) := (Opens.map (X.map φ)).obj U.unop.toOpens
  let mid : SimplicialOpen X := ⟨V.unop.degree, pre⟩
  let i : V.unop.toOpens ⟶ pre := homOfLE (SimplicialOpen.Hom.le f.unop)
  let a : V.unop ⟶ mid := (levelFunctor X V.unop.degree).map i
  let b : mid ⟶ U.unop := SimplicialSheafSystem.transitionHom φ U.unop.toOpens
  have hf : f.unop = a ≫ b := by
    apply SimplicialOpen.Hom.ext
    exact (Category.id_comp _).symm
  have h1 : f = b.op ≫ a.op := Quiver.Hom.unop_inj hf
  have hR : R.map f = R.map b.op ≫ R.map a.op :=
    (congrArg (fun k : U ⟶ V => R.map k) h1).trans (R.map_comp b.op a.op)
  have hP : P.map f = P.map b.op ≫ P.map a.op :=
    (congrArg (fun k : U ⟶ V => P.map k) h1).trans (P.map_comp b.op a.op)
  let θV := ((E.componentIso V.unop.degree).app S).hom.app (op V.unop.toOpens)
  let θP := ((E.componentIso V.unop.degree).app S).hom.app (op pre)
  let θU := ((E.componentIso U.unop.degree).app S).hom.app (op U.unop.toOpens)
  let tr := (S.transition φ).app (op U.unop.toOpens)
  let ri := (componentPresheaf P V.unop.degree).map i.op
  have hn : R.map a.op ≫ θV = θP ≫ ri :=
    ((E.componentIso V.unop.degree).app S).hom.naturality i.op
  have ht : R.map b.op ≫ θP = θU ≫ tr :=
    E.transition_compatibility S φ (op U.unop.toOpens)
  exact (congrArg (fun k => k ≫ θV) hR).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k => R.map b.op ≫ k) hn).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ ri) ht).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun k => θU ≫ k) hP.symm))))))

/-- **A presheaf on the site of a simplicial space whose components are sheaves is a sheaf.**
The coverings of the site are the open coverings inside one simplicial degree, so the sheaf
condition only involves the restrictions of the presheaf to the opens of one degree. -/
theorem isSheaf_of_isSheaf_componentPresheaf (P : (SimplicialOpen X)ᵒᵖ ⥤ A)
    (h : ∀ n, Presheaf.IsSheaf (Opens.grothendieckTopology (X.obj n)) (componentPresheaf P n)) :
    Presheaf.IsSheaf (SimplicialOpen.grothendieckTopology X) P := by
  let E := sheafEquivalenceSimplicialSheafSystem X A
  let S := componentSystemOfIsSheaf P h
  let Q := E.toEquivalence.inverse.obj S
  let e : Q.obj ≅ P :=
    (E.underlyingPresheafIso.app Q).symm ≪≫
      E.toPresheaf.mapIso (E.toEquivalence.counitIso.app S) ≪≫
        reconstructedComponentSystemIso P h
  exact (Presheaf.isSheaf_of_iso_iff e).mp Q.property

end Stacks.Topology.Simplicial

end
