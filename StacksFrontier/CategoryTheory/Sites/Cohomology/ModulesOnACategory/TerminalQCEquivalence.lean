module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalMorphismOfSitesEquivalence
public import StacksFrontier.Homology.DerivedCategory.ModelComparison

/-!
# Quasi-coherent objects on a site with a final object, as an equivalence

Let `C` be a category with a final object `X`, viewed as a site with the chaotic topology, and
`O` a presheaf of commutative rings on it. Stacks 0H0R (`main_equivalence`) shows that the derived
pullback `Lf^*` along the morphism of sites `f : (C, O) → (pt, O(X))` and the derived global
sections `RΓ(X, -)` are mutually quasi-inverse between `D(O(X))` and `QC(O)`. This file packages
those three assertions as an equivalence of categories `QC(O) ≌ D(O(X))` whose functor is
`RΓ(X, -)` and whose quasi-inverse is `Lf^*`, for any model of `D(O(X))`.

## Main definitions

* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.qcEquivalenceOfTerminalStandard`: the
  equivalence into the model of `D(O(X))` in which `RΓ(X, -)` lands.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.qcEquivalenceOfTerminal`: the equivalence
  into any model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange (baseChangeDataOfComm)
open Stacks.ModulesOnACategory.TerminalMorphismOfSites (morphismOfSites)

universe w w' u v r

namespace Stacks.ModulesOnACategory.QuasiCoherentEquivalence

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ RingCat.{r}} {X : C} (hX : IsTerminal X)
  (hO : ∀ (U : Cᵒᵖ) (x y : O.obj U), x * y = y * x)

/-- **The quasi-coherent objects on a site with a final object `X` are the derived category of
`O(X)`** (Stacks 0H0R), as an equivalence `QC(O) ≌ D(O(X))` given by the derived global sections
`RΓ(X, -)`, with quasi-inverse the derived pullback along the morphism of sites of `X`; here
`D(O(X))` is the model in which `RΓ(X, -)` lands. -/
def qcEquivalenceOfTerminalStandard :
    QC.{w} (baseChangeDataOfComm.{r, v, u, w} O hO) ≌
      @DerivedCategory (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) _ _
        (HasDerivedCategory.standard _) :=
  let mos := morphismOfSites.{w} O hO hX
  have h := main_equivalence.{w} hX hO
  CategoryTheory.Equivalence.mk
    (QCι.{w} (baseChangeDataOfComm.{r, v, u, w} O hO) ⋙ RGamma.{w} O (Opposite.op X))
    (ObjectProperty.lift _ mos.Lpullback h.1)
    (NatIso.ofComponents
      (fun K => ObjectProperty.isoMk _
        (@asIso _ _ _ _ (mos.adj.counit.app K.obj) (h.2.2 K.obj K.property)).symm)
      (fun {K L} f => by
        have := h.2.2 K.obj K.property
        have := h.2.2 L.obj L.property
        apply ObjectProperty.hom_ext
        simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map,
          ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.isoMk_hom,
          ObjectProperty.homMk_hom, Iso.symm_hom, asIso_inv, ObjectProperty.lift_map,
          ObjectProperty.ι_map]
        rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
        exact (mos.adj.counit.naturality f.hom).symm))
    (NatIso.ofComponents
      (fun P => (@asIso _ _ _ _ (mos.adj.unit.app P) (h.2.1 P)).symm)
      (fun {P Q} g => by
        have := h.2.1 P
        have := h.2.1 Q
        dsimp
        rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
        exact (mos.adj.unit.naturality g).symm))

variable [HasDerivedCategory.{w'} (ModuleCat.{max u v r w} (O.obj (Opposite.op X)))]

/-- **The quasi-coherent objects on a site with a final object `X` are the derived category of
`O(X)`** (Stacks 0H0R), for any model of `D(O(X))`: the equivalence
`qcEquivalenceOfTerminalStandard` followed by the comparison of models. -/
def qcEquivalenceOfTerminal :
    QC.{w} (baseChangeDataOfComm.{r, v, u, w} O hO) ≌
      DerivedCategory (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) :=
  (qcEquivalenceOfTerminalStandard.{w} hX hO).trans
    (StacksDraft.DerivedModel.modelEquiv (HasDerivedCategory.standard _) inferInstance)

end Stacks.ModulesOnACategory.QuasiCoherentEquivalence

end
