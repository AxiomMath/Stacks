module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianExtensionByZeroCounit
import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of an extension by zero of a map of abelian sheaves

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` and let `x̄` be a
geometric point of `Y`.  Equation 08GU identifies the stalk at `x̄` of `f_!G` with the direct sum
over the lifts `t` of `x̄` of the stalks of `G` at those lifts, naturally in `G`.  So the stalk at
`x̄` of `f_!ψ`, for a map `ψ` of abelian sheaves on `X`, is the direct sum of the stalks of `ψ` at
the lifts, and it is invertible as soon as every one of those is.

## Main results

* `AlgebraicGeometry.Space.EtaleShriekStalk.isIso_of_sigma_ι_comp`: a map of direct sums which is
  given on each summand by an invertible map of summands is invertible.
* `AlgebraicGeometry.Space.EtaleShriekStalk.isIso_sheafFiber_extensionByZero_map`: **the stalk of
  an extension by zero of a map is invertible as soon as the stalks of that map at all the lifts
  are.**

## References

* [Stacks Project, Tag 08GU](https://stacks.math.columbia.edu/tag/08GU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace EtaleShriekStalk

/-- **A map of direct sums of abelian groups which acts on each summand by an isomorphism of
summands is an isomorphism**, with inverse assembled from the inverses on the summands. -/
def sigmaIso {I : Type u} (K K' : I → AddCommGrpCat.{u}) (m : (∐ K) ⟶ (∐ K'))
    (φ : ∀ i, K i ≅ K' i)
    (h : ∀ i, Sigma.ι K i ≫ m = (φ i).hom ≫ Sigma.ι K' i) : (∐ K) ≅ (∐ K') where
  hom := m
  inv := Sigma.desc fun i => (φ i).inv ≫ Sigma.ι K i
  hom_inv_id := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [← Category.assoc, h i, Category.assoc, Sigma.ι_comp_desc, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [← Category.assoc, Sigma.ι_comp_desc, Category.assoc, h i, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp, Category.comp_id]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
  (x : GeometricPoint B S hS Y.1)

/-- **The stalk of an extension by zero of a map of abelian sheaves is the direct sum of the
stalks of that map at the lifts**, hence invertible as soon as all of those are. -/
@[stacks 08GU "the stalk of an extension by zero of a map"]
theorem isIso_sheafFiber_extensionByZero_map
    {G H : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}} (ψ : G ⟶ H)
    (hψ : ∀ t : GeometricPointLift B S hS f.hom x,
      IsIso ((liftSitePoint B S hS f t).sheafFiber.map ψ)) :
    IsIso ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
      ((abelianEtaleExtensionByZero B S hS f hf).map ψ)) := by
  have hι : ∀ t : GeometricPointLift B S hS f.hom x,
      Sigma.ι (fun s : GeometricPointLift B S hS f.hom x =>
          (liftSitePoint B S hS f s).sheafFiber.obj G) t ≫
        (stalkFamily B S hS f x ⋙
          Sigma.functor (GeometricPointLift B S hS f.hom x)).map ψ =
      (liftSitePoint B S hS f t).sheafFiber.map ψ ≫
        Sigma.ι (fun s : GeometricPointLift B S hS f.hom x =>
          (liftSitePoint B S hS f s).sheafFiber.obj H) t := by
    intro t
    have h := liftedStalkι_map_assoc B S hS f x ψ t (𝟙 _)
    rw [Category.comp_id, Category.comp_id] at h
    exact h
  have hfac : (stalkExtensionByZeroIso B S hS f hf x G).hom ≫
        ((stalkFamily B S hS f x ⋙
            Sigma.functor (GeometricPointLift B S hS f.hom x)).map ψ ≫
          (stalkExtensionByZeroIso B S hS f hf x H).inv) =
      (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
        ((abelianEtaleExtensionByZero B S hS f hf).map ψ) :=
    calc (stalkExtensionByZeroIso B S hS f hf x G).hom ≫
          ((stalkFamily B S hS f x ⋙
              Sigma.functor (GeometricPointLift B S hS f.hom x)).map ψ ≫
            (stalkExtensionByZeroIso B S hS f hf x H).inv)
        = ((stalkExtensionByZeroIso B S hS f hf x G).hom ≫
            (stalkFamily B S hS f x ⋙
              Sigma.functor (GeometricPointLift B S hS f.hom x)).map ψ) ≫
          (stalkExtensionByZeroIso B S hS f hf x H).inv := (Category.assoc _ _ _).symm
      _ = ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
              ((abelianEtaleExtensionByZero B S hS f hf).map ψ) ≫
            (stalkExtensionByZeroIso B S hS f hf x H).hom) ≫
          (stalkExtensionByZeroIso B S hS f hf x H).inv :=
        ((stalkExtensionByZeroIso_naturality B S hS f hf x ψ) =≫
          (stalkExtensionByZeroIso B S hS f hf x H).inv).symm
      _ = (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
              ((abelianEtaleExtensionByZero B S hS f hf).map ψ) ≫
          ((stalkExtensionByZeroIso B S hS f hf x H).hom ≫
            (stalkExtensionByZeroIso B S hS f hf x H).inv) := Category.assoc _ _ _
      _ = (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
            ((abelianEtaleExtensionByZero B S hS f hf).map ψ) := by
        rw [Iso.hom_inv_id, Category.comp_id]
  rw [← hfac]
  exact Iso.isIso_hom (stalkExtensionByZeroIso B S hS f hf x G ≪≫
    sigmaIso _ _ ((stalkFamily B S hS f x ⋙
        Sigma.functor (GeometricPointLift B S hS f.hom x)).map ψ)
      (fun t => @asIso _ _ _ _ ((liftSitePoint B S hS f t).sheafFiber.map ψ) (hψ t)) hι ≪≫
    (stalkExtensionByZeroIso B S hS f hf x H).symm)

end EtaleShriekStalk

end AlgebraicGeometry.Space

end
