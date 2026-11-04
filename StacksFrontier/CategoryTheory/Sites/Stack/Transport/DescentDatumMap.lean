module

public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.FiberComparison

/-!
# The image of a descent datum under an equivalence over the base

A descent datum in `𝒳` relative to a sieve is carried to one in `𝒴` by the forward functor of an
equivalence over `𝒞`: the objects are transported by
`CategoryTheory.BasedCategory.Equivalence.fiberMapFunctor` and the gluing isomorphisms are
conjugated by `CategoryTheory.BasedCategory.Equivalence.pullbackFiberFunctorFiberIso`.

## Main definitions

* `CategoryTheory.Functor.SieveDescentDatum.mapEquiv`, the image of a descent datum under the
  forward functor of an equivalence over `𝒞`.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

namespace BasedCategory.Equivalence

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒞} {𝒴 : BasedCategory.{v₃, u₃} 𝒞}
  (e : BasedCategory.Equivalence 𝒳 𝒴)

-- Every declaration below is a statement about `e`, but several mention it only in their proofs.
include e

open _root_.CategoryTheory.Functor

/-- The image of a descent datum under the forward functor of an equivalence over `𝒞`: its objects
are transported by `fiberMapFunctor`, and its gluing isomorphisms are conjugated by
`pullbackFiberFunctorFiberIso`. -/
noncomputable def _root_.CategoryTheory.Functor.SieveDescentDatum.mapEquiv [𝒳.p.IsFibered]
    [𝒴.p.IsFibered] {U : 𝒞} {R : Sieve U} (D : SieveDescentDatum 𝒳.p R) :
    SieveDescentDatum 𝒴.p R where
  obj _ f hf := e.fiberMap (D.obj f hf)
  iso {V W Z} {f} hf {g} hg ε ε' heq :=
    (e.pullbackFiberFunctorFiberIso (D.obj f hf) ε).symm ≪≫
      (e.fiberMapFunctor Z).mapIso (D.iso hf hg ε ε' heq) ≪≫
      e.pullbackFiberFunctorFiberIso (D.obj g hg) ε'
  cocycle {V W X Z} {f} hf {g} hg {h} hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃ := by
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
      Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc, D.cocycle hf hg hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃]
  iso_pullback {V W Z Z'} {f} hf {g} hg ε ε' heq γ := by
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
      pullbackFiberIso_hom, pullbackFiberHom_comp]
    rw [← D.iso_pullback hf hg ε ε' heq γ]
    simp only [pullbackFiberIso_hom, Functor.map_comp, Category.assoc,
      ← e.pullbackFiberFunctorFiberIso_comp_inv_assoc (D.obj f hf) ε γ]
    rw [← e.pullbackFiberFunctorFiberIso_naturality_assoc (D.iso hf hg ε ε' heq).hom γ,
      ← e.pullbackFiberFunctorFiberIso_comp (D.obj g hg) ε' γ]

/-- The object of a transported descent datum over an arrow of the sieve is the image under
`CategoryTheory.BasedCategory.Equivalence.fiberMap` of the original object. -/
@[simp]
lemma _root_.CategoryTheory.Functor.SieveDescentDatum.mapEquiv_obj [𝒳.p.IsFibered] [𝒴.p.IsFibered]
    {U : 𝒞} {R : Sieve U} (D : SieveDescentDatum 𝒳.p R) ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f) :
    (D.mapEquiv e).obj f hf = e.fiberMap (D.obj f hf) := rfl

/-- The gluing isomorphism of a transported descent datum is the image of the original gluing
isomorphism, conjugated by
`CategoryTheory.BasedCategory.Equivalence.pullbackFiberFunctorFiberIso`. -/
@[simp]
lemma _root_.CategoryTheory.Functor.SieveDescentDatum.mapEquiv_iso [𝒳.p.IsFibered] [𝒴.p.IsFibered]
    {U : 𝒞} {R : Sieve U} (D : SieveDescentDatum 𝒳.p R) ⦃V W Z : 𝒞⦄ ⦃f : V ⟶ U⦄ (hf : R f)
    ⦃g : W ⟶ U⦄ (hg : R g) (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    (D.mapEquiv e).iso hf hg ε ε' heq =
      (e.pullbackFiberFunctorFiberIso (D.obj f hf) ε).symm ≪≫
        (e.fiberMapFunctor Z).mapIso (D.iso hf hg ε ε' heq) ≪≫
        e.pullbackFiberFunctorFiberIso (D.obj g hg) ε' := rfl

end BasedCategory.Equivalence

end CategoryTheory
