module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsBetweenCategories.ModuleEquivalences
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.AffineReconstruction
public import StacksFrontier.CategoryTheory.Center.Equivalence

/-!
# The centre of the quasi-coherent modules on an affine scheme

Let `W` be an affine scheme.  The centre of `QCoh(𝒪_W)` — the ring of endomorphisms of its
identity functor, `CategoryTheory.CatCenter` — is the ring `Γ(W, ⊤)` of global sections, acting
by scalar multiplication.  This file records the consequence that the reconstruction of
[Stacks, Tag 0GPJ] needs: **an endomorphism of the identity functor of `QCoh(𝒪_W)` which is the
identity at the structure sheaf is the identity**.

The two ingredients are already in the library and this file only composes them.  Modules over
`Γ(W, ⊤)` are the quasi-coherent `𝒪_W`-modules
(`AlgebraicGeometry.affineQuasicoherentModulesEquiv`), the centre of `ModuleCat R` is `R`
(`ModuleCat.centerRingEquiv`), and the centre is transported along an equivalence by
`CategoryTheory.CatCenter.transportEquiv`.  Under that chain an endomorphism of the identity
functor is multiplication by a global section `r`, and the structure sheaf corresponds to the
regular module, on which multiplication by `r` is the identity only for `r = 1`.

## Why this is wanted

The gluing step of [Stacks, Tag 0GPJ] produces a natural isomorphism
`e(F)|_{V i} ≅ (g^*F ⊗ M)|_{V i}` over each member of an open cover of `Y`, each obtained from
an existential choice, hence determined only up to an automorphism of the functor
`F ↦ (g^*F ⊗ M)|_{V i}`.  Two of them over an open `W` contained in two members of the cover
therefore differ by such an automorphism, and the family can only be glued once that difference
is known to be trivial.  Normalising the family by its value at `𝒪_X` reduces the difference to
an endomorphism of the identity functor of `QCoh(𝒪_W)` which is the identity at the structure
sheaf; this file is the statement that such an endomorphism is the identity.

## Main results

* `CategoryTheory.CatCenter.app_eq_id_of_iso` — an endomorphism of the identity functor which
  is the identity at an object is the identity at every isomorphic object.
* `AlgebraicGeometry.restrictUnitIsoAffineQuasicoherentModulesEquiv` — the image of the regular
  module `Γ(W, ⊤)` under `AlgebraicGeometry.affineQuasicoherentModulesEquiv` is the structure
  sheaf.
* `AlgebraicGeometry.catCenter_eq_one_of_app_unit_eq_id` — **an endomorphism of the identity
  functor of `QCoh(𝒪_W)`, `W` affine, which is the identity at a quasi-coherent module whose
  underlying module is the structure sheaf, is the identity.**

## References

* [Stacks Project, Lemma 28.7.5 (Tag 01I8)](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace CategoryTheory.CatCenter

/-- **An endomorphism of the identity functor is determined at isomorphic objects.**  If it is
the identity at `A` and `A ≅ B`, then it is the identity at `B`: naturality along the
isomorphism turns the one statement into the other, and the isomorphism may be cancelled. -/
theorem app_eq_id_of_iso {C : Type u} [Category.{v} C] (z : CatCenter C) {A B : C} (φ : A ≅ B)
    (h : z.app A = 𝟙 A) : z.app B = 𝟙 B := by
  have hnat : φ.hom ≫ z.app B = z.app A ≫ φ.hom := z.naturality φ.hom
  rw [h, Category.id_comp] at hnat
  exact (cancel_epi φ.hom).mp (hnat.trans (Category.comp_id φ.hom).symm)

end CategoryTheory.CatCenter

namespace AlgebraicGeometry

variable (W : Scheme.{u}) [IsAffine W]

/-- **The regular module is the structure sheaf.**  Under the equivalence
`AlgebraicGeometry.affineQuasicoherentModulesEquiv` between `Γ(W, ⊤)`-modules and quasi-coherent
`𝒪_W`-modules, the regular module `Γ(W, ⊤)` goes to `𝒪_W`.

The equivalence followed by the inclusion of the quasi-coherent modules is, on the nose,
`tilde` followed by restriction along `W.isoSpec.hom`
(`AlgebraicGeometry.affineQuasicoherentModulesEquiv_functor_comp_ι`); the tilde of the regular
module is the structure sheaf of `Spec Γ(W, ⊤)` on the nose as well
(`AlgebraicGeometry.tilde.tildeSelf`), and restriction along an open immersion takes the
structure sheaf to the structure sheaf (`AlgebraicGeometry.Scheme.Modules.restrictUnitIso`). -/
def restrictUnitIsoAffineQuasicoherentModulesEquiv :
    ((affineQuasicoherentModulesEquiv W).functor.obj
        (ModuleCat.of Γ(W, ⊤) Γ(W, ⊤))).obj ≅ SheafOfModules.unit W.ringCatSheaf :=
  have : IsOpenImmersion W.isoSpec.hom := IsOpenImmersion.of_isIso W.isoSpec.hom
  Scheme.Modules.restrictUnitIso W.isoSpec.hom

/-- **The centre of `QCoh(𝒪_W)` for `W` affine is detected at the structure sheaf.**  An
endomorphism `z` of the identity functor of the category of quasi-coherent `𝒪_W`-modules which
is the identity at a quasi-coherent module whose underlying module is `𝒪_W` is the identity.

Transport `z` across `AlgebraicGeometry.affineQuasicoherentModulesEquiv` to an endomorphism of
the identity functor of `ModuleCat Γ(W, ⊤)`; by `ModuleCat.centerRingEquiv` that is
multiplication by a global section `r`.  The hypothesis, read at the regular module — which is
the structure sheaf, by
`AlgebraicGeometry.restrictUnitIsoAffineQuasicoherentModulesEquiv` — says that multiplication by
`r` on `Γ(W, ⊤)` is the identity, so `r = 1`. -/
theorem catCenter_eq_one_of_app_unit_eq_id
    (z : CatCenter (SheafOfModules.isQuasicoherent W.ringCatSheaf).FullSubcategory)
    (A : (SheafOfModules.isQuasicoherent W.ringCatSheaf).FullSubcategory)
    (hA : Nonempty (A.obj ≅ SheafOfModules.unit W.ringCatSheaf)) (h : z.app A = 𝟙 A) :
    z = 1 := by
  set E := affineQuasicoherentModulesEquiv W with hE
  -- `z` is the transport of a central element of `ModuleCat Γ(W, ⊤)`, i.e. of a scalar.
  obtain ⟨w, hw⟩ : ∃ w : CatCenter (ModuleCat.{u} Γ(W, ⊤)), CatCenter.transport E w = z :=
    ⟨(CatCenter.transportEquiv E).symm z, (CatCenter.transportEquiv E).apply_symm_apply z⟩
  obtain ⟨r, hr⟩ := (ModuleCat.center_toCatCenter_bijective Γ(W, ⊤)).surjective w
  -- Read the hypothesis at the image of the regular module.
  have hiso : A ≅ E.functor.obj (ModuleCat.of Γ(W, ⊤) Γ(W, ⊤)) :=
    (ObjectProperty.fullyFaithfulι (SheafOfModules.isQuasicoherent W.ringCatSheaf)).preimageIso
      (hA.some ≪≫ (restrictUnitIsoAffineQuasicoherentModulesEquiv W).symm)
  have hunit : z.app (E.functor.obj (ModuleCat.of Γ(W, ⊤) Γ(W, ⊤))) = 𝟙 _ :=
    CatCenter.app_eq_id_of_iso z hiso h
  -- Hence `r • 𝟙` is the identity of the regular module, so `r = 1`.
  rw [← hw, CatCenter.transport_app_functor] at hunit
  have hmap : w.app (ModuleCat.of Γ(W, ⊤) Γ(W, ⊤)) = 𝟙 _ := E.functor.map_injective (by
    simpa using hunit)
  have hr1 : r = 1 := by
    have := congrArg (fun φ : ModuleCat.of Γ(W, ⊤) Γ(W, ⊤) ⟶ ModuleCat.of Γ(W, ⊤) Γ(W, ⊤) =>
      ConcreteCategory.hom φ (1 : Γ(W, ⊤))) hmap
    simpa [← hr, CategoryTheory.Linear.toCatCenter_apply_app] using this
  rw [← hw, ← hr, hr1, map_one, CatCenter.transport_one]

end AlgebraicGeometry

end
