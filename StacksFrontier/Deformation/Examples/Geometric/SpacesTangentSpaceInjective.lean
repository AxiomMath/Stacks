module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceInjectiveTotalSpaceIso

/-!
# Injectivity of the class map of deformations of an algebraic space

In the situation of Stacks 0E3Z, two deformations `x, x'` of the algebraic space `X` over `k[V]`
with the same class in `Ext¹(NL_{X/k}, 𝒪_X ⊗_k V)` (`Deformation.Examples.spaceTangentFiberClass`)
are isomorphic: equal classes give isomorphic extensions (Stacks 0GQ5,
`AlgebraicGeometry.Space.nonempty_iso_of_modelExtClass_eq`), isomorphic extensions give an
isomorphism of the total spaces under `X` and over `Spec k[V]` (Stacks 05YZ, 05Z1,
`Deformation.Examples.exists_iso_spaceDefoArrow_comp_eq_of_iso`), and such an isomorphism is an
isomorphism of deformations: an isomorphism of total spaces over `Spec k[V]` is a cartesian square.

Consequently the class map on isomorphism classes of deformations over `k[ε]`
(`Deformation.Examples.spaceTangentExtClassAt` at `V = k`) is injective: this is the injectivity
half of the bijection `T Def_X → Ext¹(NL_{X/k}, 𝒪_X)` of the second display of
[Stacks Project, Tag 0E41].

## Main results

* `Deformation.Examples.isIsomorphic_of_spaceTangentFiberClass_eq`: deformations over `k[V]` with
  the same class are isomorphic.
* `Deformation.Examples.spaceTangentExtClassAt_injective`: the class map at `V = k` is injective.

## References

* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Tag 05YZ](https://stacks.math.columbia.edu/tag/05YZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Space Deformation.Artin Deformation.AlgebraExtension

universe u

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

/-- The spectrum of an identification of objects of `𝒞_Λ` is the identification of the
spectra. -/
theorem spaceBaseOverMap_eqToHom {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k} (h : A = A') :
    spaceBaseOverMap B hΛ hSpec (eqToHom h) =
      eqToHom (congrArg (spaceBaseOver B hΛ hSpec) h.symm) := by
  subst h
  exact spaceBaseOverMap_id B hΛ hSpec A

section Iso

variable {V : FGModuleCat.{u} k}
  (x x' : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
    ((squareZeroExtensionArtinian Λ k).obj V))
  (f : spaceTotalSpace B hΛ hSpec x.1.left ≅ spaceTotalSpace B hΛ hSpec x'.1.left)
  (harr : spaceDefoArrow B hΛ hSpec X hX toK x.1 ≫ f.hom = spaceDefoArrow B hΛ hSpec X hX toK x'.1)
  (hstr : f.hom ≫ spaceTangentStructureMap B hΛ hSpec X hX toK x' =
    spaceTangentStructureMap B hΛ hSpec X hX toK x)

/-- The identification of the coefficient algebras of two points over `k[V]`. -/
theorem spaceFiber_base_eq_base :
    x.1.left.base = x'.1.left.base :=
  (spaceFiber_base_eq B hΛ hSpec X hX toK x).trans (spaceFiber_base_eq B hΛ hSpec X hX toK x').symm

include hstr in
/-- An isomorphism of total spaces over `Spec k[V]` commutes with the structure morphisms to the
spectra of the coefficient algebras, through their identification. -/
theorem inv_comp_toBase_eq :
    f.inv.hom ≫ x.1.left.toBase = x'.1.left.toBase ≫ yoneda.map
      (spaceBaseOverMap B hΛ hSpec
        (eqToHom (spaceFiber_base_eq_base B hΛ hSpec X hX toK x x'))) := by
  have hh := congrArg (fun g => g.hom) hstr
  change f.hom.hom ≫ x'.1.left.toBase ≫ yoneda.map (spaceBaseOverMap B hΛ hSpec
      (eqToHom (spaceFiber_base_eq B hΛ hSpec X hX toK x').symm)) =
    x.1.left.toBase ≫ yoneda.map (spaceBaseOverMap B hΛ hSpec
      (eqToHom (spaceFiber_base_eq B hΛ hSpec X hX toK x).symm)) at hh
  rw [spaceBaseOverMap_eqToHom, spaceBaseOverMap_eqToHom, eqToHom_map, eqToHom_map] at hh
  rw [spaceBaseOverMap_eqToHom, eqToHom_map]
  have hinv : f.inv.hom ≫ f.hom.hom = 𝟙 _ := congrArg (fun g => g.hom) f.inv_hom_id
  calc f.inv.hom ≫ x.1.left.toBase =
        f.inv.hom ≫ (x.1.left.toBase ≫ eqToHom (congrArg (yoneda.obj)
          (congrArg (spaceBaseOver B hΛ hSpec) (spaceFiber_base_eq B hΛ hSpec X hX toK x)))) ≫
          eqToHom (congrArg (yoneda.obj)
            (congrArg (spaceBaseOver B hΛ hSpec)
              (spaceFiber_base_eq B hΛ hSpec X hX toK x))).symm := by
        simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    _ = (f.inv.hom ≫ f.hom.hom) ≫ x'.1.left.toBase ≫ eqToHom _ := by
        rw [← hh]
        simp only [Category.assoc, eqToHom_trans]
    _ = _ := by rw [hinv, Category.id_comp]

/-- **The morphism of flat families given by an isomorphism of total spaces over `Spec k[V]`**:
the identification of the coefficient algebras, and the inverse of the isomorphism, whose square
over the identification of the spectra is cartesian because both are isomorphisms. -/
def spaceFamilyHomOfIso : x.1.left ⟶ x'.1.left where
  base := eqToHom (spaceFiber_base_eq_base B hΛ hSpec X hX toK x x')
  map := f.inv.hom
  cartesian := by
    have : IsIso f.inv.hom := (ObjectProperty.ι _).map_isIso f.inv
    have : IsIso (yoneda.map (spaceBaseOverMap B hΛ hSpec
        (eqToHom (spaceFiber_base_eq_base B hΛ hSpec X hX toK x x')))) := by
      rw [spaceBaseOverMap_eqToHom, eqToHom_map]
      infer_instance
    exact IsPullback.of_horiz_isIso ⟨inv_comp_toBase_eq B hΛ hSpec X hX toK x x' f hstr⟩

include harr in
/-- The morphism of flat families given by an isomorphism of total spaces under `X` is a
morphism of the deformation category. -/
theorem spaceFamilyHomOfIso_comp :
    spaceFamilyHomOfIso B hΛ hSpec X hX toK x x' f hstr ≫ x'.1.hom = x.1.hom := by
  apply FlatAlgebraicSpaceFamily.Hom.ext
  · exact isTerminal_residueFieldBase.hom_ext _ _
  · show x'.1.hom.map ≫ f.inv.hom = x.1.hom.map
    have h := congrArg (fun g => (g ≫ f.inv).hom) harr
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
    exact h.symm

/-- **The morphism of deformations given by an isomorphism of total spaces under `X` and over
`Spec k[V]`**, a morphism of the fibre over `k[V]`. -/
def spaceFiberHomOfIso : x ⟶ x' :=
  ⟨Over.homMk (spaceFamilyHomOfIso B hΛ hSpec X hX toK x x' f hstr)
      (spaceFamilyHomOfIso_comp B hΛ hSpec X hX toK x x' f harr hstr),
    IsHomLift.of_fac' _ _ _ x.2 x'.2 (by
      change eqToHom (spaceFiber_base_eq_base B hΛ hSpec X hX toK x x') = _
      simp only [eqToHom_trans, Category.id_comp])⟩

include harr in
/-- The inverse of an isomorphism of total spaces under `X` is under `X`. -/
theorem spaceDefoArrow_comp_inv :
    spaceDefoArrow B hΛ hSpec X hX toK x'.1 ≫ f.inv = spaceDefoArrow B hΛ hSpec X hX toK x.1 := by
  rw [← harr, Category.assoc, Iso.hom_inv_id, Category.comp_id]

include hstr in
/-- The inverse of an isomorphism of total spaces over `Spec k[V]` is over `Spec k[V]`. -/
theorem inv_comp_spaceTangentStructureMap :
    f.inv ≫ spaceTangentStructureMap B hΛ hSpec X hX toK x =
      spaceTangentStructureMap B hΛ hSpec X hX toK x' := by
  rw [← hstr, Iso.inv_hom_id_assoc]

/-- **An isomorphism of total spaces under `X` and over `Spec k[V]` is an isomorphism of
deformations.** -/
def spaceFiberIsoOfIso : x ≅ x' where
  hom := spaceFiberHomOfIso B hΛ hSpec X hX toK x x' f harr hstr
  inv := spaceFiberHomOfIso B hΛ hSpec X hX toK x' x f.symm
    (spaceDefoArrow_comp_inv B hΛ hSpec X hX toK x x' f harr)
    (inv_comp_spaceTangentStructureMap B hΛ hSpec X hX toK x x' f hstr)
  hom_inv_id := by
    apply Functor.Fiber.hom_ext
    apply Over.OverMorphism.ext
    apply FlatAlgebraicSpaceFamily.Hom.ext
    · change eqToHom (spaceFiber_base_eq_base B hΛ hSpec X hX toK x x') ≫
        eqToHom (spaceFiber_base_eq_base B hΛ hSpec X hX toK x' x) = 𝟙 _
      simp only [eqToHom_trans, eqToHom_refl]
    · change f.hom.hom ≫ f.inv.hom = 𝟙 _
      exact congrArg (fun g => g.hom) f.hom_inv_id
  inv_hom_id := by
    apply Functor.Fiber.hom_ext
    apply Over.OverMorphism.ext
    apply FlatAlgebraicSpaceFamily.Hom.ext
    · change eqToHom (spaceFiber_base_eq_base B hΛ hSpec X hX toK x' x) ≫
        eqToHom (spaceFiber_base_eq_base B hΛ hSpec X hX toK x x') = 𝟙 _
      simp only [eqToHom_trans, eqToHom_refl]
    · change f.inv.hom ≫ f.hom.hom = 𝟙 _
      exact congrArg (fun g => g.hom) f.inv_hom_id

end Iso

/-- **Deformations over `k[V]` with the same class are isomorphic**: two deformations of `X`
over `k[V]` with the same class in `Ext¹(NL_{X/k}, 𝒪_X ⊗_k V)` have isomorphic extensions
(Stacks 0GQ5), hence isomorphic total spaces under `X` and over `Spec k[V]` (Stacks 05YZ,
05Z1), hence are isomorphic deformations. -/
theorem isIsomorphic_of_spaceTangentFiberClass_eq {V : FGModuleCat.{u} k}
    (x x' : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
      ((squareZeroExtensionArtinian Λ k).obj V))
    (h : spaceTangentFiberClass B hΛ hSpec X hX toK x =
      spaceTangentFiberClass B hΛ hSpec X hX toK x') :
    IsIsomorphic x x' := by
  obtain ⟨e⟩ := nonempty_iso_of_modelExtClass_eq B (Spec (.of Λ)) hΛ h
  obtain ⟨f, harr, hstr⟩ := exists_iso_spaceDefoArrow_comp_eq_of_iso B hΛ hSpec X hX toK e
  exact ⟨spaceFiberIsoOfIso B hΛ hSpec X hX toK x x' f harr hstr⟩

/-- **The class map of deformations over `k[ε]` is injective**: two first-order deformations of
`X` with the same class in `Ext¹(NL_{X/k}, 𝒪_X)` are isomorphic. This is the injectivity half of
the bijection `T Def_X ≅ Ext¹(NL_{X/k}, 𝒪_X)` of the second display of Stacks 0E41. -/
theorem spaceTangentExtClassAt_injective :
    Function.Injective (spaceTangentExtClassAt B hΛ hSpec X hX toK (FGModuleCat.of k k)) := by
  intro z z' h
  obtain ⟨x, rfl⟩ := classOf_surjective (spaceDeformationBased B hΛ hSpec X hX toK)
    (spaceDeformation_cofibered B hΛ hSpec X hX toK)
    ((squareZeroExtensionArtinian Λ k).obj (FGModuleCat.of k k)) z
  obtain ⟨x', rfl⟩ := classOf_surjective (spaceDeformationBased B hΛ hSpec X hX toK)
    (spaceDeformation_cofibered B hΛ hSpec X hX toK)
    ((squareZeroExtensionArtinian Λ k).obj (FGModuleCat.of k k)) z'
  have h₁ := spaceTangentExtClassAt_classOf B hΛ hSpec X hX toK (FGModuleCat.of k k) x
  have h₂ := spaceTangentExtClassAt_classOf B hΛ hSpec X hX toK (FGModuleCat.of k k) x'
  exact classOf_eq_of_isIsomorphic _ _ x x'
    (isIsomorphic_of_spaceTangentFiberClass_eq B hΛ hSpec X hX toK x x'
      (h₁.symm.trans (h.trans h₂)))

end Deformation.Examples

end
