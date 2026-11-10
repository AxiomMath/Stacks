module

public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde

/-!
# Invertibility of a pullback of associated sheaves is bijectivity of a base change

Let `φ : R → S` be a homomorphism of commutative rings and let `g : M ⟶ N` be a homomorphism of
`R`-modules. Pullback along `Spec φ` carries the associated sheaf `M^~` to the associated sheaf
of the extension of scalars `S ⊗_R M`, naturally in `M`
(`AlgebraicGeometry.pullbackTildeIso`), and the associated-sheaf functor is fully faithful. So
the pullback of `g^~` along `Spec φ` is invertible **exactly** when `S ⊗_R g` is bijective.

The implication from bijectivity to invertibility is
`AlgebraicGeometry.isIso_pullback_map_tilde`
(`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/OneStep/FreeMap.lean`), stated there for `S` a
field because that is the case its consumer needs. This file supplies the converse, which the
dictionary between the scheme-theoretic and the ring-theoretic complete dévissage needs in order
to read the generic-fibre condition of `AlgebraicGeometry.DevissageStage` as the bijectivity
condition of `Module.CompleteDevissage`.

## Main results

* `AlgebraicGeometry.bijective_baseChange_of_isIso_pullback_map_tilde`: if the pullback along
  `Spec φ` of the associated sheaf of `g` is invertible then `S ⊗_R g` is bijective.
* `AlgebraicGeometry.bijective_rTensor_of_isIso_pullback_map_tilde`: the same, with the base
  change written as `LinearMap.rTensor`, which is the form
  `AlgebraicGeometry.isIso_pullback_map_tilde` is stated in.

## Implementation notes

No hypothesis on `S` is used: the converse holds for an arbitrary homomorphism of commutative
rings, and in particular needs neither a field nor a flatness assumption. The field hypothesis of
`AlgebraicGeometry.isIso_pullback_map_tilde` is likewise not used by its proof; the two together
are a biconditional for any `φ`.

The argument is the forward one read backwards. Naturality of
`AlgebraicGeometry.pullbackTildeIso` turns the hypothesis into invertibility of
`(extendScalars φ ⋙ tilde.functor S).map g`; the associated-sheaf functor is fully faithful by
`AlgebraicGeometry.tilde.fullyFaithfulFunctor`, hence reflects isomorphisms, so
`(extendScalars φ).map g` is invertible; and an invertible morphism of module categories is a
bijective map by `CategoryTheory.ConcreteCategory.isIso_iff_bijective`.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **A pullback of associated sheaves is invertible only if the base change of the map is
bijective.** This is the converse of `AlgebraicGeometry.isIso_pullback_map_tilde`, and holds for
an arbitrary homomorphism of commutative rings. -/
public theorem bijective_baseChange_of_isIso_pullback_map_tilde (R S : Type u) [CommRing R]
    [CommRing S] (f : R →+* S) (M N : ModuleCat.{u} R) (g : M ⟶ N)
    (h : IsIso ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom f))).map
      ((tilde.functor (CommRingCat.of R)).map g))) :
    letI : Algebra R S := f.toAlgebra
    Function.Bijective (g.hom.baseChange S) := by
  let _ : Algebra R S := f.toAlgebra
  set η := pullbackTildeIso (CommRingCat.of R) (CommRingCat.of S) (CommRingCat.ofHom f)
  have hcomp : IsIso (η.hom.app M ≫ (tilde.functor (CommRingCat.of S)).map
      ((ModuleCat.extendScalars (CommRingCat.ofHom f).hom).map g)) := by
    rw [← Functor.comp_map, ← η.hom.naturality g]
    exact IsIso.comp_isIso' h (η.app N).isIso_hom
  have htilde : IsIso ((tilde.functor (CommRingCat.of S)).map
      ((ModuleCat.extendScalars (CommRingCat.ofHom f).hom).map g)) :=
    IsIso.of_isIso_comp_left (η.hom.app M) _
  have hext := (tilde.fullyFaithfulFunctor (R := CommRingCat.of S)).isIso_of_isIso_map
    ((ModuleCat.extendScalars (CommRingCat.ofHom f).hom).map g)
  rwa [ConcreteCategory.isIso_iff_bijective] at hext

/-- **A pullback of associated sheaves is invertible only if the base change of the map is
bijective**, with the base change written as a right tensor as in
`AlgebraicGeometry.isIso_pullback_map_tilde`. -/
public theorem bijective_rTensor_of_isIso_pullback_map_tilde (R S : Type u) [CommRing R]
    [CommRing S] (f : R →+* S) (M N : ModuleCat.{u} R) (g : M ⟶ N)
    (h : IsIso ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom f))).map
      ((tilde.functor (CommRingCat.of R)).map g))) :
    letI : Algebra R S := f.toAlgebra
    Function.Bijective (g.hom.rTensor S) := by
  let _ : Algebra R S := f.toAlgebra
  have hb := bijective_baseChange_of_isIso_pullback_map_tilde R S f M N g h
  rw [LinearMap.baseChange_eq_lTensor] at hb
  exact (LinearMap.lTensor_bij_iff_rTensor_bij S g.hom).1 hb

end AlgebraicGeometry

end
