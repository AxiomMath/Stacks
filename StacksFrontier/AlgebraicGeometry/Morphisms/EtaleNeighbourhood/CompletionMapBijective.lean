module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.IsomorphismApproximation
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties

/-!
# The completed local rings of a morphism which is an isomorphism on local rings

A morphism of schemes carrying a point `x'` to a point `x` and inducing an isomorphism of local
rings there induces an isomorphism of completed local rings. This is what lets the data of Tag
0GDX — in particular the isomorphism `φ` of completed local rings — be transported along the
restriction of a scheme to an affine open neighbourhood of a point, which is the first reduction
in the proof of that tag.

## Main results

* `bijective_adicCompletionMap_of_bijective`: the map on adic completions induced by a bijective
  ring homomorphism carrying one ideal *onto* the other is bijective.
* `IsLocalRing.map_maximalIdeal_eq_of_bijective`: a bijective local homomorphism carries the
  maximal ideal onto the maximal ideal.
* `AlgebraicGeometry.Scheme.Hom.bijective_completionMapAt_of_isIso_stalkMap`: a morphism which is
  an isomorphism on local rings at a point is one on completed local rings.

## Implementation notes

The criterion used for bijectivity of the induced map on completions is
`Stacks.AdicCompletion.adicCompletionMap_bijective_of_quotientMap_bijective`: bijectivity of
`A ⧸ I ^ n → B ⧸ (I ^ n).map f` at every level. For a bijective `f` those maps are bijective
because `Ideal.quotientMap` of a surjection onto the image ideal is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u v

/-- A bijective ring homomorphism carrying `I` onto `J` induces a bijection of the adic
completions. -/
public theorem bijective_adicCompletionMap_of_bijective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Bijective f) (I : Ideal A) (J : Ideal B) (hIJ : I.map f = J) :
    Function.Bijective (adicCompletionMap f I J (hIJ.le.trans le_rfl)) := by
  subst hIJ
  refine Stacks.AdicCompletion.adicCompletionMap_bijective_of_quotientMap_bijective f I ?_
  intro n
  refine ⟨fun a b hab => ?_, fun b => ?_⟩
  · obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      ← map_sub] at hab
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    obtain ⟨c, hc, hceq⟩ := (Ideal.mem_map_iff_of_surjective f hf.2).mp hab
    exact hf.1 hceq ▸ hc
  · obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨a', rfl⟩ := hf.2 b'
    exact ⟨Ideal.Quotient.mk (I ^ n) a', Ideal.quotientMap_mk⟩

/-- A bijective local homomorphism of local rings carries the maximal ideal *onto* the maximal
ideal. -/
public theorem IsLocalRing.map_maximalIdeal_eq_of_bijective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] (hf : Function.Bijective f) :
    (maximalIdeal A).map f = maximalIdeal B := by
  refine le_antisymm (map_maximalIdeal_le f) ?_
  intro b hb
  obtain ⟨a, rfl⟩ := hf.2 b
  refine Ideal.mem_map_of_mem _ ?_
  by_contra ha
  exact (IsLocalRing.mem_maximalIdeal _).mp hb
    (IsUnit.map f (IsLocalRing.notMem_maximalIdeal.mp ha))

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism of schemes inducing an isomorphism of local rings at a point induces a bijection
of the completed local rings there. -/
public theorem bijective_completionMapAt_of_isIso_stalkMap {X' X : Scheme.{u}} (j : X' ⟶ X)
    {x' : X'} {x : X} (hj : j x' = x) [IsIso (j.stalkMap x')] :
    Function.Bijective (j.completionMapAt hj) := by
  have hiso : IsIso ((X.presheaf.stalkCongr (.of_eq hj.symm)).hom ≫ j.stalkMap x') :=
    IsIso.comp_isIso' inferInstance inferInstance
  have hbij : Function.Bijective (j.stalkHomAt hj) :=
    (ConcreteCategory.isIso_iff_bijective
      ((X.presheaf.stalkCongr (.of_eq hj.symm)).hom ≫ j.stalkMap x')).mp hiso
  have hloc : IsLocalHom (j.stalkHomAt hj) := inferInstance
  have hmap : (maximalIdeal (X.presheaf.stalk x)).map (j.stalkHomAt hj) =
      maximalIdeal (X'.presheaf.stalk x') :=
    IsLocalRing.map_maximalIdeal_eq_of_bijective _ hbij
  have := bijective_adicCompletionMap_of_bijective (j.stalkHomAt hj) hbij
    (maximalIdeal (X.presheaf.stalk x)) (maximalIdeal (X'.presheaf.stalk x')) hmap
  exact this

end AlgebraicGeometry.Scheme.Hom

end
