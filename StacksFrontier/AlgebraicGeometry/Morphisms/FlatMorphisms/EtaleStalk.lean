module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.RingTheory.Etale.Weakly
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Stalks
public import StacksFrontier.RingTheory.WeaklyEtale.Flat
public import StacksCore.Tactic.StacksAttribute

/-!
# Flatness of a module over the local rings of an étale morphism

Let `f : T ⟶ S` be an étale morphism of schemes, let `t : T` be a point and let `M` be a module
over the local ring `𝒪_{T,t}`, regarded as a module over `𝒪_{S,f(t)}` through the map of local
rings. Then `M` is flat over `𝒪_{S,f(t)}` if and only if it is flat over `𝒪_{T,t}`.

The source deduces this from the corresponding statement for quasi-coherent modules (Tag 05B9)
by pushing `M` forward from `Spec 𝒪_{T,t}`. Here the argument is carried out on local rings
directly: the map of local rings of an étale (indeed of a weakly étale) morphism is a weakly
étale ring map, flatness over the base ascends along a weakly étale ring map (Tag 092C), and it
descends along any flat ring map.

## Main results

* `Module.flat_iff_of_weaklyEtale`: for a weakly étale algebra `A → B` and a `B`-module `M`,
  flatness of `M` over `A` and over `B` agree.
* `AlgebraicGeometry.flat_stalk_iff_of_weaklyEtale`: the comparison at the local rings of a
  weakly étale morphism of schemes.
* `AlgebraicGeometry.flat_stalk_iff_of_etale`: the comparison at the local rings of an étale
  morphism of schemes.

## References

* [Stacks Project, Tag 05BA](https://stacks.math.columbia.edu/tag/05BA)
* [Stacks Project, Tag 092C](https://stacks.math.columbia.edu/tag/092C)
-/

@[expose] public section

universe u

/-- For a weakly étale algebra `A → B`, a `B`-module is flat over `A` if and only if it is flat
over `B`. -/
theorem Module.flat_iff_of_weaklyEtale (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.WeaklyEtale A B] (M : Type*) [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] :
    Module.Flat A M ↔ Module.Flat B M :=
  ⟨fun h ↦ flat_of_flat_of_mul_flat A B (Algebra.WeaklyEtale.flat_lmul' A B) M h,
    fun _ ↦ Module.Flat.trans A B M⟩

namespace AlgebraicGeometry

variable {S T : Scheme.{u}} (f : T ⟶ S)

/-- Let `f : T ⟶ S` be weakly étale and `t : T`. A module over `𝒪_{T,t}` is flat over
`𝒪_{S,f(t)}`, acting through the map of local rings, if and only if it is flat over
`𝒪_{T,t}`. -/
theorem flat_stalk_iff_of_weaklyEtale [WeaklyEtale f] (t : T) (M : Type*) [AddCommGroup M]
    [Module (T.presheaf.stalk t) M] :
    letI : Module (S.presheaf.stalk (f t)) M := Module.compHom M (f.stalkMap t).hom
    Module.Flat (S.presheaf.stalk (f t)) M ↔ Module.Flat (T.presheaf.stalk t) M := by
  let := (f.stalkMap t).hom.toAlgebra
  let : Module (S.presheaf.stalk (f t)) M := Module.compHom M (f.stalkMap t).hom
  have : IsScalarTower (S.presheaf.stalk (f t)) (T.presheaf.stalk t) M :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : Algebra.WeaklyEtale (S.presheaf.stalk (f t)) (T.presheaf.stalk t) :=
    (weaklyEtale_iff_stalkMap_weaklyEtale f).mp ‹_› t
  exact Module.flat_iff_of_weaklyEtale _ _ M

/-- Let `f : T ⟶ S` be étale, let `t : T` and let `M` be a module over `𝒪_{T,t}`. Then `M` is
flat over `𝒪_{S,f(t)}`, acting through the map of local rings, if and only if it is flat over
`𝒪_{T,t}`. -/
@[stacks 05BA]
theorem flat_stalk_iff_of_etale [Etale f] (t : T) (M : Type*) [AddCommGroup M]
    [Module (T.presheaf.stalk t) M] :
    letI : Module (S.presheaf.stalk (f t)) M := Module.compHom M (f.stalkMap t).hom
    Module.Flat (S.presheaf.stalk (f t)) M ↔ Module.Flat (T.presheaf.stalk t) M :=
  flat_stalk_iff_of_weaklyEtale f t M

end AlgebraicGeometry
