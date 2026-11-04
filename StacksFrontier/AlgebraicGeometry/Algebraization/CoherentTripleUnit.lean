module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwist
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.StructureSheafCoherent

/-!
# The unit coherent triple

Let `A` be a Noetherian local ring and `f ∈ A`. The structure sheaves of the punctured spectrum
and of the closed fibre, identified over the punctured closed fibre by the canonical comparison
of the inverse images of a structure sheaf, form a coherent triple for `(A, f)`: the *unit*
coherent triple. It is the source of the morphism of triples `(s, s₀)` out of which the induction
step of [Stacks, Tag 0F27] builds its short exact sequence, and it is the triple whose twists
[Stacks, Tag 0F2A] takes the Euler characteristics of.

The one condition that is not formal is `f`-torsion-freeness of the structure sheaf of the
punctured spectrum. It is carried as a hypothesis of the construction, and discharged here from
`f`-torsion-freeness of *any* invertible module: an invertible module and the structure sheaf
differ by a tensor factor which is again invertible, and `f`-torsion-freeness passes through such
a factor. In particular an invertible coherent triple discharges it, which is the situation both
of the induction step of Tag 0F27 and of Tag 0F2A.

## Main definitions

* `Stacks.Algebraization.CoherentTriple.unit`: the unit coherent triple.

## Main results

* `Stacks.Algebraization.isFTorsionFree_of_iso`: `f`-torsion-freeness is an invariant of the
  isomorphism class.
* `Stacks.Algebraization.isFTorsionFree_of_isInvertible`: **if one invertible module on the
  punctured spectrum is `f`-torsion-free then every invertible module is.**
* `Stacks.Algebraization.IsInvertibleTriple.isFTorsionFree_unitModule`: an invertible coherent
  triple makes the structure sheaf of the punctured spectrum `f`-torsion-free.
* `Stacks.Algebraization.CoherentTriple.unit_twistZ_F_iso`: the punctured-spectrum member of the
  `n`-th twist of the unit triple is the `n`-th tensor power of the twisting module.

## Implementation notes

The chain that moves `f`-torsion-freeness between invertible modules is the addition law for the
tensor powers in the two degrees it needs, both of which are instances of
`Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso`. At the exponent `-1` it gives
`M^{⊗ -1} ⊗ M ≅ M^{⊗ 0}`, and the zeroth tensor power *is* the structure sheaf — by `rfl`, since
`Stacks.SheafOfModules.TensorPower.tensorPower_zero` is an equality rather than an isomorphism.
At the exponent `0` it gives `𝒪_X ⊗ M ≅ M^{⊗ 1}`, which with
`Stacks.SheafOfModules.TensorPower.tensorPowerOneIso` is the left unit constraint.

One braiding is unavoidable. `Stacks.Algebraization.isFTorsionFree_tensorModules` carries
`f`-torsion-freeness from the *first* factor of a tensor product across an invertible *second*
factor, because the trivialisation it rests on trivialises the second factor; and the addition law
at `-1` presents the structure sheaf with `M^{⊗ -1}` in the first position. So the two are joined
by `Stacks.Algebraization.tensorModulesBraidingIso`, which is
`Stacks.SheafOfModules.tensorSheafBraiding` at the scheme spelling.

Coherence of the two structure sheaves is
`Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit`, and the identification over the punctured
closed fibre is `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` on each of the two
routes around the square, composed. No compatibility has to be checked: the identification is
*defined* as that composite, which is what the structure field asks for.

## What is not done

That the structure sheaf of the punctured spectrum is `f`-torsion-free for *every* nonzerodivisor
`f` of `A`, with no invertible module supplied, is not proved. The argument is that multiplication
by `f` is bijective on the local ring at every associated point of `A` — a nonzerodivisor lies in
no associated prime — so [Stacks, Tag 0AVL]
(`Stacks.AlgebraicGeometry.AssociatedPointsMono.mono_of_stalk_injective_on_associatedPoints`)
makes it a monomorphism; what is missing is the comparison of the associated points of the
structure sheaf of an open of `Spec A` with the associated primes of `A`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0F23](https://stacks.math.columbia.edu/tag/0F23)
* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RelativeVeryAmple

universe u

namespace Stacks.Algebraization

/-! ### Transport of `f`-torsion-freeness -/

/-- **`f`-torsion-freeness is an invariant of the isomorphism class.** An isomorphism of modules
on the punctured spectrum is a bijection on the sections over every open which is linear over the
functions there, so it carries injectivity of multiplication by the image of `f` to injectivity
of multiplication by the image of `f`. -/
public theorem isFTorsionFree_of_iso (A : Type u) [CommRing A] [IsLocalRing A] (f : A)
    {F G : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules} (e : F ≅ G)
    (hF : IsFTorsionFree A f F) : IsFTorsionFree A f G := by
  intro V x y hxy
  have hlin : ∀ z : Γ(G, V), e.inv.app V (scalarOnOpen A f V • z)
      = scalarOnOpen A f V • e.inv.app V z := fun z =>
    Scheme.Modules.Hom.app_smul e.inv (scalarOnOpen A f V) z
  have hinv : ∀ z : Γ(G, V), e.hom.app V (e.inv.app V z) = z := fun z =>
    (ConcreteCategory.congr_hom
      (congrArg (fun t => Scheme.Modules.Hom.app t V) e.inv_hom_id) z).trans
        (CategoryTheory.id_apply z)
  have hinj : Function.Injective (e.inv.app V) := by
    intro a b hab
    rw [← hinv a, ← hinv b, hab]
  refine hinj (hF V ?_)
  have h := congrArg (e.inv.app V) hxy
  rw [hlin, hlin] at h
  exact h

/-! ### Two instances of the addition law, and the braiding -/

/-- **The tensor product of `𝒪_X`-modules is commutative**, at the spelling the triples'
identifications are written in. -/
public noncomputable def tensorModulesBraidingIso (X : Scheme.{u}) (M N : X.Modules) :
    tensorModules X M N ≅ tensorModules X N M :=
  Stacks.SheafOfModules.tensorSheafBraiding X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M N

/-- **`M^{⊗ -1} ⊗ M ≅ 𝒪_X`**: the addition law for the tensor powers at the exponent `-1`,
the zeroth tensor power being the structure sheaf. -/
@[ega "0 5.4.4" "case m = −1"]
public noncomputable def tensorPowSchemeNegOneIso (X : Scheme.{u}) (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] :
    tensorModules X (tensorPowScheme X M (-1)) M ≅ Stacks.Ample.unitModule X :=
  letI := isEquivalence_tensorRightFunctor_of_isInvertibleModule X M
  Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M (-1) ≪≫
    Stacks.SheafOfModules.TensorPower.tensorPowerReindex X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M
      (show (-1 : ℤ) + 1 = 0 by ring)

/-- **`𝒪_X ⊗ M ≅ M`** for an invertible `M`: the addition law for the tensor powers at the
exponent `0`, followed by the identification of the first tensor power with `M`. -/
public noncomputable def unitTensorModulesIso (X : Scheme.{u}) (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] :
    tensorModules X (Stacks.Ample.unitModule X) M ≅ M :=
  letI := isEquivalence_tensorRightFunctor_of_isInvertibleModule X M
  Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M 0 ≪≫
    Stacks.SheafOfModules.TensorPower.tensorPowerOneIso X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M

/-! ### `f`-torsion-freeness of the structure sheaf, and of every invertible module -/

/-- **An `f`-torsion-free invertible module makes the structure sheaf of the punctured spectrum
`f`-torsion-free.** The structure sheaf is `M ⊗ M^{⊗ -1}`, and `f`-torsion-freeness passes from
`M` across the invertible factor `M^{⊗ -1}`. -/
public theorem isFTorsionFree_unitModule_of_isFTorsionFree (A : Type u) [CommRing A]
    [IsLocalRing A] (f : A) (M : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)
    [Stacks.Ample.IsInvertibleModule (Stacks.Divisors.puncturedSpectrum A).toScheme M]
    (hM : IsFTorsionFree A f M) :
    IsFTorsionFree A f (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme) :=
  have := isInvertibleModule_tensorPowScheme
    (Stacks.Divisors.puncturedSpectrum A).toScheme M (-1)
  isFTorsionFree_of_iso A f
    (tensorModulesBraidingIso (Stacks.Divisors.puncturedSpectrum A).toScheme M
        (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme M (-1)) ≪≫
      tensorPowSchemeNegOneIso (Stacks.Divisors.puncturedSpectrum A).toScheme M)
    (isFTorsionFree_tensorModules A f M
      (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme M (-1)) hM)

/-- **If one invertible module on the punctured spectrum is `f`-torsion-free then every invertible
module is.** Both differ from the structure sheaf by an invertible tensor factor. -/
public theorem isFTorsionFree_of_isInvertible (A : Type u) [CommRing A] [IsLocalRing A] (f : A)
    (M N : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)
    [Stacks.Ample.IsInvertibleModule (Stacks.Divisors.puncturedSpectrum A).toScheme M]
    [Stacks.Ample.IsInvertibleModule (Stacks.Divisors.puncturedSpectrum A).toScheme N]
    (hM : IsFTorsionFree A f M) : IsFTorsionFree A f N :=
  isFTorsionFree_of_iso A f
    (unitTensorModulesIso (Stacks.Divisors.puncturedSpectrum A).toScheme N)
    (isFTorsionFree_tensorModules A f
      (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme) N
      (isFTorsionFree_unitModule_of_isFTorsionFree A f M hM))

/-- **An invertible coherent triple makes the structure sheaf of the punctured spectrum
`f`-torsion-free**: its punctured-spectrum member is an invertible `f`-torsion-free module. -/
public theorem IsInvertibleTriple.isFTorsionFree_unitModule {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} {L : CoherentTriple A f} (hL : IsInvertibleTriple L) :
    IsFTorsionFree A f (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme) :=
  have := hL.invertible_F
  isFTorsionFree_unitModule_of_isFTorsionFree A f L.F L.torsionFree

/-! ### The unit coherent triple -/

/-- **The unit coherent triple for `(A, f)`.** Its two members are the structure sheaves of the
punctured spectrum and of the closed fibre, and its identification over the punctured closed
fibre is the composite of the two canonical identifications of the inverse image of a structure
sheaf with the structure sheaf.

`f`-torsion-freeness of the structure sheaf of the punctured spectrum is the one hypothesis; it is
discharged from an invertible coherent triple by
`Stacks.Algebraization.IsInvertibleTriple.isFTorsionFree_unitModule`. -/
public noncomputable def CoherentTriple.unit (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A)
    (h : IsFTorsionFree A f
      (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme)) :
    CoherentTriple A f where
  F := Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme
  F₀ := Stacks.Ample.unitModule (closedFibre A f)
  coherent_F := Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit _
  coherent_F₀ := Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit _
  torsionFree := h
  alpha :=
    AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
        (morphismRestrict (closedImmersion A f) (Stacks.Divisors.puncturedSpectrum A)) ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
        (puncturedClosedFibre A f).ι).symm

/-- **The punctured-spectrum member of the `n`-th twist of the unit triple is the `n`-th tensor
power of the twisting module.** This is what makes the vanishing criterion of
[Stacks, Tag 0F28], applied to the `n`-th twist of the unit triple, a statement about the
triviality of `L^{⊗ n}`. -/
public noncomputable def CoherentTriple.unit_twistZ_F_iso (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (f : A)
    (h : IsFTorsionFree A f
      (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme))
    (L : CoherentTriple A f) (hL : IsInvertibleTriple L) (n : ℤ) :
    letI := hL.invertible_F
    ((CoherentTriple.unit A f h).twistZ L hL n).F ≅
      tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n :=
  letI := hL.invertible_F
  letI := isInvertibleModule_tensorPowScheme
    (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n
  unitTensorModulesIso (Stacks.Divisors.puncturedSpectrum A).toScheme
    (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)

end Stacks.Algebraization

end
