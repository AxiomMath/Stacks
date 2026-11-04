module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.FormsAlgEquivTensor

/-!
# Naturality of the transport of divided power forms along an isomorphism of divided power rings

`Crystalline.differentialFormsEquivOfAlgEquiv` of `ModuleDifferentials/FormsAlgEquiv.lean` carries
the divided power differential forms along an isomorphism of divided power rings, and
`Crystalline.tensorFormsEquivOfAlgEquiv` of `ModuleDifferentials/FormsAlgEquivTensor.lean` does
the same inside a tensor product.  Neither comes with a naturality statement, and the consumer —
the cosimplicial direction of the isomorphism `ε` of [Stacks, Lemma 60.21.1, Tag 07LF] — needs
one: the degreewise crossing of the ring identification has to commute with the transition maps
of the cosimplicial object on both sides.

This file supplies it.  The square is

```
Ωⁱ_{B/A,δ} ──Ωⁱ(f)──▶ Ωⁱ_{C/A,ε}
     │ Ωⁱ(u)               │ Ωⁱ(v)
     ▼                     ▼
Ωⁱ_{B'/A,δ'} ─Ωⁱ(f')─▶ Ωⁱ_{C'/A,ε'}
```

for four divided power rings over `A`, two horizontal isomorphisms `f`, `f'` and two vertical
divided power morphisms `u`, `v` whose two composites agree as algebra maps.

**The whole content is that the forward map of `Crystalline.differentialFormsEquivOfAlgEquiv` is
`Crystalline.mapDifferentialFormsOfDPMorphism`**, which that definition records as its bundled
equation; the square is then two applications of
`Crystalline.mapDifferentialFormsOfDPMorphism_comp` against the two spellings `f' ∘ u` and
`v ∘ f` of one and the same divided power morphism `B ⟶ C'`.  Nothing is assumed of `u` or `v`
beyond being divided power morphisms, and in particular neither is required to be an isomorphism.

## Main results

* `Crystalline.mapDifferentialFormsOfDPMorphism_crossing` — **the square**, for the bare
  comparison of forms.
* `Crystalline.differentialFormsEquivOfAlgEquiv_naturality` — the square with the two horizontals
  read as the transports of `Crystalline.differentialFormsEquivOfAlgEquiv`.
* `Crystalline.tensorFormsEquivOfAlgEquiv_naturality` — the square after tensoring, elementwise on
  a section and a form.  The two verticals of the tensored square act on the second factor only,
  so no compatibility between `u` and the module structures is needed and none is assumed; the
  coefficient `m` is arbitrary and is carried through untouched.
* `Crystalline.mapDifferentialFormsOfDPMorphism_congr` — the comparison of forms depends on the
  divided power morphism only through its underlying algebra map, the divided power
  compatibility being a `Prop`.  This is what lets the two spellings of `B ⟶ C'` be identified.

## Implementation notes

The two composites `f' ∘ u` and `v ∘ f` are *equal* algebra maps but not the same term, which is
the only difficulty: `Crystalline.mapDifferentialFormsOfDPMorphism` takes the divided power
compatibility as an argument whose type mentions the algebra map, so rewriting the map requires
moving that argument too.  `mapDifferentialFormsOfDPMorphism_congr` isolates this, with both maps
as variables so that `subst` applies and proof irrelevance closes the goal.

Contrast `Crystalline.formsQuotientMap_naturality` of `ModuleDifferentials/QuotientForms.lean`,
which is the same two applications of
`Crystalline.mapDifferentialFormsOfDPMorphism_comp` in the special case where the two spellings
of the composite are the same ring map on the nose and no such transport is needed.

## What is and is not proved

**No tag attribute is placed in this file, and [Stacks, Tag 07LF] is not proved.**  This is one
of the three naturality squares the cosimplicial direction of the isomorphism `ε` of that tag
needs, the other two being `Crystalline.tensorFormsLevelEquiv_symm_naturality` and
`Crystalline.tensorFormsCompletionLevelEquivAt_naturality`; the composite is not formed here and
no isomorphism of cosimplicial abelian groups is constructed.

No hypothesis is carried beyond the two ring isomorphisms with their divided power data, the two
vertical divided power morphisms, and the agreement of the two composites.  No flatness, no
finiteness, and no hypothesis on the degree `i`.

## References

* [Stacks Project, Lemma 60.21.1, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Crystalline

section FormsAlgEquivNaturality

variable {A : Type u} [CommRing A]

/-- **The comparison of divided power differential forms depends on the divided power morphism
only through its underlying algebra map.**  The divided power compatibility is a `Prop`, so two
compatibility proofs for equal algebra maps give the same comparison. -/
theorem mapDifferentialFormsOfDPMorphism_congr {B C : Type*} [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] {J : Ideal B} {K : Ideal C} (delta : DividedPowers J)
    (epsilon : DividedPowers K) {g g' : B →ₐ[A] C} (hgg' : g = g')
    (hg : delta.IsDPMorphism epsilon g.toRingHom)
    (hg' : delta.IsDPMorphism epsilon g'.toRingHom) (i : ℕ)
    (x : dividedPowerDifferentialForms (A := A) delta i) :
    mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta) epsilon g hg i x =
      mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta) epsilon g' hg' i x := by
  subst hgg'
  rfl

/-- **The transport of divided power differential forms along an isomorphism of divided power
rings is surjective**, being the forward map of
`Crystalline.differentialFormsEquivOfAlgEquiv`, which is an additive isomorphism.  This is how a
form over the target is named as the image of one over the source without any `symm` lemma for
the transport. -/
theorem mapDifferentialFormsOfDPMorphism_surjective {B C : Type*} [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] {J : Ideal B} {K : Ideal C} (delta : DividedPowers J)
    (epsilon : DividedPowers K) (f : B ≃ₐ[A] C)
    (hf : delta.IsDPMorphism epsilon f.toAlgHom.toRingHom)
    (hJ : J.map f.toAlgHom.toRingHom = K) (i : ℕ) :
    Function.Surjective (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta)
      epsilon f.toAlgHom hf i) := fun y ↦
  ⟨(differentialFormsEquivOfAlgEquiv delta epsilon f hf hJ i).1.symm y,
    ((differentialFormsEquivOfAlgEquiv delta epsilon f hf hJ i).2 _).symm.trans
      (AddEquiv.apply_symm_apply _ y)⟩

variable {B B' C C' : Type*} [CommRing B] [CommRing B'] [CommRing C] [CommRing C']
  [Algebra A B] [Algebra A B'] [Algebra A C] [Algebra A C']
  {J : Ideal B} {J' : Ideal B'} {K : Ideal C} {K' : Ideal C'}
  (delta : DividedPowers J) (delta' : DividedPowers J')
  (epsilon : DividedPowers K) (epsilon' : DividedPowers K')

/-- **The crossing square for the comparison of divided power differential forms.**

For divided power morphisms `u : (B, δ) ⟶ (B', δ')`, `v : (C, ε) ⟶ (C', ε')`,
`f : (B, δ) ⟶ (C, ε)` and `f' : (B', δ') ⟶ (C', ε')` over `A` with `f' ∘ u = v ∘ f` as algebra
maps, transporting forms across `u` and then `f'` is transporting them across `f` and then `v`.

Both composites are the comparison of the one divided power morphism `B ⟶ C'`, by
`Crystalline.mapDifferentialFormsOfDPMorphism_comp` twice; the two spellings of it are
identified by `mapDifferentialFormsOfDPMorphism_congr`.  Neither `u` nor `v` is assumed to be an
isomorphism, and `f`, `f'` are not either — only their divided power compatibility is used. -/
theorem mapDifferentialFormsOfDPMorphism_crossing
    (u : B →ₐ[A] B') (f : B →ₐ[A] C) (f' : B' →ₐ[A] C') (v : C →ₐ[A] C')
    (hu : delta.IsDPMorphism delta' u.toRingHom)
    (hf : delta.IsDPMorphism epsilon f.toRingHom)
    (hf' : delta'.IsDPMorphism epsilon' f'.toRingHom)
    (hv : epsilon.IsDPMorphism epsilon' v.toRingHom)
    (hcomm : f'.comp u = v.comp f) (i : ℕ)
    (x : dividedPowerDifferentialForms (A := A) delta i) :
    mapDifferentialFormsOfDPMorphism (A := A) (J := J') (delta := delta') epsilon' f' hf' i
        (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta) delta' u hu i x) =
      mapDifferentialFormsOfDPMorphism (A := A) (J := K) (delta := epsilon) epsilon' v hv i
        (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta) epsilon f hf i x) :=
  ((mapDifferentialFormsOfDPMorphism_comp (A := A) (J := J) (delta := delta) delta' epsilon'
        u f' hu hf' (DividedPowers.IsDPMorphism.comp epsilon' hf' hu) i x).symm.trans
      (mapDifferentialFormsOfDPMorphism_congr (A := A) delta epsilon' hcomm
        (DividedPowers.IsDPMorphism.comp epsilon' hf' hu)
        (DividedPowers.IsDPMorphism.comp epsilon' hv hf) i x)).trans
    (mapDifferentialFormsOfDPMorphism_comp (A := A) (J := J) (delta := delta) epsilon epsilon'
      f v hf hv (DividedPowers.IsDPMorphism.comp epsilon' hv hf) i x)

variable (f : B ≃ₐ[A] C) (f' : B' ≃ₐ[A] C')
  (hf : delta.IsDPMorphism epsilon f.toAlgHom.toRingHom)
  (hf' : delta'.IsDPMorphism epsilon' f'.toAlgHom.toRingHom)
  (hJ : J.map f.toAlgHom.toRingHom = K) (hJ' : J'.map f'.toAlgHom.toRingHom = K')
  (u : B →ₐ[A] B') (v : C →ₐ[A] C')
  (hu : delta.IsDPMorphism delta' u.toRingHom)
  (hv : epsilon.IsDPMorphism epsilon' v.toRingHom)
  (hcomm : f'.toAlgHom.comp u = v.comp f.toAlgHom)

include hcomm

/-- **The transport of divided power differential forms along an isomorphism of divided power
rings is natural in the divided power ring.**

This is `mapDifferentialFormsOfDPMorphism_crossing` with the two horizontals read as
`Crystalline.differentialFormsEquivOfAlgEquiv`, whose bundled equation says that its forward map
*is* `Crystalline.mapDifferentialFormsOfDPMorphism`. -/
theorem differentialFormsEquivOfAlgEquiv_naturality (i : ℕ)
    (x : dividedPowerDifferentialForms (A := A) delta i) :
    (differentialFormsEquivOfAlgEquiv delta' epsilon' f' hf' hJ' i).1
        (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta) delta' u hu i x) =
      mapDifferentialFormsOfDPMorphism (A := A) (J := K) (delta := epsilon) epsilon' v hv i
        ((differentialFormsEquivOfAlgEquiv delta epsilon f hf hJ i).1 x) := by
  rw [(differentialFormsEquivOfAlgEquiv delta' epsilon' f' hf' hJ' i).2,
    (differentialFormsEquivOfAlgEquiv delta epsilon f hf hJ i).2]
  exact mapDifferentialFormsOfDPMorphism_crossing delta delta' epsilon epsilon' u f.toAlgHom
    f'.toAlgHom v hu hf hf' hv hcomm i x

/-- **The tensored transport of divided power differential forms along an isomorphism of divided
power rings is natural in the divided power ring**, elementwise on a section and a form.

For a module `M'` over `B'` and over `C'` whose two structures agree along `f'`, the transport
`Crystalline.tensorFormsEquivOfAlgEquiv` at `f'` carries `m ⊗ Ωⁱ(u) x` to
`m ⊗ Ωⁱ(v) (Ωⁱ(f) x)`.  Pure tensors span, so this determines the square; it is stated
elementwise, as `Crystalline.tensorFormsLevelEquiv_symm_naturality` is, because the vertical on
the left is not a map built here — in the application it is the transition map of a cosimplicial
object, and only its value on a pure tensor is known.

The two verticals act on the second factor alone: the coefficient `m` is arbitrary and is not
moved, so no compatibility between `u` and the module structures is needed. -/
theorem tensorFormsEquivOfAlgEquiv_naturality {M' : Type*} [AddCommGroup M'] [Module B' M']
    [Module C' M'] (hsm' : ∀ (b : B') (m : M'), b • m = f' b • m) (i : ℕ) (m : M')
    (x : dividedPowerDifferentialForms (A := A) delta i) :
    (tensorFormsEquivOfAlgEquiv delta' epsilon' f' hf' hJ' hsm' i).1
        (m ⊗ₜ[B'] mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta)
          delta' u hu i x) =
      m ⊗ₜ[C'] mapDifferentialFormsOfDPMorphism (A := A) (J := K) (delta := epsilon) epsilon' v
        hv i (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta) epsilon
          f.toAlgHom hf i x) :=
  ((tensorFormsEquivOfAlgEquiv delta' epsilon' f' hf' hJ' hsm' i).2 m _).trans
    (congrArg (fun y ↦ m ⊗ₜ[C'] y)
      (mapDifferentialFormsOfDPMorphism_crossing delta delta' epsilon epsilon' u f.toAlgHom
        f'.toAlgHom v hu hf hf' hv hcomm i x))

end FormsAlgEquivNaturality

end Crystalline

end
