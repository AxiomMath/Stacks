module

public import Mathlib.RingTheory.Extension.Cotangent.Basic

/-!
# The naive cotangent complex along a commutative square of ring maps

A commutative square of ring maps
```
R ──fR──▸ R'
│          │
▼          ▼
S ──fS──▸ S'
```
induces a morphism `Generators.self R S ⟶ Generators.self R' S'` of the canonical presentations
`R[S] ⟶ S` and `R'[S'] ⟶ S'`, hence maps between the two terms of the naive cotangent complexes
`NL_{S/R}` and `NL_{S'/R'}` and between their first homology groups.  Mathlib provides these
maps through `Algebra.Generators.defaultHom`, which asks for the four ring maps as `Algebra`
instances together with two scalar towers.  This file packages them for a square given by bare
ring homomorphisms, which is the form in which squares arise from restriction maps of presheaves
of rings and from germ maps into stalks, and records their action on the generators of the
conormal module.

## Main definitions

* `Stacks.NaiveCotangent.selfRingHomOfSquare`: the map `R[S] → R'[S']` of polynomial rings
  induced by the square, `r ↦ fR r`, `[s] ↦ [fS s]`.
* `Stacks.NaiveCotangent.cotangentMapOfSquare`,
  `Stacks.NaiveCotangent.cotangentSpaceMapOfSquare` and
  `Stacks.NaiveCotangent.h1CotangentMapOfSquare`: the induced additive maps on `I/I²`, on
  `S ⊗_{R[S]} Ω_{R[S]/R}` and on `H₁(L_{S/R})`.

## Main results

* `Stacks.NaiveCotangent.cotangentMapOfSquare_mk`: the map on `I/I²` sends the class of a
  polynomial `p` to the class of `selfRingHomOfSquare p`.
* `Stacks.NaiveCotangent.cotangentMapOfSquare_comp` and
  `Stacks.NaiveCotangent.h1CotangentMapOfSquare_comp`: the maps are compatible with pasting of
  squares.
* `Stacks.NaiveCotangent.cotangentMapOfSquare_cotangentComplex`: they commute with the
  differentials.

## Implementation notes

Every map is defined by installing the square as `Algebra` instances with `letI` and applying the
corresponding Mathlib construction to `Algebra.Generators.defaultHom`.  The maps are recorded as
additive maps only, because their linearity is over a ring which the bare square does not make a
scalar ring of the target. All further properties are read off the formula
`cotangentMapOfSquare_mk`, which avoids comparing two `Algebra` instances on the same pair of
rings.
-/

@[expose] public section

open Algebra MvPolynomial

namespace Stacks.NaiveCotangent

variable {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
  [Algebra R S] [Algebra R' S'] (fR : R →+* R') (fS : S →+* S')
  (h : ∀ r : R, fS (algebraMap R S r) = algebraMap R' S' (fR r))

/-- The map of polynomial rings `R[S] → R'[S']` induced by a commutative square: coefficients
along `fR` and the variable `[s]` to the variable `[fS s]`. -/
noncomputable def selfRingHomOfSquare :
    (Generators.self R S).Ring →+* (Generators.self R' S').Ring :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp fR) fun s => MvPolynomial.X (fS s)

/-- The map `R[S] → R'[S']` sends the constant `r` to the constant `fR r`. -/
@[simp]
theorem selfRingHomOfSquare_C (r : R) :
    selfRingHomOfSquare fR fS (MvPolynomial.C r) = MvPolynomial.C (fR r) := by
  simp [selfRingHomOfSquare]

/-- The map `R[S] → R'[S']` sends the variable `[s]` to the variable `[fS s]`. -/
@[simp]
theorem selfRingHomOfSquare_X (s : S) :
    selfRingHomOfSquare fR fS (MvPolynomial.X s) = MvPolynomial.X (fS s) := by
  simp [selfRingHomOfSquare]

include h in
/-- Evaluation commutes with the map of polynomial rings induced by the square. -/
theorem aeval_selfRingHomOfSquare (p : (Generators.self R S).Ring) :
    MvPolynomial.aeval (R := R') (S₁ := S') _root_.id (selfRingHomOfSquare fR fS p) =
      fS (MvPolynomial.aeval (R := R) (S₁ := S) _root_.id p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [h]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s hp => simp only [map_mul, hp, selfRingHomOfSquare_X, MvPolynomial.aeval_X,
      id_eq]

/-- The morphism of canonical presentations induced by a commutative square of ring maps, for
the square installed as `Algebra` instances. -/
noncomputable abbrev selfHomOfSquare [Algebra R R'] [Algebra S S'] [Algebra R S'] :
    (Generators.self R S).Hom (Generators.self R' S') :=
  Generators.defaultHom _ _

/-- The algebra homomorphism of polynomial rings underlying `selfHomOfSquare` is
`selfRingHomOfSquare`. -/
theorem selfHomOfSquare_toAlgHom (p : (Generators.self R S).Ring) :
    letI := fR.toAlgebra
    letI := fS.toAlgebra
    letI := (fS.comp (algebraMap R S)).toAlgebra
    (selfHomOfSquare (R := R) (S := S) (R' := R') (S' := S')).toAlgHom p =
      selfRingHomOfSquare fR fS p := by
  let := fR.toAlgebra
  let := fS.toAlgebra
  let := (fS.comp (algebraMap R S)).toAlgebra
  change (MvPolynomial.aeval (Generators.defaultHom (Generators.self R S)
    (Generators.self R' S')).val) p = _
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.aeval_C, selfRingHomOfSquare_C]
    rfl
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s hp =>
    rw [map_mul, map_mul, hp, MvPolynomial.aeval_X, selfRingHomOfSquare_X]
    rfl

/-- The map `I/I² → I'/I'²` on the degree `-1` terms of the naive cotangent complexes induced by
a commutative square of ring maps. -/
noncomputable def cotangentMapOfSquare :
    (Generators.self R S).toExtension.Cotangent →+ (Generators.self R' S').toExtension.Cotangent :=
  letI := fR.toAlgebra
  letI := fS.toAlgebra
  letI := (fS.comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun r => h r
  haveI : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  (Extension.Cotangent.map
    (selfHomOfSquare (R := R) (S := S) (R' := R') (S' := S')).toExtensionHom).toAddMonoidHom

/-- The map `S ⊗ Ω → S' ⊗ Ω'` on the degree `0` terms of the naive cotangent complexes induced
by a commutative square of ring maps. -/
noncomputable def cotangentSpaceMapOfSquare :
    (Generators.self R S).toExtension.CotangentSpace →+
      (Generators.self R' S').toExtension.CotangentSpace :=
  letI := fR.toAlgebra
  letI := fS.toAlgebra
  letI := (fS.comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun r => h r
  haveI : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  (Extension.CotangentSpace.map
    (selfHomOfSquare (R := R) (S := S) (R' := R') (S' := S')).toExtensionHom).toAddMonoidHom

/-- The map induced by a commutative square on the first homology `H₁(L_{S/R}) → H₁(L_{S'/R'})`
of the naive cotangent complexes. -/
noncomputable def h1CotangentMapOfSquare :
    H1Cotangent R S →+ H1Cotangent R' S' :=
  letI := fR.toAlgebra
  letI := fS.toAlgebra
  letI := (fS.comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun r => h r
  haveI : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  (Extension.H1Cotangent.map
    (selfHomOfSquare (R := R) (S := S) (R' := R') (S' := S')).toExtensionHom).toAddMonoidHom

include h in
/-- The map of polynomial rings induced by the square carries the kernel of `R[S] → S` into the
kernel of `R'[S'] → S'`. -/
theorem selfRingHomOfSquare_mem_ker (p : (Generators.self R S).toExtension.ker) :
    selfRingHomOfSquare fR fS p.1 ∈ (Generators.self R' S').toExtension.ker := by
  have hp : MvPolynomial.aeval (R := R) (S₁ := S) _root_.id p.1 = 0 := p.2
  change MvPolynomial.aeval (R := R') (S₁ := S') _root_.id (selfRingHomOfSquare fR fS p.1) = 0
  exact (aeval_selfRingHomOfSquare fR fS h (p.1 : (Generators.self R S).Ring)).trans
    ((congrArg fS hp).trans (map_zero fS))

/-- **The map on conormal modules, on generators.**  The class of a polynomial `p` in the kernel
of `R[S] → S` goes to the class of its image under the map of polynomial rings. -/
theorem cotangentMapOfSquare_mk (p : (Generators.self R S).toExtension.ker) :
    cotangentMapOfSquare fR fS h (Extension.Cotangent.mk p) =
      Extension.Cotangent.mk ⟨selfRingHomOfSquare fR fS p.1,
        selfRingHomOfSquare_mem_ker fR fS h p⟩ := by
  let := fR.toAlgebra
  let := fS.toAlgebra
  let := (fS.comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun r => h r
  have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  change Extension.Cotangent.map
    (selfHomOfSquare (R := R) (S := S) (R' := R') (S' := S')).toExtensionHom
    (Extension.Cotangent.mk p) = _
  rw [Extension.Cotangent.map_mk]
  congr 2

/-- The underlying element of the conormal module of the image of a class of `H₁` is the image of
its underlying element. -/
theorem h1CotangentMapOfSquare_val (x : H1Cotangent R S) :
    (h1CotangentMapOfSquare fR fS h x).1 = cotangentMapOfSquare fR fS h x.1 :=
  rfl

/-- **The maps commute with the differentials.** -/
theorem cotangentMapOfSquare_cotangentComplex
    (x : (Generators.self R S).toExtension.Cotangent) :
    (Generators.self R' S').toExtension.cotangentComplex (cotangentMapOfSquare fR fS h x) =
      cotangentSpaceMapOfSquare fR fS h ((Generators.self R S).toExtension.cotangentComplex x) :=
  let := fR.toAlgebra
  let := fS.toAlgebra
  let := (fS.comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun r => h r
  have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  (Extension.CotangentSpace.map_cotangentComplex
    (selfHomOfSquare (R := R) (S := S) (R' := R') (S' := S')).toExtensionHom x).symm

/-- The map on `H₁` is semilinear over the top edge `fS` of the square. -/
theorem h1CotangentMapOfSquare_smul (s : S) (x : H1Cotangent R S) :
    h1CotangentMapOfSquare fR fS h (s • x) = fS s • h1CotangentMapOfSquare fR fS h x := by
  let := fR.toAlgebra
  let := fS.toAlgebra
  let := (fS.comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun r => h r
  have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (Extension.H1Cotangent.map
    (selfHomOfSquare (R := R) (S := S) (R' := R') (S' := S')).toExtensionHom).map_smul s x

section Instances

variable {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
  [Algebra R S] [Algebra R' S'] [Algebra R R'] [Algebra S S'] [Algebra R S']
  [IsScalarTower R R' S'] [IsScalarTower R S S']

/-- The square of structure maps `R → R' → S'` and `R → S → S'` commutes. -/
theorem algebraMap_square (r : R) :
    algebraMap S S' (algebraMap R S r) = algebraMap R' S' (algebraMap R R' r) := by
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

/-- **Mathlib's functoriality of `H₁` is the map of the square.**  For a square given by
`Algebra` instances, `Algebra.H1Cotangent.map` is `h1CotangentMapOfSquare` of the four structure
maps. -/
theorem h1Cotangent_map_eq_h1CotangentMapOfSquare (x : H1Cotangent R S) :
    H1Cotangent.map R R' S S' x =
      h1CotangentMapOfSquare (algebraMap R R') (algebraMap S S') algebraMap_square x := by
  apply Subtype.ext
  obtain ⟨p, hp⟩ := Extension.Cotangent.mk_surjective x.1
  change Extension.Cotangent.map (Generators.defaultHom _ _).toExtensionHom x.1 =
    cotangentMapOfSquare (algebraMap R R') (algebraMap S S') algebraMap_square x.1
  rw [← hp, Extension.Cotangent.map_mk, cotangentMapOfSquare_mk]
  congr 2

end Instances

section Comp

variable {R'' S'' : Type*} [CommRing R''] [CommRing S''] [Algebra R'' S'']
  (gR : R' →+* R'') (gS : S' →+* S'')
  (h' : ∀ r : R', gS (algebraMap R' S' r) = algebraMap R'' S'' (gR r))

/-- The maps of polynomial rings induced by two squares compose to the map induced by the pasted
square. -/
theorem selfRingHomOfSquare_comp :
    (selfRingHomOfSquare gR gS).comp (selfRingHomOfSquare fR fS) =
      selfRingHomOfSquare (gR.comp fR) (gS.comp fS) := by
  apply MvPolynomial.ringHom_ext <;> intro x <;> simp

include h h' in
/-- **Pasting squares, on conormal modules.** -/
theorem cotangentMapOfSquare_comp (x : (Generators.self R S).toExtension.Cotangent) :
    cotangentMapOfSquare gR gS h' (cotangentMapOfSquare fR fS h x) =
      cotangentMapOfSquare (gR.comp fR) (gS.comp fS)
        (fun r => by simp only [RingHom.comp_apply, h, h']) x := by
  obtain ⟨p, rfl⟩ := Extension.Cotangent.mk_surjective x
  rw [cotangentMapOfSquare_mk, cotangentMapOfSquare_mk, cotangentMapOfSquare_mk]
  congr 2
  exact DFunLike.congr_fun (selfRingHomOfSquare_comp fR fS gR gS) p.1

include h h' in
/-- **Pasting squares, on first homology.** -/
theorem h1CotangentMapOfSquare_comp (x : H1Cotangent R S) :
    h1CotangentMapOfSquare gR gS h' (h1CotangentMapOfSquare fR fS h x) =
      h1CotangentMapOfSquare (gR.comp fR) (gS.comp fS)
        (fun r => by simp only [RingHom.comp_apply, h, h']) x :=
  Subtype.ext (cotangentMapOfSquare_comp fR fS h gR gS h' x.1)

end Comp

omit [Algebra R S] [Algebra R' S'] in
/-- The maps induced by two squares with the same ring maps agree. -/
theorem h1CotangentMapOfSquare_congr [Algebra R S] [Algebra R' S'] {fR fR' : R →+* R'}
    {fS fS' : S →+* S'} (h : ∀ r : R, fS (algebraMap R S r) = algebraMap R' S' (fR r))
    (h' : ∀ r : R, fS' (algebraMap R S r) = algebraMap R' S' (fR' r)) (eR : fR = fR')
    (eS : fS = fS') (x : H1Cotangent R S) :
    h1CotangentMapOfSquare fR fS h x = h1CotangentMapOfSquare fR' fS' h' x := by
  subst eR
  subst eS
  rfl

/-- The identity square induces the identity on conormal modules. -/
theorem cotangentMapOfSquare_id (x : (Generators.self R S).toExtension.Cotangent) :
    cotangentMapOfSquare (RingHom.id R) (RingHom.id S) (fun _ => rfl) x = x := by
  obtain ⟨p, rfl⟩ := Extension.Cotangent.mk_surjective x
  rw [cotangentMapOfSquare_mk]
  congr 2
  exact MvPolynomial.eval₂_eta p.1

/-- The identity square induces the identity on first homology. -/
theorem h1CotangentMapOfSquare_id (x : H1Cotangent R S) :
    h1CotangentMapOfSquare (RingHom.id R) (RingHom.id S) (fun _ => rfl) x = x :=
  Subtype.ext (cotangentMapOfSquare_id x.1)

end Stacks.NaiveCotangent

end
