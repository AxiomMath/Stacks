module

public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.FormallyUnramified
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeShortExact
public import StacksFrontier.AlgebraicGeometry.Thickenings.Existence
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalDifferentials
import StacksCore.Tactic.StacksAttribute

/-!
# Short exactness of the conormal sequence of a formally unramified morphism

Let `h : Z ⟶ X` be a formally unramified morphism of schemes over `p : X ⟶ S`. There is a
canonical exact sequence

```
𝒞_{Z/X} ⟶ h^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0
```

of `𝒪_Z`-modules, and if moreover `Z` is formally smooth over `S` then that sequence is short
exact, i.e. the first arrow is a monomorphism as well:

```
0 ⟶ 𝒞_{Z/X} ⟶ h^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0.
```

Here `𝒞_{Z/X}` is the conormal sheaf of the inclusion `i : Z ⟶ Z'` of `Z` into a universal
first-order thickening of `Z` over `X`, and the sequence is identified with the conormal
sequence of `i`.

## Main definitions

* `Stacks.UnramifiedConormalSequence.middleIso`: the identification
  `h^*Ω_{X/S} ≅ i^*Ω_{Z'/S}` of the middle term of the sequence with the middle term of the
  conormal sequence of the inclusion `i : Z ⟶ Z'` of `Z` into a universal first-order
  thickening of `Z` over `X`.
* `Stacks.UnramifiedConormalSequence.unramifiedConormalDifferential`: the first arrow
  `𝒞_{Z/X} ⟶ h^*Ω_{X/S}` of the sequence, the conormal differential of `i` composed with
  the inverse of `middleIso`.
* `Stacks.UnramifiedConormalSequence.unramifiedConormalShortComplex`: the sequence
  `𝒞_{Z/X} ⟶ h^*Ω_{X/S} ⟶ Ω_{Z/S}`, as a short complex, at an arbitrary universal first-order
  thickening of `h`.
* `Stacks.UnramifiedConormalSequence.thickeningShortComplexIso`: the isomorphism of short
  complexes between the conormal sequence of `i` and the sequence of `h`.
* `Stacks.UnramifiedConormalSequence.conormalShortComplex`: the same sequence at the universal
  first-order thickening `Stacks.Thickenings.universalFirstOrderThickening h`.

## Main results

* `Stacks.UnramifiedConormalSequence.conormalShortComplex_shortExact`: for a formally
  unramified `h : Z ⟶ X` with `h ≫ p : Z ⟶ S` formally smooth, the sequence
  `0 ⟶ 𝒞_{Z/X} ⟶ h^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0` is short exact.
* `Stacks.UnramifiedConormalSequence.shortExact_of_isUniversalFirstOrderThickening`: the same
  at an arbitrary universal first-order thickening of `h`.
* `Stacks.UnramifiedConormalSequence.conormalShortComplex_exact` and
  `Stacks.UnramifiedConormalSequence.unramifiedConormalShortComplex_exact`: exactness at the
  middle term, without the formal smoothness hypothesis.
* `Stacks.UnramifiedConormalSequence.middleIso_hom_comp` and
  `Stacks.UnramifiedConormalSequence.middleIso_inv_comp`: the identification of the middle terms
  carries the second arrow of the conormal sequence of `i` to the second arrow of the sequence
  of `h`.

## References

* [Stacks Project, Tag 06B7](https://stacks.math.columbia.edu/tag/06B7)
* [Stacks Project, Tag 04FC](https://stacks.math.columbia.edu/tag/04FC)
* [Stacks Project, Tag 06AA](https://stacks.math.columbia.edu/tag/06AA)
* [Stacks Project, Tag 06A8](https://stacks.math.columbia.edu/tag/06A8)
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
* [Stacks Project, Tag 04FB](https://stacks.math.columbia.edu/tag/04FB)
* [Stacks Project, Tag 04F4](https://stacks.math.columbia.edu/tag/04F4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.Thickenings

universe u

namespace Stacks.UnramifiedConormalSequence

/-! ### The conormal sequence of an immersion with a named structure morphism

The conormal sequence of an immersion `j : Z ⟶ W` over `q : W ⟶ S`, with the structure
morphism `r` of `Z` over `S` a morphism of its own, equal to `j ≫ q`. -/

section Named

variable {Z W S : Scheme.{u}} (j : Z ⟶ W) [IsImmersion j] (q : W ⟶ S) (r : Z ⟶ S)

/-- The left-hand term of the conormal sequence of an immersion `j`: the pullback along
`j.liftCoborder` of the defining ideal sheaf of `j`. -/
@[sga "7 XVII 5.1" "partial"]
abbrev conormalSource : Z.Modules :=
  (Scheme.Modules.pullback j.liftCoborder).obj ((definingIdeal j).toSheafOfModules)

/-- The two arrows of the conormal sequence of an immersion compose to zero, with the
structure morphism `r` of `Z` over `S` given as a morphism of its own rather than as the
composite `j ≫ q`. -/
theorem conormalDifferential_comp_relativeDifferentialsMap_of_eq (hr : j ≫ q = r)
    (hc : j ≫ q = r ≫ 𝟙 S) :
    Stacks.ConormalSequenceRight.conormalDifferential j q ≫
        relativeDifferentialsMap j q r (𝟙 S) hc =
      (0 : conormalSource j ⟶ relativeDifferentials r) := by
  subst hr
  exact Stacks.ConormalSequenceRight.conormalDifferential_comp_relativeDifferentialsMap j q

/-- The conormal sequence of an immersion is exact at its middle term, with the structure
morphism `r` of `Z` over `S` given as a morphism of its own. -/
theorem exact_mk_of_eq (hr : j ≫ q = r) (hc : j ≫ q = r ≫ 𝟙 S)
    (hz : Stacks.ConormalSequenceRight.conormalDifferential j q ≫
      relativeDifferentialsMap j q r (𝟙 S) hc =
        (0 : conormalSource j ⟶ relativeDifferentials r)) :
    (ShortComplex.mk (Stacks.ConormalSequenceRight.conormalDifferential j q)
      (relativeDifferentialsMap j q r (𝟙 S) hc) hz).Exact := by
  subst hr
  exact Stacks.ConormalSequenceRight.conormalShortComplex_exact j q

/-- The conormal sequence of an immersion with formally smooth source is short exact, with the
structure morphism `r` of `Z` over `S` given as a morphism of its own. -/
theorem shortExact_mk_of_eq (hr : j ≫ q = r) (hsm : AlgebraicGeometry.FormallySmooth r)
    (hc : j ≫ q = r ≫ 𝟙 S)
    (hz : Stacks.ConormalSequenceRight.conormalDifferential j q ≫
      relativeDifferentialsMap j q r (𝟙 S) hc =
        (0 : conormalSource j ⟶ relativeDifferentials r)) :
    (ShortComplex.mk (Stacks.ConormalSequenceRight.conormalDifferential j q)
      (relativeDifferentialsMap j q r (𝟙 S) hc) hz).ShortExact := by
  subst hr
  exact Stacks.ConormalSequenceRight.conormalShortComplex_shortExact_of_formallySmooth j q hsm

end Named

/-! ### The sequence of a formally unramified morphism -/

section Thickening

variable {Z X S Z' : Scheme.{u}} {h : Z ⟶ X} {i : Z ⟶ Z'} {h' : Z' ⟶ X}

/-- For a universal first-order thickening `i : Z ⟶ Z'` of `h` with structure morphism
`h' : Z' ⟶ X`, `i ≫ (h' ≫ p) = h ≫ p`. -/
theorem inclusion_comp_toBase_comp (hi : IsUniversalFirstOrderThickening h i h') (p : X ⟶ S) :
    i ≫ (h' ≫ p) = h ≫ p := by
  rw [← Category.assoc, hi.inclusion_toBase]

/-- For a universal first-order thickening `i : Z ⟶ Z'` of `h` with structure morphism
`h' : Z' ⟶ X`, `i ≫ (h' ≫ p) = (h ≫ p) ≫ 𝟙 S`. -/
theorem inclusion_comp_toBase_comp' (hi : IsUniversalFirstOrderThickening h i h') (p : X ⟶ S) :
    i ≫ (h' ≫ p) = (h ≫ p) ≫ 𝟙 S :=
  (inclusion_comp_toBase_comp hi p).trans (Category.comp_id _).symm

/-- For a universal first-order thickening `i : Z ⟶ Z'` of `h : Z ⟶ X` with structure morphism
`h' : Z' ⟶ X`, and `p : X ⟶ S`, the canonical identification `h^*Ω_{X/S} ≅ i^*Ω_{Z'/S}`: the
isomorphism `h^* ≅ i^*(h')^*` followed by the canonical map `i^*(h')^*Ω_{X/S} ⟶ i^*Ω_{Z'/S}`,
which is an isomorphism. -/
def middleIso (hi : IsUniversalFirstOrderThickening h i h') (p : X ⟶ S) :
    (Scheme.Modules.pullback h).obj (relativeDifferentials p) ≅
      (Scheme.Modules.pullback i).obj (relativeDifferentials (h' ≫ p)) :=
  have := Stacks.Thickenings.isIso_thickeningRelativeDifferentialsMap hi p
  ((Scheme.Modules.pullbackCongr hi.inclusion_toBase).app (relativeDifferentials p)).symm ≪≫
    ((Scheme.Modules.pullbackComp i h').app (relativeDifferentials p)).symm ≪≫
      asIso (thickeningRelativeDifferentialsMap i h' p)

/-- The forward map of `middleIso` as a composite. -/
theorem middleIso_hom (hi : IsUniversalFirstOrderThickening h i h') (p : X ⟶ S) :
    (middleIso hi p).hom =
      ((Scheme.Modules.pullbackCongr hi.inclusion_toBase).app (relativeDifferentials p)).inv ≫
        ((Scheme.Modules.pullbackComp i h').app (relativeDifferentials p)).inv ≫
          thickeningRelativeDifferentialsMap i h' p :=
  rfl

/-- The identification `middleIso` of the middle terms, followed by the second arrow of the
conormal sequence of the inclusion `i`, is the canonical map `h^*Ω_{X/S} ⟶ Ω_{Z/S}`. -/
theorem middleIso_hom_comp (hi : IsUniversalFirstOrderThickening h i h') (p : X ⟶ S) :
    (middleIso hi p).hom ≫
        relativeDifferentialsMap i (h' ≫ p) (h ≫ p) (𝟙 S)
          (inclusion_comp_toBase_comp' hi p) =
      relativeDifferentialsMap h p (h ≫ p) (𝟙 S) (by simp) := by
  have hc := isRelativeDifferentialsMap_relativeDifferentialsMap h' p (h' ≫ p) (𝟙 S)
    (show h' ≫ p = (h' ≫ p) ≫ 𝟙 S by simp)
  have hc' := isRelativeDifferentialsMap_relativeDifferentialsMap i (h' ≫ p) (h ≫ p) (𝟙 S)
    (inclusion_comp_toBase_comp' hi p)
  have e := ((hc.comp hc').congr_left hi.inclusion_toBase).eq_relativeDifferentialsMap (𝟙 S)
    (show h ≫ p = (h ≫ p) ≫ 𝟙 S by simp)
  rw [middleIso_hom]
  simp only [Category.assoc]
  exact e

/-- The inverse of `middleIso` followed by the canonical map `h^*Ω_{X/S} ⟶ Ω_{Z/S}` is the
second arrow of the conormal sequence of the inclusion `i`. -/
theorem middleIso_inv_comp (hi : IsUniversalFirstOrderThickening h i h') (p : X ⟶ S) :
    (middleIso hi p).inv ≫ relativeDifferentialsMap h p (h ≫ p) (𝟙 S) (by simp) =
      relativeDifferentialsMap i (h' ≫ p) (h ≫ p) (𝟙 S)
        (inclusion_comp_toBase_comp' hi p) := by
  rw [← middleIso_hom_comp hi p, Iso.inv_hom_id_assoc]

variable [IsImmersion i]

/-- For a formally unramified `h : Z ⟶ X` presented by a universal first-order thickening
`i : Z ⟶ Z'` with structure morphism `h' : Z' ⟶ X`, and `p : X ⟶ S`, the canonical morphism
`𝒞_{Z/X} ⟶ h^*Ω_{X/S}`: the first arrow `𝒞_{Z/Z'} ⟶ i^*Ω_{Z'/S}` of the conormal sequence of
the immersion `i` followed by the inverse of `middleIso`. -/
def unramifiedConormalDifferential (hi : IsUniversalFirstOrderThickening h i h') (p : X ⟶ S) :
    (conormalSheaf i : Z.Modules) ⟶
      (Scheme.Modules.pullback h).obj (relativeDifferentials p) :=
  Stacks.ConormalSequenceRight.conormalDifferential i (h' ≫ p) ≫ (middleIso hi p).inv

/-- The two arrows of the sequence `𝒞_{Z/X} ⟶ h^*Ω_{X/S} ⟶ Ω_{Z/S}` compose to zero. -/
theorem unramifiedConormalDifferential_comp_relativeDifferentialsMap
    (hi : IsUniversalFirstOrderThickening h i h') (p : X ⟶ S) :
    unramifiedConormalDifferential hi p ≫
        relativeDifferentialsMap h p (h ≫ p) (𝟙 S) (by simp) =
      (0 : conormalSource i ⟶ relativeDifferentials (h ≫ p)) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun m => Stacks.ConormalSequenceRight.conormalDifferential i (h' ≫ p) ≫ m)
        (middleIso_inv_comp hi p)).trans
      (conormalDifferential_comp_relativeDifferentialsMap_of_eq i (h' ≫ p) (h ≫ p)
        (inclusion_comp_toBase_comp hi p) (inclusion_comp_toBase_comp' hi p)))

/-- For a formally unramified `h : Z ⟶ X` presented by a universal first-order thickening
`i : Z ⟶ Z'` over `h' : Z' ⟶ X`, and `p : X ⟶ S`, the sequence

```
𝒞_{Z/X} ⟶ h^*Ω_{X/S} ⟶ Ω_{Z/S}
```

of `𝒪_Z`-modules, whose first arrow is `unramifiedConormalDifferential` and whose second arrow
is the canonical map on relative differentials. -/
def unramifiedConormalShortComplex (hi : IsUniversalFirstOrderThickening h i h') (p : X ⟶ S) :
    ShortComplex Z.Modules :=
  ShortComplex.mk (unramifiedConormalDifferential hi p)
    (relativeDifferentialsMap h p (h ≫ p) (𝟙 S) (by simp))
    (unramifiedConormalDifferential_comp_relativeDifferentialsMap hi p)

/-- The isomorphism of short complexes identifying the conormal sequence of the inclusion
`i : Z ⟶ Z'` over `h' ≫ p` with the sequence `unramifiedConormalShortComplex` of `h` over `p`.
It is the identity on the left-hand and right-hand terms and `middleIso` on the middle
terms. -/
def thickeningShortComplexIso (hi : IsUniversalFirstOrderThickening h i h') (p : X ⟶ S) :
    ShortComplex.mk (Stacks.ConormalSequenceRight.conormalDifferential i (h' ≫ p))
        (relativeDifferentialsMap i (h' ≫ p) (h ≫ p) (𝟙 S)
          (inclusion_comp_toBase_comp' hi p))
        (conormalDifferential_comp_relativeDifferentialsMap_of_eq i (h' ≫ p) (h ≫ p)
          (inclusion_comp_toBase_comp hi p) (inclusion_comp_toBase_comp' hi p)) ≅
      unramifiedConormalShortComplex hi p :=
  ShortComplex.isoMk (Iso.refl _) (middleIso hi p).symm (Iso.refl _)
    (Category.id_comp _)
    ((middleIso_inv_comp hi p).trans (Category.comp_id _).symm)

/-- The sequence `𝒞_{Z/X} ⟶ h^*Ω_{X/S} ⟶ Ω_{Z/S}` of a formally unramified morphism, at a
universal first-order thickening, is exact at `h^*Ω_{X/S}`. -/
@[sga "7 XI 1.3" "partial"]
theorem unramifiedConormalShortComplex_exact
    (hi : IsUniversalFirstOrderThickening h i h') (p : X ⟶ S) :
    (unramifiedConormalShortComplex hi p).Exact :=
  ShortComplex.exact_of_iso (thickeningShortComplexIso hi p)
    (exact_mk_of_eq i (h' ≫ p) (h ≫ p) (inclusion_comp_toBase_comp hi p)
      (inclusion_comp_toBase_comp' hi p) _)

/-- For a formally unramified `h : Z ⟶ X` presented by a universal first-order thickening
`i : Z ⟶ Z'` over `h' : Z' ⟶ X`, and `p : X ⟶ S` such that `Z` is formally smooth over `S`, the
sequence

```
0 ⟶ 𝒞_{Z/X} ⟶ h^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0
```

is short exact. -/
@[sga "7 XI 1.3" "partial"]
theorem shortExact_of_isUniversalFirstOrderThickening
    (hi : IsUniversalFirstOrderThickening h i h') (p : X ⟶ S)
    (hZ : AlgebraicGeometry.FormallySmooth (h ≫ p)) :
    (unramifiedConormalShortComplex hi p).ShortExact :=
  ShortComplex.shortExact_of_iso (thickeningShortComplexIso hi p)
    (shortExact_mk_of_eq i (h' ≫ p) (h ≫ p) (inclusion_comp_toBase_comp hi p) hZ
      (inclusion_comp_toBase_comp' hi p) _)

end Thickening

/-! ### The sequence at the chosen universal first-order thickening -/

section Chosen

variable {Z X S : Scheme.{u}} (h : Z ⟶ X) [FormallyUnramified h] (p : X ⟶ S)

/-- The sequence

```
𝒞_{Z/X} ⟶ h^*Ω_{X/S} ⟶ Ω_{Z/S}
```

of a formally unramified `h : Z ⟶ X` over `p : X ⟶ S`, at the universal first-order thickening
`Stacks.Thickenings.universalFirstOrderThickening h`. -/
def conormalShortComplex : ShortComplex Z.Modules :=
  unramifiedConormalShortComplex (universalFirstOrderThickening h).isUniversal p

/-- The sequence `𝒞_{Z/X} ⟶ h^*Ω_{X/S} ⟶ Ω_{Z/S}` of a formally unramified morphism is exact
at `h^*Ω_{X/S}`. -/
@[sga "7 XI 1.3" "partial"]
theorem conormalShortComplex_exact : (conormalShortComplex h p).Exact :=
  unramifiedConormalShortComplex_exact _ p

/-- Let `h : Z ⟶ X` be a formally unramified morphism of schemes over `p : X ⟶ S` and assume
`Z` is formally smooth over `S`. Then the canonical sequence

```
0 ⟶ 𝒞_{Z/X} ⟶ h^*Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0
```

is short exact: the first arrow is a monomorphism, the sequence is exact at `h^*Ω_{X/S}`, and the
second arrow is an epimorphism. Here `𝒞_{Z/X}` is the conormal sheaf of the inclusion of `Z`
into the universal first-order thickening of `Z` over `X`. -/
@[stacks 06B7,
  ega "IV 17.2.5" "more general",
  sga "7 XI 1.3" "partial",
  sga "7 XVII 5.1" "more general"]
theorem conormalShortComplex_shortExact
    (hZ : AlgebraicGeometry.FormallySmooth (h ≫ p)) :
    (conormalShortComplex h p).ShortExact :=
  shortExact_of_isUniversalFirstOrderThickening _ p hZ

end Chosen

/-! ### The terms and arrows of the sequence, and its short exactness -/

section Faithfulness

variable {Z X S : Scheme.{u}} (h : Z ⟶ X) [FormallyUnramified h] (p : X ⟶ S)

/-- The left-hand term of the sequence is `𝒞_{Z/X}`, the conormal sheaf of the inclusion of `Z`
into the universal first-order thickening of `Z` over `X`. -/
example : (conormalShortComplex h p).X₁ =
    (conormalSheaf (universalFirstOrderThickening h).inclusion : Z.Modules) :=
  rfl

/-- The middle term of the sequence is `h^*Ω_{X/S}`. -/
example : (conormalShortComplex h p).X₂ =
    (Scheme.Modules.pullback h).obj (relativeDifferentials p) :=
  rfl

/-- The right-hand term of the sequence is `Ω_{Z/S}`. -/
example : (conormalShortComplex h p).X₃ = relativeDifferentials (h ≫ p) :=
  rfl

/-- The second arrow of the sequence is the canonical map on relative differentials. -/
example : (conormalShortComplex h p).g =
    relativeDifferentialsMap h p (h ≫ p) (𝟙 S) (by simp) :=
  rfl

/-- If `Z` is formally smooth over `S`, the first arrow `𝒞_{Z/X} ⟶ h^*Ω_{X/S}` is a
monomorphism. -/
example (hZ : AlgebraicGeometry.FormallySmooth (h ≫ p)) :
    Mono (conormalShortComplex h p).f :=
  (conormalShortComplex_shortExact h p hZ).mono_f

/-- If `Z` is formally smooth over `S`, the sequence is exact at `h^*Ω_{X/S}`. -/
example (hZ : AlgebraicGeometry.FormallySmooth (h ≫ p)) :
    (conormalShortComplex h p).Exact :=
  (conormalShortComplex_shortExact h p hZ).exact

/-- If `Z` is formally smooth over `S`, the second arrow `h^*Ω_{X/S} ⟶ Ω_{Z/S}` is an
epimorphism. -/
example (hZ : AlgebraicGeometry.FormallySmooth (h ≫ p)) :
    Epi (conormalShortComplex h p).g :=
  (conormalShortComplex_shortExact h p hZ).epi_g

end Faithfulness

end Stacks.UnramifiedConormalSequence

end
