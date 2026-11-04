module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequencePairDerivation
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceUnramifiedPair
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedConormalSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceUnramifiedPairSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningDifferentialsIso
import StacksCore.Tactic.StacksAttribute

/-!
# The conormal sequence of a pair of formally unramified morphisms of algebraic spaces

Let `S` be a scheme and let

```
  Z --i--→ X
   \       |
    j      g
     \     ↓
      `--→ Y
```

be a commutative triangle of algebraic spaces over `S` with `i` and `j` formally unramified.
Stacks 06BE asserts that there is a canonical exact sequence

```
  𝒞_{Z/Y} ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Y} ⟶ 0
```

whose first arrow comes from Stacks 060A and whose second arrow comes from Stacks 060F.  This
file proves it, as `AlgebraicGeometry.Space.exists_conormalPairSequence_exact`, with no
hypothesis beyond those of the source.

## How the situation is presented

Formal unramifiedness of `i` and `j` is presented by universal first-order thickenings
`ti : UniversalFirstOrderThickening i` and `tj : UniversalFirstOrderThickening j`, which exist by
Stacks 0606 (`AlgebraicGeometry.Space.nonempty_universalFirstOrderThickening`) and carry the
formal unramifiedness as a field; the conormal sheaves `𝒞_{Z/X}` and `𝒞_{Z/Y}` are the conormal
modules of the smaller spaces in the two ambient spaces `Z'` and `Z''` (Stacks 0607), read on the
smaller space of `ti`.

* The first arrow is the map of conormal modules of Stacks 060A attached to the canonical
  morphism `Z' ⟶ Z''` of thickenings over `Y`
  (`AlgebraicGeometry.Space.universalThickeningComparison`).  It is written as the conormal map
  `AlgebraicGeometry.Space.conormalMap` of Stacks 04CP for the square of closed subspaces of that
  morphism, which is what `AlgebraicGeometry.Space.universalThickeningConormalMap` is by
  definition (`AlgebraicGeometry.Space.universalThickeningConormalMap_eq_conormalMap`, proved by
  `rfl`).
* The second arrow is the canonical first arrow
  `AlgebraicGeometry.Space.thickeningConormalFirstMap` of Stacks 060F, and
  `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.isIso_thickeningSheafOfDifferentialsMap`
  supplies the isomorphism of Stacks 060E.

## The proof

The source reduces to the case of schemes, Stacks 067V, which in turn applies Stacks 067L to the
two closed immersions `Z ⟶ Z'` and `Z ⟶ Z''` over the canonical morphism `Z' ⟶ Z''`.  Here the
statement of Stacks 067L for that pair is proved directly on the small étale site of `Z'`, in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequencePairDerivation.lean`:

* every morphism out of `𝒞_{Z/Z'}` killed by the first arrow factors through the first arrow
  `𝒞_{Z/Z'} ⟶ ι^*Ω_{Z'/Y}` of Stacks 05ZA
  (`AlgebraicGeometry.Space.exists_conormalSequenceFirstMap_comp_eq`),
  which is exactness at `𝒞_{Z/X}`;
* the composite vanishes because `Ω_{Z''/Y}` does, `Z''` being formally unramified over `Y`
  (Stacks 0609 and 04G9);
* the second arrow is an epimorphism because the sequence of Stacks 060F is exact at
  `i^*Ω_{X/Y}` and `Ω_{Z/Y}` vanishes, `j` being formally unramified.

The isomorphism of Stacks 060E carries the first arrow of Stacks 05ZA onto the second arrow of
the sequence, which transports exactness.

## Main results

* `AlgebraicGeometry.Space.exact_conormalMap_conormalSequenceFirstMap`: the sequence
  `f^*𝒞_{W/X'} ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Y}` is exact for a thickening `Z ⊆ X` and a morphism
  `X ⟶ X'` restricting to an isomorphism of `Z` onto a closed subspace `W`.
* `AlgebraicGeometry.Space.exists_conormalMap_comp_thickeningConormalFirstMap_exact`: the same
  for the second arrow of Stacks 060F.
* `AlgebraicGeometry.Space.exists_conormalPairSequence_exact`: **Stacks 06BE.**

## References

* [Stacks Project, Tag 06BE](https://stacks.math.columbia.edu/tag/06BE)
* [Stacks Project, Tag 060A](https://stacks.math.columbia.edu/tag/060A)
* [Stacks Project, Tag 060F](https://stacks.math.columbia.edu/tag/060F)
* [Stacks Project, Tag 060E](https://stacks.math.columbia.edu/tag/060E)
* [Stacks Project, Tag 067V](https://stacks.math.columbia.edu/tag/067V)
* [Stacks Project, Tag 067L](https://stacks.math.columbia.edu/tag/067L)
* [Stacks Project, Tag 0606](https://stacks.math.columbia.edu/tag/0606)
* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607)
* [Stacks Project, Tag 0609](https://stacks.math.columbia.edu/tag/0609)
* [Stacks Project, Tag 04G9](https://stacks.math.columbia.edu/tag/04G9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Pair

variable {X X' Y : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1) (g : X ⟶ X')
  (W : ClosedSubspaces B S hS X'.1)
  (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS))
  (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' W)

attribute [local irreducible] modulePullback in
/-- **Stacks 067L for a thickening, in cokernel form.**  Let `Z ⊆ X` be a thickening, let
`g : X ⟶ X'` restrict to an isomorphism of `Z` onto a closed subspace `W ⊆ X'`, and let
`b : X ⟶ Y` factor through `g`.  Every morphism out of `𝒞_{Z/X}` killed by the conormal map
`f^*𝒞_{W/X'} ⟶ 𝒞_{Z/X}` of Stacks 04CP factors through the first arrow
`𝒞_{Z/X} ⟶ i^*Ω_{X/Y}` of Stacks 05ZA. -/
theorem exists_conormalSequenceFirstMap_comp_eq (hZ : IsThickening B S hS X Z.1) [IsIso f]
    (q : X' ⟶ Y) (b : X ⟶ Y) (hb : g ≫ q = b) {N : Modules.{u, u} B S hS Z.1.toFunctor Z.2.1}
    (k : conormalModule B S hS X Z ⟶ N) (hk : conormalMap B S hS Z W g f hsq ≫ k = 0) :
    ∃ h, conormalSequenceFirstMap B S hS Z b ≫ h = k := by
  subst hb
  have hk' := (conormalMap_comp_eq_zero_iff B S hS Z g W f hsq k).1 hk
  obtain ⟨h, hh⟩ := exists_conormalSequenceIdealPullbackMap_comp_eq B S hS Z g W f q N
    ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).homEquiv _ _ k) hZ hsq hk'
  exact ⟨h, hh.trans (Equiv.symm_apply_apply _ k)⟩

/-- **The composite of the conormal map of Stacks 04CP and the first arrow of Stacks 05ZA
vanishes** as soon as the sheaf of differentials of `X'` over the base vanishes. -/
theorem conormalMap_comp_conormalSequenceFirstMap_eq_zero (q : X' ⟶ Y) (b : X ⟶ Y)
    (hb : g ≫ q = b) (hΩ : IsZero (sheafOfDifferentials B S hS q)) :
    conormalMap B S hS Z W g f hsq ≫ conormalSequenceFirstMap B S hS Z b = 0 := by
  subst hb
  show conormalMap B S hS Z W g f hsq ≫ conormalSequenceIdealPullbackMap B S hS Z (g ≫ q) = 0
  have h0 := idealSheafMap_comp_conormalSequenceIdealDifferential_eq_zero B S hS Z g W f hsq q hΩ
  rw [conormalSequenceIdealPullbackMap_eq_homEquiv_symm]
  refine (conormalMap_comp_eq_zero_iff B S hS Z g W f hsq _).2 ?_
  exact (congrArg (fun m ↦ idealSheafMap B S hS Z W g f hsq ≫ m)
    (Equiv.apply_symm_apply _ _)).trans h0

/-- **The sequence `f^*𝒞_{W/X'} ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Y}` is exact at `𝒞_{Z/X}`**, for a
thickening `Z ⊆ X`, a morphism `g : X ⟶ X'` restricting to an isomorphism of `Z` onto a closed
subspace `W ⊆ X'`, and a base `q : X' ⟶ Y` over which `X'` has vanishing differentials, provided
the first arrow of Stacks 05ZA is an epimorphism. -/
theorem exact_conormalMap_conormalSequenceFirstMap (hZ : IsThickening B S hS X Z.1) [IsIso f]
    (q : X' ⟶ Y) (b : X ⟶ Y) (hb : g ≫ q = b) (hΩ : IsZero (sheafOfDifferentials B S hS q))
    [Epi (conormalSequenceFirstMap B S hS Z b)] :
    (ShortComplex.mk _ _
      (conormalMap_comp_conormalSequenceFirstMap_eq_zero B S hS Z g W f hsq q b hb hΩ)).Exact := by
  refine ShortComplex.exact_of_g_is_cokernel _ (CokernelCofork.IsColimit.ofπ' _ _ ?_)
  intro N k hk
  have h := exists_conormalSequenceFirstMap_comp_eq B S hS Z g W f hsq hZ q b hb k hk
  exact ⟨h.choose, h.choose_spec⟩

end Pair

section UnramifiedPair

variable {X Y Z : AlgebraicSpaces B S hS}

/-- The identification of the smaller spaces of two universal first-order thickenings of `Z` is an
isomorphism of algebraic spaces. -/
theorem isIso_homMk_universalThickeningSourceMap {i : Z ⟶ X} {j : Z ⟶ Y}
    (ti : UniversalFirstOrderThickening B S hS i) (tj : UniversalFirstOrderThickening B S hS j) :
    IsIso (ObjectProperty.homMk (universalThickeningSourceMap B S hS ti tj) :
      (⟨(thickeningClosedSubspace B S hS ti.isUniversal).1.toFunctor,
          (thickeningClosedSubspace B S hS ti.isUniversal).2.1⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨(thickeningClosedSubspace B S hS tj.isUniversal).1.toFunctor,
            (thickeningClosedSubspace B S hS tj.isUniversal).2.1⟩) :=
  let e := ti.sourceIso.symm ≪≫ tj.sourceIso
  ⟨ObjectProperty.homMk e.inv, ObjectProperty.hom_ext _ e.hom_inv_id,
    ObjectProperty.hom_ext _ e.inv_hom_id⟩

/-- **The sequence `f^*𝒞_{W/X'} ⟶ 𝒞_{Z/X} ⟶ h^*Ω_{X/Y} ⟶ 0` of a universal first-order
thickening.**  Let `Z ⊂ Z'` be a universal first-order thickening over `X` with structure
morphism `p`, let `g : X ⟶ Y`, and let `c : Z' ⟶ X'` restrict to an isomorphism `f` of `Z` onto
a closed subspace `W ⊆ X'`, where `X'` lies over `Y` with vanishing differentials and
`Z ⟶ Z' ⟶ X ⟶ Y` is formally unramified.  Then the conormal map of Stacks 04CP followed by the
first arrow of Stacks 060F composes to zero, is exact at `𝒞_{Z/X}`, and the second arrow is an
epimorphism. -/
theorem exists_conormalMap_comp_thickeningConormalFirstMap_exact {X' Z' : AlgebraicSpaces B S hS}
    {Zs : Subfunctor Z'.1} {p : Z' ⟶ X} (hZ : IsUniversalFirstOrderThickening B S hS Zs p)
    (g : X ⟶ Y) (he : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ g))
    (W : ClosedSubspaces B S hS X'.1) (c : Z' ⟶ X')
    (f : (⟨(thickeningClosedSubspace B S hS hZ).1.toFunctor,
        (thickeningClosedSubspace B S hS hZ).2.1⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨W.1.toFunctor, W.2.1⟩) [IsIso f]
    (hsq : subspaceInclusion B S hS Z' (thickeningClosedSubspace B S hS hZ) ≫ c =
      f ≫ subspaceInclusion B S hS X' W)
    (q : X' ⟶ Y) (hb : c ≫ q = p ≫ g) (hΩ : IsZero (sheafOfDifferentials B S hS q))
    (hj : FormallyUnramified (universalThickeningInclusion B S hS hZ ≫ p ≫ g).hom) :
    ∃ hc : conormalMap B S hS (thickeningClosedSubspace B S hS hZ) W c f hsq ≫
        thickeningConormalFirstMap B S hS hZ g he = 0,
      (ShortComplex.mk _ _ hc).Exact ∧ Epi (thickeningConormalFirstMap B S hS hZ g he) := by
  have : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ g) := he
  have hZt := IsNthOrderThickening.isThickening B S hS hZ.firstOrder
  have hepi := epi_thickeningConormalFirstMap B S hS g hZ he
    (conormalSequenceFirstMap_comp_pullbackDifferentialsMap_thickening B S hS hZ g)
    (exact_conormalSequence B S hS (p ≫ g) (thickeningClosedSubspace B S hS hZ)) hj
  have key := thickeningConormalFirstMap_comp_thickeningSheafOfDifferentialsMap B S hS hZ g he
  have : Epi (conormalSequenceFirstMap B S hS (thickeningClosedSubspace B S hS hZ) (p ≫ g)) := by
    rw [← key]
    exact epi_comp _ _
  have hex := exact_conormalMap_conormalSequenceFirstMap B S hS
    (thickeningClosedSubspace B S hS hZ) c W f hsq hZt q (p ≫ g) hb hΩ
  have hc0 := conormalMap_comp_conormalSequenceFirstMap_eq_zero B S hS
    (thickeningClosedSubspace B S hS hZ) c W f hsq q (p ≫ g) hb hΩ
  have hc : conormalMap B S hS (thickeningClosedSubspace B S hS hZ) W c f hsq ≫
      thickeningConormalFirstMap B S hS hZ g he = 0 := by
    refine (cancel_mono (thickeningSheafOfDifferentialsMap B S hS hZ g)).mp ?_
    rw [Category.assoc, key, zero_comp]
    exact hc0
  refine ⟨hc, ?_, hepi⟩
  have hsc : ShortComplex.mk _ _ hc ≅ ShortComplex.mk _ _ hc0 :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (asIso (thickeningSheafOfDifferentialsMap B S hS hZ g)) (by simp)
      (by simpa using key.symm)
  exact (ShortComplex.exact_iff_of_iso hsc).mpr hex

/-- **Stacks 06BE.**  Let `i : Z ⟶ X` and `j : Z ⟶ Y` be formally unramified morphisms of
algebraic spaces over `S` with `i ≫ g = j`, presented by universal first-order thickenings
`ti` of `i` and `tj` of `j`.  Then the canonical sequence

```
  𝒞_{Z/Y} ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Y} ⟶ 0
```

is exact: the composite of the two arrows is zero, the sequence is exact at `𝒞_{Z/X}`, and the
second arrow is an epimorphism.  The first arrow is the map of conormal modules of Stacks 060A
attached to the canonical morphism `Z' ⟶ Z''` of the two thickenings, written as the conormal map
of Stacks 04CP of its square of closed subspaces; the second is the canonical first arrow of
Stacks 060F. -/
@[stacks 06BE]
theorem exists_conormalPairSequence_exact (g : X ⟶ Y) {i : Z ⟶ X} {j : Z ⟶ Y}
    (hij : i ≫ g = j) (ti : UniversalFirstOrderThickening B S hS i)
    (tj : UniversalFirstOrderThickening B S hS j) :
    ∃ hc : conormalMap B S hS (thickeningClosedSubspace B S hS ti.isUniversal)
          (thickeningClosedSubspace B S hS tj.isUniversal)
          (universalThickeningComparison B S hS g hij ti tj)
          (ObjectProperty.homMk (universalThickeningSourceMap B S hS ti tj))
          (universalThickeningComparison_square B S hS g hij ti tj) ≫
        thickeningConormalFirstMap B S hS ti.isUniversal g
          (ti.isUniversal.isIso_thickeningSheafOfDifferentialsMap B S hS g) = 0,
      (ShortComplex.mk _ _ hc).Exact ∧
        Epi (thickeningConormalFirstMap B S hS ti.isUniversal g
          (ti.isUniversal.isIso_thickeningSheafOfDifferentialsMap B S hS g)) :=
  have := isIso_homMk_universalThickeningSourceMap B S hS ti tj
  exists_conormalMap_comp_thickeningConormalFirstMap_exact B S hS ti.isUniversal g
    (ti.isUniversal.isIso_thickeningSheafOfDifferentialsMap B S hS g)
    (thickeningClosedSubspace B S hS tj.isUniversal)
    (universalThickeningComparison B S hS g hij ti tj)
    (ObjectProperty.homMk (universalThickeningSourceMap B S hS ti tj))
    (universalThickeningComparison_square B S hS g hij ti tj)
    tj.toBase (universalThickeningComparison_over B S hS g hij ti tj)
    (isZero_sheafOfDifferentials_of_formallyUnramified B S hS _
      (formallyUnramified_of_isUniversalFirstOrderThickening B S hS tj.sub tj.toBase
          tj.isUniversal))
    (by
    have h1 : ti.sub.ι ≫ ti.toBase.hom = ti.sourceIso.inv ≫ i.hom := by
      rw [← ti.sourceIso_ι_toBase, Iso.inv_hom_id_assoc]
    have h : (universalThickeningInclusion B S hS ti.isUniversal ≫ ti.toBase ≫ g).hom =
        ti.sourceIso.inv ≫ j.hom := by
      show ti.sub.ι ≫ ti.toBase.hom ≫ g.hom = _
      rw [← Category.assoc, h1, Category.assoc, ← hij]
      rfl
    rw [h]
    exact formallyUnramified_comp _ _ (formallyUnramified_of_mono _) tj.formallyUnramified
    )

end UnramifiedPair

end AlgebraicGeometry.Space

end
