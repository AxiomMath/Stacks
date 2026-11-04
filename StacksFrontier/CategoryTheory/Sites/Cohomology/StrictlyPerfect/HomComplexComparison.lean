module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomQuasiIso
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison from the internal Hom complex to derived internal Hom

Let `(C, O)` be a ringed site and let `E` and `F` be complexes of `O`-modules. Stacks 08JH
asserts that for `E` strictly perfect the derived internal Hom `RSheafHom(E, F)` is represented
by the ordinary internal Hom complex `SheafHom(E, F)` of Stacks 0A8Z. This file constructs the
canonical comparison

`Q(SheafHom(E, F)) ⟶ RSheafHom(E, F)`

whose invertibility is that assertion, and reduces the assertion to a single statement about
the internal Hom complex.

The comparison is built the way the source builds it: choose the K-injective resolution
`F ⟶ I` of the target, use that a K-injective target computes derived internal Hom
(`DerivedInternalHom.homComparison`), and invert the map induced on derived internal Hom by the
resolution. Only the first of the three factors can fail to be invertible, so the content of
Stacks 08JH is exactly that the induced map of internal Hom complexes

`SheafHom(E, F) ⟶ SheafHom(E, I)`

is a quasi-isomorphism. That reduction is `strictlyPerfectHomComparison_isIso_iff` below, and it
holds for arbitrary `E` — no hypothesis on `E` is used in it. The quasi-isomorphy itself is
`AlgebraicGeometry.RingedSite.homMap_quasiIso_of_isFiniteFreeSummand`, proved by the stupid
filtration of `E`, so Stacks 08JH follows: `strictlyPerfectHomComparison_isIso`.

## Main definitions

* `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison`: the canonical comparison from
  the class of the internal Hom complex to derived internal Hom.

## Main results

* `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso_iff`: the comparison is an
  isomorphism precisely when the internal Hom complex map induced by the K-injective
  augmentation of the target is a quasi-isomorphism.
* `AlgebraicGeometry.RingedSite.isIso_strictlyPerfectHomComparison_of_isKInjective`: the
  comparison is an isomorphism whenever the target is already K-injective. This is the case the
  derived internal Hom is defined by, and it is recorded here to pin down that the comparison is
  the intended morphism rather than a formally invertible one.
* `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso`: **Stacks 08JH.** The
  comparison is an isomorphism for a strictly perfect source.

## Implementation notes

The statements are taken over an arbitrary `AlgebraicGeometry.RingedSite.DerivedInternalHom X`
rather than over the chosen `canonicalDerivedInternalHom X`. That choice is
`Classical.choice` of a *proved* `Nonempty`, so there is nothing wrong with it; but it is
opaque, so a statement about it cannot be related to the explicit bifunctor
`derivedSheafHomBifunctor` that realizes it. Quantifying over the structure instead keeps the
results usable from either side, and instantiating at `canonicalDerivedInternalHom X` recovers
the form Stacks 08JH states.

Strict perfectness is spelled as boundedness together with
`AlgebraicGeometry.RingedSite.IsFiniteFreeSummand` on every term, rather than through the
predicate `IsStrictlyPerfect`, which cannot be mentioned at these
universes. Those are exactly the two clauses of Stacks 08FL; the reasons and the comparison
between the two spellings are in the implementation notes of
`AlgebraicGeometry.RingedSite.homMap_quasiIso_of_isFiniteFreeSummand` and of
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso_of_isStrictlyPerfect`.

The neighbouring `AlgebraicGeometry.RingedSite.homMap_quasiIso` (Stacks 0A95) proves
quasi-isomorphy of `homMap` but requires **both** targets to be K-injective, so it does not
apply: in Stacks 08JH the source target `F` is arbitrary and only its resolution is
K-injective.

## The two parts of Stacks 08JH

Stacks 08JH has two assertions, and they are tagged in two files.

* The degreewise direct-sum formula `H^n = ⨁_{n = p + q} SheafHom(E^{-q}, F^p)` together with
  its Hom-complex differential is
  `AlgebraicGeometry.RingedSite.strictlyPerfectHomDegreeIso`, tagged
  `@[stacks 08JH "finite direct-sum terms and Hom differential"]`.
* That this complex represents the derived internal Hom is
  `strictlyPerfectHomComparison_isIso` below, tagged
  `@[stacks 08JH "representation by the finite direct-sum Hom complex"]`.

Together those two cover the clause; nothing of Stacks 08JH is left unformalised.

## References

* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  (D : DerivedInternalHom.{u, d} X)
  (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The canonical comparison from the class of the internal Hom complex `SheafHom(E, F)` of
Stacks 0A8Z to the derived internal Hom `RSheafHom(E, F)`.

It is the composite of three maps: the map of internal Hom complexes induced by the K-injective
augmentation `F ⟶ I`, the inverse of the comparison identifying derived internal Hom with the
internal Hom complex at the K-injective target `I`, and the inverse of the map induced on
derived internal Hom by `F ⟶ I`, which is invertible because that augmentation is a
quasi-isomorphism. -/
def strictlyPerfectHomComparison :
    DerivedCategory.Q.obj (sheafHomComplex X E F).obj ⟶
      (D.hom.obj (op (DerivedCategory.Q.obj E))).obj (DerivedCategory.Q.obj F) :=
  DerivedCategory.Q.map (homMap X (𝟙 E) ((kInjectiveAugmentation X).app F)) ≫
    (D.homComparison E ((kInjectiveResolution X).obj F)).inv ≫
    inv ((D.hom.obj (op (DerivedCategory.Q.obj E))).map
      (DerivedCategory.Q.map ((kInjectiveAugmentation X).app F)))

/-- **The content of Stacks 08JH, isolated.** The comparison to derived internal Hom is an
isomorphism exactly when the map of internal Hom complexes induced by the K-injective
augmentation of the target is a quasi-isomorphism.

The last two factors of the comparison are invertible by construction, so this is the
cancellation of an isomorphism. No hypothesis on `E` enters; the strict perfectness of `E` in
Stacks 08JH is needed only for the right-hand side. -/
theorem strictlyPerfectHomComparison_isIso_iff :
    IsIso (strictlyPerfectHomComparison X D E F) ↔
      QuasiIso (homMap X (𝟙 E) ((kInjectiveAugmentation X).app F)) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  unfold strictlyPerfectHomComparison
  exact isIso_comp_right_iff _ _

/-- A K-injective target computes derived internal Hom through the ordinary internal Hom
complex, so the comparison is an isomorphism there. This is the defining case of derived
internal Hom; Stacks 08JH extends it to an arbitrary target at the cost of assuming the source
strictly perfect. -/
instance isIso_strictlyPerfectHomComparison_of_isKInjective [F.IsKInjective] :
    IsIso (strictlyPerfectHomComparison X D E F) :=
  (strictlyPerfectHomComparison_isIso_iff X D E F).2
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1
      (isIso_Q_map_homMap_kInjectiveAugmentation X E F))

/-- **Stacks 08JH**, the representation statement. For `E` strictly perfect — bounded, with
every term a direct summand of a finite free `O`-module — the derived internal Hom
`RSheafHom(E, F)` is represented by the ordinary internal Hom complex `SheafHom(E, F)` of
Stacks 0A8Z, the comparison being the canonical one.

By `strictlyPerfectHomComparison_isIso_iff` this is the quasi-isomorphy of the map of internal
Hom complexes induced by the K-injective augmentation of the target, which is
`homMap_quasiIso_of_isFiniteFreeSummand`.

The degreewise direct-sum description of that complex, the other half of Stacks 08JH, is
`strictlyPerfectHomDegreeIso`. -/
@[stacks 08JH "representation by the finite direct-sum Hom complex"]
theorem strictlyPerfectHomComparison_isIso
    (hbdd : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i : ℤ, IsFiniteFreeSummand X (E.X i)) :
    IsIso (strictlyPerfectHomComparison X D E F) :=
  (strictlyPerfectHomComparison_isIso_iff X D E F).2
    (homMap_quasiIso_of_isFiniteFreeSummand X ((kInjectiveAugmentation X).app F) E hbdd hterm)

end AlgebraicGeometry.RingedSite

end
