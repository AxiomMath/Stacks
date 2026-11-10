module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineStalkLegsLinear
public import StacksFrontier.Topology.Sheaves.Modules.ConormalSequenceStalkSquareMaps
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentSquare

/-!
# The stalk legs of Stacks 0D0I are natural in a square

Let
```
B ──β──▸ B'
▲         ▲
a         a'
│         │
A ──f──▸ A'
```
be a commutative square of sheaves of commutative rings on a topological space `T` and let `z`
be a point of `T`.  Stacks 08TX attaches to the square a chain map
`NL_{B/A} ⟶ NL_{B'/A'}` of complexes of sheaves of modules
(`Stacks.SheafOfModules.spaceNaiveCotangentComplexMapOfSquare`), and
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineStalkLegsLinear` identifies the stalk
at `z` of each term of `NL_{B/A}` with the corresponding term of `NL_{Bₓ/Aₓ}`.  This file
computes the stalk of that chain map in terms of those identifications: it is the functorial map
of the morphism of canonical presentations of the stalks that the square induces.

This is the one statement the stalkwise comparison of Stacks 0FJZ was missing.  The two families
it relates had never been related: the legs
`Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOneLinear` and
`Stacks.NaiveCotangentAffineStalkLegs.stalkLegZeroLinear` land on
`Algebra.Generators.self Aₓ Bₓ` through
`Stacks.SheafOfModules.canonicalStalkExtensionHom`, while the square-level stalk lemmas
`Stacks.Sites.Conormal.conormalSheafMapOfSquareStalk_eq_cotangentMap` and
`Stacks.Sites.Conormal.tensorSheafMapOfSquareStalk_eq_cotangentSpaceMap` land on
`Stacks.Sites.Conormal.stalkExtensionHomOfSquare`, a morphism between the stalk extensions of
the two *presentations*.  The bridge is
`Stacks.NaiveCotangentAffineStalkLegs.canonicalStalkExtensionHom_comp_stalkExtensionHomOfSquare`:
the square of morphisms of extensions
```
Aₓ[Bₓ] ──────▸ A'ₓ[B'ₓ]
   ▲              ▲
   │              │
(A[B])ₓ ─────▸ (A'[B'])ₓ
```
commutes.

## Main definitions

* `Stacks.NaiveCotangentAffineStalkLegs.squareFreeAlgebraMap`: the morphism `A[B] ⟶ A'[B']` of
  the two canonical polynomial presentations attached to the square.
* `Stacks.NaiveCotangentAffineStalkLegs.generatorsSelfStalkHomOfSquare`: the morphism of
  extensions `Generators.self Aₓ Bₓ ⟶ Generators.self A'ₓ B'ₓ` attached to the square.
* `Stacks.NaiveCotangentAffineStalkLegs.canonicalStalkExtensionHomOfSquare`: the morphism of the
  stalk extensions of the two canonical presentations attached to the square, that is,
  `Stacks.Sites.Conormal.stalkExtensionHomOfSquare` for the square whose middle row is
  `squareFreeAlgebraMap`.

## Main results

* `Stacks.NaiveCotangentAffineStalkLegs.canonicalStalkRingEquiv_variable`: the identification
  `(A[B])ₓ ≅ Aₓ[Bₓ]` carries the germ of the variable attached to a section of `B` to the
  variable indexed by the germ of that section.  This is the variable half of the pre-existing
  `Stacks.SheafOfModules.canonicalStalkRingEquiv_coefficientMap`, and it is what makes the stalk
  of `A[B] ⟶ A'[B']` computable.
* `Stacks.NaiveCotangentAffineStalkLegs.canonicalStalkRingEquiv_squareFreeAlgebraMap`: read
  through `(A[B])ₓ ≅ Aₓ[Bₓ]` and `(A'[B'])ₓ ≅ A'ₓ[B'ₓ]`, the stalk of `A[B] ⟶ A'[B']` is the
  polynomial map `Stacks.NaiveCotangentAffineComparison.squareRingHom` of the square of stalk
  rings.
* `Stacks.NaiveCotangentAffineStalkLegs.canonicalStalkExtensionHom_comp_stalkExtensionHomOfSquare`:
  the two routes from `(A[B])ₓ` to `A'ₓ[B'ₓ]` agree.
* `NaiveCotangentAffineStalkLegs.stalkLegLinear_spaceNaiveCotangentComplexMapOfSquare_negOne` and
  `NaiveCotangentAffineStalkLegs.stalkLegLinear_spaceNaiveCotangentComplexMapOfSquare_zero`:
  **the stalk of the chain map of Stacks 08TX.**  Through the two legs, the stalk of the degree
  `-1`, respectively degree `0`, component of `NL_{B/A} ⟶ NL_{B'/A'}` is
  `Algebra.Extension.Cotangent.map`, respectively `Algebra.Extension.CotangentSpace.map`, of
  `generatorsSelfStalkHomOfSquare`.

## Implementation notes

**The scalar rings.**  The two legs are linear over the `RingCat`-valued stalk of
`Stacks.SheafOfModules.Tensor.ringSheaf B`, for the reasons recorded in
`StacksFrontier.Topology.Sheaves.Modules.ConormalSequenceStalkTargetAction`; nothing here changes
that, and no new `Module` instance is declared.  The statements below are additive: the two sides
of each are linear over different rings — over the stalk of `B` at the source and over the stalk
of `B'` at the target — so only their underlying maps can be compared, exactly as for
`Stacks.Sites.Conormal.conormalSheafMapOfSquareStalk_eq_cotangentMap`.

**The `Aₓ`-algebra structure on `B'ₓ`.**  `Algebra.Extension.Cotangent.map` of a morphism from an
extension of `Bₓ` over `Aₓ` to an extension of `B'ₓ` over `A'ₓ` needs `B'ₓ` to be an
`Aₓ`-algebra for which `Aₓ → A'ₓ → B'ₓ` is a tower.  As in
`StacksFrontier.Topology.Sheaves.Modules.ConormalSequenceStalkSquareMaps`, that structure is read
off a morphism `d : A ⟶ B'` of sheaves together with an equation `f ≫ a' = d` it satisfies,
rather than off a composite, so that the structures appearing in two statements about the same
square are the same structure and not merely propositionally equal ones.

**Term-mode proofs.**  The direct image along a composite and the composite of the direct images
are definitionally but not syntactically equal in this area, so `rw` cannot match across the two
spellings; the proofs below are `Eq.trans`/`congrArg` chains, like those of
`Stacks.NaiveCotangentAffineStalkLegs.stalkLeg_d`.  The one place a lambda needs a type
ascription is the rewrite of the bridge under `Algebra.Extension.Cotangent.map`, whose target
extension is not determined by the element it is applied to.

**Transfer to the additive legs.**  `stalkLegNegOneLinear_apply` and `stalkLegZeroLinear_apply`
are `rfl`, so the two main results hold verbatim for
`Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOne` and
`Stacks.NaiveCotangentAffineStalkLegs.stalkLegZero`.

## References

* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX), the canonical map of
  naive cotangent complexes attached to a square of sheaves of rings.
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I), of whose proof the two
  legs are a step.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

noncomputable section

namespace Stacks.NaiveCotangentAffineStalkLegs

open Stacks.SheafOfModules Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open Stacks.RelativeDifferentialStalk (algebraStalk)

/-! ### The polynomial map of a square of rings on generators -/

section SquareRingHom

variable {R R' S S' : Type u} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
  [Algebra R R'] [Algebra S S']

/-- The polynomial map of a square of rings acts on coefficients by `R ⟶ R'`. -/
theorem squareRingHom_C (r : R) :
    Stacks.NaiveCotangentAffineComparison.squareRingHom (R := R) (S := S) (S' := S')
        (MvPolynomial.C r) =
      MvPolynomial.C (algebraMap R R' r) :=
  MvPolynomial.eval₂Hom_C ((MvPolynomial.C : R' →+* MvPolynomial S' R').comp (algebraMap R R'))
    (fun s : S => (MvPolynomial.X (algebraMap S S' s) : MvPolynomial S' R')) r

/-- The polynomial map of a square of rings carries the variable `X_s` to the variable
`X_{s'}`, for `s'` the image of `s` under `S ⟶ S'`. -/
theorem squareRingHom_X (s : S) :
    Stacks.NaiveCotangentAffineComparison.squareRingHom (R := R) (R' := R') (S := S) (S' := S')
        (MvPolynomial.X s) =
      MvPolynomial.X (algebraMap S S' s) :=
  MvPolynomial.eval₂Hom_X' ((MvPolynomial.C : R' →+* MvPolynomial S' R').comp (algebraMap R R'))
    (fun s : S => (MvPolynomial.X (algebraMap S S' s) : MvPolynomial S' R')) s

end SquareRingHom

section Square

variable {T : TopCat.{u}}
  (A A' B B' : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (a : A ⟶ B) (a' : A' ⟶ B') (f : A ⟶ A') (β : B ⟶ B') (z : T)

/-! ### The variables of the canonical presentation on stalks -/

/-- **The identification `(A[B])ₓ ≅ Aₓ[Bₓ]` carries the germ of the variable attached to a
section `t` of `B` to the variable indexed by the germ of `t`.**  This is the variable half of
`Stacks.SheafOfModules.canonicalStalkRingEquiv_coefficientMap`. -/
theorem canonicalStalkRingEquiv_variable (U : Opens T) (hz : z ∈ U)
    (t : ToType (B.obj.obj (op U))) :
    canonicalStalkRingEquiv A B z
        ((TopCat.Presheaf.germ (AA A B).obj U z hz).hom
          ((freeAlgebraSheafVariable (Opens.grothendieckTopology T) A
            (underlyingPresheaf (Opens.grothendieckTopology T) B)).app (op U) t)) =
      MvPolynomial.X ((TopCat.Presheaf.germ B.obj U z hz).hom t) := by
  refine Eq.trans (congrArg (MvPolynomial.rename
      (Equiv.ofBijective _ (bijective_presentationStalkVariable_id B z)))
    (freeAlgebraSheafStalkRingEquiv_variable A
      (underlyingPresheaf (Opens.grothendieckTopology T) B) z U hz t)) ?_
  refine Eq.trans (MvPolynomial.rename_X _ _) ?_
  exact congrArg MvPolynomial.X (presentationStalkVariable_germ B
    (underlyingPresheaf (Opens.grothendieckTopology T) B) (𝟙 _) z U hz t)

/-! ### The morphism of canonical presentations attached to the square -/

/-- The morphism `A[B] ⟶ A'[B']` of the two canonical polynomial presentations attached to a
commutative square, in the spelling of
`Stacks.NaiveCotangentAffineStalkLegs.AA`. -/
abbrev squareFreeAlgebraMap : AA A B ⟶ AA A' B' :=
  canonicalFreeAlgebraMapOfSquare (Opens.grothendieckTopology T) A A' B B' f β

/-- The morphism `A[B] ⟶ A'[B']` respects the structural morphisms from the coefficients. -/
theorem coefficientMap_comp_squareFreeAlgebraMap :
    f ≫ freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A'
        (underlyingPresheaf (Opens.grothendieckTopology T) B') =
      freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A
          (underlyingPresheaf (Opens.grothendieckTopology T) B) ≫
        squareFreeAlgebraMap A A' B B' f β :=
  (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare (Opens.grothendieckTopology T) A A'
    (underlyingPresheaf (Opens.grothendieckTopology T) B)
    (underlyingPresheaf (Opens.grothendieckTopology T) B') f
    (underlyingPresheafMap (Opens.grothendieckTopology T) B B' β)).symm

/-! ### The morphism of canonical presentations of the stalks -/

variable (hsq : a ≫ β = f ≫ a')

include hsq in
/-- **The morphism of canonical presentations of the stalks attached to a commutative square.**
The square induces `Aₓ ⟶ A'ₓ` and `Bₓ ⟶ B'ₓ`, which commute over `Aₓ`, hence a morphism of the
canonical presentations `Aₓ[Bₓ] ⟶ Bₓ` and `A'ₓ[B'ₓ] ⟶ B'ₓ`. -/
def generatorsSelfStalkHomOfSquare :
    letI := algebraStalk a.hom z
    letI := algebraStalk a'.hom z
    letI := algebraStalk f.hom z
    letI := algebraStalk β.hom z
    (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
        (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension.Hom
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A'.obj z))
        (ToType (TopCat.Presheaf.stalk B'.obj z))).toExtension :=
  letI := algebraStalk a.hom z
  letI := algebraStalk a'.hom z
  letI := algebraStalk f.hom z
  letI := algebraStalk β.hom z
  Stacks.NaiveCotangentAffineComparison.selfSquareHom
    (fun r => stalkFunctor_map_square_apply z a β f a' hsq r)

include hsq in
/-- The underlying map of polynomial rings is the polynomial map of the square of stalk rings. -/
theorem generatorsSelfStalkHomOfSquare_toRingHom :
    letI := algebraStalk a.hom z
    letI := algebraStalk a'.hom z
    letI := algebraStalk f.hom z
    letI := algebraStalk β.hom z
    (generatorsSelfStalkHomOfSquare A A' B B' a a' f β z hsq).toRingHom =
      Stacks.NaiveCotangentAffineComparison.squareRingHom := rfl

/-! ### The stalk of the morphism `A[B] ⟶ A'[B']` -/

/-- **The stalk of the morphism `A[B] ⟶ A'[B']` of a square is the polynomial map of the square
of stalk rings.**  Read through the two identifications `(A[B])ₓ ≅ Aₓ[Bₓ]` and
`(A'[B'])ₓ ≅ A'ₓ[B'ₓ]`, the stalk of `A[B] ⟶ A'[B']` is
`Stacks.NaiveCotangentAffineComparison.squareRingHom`: it is `Aₓ ⟶ A'ₓ` on coefficients and
carries the variable `X_b` to the variable `X_{βₓ b}`. -/
theorem canonicalStalkRingEquiv_comp_squareFreeAlgebraMap :
    letI := algebraStalk f.hom z
    letI := algebraStalk β.hom z
    ((canonicalStalkRingEquiv A' B' z).toRingHom.comp
          ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map
            (squareFreeAlgebraMap A A' B B' f β).hom).hom).comp
        (canonicalStalkRingEquiv A B z).symm.toRingHom =
      Stacks.NaiveCotangentAffineComparison.squareRingHom := by
  let := algebraStalk f.hom z
  let := algebraStalk β.hom z
  apply MvPolynomial.ringHom_ext
  · intro r
    change canonicalStalkRingEquiv A' B' z
        (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map
          (squareFreeAlgebraMap A A' B B' f β).hom).hom
          ((canonicalStalkRingEquiv A B z).symm (MvPolynomial.C r))) =
      Stacks.NaiveCotangentAffineComparison.squareRingHom (MvPolynomial.C r)
    have hs : (canonicalStalkRingEquiv A B z).symm (MvPolynomial.C r) =
        ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A
            (underlyingPresheaf (Opens.grothendieckTopology T) B)).hom).hom r :=
      (canonicalStalkRingEquiv A B z).symm_apply_eq.2
        (canonicalStalkRingEquiv_coefficientMap A B z r).symm
    have hmid := stalkFunctor_map_square_apply z
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A
        (underlyingPresheaf (Opens.grothendieckTopology T) B))
      (squareFreeAlgebraMap A A' B B' f β) f
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A'
        (underlyingPresheaf (Opens.grothendieckTopology T) B'))
      (coefficientMap_comp_squareFreeAlgebraMap A A' B B' f β).symm r
    refine Eq.trans (congrArg (fun y => canonicalStalkRingEquiv A' B' z
        (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map
          (squareFreeAlgebraMap A A' B B' f β).hom).hom y)) hs) ?_
    refine Eq.trans (congrArg (canonicalStalkRingEquiv A' B' z) hmid) ?_
    refine Eq.trans (canonicalStalkRingEquiv_coefficientMap A' B' z _) ?_
    exact (squareRingHom_C r).symm
  · intro σ
    obtain ⟨U, hz, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq B.obj σ
    change canonicalStalkRingEquiv A' B' z
        (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map
          (squareFreeAlgebraMap A A' B B' f β).hom).hom
          ((canonicalStalkRingEquiv A B z).symm
            (MvPolynomial.X ((TopCat.Presheaf.germ B.obj U z hz).hom t)))) =
      Stacks.NaiveCotangentAffineComparison.squareRingHom
        (MvPolynomial.X ((TopCat.Presheaf.germ B.obj U z hz).hom t))
    have hs : (canonicalStalkRingEquiv A B z).symm
          (MvPolynomial.X ((TopCat.Presheaf.germ B.obj U z hz).hom t)) =
        (TopCat.Presheaf.germ (AA A B).obj U z hz).hom
          ((freeAlgebraSheafVariable (Opens.grothendieckTopology T) A
            (underlyingPresheaf (Opens.grothendieckTopology T) B)).app (op U) t) :=
      (canonicalStalkRingEquiv A B z).symm_apply_eq.2
        (canonicalStalkRingEquiv_variable A B z U hz t).symm
    have hv : ((squareFreeAlgebraMap A A' B B' f β).hom.app (op U)).hom
          ((freeAlgebraSheafVariable (Opens.grothendieckTopology T) A
            (underlyingPresheaf (Opens.grothendieckTopology T) B)).app (op U) t) =
        (freeAlgebraSheafVariable (Opens.grothendieckTopology T) A'
            (underlyingPresheaf (Opens.grothendieckTopology T) B')).app (op U)
          ((underlyingPresheafMap (Opens.grothendieckTopology T) B B' β).app (op U) t) :=
      congrArg (fun n : underlyingPresheaf (Opens.grothendieckTopology T) B ⟶
          underlyingPresheaf (Opens.grothendieckTopology T) (AA A' B') => n.app (op U) t)
        (freeAlgebraSheafVariable_comp_freeAlgebraMapOfSquare (Opens.grothendieckTopology T) A A'
          (underlyingPresheaf (Opens.grothendieckTopology T) B)
          (underlyingPresheaf (Opens.grothendieckTopology T) B') f
          (underlyingPresheafMap (Opens.grothendieckTopology T) B B' β))
    refine Eq.trans (congrArg (fun y => canonicalStalkRingEquiv A' B' z
        (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map
          (squareFreeAlgebraMap A A' B B' f β).hom).hom y)) hs) ?_
    refine Eq.trans (congrArg (canonicalStalkRingEquiv A' B' z)
      ((TopCat.Presheaf.stalkFunctor_map_germ_apply U z hz
          (squareFreeAlgebraMap A A' B B' f β).hom _).trans
        (congrArg (TopCat.Presheaf.germ (AA A' B').obj U z hz).hom hv))) ?_
    refine Eq.trans (canonicalStalkRingEquiv_variable A' B' z U hz _) ?_
    refine Eq.trans (congrArg MvPolynomial.X
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U z hz β.hom t).symm) ?_
    exact (squareRingHom_X ((TopCat.Presheaf.germ B.obj U z hz).hom t)).symm

/-- The stalk of the morphism `A[B] ⟶ A'[B']` of a square is the polynomial map of the square of
stalk rings, read on elements. -/
theorem canonicalStalkRingEquiv_squareFreeAlgebraMap
    (p : ToType (TopCat.Presheaf.stalk (AA A B).obj z)) :
    letI := algebraStalk f.hom z
    letI := algebraStalk β.hom z
    canonicalStalkRingEquiv A' B' z
        (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map
          (squareFreeAlgebraMap A A' B B' f β).hom).hom p) =
      Stacks.NaiveCotangentAffineComparison.squareRingHom
        (canonicalStalkRingEquiv A B z p) := by
  let := algebraStalk f.hom z
  let := algebraStalk β.hom z
  refine Eq.trans (congrArg (fun y => canonicalStalkRingEquiv A' B' z
      (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map
        (squareFreeAlgebraMap A A' B B' f β).hom).hom y))
    ((canonicalStalkRingEquiv A B z).symm_apply_apply p).symm) ?_
  exact DFunLike.congr_fun (canonicalStalkRingEquiv_comp_squareFreeAlgebraMap A A' B B' f β z)
    (canonicalStalkRingEquiv A B z p)

/-! ### The two morphisms of stalk extensions attached to the square -/

include hsq in
/-- **The morphism of the stalk extensions of the two canonical presentations attached to a
commutative square.**  This is `Stacks.Sites.Conormal.stalkExtensionHomOfSquare` for the square
whose middle row is the morphism `A[B] ⟶ A'[B']` of
`Stacks.NaiveCotangentAffineStalkLegs.squareFreeAlgebraMap`. -/
abbrev canonicalStalkExtensionHomOfSquare :
    letI := algebraStalk a.hom z
    letI := algebraStalk a'.hom z
    letI := algebraStalk f.hom z
    letI := algebraStalk β.hom z
    (canonicalStalkExtension A B a z).Hom (canonicalStalkExtension A' B' a' z) :=
  stalkExtensionHomOfSquare A A' (AA A B) (AA A' B') B B'
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A
      (underlyingPresheaf (Opens.grothendieckTopology T) B))
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A'
      (underlyingPresheaf (Opens.grothendieckTopology T) B'))
    (pres A B a) (pres A' B' a') a a' f (squareFreeAlgebraMap A A' B B' f β) β z
    (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology T) A B
      (underlyingPresheaf (Opens.grothendieckTopology T) B) a (𝟙 _))
    (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology T) A' B'
      (underlyingPresheaf (Opens.grothendieckTopology T) B') a' (𝟙 _))
    (coefficientMap_comp_squareFreeAlgebraMap A A' B B' f β)
    (freeAlgebraMapOfSquare_comp_canonicalPresentation (Opens.grothendieckTopology T)
      A A' B B' a a' f β hsq)

include hsq in
/-- **The two morphisms of stalk extensions attached to the square agree.**  The square of
extensions
```
Aₓ[Bₓ] ──────▸ A'ₓ[B'ₓ]
   ▲              ▲
   │              │
(A[B])ₓ ─────▸ (A'[B'])ₓ
```
commutes: the vertical maps are the identifications
`Stacks.SheafOfModules.canonicalStalkExtensionHom` of the stalk of the canonical presentation
with the canonical presentation of the stalk, the bottom map is the stalk of the morphism of
presentations attached to the square
(`Stacks.NaiveCotangentAffineStalkLegs.canonicalStalkExtensionHomOfSquare`) and the top map is
the morphism of canonical presentations of the stalks
(`Stacks.NaiveCotangentAffineStalkLegs.generatorsSelfStalkHomOfSquare`).

This is the bridge between the square-level stalk lemmas of
`StacksFrontier.Topology.Sheaves.Modules.ConormalSequenceStalkSquareMaps`, which are stated between
the stalk extensions of presentations, and the legs of Stacks 0D0I, which land on
`Algebra.Generators.self Aₓ Bₓ`. -/
theorem canonicalStalkExtensionHom_comp_stalkExtensionHomOfSquare :
    letI := algebraStalk a.hom z
    letI := algebraStalk a'.hom z
    letI := algebraStalk f.hom z
    letI := algebraStalk β.hom z
    (canonicalStalkExtensionHom A' B' a' z).comp
        (canonicalStalkExtensionHomOfSquare A A' B B' a a' f β z hsq) =
      (generatorsSelfStalkHomOfSquare A A' B B' a a' f β z hsq).comp
        (canonicalStalkExtensionHom A B a z) := by
  let := algebraStalk a.hom z
  let := algebraStalk a'.hom z
  let := algebraStalk f.hom z
  let := algebraStalk β.hom z
  refine Algebra.Extension.Hom.ext (RingHom.ext fun p => ?_)
  exact canonicalStalkRingEquiv_squareFreeAlgebraMap A A' B B' f β z p

/-! ### The stalk of the map of complexes -/

variable (d : A ⟶ B') (hd : f ≫ a' = d)

/-- Two factorizations of a map of sheaves of modules through the same target agree on stalks. -/
private theorem stalkMap_comp_eq_of_comp_eq {O : CategoryTheory.Sheaf (Opens.grothendieckTopology T)
    RingCat.{u}} {M N P P' : _root_.SheafOfModules.{u} O} (ψ : M ⟶ N) (χ : N ⟶ P) (ψ' : M ⟶ P')
    (χ' : P' ⟶ P) (h : ψ ≫ χ = ψ' ≫ χ')
    (ω : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf z)) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
        ((PresheafOfModules.toPresheaf O.obj).map χ.val)).hom
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
        ((PresheafOfModules.toPresheaf O.obj).map ψ.val)).hom ω) =
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
        ((PresheafOfModules.toPresheaf O.obj).map χ'.val)).hom
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
        ((PresheafOfModules.toPresheaf O.obj).map ψ'.val)).hom ω) :=
  (stalkMap_comp_apply z ψ χ ω).symm.trans
    ((congrArg (fun φ : M ⟶ P =>
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
        ((PresheafOfModules.toPresheaf O.obj).map φ.val)).hom ω) h).trans
      (stalkMap_comp_apply z ψ' χ' ω))

include hsq in
/-- The degree `-1` component of the chain map of the square, with the identification of the
degree `-1` term of `NL_{B'/A'}` folded in. -/
theorem spaceNaiveCotangentComplexMapOfSquare_f_negOne_comp :
    (spaceNaiveCotangentComplexMapOfSquare A A' B B' a a' f β hsq).f (-1) ≫
        (_root_.SheafOfModules.restrictScalars.{u, u, u, u}
            (AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite.{u, u, u} β)).map
          (eqToHom (naiveCotangentComplex_X_negOne.{u, u, u, u}
            (Opens.grothendieckTopology T) A' B' a')) =
      eqToHom (naiveCotangentComplex_X_negOne.{u, u, u, u}
          (Opens.grothendieckTopology T) A B a) ≫
        naiveCotangentConormalMapOfSquare.{u, u, u, u} (Opens.grothendieckTopology T)
          A B a A' B' a' f β hsq := by
  rw [spaceNaiveCotangentComplexMapOfSquare_f_negOne, Category.assoc, Category.assoc,
    ← CategoryTheory.Functor.map_comp, eqToHom_trans, eqToHom_refl,
    CategoryTheory.Functor.map_id, Category.comp_id]

include hsq in
/-- The stalk of the degree `-1` component of the chain map of the square is the stalk of the map
of conormal sheaves, read through the identifications of the degree `-1` terms. -/
theorem stalkAddEquivOfIso_stalk_f_negOne
    (ω : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
        (-1)).val.presheaf z)) :
    stalkAddEquivOfIso z (eqToIso (naiveCotangentComplex_X_negOne.{u, u, u, u}
          (Opens.grothendieckTopology T) A' B' a'))
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
          ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf B).obj).map
            ((spaceNaiveCotangentComplexMapOfSquare A A' B B' a a' f β hsq).f
              (-1)).val)).hom ω) =
      conormalSheafMapOfSquareStalk (AA A B) (AA A' B') B B' (pres A B a) (pres A' B' a')
        (squareFreeAlgebraMap A A' B B' f β) β z
        (freeAlgebraMapOfSquare_comp_canonicalPresentation (Opens.grothendieckTopology T)
          A A' B B' a a' f β hsq)
        (stalkAddEquivOfIso z (eqToIso (naiveCotangentComplex_X_negOne.{u, u, u, u}
          (Opens.grothendieckTopology T) A B a)) ω) := by
  exact stalkMap_comp_eq_of_comp_eq z _ _ _ _
    (spaceNaiveCotangentComplexMapOfSquare_f_negOne_comp A A' B B' a a' f β hsq) ω

include hsq hd in
/-- **The degree `-1` leg of Stacks 0D0I is natural in the square.**  The stalk at `z` of the
degree `-1` component of the chain map `NL_{B/A} ⟶ NL_{B'/A'}` attached to a commutative square
(Stacks 08TX) is, read through the two legs
`Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOneLinear`, the conormal map of the morphism
`Stacks.NaiveCotangentAffineStalkLegs.generatorsSelfStalkHomOfSquare` of canonical presentations
of the stalks. -/
theorem stalkLegLinear_spaceNaiveCotangentComplexMapOfSquare_negOne
    (ω : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
        (-1)).val.presheaf z)) :
    letI := algebraStalk a.hom z
    letI := algebraStalk a'.hom z
    letI := algebraStalk f.hom z
    letI := algebraStalk β.hom z
    letI := algebraStalk d.hom z
    letI := stalkIsScalarTowerSquareBase A A' B' a' d f z hd
    stalkLegNegOneLinear A' B' a' z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) z).map
          ((spaceNaiveCotangentComplexMapOfSquare A A' B B' a a' f β hsq).f
            (-1))).hom ω) =
      Algebra.Extension.Cotangent.map
          (generatorsSelfStalkHomOfSquare A A' B B' a a' f β z hsq)
        (stalkLegNegOneLinear A B a z ω) := by
  let := algebraStalk a.hom z
  let := algebraStalk a'.hom z
  let := algebraStalk f.hom z
  let := algebraStalk β.hom z
  let := algebraStalk d.hom z
  let := stalkIsScalarTowerSquareBase A A' B' a' d f z hd
  refine Eq.trans (stalkLegNegOneLinear_apply A' B' a' z _) ?_
  refine Eq.trans (stalkLegNegOne_apply A' B' a' z _) ?_
  refine Eq.trans (congrArg (naiveCotangentStalkCotangentEquiv A' B' a' z)
    (stalkAddEquivOfIso_stalk_f_negOne A A' B B' a a' f β z hsq ω)) ?_
  refine Eq.trans (naiveCotangentStalkCotangentEquiv_apply A' B' a' z _) ?_
  refine Eq.trans (congrArg (Algebra.Extension.Cotangent.map
      (canonicalStalkExtensionHom A' B' a' z))
    (conormalSheafMapOfSquareStalk_eq_cotangentMap A A' (AA A B) (AA A' B') B B'
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A
        (underlyingPresheaf (Opens.grothendieckTopology T) B))
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A'
        (underlyingPresheaf (Opens.grothendieckTopology T) B'))
      (pres A B a) (pres A' B' a') a a' d f (squareFreeAlgebraMap A A' B B' f β) β z
      (freeAlgebraMapOfSquare_comp_canonicalPresentation (Opens.grothendieckTopology T)
        A A' B B' a a' f β hsq)
      (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology T) A B
        (underlyingPresheaf (Opens.grothendieckTopology T) B) a (𝟙 _))
      (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology T) A' B'
        (underlyingPresheaf (Opens.grothendieckTopology T) B') a' (𝟙 _))
      hd (coefficientMap_comp_squareFreeAlgebraMap A A' B B' f β) _)) ?_
  refine Eq.trans (DFunLike.congr_fun (Algebra.Extension.Cotangent.map_comp
    (f := canonicalStalkExtensionHomOfSquare A A' B B' a a' f β z hsq)
    (g := canonicalStalkExtensionHom A' B' a' z)) _).symm ?_
  refine Eq.trans (congrArg (fun h : (canonicalStalkExtension A B a z).Hom
        (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A'.obj z))
          (ToType (TopCat.Presheaf.stalk B'.obj z))).toExtension =>
      Algebra.Extension.Cotangent.map h
        (conormalSheafStalkLinearEquiv (AA A B) B (pres A B a) z
          (stalkAddEquivOfIso z (eqToIso (naiveCotangentComplex_X_negOne.{u, u, u, u}
            (Opens.grothendieckTopology T) A B a)) ω)))
    (canonicalStalkExtensionHom_comp_stalkExtensionHomOfSquare A A' B B' a a' f β z hsq)) ?_
  refine Eq.trans (DFunLike.congr_fun (Algebra.Extension.Cotangent.map_comp
    (f := canonicalStalkExtensionHom A B a z)
    (g := generatorsSelfStalkHomOfSquare A A' B B' a a' f β z hsq)) _) ?_
  refine congrArg (Algebra.Extension.Cotangent.map
    (generatorsSelfStalkHomOfSquare A A' B B' a a' f β z hsq)) ?_
  refine Eq.trans (naiveCotangentStalkCotangentEquiv_apply A B a z _).symm ?_
  exact Eq.trans (stalkLegNegOne_apply A B a z ω).symm
    (stalkLegNegOneLinear_apply A B a z ω).symm

include hsq in
/-- The degree `0` component of the chain map of the square, with the identification of the
degree `0` term of `NL_{B'/A'}` folded in. -/
theorem spaceNaiveCotangentComplexMapOfSquare_f_zero_comp :
    (spaceNaiveCotangentComplexMapOfSquare A A' B B' a a' f β hsq).f 0 ≫
        (_root_.SheafOfModules.restrictScalars.{u, u, u, u}
            (AlgebraicGeometry.SheafOfModules.underlyingRingHomOfSite.{u, u, u} β)).map
          (eqToHom (naiveCotangentComplex_X_zero.{u, u, u, u}
            (Opens.grothendieckTopology T) A' B' a')) =
      eqToHom (naiveCotangentComplex_X_zero.{u, u, u, u}
          (Opens.grothendieckTopology T) A B a) ≫
        naiveCotangentTensorMapOfSquare.{u, u, u, u} (Opens.grothendieckTopology T)
          A B a A' B' a' f β hsq := by
  rw [spaceNaiveCotangentComplexMapOfSquare_f_zero, Category.assoc, Category.assoc,
    ← CategoryTheory.Functor.map_comp, eqToHom_trans, eqToHom_refl,
    CategoryTheory.Functor.map_id, Category.comp_id]

include hsq in
/-- The stalk of the degree `0` component of the chain map of the square is the stalk of the map
of tensor-differentials sheaves, read through the identifications of the degree `0` terms. -/
theorem stalkAddEquivOfIso_stalk_f_zero
    (ω : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
        0).val.presheaf z)) :
    stalkAddEquivOfIso z (eqToIso (naiveCotangentComplex_X_zero.{u, u, u, u}
          (Opens.grothendieckTopology T) A' B' a'))
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
          ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf B).obj).map
            ((spaceNaiveCotangentComplexMapOfSquare A A' B B' a a' f β hsq).f
              0).val)).hom ω) =
      tensorSheafMapOfSquareStalk A A' (AA A B) (AA A' B') B B'
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A
          (underlyingPresheaf (Opens.grothendieckTopology T) B))
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A'
          (underlyingPresheaf (Opens.grothendieckTopology T) B'))
        (pres A B a) (pres A' B' a') f (squareFreeAlgebraMap A A' B B' f β) β z
        (freeAlgebraMapOfSquare_comp_canonicalPresentation (Opens.grothendieckTopology T)
          A A' B B' a a' f β hsq)
        (coefficientMap_comp_squareFreeAlgebraMap A A' B B' f β)
        (stalkAddEquivOfIso z (eqToIso (naiveCotangentComplex_X_zero.{u, u, u, u}
          (Opens.grothendieckTopology T) A B a)) ω) := by
  exact stalkMap_comp_eq_of_comp_eq z _ _ _ _
    (spaceNaiveCotangentComplexMapOfSquare_f_zero_comp A A' B B' a a' f β hsq) ω

include hsq hd in
/-- **The degree `0` leg of Stacks 0D0I is natural in the square.**  The stalk at `z` of the
degree `0` component of the chain map `NL_{B/A} ⟶ NL_{B'/A'}` attached to a commutative square
(Stacks 08TX) is, read through the two legs
`Stacks.NaiveCotangentAffineStalkLegs.stalkLegZeroLinear`, the cotangent-space map of the
morphism `Stacks.NaiveCotangentAffineStalkLegs.generatorsSelfStalkHomOfSquare` of canonical
presentations of the stalks. -/
theorem stalkLegLinear_spaceNaiveCotangentComplexMapOfSquare_zero
    (ω : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
        0).val.presheaf z)) :
    letI := algebraStalk a.hom z
    letI := algebraStalk a'.hom z
    letI := algebraStalk f.hom z
    letI := algebraStalk β.hom z
    letI := algebraStalk d.hom z
    letI := stalkIsScalarTowerSquareBase A A' B' a' d f z hd
    stalkLegZeroLinear A' B' a' z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) z).map
          ((spaceNaiveCotangentComplexMapOfSquare A A' B B' a a' f β hsq).f
            0)).hom ω) =
      Algebra.Extension.CotangentSpace.map
          (generatorsSelfStalkHomOfSquare A A' B B' a a' f β z hsq)
        (stalkLegZeroLinear A B a z ω) := by
  let := algebraStalk a.hom z
  let := algebraStalk a'.hom z
  let := algebraStalk f.hom z
  let := algebraStalk β.hom z
  let := algebraStalk d.hom z
  let := stalkIsScalarTowerSquareBase A A' B' a' d f z hd
  let _ : DecidableEq (OrderDual (TopologicalSpace.OpenNhds z)) := Classical.decEq _
  refine Eq.trans (stalkLegZeroLinear_apply A' B' a' z _) ?_
  refine Eq.trans (stalkLegZero_apply A' B' a' z _) ?_
  refine Eq.trans (congrArg (naiveCotangentStalkCotangentSpaceEquiv A' B' a' z)
    (stalkAddEquivOfIso_stalk_f_zero A A' B B' a a' f β z hsq ω)) ?_
  refine Eq.trans (naiveCotangentStalkCotangentSpaceEquiv_apply A' B' a' z _) ?_
  refine Eq.trans (congrArg (Algebra.Extension.CotangentSpace.map
      (canonicalStalkExtensionHom A' B' a' z))
    (tensorSheafMapOfSquareStalk_eq_cotangentSpaceMap A A' (AA A B) (AA A' B') B B'
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A
        (underlyingPresheaf (Opens.grothendieckTopology T) B))
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A'
        (underlyingPresheaf (Opens.grothendieckTopology T) B'))
      (pres A B a) (pres A' B' a') a a' d f (squareFreeAlgebraMap A A' B B' f β) β z
      (freeAlgebraMapOfSquare_comp_canonicalPresentation (Opens.grothendieckTopology T)
        A A' B B' a a' f β hsq)
      (coefficientMap_comp_squareFreeAlgebraMap A A' B B' f β)
      (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology T) A B
        (underlyingPresheaf (Opens.grothendieckTopology T) B) a (𝟙 _))
      (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology T) A' B'
        (underlyingPresheaf (Opens.grothendieckTopology T) B') a' (𝟙 _))
      hd _)) ?_
  refine Eq.trans (DFunLike.congr_fun (Algebra.Extension.CotangentSpace.map_comp
    (f := canonicalStalkExtensionHomOfSquare A A' B B' a a' f β z hsq)
    (g := canonicalStalkExtensionHom A' B' a' z)) _).symm ?_
  refine Eq.trans (congrArg (fun h : (canonicalStalkExtension A B a z).Hom
        (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A'.obj z))
          (ToType (TopCat.Presheaf.stalk B'.obj z))).toExtension =>
      Algebra.Extension.CotangentSpace.map h
        (cotangentSpaceStalkLinearEquiv A (AA A B) B
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A
            (underlyingPresheaf (Opens.grothendieckTopology T) B)) (pres A B a) z
          (stalkAddEquivOfIso z (eqToIso (naiveCotangentComplex_X_zero.{u, u, u, u}
            (Opens.grothendieckTopology T) A B a)) ω)))
    (canonicalStalkExtensionHom_comp_stalkExtensionHomOfSquare A A' B B' a a' f β z hsq)) ?_
  refine Eq.trans (DFunLike.congr_fun (Algebra.Extension.CotangentSpace.map_comp
    (f := canonicalStalkExtensionHom A B a z)
    (g := generatorsSelfStalkHomOfSquare A A' B B' a a' f β z hsq)) _) ?_
  refine congrArg (Algebra.Extension.CotangentSpace.map
    (generatorsSelfStalkHomOfSquare A A' B B' a a' f β z hsq)) ?_
  refine Eq.trans (naiveCotangentStalkCotangentSpaceEquiv_apply A B a z _).symm ?_
  exact Eq.trans (stalkLegZero_apply A B a z ω).symm
    (stalkLegZeroLinear_apply A B a z ω).symm

end Square

end Stacks.NaiveCotangentAffineStalkLegs

end

end
