module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IdealSheafPowers
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModule
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# The conormal algebra of an immersion of algebraic spaces

Let `i : Z ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, and let `𝓘 = Ker(𝒪_X ⟶ i_*𝒪_Z)` be its kernel ideal sheaf on the small étale site of
`X`.  For a closed immersion this is the ideal sheaf of `Z` in `X` of Stacks 03MB.  The
**conormal algebra** `𝒞_{Z/X,*}` of `i` is the inverse image along `i` of the sheaf of graded
`𝒪_X`-algebras `⨁_{n ≥ 0} 𝓘ⁿ`: a sheaf of graded `𝒪_Z`-algebras whose degree-`n` piece is
`i^*(𝓘ⁿ)` and whose degree-one piece is the conormal module `𝒞_{Z/X}` of Stacks 04CN.

## Main definitions

* `AlgebraicGeometry.Space.kernelIdealSheafZPow`: the integer-indexed family of powers of the
  kernel ideal sheaf of a morphism of algebraic spaces.
* `AlgebraicGeometry.Space.conormalAlgebra`: **Stacks 09RN** for a closed immersion, the
  conormal algebra `𝒞_{Z/X,*}`.
* `AlgebraicGeometry.Space.boundaryComplementLift` and
  `AlgebraicGeometry.Space.immersionClosedFactorization`: the closed factorisation of an
  immersion through the complement of its boundary, as a canonical morphism.
* `AlgebraicGeometry.Space.conormalAlgebraOfImmersion`: **Stacks 09RN**, the conormal algebra
  of an immersion, taken through that closed factorisation.
* `AlgebraicGeometry.Space.immersionRangeSubspace`: the image of that closed factorisation, as
  a closed subspace of the complement of the boundary, and
  `AlgebraicGeometry.Space.conormalModuleOfImmersionRange`, the conormal module of Stacks 04CN
  of that closed subspace, which lives on the range rather than on `Z`.
* `AlgebraicGeometry.Space.conormalModuleOfImmersion`: **Stacks 04CN for an immersion**, the
  conormal module `𝒞_{Z/X}` of an immersion as an `𝒪_Z`-module on `Z` itself.

## Main results

* `AlgebraicGeometry.Space.structureRingSheaf_mul_comm`: the sections of the structure sheaf of
  an algebraic space commute, which is what makes the graded algebra of the powers of a sheaf
  of ideals available on the small étale site.
* `AlgebraicGeometry.Space.conormalAlgebra_piece`: the degree-`n` piece is `i^*(𝓘ⁿ)`.
* `AlgebraicGeometry.Space.conormalAlgebra_piece_one`: the degree-one piece is `i^*𝓘`, which
  for the inclusion of a closed subspace is the conormal module
  `AlgebraicGeometry.Space.conormalModule` of Stacks 04CN.
* `AlgebraicGeometry.Space.conormalAlgebra_piece_neg`: in negative degrees the pieces are the
  inverse image of the zero sheaf of ideals, so the algebra is concentrated in nonnegative
  degrees.
* `AlgebraicGeometry.Space.isClosedImmersion_boundaryComplementLift` and
  `AlgebraicGeometry.Space.boundaryComplementLift_comp_ι`: the canonical factorisation of an
  immersion through the complement of its boundary is a closed immersion composing back to the
  immersion, which is Stacks 04CE for that canonical factorisation.
* `AlgebraicGeometry.Space.kernelIdealSheaf_immersionClosedFactorization`: the kernel ideal
  sheaf of the closed factorisation of an immersion is the defining ideal sheaf of Stacks 03MB
  of the image of that factorisation, which is Stacks 082Z applied to it.
* `AlgebraicGeometry.Space.conormalModuleOfImmersion_eq_conormalAlgebraOfImmersion_piece_one`:
  the conormal module of an immersion is the degree-one piece of its conormal algebra, which
  is the agreement of Stacks 04CN with Stacks 09RN in the immersion case.

## Implementation notes

Stacks 76.6 describes the degree-`n` piece as `𝓘ⁿ/𝓘ⁿ⁺¹`, an `𝒪_X/𝓘`-module, and takes the
`𝒪_Z`-module corresponding to it under the equivalence of Stacks 04CJ.  That `𝒪_Z`-module is
`i^*(𝓘ⁿ)`, because `i_*i^*(𝓘ⁿ) = 𝓘ⁿ ⊗_{𝒪_X} 𝒪_X/𝓘 = 𝓘ⁿ/𝓘ⁿ⁺¹`; the identification is standard
and is **not** formalized here, exactly as in the degree-one case
`AlgebraicGeometry.Space.conormalModule`, whose module documentation records why `i^*𝓘` is the
module the source describes and that the identification with `𝓘/𝓘²` is deferred.  The same
convention is the one the scheme-level `Stacks.Conormal.conormalGradedAlgebra` follows: there
too the conormal algebra is the pullback along the closed factorization of the graded algebra
of the powers of the ideal sheaf.

For an immersion the ambient space is replaced by the complement `X ∖ ∂Z` of the boundary of
the image, through which the immersion factors as a closed immersion by Stacks 04CE.  That
factorisation is `AlgebraicGeometry.Space.exists_isClosedImmersion_comp_ι_boundaryComplement`
in existence form only; the morphism itself is recovered without any choice, because the
containment of subfunctors `AlgebraicGeometry.Space.range_le_boundaryComplement` that the
existence statement yields is a proposition, and a morphism whose range lies in a subfunctor
factors through it by `CategoryTheory.Subfunctor.lift`.  Closedness of that canonical
factorisation then follows because the inclusion of an open subspace is a monomorphism, so the
factorisation agrees with the one the existence statement produces.

The graded algebra of the powers of the ideal sheaf is
`SheafOfModules.reesGradedAlgebra`, which needs the sections of the structure sheaf to commute;
on the small étale site they do, because the structure sheaf is a sheaf of commutative rings
with commutativity forgotten, which is
`AlgebraicGeometry.Space.structureRingSheaf_mul_comm`.  Its inverse image is
`Stacks.Sheaves.GradedAlgebraPullback.toposPullbackGradedAlgebra` at the morphism of small
étale ringed topoi of Stacks 03G8, whose homogeneous pieces are the module pullbacks of the
original ones on the nose, so `conormalAlgebra_piece` is a definitional equality.

**Why the conormal module of an immersion is not `conormalModule` applied to a subspace.**
`AlgebraicGeometry.Space.conormalModule` of Stacks 04CN takes a closed subspace and returns a
module on that subspace's own functor, whereas Stacks 04CN asks for an `𝒪_Z`-module on `Z`.
The closed factorisation of an immersion is a morphism out of `Z`, and its image
`AlgebraicGeometry.Space.immersionRangeSubspace` is only *isomorphic* to `Z`, so the module on
`Z` has to be an inverse image along
`AlgebraicGeometry.Space.immersionClosedFactorization`.  That is
`AlgebraicGeometry.Space.conormalModuleOfImmersion`, and the module on the range is
`AlgebraicGeometry.Space.conormalModuleOfImmersionRange`.

Because the factorisation and the inclusion of its image are two different morphisms — with
isomorphic but not equal sources — `AlgebraicGeometry.Space.kernelIdealSheaf_eq_definingIdealSheaf`
does not identify their ideal sheaves, and no invariance of
`AlgebraicGeometry.Space.kernelIdealSheaf` under an isomorphism of the source is available in
this development.  `AlgebraicGeometry.Space.kernelIdealSheaf_immersionClosedFactorization`
goes through the scheme-theoretic image instead: a closed immersion is quasi-compact by
Stacks 04CG, so Stacks 082Z identifies the kernel ideal sheaf of the factorisation with the
defining ideal sheaf of its scheme-theoretic image, and that image is the range because the
range is a closed subspace containing the image and the scheme-theoretic image is the least
such.  This is what makes the agreement with the conormal algebra provable.

## What is not proved

* **Quasi-coherence of the pieces is not established.**  The powers of the ideal sheaf are
  quasi-coherent only after a finiteness input, and the inverse image of a quasi-coherent
  module along a morphism of ringed topoi is known to preserve quasi-coherence only by
  Stacks 03DO, part (6), which no statement in this development carries; the same gap is
  recorded for the degree-one case in the module documentation of
  `StacksFrontier.AlgebraicGeometry.Spaces.ConormalModule`.
* **The identification of the direct image of the degree-`n` piece with `𝓘ⁿ/𝓘ⁿ⁺¹`** is not
  proved, for the reason given in the implementation notes.
* **The étale-restriction clause of Stacks 04CO is not transferred to the immersion case.**
  For a closed subspace it is `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso`,
  stated for the inverse image `CategoryTheory.Subfunctor.preimage` of the subspace along an
  étale morphism.  Carrying it to `AlgebraicGeometry.Space.conormalModuleOfImmersion` needs
  the ambient space to commute with étale base change, that is
  `(X ∖ ∂Z) ×_X U = U ∖ ∂(Z ×_X U)` as subfunctors of `U`, and three inputs for it are
  missing: that the point set of the base-changed immersion is the preimage of the point set
  of `i`; that `closure` commutes with the preimage along the map on points of an étale
  morphism, which needs that map to be open — available as
  `AlgebraicGeometry.Space.isOpenMap_pointsMap_of_isEtale` — together with the topological
  statement, which is not in this development; and that the reduced induced structure of
  Stacks 06EC on a preimage point set is the inverse image of the reduced induced structure.
  What is available is the comparison of the range of a base change with the preimage of the
  range, `CategoryTheory.Subfunctor.range_snd_eq_preimage_range_of_isPullback`.

## References

* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04CG](https://stacks.math.columbia.edu/tag/04CG)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.GradedAlgebraPullback (toposPullbackGradedAlgebra)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The sections of the structure sheaf of an algebraic space commute.**  The structure sheaf
of the small étale ringed site is a sheaf of commutative rings; the `RingCat`-valued sheaf over
which its modules are indexed is that sheaf with commutativity forgotten. -/
theorem structureRingSheaf_mul_comm (X : AlgebraicSpaces B S hS)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a b : ToType ((structureRingSheaf B S hS X).obj.obj U)) : a * b = b * a :=
  mul_comm (G := ToType ((structureSheaf B S hS X.1 X.2).obj.obj U)) a b

variable {X Y Z : AlgebraicSpaces B S hS}

/-- The integer-indexed family of powers of the kernel ideal sheaf of a morphism of algebraic
spaces: `𝓘ⁿ` in degree `n ≥ 0` and the zero sheaf of ideals in negative degrees. -/
noncomputable def kernelIdealSheafZPow (f : X ⟶ Y) (n : ℤ) :
    (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule :=
  SheafOfModules.idealSheafZPow (kernelIdealSheaf B S hS f) n

/-- The first power of the kernel ideal sheaf is the kernel ideal sheaf. -/
theorem kernelIdealSheafZPow_one (f : X ⟶ Y) :
    kernelIdealSheafZPow B S hS f 1 = kernelIdealSheaf B S hS f :=
  SheafOfModules.idealSheafZPow_one _

/-- In negative degrees the family of powers of the kernel ideal sheaf is the zero sheaf of
ideals. -/
theorem kernelIdealSheafZPow_of_neg (f : X ⟶ Y) {n : ℤ} (hn : n < 0) :
    kernelIdealSheafZPow B S hS f n = SheafOfModules.zeroIdealSheaf :=
  SheafOfModules.idealSheafZPow_of_neg _ hn

/-- The sheaf of graded `𝒪_Y`-algebras `⨁_{n ≥ 0} 𝓘ⁿ` of the kernel ideal sheaf of a morphism
of algebraic spaces. -/
noncomputable def kernelIdealGradedAlgebra (f : X ⟶ Y) :
    SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS Y) :=
  SheafOfModules.reesGradedAlgebra (kernelIdealSheaf B S hS f)
    (structureRingSheaf_mul_comm B S hS Y)

/-- The degree-`n` piece of `⨁_{n ≥ 0} 𝓘ⁿ` is `𝓘ⁿ`, and the zero sheaf of ideals for `n < 0`. -/
theorem kernelIdealGradedAlgebra_piece (f : X ⟶ Y) (n : ℤ) :
    (kernelIdealGradedAlgebra B S hS f).piece n =
      (kernelIdealSheafZPow B S hS f n).toSheafOfModules :=
  rfl

/-- **Stacks Project, Tag 09RN.**  The conormal algebra `𝒞_{Z/X,*}` of a closed immersion
`i : Z ⟶ X` of algebraic spaces: the inverse image along `i` of the sheaf of graded
`𝒪_X`-algebras `⨁_{n ≥ 0} 𝓘ⁿ`, for `𝓘` the ideal sheaf of `i`.

Its degree-`n` piece is `i^*(𝓘ⁿ)`, which is the `𝒪_Z`-module the source describes as
`𝓘ⁿ/𝓘ⁿ⁺¹`; the module documentation records why, and that the identification is deferred, as
it is in the degree-one case `AlgebraicGeometry.Space.conormalModule`. -/
@[stacks 09RN "the conormal algebra of a closed immersion"]
noncomputable def conormalAlgebra (i : Z ⟶ X) :
    SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS Z) :=
  toposPullbackGradedAlgebra (X := smallEtaleRingedTopos B S hS Z)
    (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposModulesHom B S hS i)
    (kernelIdealGradedAlgebra B S hS i)

/-- **The degree-`n` piece of the conormal algebra is `i^*(𝓘ⁿ)`.** -/
theorem conormalAlgebra_piece (i : Z ⟶ X) (n : ℤ) :
    (conormalAlgebra B S hS i).piece n =
      (modulePullback B S hS i).obj (kernelIdealSheafZPow B S hS i n).toSheafOfModules :=
  rfl

/-- **The degree-one piece of the conormal algebra is `i^*𝓘`**, the conormal module of
Stacks 04CN. -/
theorem conormalAlgebra_piece_one (i : Z ⟶ X) :
    (conormalAlgebra B S hS i).piece 1 =
      (modulePullback B S hS i).obj (kernelIdealSheaf B S hS i).toSheafOfModules := by
  rw [conormalAlgebra_piece, kernelIdealSheafZPow_one]

/-- **In negative degrees the conormal algebra is the inverse image of the zero sheaf of
ideals**, so it is concentrated in nonnegative degrees. -/
theorem conormalAlgebra_piece_neg (i : Z ⟶ X) {n : ℤ} (hn : n < 0) :
    (conormalAlgebra B S hS i).piece n =
      (modulePullback B S hS i).obj
        (SheafOfModules.zeroIdealSheaf
          (R := structureRingSheaf B S hS X)).toSheafOfModules := by
  rw [conormalAlgebra_piece, kernelIdealSheafZPow_of_neg B S hS i hn]

/-- **The degree-one piece of the conormal algebra of the inclusion of a closed subspace is the
conormal module of Stacks 04CN.** -/
theorem conormalAlgebra_piece_one_eq_conormalModule (X : AlgebraicSpaces B S hS)
    (W : ClosedSubspaces B S hS X.1) :
    (conormalAlgebra B S hS (subspaceInclusion B S hS X W)).piece 1 =
      conormalModule B S hS X W := by
  rw [conormalAlgebra_piece_one, conormalModule_eq]
  rfl

/-! ### The conormal algebra of an immersion -/

section Immersion

attribute [local instance] pointTopology

variable {Z₀ X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The image of an immersion lies in the complement of its boundary.**  This is the
factorisation of Stacks 04CE, read as a containment of subfunctors. -/
theorem range_le_boundaryComplement (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    Subfunctor.range i ≤
      boundaryComplement B S hS X₀ (Set.range (pointsMap B S hS Z₀ i)) := by
  obtain ⟨g, _, hg⟩ :=
    exists_isClosedImmersion_comp_ι_boundaryComplement B S hS hX hZ i hi
  conv_lhs => rw [← hg]
  exact (Subfunctor.range_comp_le _ _).trans_eq (Subfunctor.range_ι _)

/-- **The closed factorisation of an immersion**, as a morphism: the immersion read as a
morphism into the complement of its boundary.  This is the unique factorisation of Stacks 04CE
through that open subspace. -/
noncomputable def boundaryComplementLift (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    Z₀ ⟶ (boundaryComplement B S hS X₀ (Set.range (pointsMap B S hS Z₀ i))).toFunctor :=
  Subfunctor.lift i (range_le_boundaryComplement B S hS hX hZ i hi)

/-- The closed factorisation of an immersion composes with the inclusion of the complement of
the boundary to the immersion. -/
theorem boundaryComplementLift_comp_ι (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    boundaryComplementLift B S hS hX hZ i hi ≫
        (boundaryComplement B S hS X₀ (Set.range (pointsMap B S hS Z₀ i))).ι = i :=
  Subfunctor.lift_ι _ _

/-- **Stacks 04CE for the canonical factorisation.**  The factorisation of an immersion through
the complement of its boundary is a closed immersion. -/
theorem isClosedImmersion_boundaryComplementLift (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    IsClosedImmersion B S hS (boundaryComplementLift B S hS hX hZ i hi) := by
  obtain ⟨g, hgc, hg⟩ :=
    exists_isClosedImmersion_comp_ι_boundaryComplement B S hS hX hZ i hi
  have hgeq : g = boundaryComplementLift B S hS hX hZ i hi :=
    (cancel_mono (boundaryComplement B S hS X₀
      (Set.range (pointsMap B S hS Z₀ i))).ι).mp
      (by rw [hg, boundaryComplementLift_comp_ι])
  rwa [hgeq] at hgc

/-- The complement of the boundary of an immersion, as an algebraic space: the ambient space in
which an immersion is a closed immersion. -/
noncomputable def immersionAmbient (hX : IsAlgebraicSpace B S hS X₀)
    (_hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    AlgebraicSpaces B S hS :=
  ⟨(boundaryComplement B S hS X₀ (Set.range (pointsMap B S hS Z₀ i))).toFunctor,
    (isOpenSubspace_boundaryComplement B S hS hX
      (isLocallyClosed_range_pointsMap_of_isImmersion B S hS hX i hi)).1⟩

/-- The closed factorisation of an immersion, as a morphism of algebraic spaces. -/
noncomputable def immersionClosedFactorization (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶ immersionAmbient B S hS hX hZ i hi :=
  ObjectProperty.homMk (boundaryComplementLift B S hS hX hZ i hi)

/-- **Stacks Project, Tag 09RN.**  The conormal algebra `𝒞_{Z/X,*}` of an immersion
`i : Z ⟶ X` of algebraic spaces: the conormal algebra of the closed immersion of `Z` into the
complement `X ∖ ∂Z` of the boundary of its image, through which `i` factors by Stacks 04CE.

Its degree-`n` piece is the inverse image along that closed immersion of the `n`-th power of
the ideal sheaf of `Z` in `X ∖ ∂Z`, which is the `𝒪_Z`-module the source describes as
`𝓘ⁿ/𝓘ⁿ⁺¹`. -/
@[stacks 09RN "the conormal algebra of an immersion"]
noncomputable def conormalAlgebraOfImmersion (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    SheafOfModules.GradedAlgebra.{u, u}
      (structureRingSheaf B S hS (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS)) :=
  conormalAlgebra B S hS (immersionClosedFactorization B S hS hX hZ i hi)

/-- The conormal algebra of an immersion is the conormal algebra of its closed factorisation. -/
theorem conormalAlgebraOfImmersion_eq (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    conormalAlgebraOfImmersion B S hS hX hZ i hi =
      conormalAlgebra B S hS (immersionClosedFactorization B S hS hX hZ i hi) :=
  rfl

/-- **The degree-`n` piece of the conormal algebra of an immersion** is the inverse image along
the closed factorisation of the `n`-th power of the ideal sheaf of that factorisation. -/
theorem conormalAlgebraOfImmersion_piece (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) (n : ℤ) :
    (conormalAlgebraOfImmersion B S hS hX hZ i hi).piece n =
      (modulePullback B S hS (immersionClosedFactorization B S hS hX hZ i hi)).obj
        (kernelIdealSheafZPow B S hS
          (immersionClosedFactorization B S hS hX hZ i hi) n).toSheafOfModules :=
  rfl

/-! #### The conormal module of an immersion -/

/-- **The image of the closed factorisation of an immersion, as a closed subspace of the
complement of the boundary.**  It is isomorphic to `Z`, but is *not* `Z`. -/
noncomputable abbrev immersionRangeSubspace (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    ClosedSubspaces B S hS (immersionAmbient B S hS hX hZ i hi).1 :=
  ⟨Subfunctor.range (boundaryComplementLift B S hS hX hZ i hi),
    isClosedSubspace_range_of_isClosedImmersion B S hS
      (boundaryComplementLift B S hS hX hZ i hi) hZ
      (isClosedImmersion_boundaryComplementLift B S hS hX hZ i hi)⟩

/-- **The conormal module of the closed immersion underlying an immersion**, living on the
range of the closed factorisation inside `X ∖ ∂Z`.

This is `AlgebraicGeometry.Space.conormalModule` of Stacks 04CN reused verbatim, for the
closed subspace `AlgebraicGeometry.Space.immersionRangeSubspace`.  It carries no `@[stacks]`
attribute: the module of Stacks 04CN for the immersion `i` is an `𝒪_Z`-module on `Z`, whereas
this one is a module on the range, and the two are only isomorphic.  The `𝒪_Z`-module the
source asks for is `AlgebraicGeometry.Space.conormalModuleOfImmersion` below. -/
noncomputable def conormalModuleOfImmersionRange (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    Modules.{u, u} B S hS (immersionRangeSubspace B S hS hX hZ i hi).1.toFunctor
      (immersionRangeSubspace B S hS hX hZ i hi).2.1 :=
  conormalModule B S hS (immersionAmbient B S hS hX hZ i hi)
    (immersionRangeSubspace B S hS hX hZ i hi)

/-- **The kernel ideal sheaf of the closed factorisation of an immersion is the defining ideal
sheaf of its range.**  Both are sheaves of ideals of `𝒪_{X ∖ ∂Z}`; the first is the kernel of
the structure map of the factorisation, which is a morphism out of `Z`, and the second is the
ideal sheaf of Stacks 03MB of the range, which is a morphism out of a subfunctor of `X ∖ ∂Z`. -/
theorem kernelIdealSheaf_immersionClosedFactorization (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    kernelIdealSheaf B S hS (immersionClosedFactorization B S hS hX hZ i hi) =
      definingIdealSheaf B S hS (immersionAmbient B S hS hX hZ i hi)
        (immersionRangeSubspace B S hS hX hZ i hi) := by
  have himg : schemeTheoreticImage B S hS
        (immersionClosedFactorization B S hS hX hZ i hi).hom
        (immersionAmbient B S hS hX hZ i hi).2 =
      immersionRangeSubspace B S hS hX hZ i hi :=
    Subtype.ext (le_antisymm
      (schemeTheoreticImageSubfunctor_le B S hS
        (immersionClosedFactorization B S hS hX hZ i hi).hom
        (immersionRangeSubspace B S hS hX hZ i hi).2 le_rfl)
      (range_le_schemeTheoreticImageSubfunctor B S hS _))
  rw [← himg]
  exact (definingIdealSheaf_schemeTheoreticImage_eq_kernelIdealSheaf B S hS
    (immersionClosedFactorization B S hS hX hZ i hi)
    (isQuasiCompact_of_isClosedImmersion' B S hS
      (isClosedImmersion_boundaryComplementLift B S hS hX hZ i hi))).symm

/-- **Stacks 04CN for an immersion.**  The conormal module `𝒞_{Z/X}` of an immersion
`i : Z ⟶ X` of algebraic spaces: the inverse image along the closed factorisation
`Z ⟶ X ∖ ∂Z` of the defining ideal sheaf of the image of that factorisation.

Stacks 76.5 defines the conormal sheaf of an immersion to be the conormal sheaf of the closed
immersion `i : Z ⟶ X ∖ ∂Z` of Stacks 04CE, which is what this is.  Unlike
`AlgebraicGeometry.Space.conormalModule`, which returns a module on the closed subspace's own
functor, this is a module on `Z` itself, as the source asks; the two are related by
`AlgebraicGeometry.Space.conormalModuleOfImmersion_eq_conormalAlgebraOfImmersion_piece_one`
below, which identifies this module with the degree-one piece of the conormal algebra
`AlgebraicGeometry.Space.conormalAlgebraOfImmersion`.

The source describes the module as `𝓘/𝓘²`, which is `i_*i^*𝓘`; the module documentation of
`StacksFrontier.AlgebraicGeometry.Spaces.ConormalModule` records why `i^*𝓘` is that module
and that the identification is not formalized, and the "What is not proved" section of this
file records that quasi-coherence is not established either. -/
@[stacks 04CN "construction as the pullback of the ideal sheaf, via the closed factorisation"]
noncomputable def conormalModuleOfImmersion (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    Modules.{u, u} B S hS Z₀ hZ :=
  (modulePullback B S hS (immersionClosedFactorization B S hS hX hZ i hi)).obj
    (definingIdealSheaf B S hS (immersionAmbient B S hS hX hZ i hi)
      (immersionRangeSubspace B S hS hX hZ i hi)).toSheafOfModules

/-- The conormal module of an immersion is the inverse image along its closed factorisation of
the defining ideal sheaf of the image of that factorisation. -/
theorem conormalModuleOfImmersion_eq (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    conormalModuleOfImmersion B S hS hX hZ i hi =
      (modulePullback B S hS (immersionClosedFactorization B S hS hX hZ i hi)).obj
        (definingIdealSheaf B S hS (immersionAmbient B S hS hX hZ i hi)
          (immersionRangeSubspace B S hS hX hZ i hi)).toSheafOfModules :=
  rfl

/-- **The conormal module of an immersion is the degree-one piece of its conormal algebra.**
This is the agreement of Stacks 04CN with Stacks 09RN in the immersion case. -/
theorem conormalModuleOfImmersion_eq_conormalAlgebraOfImmersion_piece_one
    (hX : IsAlgebraicSpace B S hS X₀) (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀)
    (hi : IsImmersion B S hS i) :
    conormalModuleOfImmersion B S hS hX hZ i hi =
      (conormalAlgebraOfImmersion B S hS hX hZ i hi).piece 1 := by
  rw [conormalAlgebraOfImmersion_piece, kernelIdealSheafZPow_one,
    kernelIdealSheaf_immersionClosedFactorization]
  rfl

end Immersion

end AlgebraicGeometry.Space

end
