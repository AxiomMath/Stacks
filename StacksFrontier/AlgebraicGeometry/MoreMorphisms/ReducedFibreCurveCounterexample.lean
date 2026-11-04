module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreCurveSeparable
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreCurveCounterexample.Failure
public import StacksFrontier.FieldTheory.Separable.PerfectField

/-!
# Tags 0BRQ and 0BRS are false as stated

The reduced fibre theorem over a curve, Tag 0BRQ, and its variant with separable extensions, Tag
0BRS, are stated in the source for an arbitrary base `S`, Nagata, integral, regular of dimension
one, and a flat morphism `f : X ⟶ S` of finite type. Both are false without quasi-compactness of
`S` (or of `X`); the source's proof begins with a finite affine open covering of `S`.

The counterexample, over any field `k` (of characteristic zero for Tag 0BRS): `S` is the affine
line with infinitely many origins, countably many copies of `Spec k[t]` glued along
`Spec k[t, t⁻¹]`, and `X` is glued from countably many copies of the plane `Spec k[x, y]` along the
torus `Spec k[x, t, (xt)⁻¹]`, the `n`-th copy lying over the `n`-th copy of the line by
`t = x ^ (n + 1) y`. Then `S` is integral, Nagata and regular of dimension one, and `f` is flat,
affine and of finite type; over the `n`-th origin the fibre of `X` contains the line `x = 0`
with multiplicity `n + 1`. For a finite extension `L` of the function field `K = k(t)`, at a point
of the normalization `T` of `S` in `Spec L` over the `[L : K]`-th origin the ramification index is
at most `[L : K]`, and smoothness of the normalized base change at a generic point of the fibre
over it would force it to be at least `[L : K] + 1`.

The statements below are the source's statements, with exactly the source's hypotheses, in the
formal vocabulary of the corrected theorems
`exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_of_isRegular` and
`exists_finiteSeparableExtension_smoothAt_genericPoints_fiber_normalization_of_isRegular`, which
carry the additional hypothesis `[CompactSpace X]`; they are negated at every universe.

## Main results

* `not_forall_exists_finiteExtension_smoothAt_genericPoints_fiber_normalization`:
  Tag 0BRQ as stated in the source is false.
* `not_forall_exists_finiteSeparableExtension_smoothAt_genericPoints_fiber_normalization`:
  Tag 0BRS as stated in the source is false.

## References

* [Stacks Project, Tag 0BRQ](https://stacks.math.columbia.edu/tag/0BRQ)
* [Stacks Project, Tag 0BRS](https://stacks.math.columbia.edu/tag/0BRS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace ReducedFibreCurveCounterexample

variable (k : Type u) [Field k]

/-- In characteristic zero, every residue field of the line with infinitely many origins has
characteristic zero. -/
theorem charZero_residueField_base [CharZero k] (s : base k) :
    CharZero ((base k).residueField s) := by
  obtain ⟨n, y, rfl⟩ := baseι_jointly_surjective k s
  let φ : k →+* (base k).residueField (baseι k n y) :=
    ((base k).evaluation (baseChart k n) _ (mem_baseChart k n y)).hom.comp
      ((chartSectionEquiv (baseι k n)).toRingHom.comp (algebraMap k (Polynomial k)))
  exact charZero_of_injective_ringHom φ.injective

/-- In characteristic zero, the counterexample satisfies the separability hypothesis of Tag 0BRS:
the residue fields of the base are perfect. -/
theorem isSeparableExtension_residueField_totalMap [CharZero k] (x : total k) :
    letI : Algebra ((base k).residueField (totalMap k x)) ((total k).residueField x) :=
      ((totalMap k).residueFieldMap x).hom.toAlgebra
    Algebra.IsSeparableExtension ((base k).residueField (totalMap k x))
      ((total k).residueField x) := by
  let : Algebra ((base k).residueField (totalMap k x)) ((total k).residueField x) :=
    ((totalMap k).residueFieldMap x).hom.toAlgebra
  have := charZero_residueField_base k (totalMap k x)
  exact Algebra.isSeparableExtension_of_perfectField _ _

/-- The ring `ULift ℚ` has characteristic zero. -/
instance : CharZero (ULift.{u} ℚ) :=
  charZero_of_injective_ringHom (f := (ULift.ringEquiv.{0, u} (R := ℚ)).symm.toRingHom)
    (ULift.ringEquiv.{0, u} (R := ℚ)).symm.injective

end ReducedFibreCurveCounterexample

open ReducedFibreCurveCounterexample in
/-- **Stacks Project, Tag 0BRQ, as stated in the source, is false.** The statement of Tag 0BRQ,
with exactly the source's hypotheses — `f : X ⟶ S` flat and of finite type, `S` Nagata, integral
and regular of dimension one — and in the formal vocabulary of the corrected theorem
`AlgebraicGeometry.exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_of_isRegular`
(which assumes in addition that `X` is quasi-compact), does not hold, in any universe.

The counterexample is the line with infinitely many origins over `ℚ`
(`AlgebraicGeometry.ReducedFibreCurveCounterexample.base`), with the total space
`AlgebraicGeometry.ReducedFibreCurveCounterexample.total` glued from planes, the `n`-th lying over
the `n`-th copy of the line by `t = x ^ (n + 1) y`; for every finite extension `L` of the function
field the normalized base change fails to be smooth at a generic point of the fibre over a point
above the `[L : K]`-th origin
(`AlgebraicGeometry.ReducedFibreCurveCounterexample.exists_not_smoothAt`). -/
theorem not_forall_exists_finiteExtension_smoothAt_genericPoints_fiber_normalization :
    ¬ ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsIntegral S], IsNagataScheme S → IsRegular S → topologicalKrullDim S = 1 →
      ∃ (L : Type u) (_ : Field L) (_ : Algebra S.functionField L)
        (_ : FiniteDimensional S.functionField L),
        ∃ hW : ∀ V : (pullback f (S.genericExtensionHom L).fromNormalization : Scheme.{u}).Opens,
          IsCompact (V : Set (pullback f (S.genericExtensionHom L).fromNormalization :
            Scheme.{u})) → (irreducibleComponents V).Finite,
        ∀ b : (S.genericExtensionHom L).normalization,
        ∀ y : (Scheme.normalization _ hW ≫
          pullback.snd f (S.genericExtensionHom L).fromNormalization).fiber b,
        y ∈ genericPoints ↥((Scheme.normalization _ hW ≫
          pullback.snd f (S.genericExtensionHom L).fromNormalization).fiber b) →
        InfinitesimalLifting.SmoothAt (Scheme.normalization _ hW ≫
            pullback.snd f (S.genericExtensionHom L).fromNormalization)
          ((Scheme.normalization _ hW ≫
            pullback.snd f (S.genericExtensionHom L).fromNormalization).fiberι b y) := by
  intro H
  obtain ⟨L, _, _, _, hW, hsm⟩ := H (totalMap (ULift.{u} ℚ)) (isNagataScheme_base _)
    (isRegular_base _) (topologicalKrullDim_base _)
  obtain ⟨b, y, hy, hns⟩ := exists_not_smoothAt (ULift.{u} ℚ) L hW
  exact hns (hsm b y hy)

open ReducedFibreCurveCounterexample in
/-- **Stacks Project, Tag 0BRS, as stated in the source, is false.** The statement of Tag 0BRS,
with exactly the source's hypotheses — `f : X ⟶ S` flat and of finite type, `S` Nagata, integral
and regular of dimension one, `κ(η) / K` separable at every generic point `η` of `X` — and in the
formal vocabulary of the corrected theorem
`exists_finiteSeparableExtension_smoothAt_genericPoints_fiber_normalization_of_isRegular` (which
assumes in addition that `X` is quasi-compact), does not hold, in any universe.

The counterexample is that of Tag 0BRQ
(`AlgebraicGeometry.not_forall_exists_finiteExtension_smoothAt_genericPoints_fiber_normalization`),
over `ℚ`: in characteristic zero every residue field extension is separable, and the conclusion of
Tag 0BRS contains that of Tag 0BRQ. -/
theorem not_forall_exists_finiteSeparableExtension_smoothAt_genericPoints_fiber_normalization :
    ¬ ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsIntegral S], IsNagataScheme S → IsRegular S → topologicalKrullDim S = 1 →
      (∀ x : X, x ∈ genericPoints X →
        letI : Algebra (S.residueField (f.base x)) (X.residueField x) :=
          (f.residueFieldMap x).hom.toAlgebra
        Algebra.IsSeparableExtension (S.residueField (f.base x)) (X.residueField x)) →
      ∃ (L : Type u) (_ : Field L) (_ : Algebra S.functionField L)
        (_ : FiniteDimensional S.functionField L) (_ : Algebra.IsSeparable S.functionField L),
        ∃ hW : ∀ V : (pullback f (S.genericExtensionHom L).fromNormalization : Scheme.{u}).Opens,
          IsCompact (V : Set (pullback f (S.genericExtensionHom L).fromNormalization :
            Scheme.{u})) → (irreducibleComponents V).Finite,
        ∀ b : (S.genericExtensionHom L).normalization,
        ∀ y : (Scheme.normalization _ hW ≫
          pullback.snd f (S.genericExtensionHom L).fromNormalization).fiber b,
        y ∈ genericPoints ↥((Scheme.normalization _ hW ≫
          pullback.snd f (S.genericExtensionHom L).fromNormalization).fiber b) →
        InfinitesimalLifting.SmoothAt (Scheme.normalization _ hW ≫
            pullback.snd f (S.genericExtensionHom L).fromNormalization)
          ((Scheme.normalization _ hW ≫
            pullback.snd f (S.genericExtensionHom L).fromNormalization).fiberι b y) := by
  intro H
  obtain ⟨L, _, _, _, _, hW, hsm⟩ := H (totalMap (ULift.{u} ℚ)) (isNagataScheme_base _)
    (isRegular_base _) (topologicalKrullDim_base _)
    (fun x _ ↦ isSeparableExtension_residueField_totalMap _ x)
  obtain ⟨b, y, hy, hns⟩ := exists_not_smoothAt (ULift.{u} ℚ) L hW
  exact hns (hsm b y hy)

end AlgebraicGeometry
