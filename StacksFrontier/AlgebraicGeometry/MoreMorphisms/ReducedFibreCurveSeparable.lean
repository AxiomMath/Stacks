module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreCurve
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreSeparableTheorem
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import StacksFrontier.FieldTheory.Separable.Transport

/-!
# The reduced fibre theorem over a curve, with a separable extension

Let `f : X ⟶ S` be flat and of finite type with `X` quasi-compact, and let `S` be Nagata,
integral with function field `K`, and regular of dimension one.  Assume that `κ(η)` is separable
over `K` at every generic point `η` of an irreducible component of `X`.  **Then there is a finite
separable extension `L / K` such that, with `T` the normalization of `S` in `Spec L` and
`ν : Y ⟶ X ×_S T` the normalization, `g : Y ⟶ T` is smooth at every generic point of every
fibre.**  This is Tag 0BRS, corrected by the quasi-compactness of `X`, without which it is false.

The proof is the source's: Tag 0BRS follows from Tag 0BRR exactly as Tag 0BRQ follows from Tag
09IL.  The gluing over a finite affine cover is
`AlgebraicGeometry.exists_finiteExtension_smoothAt_normalization_of_forall_affine`, which is
parametrized by a property of finite extensions stable under taking a common finite extension;
here that property is separability, stable because finitely many finite separable extensions embed
into a common finite separable one (`exists_finiteDimensional_isSeparable_algHom_forall`).  Over
each nonempty affine open `Spec A ⊆ S` the per-affine input is Tag 0BRR
(`AlgebraicGeometry.exists_finiteSeparableExtension_smoothAt_genericPoints_fiber_normalization_\
pullback`) for `X ×_S Spec A ⟶ Spec A`, whose separability hypothesis at the generic points is the
global one restricted to an open subscheme of `X`
(`AlgebraicGeometry.isSeparableExtension_residueFieldMap_pullback_snd`).

## Main results

* `AlgebraicGeometry.isSeparableExtension_residueFieldMap_pullback_snd`: separability of the
  residue field extensions at the generic points passes to the base change along an open
  immersion.
* `AlgebraicGeometry.exists_finiteSeparableExtension_smoothAt_genericPoints_fiber_normalization_\
  of_isRegular`: **Tag 0BRS**, with `X` quasi-compact.
* `AlgebraicGeometry.exists_finiteSeparableExtension_smoothAt_genericPoints_normalization_of_\
  compactSpace`: the same with `S` quasi-compact.

## Implementation notes

The separability hypothesis is stated as separability of `κ(η)` over `κ(f η)`, the residue field
extension of `f` at `η`.  Since `f` is flat it carries every generic point of `X` to the generic
point of `S`, whose residue field is the function field `K`; so this is the source's condition
that `κ(η) / K` be separable, in the form Tag 0BRR takes it.  Separability is that of Tag 030O,
`Algebra.IsSeparableExtension`, which does not require `κ(η) / K` algebraic.

The normalization `T` of `S` in `Spec L` is Mathlib's relative normalization (Tag 035H) of
`S.genericExtensionHom L : Spec L ⟶ S`.

## References

* [Stacks Project, Tag 0BRS](https://stacks.math.columbia.edu/tag/0BRS)
* [Stacks Project, Tag 0BRR](https://stacks.math.columbia.edu/tag/0BRR)
* [Stacks Project, Tag 0BRQ](https://stacks.math.columbia.edu/tag/0BRQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Separability of the residue field extensions at the generic points passes to an open
piece of the base.**  Let `f : X ⟶ S` be a morphism such that `κ(x) / κ(f x)` is separable at
every generic point `x` of an irreducible component of `X`, and let `j : V ⟶ S` be an open
immersion.  Then the base change `X ×_S V ⟶ V` has the same property: the projection to `X` is an
open immersion, so it carries generic points to generic points and induces isomorphisms of
residue fields compatible with those of `j`. -/
theorem isSeparableExtension_residueFieldMap_pullback_snd {X S V : Scheme.{u}} (f : X ⟶ S)
    (j : V ⟶ S) [IsOpenImmersion j]
    (hsep : ∀ x : X, x ∈ genericPoints X →
      letI : Algebra (S.residueField (f.base x)) (X.residueField x) :=
        (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparableExtension (S.residueField (f.base x)) (X.residueField x)) :
    ∀ z : (pullback f j : Scheme.{u}), z ∈ genericPoints (pullback f j : Scheme.{u}) →
      letI : Algebra (V.residueField ((pullback.snd f j).base z))
          ((pullback f j : Scheme.{u}).residueField z) :=
        ((pullback.snd f j).residueFieldMap z).hom.toAlgebra
      Algebra.IsSeparableExtension (V.residueField ((pullback.snd f j).base z))
        ((pullback f j : Scheme.{u}).residueField z) := by
  intro z hz
  have hx : (pullback.fst f j).base z ∈ genericPoints X :=
    mem_genericPoints_of_generalizingMap (pullback.fst f j).isOpenEmbedding.generalizingMap hz
  have hxz := hsep _ hx
  have hpt : f.base ((pullback.fst f j).base z) = j.base ((pullback.snd f j).base z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  -- the square of residue fields
  have hsq : f.residueFieldMap ((pullback.fst f j).base z) ≫
      (pullback.fst f j).residueFieldMap z =
      (S.residueFieldCongr hpt).hom ≫ j.residueFieldMap ((pullback.snd f j).base z) ≫
        (pullback.snd f j).residueFieldMap z := by
    rw [← Scheme.residueFieldMap_comp, ← Scheme.residueFieldMap_comp,
      Scheme.Hom.residueFieldMap_congr pullback.condition]
    rfl
  let : Algebra (S.residueField (f.base ((pullback.fst f j).base z)))
      (X.residueField ((pullback.fst f j).base z)) :=
    (f.residueFieldMap ((pullback.fst f j).base z)).hom.toAlgebra
  let : Algebra (V.residueField ((pullback.snd f j).base z))
      ((pullback f j : Scheme.{u}).residueField z) :=
    ((pullback.snd f j).residueFieldMap z).hom.toAlgebra
  refine Algebra.IsSeparableExtension.of_ringEquiv
    ((S.residueFieldCongr hpt ≪≫ asIso (j.residueFieldMap ((pullback.snd f j).base z))
      ).commRingCatIsoToRingEquiv)
    (asIso ((pullback.fst f j).residueFieldMap z)).commRingCatIsoToRingEquiv
    (fun a ↦ ?_) hxz
  have := congrArg (fun φ ↦ φ.hom a) hsq
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this

/-- **Stacks Project, Tag 0BRS (variant with separable extensions over curves), corrected: the
source omits quasi-compactness, and the statement is false without it.**  Let `f : X ⟶ S` be
flat and of finite type with `X` quasi-compact.  Assume `S` is Nagata, integral with function
field `K`, and regular of dimension `1`, and that the field extension `κ(η) / K` is separable for
every generic point `η` of an irreducible component of `X`.  Then there is a finite separable
extension `L / K` such that, with `T` the normalization of `S` in `Spec L`
(`(S.genericExtensionHom L).normalization`) and `ν : Y ⟶ X ×_S T` the normalization, the
morphism `g = ν ≫ pr₂ : Y ⟶ T` is smooth at every generic point of every fibre.

The separability hypothesis is that of `κ(η)` over `κ(f η)`; flatness puts `f η` at the generic
point of `S`, whose residue field is `K`.  The finiteness witness `hW` is the argument the
normalization of a scheme takes; it is a theorem (`X ×_S T` is locally Noetherian), not a
hypothesis.

**Correction.**  The source's proof is that of Tag 0BRQ, which begins with a finite affine open
covering of `S`; without quasi-compactness the statement is false: this is
`not_forall_exists_finiteSeparableExtension_smoothAt_genericPoints_fiber_normalization`, the
negation of the statement exactly as the source writes it, in the vocabulary of this theorem.
The counterexample is that of Tag 0BRQ
(`AlgebraicGeometry.not_forall_exists_finiteExtension_smoothAt_genericPoints_fiber_normalization`)
over `ℚ`, where the separability hypothesis holds because every extension of a field of
characteristic zero is separable, and the conclusion of Tag 0BRS contains that of Tag 0BRQ.
Quasi-compactness of `X` repairs the statement (only the finitely many affine opens covering the
image of `X` matter), and it is implied by that of `S`
(`AlgebraicGeometry.exists_finiteSeparableExtension_smoothAt_genericPoints_normalization_of_\
compactSpace`). -/
@[stacks 0BRS "corrected statement: the source omits quasi-compactness and is false without it \
(`not_forall_exists_finiteSeparableExtension_smoothAt_genericPoints_fiber_normalization`); stated \
here with `X` quasi-compact, which is implied by `S` quasi-compact (see the `_of_compactSpace` \
corollary)"]
theorem exists_finiteSeparableExtension_smoothAt_genericPoints_fiber_normalization_of_isRegular
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace X] [IsIntegral S] (hN : IsNagataScheme S) (hR : IsRegular S)
    (hdim : topologicalKrullDim S = 1)
    (hsep : ∀ x : X, x ∈ genericPoints X →
      letI : Algebra (S.residueField (f.base x)) (X.residueField x) :=
        (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparableExtension (S.residueField (f.base x)) (X.residueField x)) :
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
  obtain ⟨L, h₁, h₂, h₃, hP, h⟩ :=
    exists_finiteExtension_smoothAt_normalization_of_forall_affine f hN hR hdim
      (fun L _ _ ↦ Algebra.IsSeparable S.functionField L)
      (fun ι _ F _ _ _ hF ↦ by
        have := hF
        obtain ⟨E, hE₁, hE₂, hE₃, hE₄, hφ⟩ :=
          exists_finiteDimensional_isSeparable_algHom_forall (K := S.functionField) F
        exact ⟨E, hE₁, hE₂, hE₃, hE₄, hφ⟩)
      (fun U hU _ hA hD ↦ by
        have := hD
        have := functionField_isFractionRing_of_isAffineOpen S U hU
        obtain ⟨L, h₁, h₂, h₃, hsepL, h₄, h₅, h⟩ :=
          exists_finiteSeparableExtension_smoothAt_genericPoints_fiber_normalization_pullback
            (A := Γ(S, U)) S.functionField hA (pullback.snd f hU.fromSpec)
            (isSeparableExtension_residueFieldMap_pullback_snd f hU.fromSpec hsep)
        exact ⟨L, h₁, h₂, h₃, h₄, h₅, hsepL, h⟩)
  exact ⟨L, h₁, h₂, h₃, hP, h⟩

/-- **Tag 0BRS for a quasi-compact base.**  Let `f : X ⟶ S` be flat and of finite type, and let
`S` be quasi-compact, Nagata, integral with function field `K`, and regular of dimension `1`.
Assume `κ(η) / K` is separable at every generic point `η` of an irreducible component of `X`.
Then there is a finite separable extension `L / K` such that, with `T` the normalization of `S`
in `Spec L` and `ν : Y ⟶ X ×_S T` the normalization, `Y ⟶ T` is smooth at every generic point of
every fibre.  `X` is then quasi-compact, and the statement is
`AlgebraicGeometry.exists_finiteSeparableExtension_smoothAt_genericPoints_fiber_normalization_\
of_isRegular`. -/
theorem exists_finiteSeparableExtension_smoothAt_genericPoints_normalization_of_compactSpace
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace S] [IsIntegral S] (hN : IsNagataScheme S) (hR : IsRegular S)
    (hdim : topologicalKrullDim S = 1)
    (hsep : ∀ x : X, x ∈ genericPoints X →
      letI : Algebra (S.residueField (f.base x)) (X.residueField x) :=
        (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparableExtension (S.residueField (f.base x)) (X.residueField x)) :
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
          pullback.snd f (S.genericExtensionHom L).fromNormalization).fiberι b y) :=
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exists_finiteSeparableExtension_smoothAt_genericPoints_fiber_normalization_of_isRegular f hN hR
    hdim hsep

end AlgebraicGeometry
