module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafSpelling
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.AffineDerivedTildePushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.AffineTildeQuasicoherentEquivalence
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksFrontier.Homology.Perfect.Characterizing
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalPerfectness

/-!
# Compact and perfect objects of `D_QCoh(𝒪_X)`

Let `X` be a scheme. An object of `D_QCoh(𝒪_X)` is *compact* when every morphism out of it into a
direct sum factors through a finite subsum in exactly one way, and *perfect* when some complex
representing it is, on an open covering, quasi-isomorphic to a strictly perfect complex. On a
quasi-compact quasi-separated scheme the two conditions agree.

This file proves the implication from compactness to perfectness. On `X = Spec R` the two
conditions agree outright: derived sheafification `M ↦ M̃` carries `D(R)` onto `D_QCoh(𝒪_X)` and
matches the perfect objects on the two sides, so the statement becomes the ring-theoretic one
that a perfect object of `D(R)` is the same thing as a compact one. Globally, perfectness is
local on the space, so it is enough that `K` restrict, near every point, to a compact object of
the quasi-coherent derived category of an affine scheme.

## Main results

* `AlgebraicGeometry.isCompactObject_iff_isPerfect_spec`: on an affine scheme an object of
  `D_QCoh(𝒪_X)` is compact if and only if it is perfect.
* `AlgebraicGeometry.isPerfect_of_isCompactObject`: an object of `D_QCoh(𝒪_X)` which restricts,
  near every point, to a compact object of the quasi-coherent derived category of an affine
  scheme is a perfect object of `D(𝒪_X)`.

## Implementation notes

*What is assumed, and why.* Neither result assumes [Stacks, Tag 06Z0]. That the functor
`AlgebraicGeometry.affineTildeQuasicoherent R`, namely `M ↦ M̃` read as taking values in
`D_QCoh(𝒪_{Spec R})`, is an equivalence is proved, and is available here as the instance
`AlgebraicGeometry.affineTildeQuasicoherent_isEquivalence`; it rests on
`AlgebraicGeometry.StandardModel.derivedTilde_isEquivalence` of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean`. So the affine
case below is unconditional.

The global statement still assumes the affine-local datum: in the source it comes from
[Stacks, Tag 08DZ], that derived direct image along a quasi-compact quasi-separated morphism
commutes with direct sums, together with the identification of an affine open with the spectrum
of its ring of sections. Since that datum is a hypothesis, quasi-compactness and
quasi-separatedness of `X` are not needed; they enter the source only through
[Stacks, Tag 08DZ].

*The converse implication, that a perfect object of `D_QCoh(𝒪_X)` is compact, is not proved
here* — though not for want of its inputs. The source deduces it from the identification
`Hom_{D(𝒪_X)}(K, M) = H⁰(X, K^∨ ⊗^L_{𝒪_X} M)` of [Stacks, Tag 08DQ], *functorially in* `M`,
together with [Stacks, Tag 08DZ]. Tag 08DZ is formalized, in the namespace
`Stacks.Duality.DerivedPushforward.Qcoh`, as
`preservesColimitsOfShape_discrete_qcqsQuasiCoherentDerivedPushforward`;
the identification is formalized as an isomorphism of abelian groups, as
`Stacks.SheafOfModules.derivedTensorDualGlobalSectionsAddEquiv`, but its functoriality in `M` is
explicitly not claimed there, and functoriality is what the argument needs. Assembling the
converse from the two is open.

*Universes and spellings.* `AlgebraicGeometry.QuasicoherentDerivedCategory` is a full subcategory
of the derived category of `AlgebraicGeometry.SheafOfModules X.ringCatSheaf`, whereas perfectness
is stated for `StrictlyPerfect.OXMod X.toRingedSpace`. The two are the same type carrying the
same instances, by `Stacks.DerivedQCoh.oxMod_eq_sheafOfModules`, and `HasDerivedCategory.standard`
is seated as a local instance of high priority so that every spelling receives the same model.
That `attribute` is written *inside* `namespace AlgebraicGeometry` rather than at file scope: at
file scope it captures every declaration of the file wherever it is placed, so a statement at
another model — the locally small
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, at which the compact-generation results of
this chapter live — could not be added here at all, and
`StacksFrontier/AlgebraicGeometry/Perfect/QuasiCoherentDerived/CompactAndPerfectLocallySmall.lean`
exists because of it.
Additivity of `AlgebraicGeometry.affineTildeQuasicoherent` has to be moved across the
semireducible `def` by a term-level ascription, Mathlib's instance being stated for
`CategoryTheory.ObjectProperty.lift` and instance search unfolding only at reducible
transparency.

## References

* [The Stacks Project, Proposition 36.17.1 (09M1)](https://stacks.math.columbia.edu/tag/09M1)
* [The Stacks Project, Lemma 36.3.5 (06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
* [The Stacks Project, Lemma 36.4.5 (08DZ)](https://stacks.math.columbia.edu/tag/08DZ)
* [The Stacks Project, Lemma 36.10.7 (08EB)](https://stacks.math.columbia.edu/tag/08EB)
* [The Stacks Project, Proposition 15.80.3 (07LT)](https://stacks.math.columbia.edu/tag/07LT)
* [The Stacks Project, Lemma 20.49.2 (08CN)](https://stacks.math.columbia.edu/tag/08CN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty TopologicalSpace
open AlgebraicGeometry.RingedSpace.PseudoCoherence

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- Derived sheafification on an affine scheme, read as taking values in the quasi-coherent
derived category, is additive: it is so after the faithful inclusion of the full subcategory,
where it is the derived functor of an exact functor. -/
instance affineTildeQuasicoherent_additive (R : CommRingCat.{u}) :
    (affineTildeQuasicoherent R).Additive :=
  have _h : (affineTildeQuasicoherent R ⋙ ObjectProperty.ι
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf))).Additive :=
    inferInstanceAs ((tilde.functor R).mapDerivedCategory).Additive
  Functor.additive_of_comp_faithful (affineTildeQuasicoherent R)
    (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)))

/-- **Stacks 09M1 on an affine scheme.** Let `R` be a ring and let `L` be an object of
`D_QCoh(𝒪_{Spec R})`. Then `L` is a compact object of `D_QCoh(𝒪_{Spec R})` if and only if it is a
perfect object of `D(𝒪_{Spec R})`.

Writing `L = M̃` for an object `M` of `D(R)`, compactness of `L` is compactness of `M` because
`M ↦ M̃` is an equivalence ([Stacks, Tag 06Z0], here
`AlgebraicGeometry.affineTildeQuasicoherent_isEquivalence`), compactness of `M` is perfectness of
`M` by [Stacks, Tag 07LT], and perfectness of `M` is perfectness of `M̃` by
[Stacks, Tag 08EB]. -/
@[stacks 09M1 "the affine case, both directions"]
theorem isCompactObject_iff_isPerfect_spec (R : CommRingCat.{u})
    (L : QuasicoherentDerivedCategory (Spec R)) :
    IsCompactObject.{u} L ↔
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) L.obj := by
  let e := (affineTildeQuasicoherent R).asEquivalence
  let M := e.inverse.obj L
  have hLe : (affineTildeQuasicoherent R).obj M ≅ L := e.counitIso.app L
  have hLobj : (tilde.functor R).mapDerivedCategory.obj M ≅ L.obj :=
    (ObjectProperty.ι _).mapIso hLe
  exact ⟨fun hL => Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      (X := (Spec R).toRingedSpace) hLobj
      ((isPerfect_tilde_iff M).2
        ((StacksDraft.Perfect.isPerfect_iff_isCompactObject M).2
          ((isCompactObject_iff_isCompactObject_obj (affineTildeQuasicoherent R) M).2
            (isCompactObject_of_iso hLe hL)))),
    fun hL => isCompactObject_of_iso hLe.symm
      ((isCompactObject_iff_isCompactObject_obj (affineTildeQuasicoherent R) M).1
        ((StacksDraft.Perfect.isPerfect_iff_isCompactObject M).1
          ((isPerfect_tilde_iff M).1
            (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
              (X := (Spec R).toRingedSpace) hLobj.symm hL))))⟩

/-- **Stacks 09M1, the implication from compactness to perfectness.** Let `X` be a scheme and let
`K` be an object of `D_QCoh(𝒪_X)`. Suppose every point of `X` has an open neighbourhood `U` on
which `K` is the image, under a functor preserving perfectness, of a compact object of
`D_QCoh(𝒪_{Spec R})` for some ring `R`. Then `K` is a perfect object of `D(𝒪_X)`.

Compactness of `K` itself enters only through the local models: on a quasi-compact
quasi-separated scheme the restriction of a compact object of `D_QCoh(𝒪_X)` to an affine open is
compact there, by [Stacks, Tag 08DZ] and adjunction. The affine case makes the local models
perfect, and perfectness is local on the space by [Stacks, Tag 08CN]. -/
@[stacks 09M1 "compact implies perfect; the affine-local datum, which the source draws from Tag
08DZ (derived direct image along a quasi-compact quasi-separated morphism commutes with direct
sums) together with Tag 06Z0, is a hypothesis: that deduction is not carried out here. Tag 08DZ
is proved in this repository, as
Stacks.Duality.DerivedPushforward.preservesColimitsOfShape_discrete_qcqsQuasiCoherentDerivedPushforward,
but only at HasDerivedCategory.standard"]
theorem isPerfect_of_isCompactObject (X : Scheme.{u}) (K : QuasicoherentDerivedCategory X)
    (hloc : ∀ x : X.toRingedSpace.carrier,
      ∃ (U : Opens X.toRingedSpace.carrier) (_ : x ∈ U) (R : CommRingCat.{u})
        (Φ : DerivedCategory (SheafOfModules.{u} (Spec R).ringCatSheaf) ⥤
          DerivedCategory (StrictlyPerfect.OXMod.{u, u, u}
            (X.toRingedSpace.restrict U.isOpenEmbedding)))
        (L : QuasicoherentDerivedCategory (Spec R)),
        IsCompactObject.{u} L ∧
          (∀ N, Stacks.Cohomology.PerfectComplexes.IsPerfect
              (X := (Spec R).toRingedSpace) N →
            Stacks.Cohomology.PerfectComplexes.IsPerfect
              (X := X.toRingedSpace.restrict U.isOpenEmbedding) (Φ.obj N)) ∧
          Nonempty (Φ.obj L.obj ≅
            (RingedSpace.restrictModules X.toRingedSpace U).mapDerivedCategory.obj K.obj)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K.obj := by
  refine Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect
    (X := X.toRingedSpace) K.obj fun x => ?_
  obtain ⟨U, hxU, R, Φ, L, hL, hΦ, ⟨eΦ⟩⟩ := hloc x
  exact ⟨U, hxU, Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    (X := X.toRingedSpace.restrict U.isOpenEmbedding) eΦ
    (hΦ L.obj ((isCompactObject_iff_isPerfect_spec R L).1 hL))⟩

end AlgebraicGeometry

end
