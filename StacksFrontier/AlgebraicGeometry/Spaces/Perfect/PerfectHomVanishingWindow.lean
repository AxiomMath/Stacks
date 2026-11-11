module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectHomWindowAffine
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryModel
public import StacksFrontier.Homology.DerivedCategory.ModelComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Ext from a perfect object into a bounded quasi-coherent object on an algebraic space

Let `S` be a scheme, let `X` be a quasi-compact and quasi-separated algebraic space over `S` and
let `K` be a perfect object of `D(𝒪_X)`.  [Stacks, Tag 09MB] asserts:

1. there are integers `a ≤ b` such that `Hom_{D(𝒪_X)}(K, L) = 0` for every `L ∈ D_QCoh(𝒪_X)`
   with `Hⁱ(L) = 0` for `i ∈ [a, b]`;
2. if `L ∈ D_QCoh(𝒪_X)` is bounded, then `Extⁿ_{D(𝒪_X)}(K, L) = Hom_{D(𝒪_X)}(K, L[n])` is zero
   for all but finitely many `n`.

## Main results

* `AlgebraicGeometry.Space.exists_window_subsingleton_hom_of_isPerfect`: [Stacks, Tag 09MB]
  part (1).
* `AlgebraicGeometry.Space.finite_setOf_not_subsingleton_hom_shift_of_isPerfect`:
  [Stacks, Tag 09MB] part (2).

## Implementation notes

**The objects.**  `𝒪_X`-modules are the sheaves of modules on the small étale ringed site of `X`,
`AlgebraicGeometry.Space.Modules`, at the module universe of the structure rings.  `K` is
perfect in the sense of Stacks 08G5 on that ringed site, and `L ∈ D_QCoh(𝒪_X)` is spelled as the
condition that every cohomology sheaf of `L` be quasi-coherent, which is the membership condition
of `AlgebraicGeometry.Space.QuasicoherentDerivedCategory` (Stacks 071X).  Quasi-separatedness is
the absolute notion `AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated` of Stacks 03BS(3), which
is why the ambient big fppf site is required to contain the terminal scheme `Spec ℤ`.  Vanishing
of a group of morphisms of `D(𝒪_X)` is `Subsingleton`, the category being preadditive, and
`Extⁿ(K, L)` is `Hom(K, L⟦n⟧)`, as in the source's proof.

**The model of `D(𝒪_X)`** is an arbitrary `[HasDerivedCategory.{w}]`.  The window is produced at
`CategoryTheory.HasDerivedCategory.standard`, the only model of the derived category of
`𝒪_X`-modules in which its inputs (Stacks 08H9, 08JL, 09M4) are available, and carried to the given
model along the comparison `StacksDraft.DerivedModel.modelEquiv`, which commutes with the
cohomology functors (`StacksDraft.DerivedModel.modelHomologyFunctorIso`) and with the localization
functors (`StacksDraft.DerivedModel.modelCompQIso`); perfectness is a statement about a
representing complex and so does not depend on the model.

**The argument for part (1)** is not the source's.  The source writes
`Hom(K, L) = H⁰(X, K^∨ ⊗^𝐋 L)` with the dual of Stacks 08JJ and bounds the cohomological dimension
by Stacks 072C and 08F7.  The dual is not available in this library at the universes of the small
étale site of an algebraic space (the internal Hom of Stacks 0A8Z raises the module universe of a
site whose objects lie in `Type (u + 1)`), so the window is built by induction on `X` instead,
with the induction principle of Stacks 08GP: a window crosses an elementary distinguished square
by the Mayer–Vietoris sequence of Stacks 08H9
(`AlgebraicGeometry.Space.hasHomWindow_of_eds`), and on an affine algebraic space it is the
scheme statement Stacks 09M4, through the equivalence `D_QCoh(𝒪_T) ≌ D_QCoh(T_étale, 𝒪)` of
Stacks 071Q and the perfectness comparison of Stacks 08HG
(`AlgebraicGeometry.Space.hasHomWindow_of_isAffineSpace`).

**Part (2)** follows from part (1) as in the source: outside a bounded range of `n` the shift
`L⟦n⟧` has no cohomology at all in the window of part (1), `L` being bounded.

## References

* [Stacks Project, Tag 09MB](https://stacks.math.columbia.edu/tag/09MB)
* [Stacks Project, Tag 09M4](https://stacks.math.columbia.edu/tag/09M4)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08H9](https://stacks.math.columbia.edu/tag/08H9)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 08HG](https://stacks.math.columbia.edu/tag/08HG)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.HomWindow StacksDraft.DerivedModel

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

variable (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-- **Stacks 09MB, part (1).**  Let `S` be a scheme, let `X` be a quasi-compact and
quasi-separated algebraic space over `S` and let `K` be a perfect object of `D(𝒪_X)`.  Then there
are integers `a ≤ b` such that `Hom_{D(𝒪_X)}(K, L) = 0` for every `L ∈ D_QCoh(𝒪_X)` with
`Hⁱ(L) = 0` for `i ∈ [a, b]`.

The model of the derived category is arbitrary.  The window is the one produced at the standard
model by the induction `AlgebraicGeometry.Space.hasHomWindow_of_isPerfect_of_affine`, whose affine
case is `AlgebraicGeometry.Space.hasHomWindow_of_isAffineSpace`, carried across the comparison of
the two models. -/
@[stacks 09MB "part (1)", stacks 09M9 "Lemma 09MB of the section, part (1)"]
theorem exists_window_subsingleton_hom_of_isPerfect
    (hqc : IsQuasiCompactSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    [hD : HasDerivedCategory.{w} (Modules.{u, u} B S hS X hX)]
    (K : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hK : (smallEtaleRingedSite B S hS X hX).IsPerfect K) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ L : DerivedCategory (Modules.{u, u} B S hS X hX),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i).obj
        L).IsQuasicoherentOnSite) →
      (∀ i : ℤ, a ≤ i → i ≤ b →
        IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i).obj L)) →
      Subsingleton (K ⟶ L) := by
  obtain ⟨E, hE, ⟨eK⟩⟩ := hK
  obtain ⟨a, b, hab, hw⟩ := hasHomWindow_of_isPerfect_of_affine B S hS hZ
    (fun Y hY K hK => hasHomWindow_of_isAffineSpace B S hS Y hY K hK) ⟨X, hX⟩ hqc hqs
    ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (Modules.{u, u} B S hS X hX))).obj E)
    ⟨E, hE, ⟨Iso.refl _⟩⟩
  refine ⟨a, b, hab, fun L hL hz => ?_⟩
  let Φ := modelEquiv (HasDerivedCategory.standard (Modules.{u, u} B S hS X hX)) hD
  let L₁ := Φ.inverse.obj L
  let eL : Φ.functor.obj L₁ ≅ L := Φ.counitIso.app L
  have hH : ∀ i : ℤ, (@DerivedCategory.homologyFunctor _ _ _
      (HasDerivedCategory.standard (Modules.{u, u} B S hS X hX)) i).obj L₁ ≅
      (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i).obj L := fun i =>
    ((modelHomologyFunctorIso (HasDerivedCategory.standard (Modules.{u, u} B S hS X hX))
        hD i).app L₁).symm ≪≫
      (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i).mapIso eL
  have hsub := hw L₁ (fun i => (qcohModules B S hS ⟨X, hX⟩).prop_of_iso (hH i).symm (hL i))
    (fun i hai hib => (hz i hai hib).of_iso (hH i))
  exact (Iso.homCongr (((modelCompQIso (HasDerivedCategory.standard (Modules.{u, u} B S hS X hX))
      hD).app E) ≪≫ eK) eL).subsingleton_congr.1
    ((Φ.fullyFaithfulFunctor.homEquiv).subsingleton_congr.1 hsub)

/-- **Stacks 09MB, part (2).**  Let `S` be a scheme, let `X` be a quasi-compact and
quasi-separated algebraic space over `S`, let `K` be a perfect object of `D(𝒪_X)` and let `L` be a
bounded object of `D_QCoh(𝒪_X)`.  Then `Extⁿ_{D(𝒪_X)}(K, L) = Hom_{D(𝒪_X)}(K, L⟦n⟧)` is zero for
all but finitely many `n`.

Outside a bounded range of `n` the shift `L⟦n⟧` has no cohomology at all in the window of part
(1), because `L` is bounded. -/
@[stacks 09MB "part (2)", stacks 09M9 "Lemma 09MB of the section, part (2)"]
theorem finite_setOf_not_subsingleton_hom_shift_of_isPerfect
    (hqc : IsQuasiCompactSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    [HasDerivedCategory.{w} (Modules.{u, u} B S hS X hX)]
    (K : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hK : (smallEtaleRingedSite B S hS X hX).IsPerfect K)
    (L : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hLqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i).obj
      L).IsQuasicoherentOnSite)
    (c d : ℤ) (hLGE : L.IsGE c) (hLLE : L.IsLE d) :
    {n : ℤ | ¬ Subsingleton (K ⟶ L⟦n⟧)}.Finite := by
  have := hLGE
  have := hLLE
  obtain ⟨a, b, -, hvan⟩ :=
    exists_window_subsingleton_hom_of_isPerfect B S hS hZ X hX hqc hqs K hK
  refine Set.Finite.subset (Set.finite_Icc (c - b) (d - a)) ?_
  intro n hn
  replace hn : ¬ Subsingleton (K ⟶ L⟦n⟧) := hn
  by_contra hmem
  simp only [Set.mem_Icc, not_and_or, not_le] at hmem
  have hqc' : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) i).obj
      (L⟦n⟧)).IsQuasicoherentOnSite := fun i =>
    (qcohModules B S hS ⟨X, hX⟩).prop_of_iso
      (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0).shiftIso n i (n + i)
        rfl).app L).symm (hLqc (n + i))
  refine hn (hvan (L⟦n⟧) hqc' fun i hai hib => ?_)
  rcases hmem with hlt | hlt
  · have : (L⟦n⟧).IsGE (c - n) :=
      DerivedCategory.TStructure.t.isGE_shift L c n (c - n) (by omega)
    exact DerivedCategory.isZero_of_isGE _ (c - n) i (by omega)
  · have : (L⟦n⟧).IsLE (d - n) :=
      DerivedCategory.TStructure.t.isLE_shift L d n (d - n) (by omega)
    exact DerivedCategory.isZero_of_isLE _ (d - n) i (by omega)

end AlgebraicGeometry.Space

end
