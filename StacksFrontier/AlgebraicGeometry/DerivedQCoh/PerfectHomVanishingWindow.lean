module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.GlobalSections
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.DerivedUpperBound
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BoundedAbove
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace
import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of morphisms from a perfect complex into a quasi-coherent complex

Let `X` be a quasi-compact and quasi-separated scheme and let `K` be a perfect object of
`D(𝒪_X)`. There is a finite window `[a, b]` of cohomological degrees, depending only on `X` and
`K`, such that an object of `D_{QCoh}(𝒪_X)` whose cohomology sheaves vanish throughout the
window admits no nonzero morphism from `K`; consequently the groups
`Ext^n_{D(𝒪_X)}(K, L) = Hom_{D(𝒪_X)}(K, L⟦n⟧)` vanish for all but finitely many `n` when `L` is
bounded. This is [Stacks, Tag 09M4] with two of its inputs carried as hypotheses; the tag itself,
with neither, is `Stacks.DerivedQCoh.exists_window_subsingleton_hom_of_isPerfect_qcqs` and
`Stacks.DerivedQCoh.finite_setOf_not_subsingleton_hom_shift_of_isPerfect_qcqs`.

## Main definitions

* `Stacks.DerivedQCoh.DualPerfectComplexData`: the content of [Stacks, Tag 08DQ] used below —
  the dual `K^∨ = R𝓗om(K, 𝒪_X)` of a perfect object, an upper cohomological bound for it, the
  quasi-coherence of the cohomology sheaves of `K^∨ ⊗^𝐋_{𝒪_X} M`, and the identification
  `Hom_{D(𝒪_X)}(K, M) = H⁰(X, K^∨ ⊗^𝐋_{𝒪_X} M)` in the one direction used.

## Main results

* `Stacks.DerivedQCoh.exists_window_subsingleton_hom_of_isPerfect` is part (1) of the tag, with
  the dual complex and the upper bound of `K` carried as hypotheses; part (1) with neither is
  `Stacks.DerivedQCoh.exists_window_subsingleton_hom_of_isPerfect_qcqs`.
* `Stacks.DerivedQCoh.finite_setOf_not_subsingleton_hom_shift_of_isPerfect` is part (2), with the
  same two hypotheses; part (2) with neither is
  `Stacks.DerivedQCoh.finite_setOf_not_subsingleton_hom_shift_of_isPerfect_qcqs`.
* `Stacks.DerivedQCoh.isLE_truncLE_obj_of_isZero_homology` is the step that converts the window
  hypothesis into a cohomological bound on the truncation of the target.

## Implementation notes

**The proof.** Write `b` for an upper cohomological bound of `K` and split the target `L` by the
truncation triangle `τ_{≤b}L ⟶ L ⟶ τ_{≥b+1}L`. Morphisms from `K` into the third vertex vanish
by t-structure orthogonality. The first vertex retains only the cohomology of `L` in degrees
`≤ b`, all of which the window hypothesis kills from `a` upwards, so `τ_{≤b}L` lies in degrees
`≤ a - 1`; tensoring with `K^∨`, which lies in degrees `≤ b'`, puts `K^∨ ⊗^𝐋 τ_{≤b}L` in degrees
`≤ b' + a - 1`, and the cohomological-dimension bound of [Stacks, Tag 071L] in the form of
[Stacks, Tag 08D4] then puts `RΓ(X, K^∨ ⊗^𝐋 τ_{≤b}L)` in degrees `< 0` once `a` is chosen below
`-b' - N`. So `H⁰(X, K^∨ ⊗^𝐋 τ_{≤b}L) = 0`, whence `Hom(K, τ_{≤b}L) = 0`, and the two vanishings
combine along the truncation triangle.

**What is carried as a hypothesis, and why.** Two inputs the source cites are not available in
this library in a form that applies here, and are carried as named hypotheses rather than proved.

The first is [Stacks, Tag 08DQ]: the dual perfect complex `K^∨` and the functorial
identification `H⁰(X, M ⊗^𝐋_{𝒪_X} K^∨) = Hom_{D(𝒪_X)}(K, M)`. There is no absolute derived
internal hom `R𝓗om` on `D(𝒪_X)` for a single scheme `X` in this library — the scheme-level
derived internal hom is relative to a morphism, and the absolute one is stated over a ringed
site with its own, different, perfectness predicate — so `K^∨` cannot even be written down here.
`Stacks.DerivedQCoh.DualPerfectComplexData` therefore carries the dual as data together with
exactly the properties the proof consumes. It asserts no vanishing: the vanishing of
`Hom_{D(𝒪_X)}(K, M)` is derived below from a vanishing of `H⁰(X, K^∨ ⊗^𝐋 M)` which is itself
proved. Quasi-coherence of the cohomology sheaves of `K^∨ ⊗^𝐋 M` travels with the dual: it is
[Stacks, Tag 08DX] part (1) together with [Stacks, Tag 08E5], the pair the source cites at this
point, and the library's form of 08DX part (1) is stated for the bounded subcategory
`D^b_{QCoh}(𝒪_X)`, which the truncation `τ_{≤b}L` used below need not lie in.

The second is the boundedness above of a perfect object, [Stacks, Tags 0BCJ and 08E8]: a perfect
object of `D(𝒪_X)` is locally represented by a strictly perfect complex, hence locally bounded,
and quasi-compactness of `X` makes the bound global. The library has the local statement
`Stacks.Cohomology.TorAmplitude.exists_bounds_of_isStrictlyPerfect` but not its globalization,
which is recorded elsewhere in this library as an un-bridged step, so the upper bound is a
hypothesis here too.

**Spellings.** The derived tensor product is the canonical one of [Stacks, Tag 06YU], read off
the ringed space underlying `X` as `Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace`;
`RΓ(X, -)` on the unbounded derived category is a total right derived functor of
`Stacks.Cohomology.sectionsFunctor X ⊤` and, as in
`StacksFrontier.AlgebraicGeometry.DerivedAcyclic.GlobalSections`, enters as a pair of a functor and
its structure morphism with the right-derived-functor instance, so the statements below hold for
every model of it. `H⁰(X, -)` is the degree-zero cohomology of that functor.

## References

* [Stacks Project, Tag 09M4](https://stacks.math.columbia.edu/tag/09M4)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology (sectionsFunctor)
open Stacks.Cohomology.TorAmplitude (derTensor)

universe u

namespace Stacks.DerivedQCoh

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### The cited dual perfect complex -/

/-- **The dual perfect complex of [Stacks, Tag 08DQ], carried as data.** For a perfect object `K`
of `D(𝒪_X)` the tag produces the dual `K^∨ = R𝓗om(K, 𝒪_X)`, again perfect — hence bounded, and
with `K^∨ ⊗^𝐋 M` quasi-coherent whenever `M` is, by [Stacks, Tags 08DX and 08E5] — together with
the functorial identification `H⁰(X, K^∨ ⊗^𝐋_{𝒪_X} M) = Hom_{D(𝒪_X)}(K, M)`.

Recorded here are only the properties used in the proof of [Stacks, Tag 09M4]: an upper
cohomological bound `upper` for the dual, quasi-coherence of the cohomology sheaves of
`K^∨ ⊗^𝐋 M`, and the implication from vanishing of `H⁰(X, K^∨ ⊗^𝐋 M)` to vanishing of
`Hom_{D(𝒪_X)}(K, M)`. -/
structure DualPerfectComplexData (X : Scheme.{u})
    (RΓ : DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(X, ⊤)))
    (K : DerivedCategory X.Modules) where
  /-- The dual `K^∨ = R𝓗om(K, 𝒪_X)`. -/
  dual : DerivedCategory X.Modules
  /-- An upper cohomological bound for the dual, which is perfect, hence bounded. -/
  upper : ℤ
  /-- The dual lies in cohomological degrees `≤ upper`. -/
  isLE_dual : dual.IsLE upper
  /-- Tensoring with the dual preserves quasi-coherence of the cohomology sheaves. -/
  isQuasicoherent_derivedTensor : ∀ M : DerivedCategory X.Modules,
    (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj M).IsQuasicoherent) →
    ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj
      (((derTensor X.toRingedSpace).tensor.obj dual).obj M)).IsQuasicoherent
  /-- Vanishing of `H⁰(X, K^∨ ⊗^𝐋 M)` forces vanishing of `Hom_{D(𝒪_X)}(K, M)`. -/
  subsingleton_hom_of_isZero : ∀ M : DerivedCategory X.Modules,
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) 0).obj
      (RΓ.obj (((derTensor X.toRingedSpace).tensor.obj dual).obj M))) →
    Subsingleton (K ⟶ M)

/-! ### Truncating a complex with a window of vanishing cohomology -/

/-- **A window of vanishing cohomology makes a truncation from above small.** If the cohomology
sheaves of `L` vanish in the degrees `a, a + 1, …, b`, then `τ_{≤b}L` lies in cohomological
degrees `≤ a - 1`: above `b` the truncation vanishes, and between `a` and `b` its cohomology is
that of `L`. -/
theorem isLE_truncLE_obj_of_isZero_homology {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] (L : DerivedCategory A) (a b : ℤ)
    (hL : ∀ i : ℤ, a ≤ i → i ≤ b → IsZero ((DerivedCategory.homologyFunctor A i).obj L)) :
    ((DerivedCategory.TStructure.t.truncLE b).obj L).IsLE (a - 1) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  rcases le_or_gt i b with hib | hib
  · have := Stacks.SmallDerivedCategory.isIso_homologyFunctor_map_truncLEι L b i hib
    exact IsZero.of_iso (hL i (by omega) hib)
      (asIso ((DerivedCategory.homologyFunctor A i).map
        ((DerivedCategory.TStructure.t.truncLEι b).app L)))
  · exact DerivedCategory.isZero_of_isLE _ b i hib

/-! ### Stacks 09M4 -/

section Main

variable (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
  (RΓ : DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(X, ⊤)))
  (α : (sectionsFunctor X ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RΓ)
  [RΓ.IsRightDerivedFunctor α (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
  (K : DerivedCategory X.Modules)

include α in
/-- **A special case of Stacks Project, Tag 09M4, part (1).** Let `X` be a quasi-compact and
quasi-separated scheme and let `K` be a perfect object of `D(𝒪_X)`. Then there are integers
`a ≤ b` such that every `L ∈ D_{QCoh}(𝒪_X)` whose cohomology sheaves vanish in the degrees
`a, a + 1, …, b` admits no nonzero morphism from `K`.

The cited dual perfect complex of [Stacks, Tag 08DQ] and the boundedness above of the perfect
object `K` ([Stacks, Tags 0BCJ, 08E8]) are carried as hypotheses; see the implementation notes.
Perfectness of `K` is what the source uses to produce those two inputs, so it is recorded in the
statement but consumed only through them. Part (1) with neither hypothesis, which carries the tag,
is `Stacks.DerivedQCoh.exists_window_subsingleton_hom_of_isPerfect_qcqs`. -/
theorem exists_window_subsingleton_hom_of_isPerfect
    (_hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K)
    (D : DualPerfectComplexData X RΓ K) (bK : ℤ) (hKLE : K.IsLE bK) :
    ∃ a b : ℤ, a ≤ b ∧
      ∀ L : DerivedCategory X.Modules,
        (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsQuasicoherent) →
        (∀ i : ℤ, a ≤ i → i ≤ b → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj L)) →
        Subsingleton (K ⟶ L) := by
  obtain ⟨N, hN⟩ := AlgebraicGeometry.isLE_rightDerivedSections_obj_of_isQuasicoherent X RΓ α
  obtain ⟨a, hale, haK⟩ : ∃ a : ℤ, a ≤ -D.upper - N ∧ a ≤ bK :=
    ⟨min (-D.upper - N) bK, min_le_left _ _, min_le_right _ _⟩
  refine ⟨a, bK, haK, fun L hLqc hLvan => ?_⟩
  -- the truncation triangle of `L` at `bK`
  let T := (DerivedCategory.TStructure.t.triangleLEGE bK (bK + 1) rfl).obj L
  have hTd : T ∈ distTriang (DerivedCategory X.Modules) :=
    DerivedCategory.TStructure.t.triangleLEGE_distinguished bK (bK + 1) rfl L
  have hge₃ : T.obj₃.IsGE (bK + 1) :=
    DerivedCategory.TStructure.t.isGE_truncGE_obj L (bK + 1) (bK + 1) le_rfl
  -- no nonzero morphism from `K` into the part in degrees `≥ bK + 1`
  have hzero₃ : ∀ f : K ⟶ T.obj₃, f = 0 := fun f =>
    DerivedCategory.TStructure.t.zero_of_isLE_of_isGE f bK (bK + 1) (by omega) hKLE hge₃
  -- the part in degrees `≤ bK` lies in degrees `≤ a - 1`
  have hle₁ : T.obj₁.IsLE (a - 1) :=
    isLE_truncLE_obj_of_isZero_homology L a bK (fun i h₁ h₂ => hLvan i h₁ h₂)
  have hqc₁ : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor X.Modules i).obj T.obj₁).IsQuasicoherent := fun i =>
    DerivedCategory.prop_homologyFunctor_truncLE_obj
      (AlgebraicGeometry.isQuasicoherentModules X) L (fun j => hLqc j) bK i
  -- tensoring with the dual, then taking derived global sections, lands in negative degrees
  let W := ((derTensor X.toRingedSpace).tensor.obj D.dual).obj T.obj₁
  have htenLE : W.IsLE (D.upper + (a - 1)) :=
    @Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct _ _ _ X.sheaf _ _ _ _ _ _ _
      D.dual T.obj₁ D.upper (a - 1) D.isLE_dual hle₁
  have htenQc : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor X.Modules i).obj W).IsQuasicoherent :=
    D.isQuasicoherent_derivedTensor T.obj₁ hqc₁
  have hRΓ := hN W (D.upper + (a - 1)) htenQc htenLE
  have hH0 : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) 0).obj
      (RΓ.obj W)) :=
    DerivedCategory.isZero_of_isLE _ (D.upper + (a - 1) + N - 1) 0 (by omega) (hX := hRΓ)
  have hsub₁ : Subsingleton (K ⟶ T.obj₁) := D.subsingleton_hom_of_isZero T.obj₁ hH0
  -- combine the two vanishings along the triangle
  refine ⟨fun f g => ?_⟩
  obtain ⟨f', hf'⟩ := Pretriangulated.Triangle.coyoneda_exact₂ T hTd f (hzero₃ (f ≫ T.mor₂))
  obtain ⟨g', hg'⟩ := Pretriangulated.Triangle.coyoneda_exact₂ T hTd g (hzero₃ (g ≫ T.mor₂))
  rw [hf', hg', hsub₁.elim f' g']

include α in
/-- **A special case of Stacks Project, Tag 09M4, part (2).** Let `X` be a quasi-compact and
quasi-separated scheme, let `K` be a perfect object of `D(𝒪_X)` and let `L` be a bounded object of
`D_{QCoh}(𝒪_X)`. Then `Ext^n_{D(𝒪_X)}(K, L) = Hom_{D(𝒪_X)}(K, L⟦n⟧)` vanishes for all but
finitely many `n`.

Outside a bounded range of `n` the shift `L⟦n⟧` has no cohomology at all in the window of part
(1), because `L` is bounded; the hypotheses are those of part (1). Part (2) with neither the dual
complex nor the upper bound of `K` as a hypothesis, which carries the tag, is
`Stacks.DerivedQCoh.finite_setOf_not_subsingleton_hom_shift_of_isPerfect_qcqs`. -/
theorem finite_setOf_not_subsingleton_hom_shift_of_isPerfect
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K)
    (D : DualPerfectComplexData X RΓ K) (bK : ℤ) (hKLE : K.IsLE bK)
    (L : DerivedCategory X.Modules)
    (hLqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsQuasicoherent)
    (c d : ℤ) (hLGE : L.IsGE c) (hLLE : L.IsLE d) :
    {n : ℤ | ¬ Subsingleton (K ⟶ L⟦n⟧)}.Finite := by
  have := hLGE
  have := hLLE
  obtain ⟨a, b, -, hvan⟩ :=
    exists_window_subsingleton_hom_of_isPerfect X RΓ α K hK D bK hKLE
  refine Set.Finite.subset (Set.finite_Icc (c - b) (d - a)) ?_
  intro n hn
  replace hn : ¬ Subsingleton (K ⟶ L⟦n⟧) := hn
  by_contra hmem
  simp only [Set.mem_Icc, not_and_or, not_le] at hmem
  -- the shift has quasi-coherent cohomology
  have hqc : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor X.Modules i).obj (L⟦n⟧)).IsQuasicoherent := by
    intro i
    exact (AlgebraicGeometry.isQuasicoherentModules X).prop_of_iso
      (((DerivedCategory.homologyFunctor X.Modules 0).shiftIso n i (n + i) rfl).app L).symm
      (hLqc (n + i))
  refine hn (hvan (L⟦n⟧) hqc fun i hai hib => ?_)
  rcases hmem with hlt | hlt
  · have : (L⟦n⟧).IsGE (c - n) :=
      DerivedCategory.TStructure.t.isGE_shift L c n (c - n) (by omega)
    exact DerivedCategory.isZero_of_isGE _ (c - n) i (by omega)
  · have : (L⟦n⟧).IsLE (d - n) :=
      DerivedCategory.TStructure.t.isLE_shift L d n (d - n) (by omega)
    exact DerivedCategory.isZero_of_isLE _ (d - n) i (by omega)

end Main

end Stacks.DerivedQCoh

end
