module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPresentationExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerArbitraryIndex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeTensorFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPresentationExact

/-!
# Free presentations of the symmetric and exterior powers of a presented sheaf of modules

Let `X` be a ringed space and let `M₂ --q--> M₁ --p--> M ⟶ 0` be an exact presentation of a
sheaf of `O_X`-modules, with `M₂` and `M₁` isomorphic to free sheaves of modules on index types
`I₂` and `I₁`. Tag 01CJ gives, for every `n ≥ 1`, the three-term exact sequence

`M₂ ⊗ Sym^{n-1}(M₁) ⟶ Symⁿ(M₁) ⟶ Symⁿ(M) ⟶ 0`

and its exterior analogue. This file records that the first two terms of those sequences are
themselves free: the middle term because a symmetric or exterior power of a free sheaf of modules
is free
(`Stacks.SheafOfModules.symmetricPowerFreeIsoOfIsoAnyIndex`,
`exteriorPowerFreeIsoOfIsoAnyIndex`), and the first term because the tensor product of two free
sheaves of modules is free (`Stacks.SheafOfModules.tensorIsoFree`). So an exact presentation by
free sheaves of modules presents every positive symmetric and exterior power by free sheaves of
modules, on the same space and with the same presentation data.

## Main results

* `Stacks.SheafOfModules.exists_free_symmetricPower_presentation` and
  `exists_free_exteriorPower_presentation`: **the general form.** For an arbitrary package of
  algebras in the sense of Section 17.21 over `M₁` and over `M`, the complex of Tag 01CJ in
  degree `n` is exact with epimorphic second map and has free first and middle terms, with the
  freeness of the two index types recorded as an implication from the freeness of `I₂` and `I₁`.
* `Stacks.SheafOfModules.symmetricPower_freePresentation`,
  `exteriorPower_freePresentation`, `symmetricPower_finiteFreePresentation` and
  `exteriorPower_finiteFreePresentation`: the four consumer forms, for the chosen package
  `SheafOfModules.ringedSpaceAlgebras`, with the finite versions asserting `Finite` of the two
  index types outright.

## Implementation notes

**Nothing here is new mathematics; the file is the assembly.** Each of the three inputs is
already proved:

* the exact sequence and the epimorphy are Tag 01CJ,
  `SheafOfModules.SymPresentation.symmetricPresentation_exact` and
  `SheafOfModules.ExtPresentation.exteriorPresentation_exact`;
* the middle term is free by `Stacks.SheafOfModules.symmetricPowerFreeIsoOfIsoAnyIndex` and
  `exteriorPowerFreeIsoOfIsoAnyIndex`, which carry **no finiteness hypothesis** on the index
  type;
* the first term is free by `Stacks.SheafOfModules.tensorIsoFree`.

**The index types are produced concretely, not existentially.** The consumer forms
`exists_nonempty_iso_free_symmetricPower` and `exists_nonempty_iso_free_exteriorPower` hide the
index type behind an existential, which makes the finiteness clause of the finite statements
unprovable; the isomorphisms themselves name the index types
(`{d : I₁ →₀ ℕ | d.degree = n}` and `Set.powersetCard I₁ n`), so the finite case is then an
instance search. The first term's index type is the product `I₂ × …`.

**The degree is peeled once, at the start.** `1 ≤ n` is turned into `n = m + 1` by `obtain`, so
every subsequent degree is `m` or `m + 1` for a variable `m`, and `n - 1` becomes `m` by `rfl`.
This is the discipline the symmetric-algebra development needs throughout: at a numeral degree
the reducible `SymmetricAlgebra` is unfolded by `whnf` through a `RingCon` quotient.

**The epimorphy of the presentation is an explicit hypothesis, not an instance.** The structure
sheaf of a ringed space has two definitionally equal spellings — `structureSheafRing X` and
`CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf` — and `Epi` in
the two resulting categories is not one discrimination-tree key, so an instance binder
`[Epi S.g]` at one spelling is not found at the other. A `Prop`-valued hypothesis is exactly as
strong and crosses the boundary at the application site, where the defeq is checked once.
Correspondingly the general theorems are stated throughout in the `toRingCat` spelling, which is
the one all the machinery above uses, and the four consumer forms in the `structureSheafRing`
spelling, which is the one a ringed-space consumer uses.

**Universes.** Everything is at a single universe: `RingedSpace.{u, u}` with modules in
`SheafOfModules.{u}`. This is forced, not chosen — Tag 01CJ's stalkwise proof is stated for
`X : TopCat.{u}` with `Osharp : Sheaf _ CommRingCat.{u}` and graded algebras in
`GradedAlgebra.{u, u}`, and `SheafOfModules.free` takes its index type in the module universe.

**No `@[stacks]` attribute.** The exact sequences are Tag 01CJ, whose covering set is already
complete and recorded on `symmetricPresentation_exact` and `exteriorPresentation_exact`. The
freeness of the powers is Tag 01CK clause (6), which is the assertion for a *locally* free sheaf
of modules; what is proved here, as in `FreePowerFree`, `FreePowerSheafify` and
`FreePowerArbitraryIndex`, is the globally free case, so the tag is declined for the same reason
those three files decline it. The module-level analogue of this statement is
`SymPow.symmetricPower_freePresentation` in
`StacksFrontier.LinearAlgebra.SymmetricPower.FreePresentation`.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf AlgebraicGeometry
  TopologicalSpace RingedSpaceModuleAdjunction

universe u

namespace Stacks.SheafOfModules

section General

variable {X : RingedSpace.{u, u}}
  {S : ShortComplex (SheafOfModules.{u}
    (toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf))}

/-- **An exact presentation by free sheaves of modules presents every positive symmetric power
by free sheaves of modules.** For `n ≥ 1` the complex of Tag 01CJ

`M₂ ⊗ Sym^{n-1}(M₁) ⟶ Symⁿ(M₁) ⟶ Symⁿ(M)`

is exact at the middle term, its second map is an epimorphism, and its first two terms are free
sheaves of modules — of finite rank when `I₂` and `I₁` are finite, which is recorded as an
implication so that the statement itself needs no finiteness hypothesis. -/
theorem exists_free_symmetricPower_presentation (hS : S.Exact) (hg : Epi S.g)
    (A₂ : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier) S.X₂)
    (A₃ : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier) S.X₃)
    (I₂ I₁ : Type u)
    (e₂ : S.X₁ ≅ _root_.SheafOfModules.free
      (R := toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf) I₂)
    (e₁ : S.X₂ ≅ _root_.SheafOfModules.free
      (R := toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf) I₁)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (T : ShortComplex (SheafOfModules.{u}
        (toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf))) (J K : Type u),
      (Finite I₂ → Finite I₁ → Finite J) ∧ (Finite I₁ → Finite K) ∧
      T.X₁ = ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj S.X₁).obj
          (A₂.symmetricPower (n - 1)) ∧
      T.X₂ = A₂.symmetricPower n ∧
      T.X₃ = A₃.symmetricPower n ∧
      T.Exact ∧ Epi T.g ∧
      Nonempty (T.X₁ ≅ _root_.SheafOfModules.free
        (R := toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf) J) ∧
      Nonempty (T.X₂ ≅ _root_.SheafOfModules.free
        (R := toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf) K) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  have _ := hg
  have hex := _root_.SheafOfModules.SymPresentation.symmetricPresentation_exact
    (A' := A₂.symmetric) (B' := A₃.symmetric) A₂.symmetricGenerator A₃.symmetricGenerator
    A₂.symmetric_isSymmetricAlgebra A₃.symmetric_isSymmetricAlgebra S.f S.g S.zero hS m
  refine ⟨_, I₂ × ↥{d : I₁ →₀ ℕ | d.degree = m}, ↥{d : I₁ →₀ ℕ | d.degree = m + 1},
    fun h₂ h₁ => ?_, fun h₁ => ?_, rfl, rfl, rfl,
    hex.1,
    hex.2,
    ⟨tensorIsoFree (Opens.grothendieckTopology X.carrier) e₂
      (symmetricPowerFreeIsoOfIsoAnyIndex (Opens.grothendieckTopology X.carrier) I₁ m A₂ e₁)⟩,
    ⟨symmetricPowerFreeIsoOfIsoAnyIndex
      (Opens.grothendieckTopology X.carrier) I₁ (m + 1) A₂ e₁⟩⟩
  · have := h₂
    have := h₁
    exact inferInstance
  · have := h₁
    exact inferInstance

/-- **An exact presentation by free sheaves of modules presents every positive exterior power by
free sheaves of modules.** The exterior half of
`Stacks.SheafOfModules.exists_free_symmetricPower_presentation`: for `n ≥ 1` the complex

`M₂ ⊗ ⋀^{n-1}(M₁) ⟶ ⋀ⁿ(M₁) ⟶ ⋀ⁿ(M)`

of Tag 01CJ is exact at the middle term, its second map is an epimorphism, and its first two
terms are free. -/
theorem exists_free_exteriorPower_presentation (hS : S.Exact) (hg : Epi S.g)
    (A₂ : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier) S.X₂)
    (A₃ : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier) S.X₃)
    (I₂ I₁ : Type u)
    (e₂ : S.X₁ ≅ _root_.SheafOfModules.free
      (R := toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf) I₂)
    (e₁ : S.X₂ ≅ _root_.SheafOfModules.free
      (R := toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf) I₁)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (T : ShortComplex (SheafOfModules.{u}
        (toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf))) (J K : Type u),
      (Finite I₂ → Finite I₁ → Finite J) ∧ (Finite I₁ → Finite K) ∧
      T.X₁ = ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj S.X₁).obj
          (A₂.exteriorPower (n - 1)) ∧
      T.X₂ = A₂.exteriorPower n ∧
      T.X₃ = A₃.exteriorPower n ∧
      T.Exact ∧ Epi T.g ∧
      Nonempty (T.X₁ ≅ _root_.SheafOfModules.free
        (R := toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf) J) ∧
      Nonempty (T.X₂ ≅ _root_.SheafOfModules.free
        (R := toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf) K) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  have _ := hg
  let _ : LinearOrder I₁ := IsWellOrder.linearOrder WellOrderingRel
  have hex := _root_.SheafOfModules.ExtPresentation.exteriorPresentation_exact
    (A' := A₂.exterior) (B' := A₃.exterior) A₂.exteriorGenerator A₃.exteriorGenerator
    A₂.exterior_isExteriorAlgebra A₃.exterior_isExteriorAlgebra S.g S.f S.zero hS m
  refine ⟨_, I₂ × ↥(Set.powersetCard I₁ m), ↥(Set.powersetCard I₁ (m + 1)),
    fun h₂ h₁ => ?_, fun h₁ => ?_, rfl, rfl, rfl,
    hex.1,
    hex.2,
    ⟨tensorIsoFree (Opens.grothendieckTopology X.carrier) e₂
      (exteriorPowerFreeIsoOfIsoAnyIndex (Opens.grothendieckTopology X.carrier) I₁ m A₂ e₁)⟩,
    ⟨exteriorPowerFreeIsoOfIsoAnyIndex
      (Opens.grothendieckTopology X.carrier) I₁ (m + 1) A₂ e₁⟩⟩
  · have := h₂
    have := h₁
    exact inferInstance
  · have := h₁
    exact inferInstance

end General

/-! ### The four consumer forms, for the chosen package of algebras -/

section RingedSpace

variable {X : RingedSpace.{u, u}} {S : ShortComplex (SheafOfModules.{u} (structureSheafRing X))}

/-- **The symmetric powers of a sheaf of modules with a free presentation have free
presentations in every positive degree**, for the chosen package of algebras
`SheafOfModules.ringedSpaceAlgebras`. -/
theorem symmetricPower_freePresentation (hS : S.Exact) (hg : Epi S.g) (I₂ I₁ : Type u)
    (e₂ : S.X₁ ≅ _root_.SheafOfModules.free (R := structureSheafRing X) I₂)
    (e₁ : S.X₂ ≅ _root_.SheafOfModules.free (R := structureSheafRing X) I₁)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (T : ShortComplex (SheafOfModules.{u} (structureSheafRing X))) (J K : Type u),
      T.X₁ = ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj S.X₁).obj
          ((_root_.SheafOfModules.ringedSpaceAlgebras X S.X₂).symmetricPower (n - 1)) ∧
      T.X₂ = (_root_.SheafOfModules.ringedSpaceAlgebras X S.X₂).symmetricPower n ∧
      T.X₃ = (_root_.SheafOfModules.ringedSpaceAlgebras X S.X₃).symmetricPower n ∧
      T.Exact ∧ Epi T.g ∧
      Nonempty (T.X₁ ≅ _root_.SheafOfModules.free (R := structureSheafRing X) J) ∧
      Nonempty (T.X₂ ≅ _root_.SheafOfModules.free (R := structureSheafRing X) K) := by
  obtain ⟨T, J, K, -, -, h₁, h₂, h₃, hex, hepi, hJ, hK⟩ :=
    exists_free_symmetricPower_presentation hS hg
      (_root_.SheafOfModules.ringedSpaceAlgebras X S.X₂)
      (_root_.SheafOfModules.ringedSpaceAlgebras X S.X₃) I₂ I₁ e₂ e₁ n hn
  exact ⟨T, J, K, h₁, h₂, h₃, hex, hepi, hJ, hK⟩

/-- **The exterior powers of a sheaf of modules with a free presentation have free presentations
in every positive degree**, for the chosen package of algebras
`SheafOfModules.ringedSpaceAlgebras`. -/
theorem exteriorPower_freePresentation (hS : S.Exact) (hg : Epi S.g) (I₂ I₁ : Type u)
    (e₂ : S.X₁ ≅ _root_.SheafOfModules.free (R := structureSheafRing X) I₂)
    (e₁ : S.X₂ ≅ _root_.SheafOfModules.free (R := structureSheafRing X) I₁)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (T : ShortComplex (SheafOfModules.{u} (structureSheafRing X))) (J K : Type u),
      T.X₁ = ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj S.X₁).obj
          ((_root_.SheafOfModules.ringedSpaceAlgebras X S.X₂).exteriorPower (n - 1)) ∧
      T.X₂ = (_root_.SheafOfModules.ringedSpaceAlgebras X S.X₂).exteriorPower n ∧
      T.X₃ = (_root_.SheafOfModules.ringedSpaceAlgebras X S.X₃).exteriorPower n ∧
      T.Exact ∧ Epi T.g ∧
      Nonempty (T.X₁ ≅ _root_.SheafOfModules.free (R := structureSheafRing X) J) ∧
      Nonempty (T.X₂ ≅ _root_.SheafOfModules.free (R := structureSheafRing X) K) := by
  obtain ⟨T, J, K, -, -, h₁, h₂, h₃, hex, hepi, hJ, hK⟩ :=
    exists_free_exteriorPower_presentation hS hg
      (_root_.SheafOfModules.ringedSpaceAlgebras X S.X₂)
      (_root_.SheafOfModules.ringedSpaceAlgebras X S.X₃) I₂ I₁ e₂ e₁ n hn
  exact ⟨T, J, K, h₁, h₂, h₃, hex, hepi, hJ, hK⟩

/-- **A finite free presentation gives finite free symmetric-power presentations in every
positive degree**, on the same ringed space. -/
theorem symmetricPower_finiteFreePresentation (hS : S.Exact) (hg : Epi S.g) (I₂ I₁ : Type u)
    [Finite I₂] [Finite I₁]
    (e₂ : S.X₁ ≅ _root_.SheafOfModules.free (R := structureSheafRing X) I₂)
    (e₁ : S.X₂ ≅ _root_.SheafOfModules.free (R := structureSheafRing X) I₁)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (T : ShortComplex (SheafOfModules.{u} (structureSheafRing X))) (J K : Type u),
      Finite J ∧ Finite K ∧
      T.X₁ = ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj S.X₁).obj
          ((_root_.SheafOfModules.ringedSpaceAlgebras X S.X₂).symmetricPower (n - 1)) ∧
      T.X₂ = (_root_.SheafOfModules.ringedSpaceAlgebras X S.X₂).symmetricPower n ∧
      T.X₃ = (_root_.SheafOfModules.ringedSpaceAlgebras X S.X₃).symmetricPower n ∧
      T.Exact ∧ Epi T.g ∧
      Nonempty (T.X₁ ≅ _root_.SheafOfModules.free (R := structureSheafRing X) J) ∧
      Nonempty (T.X₂ ≅ _root_.SheafOfModules.free (R := structureSheafRing X) K) := by
  obtain ⟨T, J, K, hJfin, hKfin, h₁, h₂, h₃, hex, hepi, hJ, hK⟩ :=
    exists_free_symmetricPower_presentation hS hg
      (_root_.SheafOfModules.ringedSpaceAlgebras X S.X₂)
      (_root_.SheafOfModules.ringedSpaceAlgebras X S.X₃) I₂ I₁ e₂ e₁ n hn
  exact ⟨T, J, K, hJfin inferInstance inferInstance, hKfin inferInstance,
    h₁, h₂, h₃, hex, hepi, hJ, hK⟩

/-- **A finite free presentation gives finite free exterior-power presentations in every positive
degree**, on the same ringed space. -/
theorem exteriorPower_finiteFreePresentation (hS : S.Exact) (hg : Epi S.g) (I₂ I₁ : Type u)
    [Finite I₂] [Finite I₁]
    (e₂ : S.X₁ ≅ _root_.SheafOfModules.free (R := structureSheafRing X) I₂)
    (e₁ : S.X₂ ≅ _root_.SheafOfModules.free (R := structureSheafRing X) I₁)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (T : ShortComplex (SheafOfModules.{u} (structureSheafRing X))) (J K : Type u),
      Finite J ∧ Finite K ∧
      T.X₁ = ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj S.X₁).obj
          ((_root_.SheafOfModules.ringedSpaceAlgebras X S.X₂).exteriorPower (n - 1)) ∧
      T.X₂ = (_root_.SheafOfModules.ringedSpaceAlgebras X S.X₂).exteriorPower n ∧
      T.X₃ = (_root_.SheafOfModules.ringedSpaceAlgebras X S.X₃).exteriorPower n ∧
      T.Exact ∧ Epi T.g ∧
      Nonempty (T.X₁ ≅ _root_.SheafOfModules.free (R := structureSheafRing X) J) ∧
      Nonempty (T.X₂ ≅ _root_.SheafOfModules.free (R := structureSheafRing X) K) := by
  obtain ⟨T, J, K, hJfin, hKfin, h₁, h₂, h₃, hex, hepi, hJ, hK⟩ :=
    exists_free_exteriorPower_presentation hS hg
      (_root_.SheafOfModules.ringedSpaceAlgebras X S.X₂)
      (_root_.SheafOfModules.ringedSpaceAlgebras X S.X₃) I₂ I₁ e₂ e₁ n hn
  exact ⟨T, J, K, hJfin inferInstance inferInstance, hKfin inferInstance,
    h₁, h₂, h₃, hex, hepi, hJ, hK⟩

end RingedSpace

end Stacks.SheafOfModules

end
