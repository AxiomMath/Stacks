module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BoundedAbove
public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleApproximation
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of a derived tensor product above a degree

Let `(C, O)` be a ringed site, let `α : K ⟶ L` be a map of `D(Mod(O))`, let `F` be a sheaf of
`O`-modules and let `n` be an integer.

1. If `H^i(α)` is an isomorphism for every `i ≥ n`, then so is
   `H^i(α ⊗_O^{L} 1_F)`.
2. If `H^i(α)` is an isomorphism for every `i > n` and a surjection for `i = n`, then
   `H^i(α ⊗_O^{L} 1_F)` is an isomorphism for every `i > n` and a surjection for `i = n`.

Both are read off the third vertex of the cocone triangle of `α`. Saying that `H^i(α)` is an
isomorphism above `n` and a surjection at `n` is saying that that vertex lies in
`D^{≤ n - 1}(Mod(O))`; the derived tensor product is right t-exact, so tensoring keeps it
there; and the same dictionary read backwards is part (2). Part (1) is part (2) together with
injectivity in degree `n`, which needs one more step: the connecting map
`H^{n-1}(C ⊗^{L} F) ⟶ H^n(K ⊗^{L} F)` vanishes because `H^{n-1}(L ⊗^{L} F) ⟶ H^{n-1}(C ⊗^{L} F)`
is surjective, and that in turn is part (2) applied to the composite
`τ^{<n} L ⟶ L ⟶ C`, whose source and target both have vanishing cohomology above `n - 1`.

## Main definitions

* `Stacks.DerivedTensor.RingedSite.derivedTensorSingle`: the functor `- ⊗_O^{L} F` on
  `D(Mod(O))` attached to a sheaf of `O`-modules `F`.

## Main results

* `Stacks.DerivedTensor.RingedSite.isLE_derivedTensorSingle`: `- ⊗_O^{L} F` preserves
  `D^{≤ m}(Mod(O))`.
* `Stacks.DerivedTensor.RingedSite.isIso_homologyMap_derivedTensorSingle_of_isIso`: part (1).
* `Stacks.DerivedTensor.RingedSite.isIso_homologyMap_derivedTensorSingle_of_epi` and
  `Stacks.DerivedTensor.RingedSite.epi_homologyMap_derivedTensorSingle`: the two conclusions of
  part (2), with `Stacks.DerivedTensor.RingedSite.approximation_derivedTensorSingle` the single
  statement they are projections of.

## Implementation notes

The source states both parts for a map of `D^-(O)`. **Neither part needs the boundedness**: the
third vertex of the cocone triangle is bounded above by the hypotheses on `α` alone, by the long
exact cohomology sequence, and right t-exactness of the derived tensor product asks nothing of
`K` or `L` beyond that. So the hypothesis `K, L ∈ D^-(O)` is dropped from both parts, which
generalizes the source statement rather than weakening it.

Tensoring with `F` means tensoring with `F` placed in degree zero, i.e. with
`DerivedCategory.singleFunctor (Modules O) 0 |>.obj F`, and `α ⊗_O^{L} 1_F` is the image of `α`
under the partial functor `derivedTensorSingle` the derived tensor bifunctor of Stacks 06YU
restricts to there. That functor is exact, which is the `exact_left` field of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`, so it carries the cocone triangle of
`α` to a distinguished triangle.

The universes are those of `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` and the
narrowing of the site to a small one with all four universes equal is inherited from it; nothing
is narrowed here.

## References

* [Stacks Project, Tag 0DIV](https://stacks.math.columbia.edu/tag/0DIV)
* [Stacks Project, Tag 05TC](https://stacks.math.columbia.edu/tag/05TC)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u d

namespace Stacks.DerivedTensor.RingedSite

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Modules R)]
variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- Derived tensoring with a sheaf of `O`-modules `F`, regarded as a complex concentrated in
degree zero: the functor `- ⊗_O^{L} F` on `D(Mod(O))`. It is the partial functor of the derived
tensor bifunctor of Stacks 06YU at `F[0]`. -/
abbrev derivedTensorSingle (F : Modules R) : DerivedModules R ⥤ DerivedModules R :=
  (derivedTensorProductFunctor R).flip.obj
    ((DerivedCategory.singleFunctor (Modules R) 0).obj F)

/-- **`- ⊗_O^{L} F` preserves bounded above objects**, with no shift of the bound: a sheaf of
`O`-modules in degree zero lies in `D^{≤ 0}(Mod(O))`, so right t-exactness of the derived
tensor product adds nothing to the bound. -/
theorem isLE_derivedTensorSingle (F : Modules R) (M : DerivedModules R) (m : ℤ) [M.IsLE m] :
    ((derivedTensorSingle R F).obj M).IsLE m := by
  have h := isLE_derivedTensorProductFunctor R M
    ((DerivedCategory.singleFunctor (Modules R) 0).obj F) m 0
  rw [add_zero] at h
  exact h

/-- **Derived tensoring preserves a cohomological approximation.** If `H^i(α)` is an
isomorphism in every degree `> n` and a surjection in degree `n`, then the same holds of
`H^i(α ⊗_O^{L} 1_F)`.

The third vertex of the cocone triangle of `α` lies in `D^{≤ n - 1}(Mod(O))` precisely because
of the hypotheses, derived tensoring keeps it there, and the image triangle is distinguished
because `- ⊗_O^{L} F` is exact; so the dictionary read backwards gives both conclusions at
once. -/
theorem approximation_derivedTensorSingle {K L : DerivedModules R} (α : K ⟶ L) (F : Modules R)
    (n : ℤ)
    (hiso : ∀ i : ℤ, n < i → IsIso ((DerivedCategory.homologyFunctor (Modules R) i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor (Modules R) n).map α)) :
    (∀ i : ℤ, n < i → IsIso ((DerivedCategory.homologyFunctor (Modules R) i).map
        ((derivedTensorSingle R F).map α))) ∧
      Epi ((DerivedCategory.homologyFunctor (Modules R) n).map
        ((derivedTensorSingle R F).map α)) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle α
  have hZLE : Z.IsLE (n - 1) :=
    DerivedCategory.triangle_obj₃_isLE_of_approximation _ hT n hiso hepi
  exact DerivedCategory.approximation_of_triangle_isLE _
    ((derivedTensorSingle R F).map_distinguished _ hT) n (isLE_derivedTensorSingle R F Z (n - 1))

/-- **Stacks 0DIV (2), the isomorphisms.** If `H^i(α)` is an isomorphism in every degree `> n`
and a surjection in degree `n`, then `H^i(α ⊗_O^{L} 1_F)` is an isomorphism in every degree
`> n`. -/
@[stacks 0DIV "tensoring keeps the isomorphisms above the degree"]
theorem isIso_homologyMap_derivedTensorSingle_of_epi
    {K L : DerivedModules R} (α : K ⟶ L) (F : Modules R) (n : ℤ)
    (hiso : ∀ i : ℤ, n < i → IsIso ((DerivedCategory.homologyFunctor (Modules R) i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor (Modules R) n).map α))
    (i : ℤ) (hi : n < i) :
    IsIso ((DerivedCategory.homologyFunctor (Modules R) i).map
      ((derivedTensorSingle R F).map α)) :=
  (approximation_derivedTensorSingle R α F n hiso hepi).1 i hi

/-- **Stacks 0DIV (2), the surjection.** If `H^i(α)` is an isomorphism in every degree `> n`
and a surjection in degree `n`, then `H^n(α ⊗_O^{L} 1_F)` is a surjection. -/
@[stacks 0DIV "tensoring keeps the surjection in the degree"]
theorem epi_homologyMap_derivedTensorSingle
    {K L : DerivedModules R} (α : K ⟶ L) (F : Modules R) (n : ℤ)
    (hiso : ∀ i : ℤ, n < i → IsIso ((DerivedCategory.homologyFunctor (Modules R) i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor (Modules R) n).map α)) :
    Epi ((DerivedCategory.homologyFunctor (Modules R) n).map
      ((derivedTensorSingle R F).map α)) :=
  (approximation_derivedTensorSingle R α F n hiso hepi).2

/-- **Stacks 0DIV (1).** If `H^i(α)` is an isomorphism in every degree `≥ n`, then so is
`H^i(α ⊗_O^{L} 1_F)`.

Above `n` this is part (2). In degree `n` surjectivity is again part (2), and injectivity comes
from the vanishing of the connecting map `H^{n-1}(C ⊗^{L} F) ⟶ H^n(K ⊗^{L} F)` of the tensored
triangle, equivalently from surjectivity of `H^{n-1}(L ⊗^{L} F) ⟶ H^{n-1}(C ⊗^{L} F)`. That is
part (2) applied in degree `n - 1` to `τ^{<n} L ⟶ L ⟶ C`: this composite is surjective on
`H^{n-1}` — the truncation map is an isomorphism there and `H^{n-1}(L) ⟶ H^{n-1}(C)` is
surjective because `H^n(α)` is injective — and it is an isomorphism on cohomology above
`n - 1` for the trivial reason that both its source and its target vanish there. -/
@[stacks 0DIV "tensoring keeps the isomorphisms in all degrees at least the bound"]
theorem isIso_homologyMap_derivedTensorSingle_of_isIso
    {K L : DerivedModules R} (α : K ⟶ L) (F : Modules R) (n : ℤ)
    (hα : ∀ i : ℤ, n ≤ i → IsIso ((DerivedCategory.homologyFunctor (Modules R) i).map α))
    (i : ℤ) (hi : n ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor (Modules R) i).map
      ((derivedTensorSingle R F).map α)) := by
  have hαiso := hα n le_rfl
  have hαepi : Epi ((DerivedCategory.homologyFunctor (Modules R) n).map α) := inferInstance
  have hαmono : Mono ((DerivedCategory.homologyFunctor (Modules R) n).map α) := inferInstance
  obtain ⟨hgt, hepi⟩ :=
    approximation_derivedTensorSingle R α F n (fun j hj => hα j (by omega)) hαepi
  by_cases hlt : n < i
  · exact hgt i hlt
  rw [show i = n from by omega]
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle α
  have hij : n - 1 + 1 = n := by omega
  have hZLE : Z.IsLE (n - 1) :=
    DerivedCategory.triangle_obj₃_isLE_of_approximation _ hT n
      (fun j hj => hα j (by omega)) hαepi
  -- For a distinguished triangle, `H^n(mor₁)` is mono iff `H^{n-1}(mor₂)` is epi.
  have key : ∀ T ∈ distTriang (DerivedModules R),
      Mono ((DerivedCategory.homologyFunctor (Modules R) n).map T.mor₁) ↔
        Epi ((DerivedCategory.homologyFunctor (Modules R) (n - 1)).map T.mor₂) := fun T hT =>
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (n - 1) n hij).trans
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT (n - 1) n hij).symm
  -- `H^{n-1}(L) ⟶ H^{n-1}(C)` is surjective because `H^n(α)` is injective.
  have hepig : Epi ((DerivedCategory.homologyFunctor (Modules R) (n - 1)).map g) :=
    (key (Triangle.mk α g h) hT).1 hαmono
  -- So is its restriction along the truncation `τ^{<n} L ⟶ L`.
  have hιiso : IsIso ((DerivedCategory.homologyFunctor (Modules R) (n - 1)).map
      ((DerivedCategory.TStructure.t.truncLTι n).app L)) :=
    DerivedCategory.isIso_homologyMap_truncLTι_app n (n - 1) (by omega) L
  have hcomp : Epi ((DerivedCategory.homologyFunctor (Modules R) (n - 1)).map
      ((DerivedCategory.TStructure.t.truncLTι n).app L ≫ g)) := by
    rw [Functor.map_comp]
    infer_instance
  -- Part (2) in degree `n - 1`, applied to that composite.
  obtain ⟨-, hEpiComposite⟩ := approximation_derivedTensorSingle R
    ((DerivedCategory.TStructure.t.truncLTι n).app L ≫ g) F (n - 1)
    (fun j hj => (DerivedCategory.isZero_of_isLE
        ((DerivedCategory.TStructure.t.truncLT n).obj L) (n - 1) j hj).isIso
      (DerivedCategory.isZero_of_isLE Z (n - 1) j hj) _) hcomp
  have hEpiGg : Epi ((DerivedCategory.homologyFunctor (Modules R) (n - 1)).map
      ((derivedTensorSingle R F).map g)) := by
    simp only [Functor.map_comp] at hEpiComposite
    exact epi_of_epi ((DerivedCategory.homologyFunctor (Modules R) (n - 1)).map
      ((derivedTensorSingle R F).map ((DerivedCategory.TStructure.t.truncLTι n).app L))) _
  have hmono : Mono ((DerivedCategory.homologyFunctor (Modules R) n).map
      ((derivedTensorSingle R F).map α)) :=
    (key _ ((derivedTensorSingle R F).map_distinguished _ hT)).2 hEpiGg
  exact isIso_of_mono_of_epi _

end Stacks.DerivedTensor.RingedSite

end
