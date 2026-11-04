module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationTowerConvergence
import StacksCore.Tactic.StacksAttribute

/-!
# Convergence of the truncation tower under degree-dependent cohomological bounds

Let `S = (C, O)` be a ringed site and let `E` be an object of the derived category of
`O`-modules. Suppose a subset `B` of the objects of `C` covers every object, and that there is a
function `p : ℤ → ℤ`, depending only on the total degree, with `H^p(V, H^{m - p}(E)) = 0` for
every `V ∈ B` and all `p > p(m)`. Then the canonical map from `E` to the derived limit of its
truncation tower `n ↦ τ_{≥ -n} E` is an isomorphism.

This is the specialisation of `Stacks.Cohomology.isIso_to_isDerivedLimit_truncationGETower`
(Tag 0D6M) in which the degree bound does not depend on the object `V`: take
`p(V, m) = p(m)`, and for the cofinal system of coverings of `V ∈ B` take all coverings whose
members lie in `B`. That system is cofinal because an arbitrary covering of `V` can be refined
by binding it with coverings of its own members drawn from `B`, and the bound hypothesis then
holds on every member of every such covering.

## Main results

* `Stacks.Cohomology.isIso_to_isDerivedLimit_truncGETower_of_degreeBound`: the convergence
  criterion under a degree-dependent bound.

## Implementation notes

A covering family is represented by a `PreZeroHypercover`, which is a covering exactly when the
sieve it generates lies in the topology. Cohomology over an object is
`Stacks.Cohomology.moduleCohomology`, applied to the structure sheaf with commutativity
forgotten, and the truncation tower is `Stacks.DerivedLimit.truncGETower`, as in Tag 0D6M.
Because the predicate "`L` is a derived limit" does not remember the first arrow of its
distinguished triangle, the statement is given for a presentation of that triangle together with
a map whose composites with all product projections are the canonical truncation maps; this pins
down the canonical map of the source rather than an arbitrary map to a derived limit.

The site objects, the site morphisms and the sections of the structure sheaf all share the
single universe `u` here, whereas Tag 0D6M keeps them independent. A consumer needing several
universes should cite `Stacks.Cohomology.isIso_to_isDerivedLimit_truncationGETower` directly.

## References

* [Stacks Project, Tag 08U3](https://stacks.math.columbia.edu/tag/08U3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace Stacks.Cohomology

attribute [local instance] HasDerivedCategory.standard

/-- If every object has a covering by members of `B`, every covering is refined by a covering
by members of `B`. -/
private theorem exists_covering_in_set_hom {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {B : Set C}
    (hB : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{u} U, 𝒰.sieve₀ ∈ J U ∧ ∀ i, B (𝒰.X i))
    {V : C} {𝒰 : PreZeroHypercover.{u} V} (h𝒰 : 𝒰.sieve₀ ∈ J V) :
    ∃ 𝒱 : PreZeroHypercover.{u} V, (𝒱.sieve₀ ∈ J V ∧ ∀ i, B (𝒱.X i)) ∧ Nonempty (𝒱.Hom 𝒰) := by
  choose F hF using fun i : 𝒰.I₀ => hB (𝒰.X i)
  refine ⟨𝒰.bind F, ⟨?_, ?_⟩, ⟨?_⟩⟩
  · have hbind : Sieve.generate
        (Presieve.bindOfArrows 𝒰.X 𝒰.f (fun i => (F i).presieve₀)) ∈ J V :=
      J.bindOfArrows h𝒰 (fun i => by
        simpa [PreZeroHypercover.presieve₀] using (hF i).1)
    simpa [PreZeroHypercover.bind, PreZeroHypercover.sieve₀,
      Presieve.bindOfArrows_ofArrows] using hbind
  · exact fun ij => (hF ij.1).2 ij.2
  · exact ⟨(fun ij => ij.1), (fun ij => (F ij.1).f ij.2), by intro ij; rfl⟩

/-- Degree-dependent bounds for cohomology on a locally covering class imply that the canonical
map to the derived limit of the lower-truncation tower is an isomorphism.

This is a variant of [Stacks, Tag 08U3]: the enough-injectives and product hypotheses below are
not hypotheses of the source, and they are avoidable.  The full statement is
`Stacks.Cohomology.DegreeBound.isIso_to_isDerivedLimit_truncGETower_of_degreeBound`, which
discharges them by taking the module universe large enough to contain the site and the structure
rings.  This single-universe form is kept for the consumers that are already stated at it. -/
@[stacks 08U3 "variant: the single-universe form, for a ringed site whose module category has
enough injectives and the countable product of the truncation tower; the tag, with neither of
these, is Stacks.Cohomology.DegreeBound.isIso_to_isDerivedLimit_truncGETower_of_degreeBound"]
theorem isIso_to_isDerivedLimit_truncGETower_of_degreeBound
    (S : AlgebraicGeometry.RingedSite.{u, u, u})
    [HasSheafify S.J AddCommGrpCat.{u}]
    [S.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))]
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)))
    (degreeBound : ℤ → ℤ) (B : Set S.C)
    (basisCover : ∀ U : S.C, ∃ 𝒰 : PreZeroHypercover.{u} U,
      𝒰.sieve₀ ∈ S.J U ∧ ∀ i, B (𝒰.X i))
    (vanishing : ∀ (V : S.C), B V → ∀ (p : ℕ) (m : ℤ),
      degreeBound m < (p : ℤ) →
        IsZero (moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf S.O) V p
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
            (m - (p : ℤ))).obj E)))
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)))
    [HasProduct fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) E).obj ⟨n⟩]
    (q : L ⟶ ∏ᶜ fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) E).obj ⟨n⟩)
    (hL : ∃ δ :
      (∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) E).obj ⟨n⟩) ⟶
          L⟦(1 : ℤ)⟧,
      Triangle.mk q (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) E).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦
            (Stacks.DerivedLimit.truncGETower
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) E).obj ⟨n⟩)
              (n + 1) ≫
            (Stacks.DerivedLimit.truncGETower
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) E).map
              (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))))
    (c : E ⟶ L)
    (hc : ∀ n : ℕ, c ≫ q ≫ Pi.π
      (fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) E).obj ⟨n⟩) n =
      (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) :
    IsIso c := by
  classical
  rcases hL with ⟨δ, hL⟩
  exact isIso_to_isDerivedLimit_truncationGETower
    (Stacks.SheafOfModules.Tensor.ringSheaf S.O) E B basisCover (fun _ _ => degreeBound)
    (fun V _ => {𝒰 | 𝒰.sieve₀ ∈ S.J V ∧ ∀ i, B (𝒰.X i)})
    (by intro V hV 𝒰 h𝒰; exact h𝒰.1)
    (fun _ _ _ h𝒰 => exists_covering_in_set_hom basisCover h𝒰)
    (by intro V hV 𝒰 h𝒰 i p m hm; exact vanishing _ (h𝒰.2 i) p m hm)
    L c q δ hL hc

end Stacks.Cohomology

end

-- ===== merged from StacksDraft.Ch21.Sec23.TruncationConvergenceUniformBound =====

/-!
# Convergence of the truncation tower under a uniform cohomological bound

Let `(C, O)` be a ringed site and let `E` be an object of the derived category of `O`-modules.
Suppose a subset `B` of the objects of `C` covers every object, and that there is a single
integer `d ≥ 0` with `H^p(V, H^q(E)) = 0` for every `V ∈ B`, every `p > d` and every `q < 0`.
Then the canonical map from `E` to the derived limit of its truncation tower `n ↦ τ_{≥ -n} E` is
an isomorphism.

This is the uniform-bound specialisation of
`Stacks.Cohomology.isIso_to_isDerivedLimit_truncationGETower` (Tag 0D6M): the degree-dependent
bound `p(V, m) = d + max 0 m` works, because a vanishing statement for `p > d + max 0 m` in total
degree `m` only ever asks about `H^{m - p}(E)` with `m - p < 0`. The cofinal system of coverings
of `V ∈ B` is taken to be all coverings whose members lie in `B`, which is cofinal because any
covering can be refined by binding it with coverings of its own members drawn from `B`.

## Main results

* `Stacks.Cohomology.isIso_to_isDerivedLimit_truncGETower_of_cohomology_vanishing`: the
  convergence criterion under a uniform bound.

## Implementation notes

A covering family is represented by a `PreZeroHypercover`, which is a covering exactly when the
sieve it generates lies in the topology. Cohomology over an object is
`Stacks.Cohomology.moduleCohomology` and the truncation tower is
`Stacks.DerivedLimit.truncGETower`, as in Tag 0D6M. Because the predicate "`L` is a derived
limit" does not remember the first arrow of its distinguished triangle, the statement is given
for a presentation of that triangle together with a map whose composites with all product
projections are the canonical truncation maps; this pins down the canonical map of the source.

Unlike Tag 0D6M, which is polymorphic in four independent universes (site objects, site
morphisms, rings, modules), this statement collapses all of them to a single universe `u`. That
narrowness is deliberate and is the shape the tagged statement fixes; a consumer that needs several
universes should cite `Stacks.Cohomology.isIso_to_isDerivedLimit_truncationGETower` directly
rather than this specialisation.

## References

* [Stacks Project, Tag 0D6P](https://stacks.math.columbia.edu/tag/0D6P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace Stacks.Cohomology

attribute [local instance] HasDerivedCategory.standard

/-- Uniform boundedness of the cohomology of the negative cohomology sheaves on a locally
covering class of objects implies that the canonical map to every derived limit of the lower
truncation tower is an isomorphism.

This is the content of [Stacks, Tag 0D6P], but it is not the registration of that tag: the four
class hypotheses below are not hypotheses of the source, and they are avoidable.  The tag is
carried by
`Stacks.Cohomology.UniformBound.isIso_to_isDerivedLimit_truncGETower_of_vanishing_uniform`,
which discharges all four by taking the module universe large enough to contain the site and the
structure rings.  This single-universe form is kept for the consumers that are already stated at
it. -/
theorem isIso_to_isDerivedLimit_truncGETower_of_cohomology_vanishing
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [EnoughInjectives (SheafOfModules.{u} O)]
    (E : DerivedCategory (SheafOfModules.{u} O))
    (d : ℤ) (hd : 0 ≤ d) (B : Set C)
    (hB : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{u} U,
      𝒰.sieve₀ ∈ J U ∧ ∀ i, B (𝒰.X i))
    (hvan : ∀ (V : C), B V → ∀ (p : ℕ), d < (p : ℤ) → ∀ (q : ℤ), q < 0 →
      IsZero (moduleCohomology O V p
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) q).obj E)))
    (L : DerivedCategory (SheafOfModules.{u} O))
    [HasProduct fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩)
    (hL : ∃ δ :
      (∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) (n + 1) ≫
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).map
              (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang
          (DerivedCategory (SheafOfModules.{u} O)))
    (c : E ⟶ L)
    (hc : ∀ n : ℕ, c ≫ p ≫ Pi.π
      (fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n =
      (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) :
    IsIso c := by
  classical
  rcases hL with ⟨δ, hL⟩
  exact isIso_to_isDerivedLimit_truncationGETower
    O E B hB (fun _ _ m => d + max 0 m)
    (fun V _ => {𝒰 | 𝒰.sieve₀ ∈ J V ∧ ∀ i, B (𝒰.X i)})
    (by intro V hV 𝒰 h𝒰; exact h𝒰.1)
    (fun _ _ _ h𝒰 => exists_covering_in_set_hom hB h𝒰)
    (by intro V hV 𝒰 h𝒰 i p m hm; exact hvan _ (h𝒰.2 i) p (by omega) _ (by omega))
    L c p δ hL hc

end Stacks.Cohomology

end
