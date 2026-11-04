module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.ComparisonDiagram
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CohomologyPresheafSheafification
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology sheaves of a derived inverse limit on a ringed space

Let `X` be a topological space, let `O` be a sheaf of rings on it, let `(Kₙ)` be an inverse
system in the unbounded derived category `D(O)` and let `L` be a derived limit of it, presented
by the structural map `p : L ⟶ ∏ Kₙ` together with the distinguished triangle whose second map
is the difference map `(xₙ) ↦ (xₙ - fₙ₊₁(xₙ₊₁))`. Fix a degree `m` and write, as in the source,
`Hᵐ` for the cohomology sheaf functor, `underline Hᵐ` for the cohomology presheaf functor
`K ↦ (U ↦ Hᵐ(U, K))` and `S` for sheafification.

Tag 0BKJ identifies `S (underline Hᵐ K)` with `Hᵐ(K)`, naturally in `K`; in the notation of the
source this says that `𝓗ᵐ_n` is the sheafification of `underline 𝓗ᵐ_n` and that `𝓗ᵐ` is the
sheafification of `underline 𝓗ᵐ`. The remark then records the square

```
underline 𝓗ᵐ        ⟶   𝓗ᵐ
      |                  |
      v                  v
lim underline 𝓗ᵐ_n  ⟶   lim 𝓗ᵐ_n
```

whose two vertical maps are induced by the structural maps `L ⟶ Kₙ`, whose top map is the Tag
0BKJ identification and whose bottom map is the comparison out of the sheafification of the
limit of the cohomology presheaves. That square, with the three maps pinned down by their
composites with the limit projections, is what is proved here.

The content is that the family `p ≫ πₙ` is a cone at all, which holds because `p` is the first
map of the derived-limit triangle, so its composite with the difference map vanishes; that is
`Stacks.Cohomology.DerivedLimitDiagram.comp_π_eq_comp_π_succ`, reused here.

## Main results

* `Stacks.Cohomology.DerivedLimits.sheafificationCohomologyPresheafSystemIso`: the cohomology
  sheaf `𝓗ᵐ_n` is the sheafification of the cohomology presheaf `underline 𝓗ᵐ_n`, naturally in
  `n`; the corresponding statement for `L` is the component of the Tag 0BKJ isomorphism at `L`.
* `Stacks.Cohomology.DerivedLimits.cohomologyDerivedLimitDiagram`: the three comparison maps and
  the commuting square they form with the Tag 0BKJ associated-sheaf isomorphism, which is the
  first assertion of Tag 0BKQ together with its diagram.

## Implementation notes

The three maps are existentially quantified but pinned down: each is required to have prescribed
composites with every limit projection, and a morphism into a limit is determined by those, so
the statement names a unique triple. The first two are the lifts of the cone `p ≫ πₙ`; the third
factors the sheafified limit of the cohomology presheaves through the limit of the cohomology
sheaves, which is where the Tag 0BKJ identification enters, and it is *not* asserted to be
invertible -- the source explicitly warns that `lim 𝓗ᵐ_n` need not be the sheafification of
`lim underline 𝓗ᵐ_n`.

The remaining assertion of Tag 0BKQ, the short exact sequences of Equation 0BKR over an open, is
`Stacks.Cohomology.DerivedLimits.exists_shortExact_limOne_cohomology_derivedLimit_family` in
`StacksFrontier/Topology/Sheaves/Cohomology/MayerVietorisAndLimits/DerivedLimits.lean`.

The cohomology presheaf is the one of Tag 0BKJ: `derivedSectionsPresheaf` is the unbounded right
derived functor of sections on all opens at once, so its degree-`m` homology is a presheaf of
`O`-modules whose value on an open `U` is `Hᵐ(U, K)`, which is
`Stacks.Cohomology.CohomologyPresheaf.cohomologyPresheafEvaluationIso`, the other Tag 0BKJ
registration. Taking sections on every open simultaneously rather than open by open is what
carries the restriction maps, hence what makes `underline 𝓗ᵐ` a presheaf at all.

The ring sheaf is an arbitrary sheaf of rings on the space rather than the structure sheaf of a
ringed space, as in Tag 0BKJ itself; a ringed space is the case `O = structureSheafRing X`.
Nothing else is assumed: the two `HasDerivedCategory` instances are choices of a model of the
derived category, not hypotheses, and existence of the derived functors involved comes from
K-injective resolutions of complexes of modules, so the statement carries no class hypothesis
that the source does not have.

The square is extracted from `exists_sheafificationComparisonSquare`, which asks only for a
functor into presheaves, a functor into sheaves, an identification of the sheafification of the
first with the second, and a cone in the source category. The ringed-site analogue of this
remark, Tag 0BKW in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedLimit/ComparisonDiagram.lean`, proves its
square by the same argument spelled out at its own `P`, `H`, `S` and `e`, and could be rewritten
to apply this lemma; that file is left untouched here, since its tag is not this one.

The difference map is written out as the explicit `Pi.lift` of the derived-limit triangle rather
than through `Stacks.DerivedLimit.inverseSystemDifference`; the two are the same term, and
spelling it out keeps the triangle appearing here the one the derived-limit hypotheses of the
neighbouring tags name.

## References

* [Stacks Project, Tag 0BKQ](https://stacks.math.columbia.edu/tag/0BKQ)
* [Stacks Project, Tag 0BKJ](https://stacks.math.columbia.edu/tag/0BKJ)
* [Stacks Project, Tag 0D60](https://stacks.math.columbia.edu/tag/0D60)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open Stacks.Cohomology.CohomologyPresheaf

namespace Stacks.Cohomology.DerivedLimits

universe wX wP u

/-- The comparison square attached to a cone over an inverse system indexed by `ℕᵒᵖ`, for a
functor `P` into a category of presheaves, a functor `H` into a category of sheaves, a
sheafification functor `S` and an identification `e : P ⋙ S ≅ H`.

The three maps are the lift of the cone along `P`, the lift of the cone along `H`, and the
comparison from the sheafification of the limit of the `P`-values to the limit of the
`H`-values; each is determined by its composites with the limit projections, and the square
they form with `e` commutes. -/
private theorem exists_sheafificationComparisonSquare
    {D : Type*} [Category* D] {Pres : Type*} [Category* Pres] {Shv : Type*} [Category* Shv]
    (P : D ⥤ Pres) (H : D ⥤ Shv) (S : Pres ⥤ Shv) (e : P ⋙ S ≅ H)
    (K : ℕᵒᵖ ⥤ D) (L : D) [HasLimit (K ⋙ P)] [HasLimit (K ⋙ H)]
    (f : ∀ n : ℕ, L ⟶ K.obj ⟨n⟩)
    (hf : ∀ n : ℕ, f n = f (n + 1) ≫ K.map (homOfLE (Nat.le_succ n)).op) :
    ∃ (a : P.obj L ⟶ limit (K ⋙ P))
      (b : H.obj L ⟶ limit (K ⋙ H))
      (c : S.obj (limit (K ⋙ P)) ⟶ limit (K ⋙ H)),
      (∀ n : ℕ, a ≫ limit.π (K ⋙ P) ⟨n⟩ = P.map (f n)) ∧
      (∀ n : ℕ, b ≫ limit.π (K ⋙ H) ⟨n⟩ = H.map (f n)) ∧
      (∀ n : ℕ, c ≫ limit.π (K ⋙ H) ⟨n⟩ =
        S.map (limit.π (K ⋙ P) ⟨n⟩) ≫ e.hom.app (K.obj ⟨n⟩)) ∧
      S.map a ≫ c = e.hom.app L ≫ b := by
  let c₀ : Cone K := Cone.mk L
    (NatTrans.ofOpSequence (F := (Functor.const ℕᵒᵖ).obj L) (G := K) f
      (fun n ↦ (Category.id_comp _).trans (hf n)))
  let cS : Cone (K ⋙ H) := Cone.mk (S.obj (limit (K ⋙ P)))
    (NatTrans.ofOpSequence
      (F := (Functor.const ℕᵒᵖ).obj (S.obj (limit (K ⋙ P)))) (G := K ⋙ H)
      (fun n ↦ S.map (limit.π (K ⋙ P) ⟨n⟩) ≫ e.hom.app (K.obj ⟨n⟩))
      (fun n ↦ by
        dsimp only [Functor.const_obj_map, Functor.comp_map]
        have hw := limit.w (K ⋙ P) (homOfLE (Nat.le_succ n)).op
        have hnat := e.hom.naturality (K.map (homOfLE (Nat.le_succ n)).op)
        simp only [Functor.comp_map] at hw hnat
        refine (Category.id_comp _).trans ?_
        rw [Category.assoc, ← hnat, ← Category.assoc, ← Functor.map_comp, hw]))
  let a : P.obj L ⟶ limit (K ⋙ P) := limit.lift (K ⋙ P) (P.mapCone c₀)
  let b : H.obj L ⟶ limit (K ⋙ H) := limit.lift (K ⋙ H) (H.mapCone c₀)
  let c : S.obj (limit (K ⋙ P)) ⟶ limit (K ⋙ H) := limit.lift (K ⋙ H) cS
  have ha : ∀ n : ℕ, a ≫ limit.π (K ⋙ P) ⟨n⟩ = P.map (f n) :=
    fun n ↦ limit.lift_π (P.mapCone c₀) ⟨n⟩
  have hb : ∀ n : ℕ, b ≫ limit.π (K ⋙ H) ⟨n⟩ = H.map (f n) :=
    fun n ↦ limit.lift_π (H.mapCone c₀) ⟨n⟩
  have hc : ∀ n : ℕ, c ≫ limit.π (K ⋙ H) ⟨n⟩ =
      S.map (limit.π (K ⋙ P) ⟨n⟩) ≫ e.hom.app (K.obj ⟨n⟩) := fun n ↦ limit.lift_π cS ⟨n⟩
  refine ⟨a, b, c, ha, hb, hc, ?_⟩
  refine limit.hom_ext fun j ↦ ?_
  obtain ⟨n⟩ := j
  rw [Category.assoc, hc n, Category.assoc, hb n, ← Category.assoc, ← Functor.map_comp, ha n]
  exact e.hom.naturality (f n)

/-- **Stacks 0BKQ, first assertion.** For an inverse system `(Kₙ)` in `D(O)` and a degree `m`,
the cohomology sheaf `𝓗ᵐ_n = Hᵐ(Kₙ)` is the sheafification of the cohomology presheaf
`underline 𝓗ᵐ_n : U ↦ Hᵐ(U, Kₙ)`, naturally in `n`: sheafifying the system of cohomology
presheaves of the `Kₙ` gives the system of their cohomology sheaves, compatibly with the
transition maps of the system.

This is Tag 0BKJ applied to each `Kₙ`, read as an isomorphism of systems; the same statement for
a derived limit `L` of the system -- that `𝓗ᵐ = Hᵐ(R lim Kₙ)` is the sheafification of
`underline 𝓗ᵐ : U ↦ Hᵐ(U, R lim Kₙ)` -- is Tag 0BKJ at the single object `L`, i.e. the component
`(sheafificationCohomologyPresheafIso O m).app L`. Both appear in
`Stacks.Cohomology.DerivedLimits.cohomologyDerivedLimitDiagram`, which puts them into the
remark's square. -/
@[stacks 0BKQ "the cohomology sheaf H^m(K_n) of each member of the inverse system is the \
sheafification of the cohomology presheaf U ↦ H^m(U, K_n), naturally in n"]
def sheafificationCohomologyPresheafSystemIso {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{wP} (PresheafOfModules.{u} O.obj)]
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} O)) (m : ℤ) :
    (K ⋙ derivedSectionsPresheaf O ⋙
          DerivedCategory.homologyFunctor (PresheafOfModules.{u} O.obj) m) ⋙
        PresheafOfModules.sheafification (𝟙 O.obj) ≅
      K ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{u} O) m :=
  Functor.isoWhiskerLeft K (sheafificationCohomologyPresheafIso O m)

/-- **Stacks 0BKQ, first assertion and diagram.** Let `O` be a sheaf of rings on a space, let
`(Kₙ)` be an inverse system in `D(O)` and let `L` be a derived limit of it, given by its
structural map `p` and the defining distinguished triangle. Fix a degree `m`, and let `e` be the
Tag 0BKJ identification of the sheafification `S` of the cohomology presheaf `underline 𝓗ᵐ` with
the cohomology sheaf `𝓗ᵐ`; in particular `e.hom.app (K.obj ⟨n⟩)` says that `𝓗ᵐ_n` is the
sheafification of `underline 𝓗ᵐ_n`, and `e.hom.app L` says the same for `L`.

Then there are comparison maps `a` into the limit of the cohomology presheaves, `b` into the
limit of the cohomology sheaves and `c` out of the sheafification of the former, each determined
by its composites with the limit projections -- `a` and `b` by the maps induced by `p ≫ πₙ`, and
`c` by the sheafified projections followed by `e` -- and the square

`S a ≫ c = e L ≫ b`

commutes. The map `c` is not asserted to be invertible: the source warns that `lim 𝓗ᵐ_n` need
not be the sheafification of `lim underline 𝓗ᵐ_n`. -/
@[stacks 0BKQ "the cohomology sheaves of the system and of the derived limit are the \
sheafifications of the cohomology presheaves U ↦ H^m(U, K_n) and U ↦ H^m(U, R lim K_n), and the \
comparison square of the remark's diagram commutes"]
theorem cohomologyDerivedLimitDiagram {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{wP} (PresheafOfModules.{u} O.obj)]
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} O))
    (L : DerivedCategory (SheafOfModules.{u} O))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{u} O)))
    (m : ℤ) :
    let P := derivedSectionsPresheaf O ⋙
      DerivedCategory.homologyFunctor (PresheafOfModules.{u} O.obj) m
    let H := DerivedCategory.homologyFunctor (SheafOfModules.{u} O) m
    let S := PresheafOfModules.sheafification (𝟙 O.obj)
    let e := sheafificationCohomologyPresheafIso O m
    ∃ (a : P.obj L ⟶ limit (K ⋙ P))
      (b : H.obj L ⟶ limit (K ⋙ H))
      (c : S.obj (limit (K ⋙ P)) ⟶ limit (K ⋙ H)),
      (∀ n : ℕ,
        a ≫ limit.π (K ⋙ P) ⟨n⟩ =
          P.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) ∧
      (∀ n : ℕ,
        b ≫ limit.π (K ⋙ H) ⟨n⟩ =
          H.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) ∧
      (∀ n : ℕ,
        c ≫ limit.π (K ⋙ H) ⟨n⟩ =
          S.map (limit.π (K ⋙ P) ⟨n⟩) ≫ e.hom.app (K.obj ⟨n⟩)) ∧
      (S.map a ≫ c = e.hom.app L ≫ b) := by
  intro P H S e
  exact exists_sheafificationComparisonSquare P H S e K L
    (fun n ↦ p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)
    (fun n ↦ (Stacks.Cohomology.DerivedLimitDiagram.comp_π_eq_comp_π_succ K L p hp n).trans
      (Category.assoc _ _ _).symm)

end Stacks.Cohomology.DerivedLimits

end
