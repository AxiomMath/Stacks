module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.GaloisDescentEquivalence
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenCharacterisation

/-!
# The single-degree rank locus at an integer rank

[Stacks 0BDK] prescribes the degree `i` and the rank `r` as **integers**, while finite local
freeness of a fixed rank is stated at a natural number. This file states and proves the tag at an
arbitrary integer rank.

For `r ≥ 0` nothing changes. For `r < 0` no sheaf of modules on a nonempty scheme is locally free
of rank `r`, so the asserted open subscheme is the empty one, and the rank clause has to be read
the way it is stated — as a condition at each point: "every point has a neighbourhood on which the
sheaf is free of rank `r`". That reading is vacuous on the empty scheme, which is exactly what
makes the empty open subscheme satisfy both of the tag's descriptions, and makes the universal
property hold: a morphism `f : Y ⟶ X` factors through the empty open subscheme if and only if `Y`
is empty, and `Lf^* E` is a locally free module of rank `r < 0` placed in degree `i` if and only
if `Y` is empty.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isZero_of_isEmpty`: a sheaf of modules on an empty scheme is
  zero.
* `AlgebraicGeometry.Scheme.Modules.opens_eq_of_factorsThrough_iff`: two open subschemes with the
  same universal property for factorisations are equal.
* `AlgebraicGeometry.Scheme.Modules.existsUnique_opens_singleDegreeRank_int`: **[stacks 0BDK]** at
  the source's integer rank — a unique open subscheme satisfying both of the tag's descriptions.

## Implementation notes

*Why the rank clause is read pointwise.* The source's clause is "`H^i(E|_U)` is a locally free
`𝒪_U`-module of rank `r`", which is by definition a condition at every point of `U`. At a natural
rank the pointwise reading and the global one agree — this is proved as part of the non-negative
case, using that `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank` is itself a
pointwise condition and so is vacuous on an empty scheme — so nothing is weakened for `r ≥ 0` and
nothing is invented for `r < 0`.

*The empty scheme.* `Stacks.Descent.modules_hom_subsingleton_of_isEmpty` says a morphism of sheaves
of modules on an empty scheme is unique; so the identity is zero and every such sheaf is zero,
which is what makes an object of the derived category over an empty scheme concentrated in any
prescribed degree.

*The uniqueness.* `opens_eq_of_factorsThrough_iff` isolates the argument: description (2) applied
to the inclusion of either candidate puts each inside the other. It uses only description (2), so
it is independent of how the rank clause is read.

## References

* [The Stacks Project, Lemma 36.31.3 (0BDK)](https://stacks.math.columbia.edu/tag/0BDK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-! ### Sheaves of modules on an empty scheme -/

/-- **A sheaf of modules on an empty scheme is zero.** There is only one morphism between any two
such sheaves (`Stacks.Descent.modules_hom_subsingleton_of_isEmpty`), so the identity is zero. -/
theorem isZero_of_isEmpty {Z : Scheme.{u}} [IsEmpty Z] (F : Z.Modules) : IsZero F :=
  (IsZero.iff_id_eq_zero F).2
    ((Stacks.Descent.modules_hom_subsingleton_of_isEmpty F F).elim _ _)

/-! ### Uniqueness from the universal property -/

/-- **Two open subschemes with the same universal property for factorisations are equal.**
Description (2) of [stacks 0BDK] applied to the inclusion of either candidate puts each inside the
other. -/
theorem opens_eq_of_factorsThrough_iff {U V : X.Opens}
    (P : (Y : Scheme.{u}) → (Y ⟶ X) → Prop)
    (hU : ∀ (Y : Scheme.{u}) (f : Y ⟶ X), (∃ g : Y ⟶ U.toScheme, g ≫ U.ι = f) ↔ P Y f)
    (hV : ∀ (Y : Scheme.{u}) (f : Y ⟶ X), (∃ g : Y ⟶ V.toScheme, g ≫ V.ι = f) ↔ P Y f) :
    U = V :=
  le_antisymm
    (le_of_factorsThrough ((hV U.toScheme U.ι).2 ((hU U.toScheme U.ι).1 ⟨𝟙 _, by simp⟩)))
    (le_of_factorsThrough ((hU V.toScheme V.ι).2 ((hV V.toScheme V.ι).1 ⟨𝟙 _, by simp⟩)))

/-! ### The tag at an integer rank -/

/-- **[Stacks, Tag 0BDK].** Let `X` be a scheme, let `E ∈ D(𝒪_X)` be perfect and let `i, r` be
integers. There is a unique open subscheme `U ⊆ X` characterised by the following:

1. `E|_U ≅ H^i(E|_U)[-i]` and `H^i(E|_U)` is a locally free `𝒪_U`-module of rank `r`,
2. a morphism `f : Y ⟶ X` factors through `U` if and only if `Lf^* E` is isomorphic to a locally
   free module of rank `r` placed in degree `i`.

"Locally free of rank `r`" for an integer `r` is read, as the source states it, at each point: a
sheaf of modules has it when every point has a neighbourhood on which the sheaf is free of rank
`r`. For `r ≥ 0` that is finite local freeness of rank `r` and the statement is
`existsUnique_opens_singleDegreeRank` with its witness `singleDegreeRankOpen E i r`; for `r < 0`
the condition forces the scheme to be empty, and the open subscheme is `⊥`. -/
@[stacks 0BDK "THE WHOLE TAG, at the source's INTEGER rank: the existence of an open subscheme \
satisfying description (1), both of its clauses, and description (2) in both directions for an \
ARBITRARY morphism of schemes and the derived pullback Lf^*E, together with the UNIQUENESS \
that makes the two descriptions a characterisation. The only premise is the source's own, that \
E be perfect. The rank clause is read at each point, as the source states it; for a \
non-negative rank the witness is AlgebraicGeometry.Scheme.Modules.singleDegreeRankOpen and the \
statement is AlgebraicGeometry.Scheme.Modules.existsUnique_opens_singleDegreeRank, and for a \
negative rank the witness is the empty open subscheme"]
theorem existsUnique_opens_singleDegreeRank_int (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (i r : ℤ) :
    ∃! U : X.Opens,
      (Nonempty ((restrictFunctor U.ι).mapDerivedCategory.obj E ≅
            (DerivedCategory.singleFunctor U.toScheme.Modules i).obj
              ((DerivedCategory.homologyFunctor U.toScheme.Modules i).obj
                ((restrictFunctor U.ι).mapDerivedCategory.obj E))) ∧
          ∀ _ : U.toScheme, ∃ n : ℕ, (n : ℤ) = r ∧
            AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
              ((DerivedCategory.homologyFunctor U.toScheme.Modules i).obj
                ((restrictFunctor U.ι).mapDerivedCategory.obj E)) n) ∧
        ∀ (Y : Scheme.{u}) (f : Y ⟶ X),
          (∃ g : Y ⟶ U.toScheme, g ≫ U.ι = f) ↔
            ∃ M : Y.Modules,
              (∀ _ : Y, ∃ n : ℕ, (n : ℤ) = r ∧
                  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M n) ∧
                Nonempty ((derivedPullback f.toLRSHom.toShHom).obj E ≅
                  (DerivedCategory.singleFunctor Y.Modules i).obj M) := by
  refine existsUnique_of_exists_of_unique ?_ fun V W hV hW =>
    opens_eq_of_factorsThrough_iff _ hV.2 hW.2
  by_cases hr : 0 ≤ r
  · obtain ⟨n₀, rfl⟩ : ∃ n : ℕ, (n : ℤ) = r := ⟨r.toNat, Int.toNat_of_nonneg hr⟩
    obtain ⟨U, hUspec, -⟩ := existsUnique_opens_singleDegreeRank E hE i n₀
    refine ⟨U, ⟨hUspec.1.1, fun _ => ⟨n₀, rfl, hUspec.1.2⟩⟩, fun Y f => ?_⟩
    refine (hUspec.2 Y f).trans ⟨fun ⟨M, hM, hiso⟩ => ⟨M, fun _ => ⟨n₀, rfl, hM⟩, hiso⟩, ?_⟩
    rintro ⟨M, hrk, hiso⟩
    refine ⟨M, ?_, hiso⟩
    rcases isEmpty_or_nonempty Y with hY | ⟨⟨y⟩⟩
    · exact (isFiniteLocallyFreeOfRank_iff M n₀).1 fun x => (hY.false x).elim
    · obtain ⟨n, hn, hM⟩ := hrk y
      exact (Nat.cast_inj.mp hn) ▸ hM
  · have hbot : IsEmpty ((⊥ : X.Opens).toScheme) := ⟨fun z => z.2⟩
    refine ⟨⊥, ⟨nonempty_iso_singleFunctor_homologyFunctor_restrict (⊥ : X.Opens).ι E i
      fun j _ => isZero_of_isEmpty _, fun z => isEmptyElim z⟩, fun Y f => ?_⟩
    constructor
    · rintro ⟨g, rfl⟩
      have : IsEmpty Y := ⟨fun y => hbot.false (g.base y)⟩
      exact ⟨(DerivedCategory.homologyFunctor Y.Modules i).obj
          ((derivedPullback (g ≫ (⊥ : X.Opens).ι).toLRSHom.toShHom).obj E),
        fun y => isEmptyElim y,
        DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero _ i
          fun j _ => isZero_of_isEmpty _⟩
    · rintro ⟨M, hrk, -⟩
      have : IsEmpty Y := ⟨fun y => by obtain ⟨n, hn, -⟩ := hrk y; omega⟩
      exact ⟨AlgebraicGeometry.IsOpenImmersion.lift _ f
          (by rw [Set.range_eq_empty]; exact Set.empty_subset _),
        AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _⟩

end AlgebraicGeometry.Scheme.Modules

end
