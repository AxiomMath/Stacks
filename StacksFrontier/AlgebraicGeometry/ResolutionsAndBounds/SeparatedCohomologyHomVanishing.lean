module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGESuccTriangle
public import StacksFrontier.AlgebraicGeometry.Properties.Regular

/-!
# Morphisms between complexes whose cohomological ranges are separated

Let `𝒜` be an abelian category and let `d` be a natural number such that
`Ext^n(F, G) = 0` for `n > d` whenever `F` and `G` satisfy a prescribed property `P`.
If `K` and `L` are objects of `D(𝒜)` which are bounded, whose cohomology objects satisfy `P`, and
whose cohomological ranges are separated by `d`, in the sense that `H^i(K) = 0` for `i < a + d`
and `H^i(L) = 0` for `i ≥ a`, then `Hom(K, L) = 0`.

Both variables are reduced to a single cohomology object by the truncation triangles
`H^b(K)[-b] ⟶ τ^{≥b}K ⟶ τ^{≥b+1}K` and `τ^{≤b}L ⟶ τ^{≤b+1}L ⟶ H^{b+1}(L)[-b-1]`, along which
the vanishing propagates because `Hom(-, L)` and `Hom(K, -)` are (co)homological. The recursion
terminates because a truncation that passes the opposite bound is a zero object. In the remaining
case `K = F[-i]` and `L = G[-c]` with `c + d < i`, so that `Hom(K, L) = Ext^{i - c}(F, G)` with
`i - c > d`, and the assumed vanishing of `Ext` applies.

For `X` a regular Noetherian scheme of dimension `d`, taking `P` to be coherence and feeding in
the vanishing of `Ext^n` between coherent modules for `n > d` gives the vanishing of `Hom(K, L)`
for `K`, `L` in `D^b_{Coh}(𝒪_X)` with cohomological ranges separated by `d`.

## Main results

* `Stacks.SeparatedCohomology.subsingleton_hom_of_isGE_of_isLE`: the vanishing of `Hom(K, L)`
  for bounded `K` and `L` with cohomological ranges separated by `d`, in an arbitrary abelian
  category.
* `AlgebraicGeometry.subsingleton_hom_of_homology_separated`: the same statement on a regular
  Noetherian scheme of dimension `d`, from the vanishing of `Ext^n` between coherent modules for
  `n > d`. With that vanishing proved, this is part (2) of [Stacks, Tag 0FZ3], registered as
  `AlgebraicGeometry.subsingleton_hom_of_homology_separated_of_isRegular`.

## Implementation notes

The vanishing of `Ext^n` between coherent modules in degrees `n > d`, which is part (1) of
[Stacks, Tag 0FZ3], is an explicit hypothesis `hExt` of
`AlgebraicGeometry.subsingleton_hom_of_homology_separated`, so that this file does not depend on
the proof of part (1). That proof is `AlgebraicGeometry.subsingleton_zExt_of_isRegular` in
`StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.ExtVanishingRegular`, which discharges `hExt`
and registers both parts of the tag. The regularity and dimension hypotheses are carried but
unused here.

Vanishing of a morphism group is expressed as `Subsingleton`, and a cohomological range is
expressed through the t-structure predicates `IsGE` and `IsLE`, which
`DerivedCategory.isGE_iff` and `DerivedCategory.isLE_iff` identify with the vanishing of
cohomology objects. The induction is on the amplitude of one variable at a time, with the other
held fixed, so that the cohomology objects appearing in the truncation triangles are those of the
original complex and no coherence statement about truncations is needed.

## References

* [Stacks Project, Tag 0FZ3](https://stacks.math.columbia.edu/tag/0FZ3)
* [Stacks Project, Tag 08J5](https://stacks.math.columbia.edu/tag/08J5)
* [Stacks Project, Tag 0149](https://stacks.math.columbia.edu/tag/0149)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated DerivedCategory

universe w v u

namespace Stacks.SeparatedCohomology

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- If neither outer vertex of a distinguished triangle admits a nonzero morphism to `L`, then
neither does the middle vertex. This is [Stacks, Tag 0149] for `Hom(-, L)`. -/
private lemma subsingleton_hom_of_distTriang {T : Triangle (DerivedCategory C)}
    (hT : T ∈ distTriang (DerivedCategory C)) (L : DerivedCategory C)
    (h₁ : Subsingleton (T.obj₁ ⟶ L)) (h₃ : Subsingleton (T.obj₃ ⟶ L)) :
    Subsingleton (T.obj₂ ⟶ L) := by
  refine subsingleton_of_forall_eq 0 fun w => ?_
  obtain ⟨g, rfl⟩ := T.yoneda_exact₂ hT w (h₁.elim _ _)
  rw [h₃.elim g 0, comp_zero]

/-- If `K` admits no nonzero morphism to either outer vertex of a distinguished triangle, then it
admits none to the middle vertex. This is [Stacks, Tag 0149] for `Hom(K, -)`. -/
private lemma subsingleton_hom_of_distTriang' {T : Triangle (DerivedCategory C)}
    (hT : T ∈ distTriang (DerivedCategory C)) (K : DerivedCategory C)
    (h₁ : Subsingleton (K ⟶ T.obj₁)) (h₃ : Subsingleton (K ⟶ T.obj₃)) :
    Subsingleton (K ⟶ T.obj₂) := by
  refine subsingleton_of_forall_eq 0 fun w => ?_
  obtain ⟨g, rfl⟩ := T.coyoneda_exact₂ hT w (h₃.elim _ _)
  rw [h₁.elim g 0, zero_comp]

/-- Morphisms from a complex concentrated in degree `i` to one concentrated in degree `c` are the
extensions of degree `i - c`. -/
private lemma subsingleton_hom_single_single (F G : C) (i c : ℤ)
    (h : Subsingleton (Abelian.zExt F G (i - c))) :
    Subsingleton ((singleFunctor C i).obj F ⟶ (singleFunctor C c).obj G) := by
  have e₁ : ((singleFunctor C i).obj F)⟦i⟧ ≅ (singleFunctor C 0).obj F :=
    ((singleFunctors C).shiftIso i 0 i (by omega)).app F
  have e₂ : ((singleFunctor C c).obj G)⟦i⟧ ≅ (singleFunctor C (c - i)).obj G :=
    ((singleFunctors C).shiftIso i (c - i) c (by omega)).app G
  have e₃ : ((singleFunctor C 0).obj G)⟦i - c⟧ ≅ (singleFunctor C (c - i)).obj G :=
    ((singleFunctors C).shiftIso (i - c) (c - i) 0 (by omega)).app G
  have hsh : Subsingleton (((singleFunctor C i).obj F)⟦i⟧ ⟶ ((singleFunctor C c).obj G)⟦i⟧) :=
    (Equiv.subsingleton_congr (Iso.homCongr e₁ (e₂ ≪≫ e₃.symm))).mpr h
  exact Function.Injective.subsingleton (shiftFunctor (DerivedCategory C) i).map_injective

variable (P : C → Prop) (d : ℕ)

/-- The vanishing of `Ext^n` above `d` between objects satisfying `P`. -/
private def ExtVanishesAbove : Prop :=
  ∀ F G : C, P F → P G → ∀ n : ℤ, (d : ℤ) < n → Subsingleton (Abelian.zExt F G n)

/-- Morphisms from a complex concentrated in a single degree `i` into an upper truncation of `L`
vanish, by induction on the amplitude of that truncation. -/
private lemma subsingleton_hom_single_truncLE (hExt : ExtVanishesAbove P d)
    (F : C) (hF : P F) (i : ℤ) (L : DerivedCategory C) (n₀ : ℤ) [L.IsGE n₀]
    (hL : ∀ j : ℤ, P ((homologyFunctor C j).obj L)) :
    ∀ (N : ℕ) (c : ℤ), c + d < i → c - (N : ℤ) < n₀ →
      Subsingleton ((singleFunctor C i).obj F ⟶ (TStructure.t.truncLE c).obj L) := by
  intro N
  induction N with
  | zero =>
    intro c _ hc
    have hzero : IsZero ((TStructure.t.truncLE c).obj L) :=
      TStructure.t.isZero _ c n₀ (by omega)
    exact ⟨fun u v => hzero.eq_of_tgt u v⟩
  | succ N ih =>
    intro c hci hc
    obtain ⟨b, rfl⟩ : ∃ b : ℤ, c = b + 1 := ⟨c - 1, by ring⟩
    obtain ⟨g, δ, hT⟩ := exists_truncLESucc_triangle L b
    refine subsingleton_hom_of_distTriang' hT _ ?_ ?_
    · exact ih b (by omega) (by omega)
    · exact subsingleton_hom_single_single F _ i (b + 1)
        (hExt F _ hF (hL (b + 1)) _ (by omega))

/-- Morphisms from a lower truncation of `K` into `L` vanish, by induction on the amplitude of
that truncation. -/
private lemma subsingleton_hom_truncGE (hExt : ExtVanishesAbove P d)
    (K : DerivedCategory C) (m : ℤ) [K.IsLE m]
    (hK : ∀ j : ℤ, P ((homologyFunctor C j).obj K))
    (L : DerivedCategory C) (n₀ a : ℤ) [L.IsGE n₀] [L.IsLE (a - 1)]
    (hL : ∀ j : ℤ, P ((homologyFunctor C j).obj L)) :
    ∀ (N : ℕ) (b : ℤ), a + d ≤ b → m < b + (N : ℤ) →
      Subsingleton ((TStructure.t.truncGE b).obj K ⟶ L) := by
  intro N
  induction N with
  | zero =>
    intro b _ hb
    have hzero : IsZero ((TStructure.t.truncGE b).obj K) :=
      TStructure.t.isZero _ m b (by omega)
    exact ⟨fun u v => hzero.eq_of_src u v⟩
  | succ N ih =>
    intro b hab hb
    obtain ⟨f, δ, hT⟩ := exists_truncGESucc_triangle K b
    refine subsingleton_hom_of_distTriang hT _ ?_ ?_
    · -- the single `H^b(K)[-b]` maps to no part of `L`, which sits in degrees `≤ a - 1`
      have hiso : (TStructure.t.truncLE (a - 1)).obj L ≅ L :=
        asIso ((TStructure.t.truncLEι (a - 1)).app L)
      refine (Equiv.subsingleton_congr (Iso.homCongr (Iso.refl _) hiso)).mp ?_
      exact subsingleton_hom_single_truncLE P d hExt _ (hK b) b L n₀ hL
        ((a - 1 - n₀).toNat + 1) (a - 1) (by omega)
        (by omega)
    · exact ih (b + 1) (by omega) (by omega)

/-- **Vanishing of morphisms between complexes whose cohomological ranges are separated.** Let
`d` be a natural number such that `Ext^n(F, G) = 0` for `n > d` whenever `F` and `G` satisfy `P`.
Let `K` and `L` be bounded objects of `D(𝒜)` all of whose cohomology objects satisfy `P`. If `K`
is concentrated in degrees `≥ a + d` and `L` in degrees `< a`, then `Hom(K, L) = 0`. -/
public theorem subsingleton_hom_of_isGE_of_isLE
    (hExt : ∀ F G : C, P F → P G → ∀ n : ℤ, (d : ℤ) < n → Subsingleton (Abelian.zExt F G n))
    (K L : DerivedCategory C) (a : ℤ)
    (hKb : TStructure.t.bounded K) (hLb : TStructure.t.bounded L)
    (hK : ∀ j : ℤ, P ((homologyFunctor C j).obj K))
    (hL : ∀ j : ℤ, P ((homologyFunctor C j).obj L))
    (hKGE : K.IsGE (a + d)) (hLLE : L.IsLE (a - 1)) :
    Subsingleton (K ⟶ L) := by
  obtain ⟨-, m, hm⟩ := hKb
  obtain ⟨n₀, hn₀⟩ := hLb.1
  have := hm
  have := hn₀
  have := hKGE
  have := hLLE
  have hiso : (TStructure.t.truncGE (a + d)).obj K ≅ K :=
    (asIso ((TStructure.t.truncGEπ (a + d)).app K)).symm
  refine (Equiv.subsingleton_congr (Iso.homCongr hiso (Iso.refl L))).mp ?_
  exact subsingleton_hom_truncGE P d hExt K m hK L n₀ a hL
    ((m - (a + d)).toNat + 1) (a + d) le_rfl
    (by omega)

end Stacks.SeparatedCohomology

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u'

/-- Let `X` be a regular Noetherian scheme of dimension `d`, and suppose that
`Ext^n_X(F, G) = 0` for coherent `F`, `G` and `n > d` (`hExt`). Let `K` and `L` be objects of
`D^b_{Coh}(𝒪_X)` and let `a` be an integer. If `H^i(K) = 0` for `i < a + d` and `H^i(L) = 0` for
`i ≥ a`, then `Hom_X(K, L) = 0`.

The hypothesis `hExt` is part (1) of [Stacks, Tag 0FZ3], proved as
`AlgebraicGeometry.subsingleton_zExt_of_isRegular`; the unconditional statement, part (2) of that
tag, is `AlgebraicGeometry.subsingleton_hom_of_homology_separated_of_isRegular`. -/
public theorem subsingleton_hom_of_homology_separated (X : Scheme.{u'}) [IsNoetherian X]
    (_hX : IsRegular X) (d : ℕ) (_hd : topologicalKrullDim X = (d : WithBot ℕ∞))
    (hExt : ∀ F G : X.Modules, F.IsCoherent → G.IsCoherent →
      ∀ n : ℤ, (d : ℤ) < n → Subsingleton (Abelian.zExt F G n))
    (K L : DerivedCategory X.Modules) (a : ℤ)
    (hKb : DerivedCategory.TStructure.t.bounded K)
    (hLb : DerivedCategory.TStructure.t.bounded L)
    (hKcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsCoherent)
    (hLcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsCoherent)
    (hK : ∀ i : ℤ, i < a + d → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K))
    (hL : ∀ i : ℤ, a ≤ i → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj L)) :
    Subsingleton (K ⟶ L) :=
  Stacks.SeparatedCohomology.subsingleton_hom_of_isGE_of_isLE
    (fun M : X.Modules => M.IsCoherent) d hExt K L a hKb hLb hKcoh hLcoh
    ((DerivedCategory.isGE_iff K (a + d)).2 fun i hi => hK i hi)
    ((DerivedCategory.isLE_iff L (a - 1)).2 fun i hi => hL i (by omega))

end AlgebraicGeometry

end
