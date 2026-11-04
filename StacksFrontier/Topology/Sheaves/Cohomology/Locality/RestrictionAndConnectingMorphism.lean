module

public import StacksFrontier.Algebra.Homology.DerivedDeltaOfShortComplexHom
public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally

/-!
# The connecting morphism is natural in the functor, and commutes with restriction

Let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence of an abelian category `B` with enough
injectives, resolved by a short exact sequence of injective resolutions — a
`Stacks.Cohomology.RightDerivedDelta.Horseshoe`. That resolution does not mention the functor
whose right derived functors are being computed, so one and the same resolution computes the
connecting morphism `RⁿQ X₃ ⟶ Rⁿ⁺¹Q X₁` for every additive `Q : B ⥤ D`. This file proves that
the resulting family of connecting morphisms is natural in `Q`: a natural transformation
`τ : Q₁ ⟶ Q₂` commutes with them, through `CategoryTheory.NatTrans.rightDerived τ`.

The application is the restriction maps of sheaf cohomology. For `U ≤ V` opens of a ringed
space, restriction of sections `secRestrict R h : Γ(V, -) ⟶ Γ(U, -)` is a natural
transformation of additive functors on `Mod(𝒪_X)` whose right derived functors are the
restriction maps `Hrestrict` on cohomology; so restricting a cohomology class along the open
immersion `U ↪ V` commutes with the connecting morphism of a short exact sequence of
`𝒪_X`-modules. That is the step which makes "the class of an extension dies on `U` because the
extension is split there" an argument about `Hⁿ(U, -)`.

## Main results

* `Stacks.Cohomology.RightDerivedDelta.Horseshoe.delta_natTrans`: the connecting morphism of the
  long exact sequence of right derived functors in the object variable is natural in the
  functor.
* `Stacks.Cohomology.Restriction.Hrestrict_delta`: restriction of cohomology along an inclusion
  of opens commutes with that connecting morphism, in every degree.
* `Stacks.Cohomology.Restriction.Hrestrict_delta_apply`: the same, on a class.
* `Stacks.Cohomology.Restriction.Hrestrict_delta_eq_zero`: a class whose restriction to `U`
  comes from a class that already dies on `U` dies on `U` — the form in which the square is
  consumed.

## Implementation notes

The connecting morphism `Stacks.Cohomology.RightDerivedDelta.Horseshoe.delta` is the
snake-lemma connecting morphism of the short exact sequence of complexes obtained by applying
`Q` degreewise to the resolving complexes, conjugated by
`CategoryTheory.InjectiveResolution.isoRightDerivedObj'`. Both conjugating isomorphisms are at
the same resolution on the two sides of the square, so they cancel against the two occurrences
inside `CategoryTheory.rightDerived_app_eq_conj`, which is the same description of
`CategoryTheory.NatTrans.rightDerived`; what is left is the naturality of the snake-lemma
connecting morphism along the morphism of short exact sequences of complexes given by `τ`
applied degreewise, which is `HomologicalComplex.HomologySequence.δ_naturality`. Nothing is
needed beyond additivity of the two functors: the sequence of resolving complexes is
degreewise split, because its first term is degreewise injective, so applying either functor
degreewise keeps it short exact.

This is naturality in the *functor*, which is the direction
`Stacks.Cohomology.RightDerivedDelta.Horseshoe.delta_naturality` does not cover — that one is
naturality in the short exact sequence. For the left derived functors the corresponding
statement is `CategoryTheory.Functor.leftDerivedδ_natTrans`.

The connecting morphism depends on the chosen resolution of the short exact sequence, as
`Stacks.Cohomology.RightDerivedDelta` records, so the resolution is carried as an argument
here too; the square is proved at one resolution, which is what the applications use, since the
two sides of the square are computed from the *same* resolution.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v₁ v₂ u₁ u₂ u

namespace Stacks.Cohomology.RightDerivedDelta.Horseshoe

variable {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasInjectiveResolutions B]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {S : ShortComplex B} (H : Horseshoe S)

/-- **The connecting morphism of the long exact sequence of right derived functors is natural in
the functor.** One resolution of the short exact sequence computes the connecting morphism for
every additive functor, and a natural transformation `τ : Q₁ ⟶ Q₂` commutes with the resulting
connecting morphisms through `CategoryTheory.NatTrans.rightDerived τ`. -/
theorem delta_natTrans {Q₁ Q₂ : B ⥤ D} [Q₁.Additive] [Q₂.Additive] (τ : Q₁ ⟶ Q₂) (n : ℕ) :
    H.delta Q₁ n ≫ (NatTrans.rightDerived τ (n + 1)).app S.X₁ =
      (NatTrans.rightDerived τ n).app S.X₃ ≫ H.delta Q₂ n := by
  have hδ : (H.shortExact_mapSequence Q₁).δ n (n + 1) (ComplexShape.up_rel_succ n) ≫
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℕ)).app H.J₁.cocomplex) (n + 1) =
      HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℕ)).app H.J₃.cocomplex) n ≫
        (H.shortExact_mapSequence Q₂).δ n (n + 1) (ComplexShape.up_rel_succ n) :=
    HomologicalComplex.HomologySequence.δ_naturality
      { τ₁ := (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℕ)).app H.J₁.cocomplex
        τ₂ := (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℕ)).app H.J₂.cocomplex
        τ₃ := (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℕ)).app H.J₃.cocomplex
        comm₁₂ := ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℕ)).naturality H.f).symm
        comm₂₃ := ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℕ)).naturality H.g).symm }
      (H.shortExact_mapSequence Q₁) (H.shortExact_mapSequence Q₂) n (n + 1)
      (ComplexShape.up_rel_succ n)
  rw [rightDerived_app_eq_conj τ H.J₁ (n + 1), rightDerived_app_eq_conj τ H.J₃ n]
  dsimp only [delta]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc, ← Category.assoc
      ((H.shortExact_mapSequence Q₁).δ n (n + 1) (ComplexShape.up_rel_succ n)), hδ,
    Category.assoc]

end Stacks.Cohomology.RightDerivedDelta.Horseshoe

namespace Stacks.Cohomology.Restriction

open Stacks.Cohomology.RightDerivedDelta

variable {X : Type u} [TopologicalSpace X] (R : Sheaf (Opens.grothendieckTopology X) RingCat)
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]
variable [EnoughInjectives (SheafOfModules R)]
variable {S : ShortComplex (SheafOfModules R)} (H : Horseshoe S)

/-- **Restriction of cohomology along an inclusion of opens commutes with the connecting
morphism** of a short exact sequence of `𝒪_X`-modules: for `U ≤ V`, the square built from
`Hrestrict` in degrees `n` and `n + 1` and the two connecting morphisms `Hⁿ(W, X₃) ⟶
Hⁿ⁺¹(W, X₁)` for `W = V` and `W = U` commutes. This is
`Stacks.Cohomology.RightDerivedDelta.Horseshoe.delta_natTrans` at the restriction-of-sections
transformation `secRestrict`, whose right derived functors are `Hrestrict` by definition. -/
theorem Hrestrict_delta {U V : Opens X} (h : U ≤ V) (n : ℕ) :
    H.delta (secF R V) n ≫ Hrestrict R h (n + 1) S.X₁ =
      Hrestrict R h n S.X₃ ≫ H.delta (secF R U) n :=
  H.delta_natTrans (secRestrict R h) n

/-- `Hrestrict_delta` read on a cohomology class: the restriction to `U` of the connecting image
of a class on `V` is the connecting image on `U` of its restriction. -/
theorem Hrestrict_delta_apply {U V : Opens X} (h : U ≤ V) (n : ℕ)
    (ξ : (Hgroup R V n S.X₃ : Type _)) :
    Hrestrict R h (n + 1) S.X₁ (H.delta (secF R V) n ξ) =
      H.delta (secF R U) n (Hrestrict R h n S.X₃ ξ) := by
  have := ConcreteCategory.congr_hom (Hrestrict_delta R H h n) ξ
  simpa only [CategoryTheory.comp_apply] using this

/-- **A connecting image dies on `U` as soon as the class it comes from does.** This is the form
in which the compatibility is used: a class on `V` which restricts to zero on `U` has a
connecting image whose restriction to `U` is zero, so an extension split over `U` has a class
that dies on `U`. -/
theorem Hrestrict_delta_eq_zero {U V : Opens X} (h : U ≤ V) (n : ℕ)
    (ξ : (Hgroup R V n S.X₃ : Type _)) (hξ : Hrestrict R h n S.X₃ ξ = 0) :
    Hrestrict R h (n + 1) S.X₁ (H.delta (secF R V) n ξ) = 0 := by
  rw [Hrestrict_delta_apply R H h n ξ, hξ, map_zero]

end Stacks.Cohomology.Restriction

end
