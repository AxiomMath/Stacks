module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.FieldTarget
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup
public import StacksFrontier.RingTheory.TotallySplit.PrimeSpectrum
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The degree of a finite étale morphism and the size of a geometric fibre

A finite étale algebra over a separably closed field `Ω` is a finite product of copies of `Ω`, so
its spectrum has exactly as many `Ω`-rational points as the algebra has dimensions, and that
dimension is the degree of the spectrum over `Ω`. Over a connected base the degree of a finite
étale morphism is a single number, and base change to a geometric point identifies it with the
number of points of the geometric fibre there.

## Main results

* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_specMap_natCard_algHom`: the spectrum of a finite
  étale algebra `A` over a separably closed field `Ω` is finite locally free of rank the number
  of `Ω`-algebra maps `A → Ω`.
* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_natCard_sections`: a finite étale scheme over a
  separably closed field is finite locally free of rank the number of its rational points.
* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_natCard_finiteEtaleFiber`: a finite étale cover of
  a connected scheme is finite locally free of rank the cardinality of its fibre at a geometric
  point.

## Implementation notes

The algebraic input is `Algebra.IsFiniteSplit.natCard_algHom_eq_finrank`, which over a separably
closed field applies to every finite étale algebra; combined with the identification of finite
local freeness of a given rank over the spectrum of a ring with the module-level condition on the
global sections of the source, it gives the statement for the spectrum of an algebra. A general
finite étale scheme over the field is affine, hence the spectrum of its own global sections, and
its comparison morphism fits in a cartesian square with an isomorphism along the top, which
carries both the rank and, through the universal property, the set of rational points.

Over a connected base no finite locally free structure has to be produced by hand: the rank
function of a finite flat locally finitely presented morphism is locally constant, hence constant,
and a constant rank function is a rank. Its value at the image of the geometric point is the rank
of the base change to that point, and the cartesian square defining that base change identifies
the sections of the base change with the lifts of the geometric point, that is with the geometric
fibre.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 02GL](https://stacks.math.columbia.edu/tag/02GL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Morphisms

/-- Around a cartesian square, the morphisms from the lower left corner to the upper right one
that lift the lower edge are the sections of the right-hand base change. -/
private def isPullbackSectionEquiv {C : Type*} [Category* C] {P X Y Z : C} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) :
    { u : Y ⟶ X // u ≫ f = g } ≃ { σ : Y ⟶ P // σ ≫ snd = 𝟙 Y } where
  toFun u := ⟨h.lift u.1 (𝟙 Y) (by simpa using u.2), h.lift_snd _ _ _⟩
  invFun σ := ⟨σ.1 ≫ fst, by rw [Category.assoc, h.w, ← Category.assoc, σ.2, Category.id_comp]⟩
  left_inv u := Subtype.ext (h.lift_fst _ _ _)
  right_inv σ := Subtype.ext (h.hom_ext (by simp) (by simp [σ.2]))

/-- The `R`-rational points of the spectrum of an `R`-algebra `A` are the `R`-algebra maps
`A → R`. -/
private def specSectionEquivAlgHom (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    { σ : Spec (.of R) ⟶ Spec (.of A) //
        σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) = 𝟙 _ } ≃ (A →ₐ[R] R) where
  toFun σ := by
    refine AlgHom.mk (Spec.preimage σ.1).hom fun r ↦ ?_
    have h : CommRingCat.ofHom (algebraMap R A) ≫ Spec.preimage σ.1 = 𝟙 _ := by
      have h2 := congrArg Spec.preimage σ.2
      rwa [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_id] at h2
    exact congrArg (fun φ : CommRingCat.of R ⟶ CommRingCat.of R ↦ φ.hom r) h
  invFun f := ⟨Spec.map (CommRingCat.ofHom f.toRingHom), by
    rw [← Spec.map_comp, Spec.map_eq_id]
    ext r
    exact f.commutes r⟩
  left_inv σ := Subtype.ext (by simp)
  right_inv f := AlgHom.ext fun x ↦ by simp

/-- The spectrum of a finite étale algebra `A` over a separably closed field `Ω` is finite locally
free of rank the number of `Ω`-algebra maps `A → Ω`. -/
@[sga "3 VIII 2.1" "Forward direction"]
theorem isFiniteLocallyFreeOfRank_specMap_natCard_algHom (Ω A : Type u) [Field Ω] [IsSepClosed Ω]
    [CommRing A] [Algebra Ω A] [Module.Finite Ω A] [Algebra.Etale Ω A] :
    IsFiniteLocallyFreeOfRank (Spec.map (CommRingCat.ofHom (algebraMap Ω A)))
      (Nat.card (A →ₐ[Ω] Ω)) := by
  rw [isFiniteLocallyFreeOfRank_specMap_iff_module, Module.isFiniteLocallyFreeOfRank_iff_finrank_eq]
  exact ⟨inferInstance, (Algebra.IsFiniteSplit.natCard_algHom_eq_finrank).symm⟩

/-- A finite étale scheme over a separably closed field `Ω` is finite locally free of rank the
number of its `Ω`-rational points. -/
@[sga "3 VIII 2.1" "Forward direction"]
theorem isFiniteLocallyFreeOfRank_natCard_sections {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    {P : Scheme.{u}} (g : P ⟶ Spec (.of Ω)) [IsFinite g] [Etale g] :
    IsFiniteLocallyFreeOfRank g (Nat.card { σ : Spec (.of Ω) ⟶ P // σ ≫ g = 𝟙 _ }) := by
  have _ : IsAffine P := isAffine_of_isAffineHom g
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (P.isoSpec.inv ≫ g)
  have hfin : IsFinite (Spec.map ψ) := hψ ▸ inferInstance
  have het : Etale (Spec.map ψ) := hψ ▸ inferInstance
  let _ : Algebra Ω ↑Γ(P, ⊤) := ψ.hom.toAlgebra
  have halg : algebraMap Ω ↑Γ(P, ⊤) = ψ.hom := RingHom.algebraMap_toAlgebra _
  have _ : Module.Finite Ω ↑Γ(P, ⊤) := by
    rw [← RingHom.finite_algebraMap, halg]
    exact (IsFinite.SpecMap_iff ψ).mp hfin
  have _ : Algebra.Etale Ω ↑Γ(P, ⊤) := by
    rw [← RingHom.etale_algebraMap, halg]
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp het
  have sq : IsPullback P.isoSpec.hom g
      (Spec.map (CommRingCat.ofHom (algebraMap Ω ↑Γ(P, ⊤)))) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [halg, CommRingCat.ofHom_hom, hψ]
      simp⟩
  have _ := isFiniteLocallyFreeOfRank_specMap_natCard_algHom Ω ↑Γ(P, ⊤)
  rw [Nat.card_congr ((isPullbackSectionEquiv sq).symm.trans
    (specSectionEquivAlgHom Ω ↑Γ(P, ⊤)))]
  exact IsFiniteLocallyFreeOfRank.of_isPullback sq

end Stacks.Morphisms

namespace AlgebraicGeometry

/-- A finite étale cover of a connected scheme is finite locally free of rank the cardinality of
its fibre at a geometric point. -/
theorem isFiniteLocallyFreeOfRank_natCard_finiteEtaleFiber {S : Scheme.{u}} [ConnectedSpace S]
    (s : GeometricPoint S) (T : FiniteEtaleOver S) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank T.hom
      (Nat.card ((finiteEtaleFiberFunctor s).obj T)) := by
  have _ := T.prop.1
  have _ := T.prop.2
  have hcard : Nat.card ((finiteEtaleFiberFunctor s).obj T) =
      Nat.card { σ : s.source ⟶ pullback T.hom s.hom //
        σ ≫ pullback.snd T.hom s.hom = 𝟙 _ } :=
    Nat.card_congr (Stacks.Morphisms.isPullbackSectionEquiv (.of_hasPullback _ _))
  have hpt : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.snd T.hom s.hom)
      (Nat.card { σ : s.source ⟶ pullback T.hom s.hom //
        σ ≫ pullback.snd T.hom s.hom = 𝟙 _ }) :=
    Stacks.Morphisms.isFiniteLocallyFreeOfRank_natCard_sections _
  have _ : PreconnectedSpace ↥((Functor.fromPUnit S).obj T.right) :=
    inferInstanceAs (PreconnectedSpace ↥S)
  rw [Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq, hcard]
  intro x
  rw [(T.hom.isLocallyConstant_finrank).apply_eq_of_preconnectedSpace x (s.hom default),
    ← Scheme.Hom.finrank_pullback_snd T.hom s.hom default]
  exact (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ _).mp hpt default

end AlgebraicGeometry

end
