module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.AcyclicResolutions
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.DeltaFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.Exactness
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
import StacksFrontier.CategoryTheory.Functor.Derived.EverywhereDefinedTriangulated
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The higher right derived functors of an everywhere defined `RF` form a universal `δ`-functor

Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories such that
`RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is everywhere defined ([Stacks, Tag 05SV]); no injectives are assumed. The
functors `R ⁱ F = H ⁱ ∘ RF ∘ (·[0])`, `i ≥ 0`, form a cohomological `δ`-functor, universal as soon
as every object of `𝒜` is a subobject of a right acyclic object ([Stacks, Tag 05TE]).

## Main results

* `CategoryTheory.Functor.isDeltaFunctor_and_isUniversal_of_isRightDerivable`: [Stacks, Tag 05TE].
* `CategoryTheory.Functor.isTriangulated_of_isRightDerivable_plus`: an everywhere defined `RF` is
  exact.
* `CategoryTheory.Functor.derivedDeltaFunctorStructureOfIsRightDerivable`: the canonical
  `δ`-functor structure on `A ↦ RF(A[0])`.

## Implementation notes

The vanishing `H ⁻¹(RF(A[0])) = 0`, which makes `R ⁰ F` left exact, is the retraction argument of
[Stacks, Tag 05TC] (`CategoryTheory.Functor.isGE_of_isRightDerivedValueAt_plus`); the vanishing
`H ⁱ(RF(I[0])) = 0`, `i > 0`, for `I[0]` computing `RF` comes from the uniqueness of values. The
`δ`-functor and universality arguments ([Stacks, Tag 05SR], [Stacks, Tag 010T]) are
`CategoryTheory.Functor.isDeltaFunctor_and_isUniversal_of_deltaFunctorStructure`.

## References

* [Stacks, Tag 05TE](https://stacks.math.columbia.edu/tag/05TE)
-/

@[expose] public section

universe w w' v v' u u'

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]

/-- **The lower cohomological bound of `RF` at a single complex.** If `RF : D⁺(C) ⥤ D⁺(D)` is
everywhere defined ([Stacks, Tag 05SV]), its value `RF(A[0])` has no cohomology in negative
degrees: the value is a retract of `F` applied to a resolution of `A[0]`, which good truncation
makes termwise `≥ 0` ([Stacks, Tag 05TC]). -/
private lemma isGE_zero_of_isRightDerivable (F : C ⥤ D) [F.Additive]
    (hF : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsRightDerivable
      (HomotopyCategory.Plus.quasiIso C))
    (RF : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D)
    (α : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶ DerivedCategory.Plus.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso C)] (A : C) :
    (RF.obj (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor C 0).obj A))).IsGE
      0 := by
  have := (isSaturated_and_isCompatibleWithTriangulation_quasiIsoPlus (C := C)).1
    |>.hasLeftCalculusOfFractions
  let X := (HomotopyCategory.Plus.singleFunctor C 0).obj A
  have hX : CochainComplex.IsGE X.obj.as 0 := by
    change CochainComplex.IsGE ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj A) 0
    infer_instance
  exact isGE_of_isRightDerivedValueAt_plus F X 0 hX _
    (isRightDerivedValueAt_derivedUnitCocone (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso C) DerivedCategory.Plus.Qh RF α hF X)

/-- **A single complex computing `RF` has no higher cohomology under `RF`.** If `RF` is
everywhere defined and `A[0]` computes `RF` ([Stacks, Tag 05SX]), then `H ⁱ(RF(A[0])) = 0` for
`i > 0`: the value of `RF` at `A[0]` is unique up to isomorphism, a value being a colimit of the
ind-object, and computing `RF` identifies it with `F(A)[0]`. -/
private lemma isZero_homology_of_computesRightDerived (F : C ⥤ D) [F.Additive]
    (hF : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsRightDerivable
      (HomotopyCategory.Plus.quasiIso C))
    (RF : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D)
    (α : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶ DerivedCategory.Plus.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso C)] (I : C)
    (hI : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso C) ((HomotopyCategory.Plus.singleFunctor C 0).obj I))
    (i : ℤ) (hi : 0 < i) :
    IsZero ((DerivedCategory.Plus.homologyFunctor D i).obj
      (RF.obj (DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.singleFunctor C 0).obj I)))) := by
  have := (isSaturated_and_isCompatibleWithTriangulation_quasiIsoPlus (C := C)).1
    |>.hasLeftCalculusOfFractions
  have := hasPointwiseRightDerivedFunctor_of_isRightDerivable
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) (HomotopyCategory.Plus.quasiIso C) hF
  let X := (HomotopyCategory.Plus.singleFunctor C 0).obj I
  obtain ⟨c, hc, hiso⟩ := hI
  let e₁ : c.pt ≅ RF.obj (DerivedCategory.Plus.Qh.obj X) :=
    hc.isColimit.coconePointUniqueUpToIso
      (isColimitDerivedUnitCocone (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
        (HomotopyCategory.Plus.quasiIso C) DerivedCategory.Plus.Qh RF α X)
  let e₂ : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj X ≅ c.pt :=
    @asIso _ _ _ _ (c.ι.app (MorphismProperty.Under.mk ⊤ (𝟙 X)
      (MorphismProperty.id_mem (HomotopyCategory.Plus.quasiIso C) X))) hiso
  let e₃ : (DerivedCategory.Plus.singleFunctor D 0).obj (F.obj I) ≅
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj X :=
    ((mapSingleFunctorCompQhIso F).app I).symm
  exact (DerivedCategory.Plus.isZero_homology_of_isLE _ 0 i hi).of_iso
    ((DerivedCategory.Plus.homologyFunctor D i).mapIso (e₃ ≪≫ e₂ ≪≫ e₁)).symm

/-- **The higher right derived functors form a universal `δ`-functor**, [Stacks, Tag 05TE].
Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories and assume that
`RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is everywhere defined: the right derived functor of
`K⁺(F) ⋙ Q : K⁺(𝒜) ⥤ D⁺(ℬ)` with respect to the quasi-isomorphisms is defined at every object
([Stacks, Tag 05SV]). Let `(RF, α)` be the right derived functor, so that
`R ⁱ F = H ⁱ ∘ RF ∘ (·[0])`. Let `h` be a `δ`-functor structure on `A ↦ RF(A[0]) : 𝒜 ⥤ D⁺(ℬ)`
(the canonical one, `CategoryTheory.Functor.derivedDeltaFunctorStructureOfIsRightDerivable`, is
`Stacks.DerivedIndexing.singleDeltaFunctorStructure` composed with the exact functor `RF`; the
statement holds for every such structure), and let `δ` be the connecting
morphism `R ⁱ F(C) ⟶ R ⁱ⁺¹ F(A)` that the homology sequence of its distinguished triangles
attaches to a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` of `𝒜`. Then
1. `{R ⁱ F, δ}_{i ≥ 0}` is a cohomological `δ`-functor from `𝒜` to `ℬ`: the `R ⁱ F` are additive,
   the long sequence `0 ⟶ R ⁰ F(A) ⟶ R ⁰ F(B) ⟶ R ⁰ F(C) ⟶ R ¹ F(A) ⟶ ⋯` is exact, and `δ` is
   natural in the short exact sequence; and
2. if every object of `𝒜` is a subobject of an object right acyclic for `F` — an object `I` such
   that `I[0]` computes `RF` ([Stacks, Tag 0157], [Stacks, Tag 05SX]) — then `{R ⁱ F, δ}_{i ≥ 0}`
   is a universal `δ`-functor: for every `δ`-functor `{G ⁱ, δ_G}_{i ≥ 0}` from `𝒜` to `ℬ` and
   every `t₀ : R ⁰ F ⟶ G ⁰` there is a unique family `t ⁱ : R ⁱ F ⟶ G ⁱ` commuting with `δ` and
   `δ_G` and with `t ⁰ = t₀`. -/
@[stacks 05TE]
public theorem isDeltaFunctor_and_isUniversal_of_isRightDerivable (F : C ⥤ D) [F.Additive]
    (hF : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsRightDerivable
      (HomotopyCategory.Plus.quasiIso C))
    (RF : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D)
    (α : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶ DerivedCategory.Plus.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso C)]
    (h : DeltaFunctorStructure C (DerivedCategory.Plus D)
      (DerivedCategory.Plus.singleFunctor C 0 ⋙ RF))
    (δ : ∀ {S : ShortComplex C}, S.ShortExact → ∀ i : ℕ,
      (DerivedCategory.Plus.singleFunctor C 0 ⋙ RF ⋙
          DerivedCategory.Plus.homologyFunctor D i).obj S.X₃ ⟶
        (DerivedCategory.Plus.singleFunctor C 0 ⋙ RF ⋙
          DerivedCategory.Plus.homologyFunctor D (i + 1)).obj S.X₁)
    (hδ : ∀ {S : ShortComplex C} (hS : S.ShortExact) (i : ℕ), δ hS i =
      (DerivedCategory.Plus.homologyFunctor D 0).homologySequenceδ
        (Pretriangulated.Triangle.mk ((DerivedCategory.Plus.singleFunctor C 0 ⋙ RF).map S.f)
          ((DerivedCategory.Plus.singleFunctor C 0 ⋙ RF).map S.g) (h.δ hS)) i (i + 1) rfl) :
    ((∀ i : ℕ, (DerivedCategory.Plus.singleFunctor C 0 ⋙ RF ⋙
          DerivedCategory.Plus.homologyFunctor D i).Additive) ∧
      (∀ {S : ShortComplex C}, S.ShortExact →
        Mono ((DerivedCategory.Plus.singleFunctor C 0 ⋙ RF ⋙
          DerivedCategory.Plus.homologyFunctor D 0).map S.f)) ∧
      (∀ {S : ShortComplex C} (_ : S.ShortExact) (i : ℕ),
        ∃ hz : (DerivedCategory.Plus.singleFunctor C 0 ⋙ RF ⋙
              DerivedCategory.Plus.homologyFunctor D i).map S.f ≫
            (DerivedCategory.Plus.singleFunctor C 0 ⋙ RF ⋙
              DerivedCategory.Plus.homologyFunctor D i).map S.g = 0,
          (ShortComplex.mk _ _ hz).Exact) ∧
      (∀ {S : ShortComplex C} (hS : S.ShortExact) (i : ℕ),
        ∃ hz : (DerivedCategory.Plus.singleFunctor C 0 ⋙ RF ⋙
            DerivedCategory.Plus.homologyFunctor D i).map S.g ≫ δ hS i = 0,
          (ShortComplex.mk _ _ hz).Exact) ∧
      (∀ {S : ShortComplex C} (hS : S.ShortExact) (i : ℕ),
        ∃ hz : δ hS i ≫ (DerivedCategory.Plus.singleFunctor C 0 ⋙ RF ⋙
            DerivedCategory.Plus.homologyFunctor D (i + 1)).map S.f = 0,
          (ShortComplex.mk _ _ hz).Exact) ∧
      (∀ {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S') (i : ℕ),
        (DerivedCategory.Plus.singleFunctor C 0 ⋙ RF ⋙
            DerivedCategory.Plus.homologyFunctor D i).map φ.τ₃ ≫ δ hS' i =
          δ hS i ≫ (DerivedCategory.Plus.singleFunctor C 0 ⋙ RF ⋙
            DerivedCategory.Plus.homologyFunctor D (i + 1)).map φ.τ₁)) ∧
    ((∀ A : C, ∃ (I : C) (u : A ⟶ I), Mono u ∧
        (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
          (HomotopyCategory.Plus.quasiIso C) ((HomotopyCategory.Plus.singleFunctor C 0).obj I)) →
      ∀ (G : ℕ → C ⥤ D) (_ : ∀ i, (G i).Additive)
        (δG : ∀ {S : ShortComplex C}, S.ShortExact → ∀ i : ℕ,
          (G i).obj S.X₃ ⟶ (G (i + 1)).obj S.X₁),
        (∀ {S : ShortComplex C}, S.ShortExact → Mono ((G 0).map S.f)) →
        (∀ {S : ShortComplex C} (_ : S.ShortExact) (i : ℕ),
          ∃ hz : (G i).map S.f ≫ (G i).map S.g = 0, (ShortComplex.mk _ _ hz).Exact) →
        (∀ {S : ShortComplex C} (hS : S.ShortExact) (i : ℕ),
          ∃ hz : (G i).map S.g ≫ δG hS i = 0, (ShortComplex.mk _ _ hz).Exact) →
        (∀ {S : ShortComplex C} (hS : S.ShortExact) (i : ℕ),
          ∃ hz : δG hS i ≫ (G (i + 1)).map S.f = 0, (ShortComplex.mk _ _ hz).Exact) →
        (∀ {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S')
          (i : ℕ), (G i).map φ.τ₃ ≫ δG hS' i = δG hS i ≫ (G (i + 1)).map φ.τ₁) →
        ∀ t₀ : DerivedCategory.Plus.singleFunctor C 0 ⋙ RF ⋙
            DerivedCategory.Plus.homologyFunctor D 0 ⟶ G 0,
          ∃! t : ∀ i : ℕ, DerivedCategory.Plus.singleFunctor C 0 ⋙ RF ⋙
              DerivedCategory.Plus.homologyFunctor D i ⟶ G i,
            t 0 = t₀ ∧ ∀ {S : ShortComplex C} (hS : S.ShortExact) (i : ℕ),
              (t i).app S.X₃ ≫ δG hS i = δ hS i ≫ (t (i + 1)).app S.X₁) := by
  -- `RF(A[0])` is `RF` at the image of `A[0]` in `D⁺(𝒜)`.
  let e : ∀ A : C, (DerivedCategory.Plus.singleFunctor C 0 ⋙ RF).obj A ≅
      RF.obj (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor C 0).obj A)) :=
    fun A ↦ RF.mapIso ((singleFunctorPlusIsoCompQh 0).app A)
  have hG : ∀ A : C, IsZero ((DerivedCategory.Plus.homologyFunctor D (-1)).obj
      ((DerivedCategory.Plus.singleFunctor C 0 ⋙ RF).obj A)) := fun A ↦ by
    have := isGE_zero_of_isRightDerivable F hF RF α A
    exact (DerivedCategory.Plus.isZero_homology_of_isGE _ 0 (-1) (by norm_num)).of_iso
      ((DerivedCategory.Plus.homologyFunctor D (-1)).mapIso (e A))
  obtain ⟨part1, part2⟩ := isDeltaFunctor_and_isUniversal_of_deltaFunctorStructure
    (DerivedCategory.Plus.singleFunctor C 0 ⋙ RF) h hG δ hδ
  refine ⟨part1, fun heff ↦ part2 fun A ↦ ?_⟩
  obtain ⟨I, u, hu, hI⟩ := heff A
  exact ⟨I, u, hu, fun i ↦ (isZero_homology_of_computesRightDerived F hF RF α I hI _
    (by positivity)).of_iso ((DerivedCategory.Plus.homologyFunctor D _).mapIso (e I))⟩

/-- **An everywhere defined `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is exact.** If the right derived functor of
`K⁺(F) ⋙ Q : K⁺(𝒜) ⥤ D⁺(ℬ)` is defined at every object ([Stacks, Tag 05SV]), then every right
derived functor `(RF, α)` of it whose comparison `α` commutes with the shift is a triangulated
functor ([Stacks, Tag 05SE]). In particular `Stacks.DerivedIndexing.singleDeltaFunctorStructure`
composed with `RF` is the canonical `δ`-functor structure on `A ↦ RF(A[0])` of
[Stacks, Tag 05TE]. -/
public theorem isTriangulated_of_isRightDerivable_plus (F : C ⥤ D) [F.Additive]
    (hF : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsRightDerivable
      (HomotopyCategory.Plus.quasiIso C))
    (RF : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D)
    (α : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶ DerivedCategory.Plus.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso C)] [RF.CommShift ℤ]
    [NatTrans.CommShift α ℤ] : RF.IsTriangulated :=
  have := (isSaturated_and_isCompatibleWithTriangulation_quasiIsoPlus (C := C)).2
  isTriangulated_of_isRightDerivable (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
    (HomotopyCategory.Plus.quasiIso C) DerivedCategory.Plus.Qh RF α
    (isSaturated_and_isCompatibleWithTriangulation_quasiIsoPlus (C := C)).1 hF

/-- **The canonical `δ`-functor structure on `A ↦ RF(A[0]) : 𝒜 ⥤ D⁺(ℬ)`** for an everywhere
defined `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` ([Stacks, Tag 05SV]), for any right derived functor `(RF, α)` and
with no injectives assumed: `RF` commutes with the shift
(`CategoryTheory.Functor.IsRightDerivedFunctor.commShift`) and is then exact
(`CategoryTheory.Functor.isTriangulated_of_isRightDerivable_plus`), so [Stacks, Tag 0151] part (1)
composes it with `Stacks.DerivedIndexing.singleDeltaFunctorStructure`. This is an input that
`CategoryTheory.Functor.isDeltaFunctor_and_isUniversal_of_isRightDerivable` quantifies over, so
that statement is not vacuous. -/
public noncomputable def derivedDeltaFunctorStructureOfIsRightDerivable (F : C ⥤ D) [F.Additive]
    (hF : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsRightDerivable
      (HomotopyCategory.Plus.quasiIso C))
    (RF : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D)
    (α : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶ DerivedCategory.Plus.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso C)] :
    DeltaFunctorStructure C (DerivedCategory.Plus D)
      (DerivedCategory.Plus.singleFunctor C 0 ⋙ RF) :=
  letI := IsRightDerivedFunctor.commShift RF α (HomotopyCategory.Plus.quasiIso C) ℤ
  have := F.isTriangulated_of_isRightDerivable_plus hF RF α
  (Stacks.DerivedIndexing.singleDeltaFunctorStructure (C := C)).comp RF

end CategoryTheory.Functor

end
