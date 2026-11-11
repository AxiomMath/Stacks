module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightAcyclicEverywhereDefined
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Right acyclicity in a short exact sequence when `RF` is everywhere defined

Let `F : 𝒜 ⥤ ℬ` be a left exact functor between abelian categories and assume that
`RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is everywhere defined (`CategoryTheory.Functor.IsRightDerivable`,
[Stacks, Tag 05SV]); no injective objects are assumed. For a short exact sequence
`0 ⟶ A ⟶ B ⟶ C ⟶ 0` of `𝒜`, two right acyclic objects among `A`, `B`, `C` force the third, in
the three configurations of [Stacks, Tag 015D], and `0 ⟶ F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is short exact.

The proof is the source's: the short exact sequence gives a distinguished triangle
`A[0] ⟶ B[0] ⟶ C[0] ⟶ A[0][1]` of `D⁺(𝒜)` ([Stacks, Tag 0152]); `RF` is exact, being everywhere
defined (`CategoryTheory.Functor.isTriangulated_of_isRightDerivable`), so the triangle has a long
exact cohomology sequence `0 ⟶ F(A) ⟶ F(B) ⟶ F(C) ⟶ R ¹ F(A) ⟶ ⋯`, where `R ⁱ F = 0` for `i < 0`
and `R ⁰ F = F` ([Stacks, Tag 05TD], proved for an everywhere defined `RF` in
`StacksFrontier.Algebra.Homology.DerivedCategory.RightAcyclicEverywhereDefined`), and acyclicity is
read off it through [Stacks, Tag 015C].

## Main results

* `CategoryTheory.Functor.rightAcyclic_and_shortExact_map_of_shortExact_of_isRightDerivable`:
  [Stacks, Tag 015D].

## References

* [Stacks, Tag 015D]
* [Stacks, Tag 015C], [Stacks, Tag 05TD], [Stacks, Tag 0152], [Stacks, Tag 05SV]
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.Functor

open _root_.DerivedCategory

section EpiMap

variable {C D : Type*} [Category* C] [Category* D]

/-- A natural isomorphism of functors does not change which morphisms are sent to epimorphisms. -/
private lemma epi_map_iff_of_natIso' {G₁ G₂ : C ⥤ D} (e : G₁ ≅ G₂) {X Y : C} (f : X ⟶ Y) :
    Epi (G₁.map f) ↔ Epi (G₂.map f) := by
  constructor <;> intro _
  · rw [← NatIso.naturality_1 e f]
    infer_instance
  · rw [← NatIso.naturality_2 e f]
    infer_instance

end EpiMap

section

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
  [(F.mapHomotopyCategoryPlus ⋙ Plus.Qh).HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso C)]

/-- The commutation with the shift of the right derived functor `RF` of `K⁺(F) ⋙ Q⁺`, induced by
its universal property. -/
@[instance_reducible]
private noncomputable def commShiftTotalRightDerived :
    ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).totalRightDerived Plus.Qh
      (HomotopyCategory.Plus.quasiIso C)).CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift _
    ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).totalRightDerivedUnit Plus.Qh
      (HomotopyCategory.Plus.quasiIso C)) (HomotopyCategory.Plus.quasiIso C) ℤ

attribute [local instance] commShiftTotalRightDerived

/-- The unit of `RF` is compatible with the shift. -/
private lemma natTransCommShiftTotalRightDerivedUnit :
    NatTrans.CommShift ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).totalRightDerivedUnit Plus.Qh
      (HomotopyCategory.Plus.quasiIso C)) ℤ :=
  Functor.IsRightDerivedFunctor.natTrans_commShift _ _ (HomotopyCategory.Plus.quasiIso C) ℤ

attribute [local instance] natTransCommShiftTotalRightDerivedUnit

/-- An everywhere defined `RF` is an exact functor. -/
private lemma isTriangulated_totalRightDerived
    (hF : (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).IsRightDerivable
      (HomotopyCategory.Plus.quasiIso C)) :
    ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).totalRightDerived Plus.Qh
      (HomotopyCategory.Plus.quasiIso C)).IsTriangulated := by
  have : (HomotopyCategory.Plus.quasiIso C).IsCompatibleWithTriangulation := by
    rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
    infer_instance
  have hsat : (HomotopyCategory.Plus.quasiIso C).IsSaturated := by
    have hleft : (HomotopyCategory.Plus.quasiIso C).HasLeftCalculusOfFractions := by
      rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
      infer_instance
    have hright : (HomotopyCategory.Plus.quasiIso C).HasRightCalculusOfFractions := by
      rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
      infer_instance
    refine ⟨hleft, hright, ?_⟩
    intro X Y Z T f g h hfg hgh n
    let H := HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n
    have : IsIso (H.map f.hom ≫ H.map g.hom) := by
      rw [← H.map_comp]; exact hfg n
    have : IsIso (H.map g.hom ≫ H.map h.hom) := by
      rw [← H.map_comp]; exact hgh n
    have : Epi (H.map g.hom) := epi_of_epi (H.map f.hom) (H.map g.hom)
    have : Mono (H.map g.hom) := mono_of_mono (H.map g.hom) (H.map h.hom)
    exact isIso_of_mono_of_epi (H.map g.hom)
  exact isTriangulated_of_isRightDerivable _ _ Plus.Qh _
    ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).totalRightDerivedUnit Plus.Qh
      (HomotopyCategory.Plus.quasiIso C)) hsat hF

/-- The canonical isomorphism `F ≅ R ⁰ F` for a left exact `F` and an everywhere defined `RF`:
`H ⁰` of the unit of `RF` at the complexes `A[0]`, conjugated by the identifications of its source
with `F` and of its target with `R ⁰ F`. -/
private noncomputable def isoTotalRightDerivedPlusHomologyZero [PreservesFiniteLimits F]
    (hF : (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).IsRightDerivable
      (HomotopyCategory.Plus.quasiIso C)) :
    F ≅ F.totalRightDerivedPlusHomology 0 :=
  haveI : IsIso (Functor.whiskerRight (Functor.whiskerLeft
      (HomotopyCategory.Plus.singleFunctor C 0)
      ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).totalRightDerivedUnit Plus.Qh
        (HomotopyCategory.Plus.quasiIso C))) (Plus.homologyFunctor D 0)) :=
    haveI : ∀ A : C, IsIso ((Functor.whiskerRight (Functor.whiskerLeft
        (HomotopyCategory.Plus.singleFunctor C 0)
        ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).totalRightDerivedUnit Plus.Qh
          (HomotopyCategory.Plus.quasiIso C))) (Plus.homologyFunctor D 0)).app A) :=
      fun A ↦ isIso_homologyFunctor_map_app_of_isRightDerivable F _ _ hF A
    NatIso.isIso_of_isIso_app _
  (Functor.isoWhiskerRight (mapSingleFunctorCompQhIso F) (Plus.homologyFunctor D 0) ≪≫
      Functor.isoWhiskerLeft F (Plus.singleFunctorCompHomologyFunctorIso 0) ≪≫
      F.rightUnitor).symm ≪≫
    asIso (Functor.whiskerRight (Functor.whiskerLeft (HomotopyCategory.Plus.singleFunctor C 0)
      ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).totalRightDerivedUnit Plus.Qh
        (HomotopyCategory.Plus.quasiIso C))) (Plus.homologyFunctor D 0)) ≪≫
    (Functor.isoWhiskerRight (singleFunctorPlusIsoCompQh 0)
      ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).totalRightDerived Plus.Qh
        (HomotopyCategory.Plus.quasiIso C) ⋙ Plus.homologyFunctor D 0)).symm

variable {S : ShortComplex C} (hS : S.ShortExact)
  (hF : (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).IsRightDerivable
    (HomotopyCategory.Plus.quasiIso C))

include hS hF

/-- The long exact cohomology sequence of `RF` applied to the triangle of `S`: there is a
distinguished triangle of `D⁺(ℬ)` whose vertices are `RF(A[0])`, `RF(B[0])`, `RF(C[0])` and whose
first two morphisms are `RF` of `S.f[0]` and `S.g[0]`. -/
private lemma exists_derivedTriangle :
    ∃ δ, Triangle.mk
        (((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).totalRightDerived Plus.Qh
          (HomotopyCategory.Plus.quasiIso C)).map ((Plus.singleFunctor C 0).map S.f))
        (((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).totalRightDerived Plus.Qh
          (HomotopyCategory.Plus.quasiIso C)).map ((Plus.singleFunctor C 0).map S.g)) δ ∈
      distTriang (DerivedCategory.Plus D) := by
  have := isTriangulated_totalRightDerived F hF
  obtain ⟨δ, hT⟩ := exists_distTriang_singleFunctor (A := C) hS
  exact ⟨_, ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).totalRightDerived Plus.Qh
    (HomotopyCategory.Plus.quasiIso C)).map_distinguished _ hT⟩

/-- Exactness at `R ⁱ F(B)`: if `R ⁱ F(A) = 0` and `R ⁱ F(C) = 0` then `R ⁱ F(B) = 0`. -/
private lemma isZero_X₂ (i : ℤ)
    (h₁ : IsZero ((F.totalRightDerivedPlusHomology i).obj S.X₁))
    (h₃ : IsZero ((F.totalRightDerivedPlusHomology i).obj S.X₃)) :
    IsZero ((F.totalRightDerivedPlusHomology i).obj S.X₂) := by
  obtain ⟨δ, hT⟩ := exists_derivedTriangle F hS hF
  exact ((Plus.homologyFunctor D 0).homologySequence_exact₂ _ hT i).isZero_X₂_iff.2
    ⟨h₁.eq_of_src _ _, h₃.eq_of_tgt _ _⟩

/-- Exactness at `R ⁱ F(C)`: if `R ⁱ F(B) = 0` and `R ⁱ⁺¹ F(A) = 0` then `R ⁱ F(C) = 0`. -/
private lemma isZero_X₃ (i : ℤ)
    (h₂ : IsZero ((F.totalRightDerivedPlusHomology i).obj S.X₂))
    (h₁ : IsZero ((F.totalRightDerivedPlusHomology (i + 1)).obj S.X₁)) :
    IsZero ((F.totalRightDerivedPlusHomology i).obj S.X₃) := by
  obtain ⟨δ, hT⟩ := exists_derivedTriangle F hS hF
  exact ((Plus.homologyFunctor D 0).homologySequence_exact₃ _ hT i (i + 1) rfl).isZero_X₂_iff.2
    ⟨h₂.eq_of_src _ _, h₁.eq_of_tgt _ _⟩

/-- `R ⁿ F(B) ⟶ R ⁿ F(C)` is epi exactly when the connecting morphism `R ⁿ F(C) ⟶ R ⁿ⁺¹ F(A)`
of the long exact sequence vanishes, and then `R ⁿ⁺¹ F(B) = 0` forces `R ⁿ⁺¹ F(A) = 0`. -/
private lemma isZero_X₁ (n : ℤ)
    (hg : Epi ((F.totalRightDerivedPlusHomology n).map S.g))
    (h₂ : IsZero ((F.totalRightDerivedPlusHomology (n + 1)).obj S.X₂)) :
    IsZero ((F.totalRightDerivedPlusHomology (n + 1)).obj S.X₁) := by
  obtain ⟨δ, hT⟩ := exists_derivedTriangle F hS hF
  exact ((Plus.homologyFunctor D 0).homologySequence_exact₁ _ hT n (n + 1) rfl).isZero_X₂_iff.2
    ⟨((Plus.homologyFunctor D 0).homologySequence_epi_shift_map_mor₂_iff _ hT n (n + 1) rfl).1 hg,
      h₂.eq_of_tgt _ _⟩

/-- `R ⁿ F(B) ⟶ R ⁿ F(C)` is epi as soon as `R ⁿ⁺¹ F(A) = 0`. -/
private lemma epi_map_g (n : ℤ)
    (h₁ : IsZero ((F.totalRightDerivedPlusHomology (n + 1)).obj S.X₁)) :
    Epi ((F.totalRightDerivedPlusHomology n).map S.g) := by
  obtain ⟨δ, hT⟩ := exists_derivedTriangle F hS hF
  exact ((Plus.homologyFunctor D 0).homologySequence_epi_shift_map_mor₂_iff _ hT n (n + 1)
    rfl).2 (h₁.eq_of_tgt _ _)

end

/-- **Right acyclicity in a short exact sequence**, [StacksProject 015D].
Let `F : 𝒜 ⥤ ℬ` be a left exact functor between abelian categories and assume that
`RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is everywhere defined, that is, `K⁺(F) ⋙ Q⁺` is right derivable with
respect to the quasi-isomorphisms of `K⁺(𝒜)` ([Stacks, Tag 05SV]). Let
`S : 0 ⟶ A ⟶ B ⟶ C ⟶ 0` be a short exact sequence of `𝒜`. Then
1. if `A` and `C` are right acyclic for `F`, so is `B`,
2. if `A` and `B` are right acyclic for `F`, so is `C`, and
3. if `B` and `C` are right acyclic for `F` and `F(B) ⟶ F(C)` is surjective, then so is `A`,
and in each of the three cases `0 ⟶ F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is a short exact sequence of `ℬ`.

The instance `HasRightDerivedFunctor` follows from `hF`
(`Functor.hasPointwiseRightDerivedFunctor_of_isRightDerivable`); it names `RF` and the predicate
`Functor.rightAcyclic`. No injective objects are assumed; with enough injectives this is
`Functor.rightAcyclic_and_shortExact_map_of_shortExact`. -/
@[stacks 015D "`RF` everywhere defined is `Functor.IsRightDerivable` of `K⁺(F) ⋙ Q⁺` \
(Tag 05SV); surjectivity of `F(B) ⟶ F(C)` is `Epi (F.map S.g)`"]
public theorem rightAcyclic_and_shortExact_map_of_shortExact_of_isRightDerivable
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F]
    [(F.mapHomotopyCategoryPlus ⋙ Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso C)]
    (hF : (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).IsRightDerivable
      (HomotopyCategory.Plus.quasiIso C))
    (S : ShortComplex C) (hS : S.ShortExact) :
    (F.rightAcyclic S.X₁ → F.rightAcyclic S.X₃ →
        F.rightAcyclic S.X₂ ∧ (S.map F).ShortExact) ∧
      (F.rightAcyclic S.X₁ → F.rightAcyclic S.X₂ →
        F.rightAcyclic S.X₃ ∧ (S.map F).ShortExact) ∧
      (F.rightAcyclic S.X₂ → F.rightAcyclic S.X₃ → Epi (F.map S.g) →
        F.rightAcyclic S.X₁ ∧ (S.map F).ShortExact) := by
  -- [Stacks, Tag 015C] part (2): for a left exact `F`, right acyclicity is the vanishing of
  -- `R ⁱ F` in positive degrees.
  have hac := fun A : C ↦
    (rightAcyclic_iff_isIso_and_isZero_totalRightDerivedPlusHomology F hF A).2 ‹_›
  have he := isoTotalRightDerivedPlusHomologyZero F hF
  -- `F(B) ⟶ F(C)` is epi as soon as `R ¹ F(A) = 0`.
  have hepi : IsZero ((F.totalRightDerivedPlusHomology 1).obj S.X₁) → Epi (F.map S.g) :=
    fun h ↦ (epi_map_iff_of_natIso' he S.g).2 (epi_map_g F hS hF 0 h)
  -- A left exact `F` takes `S` to a short exact sequence as soon as `F(B) ⟶ F(C)` is epi.
  have shortExact_map : Epi (F.map S.g) → (S.map F).ShortExact := fun hg ↦
    have h := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono F).1 ‹_› S hS
    { exact := h.1, mono_f := h.2, epi_g := hg }
  refine ⟨fun h₁ h₃ ↦ ⟨(hac _).2 fun i hi ↦
      isZero_X₂ F hS hF i ((hac _).1 h₁ i hi) ((hac _).1 h₃ i hi),
      shortExact_map (hepi ((hac _).1 h₁ 1 one_pos))⟩,
    fun h₁ h₂ ↦ ⟨(hac _).2 fun i hi ↦
      isZero_X₃ F hS hF i ((hac _).1 h₂ i hi) ((hac _).1 h₁ (i + 1) (hi.trans (lt_add_one i))),
      shortExact_map (hepi ((hac _).1 h₁ 1 one_pos))⟩,
    fun h₂ h₃ hg ↦ ⟨(hac _).2 fun i hi ↦ ?_, shortExact_map hg⟩⟩
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, (Int.sub_add_cancel i 1).symm⟩
  refine isZero_X₁ F hS hF n ?_ ((hac _).1 h₂ _ hi)
  rcases (Int.lt_add_one_iff.mp hi).eq_or_lt with rfl | h
  · exact (epi_map_iff_of_natIso' he S.g).1 hg
  · exact ((hac _).1 h₃ n h).epi _

end CategoryTheory.Functor

end
