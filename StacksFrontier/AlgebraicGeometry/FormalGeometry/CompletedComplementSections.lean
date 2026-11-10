module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletedLocalCohomologyShrink
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionUnitLocalCohomology
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.LocalizationData

/-!
# The completion of the affine localization triangle

Let `I`, `J` and `J'` be ideals of a Noetherian ring `A` with `A` `I`-adically complete, let `M`
be a finite `A`-module and write `V = Spec(A) ∖ V(J')`. The localization triangle of Stacks 0DWR

`RΓ_{J'}(M) ⟶ M ⟶ RΓ(V, M̃) ⟶ RΓ_{J'}(M)[1]`

is distinguished, and derived `I`-adic completion is a triangulated endofunctor of `D(A)`, so
its completion is distinguished too and the unit of completion is a morphism between the two.
On the second vertex the unit is invertible, `M` being a finite module over an `I`-adically
complete Noetherian ring. Hence, as soon as the unit is invertible on `H⁰` and `H¹` of the first
vertex — which for a suitable `J'` is the conclusion of Stacks 0EFL — the five lemma makes it
invertible on `H⁰` of the third:

`Γ(V, M̃) ⟶ H⁰(RΓ(V, M̃)^∧)`

is an isomorphism. This is the second row of the diagram in the proof of Stacks 0EIF, compared
with its first row.

## Main results

* `Stacks.Algebraization.isIso_homologyMap_third_of_isIso_outer` — the five lemma for the third
  vertices of a morphism of distinguished triangles.
* `Stacks.Algebraization.isIso_homology_unit_third` — the same for the morphism of triangles
  given by a natural transformation into a triangulated functor.
* `Stacks.Algebraization.isIso_homology_zero_completionUnit_complement` — the conclusion above:
  the completion unit is invertible on `H⁰` of the derived sections on `V`.

## Implementation notes

The `CommShift ℤ` and `IsTriangulated` instances for
`Stacks.Algebraization.adicCompletionFunctor` are `private` where they are first established, so
they are re-derived here from `Stacks.Algebraization.adicCompletionAdjunction` by the same three
lines: the unit of the adjunction commutes with the shift because its left adjoint does, and a
left adjoint of a triangulated functor is triangulated.

The hypothesis is stated as invertibility of
`Stacks.Algebraization.localCohomologyToCompletedLocalCohomology` — the arrow of Stacks 0EFL —
rather than of the bare unit, because that is the shape in which Stacks 0EFL concludes. The two
differ by `Stacks.Algebraization.completedLocalCohomologyShrinkIso`, which is invertible, so the
hypothesis transfers to the unit.

## References

* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-! ### The five lemma at the third vertex -/

/-- **A five lemma for the third vertices of a morphism of distinguished triangles.** If the
morphism is invertible on `H^i` and `H^{i+1}` of the first and second vertices, then it is
invertible on `H^i` of the third. -/
theorem isIso_homologyMap_third_of_isIso_outer
    {C : Type*} [Category C] [Abelian C]
    {T T' : Triangle (DerivedCategory C)}
    (hT : T ∈ distTriang _) (hT' : T' ∈ distTriang _)
    (φ : T ⟶ T') (i j : ℤ) (hij : i + 1 = j)
    [IsIso ((DerivedCategory.homologyFunctor C i).map φ.hom₁)]
    [IsIso ((DerivedCategory.homologyFunctor C i).map φ.hom₂)]
    [IsIso ((DerivedCategory.homologyFunctor C j).map φ.hom₁)]
    [IsIso ((DerivedCategory.homologyFunctor C j).map φ.hom₂)] :
    IsIso ((DerivedCategory.homologyFunctor C i).map φ.hom₃) := by
  let H := DerivedCategory.homologyFunctor C
  let R := fun (S : Triangle (DerivedCategory C)) => ComposableArrows.mk₄
    ((H i).map S.mor₁) ((H i).map S.mor₂)
    (DerivedCategory.HomologySequence.δ S i j hij) ((H j).map S.mor₁)
  have he : ∀ S, S ∈ distTriang _ → (R S).Exact := fun S hS =>
    ComposableArrows.exact_of_δ₀
      (DerivedCategory.HomologySequence.exact₂ S hS i).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        (DerivedCategory.HomologySequence.exact₃ S hS i j hij).exact_toComposableArrows
        (DerivedCategory.HomologySequence.exact₁ S hS i j hij).exact_toComposableArrows)
  let ψ : R T ⟶ R T' := ComposableArrows.homMk₄
    ((H i).map φ.hom₁) ((H i).map φ.hom₂) ((H i).map φ.hom₃)
    ((H j).map φ.hom₁) ((H j).map φ.hom₂)
    (by change (H i).map T.mor₁ ≫ _ = _ ≫ (H i).map T'.mor₁
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
    (by change (H i).map T.mor₂ ≫ _ = _ ≫ (H i).map T'.mor₂
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂])
    ((H 0).homologySequenceδ_naturality φ i j hij).symm
    (by change (H j).map T.mor₁ ≫ _ = _ ≫ (H j).map T'.mor₁
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono (he T hT) (he T' hT') ψ
    (inferInstanceAs (Epi ((H i).map φ.hom₁)))
    (inferInstanceAs (IsIso ((H i).map φ.hom₂)))
    (inferInstanceAs (IsIso ((H j).map φ.hom₁)))
    (inferInstanceAs (Mono ((H j).map φ.hom₂)))

/-- The previous five lemma for the morphism of triangles given by a natural transformation into
a triangulated functor. -/
theorem isIso_homology_unit_third
    {C : Type*} [Category C] [Abelian C]
    (F : DerivedCategory C ⥤ DerivedCategory C) [F.CommShift ℤ] [F.IsTriangulated]
    (η : 𝟭 _ ⟶ F) [NatTrans.CommShift η ℤ]
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (i j : ℤ) (hij : i + 1 = j)
    [IsIso ((DerivedCategory.homologyFunctor C i).map (η.app T.obj₁))]
    [IsIso ((DerivedCategory.homologyFunctor C i).map (η.app T.obj₂))]
    [IsIso ((DerivedCategory.homologyFunctor C j).map (η.app T.obj₁))]
    [IsIso ((DerivedCategory.homologyFunctor C j).map (η.app T.obj₂))] :
    IsIso ((DerivedCategory.homologyFunctor C i).map (η.app T.obj₃)) := by
  let φ : T ⟶ F.mapTriangle.obj T :=
    { hom₁ := η.app T.obj₁
      hom₂ := η.app T.obj₂
      hom₃ := η.app T.obj₃
      comm₁ := η.naturality T.mor₁
      comm₂ := η.naturality T.mor₂
      comm₃ := by
        change T.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map (η.app T.obj₁) =
          η.app T.obj₃ ≫ F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁
        rw [← Category.assoc, ← η.naturality T.mor₃, Functor.id_map,
          Category.assoc, ← η.shift_app_comm]
        simp }
  have h₁ : IsIso ((DerivedCategory.homologyFunctor C i).map φ.hom₁) :=
    inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor C i).map (η.app T.obj₁)))
  have h₂ : IsIso ((DerivedCategory.homologyFunctor C i).map φ.hom₂) :=
    inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor C i).map (η.app T.obj₂)))
  have h₁' : IsIso ((DerivedCategory.homologyFunctor C j).map φ.hom₁) :=
    inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor C j).map (η.app T.obj₁)))
  have h₂' : IsIso ((DerivedCategory.homologyFunctor C j).map φ.hom₂) :=
    inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor C j).map (η.app T.obj₂)))
  exact isIso_homologyMap_third_of_isIso_outer hT (F.map_distinguished T hT) φ i j hij

/-! ### The completion of the localization triangle -/

section Complement

/-- Cancelling an isomorphism on the right, in cohomology. Stated with abstract objects so that
the rewrite by `Functor.map_comp` fires: at the one place it is used, the two spellings of the
middle object agree only at default transparency. -/
private theorem isIso_homologyMap_of_eq_comp_iso
    {C : Type*} [Category C] [Abelian C] (i : ℤ)
    {X Y Z : DerivedCategory C} (f : X ⟶ Y) (e : Y ≅ Z) (g : X ⟶ Z) (hg : g = f ≫ e.hom)
    (h : IsIso ((DerivedCategory.homologyFunctor C i).map g)) :
    IsIso ((DerivedCategory.homologyFunctor C i).map f) := by
  subst hg
  rw [Functor.map_comp] at h
  exact IsIso.of_isIso_comp_right ((DerivedCategory.homologyFunctor C i).map f)
    ((DerivedCategory.homologyFunctor C i).map e.hom)

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- **The second row of the diagram in the proof of Stacks 0EIF.** Let `I`, `J` and `J'` be
ideals of a Noetherian ring `A` which is `I`-adically complete, with
`V(J') ∩ V(I) = V(J) ∩ V(I)`, let `M` be a finite `A`-module and let `V = Spec(A) ∖ V(J')`.
Assume the arrow `RΓ_{J'}(M) ⟶ RΓ_J(M)^∧` of Stacks 0EFL is invertible on cohomology in all
degrees `≤ 1`. Then the unit of derived `I`-adic completion is invertible on `H⁰` of the derived
sections of `M̃` on `V`:

`Γ(V, M̃) ⟶ H⁰(RΓ(V, M̃)^∧)`

is an isomorphism.

The three vertices of the localization triangle are `RΓ_{J'}(M)`, `M` and `RΓ(V, M̃)`. On the
second the unit is invertible outright, by
`Stacks.Algebraization.isIso_completionUnit_single`; on the first it is invertible in degrees
`0` and `1` by hypothesis, the arrow of Stacks 0EFL being the unit followed by the invertible
`Stacks.Algebraization.completedLocalCohomologyShrinkIso`. The five lemma at the third vertex
then gives the conclusion. -/
theorem isIso_homology_zero_completionUnit_complement
    (I J J' : Ideal A) (hcomplete : IsAdicComplete I A)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (D : Stacks.LocalCohomology.LocalizationTriangleData.{u, u} A J'
      J'.fg_of_isNoetherianRing)
    (h : ∀ i : ℤ, i ≤ 1 → IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      (localCohomologyToCompletedLocalCohomology A I J J' I.fg_of_isNoetherianRing
        J.fg_of_isNoetherianRing J'.fg_of_isNoetherianRing M hV))) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((adicCompletionUnit A I I.fg_of_isNoetherianRing).app (D.complement.obj M))) := by
  have := hcomplete
  let adj := adicCompletionAdjunction A I I.fg_of_isNoetherianRing
  let := adj.leftAdjointCommShift ℤ
  have := adj.commShift_of_rightAdjoint ℤ
  have : (Dualizing.derivedCompletion.{u, u} A I I.fg_of_isNoetherianRing).IsTriangulated :=
    adj.isTriangulated_leftAdjoint
  -- The unit is invertible on the second vertex `M`, a finite module over a complete ring.
  have h₂ : IsIso ((adicCompletionUnit A I I.fg_of_isNoetherianRing).app
      (D.triangle M).obj₂) :=
    isIso_completionUnit_single I I.fg_of_isNoetherianRing M
  -- The unit is invertible on `H⁰` and `H¹` of the first vertex `RΓ_{J'}(M)`.
  have hshrink : ∀ i : ℤ, i ≤ 1 →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        ((adicCompletionUnit A I I.fg_of_isNoetherianRing).app (D.triangle M).obj₁)) := by
    intro i hi
    have hcomp : localCohomologyToCompletedLocalCohomology A I J J' I.fg_of_isNoetherianRing
          J.fg_of_isNoetherianRing J'.fg_of_isNoetherianRing M hV =
        (adicCompletionUnit A I I.fg_of_isNoetherianRing).app (D.triangle M).obj₁ ≫
          (completedLocalCohomologyShrinkIso A I J J' I.fg_of_isNoetherianRing
            J.fg_of_isNoetherianRing J'.fg_of_isNoetherianRing M hV).hom := rfl
    exact isIso_homologyMap_of_eq_comp_iso i _
      (completedLocalCohomologyShrinkIso A I J J' I.fg_of_isNoetherianRing
        J.fg_of_isNoetherianRing J'.fg_of_isNoetherianRing M hV) _ hcomp (h i hi)
  have := hshrink 0 (by omega)
  have := hshrink 1 le_rfl
  exact isIso_homology_unit_third (adicCompletionFunctor A I I.fg_of_isNoetherianRing)
    (adicCompletionUnit A I I.fg_of_isNoetherianRing) (D.triangle M) (D.distinguished M) 0 1 rfl

end Complement

end Stacks.Algebraization

end
