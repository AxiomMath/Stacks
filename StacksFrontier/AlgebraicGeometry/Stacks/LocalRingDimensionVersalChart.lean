module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalRingDimensionChartComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalRingDimensionVersal

/-!
# The dimension of the local ring of an algebraic stack is `2 dim A - dim B` (Stacks 0DSB)

Let `𝒳` be an algebraic stack locally of finite type over a locally Noetherian scheme `S`, let
`x₀ : Spec k ⟶ 𝒳` be a morphism with `k` of finite type over `S`, and represent `𝓕_{𝒳,k,x₀}` as in
Remark 0DR3 by a cogroupoid `(A, B, s, t, c)`. Then the dimension of the local ring of `𝒳` at the
point of `x₀`, the single integer of Stacks 0DS9 and 0DSA, is `2 dim A - dim B`.

## Main results

* `AlgebraicGeometry.Stack.hasLocalRingDimensionAtSomeChart_iff_of_versalCogroupoid`:
  **Stacks 0DSB**. An integer `d` satisfies condition (1) of Stacks 0DS9
  (`AlgebraicGeometry.Stack.HasLocalRingDimensionAtSomeChart`) at the point of `x₀` exactly when
  `d = 2 dim A - dim B`.
* `AlgebraicGeometry.Stack.hasLocalRingDimensionAtSomeChart_iff_of_isVersal`: the same for any
  ring `B` prorepresenting the isomorphisms of the versal object.

## Implementation notes

The chart computation is
`AlgebraicGeometry.Stack.exists_canonicalChart_hasRelationLocalRingDimension_of_isVersal`, which
builds the witness of condition (1) of Stacks 0DS9 at the canonical identification of the chart.
That the integer is the only one is the chart independence of Stacks 0DS9,
`AlgebraicGeometry.Stack.hasLocalRingDimensionAtSomeChart_unique`.

## References

* [Stacks Project, Tag 0DSB](https://stacks.math.columbia.edu/tag/0DSB)
* [Stacks Project, Tag 0DS9](https://stacks.math.columbia.edu/tag/0DS9)
* [Stacks Project, Tag 0DSA](https://stacks.math.columbia.edu/tag/0DSA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

/-- **Stacks 0DSB, at the canonical identification of the chart, for any ring prorepresenting the
isomorphisms of a versal object.** In Situation 0DQU, let `x₀` be an object of `𝒳` over `Spec k`,
`k` of finite type over `S`, let `Spec Λ ⊆ S` be an affine open through which `Spec k ⟶ S` factors
with `Λ → k` finite (Section 07T2), let `ξ` be a versal formal object of `𝓕_{𝒳,k,x₀}` over `A` and
let `B` be a Noetherian complete local `Λ`-algebra with residue field `k` with
`B|_{𝒞_Λ} ≅ A|_{𝒞_Λ} ×_{ξ, 𝓕, ξ} A|_{𝒞_Λ}`. Then condition (1) of Stacks 0DS9
(`AlgebraicGeometry.Stack.HasLocalRingDimensionAtSomeChart`) holds at the point of `x₀` with the
integer `2 dim A - dim B`. By Stacks 0DS9 that integer is the only one satisfying it; see
`AlgebraicGeometry.Stack.hasLocalRingDimensionAtSomeChart_iff_of_isVersal`. -/
theorem hasLocalRingDimensionAtSomeChart_of_isVersal (D : VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    let C := Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀
    letI := C.category
    let hp := Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property
    ∀ (ξ : Deformation.FormalObject C.projection) (_ : Deformation.IsVersal hp.cofibered ξ)
      (Bv : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
      (_ : Deformation.restrictedCoyoneda Bv ≅
        (Deformation.versalGroupoid C.projection hp ξ).arrows),
      ∃ m n : ℕ, ringKrullDim ξ.base = m ∧ ringKrullDim Bv = n ∧
        HasLocalRingDimensionAtSomeChart D.B D.S D.hS D.𝒳
          (isLocallyNoetherianStack_of_versalSituation D) (objectPoint D.B D.S D.hS iΛ x₀ hx₀)
          (isFiniteTypePoint_objectPoint D iΛ hiΛ x₀ hx₀ hfinite) (2 * (m : ℤ) - (n : ℤ)) := by
  intro C hp ξ hξ Bv e
  exact exists_canonicalChart_hasRelationLocalRingDimension_of_isVersal D iΛ hiΛ x₀ hx₀ hfinite ξ
    hξ Bv e

/-- **Stacks 0DSB, for any ring prorepresenting the isomorphisms of a versal object.** Under the
hypotheses of `AlgebraicGeometry.Stack.hasLocalRingDimensionAtSomeChart_of_isVersal`, the
dimension of the local ring of `𝒳` at the point of `x₀` (Stacks 0DSA, condition (1) of Stacks
0DS9) is `2 dim A - dim B`: an integer `d` is the dimension of the local ring there exactly when
`d = 2 dim A - dim B`. Uniqueness is the chart independence of Stacks 0DS9,
`AlgebraicGeometry.Stack.hasLocalRingDimensionAtSomeChart_unique`. -/
theorem hasLocalRingDimensionAtSomeChart_iff_of_isVersal (D : VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    let C := Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀
    letI := C.category
    let hp := Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property
    ∀ (ξ : Deformation.FormalObject C.projection) (_ : Deformation.IsVersal hp.cofibered ξ)
      (Bv : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
      (_ : Deformation.restrictedCoyoneda Bv ≅
        (Deformation.versalGroupoid C.projection hp ξ).arrows),
      ∃ m n : ℕ, ringKrullDim ξ.base = m ∧ ringKrullDim Bv = n ∧
        ∀ d : ℤ, HasLocalRingDimensionAtSomeChart D.B D.S D.hS D.𝒳
          (isLocallyNoetherianStack_of_versalSituation D) (objectPoint D.B D.S D.hS iΛ x₀ hx₀)
          (isFiniteTypePoint_objectPoint D iΛ hiΛ x₀ hx₀ hfinite) d ↔
            d = 2 * (m : ℤ) - (n : ℤ) := by
  intro C hp ξ hξ Bv e
  obtain ⟨m, n, hm, hn, h⟩ :=
    hasLocalRingDimensionAtSomeChart_of_isVersal D iΛ hiΛ x₀ hx₀ hfinite ξ hξ Bv e
  exact ⟨m, n, hm, hn, fun d => ⟨fun hd => hasLocalRingDimensionAtSomeChart_unique D.B D.S D.hS
    D.𝒳 _ _ _ hd h, fun hd => hd ▸ h⟩⟩

/-- **Stacks 0DSB.** Let `𝒳` be an algebraic stack, locally of finite type over a locally
Noetherian scheme `S` (Situation 0DQU), and let `x₀ : Spec k ⟶ 𝒳` be a morphism, `k` a field of
finite type over `S`, with `Spec Λ ⊆ S` an affine open through which `Spec k ⟶ S` factors with
`Λ → k` finite (Section 07T2). Represent `𝓕_{𝒳,k,x₀}` as in Remark 0DR3 by a cogroupoid
`(A, B, s, t, c)` of Noetherian complete local `Λ`-algebras with residue field `k`: a versal formal
object `ξ` over `A` and a representable presentation `P` on `𝒞^_Λ` with objects `P.objects = A`,
arrows `P.arrows = B`, source and target `s = P.source`, `t = P.target` and comultiplication
`c = P.comultiplication`, whose restriction to `𝒞_Λ` is the groupoid in functors
`(A|_{𝒞_Λ}, A|_{𝒞_Λ} ×_{ξ, 𝓕, ξ} A|_{𝒞_Λ})` of `ξ` (this is the representation produced by
`AlgebraicGeometry.Stack.exists_versalCogroupoid_predeformationCategory`). Then the dimension of
the local ring of `𝒳` at the point of `x₀` (Stacks 0DSA, the single integer of Stacks 0DS9) is
`2 dim A - dim B`: an integer `d` satisfies condition (1) of Stacks 0DS9
(`AlgebraicGeometry.Stack.HasLocalRingDimensionAtSomeChart`) at that point exactly when
`d = 2 dim A - dim B`.

Every such representation is allowed, so the statement holds for all of them; the two dimensions
are finite and are recorded as natural numbers before the difference is taken, as in Stacks
0DSA. -/
@[stacks 0DSB]
theorem hasLocalRingDimensionAtSomeChart_iff_of_versalCogroupoid (D : VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    let C := Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀
    letI := C.category
    let hp := Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property
    ∀ (ξ : Deformation.FormalObject C.projection) (_ : Deformation.IsVersal hp.cofibered ξ)
      (P : Deformation.RepresentablePresentation.{_, u, u}
        (Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)),
      P.objects = ξ.base →
      Nonempty (Deformation.versalGroupoid C.projection hp ξ ≅
        Deformation.GroupoidInFunctors.restrict P.groupoidInFunctors
          Deformation.artinianToComplete) →
      ∃ m n : ℕ, ringKrullDim P.objects = m ∧ ringKrullDim P.arrows = n ∧
        ∀ d : ℤ, HasLocalRingDimensionAtSomeChart D.B D.S D.hS D.𝒳
          (isLocallyNoetherianStack_of_versalSituation D) (objectPoint D.B D.S D.hS iΛ x₀ hx₀)
          (isFiniteTypePoint_objectPoint D iΛ hiΛ x₀ hx₀ hfinite) d ↔
            d = 2 * (m : ℤ) - (n : ℤ) := by
  intro C hp ξ hξ P hPo ⟨eG⟩
  let K := Deformation.GroupoidInFunctors.restrict P.groupoidInFunctors
    Deformation.artinianToComplete
  -- the arrow functors of an isomorphism of groupoids in functors
  let eA : (Deformation.versalGroupoid C.projection hp ξ).arrows ≅ K.arrows :=
    { hom := eG.hom.mapArrows
      inv := eG.inv.mapArrows
      hom_inv_id := congrArg (fun f : Deformation.GroupoidInFunctors.Hom _ _ => f.mapArrows)
        eG.hom_inv_id
      inv_hom_id := congrArg (fun f : Deformation.GroupoidInFunctors.Hom _ _ => f.mapArrows)
        eG.inv_hom_id }
  let uB : K.arrows ≅ Deformation.restrictedCoyoneda P.arrows :=
    Functor.isoWhiskerLeft Deformation.artinianToComplete
      ((CategoryTheory.uliftCoyonedaIsoCoyoneda.{u}).app (op P.arrows))
  obtain ⟨m, n, hm, hn, h⟩ :=
    hasLocalRingDimensionAtSomeChart_iff_of_isVersal D iΛ hiΛ x₀ hx₀ hfinite ξ hξ
    P.arrows (uB.symm ≪≫ eA.symm)
  exact ⟨m, n, hPo ▸ hm, hn, h⟩

end AlgebraicGeometry.Stack

end
