module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparison

/-!
# The comparison with derived pullback on algebraic spaces and translation, in each variable

The comparison map `Lf^*K ⊗ᴸ_{𝒪_X} a(𝒪_Y) ⟶ a(K)` of Equation 86.7.0.1 of Stacks 0E5P commutes
with translation in `K` when the derived tensor products commute with translation in the first
variable, naturally in the second, rather than in both variables jointly.

## Main results

All in the namespace `AlgebraicGeometry.Space.PullbackComparisonData`.

* `tensorPullbackComparisonFlip` and `projectionFormulaNatTrans_eq`: the projection-formula map
  in `K` through the unit of `Lf^* ⊣ Rf_*`.
* `projectionFormulaNatTrans_commShift`: the projection-formula map commutes with translation.
* `compareWithPullbackNatTrans_commShift_of_commShift_flip` and
  `compareWithPullback_shift_of_commShift_flip`: Equation 86.7.0.1 commutes with translation.

## References

* [Stacks Project, Tag 0E5P](https://stacks.math.columbia.edu/tag/0E5P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open scoped CategoryTheory.Prod

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

namespace PullbackComparisonData

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  [HasSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS X.1 X.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedSite B S hS Y.1 Y.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS Y.1 Y.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (D : PullbackComparisonData B S hS f)

/-- The compatibility of derived pullback with the two tensor products, the second factor `G`
being fixed: `Lf^*(K ⊗ᴸ_{𝒪_Y} G) ⟶ Lf^*K ⊗ᴸ_{𝒪_X} Lf^*G`, natural in `K`. -/
def tensorPullbackComparisonFlip (G : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    D.tensorY.flip.obj G ⋙ D.pullback ⟶ D.pullback ⋙ D.tensorX.flip.obj (D.pullback.obj G) where
  app K := D.tensorPullbackComparison.app (G, K)
  naturality K K' h := by
    simpa using D.tensorPullbackComparison.naturality
      ((𝟙 G, h) : ((G, K) : _ × _) ⟶ (G, K'))

/-- The projection-formula map in `K` is the unit of `Lf^* ⊣ Rf_*`, followed by `Rf_*` of the
compatibility of `Lf^*` with the tensor products and of the counit in the second factor. -/
theorem projectionFormulaNatTrans_eq (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    D.projectionFormulaNatTrans E =
      (D.tensorY.flip.obj (D.pushforward.obj E)).rightUnitor.inv ≫
      Functor.whiskerLeft (D.tensorY.flip.obj (D.pushforward.obj E)) D.adj.unit ≫
        (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (D.tensorPullbackComparisonFlip (D.pushforward.obj E) ≫
          Functor.whiskerLeft D.pullback (D.tensorX.flip.map (D.adj.counit.app E)))
          D.pushforward := by
  refine NatTrans.ext (funext fun K => ?_)
  refine (adjunctionTensorMap_eq_unit_comp _ _ _ _ _ _).trans ?_
  simp [tensorPullbackComparisonFlip]

/-- The source of Equation 86.7.0.1 commutes with translation when derived pullback and the
derived tensor product of `D_QCoh(𝒪_X)` do. -/
instance compareWithPullbackSource_commShift_of_commShift_flip
    (T : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    [D.pullback.CommShift ℤ] [(D.tensorX.flip.obj T).CommShift ℤ] :
    (D.compareWithPullbackSource T).CommShift ℤ := by
  unfold compareWithPullbackSource
  infer_instance

/-- The projection-formula map commutes with translation in `K` when the adjunction
`Lf^* ⊣ Rf_*`, the compatibility of `Lf^*` with the tensor products and the derived tensor
product of `D_QCoh(𝒪_X)` in its second variable do. -/
theorem projectionFormulaNatTrans_commShift
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    [D.pullback.CommShift ℤ] [D.pushforward.CommShift ℤ] [D.adj.CommShift ℤ]
    [∀ T : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2, (D.tensorX.flip.obj T).CommShift ℤ]
    [∀ L : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2, (D.tensorY.flip.obj L).CommShift ℤ]
    [∀ G : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2,
      NatTrans.CommShift (D.tensorPullbackComparisonFlip G) ℤ]
    [∀ {T T' : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2} (g : T ⟶ T'),
      NatTrans.CommShift (D.tensorX.flip.map g) ℤ] :
    NatTrans.CommShift (D.projectionFormulaNatTrans E) ℤ := by
  rw [D.projectionFormulaNatTrans_eq E]
  have h1 : NatTrans.CommShift (Functor.whiskerLeft (D.tensorY.flip.obj (D.pushforward.obj E))
    D.adj.unit) ℤ := inferInstance
  have h3 : NatTrans.CommShift (Functor.whiskerRight (D.tensorPullbackComparisonFlip
      (D.pushforward.obj E) ≫
          Functor.whiskerLeft D.pullback (D.tensorX.flip.map (D.adj.counit.app E)))
          D.pushforward) ℤ :=
    inferInstance
  have h4 := @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _
    (inferInstance : NatTrans.CommShift (Functor.associator
      (D.tensorY.flip.obj (D.pushforward.obj E)) D.pullback D.pushforward).inv ℤ) h3
  have h5 := @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ h1 h4
  exact @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _
    (inferInstance : NatTrans.CommShift
      (D.tensorY.flip.obj (D.pushforward.obj E)).rightUnitor.inv ℤ) h5

section Triangles

variable [∀ (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2),
    IsIso (D.projectionFormulaMap E K)]
  {a : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2 ⥤
    QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2}
  (adja : D.pushforward ⊣ a)
  (ρ : D.tensorY.flip.obj (derivedStructureSheaf B S hS Y.1 Y.2) ≅ 𝟭 _)

/-- The adjoint transpose of Equation 86.7.0.1 commutes with translation. -/
instance compareWithPullbackTranspose_commShift_of_commShift_flip
    [D.pullback.CommShift ℤ] [D.pushforward.CommShift ℤ]
    [∀ T : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2, (D.tensorX.flip.obj T).CommShift ℤ]
    [∀ L : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2, (D.tensorY.flip.obj L).CommShift ℤ]
    [∀ {L L' : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2} (g : L ⟶ L'),
      NatTrans.CommShift (D.tensorY.flip.map g) ℤ]
    [a.CommShift ℤ] [adja.CommShift ℤ]
    [NatTrans.CommShift (D.projectionFormulaNatTrans
      (a.obj (derivedStructureSheaf B S hS Y.1 Y.2))) ℤ]
    [NatTrans.CommShift ρ.hom ℤ] :
    NatTrans.CommShift (D.compareWithPullbackTranspose adja ρ) ℤ := by
  have := NatTrans.CommShift.of_isIso
    (τ := D.projectionFormulaNatTrans (a.obj (derivedStructureSheaf B S hS Y.1 Y.2))) (A := ℤ)
  unfold compareWithPullbackTranspose
  infer_instance

/-- **Compatibility of Equation 86.7.0.1 with distinguished triangles**: the displayed comparison
map commutes with translation, so it carries the third morphism of a distinguished triangle of
`D_QCoh(𝒪_Y)` to the third morphism of its image. -/
theorem compareWithPullbackNatTrans_commShift_of_commShift_flip
    [D.pullback.CommShift ℤ] [D.pushforward.CommShift ℤ]
    [∀ T : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2, (D.tensorX.flip.obj T).CommShift ℤ]
    [∀ L : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2, (D.tensorY.flip.obj L).CommShift ℤ]
    [∀ {L L' : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2} (g : L ⟶ L'),
      NatTrans.CommShift (D.tensorY.flip.map g) ℤ]
    [a.CommShift ℤ] [adja.CommShift ℤ]
    [NatTrans.CommShift (D.projectionFormulaNatTrans
      (a.obj (derivedStructureSheaf B S hS Y.1 Y.2))) ℤ]
    [NatTrans.CommShift ρ.hom ℤ] :
    NatTrans.CommShift (D.compareWithPullbackNatTrans adja ρ) ℤ := by
  rw [D.compareWithPullbackNatTrans_eq adja ρ]
  infer_instance

/-- Equation 86.7.0.1 at a translate of `K`, which is that compatibility componentwise. -/
theorem compareWithPullback_shift_of_commShift_flip
    [D.pullback.CommShift ℤ] [D.pushforward.CommShift ℤ]
    [∀ T : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2, (D.tensorX.flip.obj T).CommShift ℤ]
    [∀ L : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2, (D.tensorY.flip.obj L).CommShift ℤ]
    [∀ {L L' : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2} (g : L ⟶ L'),
      NatTrans.CommShift (D.tensorY.flip.map g) ℤ]
    [a.CommShift ℤ] [adja.CommShift ℤ]
    [NatTrans.CommShift (D.projectionFormulaNatTrans
      (a.obj (derivedStructureSheaf B S hS Y.1 Y.2))) ℤ]
    [NatTrans.CommShift ρ.hom ℤ]
    (n : ℤ)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    D.compareWithPullback adja ρ ((shiftFunctor _ n).obj K) =
      ((D.compareWithPullbackSource
          (a.obj (derivedStructureSheaf B S hS Y.1 Y.2))).commShiftIso n).hom.app K ≫
        (shiftFunctor _ n).map (D.compareWithPullback adja ρ K) ≫
          (a.commShiftIso n).inv.app K := by
  have := D.compareWithPullbackNatTrans_commShift_of_commShift_flip adja ρ
  exact NatTrans.app_shift (D.compareWithPullbackNatTrans adja ρ) n K

end Triangles

end PullbackComparisonData

end AlgebraicGeometry.Space

end
