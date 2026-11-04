module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.BaseChangeShriek
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ProPushforward
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ProPushforwardLan
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTriangles
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictionHomColimit
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ExtensionByZeroOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.BaseChangeShriekLifting

/-!
# Further results

Results complementing
`StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.BaseChangeShriek`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u u₁ u₂ u₃ u₄ w₁ w₂

namespace CategoryTheory

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒞' : Type u₂} [Category.{v} 𝒞']
  {𝒟 : Type u₃} [Category.{v} 𝒟] {𝒟' : Type u₄} [Category.{v} 𝒟']

/-! ### Base change of extension by zero along a functor -/

section Lifting

variable {jX : 𝒟 ⥤ 𝒞} (A : DeligneSystemValues jX) {jY : 𝒟' ⥤ 𝒞'} (A' : DeligneSystemValues jY)
  (F : 𝒟 ⥤ 𝒟') (G : 𝒞 ⥤ 𝒞') (β : F ⋙ jY ≅ jX ⋙ G)

variable [∀ P : 𝒟 ⥤ Type v, F.HasLeftKanExtension P]

end Lifting

/-! ### Pushforward along a left adjoint, and base change of extension by zero -/

section Adjoint

namespace ProSeq

/-- For `F ⊣ G`, left Kan extension along `F` of functors to `Type v` is precomposition with
`G`: both are left adjoint to precomposition with `F`. -/
public def _root_.CategoryTheory.Adjunction.lanIsoProPointsWhisker {F : 𝒟 ⥤ 𝒟'} {G : 𝒟' ⥤ 𝒟}
    (adj : F ⊣ G) [∀ A : 𝒟 ⥤ Type v, F.HasLeftKanExtension A] :
    F.lan (H := Type v) ≅ proPointsWhisker G :=
  Adjunction.leftAdjointUniq (F.lanAdjunction (Type v)) (adj.whiskerLeft (C := Type v))

/-- **The termwise pushforward along a left adjoint is the pushforward of
`CategoryTheory.ProSeq.pushforward`**: for `F ⊣ G`, `ProSeq.map F ≅ ProSeq.pushforward adj`, the
functors of points being related by `CategoryTheory.Adjunction.lanIsoProPointsWhisker`. -/
public def mapIsoPushforward {F : 𝒟 ⥤ 𝒟'} {G : 𝒟' ⥤ 𝒟} (adj : F ⊣ G)
    [∀ A : 𝒟 ⥤ Type v, F.HasLeftKanExtension A] : map F ≅ pushforward adj :=
  liftOpIso (fun P => isSequentialProObject_lan F P.property)
    (fun P => isSequentialProObject_comp adj P.property) adj.lanIsoProPointsWhisker

end ProSeq

end Adjoint

section BaseChange

variable {jU : 𝒟 ⥤ 𝒞} (A : DeligneSystemAssignment jU)
  {jV : 𝒟' ⥤ 𝒞'} (A' : DeligneSystemAssignment jV)
  {gstar : 𝒞 ⥤ 𝒞'} {gshriek : 𝒞' ⥤ 𝒞} (adjg : gstar ⊣ gshriek)
  {fstar : 𝒟 ⥤ 𝒟'} {fshriek : 𝒟' ⥤ 𝒟} (adjf : fstar ⊣ fshriek)
  (κ : jV ⋙ gshriek ≅ fshriek ⋙ jU)

end BaseChange

end CategoryTheory

end
