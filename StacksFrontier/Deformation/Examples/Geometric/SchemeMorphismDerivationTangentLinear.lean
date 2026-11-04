module

public import StacksFrontier.Deformation.Applications.TangentClassCoordinateMap
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismFamilyCartesianHom
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSixTermExactInterior

/-!
# Naturality of the class of a lift in the coordinate module

The arrow `Der_k(𝒪_Y, f_*𝒪_X) → T Def_{X → Y}` of [Stacks Project, Tag 0E3V] sends a derivation
to the class of the translate of the trivial lift `f'`. Its `k`-linearity compares the addition and
scalar action of the tangent module — which [Stacks Project, Tag 06IH] produces from the product
conditions, with no formula on classes — with the translation action of
[Stacks Project, Tag 0CK2]. The only handle on the former is functoriality in the coordinate
module (`Deformation.tangentModuleMapAt`); this file supplies the matching functoriality of the
class of a lift.

## Main results

* `Deformation.map_add_of_doubling`: the formal doubling argument — a class map along a translation
  action is additive as soon as it is compatible with the two projections of a doubled coordinate
  module and their sum.
* `Deformation.squareZeroCrossUnderMap_comp`, `Deformation.squareZeroCrossUnderMap_id`: the
  re-based coordinate maps are functorial.
* `Deformation.Examples.liftClass_eq_tangentModuleMapAt_of_comp`: the class of a lift is natural in
  the coordinate module, along any pair of endpoint arrows over `k[g]` carrying one lift to the
  other.
* `Deformation.Examples.liftClass_eq_tangentModuleMapAt_of_trivialMap`: the same along the chosen
  arrows of the trivial deformations.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 06IH](https://stacks.math.columbia.edu/tag/06IH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation

section Doubling

universe uG uH uL uK uT uS

/-- **Additivity of a class map along a translation action, from a doubled coordinate module.**
Let a group `G` act on a set `L` with base point `ℓ`, and let `cls : L → T` be a map to an
additive group. Suppose a second action of `H` on `L'` with base point `ℓ'` and a class map
`cls' : L' → T'` are related to the first along three maps `π₁, π₂, πs : L' → L` and three
additive maps `τ₁, τ₂, τs : H → G` (the maps induced by the two projections of a doubled
coordinate module and their sum), with `π(θ ⬝ ℓ') = τ θ ⬝ ℓ` and
`cls (πs x) = m₁ (cls' x) + m₂ (cls' x)`, `cls (πᵢ x) = mᵢ (cls' x)`. If `G` embeds into `H`
twice, by `ι₁, ι₂`, compatibly with the splitting relations, then `θ ↦ cls (θ ⬝ ℓ)` is additive. -/
theorem map_add_of_doubling {G : Type uG} {H : Type uH} {L : Type uL} {L' : Type uK}
    {T : Type uT} {T' : Type uS} [AddCommGroup G] [AddCommGroup H] [AddCommGroup T]
    (act : G → L → L) (act' : H → L' → L') (ℓ : L) (ℓ' : L') (cls : L → T) (cls' : L' → T')
    (π₁ π₂ πs : L' → L) (τ₁ τ₂ τs : H →+ G) (ι₁ ι₂ : G →+ H) (m₁ m₂ : T' → T)
    (hπ₁ : ∀ θ, π₁ (act' θ ℓ') = act (τ₁ θ) ℓ) (hπ₂ : ∀ θ, π₂ (act' θ ℓ') = act (τ₂ θ) ℓ)
    (hπs : ∀ θ, πs (act' θ ℓ') = act (τs θ) ℓ)
    (hc₁ : ∀ x, cls (π₁ x) = m₁ (cls' x)) (hc₂ : ∀ x, cls (π₂ x) = m₂ (cls' x))
    (hcs : ∀ x, cls (πs x) = m₁ (cls' x) + m₂ (cls' x))
    (h₁₁ : ∀ θ, τ₁ (ι₁ θ) = θ) (h₂₁ : ∀ θ, τ₁ (ι₂ θ) = 0)
    (h₁₂ : ∀ θ, τ₂ (ι₁ θ) = 0) (h₂₂ : ∀ θ, τ₂ (ι₂ θ) = θ)
    (h₁s : ∀ θ, τs (ι₁ θ) = θ) (h₂s : ∀ θ, τs (ι₂ θ) = θ) (θ η : G) :
    cls (act (θ + η) ℓ) = cls (act θ ℓ) + cls (act η ℓ) := by
  have es : τs (ι₁ θ + ι₂ η) = θ + η := by rw [map_add, h₁s, h₂s]
  have e₁ : τ₁ (ι₁ θ + ι₂ η) = θ := by rw [map_add, h₁₁, h₂₁, add_zero]
  have e₂ : τ₂ (ι₁ θ + ι₂ η) = η := by rw [map_add, h₁₂, h₂₂, zero_add]
  rw [← es, ← hπs, hcs, ← hc₁, ← hc₂, hπ₁, hπ₂, e₁, e₂]

end Doubling

section CrossFunctoriality

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The re-based coordinate maps compose. -/
public theorem squareZeroCrossUnderMap_comp (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    {M N O : FGModuleCat.{max v w} k} (g : M ⟶ N) (h : N ⟶ O) :
    squareZeroCrossUnderMap.{u, v, w} A (g ≫ h) =
      squareZeroCrossUnderMap.{u, v, w} A g ≫ squareZeroCrossUnderMap.{u, v, w} A h :=
  Under.UnderMorphism.ext ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map_comp g h)

/-- The re-based coordinate map of an identity is the identity. -/
public theorem squareZeroCrossUnderMap_id (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (M : FGModuleCat.{max v w} k) :
    squareZeroCrossUnderMap.{u, v, w} A (𝟙 M) = 𝟙 _ :=
  Under.UnderMorphism.ext ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map_id M)

end CrossFunctoriality

namespace Examples

universe u

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-- **The class of a lift is natural in the coordinate module.** Let `ℓ₁` be a lift of `f` to a
pair of deformations over `k[M]`, `ℓ₂` one to a pair over `k[N]`, and let `φ`, `ψ` be arrows of
the two endpoint deformation categories over one morphism `k[g]` of bases carrying `ℓ₂` to `ℓ₁`:
`ℓ₂ ≫ ψ = φ ≫ ℓ₁` on total spaces. Then the class of `ℓ₂` in `T Def_{X → Y}(N)` is the image of
the class of `ℓ₁` under the map `T Def_{X → Y}(M) → T Def_{X → Y}(N)` induced by `g`. -/
theorem liftClass_eq_tangentModuleMapAt_of_comp
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    {M N : FGModuleCat.{u} k} (g : M ⟶ N)
    {P₁ P₂ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q₁ Q₂ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    {e₁ : Q₁.base ⟶ P₁.base} [IsIso e₁] {e₂ : Q₂.base ⟶ P₂.base} [IsIso e₂]
    (hQ₁ : Q₁.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (hQ₂ : Q₂.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj N)
    (φ : P₁ ⟶ P₂) (ψ : Q₁ ⟶ Q₂) (hb : ψ.base ≫ e₂ = e₁ ≫ φ.base)
    (hψ : ψ.base = eqToHom hQ₁ ≫ (squareZeroExtensionArtinian.{u, u, u} Λ k).map g ≫
      eqToHom hQ₂.symm)
    (ℓ₁ : globalLiftsOverBase f P₁ Q₁ e₁) (ℓ₂ : globalLiftsOverBase f P₂ Q₂ e₂)
    (hcomp : ℓ₂.1 ≫ ψ.map = φ.map ≫ ℓ₁.1) :
    liftClass f pX pY hf hM N hQ₂ ℓ₂ =
      tangentModuleMapAt.{u, u, u} (BasedCategory.ofFunctor
          (schemeMorphismDeformationCategoryProjection f pX pY hf)) hM g
        (liftClass f pX pY hf hM M hQ₁ ℓ₁) := by
  let a := morphismDeformationHom f pX pY hf (P := liftDeformationObject f pX pY hf ℓ₁)
    (Q := liftDeformationObject f pX pY hf ℓ₂) ψ.base φ.map ψ.map
    (isPullback_toBase_comp_baseSpecMap_of_cartesian φ e₁ e₂ ψ.base hb.symm) ψ.cartesian
    hcomp φ.special_compat ψ.special_compat
  exact (tangentModuleMapAt_tangentClassAt.{u, u, u} _ hM g _ _ a
    (morphismDeformationHom_isHomLift f pX pY hf a hQ₁ hQ₂ _ hψ)).symm

/-- The chosen arrow of the trivial deformation of `X` along a map `g` of coordinate modules. -/
abbrev schemeMorphismSourceTrivialMap {M N : FGModuleCat.{u} k} (g : M ⟶ N) :
    schemeMorphismSourceTrivialAt f pX pY hf M ⟶ schemeMorphismSourceTrivialAt f pX pY hf N :=
  (schemeMorphismSourcePushforwards f pX pY hf).map (squareZeroCrossUnderMap.{u, u, u} _ g)

/-- The chosen arrow of the trivial deformation of `Y` along a map `g` of coordinate modules. -/
abbrev schemeMorphismTargetTrivialMap {M N : FGModuleCat.{u} k} (g : M ⟶ N) :
    schemeMorphismTargetTrivialAt f pX pY hf M ⟶ schemeMorphismTargetTrivialAt f pX pY hf N :=
  (schemeMorphismTargetPushforwards f pX pY hf).map (squareZeroCrossUnderMap.{u, u, u} _ g)

/-- The two endpoint components of an arrow of deformations of `f` have the same component on
bases: it commutes with the identity comparisons of the bases of the endpoint deformations. -/
theorem schemeMorphismForgetful_map_base_comm {m m' : schemeMorphismDeformationCategory f pX pY hf}
    (h : m ⟶ m') (e₁ : ((schemeMorphismTargetForgetful f pX pY hf).obj m).base =
      ((schemeMorphismSourceForgetful f pX pY hf).obj m).base)
    (e₂ : ((schemeMorphismTargetForgetful f pX pY hf).obj m').base =
      ((schemeMorphismSourceForgetful f pX pY hf).obj m').base) :
    ((schemeMorphismTargetForgetful f pX pY hf).map h).base ≫ eqToHom e₂ =
      eqToHom e₁ ≫ ((schemeMorphismSourceForgetful f pX pY hf).map h).base := by
  have key : ∀ (a : m.left.base ⟶ m.left.base) (c : m.left.base ⟶ m'.left.base)
      (d : m'.left.base ⟶ m'.left.base), a = 𝟙 _ → d = 𝟙 _ → c ≫ d = a ≫ c := by
    rintro _ _ _ rfl rfl
    simp
  exact key _ h.left.base _ (eqToHom_refl _ _) (eqToHom_refl _ _)

/-- The component on bases of the chosen arrow of the trivial deformation of `Y` is `k[g]`. -/
theorem schemeMorphismTargetTrivialMap_base_eq {M N : FGModuleCat.{u} k} (g : M ⟶ N) :
    (schemeMorphismTargetTrivialMap f pX pY hf g).base =
      eqToHom (schemeMorphismTargetTrivialAt_base f pX pY hf M) ≫
        (squareZeroExtensionArtinian.{u, u, u} Λ k).map g ≫
          eqToHom (schemeMorphismTargetTrivialAt_base f pX pY hf N).symm := by
  have hl : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).IsHomLift
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g)
      (schemeMorphismTargetTrivialMap f pX pY hf g) :=
    (schemeMorphismTargetPushforwards f pX pY hf).map_isHomLift
      (squareZeroCrossUnderMap.{u, u, u} _ g)
  exact IsHomLift.fac' (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
    (squareZeroExtensionArtinian.{u, u, u} Λ k |>.map g)
    (schemeMorphismTargetTrivialMap f pX pY hf g)

/-- The chosen arrow of the trivial deformation of `X` is the source component of the chosen
arrow of the trivial deformation of `f`. -/
theorem schemeMorphismSourceTrivialMap_eq {M N : FGModuleCat.{u} k} (g : M ⟶ N) :
    schemeMorphismSourceTrivialMap f pX pY hf g =
      (schemeMorphismSourceForgetful f pX pY hf).map
        ((schemeMorphismTrivialPushforwards f pX pY hf).map
          (squareZeroCrossUnderMap.{u, u, u} _ g)) :=
  ChosenPushforwardsAt.ofComp_map (schemeMorphismSourceForgetful f pX pY hf)
    (schemeDeformationCategoryProjection_cofiberedInGroupoids _)
    (schemeMorphismTrivialPushforwards f pX pY hf) (squareZeroCrossUnderMap.{u, u, u} _ g)

/-- The chosen arrow of the trivial deformation of `Y` is the target component of the chosen
arrow of the trivial deformation of `f`. -/
theorem schemeMorphismTargetTrivialMap_eq {M N : FGModuleCat.{u} k} (g : M ⟶ N) :
    schemeMorphismTargetTrivialMap f pX pY hf g =
      (schemeMorphismTargetForgetful f pX pY hf).map
        ((schemeMorphismTrivialPushforwards f pX pY hf).map
          (squareZeroCrossUnderMap.{u, u, u} _ g)) :=
  ChosenPushforwardsAt.ofComp_map (schemeMorphismTargetForgetful f pX pY hf)
    (schemeDeformationCategoryProjection_cofiberedInGroupoids _)
    (schemeMorphismTrivialPushforwards f pX pY hf) (squareZeroCrossUnderMap.{u, u, u} _ g)

/-- The components on bases of the chosen arrows of the trivial deformations of `Y` and `X`
commute with the identity comparisons of their bases. -/
theorem schemeMorphismTrivialMap_base_comm {M N : FGModuleCat.{u} k} (g : M ⟶ N) :
    (schemeMorphismTargetTrivialMap f pX pY hf g).base ≫
        eqToHom ((schemeMorphismTargetTrivialAt_base f pX pY hf N).trans
          (schemeMorphismSourceTrivialAt_base f pX pY hf N).symm) =
      eqToHom ((schemeMorphismTargetTrivialAt_base f pX pY hf M).trans
          (schemeMorphismSourceTrivialAt_base f pX pY hf M).symm) ≫
        (schemeMorphismSourceTrivialMap f pX pY hf g).base := by
  rw [schemeMorphismSourceTrivialMap_eq, schemeMorphismTargetTrivialMap_eq]
  exact schemeMorphismForgetful_map_base_comm f pX pY hf _ _ _

/-- **The class of a lift between trivial deformations is natural in the coordinate module.**
`Deformation.Examples.liftClass_eq_tangentModuleMapAt_of_comp` along the chosen arrows of the
trivial deformations of the two endpoints. -/
theorem liftClass_eq_tangentModuleMapAt_of_trivialMap
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    {M N : FGModuleCat.{u} k} (g : M ⟶ N)
    (ℓ₁ : globalLiftsOverBase f (schemeMorphismSourceTrivialAt f pX pY hf M)
      (schemeMorphismTargetTrivialAt f pX pY hf M)
      (eqToHom ((schemeMorphismTargetTrivialAt_base f pX pY hf M).trans
        (schemeMorphismSourceTrivialAt_base f pX pY hf M).symm)))
    (ℓ₂ : globalLiftsOverBase f (schemeMorphismSourceTrivialAt f pX pY hf N)
      (schemeMorphismTargetTrivialAt f pX pY hf N)
      (eqToHom ((schemeMorphismTargetTrivialAt_base f pX pY hf N).trans
        (schemeMorphismSourceTrivialAt_base f pX pY hf N).symm)))
    (hcomp : ℓ₂.1 ≫ (schemeMorphismTargetTrivialMap f pX pY hf g).map =
      (schemeMorphismSourceTrivialMap f pX pY hf g).map ≫ ℓ₁.1) :
    liftClass f pX pY hf hM N (schemeMorphismTargetTrivialAt_base f pX pY hf N) ℓ₂ =
      tangentModuleMapAt.{u, u, u} (BasedCategory.ofFunctor
          (schemeMorphismDeformationCategoryProjection f pX pY hf)) hM g
        (liftClass f pX pY hf hM M (schemeMorphismTargetTrivialAt_base f pX pY hf M) ℓ₁) :=
  liftClass_eq_tangentModuleMapAt_of_comp f pX pY hf hM g _ _
    (schemeMorphismSourceTrivialMap f pX pY hf g) (schemeMorphismTargetTrivialMap f pX pY hf g)
    (schemeMorphismTrivialMap_base_comm f pX pY hf g)
    (schemeMorphismTargetTrivialMap_base_eq f pX pY hf g) ℓ₁ ℓ₂ hcomp

end Examples

end Deformation
