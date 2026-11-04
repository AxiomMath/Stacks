module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.Transfer
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso

/-!
# The diagonal full subcategory of a 2-fibre product

Fix a base category `𝒞`, a category `p𝒳 : 𝒳 ⥤ 𝒞` fibred in groupoids, a category
`p𝒮 : 𝒮 ⥤ 𝒞` fibred in groupoids, and two 1-morphisms `F, G : 𝒳 ⥤ 𝒮` over `𝒞`. An object of
the 2-fibre product `𝒳 ×_{F, 𝒮, G} 𝒳` (`CategoryTheory.TwoFibreProductOver`) is a quadruple
`(U, x, y, φ)` with `φ : F x ≅ G y` vertical over `U`. This file proves that the full
subcategory cut out by `x = y` — whose objects are therefore the *vertical isomorphisms*
`F x ≅ G x` at a single object `x` — is again fibred in groupoids over `𝒞`.

This is the sheaf of isomorphisms between two points of a category fibred in groupoids, in the
form in which the representability statements of Stacks 06PP are made: there `𝒳` is an algebraic
space viewed as a stack, `𝒮` is an algebraic stack, and `F`, `G` are two of its
algebraic-space-valued points.

Two separate facts are involved and are proved separately.

* The fill-in clause of Stacks 003S passes to *any* full subcategory
  (`CategoryTheory.uniqueLift_restrict`): the inclusion `P.ι` is fully faithful and strictly
  over `𝒞`, so the unique fill-in produced in the ambient category is already a morphism of the
  subcategory, and faithfulness transports its uniqueness.
* The lifting clause is where the diagonal condition is used
  (`CategoryTheory.isFiberedInGroupoids_restrict_diag`). An arbitrary lift of `f : V ⟶ U` taken
  in the ambient 2-fibre product has *two* components, which need not be equal. One instead
  lifts `f` once, along `p𝒳`, to a single `θ : b ⟶ x`, and uses it for both components. The
  comparison isomorphism of the lift is then forced: `G θ` is strongly cartesian over `f`
  because `p𝒮` is fibred in groupoids, so the vertical `F b ⟶ G b` filling
  `F θ ≫ φ = χ ≫ G θ` exists and is unique, and it is invertible because it lies over an
  identity.

## Main results

* `CategoryTheory.uniqueLift_restrict`: the fill-in clause of Stacks 003S for the restriction
  of a category fibred in groupoids to a full subcategory.
* `CategoryTheory.isFiberedInGroupoids_restrict_diag`: the diagonal full subcategory of a
  2-fibre product of a category fibred in groupoids with itself is fibred in groupoids.

## References

* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
* [Stacks Project, Tag 0041](https://stacks.math.columbia.edu/tag/0041)
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable {𝒮 : Type u₃} [Category.{v₃} 𝒮]

/-- **The fill-in clause of Stacks 003S passes to a full subcategory.** Given `φ : Y ⟶ X`,
`ψ : Z ⟶ X` in the full subcategory cut out by `P` and `f : p Z ⟶ p Y` with
`f ≫ p φ = p ψ`, there is a unique `χ : Z ⟶ Y` over `f` with `χ ≫ φ = ψ`.

No condition on `P` is needed: the fill-in is produced in the ambient category, and `P.ι` is
fully faithful, so it is already a morphism of the subcategory, uniquely. -/
theorem uniqueLift_restrict (p : 𝒳 ⥤ 𝒞) (P : ObjectProperty 𝒳)
    (hp : p.IsFiberedInGroupoids)
    {X Y Z : P.FullSubcategory} (φ : Y ⟶ X) (ψ : Z ⟶ X)
    (f : (Functor.restrict p P).obj Z ⟶ (Functor.restrict p P).obj Y)
    (hcomm : f ≫ (Functor.restrict p P).map φ = (Functor.restrict p P).map ψ) :
    ∃! χ : Z ⟶ Y, (Functor.restrict p P).map χ = f ∧ χ ≫ φ = ψ := by
  obtain ⟨χ, ⟨hχ1, hχ2⟩, huniq⟩ := hp.unique_lift (P.ι.map φ) (P.ι.map ψ) f hcomm
  refine ⟨P.ι.preimage χ, ⟨?_, ?_⟩, ?_⟩
  · exact (congrArg p.map (P.ι.map_preimage χ)).trans hχ1
  · exact P.ι.map_injective (by rwa [P.ι.map_comp, P.ι.map_preimage])
  · intro ψ' ⟨h1, h2⟩
    exact P.ι.map_injective ((huniq (P.ι.map ψ') ⟨h1, by rw [← P.ι.map_comp, h2]⟩).trans
      (P.ι.map_preimage χ).symm)

/-- **The diagonal full subcategory of a 2-fibre product is fibred in groupoids.** The objects
of the full subcategory of `𝒳 ×_{F, 𝒮, G} 𝒳` cut out by `x = y` are the vertical isomorphisms
`F x ≅ G x`; its projection to `𝒞` is fibred in groupoids.

The fill-in clause is `CategoryTheory.uniqueLift_restrict` applied to the ambient 2-fibre
product, which is fibred in groupoids by Stacks 0041. For the lifting clause, lift `f` once
along `p𝒳` to `θ : b ⟶ x` and use `θ` for both components; the comparison isomorphism of the
lift is then the unique vertical fill-in of `F θ ≫ φ` through the strongly cartesian
`G θ`. -/
theorem isFiberedInGroupoids_restrict_diag
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F G : 𝒳 ⥤ 𝒮)
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒮 : p𝒮.IsFiberedInGroupoids)
    (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒳) :
    (Functor.restrict (TwoFibreProductOver.structureFunctor p𝒳 p𝒳 p𝒮 F G)
      (fun A => A.x = A.y)).IsFiberedInGroupoids where
  exists_lift := by
    intro V U f X hXU
    obtain ⟨⟨base, x, y, hx, hy, iso, vert⟩, hA⟩ := X
    simp only at hA
    subst hA
    subst hXU
    obtain ⟨b, θ, hθ⟩ := h𝒳.exists_lift f x hx
    have hbV : p𝒳.obj b = V := IsHomLift.domain_eq p𝒳 f θ
    have hFθ : p𝒮.IsHomLift f (F.map θ) := Functor.isHomLift_map_of_comp_eq hF f θ
    have hGθ : p𝒮.IsHomLift f (G.map θ) := Functor.isHomLift_map_of_comp_eq hG f θ
    have hρ : p𝒮.IsHomLift f (F.map θ ≫ iso.hom) :=
      IsHomLift.comp_lift_id_right' p𝒮 f (F.map θ) base iso.hom
    have hcart : p𝒮.IsStronglyCartesian f (G.map θ) :=
      h𝒮.isStronglyCartesian_homLift f (G.map θ)
    set χ : F.obj b ⟶ G.obj b :=
      Functor.IsStronglyCartesian.map p𝒮 f (G.map θ) (show f = 𝟙 V ≫ f by simp)
        (F.map θ ≫ iso.hom)
    have hχvert : p𝒮.IsHomLift (𝟙 V) χ :=
      Functor.IsStronglyCartesian.map_isHomLift p𝒮 f (G.map θ) _ _
    have hχfac : χ ≫ G.map θ = F.map θ ≫ iso.hom :=
      Functor.IsStronglyCartesian.fac p𝒮 f (G.map θ) _ _
    have hχcart : p𝒮.IsStronglyCartesian (𝟙 V) χ := h𝒮.isStronglyCartesian_homLift (𝟙 V) χ
    have hχiso : IsIso χ :=
      Functor.IsStronglyCartesian.isIso_of_base_isIso (p := p𝒮) (f := 𝟙 V) χ
    refine ⟨⟨⟨V, b, b, hbV, hbV, asIso χ, hχvert⟩, rfl⟩,
      ⟨{ hbase := f, a := θ, b := θ, ha := hθ, hb := hθ, w := hχfac.symm }⟩, ?_⟩
    rw [Functor.isHomLift_restrict_iff]
    exact TwoFibreProductOver.structureFunctor_isHomLift _ f hθ
  unique_lift := fun φ ψ f hcomm =>
    uniqueLift_restrict _ _
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒳 p𝒮 F G h𝒳 h𝒳 h𝒮 hF hG) φ ψ f hcomm

end CategoryTheory

end
