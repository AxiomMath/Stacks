module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Points of a base-changed group scheme

Let `b : U ⟶ V` be a morphism in a category with pullbacks and `G` a group object over `V`. For
`T` over `U`, morphisms `T ⟶ b^* G` over `U` are, as a group, morphisms `b_! T ⟶ G` over `V`
(`Over.map b ⊣ Over.pullback b`). For a field-valued point this gives an injective group
homomorphism from the `k`-points of a group scheme `𝒜` over `Spec R`, along `R → k`, to the
rational points of any group scheme over `k` isomorphic, as a group, to the base change `𝒜_k`.

## Main definitions

* `CategoryTheory.Over.mapPullbackAdjHomMulEquiv`: the group isomorphism
  `(T ⟶ b^* G) ≃* (b_! T ⟶ G)`.
* `AlgebraicGeometry.basePointsHom`: the injective homomorphism `𝒜(k) →* A(k)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

universe v u

namespace CategoryTheory.Over

attribute [local instance] Over.cartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

open scoped CategoryTheory.Obj in
/-- **Points of a pulled-back group object.** For `b : U ⟶ V`, `G` a group object over `V` and
`T` over `U`, the morphisms `T ⟶ b^* G` form, as a group, the morphisms `b_! T ⟶ G`: the
adjunction bijection of `Over.map b ⊣ Over.pullback b` is multiplicative because the right
adjoint is monoidal. -/
noncomputable def mapPullbackAdjHomMulEquiv {U V : C} (b : U ⟶ V) (G : Grp (Over V)) (T : Over U) :
    ((Over.map b).obj T ⟶ G.X) ≃* (T ⟶ ((Over.pullback b).mapGrp.obj G).X) where
  __ := (Over.mapPullbackAdj b).homEquiv T G.X
  map_mul' f g := by
    exact (congrArg (fun a => (Over.mapPullbackAdj b).unit.app T ≫ a)
      ((Over.pullback b).map_mul f g)).trans (MonObj.comp_mul _ _ _)

end CategoryTheory.Over

namespace AlgebraicGeometry

variable {R k : Type u} [CommRing R] [Field k] (φ : R →+* k) (𝒜 : Grp (Over (Spec (.of R))))
  {A : Over (Spec (.of k))} [GrpObj A]
  (e : ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).mapGrp.obj 𝒜).X ≅ A) [IsMonHom e.hom]

/-- The scheme `Spec k` over `Spec R` along `φ` is the pushforward of the unit over `Spec k`. -/
noncomputable def overMapTensorUnitIso :
    Over.mk (Spec.map (CommRingCat.ofHom φ)) ≅
      (Over.map (Spec.map (CommRingCat.ofHom φ))).obj (𝟙_ (Over (Spec (.of k)))) :=
  Over.isoMk (Iso.refl _) (by simp)

/-- **The `k`-points of `𝒜` along `φ` map injectively and homomorphically to `A(k)`**, for `A`
isomorphic as a group to the base change `𝒜_k`. -/
noncomputable def basePointsHom :
    (Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ 𝒜.X) →* (𝟙_ (Over (Spec (.of k))) ⟶ A) where
  toFun x := Over.mapPullbackAdjHomMulEquiv _ 𝒜 (𝟙_ _)
    ((overMapTensorUnitIso φ).inv ≫ x) ≫ e.hom
  map_one' := by
    simp only [MonObj.comp_one, map_one, MonObj.one_comp]
  map_mul' x y := by
    simp only [MonObj.comp_mul, map_mul, MonObj.mul_comp]

/-- `basePointsHom` is injective. -/
theorem basePointsHom_injective : Function.Injective (basePointsHom φ 𝒜 e) := by
  intro x y h
  have h1 := (cancel_mono e.hom).mp h
  have h2 := (Over.mapPullbackAdjHomMulEquiv _ 𝒜 (𝟙_ _)).injective h1
  exact (cancel_epi _).mp h2

/-- `basePointsHom` is surjective: it is a composite of bijections. -/
theorem basePointsHom_surjective : Function.Surjective (basePointsHom φ 𝒜 e) := by
  intro y
  refine ⟨(overMapTensorUnitIso φ).hom ≫
    (Over.mapPullbackAdjHomMulEquiv _ 𝒜 (𝟙_ _)).symm (y ≫ e.inv), ?_⟩
  change Over.mapPullbackAdjHomMulEquiv _ 𝒜 (𝟙_ _) ((overMapTensorUnitIso φ).inv ≫
    (overMapTensorUnitIso φ).hom ≫ _) ≫ e.hom = y
  rw [Iso.inv_hom_id_assoc, MulEquiv.apply_symm_apply, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

end AlgebraicGeometry

end
