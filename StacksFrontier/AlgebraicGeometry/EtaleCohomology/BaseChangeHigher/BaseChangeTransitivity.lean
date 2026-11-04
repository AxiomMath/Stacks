module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageCocycle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackSheafSystem

/-!
# Transitivity of base change maps along a change of the base of the sheaf

Fix a cartesian square `Y₀ = X ×_V T₀` with projections `h₀ : Y₀ ⟶ X` and `e₀ : Y₀ ⟶ T₀`, a
morphism `fV : X ⟶ V`, and an abelian sheaf `F₀` on the small étale site of `T₀`. For a scheme
`W` with `π : W ⟶ T₀` and a square `Y' = X ×_V W` lying over `Y₀`, there are two maps into
`R^r h'_* e'⁻¹ π⁻¹ F₀`: the base change map `fV⁻¹ R^r (π ≫ g₀)_* π⁻¹ F₀ ⟶ R^r h'_* e'⁻¹ π⁻¹ F₀`,
and the pullback map `R^r h₀_* e₀⁻¹ F₀ ⟶ R^r h'_* e'⁻¹ π⁻¹ F₀`, which is the base change map of
the square `h' ≫ 𝟙 = y ≫ h₀` followed by the identification `y⁻¹ e₀⁻¹ ≅ e'⁻¹ π⁻¹`.

Both maps are compatible with a morphism `φ : W₁ ⟶ W₂` over `T₀`. With the transfer map of the
target, built from the base change map of `h₁ ≫ 𝟙 = yφ ≫ h₂`, and the transfer map of the
source, built from the base change map of `g₁ ≫ 𝟙 = φ ≫ g₂`, the pullback map over `W₁` is the
pullback map over `W₂` followed by the transfer map, and the two base change maps form a
commutative square with the two transfer maps. When `φ` and `yφ` are universal homeomorphisms,
whether a class misses the image of the base change map does not change.

## Main results

* `Stacks.EtaleCohomology.smallEtalePullbackAbComp'_id_left_hom_app` — the unit law for the
  comparison of inverse images along a composite.
* `Stacks.EtaleCohomology.obstructionPullbackMap_eq_comp` — transitivity of the pullback map.
* `Stacks.EtaleCohomology.obstructionSourceTransferMap_comp_higherBaseChangeMapAb` — the square
  formed by the base change maps and the transfer maps commutes.
* `Stacks.EtaleCohomology.forall_stalk_ne_iff_of_universalHomeomorphism` — the condition that the
  pullback map sends a class outside the image of the base change map is invariant under
  universal homeomorphisms of the base.

## References

* [Stacks Project, Tag 0F07](https://stacks.math.columbia.edu/tag/0F07)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### The unit law for the comparison of inverse images -/

/-- **The unit law for the comparison of inverse images along a composite, with the first
factor an identity**: it is the identification of the inverse image along the identity with the
identity functor. -/
theorem smallEtalePullbackAbComp'_id_left_hom_app {X Y : Scheme.{u}} (v : X ⟶ X) (hv : v = 𝟙 X)
    (f : X ⟶ Y) (hf : f = v ≫ f) (G : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    (smallEtalePullbackAbComp' v f f hf).hom.app G =
      (smallEtalePullbackAbIdOf v hv).hom.app ((smallEtalePullbackAb f).obj G) := by
  have key := Adjunction.leftAdjointCompIso_comp_id (smallEtaleAdjunctionAb f)
    (smallEtaleAdjunctionAb v) (smallEtalePushforwardAbComp' v f f hf)
    (smallEtalePushforwardAbIdOf v hv) (by
      refine Iso.ext (NatTrans.ext (funext fun F ↦ ?_))
      simpa using smallEtalePushforwardAbComp'_id_left_hom_app f v hv hf F)
  rw [smallEtalePullbackAbComp'_eq_leftAdjointCompIso, key]
  simp [smallEtalePullbackAbIdOf]

/-- The inverse half of `smallEtalePullbackAbComp'_id_left_hom_app`. -/
theorem smallEtalePullbackAbComp'_id_left_inv_app {X Y : Scheme.{u}} (v : X ⟶ X) (hv : v = 𝟙 X)
    (f : X ⟶ Y) (hf : f = v ≫ f) (G : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    (smallEtalePullbackAbComp' v f f hf).inv.app G =
      (smallEtalePullbackAbIdOf v hv).inv.app ((smallEtalePullbackAb f).obj G) :=
  congrArg Iso.inv
    (Iso.ext (smallEtalePullbackAbComp'_id_left_hom_app v hv f hf G) :
      Iso.app (smallEtalePullbackAbComp' v f f hf) G =
        Iso.app (smallEtalePullbackAbIdOf v hv) ((smallEtalePullbackAb f).obj G))

/-! ### Two rearrangements, on variables -/

section Algebra

variable {E : Type*} [Category* E]

/-- `BC ≫ M = Q ≫ ι' ≫ B ≫ D` for composable morphisms related by four commuting squares. -/
private theorem transfer_algebra_target {o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ o₉ : E} {BC : o₁ ⟶ o₅}
    {I : o₁ ⟶ o₂} {J : o₂ ⟶ o₃} {K : o₃ ⟶ o₄} {L : o₄ ⟶ o₅} {M : o₅ ⟶ o₉} {Q : o₁ ⟶ o₆}
    {ι' : o₆ ⟶ o₇} {B : o₇ ⟶ o₈} {D : o₈ ⟶ o₉} {J₂ : o₃ ⟶ o₇} {N : o₄ ⟶ o₈}
    (hp : BC = I ≫ J ≫ K ≫ L) (n₁ : Q ≫ ι' = I ≫ J ≫ J₂) (n₂ : J₂ ≫ B = K ≫ N)
    (hc : L ≫ M = N ≫ D) : BC ≫ M = Q ≫ ι' ≫ B ≫ D := by
  rw [hp]
  simp only [Category.assoc]
  rw [hc, ← reassoc_of% n₂, ← reassoc_of% n₁]

/-- `(A ≫ BC) ≫ D = β ≫ ι' ≫ K ≫ Dd` for composable morphisms related by the given identities. -/
private theorem transfer_algebra_source {o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ o₉ o₁₀ o₁₁ : E}
    {A : o₁ ⟶ o₂} {BC : o₂ ⟶ o₄} {B : o₂ ⟶ o₃} {C : o₃ ⟶ o₄} {D : o₄ ⟶ o₅} {C' : o₃ ⟶ o₆}
    {D' : o₆ ⟶ o₅} {R : o₁ ⟶ o₇} {H : o₆ ⟶ o₇} {Hi : o₇ ⟶ o₆} {I : o₁ ⟶ o₈} {J : o₈ ⟶ o₉}
    {K : o₉ ⟶ o₁₀} {L : o₁₀ ⟶ o₇} {β : o₁ ⟶ o₁₁} {ι' : o₁₁ ⟶ o₉} {Dd : o₁₀ ⟶ o₅}
    (hB : BC = B ≫ C) (n₃ : C ≫ D = C' ≫ D') (h₁ : R = A ≫ B ≫ C' ≫ H) (hH : H ≫ Hi = 𝟙 _)
    (h₂ : R = I ≫ J ≫ K ≫ L) (n₄ : β ≫ ι' = I ≫ J) (hd : Dd = L ≫ Hi ≫ D') :
    (A ≫ BC) ≫ D = β ≫ ι' ≫ K ≫ Dd := by
  rw [hB, hd]
  simp only [Category.assoc]
  rw [n₃]
  calc A ≫ B ≫ C' ≫ D' = A ≫ B ≫ C' ≫ H ≫ Hi ≫ D' := by rw [reassoc_of% hH]
    _ = R ≫ Hi ≫ D' := by rw [h₁]; simp only [Category.assoc]
    _ = β ≫ ι' ≫ K ≫ L ≫ Hi ≫ D' := by
      rw [h₂]
      simp only [Category.assoc]
      rw [← reassoc_of% n₄]

/-- `P₁ ≫ P₂ ≫ P₃ = FX₁₂ ≫ Q₁ ≫ Q₂ ≫ Q₃` for composable morphisms related by the given identities
and inverse pairs. -/
private theorem transfer_algebra_coherence {o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ : E} {P₁ : o₁ ⟶ o₂}
    {P₂ : o₂ ⟶ o₃} {P₃ : o₃ ⟶ o₄} {Z : o₄ ⟶ o₃} {FX₁ : o₁ ⟶ o₅} {FX₂ : o₅ ⟶ o₆}
    {FX₂' : o₆ ⟶ o₅} {FX₁₂ : o₁ ⟶ o₆} {T : o₅ ⟶ o₃} {Q₁ : o₆ ⟶ o₇} {Q₂ : o₇ ⟶ o₈}
    {Q₂' : o₈ ⟶ o₇} {Q₃ : o₈ ⟶ o₄} {U : o₇ ⟶ o₃} (hF : FX₁₂ = FX₁ ≫ FX₂)
    (A1 : P₁ ≫ P₂ = FX₁ ≫ T) (A2 : Q₂' ≫ U = Q₃ ≫ Z) (A3 : Q₁ ≫ U = FX₂' ≫ T)
    (hZ : P₃ ≫ Z = 𝟙 _) (hZ' : Z ≫ P₃ = 𝟙 _) (hQ : Q₂ ≫ Q₂' = 𝟙 _) (hX : FX₂ ≫ FX₂' = 𝟙 _) :
    P₁ ≫ P₂ ≫ P₃ = FX₁₂ ≫ Q₁ ≫ Q₂ ≫ Q₃ := by
  have key : (P₁ ≫ P₂ ≫ P₃) ≫ Z = (FX₁₂ ≫ Q₁ ≫ Q₂ ≫ Q₃) ≫ Z := by
    simp only [Category.assoc]
    rw [hZ, Category.comp_id, ← A2, reassoc_of% hQ, A3, hF, Category.assoc, reassoc_of% hX, A1]
  have := congrArg (· ≫ P₃) key
  simpa only [Category.assoc, hZ', Category.comp_id] using this

end Algebra

/-! ### The pullback map and the transfer maps -/

section Transfer

variable {V X T₀ Y₀ : Scheme.{u}} (fV : X ⟶ V) (g₀ : T₀ ⟶ V) (h₀ : Y₀ ⟶ X) (e₀ : Y₀ ⟶ T₀)
  (F₀ : Sheaf (smallEtaleTopology T₀) Ab.{u + 1}) (r : ℕ)

variable {fV g₀ h₀ e₀ F₀ r}

/-- The coherence of the identifications of iterated inverse images along `y₁ = yφ ≫ y₂` and
`π₁ = φ ≫ π₂`. -/
theorem obstructionPullbackMap_coherence {W₁ W₂ Y₁ Y₂ : Scheme.{u}} (e₁ : Y₁ ⟶ W₁)
    (π₁ : W₁ ⟶ T₀) (e₂ : Y₂ ⟶ W₂) (π₂ : W₂ ⟶ T₀) (φ : W₁ ⟶ W₂) (hπ : π₁ = φ ≫ π₂)
    (yφ : Y₁ ⟶ Y₂) (hφe : yφ ≫ e₂ = e₁ ≫ φ) (y₁ : Y₁ ⟶ Y₀) (y₂ : Y₂ ⟶ Y₀)
    (hy₁ : y₁ ≫ e₀ = e₁ ≫ π₁) (hy₂ : y₂ ≫ e₀ = e₂ ≫ π₂) (hy : y₁ = yφ ≫ y₂) :
    (smallEtalePullbackAbComp' yφ y₂ y₁ hy).hom.app ((smallEtalePullbackAb e₀).obj F₀) ≫
        (smallEtalePullbackAbComp' y₁ e₀ (y₁ ≫ e₀) rfl).hom.app F₀ ≫
          (smallEtalePullbackAbComp' e₁ π₁ (y₁ ≫ e₀) hy₁).inv.app F₀ =
      (smallEtalePullbackAb yφ).map
          ((smallEtalePullbackAbComp' y₂ e₀ (y₂ ≫ e₀) rfl).hom.app F₀ ≫
            (smallEtalePullbackAbComp' e₂ π₂ (y₂ ≫ e₀) hy₂).inv.app F₀) ≫
        (smallEtalePullbackAbComp' yφ e₂ (e₁ ≫ φ) hφe.symm).hom.app
            ((smallEtalePullbackAb π₂).obj F₀) ≫
          (smallEtalePullbackAbComp' e₁ φ (e₁ ≫ φ) rfl).inv.app
            ((smallEtalePullbackAb π₂).obj F₀) ≫
            (smallEtalePullbackAb e₁).map ((smallEtalePullbackAbComp' φ π₂ π₁ hπ).hom.app F₀) := by
  have hc₁ : y₁ ≫ e₀ = yφ ≫ y₂ ≫ e₀ := by rw [hy, Category.assoc]
  have hc₂ : y₁ ≫ e₀ = (e₁ ≫ φ) ≫ π₂ := by rw [hy₁, hπ, Category.assoc]
  refine transfer_algebra_coherence (Functor.map_comp _ _ _)
    (smallEtalePullbackAbComp'_assoc_app yφ y₂ e₀ y₁ hy (y₂ ≫ e₀) rfl (y₁ ≫ e₀) rfl hc₁ F₀)
    (smallEtalePullbackAbComp'_assoc_app e₁ φ π₂ (e₁ ≫ φ) rfl π₁ hπ (y₁ ≫ e₀) hc₂ hy₁ F₀)
    (smallEtalePullbackAbComp'_assoc_app yφ e₂ π₂ (e₁ ≫ φ) hφe.symm (y₂ ≫ e₀) hy₂
      (y₁ ≫ e₀) hc₂ hc₁ F₀)
    (Iso.inv_hom_id_app _ _) (Iso.hom_inv_id_app _ _) (Iso.inv_hom_id_app _ _) ?_
  rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]

/-- The pasting law of a square over `fV` with a square over `𝟙 X`, with the inverse image along
the identity removed. -/
private theorem higherBaseChangeMapAb_paste_id_left_app {Y₁ Y₂ W : Scheme.{u}} {g : W ⟶ V}
    (h₁ : Y₁ ⟶ X) (h₂ : Y₂ ⟶ X) (e : Y₂ ⟶ W) (yφ : Y₁ ⟶ Y₂) (k : Y₁ ⟶ W) (hk : k = yφ ≫ e)
    (hφh : h₁ ≫ 𝟙 X = yφ ≫ h₂) (w₁ : h₁ ≫ fV = k ≫ g) (w₂ : h₂ ≫ fV = e ≫ g)
    (G : Sheaf (smallEtaleTopology W) Ab.{u + 1}) :
    (higherBaseChangeMapAb fV g h₁ k w₁ r).app G =
      (smallEtalePullbackAbIdOf (𝟙 X) rfl).inv.app ((smallEtalePullbackAb fV).obj
          (((smallEtalePushforwardAb g).rightDerived r).obj G)) ≫
        (smallEtalePullbackAb (𝟙 X)).map ((higherBaseChangeMapAb fV g h₂ e w₂ r).app G) ≫
        (higherBaseChangeMapAb (𝟙 X) h₂ h₁ yφ hφh r).app ((smallEtalePullbackAb e).obj G) ≫
        ((smallEtalePushforwardAb h₁).rightDerived r).map
          ((smallEtalePullbackAbComp' yφ e k hk).hom.app G) := by
  rw [higherBaseChangeMapAb_paste_app_named g h₂ h₁ fV (𝟙 X) e yφ fV
    (Category.id_comp _).symm k hk _ w₂ hφh r G,
    smallEtalePullbackAbComp'_id_left_inv_app (𝟙 X) rfl]

section Steps

variable {W₁ W₂ Y₁ Y₂ : Scheme.{u}} (h₁ : Y₁ ⟶ X) (e₁ : Y₁ ⟶ W₁) (π₁ : W₁ ⟶ T₀) (g₁ : W₁ ⟶ V)
  (h₂ : Y₂ ⟶ X) (e₂ : Y₂ ⟶ W₂) (π₂ : W₂ ⟶ T₀) (g₂ : W₂ ⟶ V) (φ : W₁ ⟶ W₂)
  (hπ : π₁ = φ ≫ π₂) (yφ : Y₁ ⟶ Y₂) (hφh : h₁ ≫ 𝟙 X = yφ ≫ h₂) (hφe : yφ ≫ e₂ = e₁ ≫ φ)
  (y₁ : Y₁ ⟶ Y₀) (y₂ : Y₂ ⟶ Y₀) (hy₁ : y₁ ≫ e₀ = e₁ ≫ π₁) (hy₂ : y₂ ≫ e₀ = e₂ ≫ π₂)
  (hyh₁ : h₁ ≫ 𝟙 X = y₁ ≫ h₀) (hyh₂ : h₂ ≫ 𝟙 X = y₂ ≫ h₀) (hy : y₁ = yφ ≫ y₂)

/-- The naturality of the identification of the inverse image along the identity. -/
private theorem pullbackMap_unit_naturality :
    ((higherBaseChangeMapAb (𝟙 X) h₀ h₂ y₂ hyh₂ r).app ((smallEtalePullbackAb e₀).obj F₀) ≫
      ((smallEtalePushforwardAb h₂).rightDerived r).map
        ((smallEtalePullbackAbComp' y₂ e₀ (y₂ ≫ e₀) rfl).hom.app F₀ ≫
          (smallEtalePullbackAbComp' e₂ π₂ (y₂ ≫ e₀) hy₂).inv.app F₀)) ≫
        (smallEtalePullbackAbIdOf (𝟙 X) rfl).inv.app
          (((smallEtalePushforwardAb h₂).rightDerived r).obj
            ((smallEtalePullbackAb e₂).obj ((smallEtalePullbackAb π₂).obj F₀))) =
      (smallEtalePullbackAbIdOf (𝟙 X) rfl).inv.app ((smallEtalePullbackAb (𝟙 X)).obj
          (((smallEtalePushforwardAb h₀).rightDerived r).obj ((smallEtalePullbackAb e₀).obj F₀))) ≫
        (smallEtalePullbackAb (𝟙 X)).map
          ((higherBaseChangeMapAb (𝟙 X) h₀ h₂ y₂ hyh₂ r).app ((smallEtalePullbackAb e₀).obj F₀)) ≫
        (smallEtalePullbackAb (𝟙 X)).map (((smallEtalePushforwardAb h₂).rightDerived r).map
          ((smallEtalePullbackAbComp' y₂ e₀ (y₂ ≫ e₀) rfl).hom.app F₀ ≫
            (smallEtalePullbackAbComp' e₂ π₂ (y₂ ≫ e₀) hy₂).inv.app F₀)) := by
  rw [← Functor.map_comp]
  exact (smallEtalePullbackAbIdOf (𝟙 X) rfl).inv.naturality _

/-- The naturality of the base change map of `h₁ ≫ 𝟙 = yφ ≫ h₂`. -/
private theorem transferMap_naturality :
    (smallEtalePullbackAb (𝟙 X)).map (((smallEtalePushforwardAb h₂).rightDerived r).map
          ((smallEtalePullbackAbComp' y₂ e₀ (y₂ ≫ e₀) rfl).hom.app F₀ ≫
            (smallEtalePullbackAbComp' e₂ π₂ (y₂ ≫ e₀) hy₂).inv.app F₀)) ≫
        (higherBaseChangeMapAb (𝟙 X) h₂ h₁ yφ hφh r).app
          ((smallEtalePullbackAb e₂).obj ((smallEtalePullbackAb π₂).obj F₀)) =
      (higherBaseChangeMapAb (𝟙 X) h₂ h₁ yφ hφh r).app
          ((smallEtalePullbackAb y₂).obj ((smallEtalePullbackAb e₀).obj F₀)) ≫
        ((smallEtalePushforwardAb h₁).rightDerived r).map ((smallEtalePullbackAb yφ).map
          ((smallEtalePullbackAbComp' y₂ e₀ (y₂ ≫ e₀) rfl).hom.app F₀ ≫
            (smallEtalePullbackAbComp' e₂ π₂ (y₂ ≫ e₀) hy₂).inv.app F₀)) :=
  (higherBaseChangeMapAb (𝟙 X) h₂ h₁ yφ hφh r).naturality _

include hy in
/-- The coherence of the identifications, under `R^r h₁_*`. -/
private theorem transferMap_coherence :
    ((smallEtalePushforwardAb h₁).rightDerived r).map
        ((smallEtalePullbackAbComp' yφ y₂ y₁ hy).hom.app ((smallEtalePullbackAb e₀).obj F₀)) ≫
      ((smallEtalePushforwardAb h₁).rightDerived r).map
        ((smallEtalePullbackAbComp' y₁ e₀ (y₁ ≫ e₀) rfl).hom.app F₀ ≫
          (smallEtalePullbackAbComp' e₁ π₁ (y₁ ≫ e₀) hy₁).inv.app F₀) =
      ((smallEtalePushforwardAb h₁).rightDerived r).map ((smallEtalePullbackAb yφ).map
          ((smallEtalePullbackAbComp' y₂ e₀ (y₂ ≫ e₀) rfl).hom.app F₀ ≫
            (smallEtalePullbackAbComp' e₂ π₂ (y₂ ≫ e₀) hy₂).inv.app F₀)) ≫
      ((smallEtalePushforwardAb h₁).rightDerived r).map
        ((smallEtalePullbackAbComp' yφ e₂ (e₁ ≫ φ) hφe.symm).hom.app
            ((smallEtalePullbackAb π₂).obj F₀) ≫
          (smallEtalePullbackAbComp' e₁ φ (e₁ ≫ φ) rfl).inv.app
            ((smallEtalePullbackAb π₂).obj F₀) ≫
          (smallEtalePullbackAb e₁).map ((smallEtalePullbackAbComp' φ π₂ π₁ hπ).hom.app F₀)) := by
  rw [← Functor.map_comp, ← Functor.map_comp,
    obstructionPullbackMap_coherence e₁ π₁ e₂ π₂ φ hπ yφ hφe y₁ y₂ hy₁ hy₂ hy]

include hy in
/-- **Transitivity of the pullback map.** For a morphism `φ : W₁ ⟶ W₂` over `T₀` and a morphism
`yφ : Y₁ ⟶ Y₂` over it compatible with the maps to `Y₀`, the pullback map over `W₁` is the
pullback map over `W₂` followed by the transfer map: the base change map of `h₁ ≫ 𝟙 = yφ ≫ h₂`,
read through the identifications of the iterated inverse images. -/
theorem obstructionPullbackMap_eq_comp :
    (higherBaseChangeMapAb (𝟙 X) h₀ h₁ y₁ hyh₁ r).app ((smallEtalePullbackAb e₀).obj F₀) ≫
      ((smallEtalePushforwardAb h₁).rightDerived r).map
        ((smallEtalePullbackAbComp' y₁ e₀ (y₁ ≫ e₀) rfl).hom.app F₀ ≫
          (smallEtalePullbackAbComp' e₁ π₁ (y₁ ≫ e₀) hy₁).inv.app F₀) =
    ((higherBaseChangeMapAb (𝟙 X) h₀ h₂ y₂ hyh₂ r).app ((smallEtalePullbackAb e₀).obj F₀) ≫
      ((smallEtalePushforwardAb h₂).rightDerived r).map
        ((smallEtalePullbackAbComp' y₂ e₀ (y₂ ≫ e₀) rfl).hom.app F₀ ≫
          (smallEtalePullbackAbComp' e₂ π₂ (y₂ ≫ e₀) hy₂).inv.app F₀)) ≫
      (smallEtalePullbackAbIdOf (𝟙 X) rfl).inv.app
        (((smallEtalePushforwardAb h₂).rightDerived r).obj
          ((smallEtalePullbackAb e₂).obj ((smallEtalePullbackAb π₂).obj F₀))) ≫
      (higherBaseChangeMapAb (𝟙 X) h₂ h₁ yφ hφh r).app
        ((smallEtalePullbackAb e₂).obj ((smallEtalePullbackAb π₂).obj F₀)) ≫
      ((smallEtalePushforwardAb h₁).rightDerived r).map
        ((smallEtalePullbackAbComp' yφ e₂ (e₁ ≫ φ) hφe.symm).hom.app
            ((smallEtalePullbackAb π₂).obj F₀) ≫
          (smallEtalePullbackAbComp' e₁ φ (e₁ ≫ φ) rfl).inv.app
            ((smallEtalePullbackAb π₂).obj F₀) ≫
          (smallEtalePullbackAb e₁).map ((smallEtalePullbackAbComp' φ π₂ π₁ hπ).hom.app F₀)) :=
  transfer_algebra_target
    (higherBaseChangeMapAb_paste_id_left_app h₁ h₂ y₂ yφ y₁ hy hφh hyh₁ hyh₂ _)
    (pullbackMap_unit_naturality h₂ e₂ π₂ y₂ hy₂ hyh₂)
    (transferMap_naturality h₁ h₂ e₂ π₂ yφ hφh y₂ hy₂)
    (transferMap_coherence h₁ e₁ π₁ e₂ π₂ φ hπ yφ hφe y₁ y₂ hy₁ hy₂ hy)

variable (w₁ : h₁ ≫ fV = e₁ ≫ g₁) (w₂ : h₂ ≫ fV = e₂ ≫ g₂) (wφ : g₁ ≫ 𝟙 V = φ ≫ g₂)

include w₁ wφ in
/-- The pasting law through the square over `𝟙 V`. -/
private theorem sourceTransfer_paste₁ :
    (higherBaseChangeMapAb fV g₂ h₁ (e₁ ≫ φ)
        (by rw [w₁, Category.assoc, ← wφ, Category.comp_id]) r).app
        ((smallEtalePullbackAb π₂).obj F₀) =
      (smallEtalePullbackAbComp' fV (𝟙 V) fV (Category.comp_id fV).symm).inv.app
          (((smallEtalePushforwardAb g₂).rightDerived r).obj ((smallEtalePullbackAb π₂).obj F₀)) ≫
        (smallEtalePullbackAb fV).map
          ((higherBaseChangeMapAb (𝟙 V) g₂ g₁ φ wφ r).app ((smallEtalePullbackAb π₂).obj F₀)) ≫
        (higherBaseChangeMapAb fV g₁ h₁ e₁ w₁ r).app
          ((smallEtalePullbackAb φ).obj ((smallEtalePullbackAb π₂).obj F₀)) ≫
        ((smallEtalePushforwardAb h₁).rightDerived r).map
          ((smallEtalePullbackAbComp' e₁ φ (e₁ ≫ φ) rfl).hom.app
            ((smallEtalePullbackAb π₂).obj F₀)) :=
  higherBaseChangeMapAb_paste_app_named g₂ g₁ h₁ (𝟙 V) fV φ e₁ fV
    (Category.comp_id _).symm (e₁ ≫ φ) rfl _ wφ w₁ r _

/-- The naturality of the base change map over `W₁` along `φ⁻¹ π₂⁻¹ ≅ π₁⁻¹`. -/
private theorem sourceTransfer_naturality :
    (smallEtalePullbackAb fV).map (((smallEtalePushforwardAb g₁).rightDerived r).map
          ((smallEtalePullbackAbComp' φ π₂ π₁ hπ).hom.app F₀)) ≫
        (higherBaseChangeMapAb fV g₁ h₁ e₁ w₁ r).app ((smallEtalePullbackAb π₁).obj F₀) =
      (higherBaseChangeMapAb fV g₁ h₁ e₁ w₁ r).app
          ((smallEtalePullbackAb φ).obj ((smallEtalePullbackAb π₂).obj F₀)) ≫
        ((smallEtalePushforwardAb h₁).rightDerived r).map ((smallEtalePullbackAb e₁).map
          ((smallEtalePullbackAbComp' φ π₂ π₁ hπ).hom.app F₀)) :=
  (higherBaseChangeMapAb fV g₁ h₁ e₁ w₁ r).naturality _

/-- The naturality of the identification of the inverse image along the identity, at the base
change map over `W₂`. -/
private theorem sourceTransfer_unit_naturality :
    (higherBaseChangeMapAb fV g₂ h₂ e₂ w₂ r).app ((smallEtalePullbackAb π₂).obj F₀) ≫
        (smallEtalePullbackAbIdOf (𝟙 X) rfl).inv.app
          (((smallEtalePushforwardAb h₂).rightDerived r).obj
            ((smallEtalePullbackAb e₂).obj ((smallEtalePullbackAb π₂).obj F₀))) =
      (smallEtalePullbackAbIdOf (𝟙 X) rfl).inv.app ((smallEtalePullbackAb fV).obj
          (((smallEtalePushforwardAb g₂).rightDerived r).obj ((smallEtalePullbackAb π₂).obj F₀))) ≫
        (smallEtalePullbackAb (𝟙 X)).map
          ((higherBaseChangeMapAb fV g₂ h₂ e₂ w₂ r).app ((smallEtalePullbackAb π₂).obj F₀)) :=
  (smallEtalePullbackAbIdOf (𝟙 X) rfl).inv.naturality _

/-- The two comparisons of `(e₁ ≫ φ)⁻¹` cancel. -/
private theorem sourceTransfer_cancel :
    ((smallEtalePushforwardAb h₁).rightDerived r).map
        ((smallEtalePullbackAbComp' e₁ φ (e₁ ≫ φ) rfl).hom.app ((smallEtalePullbackAb π₂).obj F₀)) ≫
      ((smallEtalePushforwardAb h₁).rightDerived r).map
        ((smallEtalePullbackAbComp' e₁ φ (e₁ ≫ φ) rfl).inv.app ((smallEtalePullbackAb π₂).obj F₀)) =
      𝟙 _ := by
  rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]

/-- The tail of the transfer map of the target, split. -/
private theorem sourceTransfer_tail :
    ((smallEtalePushforwardAb h₁).rightDerived r).map
        ((smallEtalePullbackAbComp' yφ e₂ (e₁ ≫ φ) hφe.symm).hom.app
            ((smallEtalePullbackAb π₂).obj F₀) ≫
          (smallEtalePullbackAbComp' e₁ φ (e₁ ≫ φ) rfl).inv.app
            ((smallEtalePullbackAb π₂).obj F₀) ≫
          (smallEtalePullbackAb e₁).map ((smallEtalePullbackAbComp' φ π₂ π₁ hπ).hom.app F₀)) =
      ((smallEtalePushforwardAb h₁).rightDerived r).map
          ((smallEtalePullbackAbComp' yφ e₂ (e₁ ≫ φ) hφe.symm).hom.app
            ((smallEtalePullbackAb π₂).obj F₀)) ≫
        ((smallEtalePushforwardAb h₁).rightDerived r).map
          ((smallEtalePullbackAbComp' e₁ φ (e₁ ≫ φ) rfl).inv.app
            ((smallEtalePullbackAb π₂).obj F₀)) ≫
        ((smallEtalePushforwardAb h₁).rightDerived r).map ((smallEtalePullbackAb e₁).map
          ((smallEtalePullbackAbComp' φ π₂ π₁ hπ).hom.app F₀)) :=
  (((smallEtalePushforwardAb h₁).rightDerived r).map_comp _ _).trans
    (congrArg (_ ≫ ·) (((smallEtalePushforwardAb h₁).rightDerived r).map_comp _ _))

/-- The inverse image along `fV` of the head of the transfer map of the source, split. -/
private theorem sourceTransfer_head :
    (smallEtalePullbackAb fV).map
        ((higherBaseChangeMapAb (𝟙 V) g₂ g₁ φ wφ r).app ((smallEtalePullbackAb π₂).obj F₀) ≫
          ((smallEtalePushforwardAb g₁).rightDerived r).map
            ((smallEtalePullbackAbComp' φ π₂ π₁ hπ).hom.app F₀)) =
      (smallEtalePullbackAb fV).map
          ((higherBaseChangeMapAb (𝟙 V) g₂ g₁ φ wφ r).app ((smallEtalePullbackAb π₂).obj F₀)) ≫
        (smallEtalePullbackAb fV).map (((smallEtalePushforwardAb g₁).rightDerived r).map
          ((smallEtalePullbackAbComp' φ π₂ π₁ hπ).hom.app F₀)) :=
  (smallEtalePullbackAb fV).map_comp _ _

include w₁ wφ in
/-- **The square of base change maps and transfer maps commutes.** For a morphism
`φ : W₁ ⟶ W₂` over `T₀` and data over `W₁` and `W₂` compatible along `yφ`, the transfer map of
the source followed by the base change map over `W₁` is the base change map over `W₂` followed
by the transfer map of the target. -/
theorem obstructionSourceTransferMap_comp_higherBaseChangeMapAb :
    ((smallEtalePullbackAbComp' fV (𝟙 V) fV (Category.comp_id fV).symm).inv.app
          (((smallEtalePushforwardAb g₂).rightDerived r).obj ((smallEtalePullbackAb π₂).obj F₀)) ≫
        (smallEtalePullbackAb fV).map
          ((higherBaseChangeMapAb (𝟙 V) g₂ g₁ φ wφ r).app ((smallEtalePullbackAb π₂).obj F₀) ≫
            ((smallEtalePushforwardAb g₁).rightDerived r).map
              ((smallEtalePullbackAbComp' φ π₂ π₁ hπ).hom.app F₀))) ≫
        (higherBaseChangeMapAb fV g₁ h₁ e₁ w₁ r).app ((smallEtalePullbackAb π₁).obj F₀) =
      (higherBaseChangeMapAb fV g₂ h₂ e₂ w₂ r).app ((smallEtalePullbackAb π₂).obj F₀) ≫
        (smallEtalePullbackAbIdOf (𝟙 X) rfl).inv.app
          (((smallEtalePushforwardAb h₂).rightDerived r).obj
            ((smallEtalePullbackAb e₂).obj ((smallEtalePullbackAb π₂).obj F₀))) ≫
        (higherBaseChangeMapAb (𝟙 X) h₂ h₁ yφ hφh r).app
          ((smallEtalePullbackAb e₂).obj ((smallEtalePullbackAb π₂).obj F₀)) ≫
        ((smallEtalePushforwardAb h₁).rightDerived r).map
          ((smallEtalePullbackAbComp' yφ e₂ (e₁ ≫ φ) hφe.symm).hom.app
              ((smallEtalePullbackAb π₂).obj F₀) ≫
            (smallEtalePullbackAbComp' e₁ φ (e₁ ≫ φ) rfl).inv.app
              ((smallEtalePullbackAb π₂).obj F₀) ≫
            (smallEtalePullbackAb e₁).map ((smallEtalePullbackAbComp' φ π₂ π₁ hπ).hom.app F₀)) :=
  transfer_algebra_source (sourceTransfer_head (wφ := wφ) ..)
    (sourceTransfer_naturality (w₁ := w₁) ..)
    (sourceTransfer_paste₁ (w₁ := w₁) (wφ := wφ) ..)
    (sourceTransfer_cancel ..)
    (higherBaseChangeMapAb_paste_id_left_app h₁ h₂ e₂ yφ (e₁ ≫ φ) hφe.symm hφh _ w₂ _)
    (sourceTransfer_unit_naturality (w₂ := w₂) ..)
    (sourceTransfer_tail (hφe := hφe) ..)

end Steps

/-! ### Invariance of the obstruction condition -/

/-- In abelian groups, the condition that `c₁ ξ` misses the image of `a₁` is transported along a
commutative square from `a₂` to `a₁` with injective target map and surjective source map, which
also relates `c₂` to `c₁`. -/
theorem forall_ne_iff_of_comp_eq {C A₁ A₂ B₁ B₂ : Ab.{u + 1}} (a₁ : A₁ ⟶ B₁) (a₂ : A₂ ⟶ B₂)
    (c₁ : C ⟶ B₁) (c₂ : C ⟶ B₂) (Θ : B₂ ⟶ B₁) (Ψ : A₂ ⟶ A₁) (hΘ : Function.Injective Θ)
    (hΨ : Function.Surjective Ψ) (h₁ : a₂ ≫ Θ = Ψ ≫ a₁) (h₂ : c₂ ≫ Θ = c₁) (ξ : C) :
    (∀ η, a₁ η ≠ c₁ ξ) ↔ (∀ η, a₂ η ≠ c₂ ξ) := by
  have e₁ : ∀ η, Θ (a₂ η) = a₁ (Ψ η) := fun η ↦ by
    rw [← ConcreteCategory.comp_apply, h₁, ConcreteCategory.comp_apply]
  have e₂ : Θ (c₂ ξ) = c₁ ξ := by rw [← ConcreteCategory.comp_apply, h₂]
  constructor
  · intro H η hη
    exact H (Ψ η) (by rw [← e₁, hη, e₂])
  · intro H η hη
    obtain ⟨η', rfl⟩ := hΨ η
    exact H η' (hΘ (by rw [e₁, e₂, hη]))

/-- `forall_ne_iff_of_comp_eq` after a functor to abelian groups, for invertible transfer
maps. -/
theorem forall_map_ne_iff_of_isIso {C : Type*} [Category* C] (S : C ⥤ Ab.{u + 1})
    {P A₁ A₂ B₁ B₂ : C} (a₁ : A₁ ⟶ B₁) (a₂ : A₂ ⟶ B₂) (c₁ : P ⟶ B₁) (c₂ : P ⟶ B₂) (Θ : B₂ ⟶ B₁)
    (Ψ : A₂ ⟶ A₁) [IsIso Θ] [IsIso Ψ] (h₁ : a₂ ≫ Θ = Ψ ≫ a₁) (h₂ : c₂ ≫ Θ = c₁)
    (ξ : S.obj P) : (∀ η, S.map a₁ η ≠ S.map c₁ ξ) ↔ (∀ η, S.map a₂ η ≠ S.map c₂ ξ) :=
  forall_ne_iff_of_comp_eq _ _ _ _ (S.map Θ) (S.map Ψ)
    (ConcreteCategory.bijective_of_isIso (S.map Θ)).1
    (ConcreteCategory.bijective_of_isIso (S.map Ψ)).2
    (by rw [← S.map_comp, h₁, S.map_comp]) (by rw [← S.map_comp, h₂]) ξ

variable {V X T₀ Y₀ W₁ W₂ Y₁ Y₂ : Scheme.{u}} {fV : X ⟶ V} {g₀ : T₀ ⟶ V} {h₀ : Y₀ ⟶ X}
  {e₀ : Y₀ ⟶ T₀} {F₀ : Sheaf (smallEtaleTopology T₀) Ab.{u + 1}} {r : ℕ}

/-- **The obstruction condition is invariant under a universal homeomorphism of the base of the
sheaf.** Let `φ : W₁ ⟶ W₂` be a universal homeomorphism over `T₀` and `yφ : Y₁ ⟶ Y₂` a
universal homeomorphism over it, compatible with the maps of the two squares to `X` and to `Y₀`.
Then a class `ξ` in the stalk at `x` of `R^r h₀_* e₀⁻¹ F₀` has image outside the image of the
base change map over `W₁` exactly when it does over `W₂`. -/
theorem forall_stalk_ne_iff_of_universalHomeomorphism (h₁ : Y₁ ⟶ X) (e₁ : Y₁ ⟶ W₁)
    (π₁ : W₁ ⟶ T₀) (g₁ : W₁ ⟶ V) (h₂ : Y₂ ⟶ X) (e₂ : Y₂ ⟶ W₂) (π₂ : W₂ ⟶ T₀) (g₂ : W₂ ⟶ V)
    (φ : W₁ ⟶ W₂) [UniversalHomeomorphism φ] (hπ : π₁ = φ ≫ π₂) (yφ : Y₁ ⟶ Y₂)
    [UniversalHomeomorphism yφ] (hφh : h₁ ≫ 𝟙 X = yφ ≫ h₂) (hφe : yφ ≫ e₂ = e₁ ≫ φ)
    (y₁ : Y₁ ⟶ Y₀) (y₂ : Y₂ ⟶ Y₀) (hy₁ : y₁ ≫ e₀ = e₁ ≫ π₁) (hy₂ : y₂ ≫ e₀ = e₂ ≫ π₂)
    (hyh₁ : h₁ ≫ 𝟙 X = y₁ ≫ h₀) (hyh₂ : h₂ ≫ 𝟙 X = y₂ ≫ h₀) (hy : y₁ = yφ ≫ y₂)
    (w₁ : h₁ ≫ fV = e₁ ≫ g₁) (w₂ : h₂ ≫ fV = e₂ ≫ g₂) (wφ : g₁ ≫ 𝟙 V = φ ≫ g₂)
    (x : GeometricPoint X)
    (ξ : (smallEtaleStalkAb x.hom).obj ((smallEtalePullbackAb (𝟙 X)).obj
      (((smallEtalePushforwardAb h₀).rightDerived r).obj ((smallEtalePullbackAb e₀).obj F₀)))) :
    (∀ η, (smallEtaleStalkAb x.hom).map
        ((higherBaseChangeMapAb fV g₁ h₁ e₁ w₁ r).app ((smallEtalePullbackAb π₁).obj F₀)) η ≠
      (smallEtaleStalkAb x.hom).map
        ((higherBaseChangeMapAb (𝟙 X) h₀ h₁ y₁ hyh₁ r).app ((smallEtalePullbackAb e₀).obj F₀) ≫
          ((smallEtalePushforwardAb h₁).rightDerived r).map
            ((smallEtalePullbackAbComp' y₁ e₀ (y₁ ≫ e₀) rfl).hom.app F₀ ≫
              (smallEtalePullbackAbComp' e₁ π₁ (y₁ ≫ e₀) hy₁).inv.app F₀)) ξ) ↔
    (∀ η, (smallEtaleStalkAb x.hom).map
        ((higherBaseChangeMapAb fV g₂ h₂ e₂ w₂ r).app ((smallEtalePullbackAb π₂).obj F₀)) η ≠
      (smallEtaleStalkAb x.hom).map
        ((higherBaseChangeMapAb (𝟙 X) h₀ h₂ y₂ hyh₂ r).app ((smallEtalePullbackAb e₀).obj F₀) ≫
          ((smallEtalePushforwardAb h₂).rightDerived r).map
            ((smallEtalePullbackAbComp' y₂ e₀ (y₂ ≫ e₀) rfl).hom.app F₀ ≫
              (smallEtalePullbackAbComp' e₂ π₂ (y₂ ≫ e₀) hy₂).inv.app F₀)) ξ) := by
  have hβY := isIso_higherBaseChangeMapAb_app_of_universalHomeomorphism yφ h₂ (𝟙 X) rfl h₁ hφh r
    ((smallEtalePullbackAb e₂).obj ((smallEtalePullbackAb π₂).obj F₀))
  have hβT := isIso_higherBaseChangeMapAb_app_of_universalHomeomorphism φ g₂ (𝟙 V) rfl g₁ wφ r
    ((smallEtalePullbackAb π₂).obj F₀)
  have hΘ : IsIso ((smallEtalePullbackAbIdOf (𝟙 X) rfl).inv.app
        (((smallEtalePushforwardAb h₂).rightDerived r).obj
          ((smallEtalePullbackAb e₂).obj ((smallEtalePullbackAb π₂).obj F₀))) ≫
      (higherBaseChangeMapAb (𝟙 X) h₂ h₁ yφ hφh r).app
        ((smallEtalePullbackAb e₂).obj ((smallEtalePullbackAb π₂).obj F₀)) ≫
      ((smallEtalePushforwardAb h₁).rightDerived r).map
        ((smallEtalePullbackAbComp' yφ e₂ (e₁ ≫ φ) hφe.symm).hom.app
            ((smallEtalePullbackAb π₂).obj F₀) ≫
          (smallEtalePullbackAbComp' e₁ φ (e₁ ≫ φ) rfl).inv.app
            ((smallEtalePullbackAb π₂).obj F₀) ≫
          (smallEtalePullbackAb e₁).map ((smallEtalePullbackAbComp' φ π₂ π₁ hπ).hom.app F₀))) :=
    IsIso.comp_isIso' (Iso.isIso_inv ((smallEtalePullbackAbIdOf (𝟙 X) rfl).app _))
      (IsIso.comp_isIso' hβY inferInstance)
  have hΨ : IsIso ((smallEtalePullbackAbComp' fV (𝟙 V) fV (Category.comp_id fV).symm).inv.app
          (((smallEtalePushforwardAb g₂).rightDerived r).obj ((smallEtalePullbackAb π₂).obj F₀)) ≫
        (smallEtalePullbackAb fV).map
          ((higherBaseChangeMapAb (𝟙 V) g₂ g₁ φ wφ r).app ((smallEtalePullbackAb π₂).obj F₀) ≫
            ((smallEtalePushforwardAb g₁).rightDerived r).map
              ((smallEtalePullbackAbComp' φ π₂ π₁ hπ).hom.app F₀))) :=
    IsIso.comp_isIso' (Iso.isIso_inv ((smallEtalePullbackAbComp' fV (𝟙 V) fV
      (Category.comp_id fV).symm).app _)) inferInstance
  have hsq := obstructionSourceTransferMap_comp_higherBaseChangeMapAb h₁ e₁ π₁ g₁ h₂ e₂ π₂ g₂ φ
    hπ yφ hφh hφe w₁ w₂ wφ (fV := fV) (F₀ := F₀) (r := r)
  have hpb := obstructionPullbackMap_eq_comp h₁ e₁ π₁ h₂ e₂ π₂ φ hπ yφ hφh hφe y₁ y₂ hy₁ hy₂
    hyh₁ hyh₂ hy (h₀ := h₀) (e₀ := e₀) (F₀ := F₀) (r := r)
  exact forall_map_ne_iff_of_isIso (smallEtaleStalkAb x.hom) _ _ _ _ _ _ hsq.symm hpb.symm ξ

end Transfer

end Stacks.EtaleCohomology

end
