module

public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveFormalNeighborhoodTopology
public import StacksFrontier.AlgebraicGeometry.Algebraization
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodMultiplicative

/-!
# The adic tower of the formal neighbourhood of a curve

Let `D` be an ideal sheaf on a scheme `X` and `A = lim Γ(Cₙ, 𝒪)` the ring of formal functions
along the subscheme it cuts out (`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing`).
Every infinitesimal thickening `Cₙ = V(Dⁿ⁺¹)` maps to `Spec A`, through `Spec Γ(Cₙ, 𝒪)`, and these
maps are compatible with the inclusions of thickenings. For an ideal `I` of `A` and a monotone
choice of thickenings `M : ℕ → ℕ`, the base changes `Cₘ₍ₙ₎ ×_{Spec A} Spec (A ⧸ Iⁿ⁺¹)` form a tower
over the adic thickenings of `Spec A`. This is the tower that Grothendieck's algebraization theorem
(Stacks 089A) is applied to, in the construction of the formal contraction of a curve with negative
normal bundle needed for Stacks 0D5E.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.thickeningToSpec`: `Cₙ ⟶ Spec A`.
* `AlgebraicGeometry.Scheme.IdealSheafData.thickeningInclusion`: `Cᵢ ⟶ Cⱼ` for `i ≤ j`.
* `AlgebraicGeometry.Scheme.IdealSheafData.adicTower`: `Cₘ₍ₙ₎ ×_{Spec A} Spec (A ⧸ Iⁿ⁺¹)`, with
  its projection `adicTowerToThickening` to the adic thickening and transition maps
  `adicTowerSucc`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.thickeningInclusion_thickeningToSpec`: the maps to
  `Spec A` are compatible with the inclusions of thickenings.
* `AlgebraicGeometry.Scheme.IdealSheafData.adicTowerSucc_adicTowerToThickening`: the transition
  maps lie over the transition maps of the adic thickenings.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- The inclusion `Cᵢ ⟶ Cⱼ` of infinitesimal thickenings, for `i ≤ j`. -/
def thickeningInclusion {i j : ℕ} (h : i ≤ j) : thickening D i ⟶ thickening D j :=
  inclusion (pow_succ_le_pow_succ D h)

/-- The morphism from the `(n + 1)`-st infinitesimal thickening to the spectrum of the ring of
formal functions: `Cₙ ⟶ Spec Γ(Cₙ, 𝒪) ⟶ Spec A`. -/
def thickeningToSpec (n : ℕ) : thickening D n ⟶ Spec (.of (formalNeighborhoodRing D)) :=
  (thickening D n).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (formalNeighborhoodProjection D n))

/-- The maps of the thickenings to `Spec A` are compatible with the inclusions. -/
@[reassoc]
theorem thickeningInclusion_thickeningToSpec {i j : ℕ} (h : i ≤ j) :
    thickeningInclusion D h ≫ thickeningToSpec D j = thickeningToSpec D i := by
  have e : CommRingCat.ofHom (formalNeighborhoodProjection D i) =
      CommRingCat.ofHom (formalNeighborhoodProjection D j) ≫ (thickeningInclusion D h).appTop := by
    ext a
    exact (thickeningRestrictionLE_formalNeighborhoodProjection D h a).symm
  have h1 : thickeningInclusion D h ≫ (thickening D j).toSpecΓ =
      (thickening D i).toSpecΓ ≫ Spec.map (thickeningInclusion D h).appTop :=
    Scheme.toSpecΓ_naturality _
  have h2 : Spec.map (thickeningInclusion D h).appTop ≫
      Spec.map (CommRingCat.ofHom (formalNeighborhoodProjection D j)) =
        Spec.map (CommRingCat.ofHom (formalNeighborhoodProjection D i)) :=
    (Spec.map_comp _ _).symm.trans (congrArg Spec.map e.symm)
  simp only [thickeningToSpec]
  rw [reassoc_of% h1, h2]
  rfl

variable (I : Ideal (formalNeighborhoodRing D)) {M : ℕ → ℕ} (hM : Monotone M)

/-- The `n`-th member `Cₘ₍ₙ₎ ×_{Spec A} Spec (A ⧸ Iⁿ⁺¹)` of the adic tower of the formal
neighbourhood. -/
abbrev adicTower (M : ℕ → ℕ) (n : ℕ) : Scheme.{u} :=
  pullback (thickeningToSpec D (M n)) (adicThickeningι (formalNeighborhoodRing D) I n)

/-- The projection of the adic tower to the adic thickening `Spec (A ⧸ Iⁿ⁺¹)`. -/
abbrev adicTowerToThickening (M : ℕ → ℕ) (n : ℕ) :
    adicTower D I M n ⟶ adicThickening (formalNeighborhoodRing D) I n :=
  pullback.snd _ _

/-- The projection of the adic tower to the thickening `Cₘ₍ₙ₎`. -/
abbrev adicTowerToThickeningOfD (M : ℕ → ℕ) (n : ℕ) :
    adicTower D I M n ⟶ thickening D (M n) :=
  pullback.fst _ _

/-- The transition map `Cₘ₍ₙ₎ ×_A A ⧸ Iⁿ⁺¹ ⟶ Cₘ₍ₙ₊₁₎ ×_A A ⧸ Iⁿ⁺²` of the adic tower. -/
def adicTowerSucc (n : ℕ) : adicTower D I M n ⟶ adicTower D I M (n + 1) :=
  pullback.map _ _ _ _ (thickeningInclusion D (hM (Nat.le_succ n)))
    (adicThickeningSucc (formalNeighborhoodRing D) I n) (𝟙 _)
    (by rw [Category.comp_id, thickeningInclusion_thickeningToSpec])
    (by rw [Category.comp_id, adicThickeningSucc_ι])

/-- The transition maps of the adic tower lie over the transition maps of the adic
thickenings. -/
@[reassoc]
theorem adicTowerSucc_adicTowerToThickening (n : ℕ) :
    adicTowerSucc D I hM n ≫ adicTowerToThickening D I M (n + 1) =
      adicTowerToThickening D I M n ≫ adicThickeningSucc (formalNeighborhoodRing D) I n :=
  pullback.lift_snd _ _ _

/-- The transition maps of the adic tower lie over the inclusions of thickenings. -/
@[reassoc]
theorem adicTowerSucc_adicTowerToThickeningOfD (n : ℕ) :
    adicTowerSucc D I hM n ≫ adicTowerToThickeningOfD D I M (n + 1) =
      adicTowerToThickeningOfD D I M n ≫ thickeningInclusion D (hM (Nat.le_succ n)) :=
  pullback.lift_fst _ _ _

end AlgebraicGeometry.Scheme.IdealSheafData

end
