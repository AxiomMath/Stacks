module

public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModulePullbackMap
public import StacksFrontier.Homology.Perfect.PerfectConeDegreeZeroLift

/-!
# The objects of the openness step of the theorem of the cube

Let `k` be a field, `f : X ⟶ Spec k` and `g : Y ⟶ Spec k` schemes over `k` with rational points
`x` and `y`, and let `R` be a `k`-algebra. This file fixes the notation of the openness step of
the theorem of the cube ([Stacks, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3), in the
form used by [Stacks, Tag 0BF4](https://stacks.math.columbia.edu/tag/0BF4)):

* `Q = (X ×_k Y) ×_k Spec R`, with its structure morphism `qR : Q ⟶ Spec R`;
* the two faces `jX : X_R ⟶ Q`, `x' ↦ (x', y)`, and `jY : Y_R ⟶ Q`, `y' ↦ (x, y')`, where
  `X_R = X ×_k Spec R` and `Y_R = Y ×_k Spec R`;
* for families of opens `UX` of `X` and `UY` of `Y`, the product family `W (a, b)` on `Q`,
  the preimage of `UX a × UY b`;
* for a module `L` on `Q`, the alternating Čech complexes of `L` on `W` and of its two face
  restrictions on the preimage families, as complexes of `R`-modules, and the two restriction
  maps between them.

## Main definitions

* `AlgebraicGeometry.Cube.Openness.Q`, `qR`, `XR`, `qX`, `jX`, `YR`, `qY`, `jY`.
* `AlgebraicGeometry.Cube.Openness.W`: the product family of opens.
* `AlgebraicGeometry.Cube.Openness.C`, `DX`, `DY`, `ΦX`, `ΦY`: the three Čech complexes and the
  two face maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

noncomputable section

namespace AlgebraicGeometry.Cube.Openness

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _)
  (R : Type u) [CommRing R] [Algebra k R]

/-- The morphism `Spec R ⟶ Spec k` of the `k`-algebra `R`. -/
abbrev φR : Spec (.of R) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k R))

/-- `Q = (X ×_k Y) ×_k Spec R`. -/
abbrev Q : Scheme.{u} := pullback (pullback.fst f g ≫ f) (φR R)

/-- The structure morphism `Q ⟶ Spec R`. -/
abbrev qR : Q f g R ⟶ Spec (.of R) := pullback.snd _ _

/-- `X_R = X ×_k Spec R`. -/
abbrev XR : Scheme.{u} := pullback f (φR R)

/-- The structure morphism `X_R ⟶ Spec R`. -/
abbrev qX : XR f R ⟶ Spec (.of R) := pullback.snd _ _

/-- `Y_R = Y ×_k Spec R`. -/
abbrev YR : Scheme.{u} := pullback g (φR R)

/-- The structure morphism `Y_R ⟶ Spec R`. -/
abbrev qY : YR g R ⟶ Spec (.of R) := pullback.snd _ _

include hy in
/-- The composite `X ⟶ X ×_k Y ⟶ Spec k` of `x' ↦ (x', y)` with the structure morphism is
`f`. -/
theorem liftX_comp : pullback.lift (𝟙 X) (f ≫ y) (by simp [hy]) ≫ pullback.fst f g ≫ f =
    𝟙 X ≫ f := by
  rw [pullback.lift_fst_assoc, Category.id_comp]

include hx in
/-- The composite `Y ⟶ X ×_k Y ⟶ Spec k` of `y' ↦ (x, y')` with the structure morphism is
`g`. -/
theorem liftY_comp : pullback.lift (g ≫ x) (𝟙 Y) (by simp [hx]) ≫ pullback.fst f g ≫ f =
    𝟙 Y ≫ g := by
  rw [pullback.lift_fst_assoc, Category.assoc, hx, Category.comp_id, Category.id_comp]

/-- The face `X_R ⟶ Q`, `x' ↦ (x', y)`. -/
def jX : XR f R ⟶ Q f g R :=
  pullback.map f (φR R) (pullback.fst f g ≫ f) (φR R)
    (pullback.lift (𝟙 X) (f ≫ y) (by simp [hy])) (𝟙 _) (𝟙 _)
    (liftX_comp f g y hy).symm (by simp)

/-- The face `Y_R ⟶ Q`, `y' ↦ (x, y')`. -/
def jY : YR g R ⟶ Q f g R :=
  pullback.map g (φR R) (pullback.fst f g ≫ f) (φR R)
    (pullback.lift (g ≫ x) (𝟙 Y) (by simp [hx])) (𝟙 _) (𝟙 _)
    (liftY_comp f g x hx).symm (by simp)

/-- The face `jX` is a morphism over `Spec R`: `jX ≫ qR = qX`. -/
theorem jX_qR : jX f g y hy R ≫ qR f g R = qX f R := by
  rw [jX, pullback.lift_snd, Category.comp_id]

/-- The face `jY` is a morphism over `Spec R`: `jY ≫ qR = qY`. -/
theorem jY_qR : jY f g x hx R ≫ qR f g R = qY g R := by
  rw [jY, pullback.lift_snd, Category.comp_id]

variable {I J : Type u} (UX : I → X.Opens) (UY : J → Y.Opens)

/-- The product family of opens of `Q`: the preimage of `UX a × UY b`. -/
def W (s : I × J) : (Q f g R).Opens :=
  pullback.fst (pullback.fst f g ≫ f) (φR R) ⁻¹ᵁ
    (pullback.fst f g ⁻¹ᵁ UX s.1 ⊓ pullback.snd f g ⁻¹ᵁ UY s.2)

variable (L : (Q f g R).Modules)

/-- The alternating Čech complex of `L` on the product family, as a complex of `R`-modules. -/
abbrev C : CochainComplex (ModuleCat.{u} R) ℕ :=
  Stacks.Cech.alternatingCechModuleComplex (qR f g R) (W f g R UX UY) L

/-- The alternating Čech complex of the restriction of `L` to the face `X_R`. -/
abbrev DX : CochainComplex (ModuleCat.{u} R) ℕ :=
  Stacks.Cech.alternatingCechModuleComplex (qX f R) (fun s => jX f g y hy R ⁻¹ᵁ W f g R UX UY s)
    ((Scheme.Modules.pullback (jX f g y hy R)).obj L)

/-- The alternating Čech complex of the restriction of `L` to the face `Y_R`. -/
abbrev DY : CochainComplex (ModuleCat.{u} R) ℕ :=
  Stacks.Cech.alternatingCechModuleComplex (qY g R) (fun s => jY f g x hx R ⁻¹ᵁ W f g R UX UY s)
    ((Scheme.Modules.pullback (jY f g x hx R)).obj L)

/-- Restriction of Čech cochains to the face `X_R`. -/
def ΦX : C f g R UX UY L ⟶ DX f g y hy R UX UY L :=
  Stacks.Cech.alternatingCechModuleComplexPullbackMap (qR f g R) (qX f R) (jX f g y hy R)
    (jX_qR f g y hy R) (W f g R UX UY) _ (fun _ => rfl) L

/-- Restriction of Čech cochains to the face `Y_R`. -/
def ΦY : C f g R UX UY L ⟶ DY f g x hx R UX UY L :=
  Stacks.Cech.alternatingCechModuleComplexPullbackMap (qR f g R) (qY g R) (jY f g x hx R)
    (jY_qR f g x hx R) (W f g R UX UY) _ (fun _ => rfl) L

end AlgebraicGeometry.Cube.Openness

end

end
