module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.AlgebraUnitPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.ClosedTowerSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackUnitIsoComp

/-!
# The structure maps `𝒪_{X_n} ⟶ z_{n, *} 𝒪_{Z_n}` as a morphism of systems

Let `z_n : Z_n ⟶ X_n` be a cartesian tower of affine morphisms over the adic fibres of an
algebraic space `X`. The structure maps `𝒪_{X_n} ⟶ z_{n, *} 𝒪_{Z_n}`, read through
`ι_n ^* 𝒪_X ≅ 𝒪_{X_n}`, are compatible with the transition isomorphisms, so they form a morphism
from the restriction of `𝒪_X` to the tower to the system `(z_{n, *} 𝒪_{Z_n})_n`.

## Main definitions

* `AlgebraicGeometry.Space.thickeningRestrictionHomOfComm`: a morphism out of the restriction of
  a coherent module to the thickenings, from compatible maps of the terms.
* `AlgebraicGeometry.Space.affineTowerUnitHomOfHom`: the structure maps precomposed with a map
  `ι_n ^* M ⟶ ι_n ^* 𝒪_X`, as a morphism of systems out of the restriction of `M`.
* `AlgebraicGeometry.Space.affineTowerUnitHom`: the morphism of systems of the structure maps.

## Main results

* `AlgebraicGeometry.Space.modulePullbackCompIsoOfEq_hom_app_comp_modulePullbackUnitIso_hom`: the
  identifications `h ^* 𝒪 ≅ 𝒪` are compatible with the comparisons `f ^* g ^* ≅ h ^*` along a
  factorization `f ≫ g = h`.
* `AlgebraicGeometry.Space.affineTowerUnitHom_comm`: the structure maps are compatible with the
  transition isomorphisms.
* `AlgebraicGeometry.Space.affineTowerUnitHom_app`,
  `AlgebraicGeometry.Space.modulePullbackUnitIso_inv_comp_affineTowerUnitHom_app`: the
  components, which read through `ι_n ^* 𝒪_X ≅ 𝒪_{Z_n}` are the structure maps.

## References

* [Stacks Project, Tag 08BG](https://stacks.math.columbia.edu/tag/08BG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The identifications `h ^* 𝒪 ≅ 𝒪` are compatible with the comparison `f ^* g ^* ≅ h ^*` along a
factorization `f ≫ g = h`. -/
theorem modulePullbackCompIsoOfEq_hom_app_comp_modulePullbackUnitIso_hom
    {X Y W : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ W) {h : X ⟶ W} (w : f ≫ g = h) :
    (modulePullbackCompIsoOfEq B S hS f g w).hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS W)) ≫
        (modulePullbackUnitIso B S hS h).hom =
      (modulePullback B S hS f).map (modulePullbackUnitIso B S hS g).hom ≫
        (modulePullbackUnitIso B S hS f).hom := by
  subst w
  have h1 : (modulePullbackCompIsoOfEq B S hS f g rfl).hom =
      (modulePullbackCompIso B S hS f g).hom := Category.comp_id _
  rw [h1]
  exact modulePullbackCompIso_hom_app_comp_modulePullbackUnitIso_hom B S hS f g

variable {X : AlgebraicSpaces B S hS} {Z : ℕ → AlgebraicSpaces B S hS} (ι : ∀ n, Z n ⟶ X)
  (t : ∀ n, Z n ⟶ Z (n + 1)) (hι : ∀ n, t n ≫ ι (n + 1) = ι n)
  (hZ : ∀ n, HasEtaleLocalProperty B S hS (Z n).1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
  (W : ∀ n, AffineOver B S hS (Z n)) (s : ∀ n, (W n).obj.left ⟶ (W (n + 1)).obj.left)
  (hcart : ∀ n, IsPullback (s n) (W n).obj.hom (W (n + 1)).obj.hom (t n))
  (hcoh : ∀ n, IsCoherent B S hS (Z n).1 (Z n).2
    (pushforwardAlgebra B S hS (W n).obj).underlyingModule)

/-- The structure sheaf of `X`, as a coherent module. -/
abbrev unitCoherentModule
    (hO : IsCoherent B S hS X.1 X.2 (SheafOfModules.unit (structureRingSheaf B S hS X))) :
    CoherentModules.{u, u} B S hS X.1 X.2 :=
  ⟨_, hO⟩

/-- The structure maps of a cartesian affine tower, read through `ι_n ^* 𝒪_X ≅ 𝒪_{Z_n}`, are
compatible with the transition isomorphisms of the tower and with the comparisons
`t n ^* ι (n + 1) ^* ≅ ι n ^*`. -/
theorem affineTowerUnitHom_comm (n : ℕ) :
    (modulePullback B S hS (t n)).map ((modulePullbackUnitIso B S hS (ι (n + 1))).hom ≫
        AlgebraSheaf.unitToUnderlyingModule (pushforwardAlgebra B S hS (W (n + 1)).obj)) ≫
        (affineTowerModuleTransition B S hS t W s hcart n).hom =
      (modulePullbackCompIsoOfEq B S hS (t n) (ι (n + 1)) (hι n)).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X)) ≫
        (modulePullbackUnitIso B S hS (ι n)).hom ≫
          AlgebraSheaf.unitToUnderlyingModule (pushforwardAlgebra B S hS (W n).obj) := by
  have h1 := modulePullback_map_unitToUnderlyingModule_comp_affineTowerModuleTransition B S hS
    t W s hcart n
  have h2 := modulePullbackCompIsoOfEq_hom_app_comp_modulePullbackUnitIso_hom B S hS (t n)
    (ι (n + 1)) (hι n)
  rw [Functor.map_comp, Category.assoc, h1, ← Category.assoc, ← h2]
  exact Category.assoc _ _ _

/-- Pasting a commutative square with a second commutative square. -/
private theorem comp_comp_eq_of_comm {C : Type*} [Category C] {a b c d a' e : C}
    (m₁ : a ⟶ b) (m₂ : b ⟶ c) (T : c ⟶ d) (k : b ⟶ e) (r : e ⟶ d) (n₁ : a ⟶ a') (n₂ : a' ⟶ e)
    (hcomm : m₂ ≫ T = k ≫ r) (hnat : m₁ ≫ k = n₁ ≫ n₂) :
    (m₁ ≫ m₂) ≫ T = n₁ ≫ n₂ ≫ r := by
  rw [Category.assoc, hcomm, ← Category.assoc, hnat, Category.assoc]

/-- A morphism out of the restriction of a coherent module to the thickenings, from maps
`ι n ^* M ⟶ F_n` compatible with the transition isomorphisms. -/
def thickeningRestrictionHomOfComm (M : CoherentModules.{u, u} B S hS X.1 X.2)
    (A' : ThickeningCoherentSystem B S hS Z t)
    (σ : ∀ n, (modulePullback B S hS (ι n)).obj M.obj ⟶ (A'.term n).obj)
    (h : ∀ n, (modulePullback B S hS (t n)).map (σ (n + 1)) ≫ (A'.transitionIso n).hom =
      (((thickeningRestriction B S hS ι t hι hZ).obj M).transitionIso n).hom ≫ σ n) :
    (thickeningRestriction B S hS ι t hι hZ).obj M ⟶ A' where
  app := σ
  comm := h

/-- The components of a morphism built by
`AlgebraicGeometry.Space.thickeningRestrictionHomOfComm`. -/
theorem thickeningRestrictionHomOfComm_app (M : CoherentModules.{u, u} B S hS X.1 X.2)
    (A' : ThickeningCoherentSystem B S hS Z t)
    (σ : ∀ n, (modulePullback B S hS (ι n)).obj M.obj ⟶ (A'.term n).obj)
    (h : ∀ n, (modulePullback B S hS (t n)).map (σ (n + 1)) ≫ (A'.transitionIso n).hom =
      (((thickeningRestriction B S hS ι t hι hZ).obj M).transitionIso n).hom ≫ σ n) (n : ℕ) :
    (thickeningRestrictionHomOfComm B S hS ι t hι hZ M A' σ h).app n = σ n :=
  rfl

/-- `AlgebraicGeometry.Space.affineTowerUnitHom_comm` precomposed with a morphism `N ⟶ 𝒪_X`. -/
theorem affineTowerUnitHom_comm_of_hom (N : Modules.{u, u} B S hS X.1 X.2)
    (φ : N ⟶ SheafOfModules.unit (structureRingSheaf B S hS X)) (n : ℕ) :
    (modulePullback B S hS (t n)).map ((modulePullback B S hS (ι (n + 1))).map φ ≫
        (modulePullbackUnitIso B S hS (ι (n + 1))).hom ≫
        AlgebraSheaf.unitToUnderlyingModule (pushforwardAlgebra B S hS (W (n + 1)).obj)) ≫
        (affineTowerModuleTransition B S hS t W s hcart n).hom =
      (modulePullbackCompIsoOfEq B S hS (t n) (ι (n + 1)) (hι n)).hom.app N ≫
        (modulePullback B S hS (ι n)).map φ ≫
        (modulePullbackUnitIso B S hS (ι n)).hom ≫
          AlgebraSheaf.unitToUnderlyingModule (pushforwardAlgebra B S hS (W n).obj) :=
  (congrArg (· ≫ (affineTowerModuleTransition B S hS t W s hcart n).hom)
      (Functor.map_comp _ _ _)).trans
    (comp_comp_eq_of_comm _ _ _ _ _ _ _
      (affineTowerUnitHom_comm B S hS ι t hι W s hcart n)
      ((modulePullbackCompIsoOfEq B S hS (t n) (ι (n + 1)) (hι n)).hom.naturality φ))

/-- `AlgebraicGeometry.Space.affineTowerUnitHom_comm_of_hom` with the comparison and the
transition isomorphism replaced by isomorphisms equal to them. -/
theorem affineTowerUnitHom_comm_of_iso (N : Modules.{u, u} B S hS X.1 X.2)
    (φ : N ⟶ SheafOfModules.unit (structureRingSheaf B S hS X)) (n : ℕ)
    (ρN : (modulePullback B S hS (t n)).obj ((modulePullback B S hS (ι (n + 1))).obj N) ≅
      (modulePullback B S hS (ι n)).obj N)
    (hρN : ρN = (modulePullbackCompIsoOfEq B S hS (t n) (ι (n + 1)) (hι n)).app N)
    (T : (modulePullback B S hS (t n)).obj
        (pushforwardAlgebra B S hS (W (n + 1)).obj).underlyingModule ≅
      (pushforwardAlgebra B S hS (W n).obj).underlyingModule)
    (hT : T = affineTowerModuleTransition B S hS t W s hcart n) :
    (modulePullback B S hS (t n)).map ((modulePullback B S hS (ι (n + 1))).map φ ≫
        (modulePullbackUnitIso B S hS (ι (n + 1))).hom ≫
        AlgebraSheaf.unitToUnderlyingModule (pushforwardAlgebra B S hS (W (n + 1)).obj)) ≫
        T.hom =
      ρN.hom ≫ (modulePullback B S hS (ι n)).map φ ≫
        (modulePullbackUnitIso B S hS (ι n)).hom ≫
          AlgebraSheaf.unitToUnderlyingModule (pushforwardAlgebra B S hS (W n).obj) := by
  subst hρN hT
  exact affineTowerUnitHom_comm_of_hom B S hS ι t hι W s hcart N φ n

/-- The structure maps of a cartesian affine tower as a morphism of systems, out of the
restriction of a coherent module mapping to the structure sheaf. -/
def affineTowerUnitHomOfHom (M : CoherentModules.{u, u} B S hS X.1 X.2)
    (φ : M.obj ⟶ SheafOfModules.unit (structureRingSheaf B S hS X)) :
    (thickeningRestriction B S hS ι t hι hZ).obj M ⟶
      affineTowerSystem B S hS t W s hcart hcoh :=
  thickeningRestrictionHomOfComm B S hS ι t hι hZ M (affineTowerSystem B S hS t W s hcart hcoh)
    (fun n => (modulePullback B S hS (ι n)).map φ ≫
      (modulePullbackUnitIso B S hS (ι n)).hom ≫
      AlgebraSheaf.unitToUnderlyingModule (pushforwardAlgebra B S hS (W n).obj))
    (fun n => affineTowerUnitHom_comm_of_iso B S hS ι t hι W s hcart M.obj φ n
      (((thickeningRestriction B S hS ι t hι hZ).obj M).transitionIso n)
      (TowerSystem.restriction_obj_transitionIso _ _ _ _ M n)
      ((affineTowerSystem B S hS t W s hcart hcoh).transitionIso n) rfl)

/-- **The structure maps of a cartesian affine tower as a morphism of systems**: from the
restriction of the structure sheaf of `X` to the tower to the system of the direct images, with
components `ι_n ^* 𝒪_X ≅ 𝒪_{Z_n} ⟶ (W_n ⟶ Z_n)_* 𝒪_{W_n}`. -/
def affineTowerUnitHom
    (hO : IsCoherent B S hS X.1 X.2 (SheafOfModules.unit (structureRingSheaf B S hS X))) :
    (thickeningRestriction B S hS ι t hι hZ).obj (unitCoherentModule B S hS hO) ⟶
      affineTowerSystem B S hS t W s hcart hcoh :=
  affineTowerUnitHomOfHom B S hS ι t hι hZ W s hcart hcoh (unitCoherentModule B S hS hO) (𝟙 _)

/-- The components of the morphism of systems of the structure maps. -/
theorem affineTowerUnitHom_app
    (hO : IsCoherent B S hS X.1 X.2 (SheafOfModules.unit (structureRingSheaf B S hS X))) (n : ℕ) :
    (affineTowerUnitHom B S hS ι t hι hZ W s hcart hcoh hO).app n =
      (modulePullbackUnitIso B S hS (ι n)).hom ≫
        AlgebraSheaf.unitToUnderlyingModule (pushforwardAlgebra B S hS (W n).obj) :=
  (congrArg (· ≫ (modulePullbackUnitIso B S hS (ι n)).hom ≫
      AlgebraSheaf.unitToUnderlyingModule (pushforwardAlgebra B S hS (W n).obj))
    (CategoryTheory.Functor.map_id (modulePullback B S hS (ι n))
      (unitCoherentModule B S hS hO).obj)).trans (Category.id_comp _)

/-- The components of the morphism of systems of the structure maps, read through
`ι_n ^* 𝒪_X ≅ 𝒪_{Z_n}`, are the structure maps `𝒪_{Z_n} ⟶ (W_n ⟶ Z_n)_* 𝒪_{W_n}`. -/
theorem modulePullbackUnitIso_inv_comp_affineTowerUnitHom_app
    (hO : IsCoherent B S hS X.1 X.2 (SheafOfModules.unit (structureRingSheaf B S hS X))) (n : ℕ) :
    (modulePullbackUnitIso B S hS (ι n)).inv ≫
        (affineTowerUnitHom B S hS ι t hι hZ W s hcart hcoh hO).app n =
      AlgebraSheaf.unitToUnderlyingModule (pushforwardAlgebra B S hS (W n).obj) :=
  (congrArg ((modulePullbackUnitIso B S hS (ι n)).inv ≫ ·)
    (affineTowerUnitHom_app B S hS ι t hι hZ W s hcart hcoh hO n)).trans
    (Iso.inv_hom_id_assoc _ _)

end AlgebraicGeometry.Space

end
