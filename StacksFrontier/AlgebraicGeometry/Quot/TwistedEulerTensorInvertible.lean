module

public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCoherence

/-!
# The twisted Euler characteristics of a twist by an invertible module

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation, `L` an invertible
`𝒪_X`-module and `(T, 𝓕)` an object of `Coh_{X/B}`.  If `(T, 𝓖)` is a second object with
`𝓖 ≅ 𝓕 ⊗ L_T`, then at every point `t ∈ T` and every integer `n`

`χ(X_t, 𝓖_t ⊗ L_t^{⊗ n}) = χ(X_t, 𝓕_t ⊗ L_t^{⊗ (n + 1)})`,

because `𝓖_t ⊗ L_t^{⊗ n} ≅ 𝓕_t ⊗ L_t ⊗ L_t^{⊗ n} ≅ 𝓕_t ⊗ L_t^{⊗ (n + 1)}` (Stacks 0DP7).

## Main definitions

* `AlgebraicGeometry.Space.moduleTensorAssocIso`, `moduleTensorBraidIso` and
  `moduleTensorMapIso`: the associativity and symmetry constraints and the functoriality of the
  tensor product of `𝒪_Z`-modules on an algebraic space `Z`.
* `AlgebraicGeometry.Space.invertibleTensorPowerSuccIso`: `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}`.

## Main results

* `AlgebraicGeometry.Space.CoherentObject.twistedEuler_mk_tensor`: the twist identity.

## References

* [Stacks Project, Tag 0DP7](https://stacks.math.columbia.edu/tag/0DP7)
* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

section Tensor

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (Z : AlgebraicSpaces B S hS)

/-- The tensor product of two `𝒪_Z`-modules, `M ⊗_{𝒪_Z} N`. -/
abbrev moduleTensor (M N : Modules.{u, u} B S hS Z.1 Z.2) : Modules.{u, u} B S hS Z.1 Z.2 :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS Z.1 Z.2).O).obj M).obj N

/-- The associativity constraint `(M ⊗ N) ⊗ P ≅ M ⊗ (N ⊗ P)`. -/
def moduleTensorAssocIso (M N P : Modules.{u, u} B S hS Z.1 Z.2) :
    moduleTensor B S hS Z (moduleTensor B S hS Z M N) P ≅
      moduleTensor B S hS Z M (moduleTensor B S hS Z N P) :=
  @Stacks.SheafOfModules.Invertible.tensorProductAssociator.{u, u + 1, u}
    (smallEtaleRingedSite B S hS Z.1 Z.2).C _ (smallEtaleRingedSite B S hS Z.1 Z.2).J
    (structurePresheaf B S hS Z.1)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O).property _ _
    M N P

/-- The symmetry constraint `M ⊗ N ≅ N ⊗ M`. -/
def moduleTensorBraidIso (M N : Modules.{u, u} B S hS Z.1 Z.2) :
    moduleTensor B S hS Z M N ≅ moduleTensor B S hS Z N M :=
  @Stacks.SheafOfModules.Invertible.tensorProductBraiding.{u, u + 1, u}
    (smallEtaleRingedSite B S hS Z.1 Z.2).C _ (smallEtaleRingedSite B S hS Z.1 Z.2).J
    (structurePresheaf B S hS Z.1)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O).property _ _
    M N

/-- The tensor product of two isomorphisms. -/
def moduleTensorMapIso {M M' N N' : Modules.{u, u} B S hS Z.1 Z.2} (e : M ≅ M') (e' : N ≅ N') :
    moduleTensor B S hS Z M N ≅ moduleTensor B S hS Z M' N' :=
  @Stacks.SheafOfModules.Invertible.tensorProductIso.{u, u + 1, u}
    (smallEtaleRingedSite B S hS Z.1 Z.2).C _ (smallEtaleRingedSite B S hS Z.1 Z.2).J
    (structurePresheaf B S hS Z.1)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O).property _ _
    _ _ _ _ e e'

/-- The successor step of the integer tensor powers, `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}`
(Stacks 01CU). -/
def invertibleTensorPowerSuccIso (L : Modules.{u, u} B S hS Z.1 Z.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Z.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).property L]
    (n : ℤ) :
    moduleTensor B S hS Z (invertibleTensorPower B S hS Z.1 Z.2 L n) L ≅
      invertibleTensorPower B S hS Z.1 Z.2 L (n + 1) :=
  @Stacks.SheafOfModules.Invertible.tensorPowerSuccIso.{u, u + 1, u}
    (smallEtaleRingedSite B S hS Z.1 Z.2).C _ (smallEtaleRingedSite B S hS Z.1 Z.2).J
    (structurePresheaf B S hS Z.1)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O).property _ _
    L (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL) n

end Tensor

namespace CoherentObject

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  (L : Modules.{u, u} B S hS D.X.1 D.X.2)
  [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property
      L]

include hL in
/-- **The twist identity of Stacks 0DP7.**  Let `(T, 𝓕)` and `(T, 𝓖)` be two objects of
`Coh_{X/B}` over the same test scheme with `𝓖 ≅ 𝓕 ⊗ L_T`.  Then at every point `t ∈ T`,
`χ(X_t, 𝓖_t ⊗ L_t^{⊗ n}) = χ(X_t, 𝓕_t ⊗ L_t^{⊗ (n + 1)})`. -/
theorem twistedEuler_mk_tensor (T : SchemesOver D.Y)
    (F F' : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (h₁ : F.IsQuasicoherentOnSite) (h₂ : F.IsFinitePresentationOnSite)
    (h₃ : IsFlatOver B S hS (D.space T).2 (D.projection T).hom F)
    (h₄ : ∃ (hp : IsLocallyOfFiniteType B S hS (D.projection T).hom)
      (hU : IsClosed (D.support T F)),
      IsProperOver B S hS (D.space T).2 ((schemeSpaceFunctor B S hS).obj T.left).2
        (D.projection T).hom hp (D.support T F) hU)
    (h₁' : F'.IsQuasicoherentOnSite) (h₂' : F'.IsFinitePresentationOnSite)
    (h₃' : IsFlatOver B S hS (D.space T).2 (D.projection T).hom F')
    (h₄' : ∃ (hp : IsLocallyOfFiniteType B S hS (D.projection T).hom)
      (hU : IsClosed (D.support T F')),
      IsProperOver B S hS (D.space T).2 ((schemeSpaceFunctor B S hS).obj T.left).2
        (D.projection T).hom hp (D.support T F') hU)
    (e : F' ≅ moduleTensor B S hS (D.space T) F
      ((modulePullback B S hS (baseChangeProjection D.f T)).obj L))
    (t : (⟨T, F, h₁, h₂, h₃, h₄⟩ : CoherentObject D).testScheme) (n : ℤ) :
    twistedEuler L (⟨T, F', h₁', h₂', h₃', h₄'⟩ : CoherentObject D) t n =
      twistedEuler L (⟨T, F, h₁, h₂, h₃, h₄⟩ : CoherentObject D) t (n + 1) := by
  let c : CoherentObject D := ⟨T, F, h₁, h₂, h₃, h₄⟩
  let g := D.relativeMap (c.pointTestHom t)
  let q := baseChangeProjection D.f (c.pointTest t)
  have hk : g ≫ baseChangeProjection D.f T = q := baseChangeMap_comp_projection D.f _
  let e₁ := moduleTensorMapIso B S hS (c.fibreSpace t)
    ((modulePullback B S hS g).mapIso e ≪≫ modulePullbackSheafTensorIso B S hS g F _ ≪≫
      moduleTensorMapIso B S hS (c.fibreSpace t) (Iso.refl _)
        ((modulePullbackTriangle B S hS hk).app L).symm)
    (Iso.refl ((modulePullback B S hS q).obj (invertibleTensorPower B S hS D.X.1 D.X.2 L n)))
  exact eulerCharacteristicAlong_congr _ _ _ _ _ _ _ (e₁ ≪≫
    moduleTensorAssocIso B S hS (c.fibreSpace t) _ _ _ ≪≫
      moduleTensorMapIso B S hS (c.fibreSpace t) (Iso.refl _)
        ((modulePullbackSheafTensorIso B S hS q L _).symm ≪≫
          (modulePullback B S hS q).mapIso (moduleTensorBraidIso B S hS D.X L _ ≪≫
            invertibleTensorPowerSuccIso B S hS D.X L n)))

end CoherentObject

end AlgebraicGeometry.Space

end
